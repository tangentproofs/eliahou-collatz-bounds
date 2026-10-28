#!/usr/bin/env python3
"""Build learn/data/decls.json and learn/data/xref.json from the repo's Lean source, WITHOUT a Lean build.

The reference sites (star-height and others) extract declarations from a compiled build
(ExtractDecls.lean) and identifier references from Lean's .ilean files. This site was written
without building the Lean (by the owner's choice: no Lean builds on our servers), so this script
does the same job by reading the source text:

  * declarations: top-level `def/theorem/lemma/abbrev/structure/inductive/class/instance` lines,
    with their namespace, line range and verbatim header text;
  * mentions (meaningDeps) / proof uses (proofDeps): identifier tokens of the statement (and of a
    definition's body) / of a theorem's proof, resolved against the declarations found here;
  * Mathlib links: dotted names under a known Mathlib/core namespace (scan.config.json), plus a
    short hand-checked list of bare names.

Every declaration is marked `"extracted": false` so the site and its Trust page say so. When the
project is built on a capable machine, replace this with ExtractDecls.lean + build_xref.py.
Configuration: learn/scan.config.json.
"""
import hashlib, json, os, re

SITE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(SITE)
CFG = json.load(open(os.path.join(SITE, "scan.config.json"), encoding="utf-8"))
OUT = os.path.join(SITE, "data")
NS = CFG.get("ns", "")                      # namespace prefix stripped from ids
HEADS = CFG["headlines"]
ML_NS = set(CFG.get("mathlibNamespaces", []))
ML_NAMES = set(CFG.get("mathlibNames", []))

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*(def|theorem|lemma|abbrev|structure|inductive|class|instance)\s+([^\s:({\[]+)?")
TOK = re.compile(r"[A-Za-z_\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2080-\u209f][\w.'\u00c0-\u024f\u0370-\u03ff\u1d00-\u1dbf\u2080-\u209f!?₀-₉]*")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


def lean_files():
    out = []
    for r in CFG["roots"]:
        p = os.path.join(ROOT, r)
        if os.path.isfile(p): out.append(r)
        for dp, dns, fs in os.walk(p):
            dns[:] = sorted(d for d in dns if not d.startswith("."))
            for f in sorted(fs):
                if f.endswith(".lean"): out.append(os.path.relpath(os.path.join(dp, f), ROOT).replace(os.sep, "/"))
    return sorted(set(out))


def cut(text, kind):
    """Header up to the top-level ':=' (or ' where' / first top-level '|' for defs). Whole text for types."""
    if kind in ("structure", "inductive", "class"): return text.rstrip(), ""
    depth, i = 0, 0
    while i < len(text):
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i); i = len(text) if j < 0 else j; continue
        if c in OPEN: depth += 1
        elif c in CLOSE: depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(":=", i):
            return text[:i].rstrip(), text[i:]
        elif depth == 0 and text.startswith(" where", i) and kind != "theorem" and (i + 6 == len(text) or text[i + 6] in " \n"):
            return text[:i].rstrip(), text[i:]
        elif depth == 0 and kind != "theorem" and c == "\n" and re.match(r"\n\s*\|", text[i:]):
            return text[:i].rstrip(), text[i:]
        i += 1
    return text.rstrip(), ""


def strip_comments(lines):
    """Blank out comment text (keeping line structure) so declarations inside /- -/ are ignored."""
    out, depth = [], 0
    for ln in lines:
        res, i = [], 0
        while i < len(ln):
            if depth == 0 and ln.startswith("--", i): break
            if ln.startswith("/-", i): depth += 1; i += 2; continue
            if depth and ln.startswith("-/", i): depth -= 1; i += 2; continue
            if depth == 0: res.append(ln[i])
            i += 1
        out.append("".join(res))
    return out


def scan(file):
    raw = open(os.path.join(ROOT, file), encoding="utf-8").read().split("\n")
    lines = strip_comments(raw)
    ns, out, starts = [], [], []
    anon = 0
    for k, ln in enumerate(lines):
        if m := re.match(r"^namespace\s+(\S+)", ln): ns.append(m.group(1)); starts.append(("ns", k)); continue
        if m := re.match(r"^end\s+(\S+)\s*$", ln):
            if ns and ns[-1] == m.group(1): ns.pop()
            starts.append(("end", k)); continue
        if re.match(r"^(section|end|open|variable|universe|set_option|attribute|#|noncomputable section|mutual|import)\b", ln): starts.append(("other", k)); continue
        if (m := DECL.match(ln)) and not ln.startswith(" "):
            name = m.group(2)
            if not name:
                if m.group(1) != "instance": continue
                anon += 1; name = f"instance_{k + 1}"
            full = name[7:] if name.startswith("_root_.") else ".".join(ns + [name])
            starts.append(("decl", k, m.group(1), full))
        elif raw[k].startswith("/-") or re.match(r"^(example|macro|macro_rules|notation|syntax|elab|scoped|local|infix|infixl|infixr|prefix|postfix|deriving|run_cmd|#)", ln):
            # a top-level line that is not a declaration (doc comment, macro, notation…) ends the previous one
            starts.append(("other", k))
    for j, st in enumerate(starts):
        if st[0] != "decl": continue
        k, kind, full = st[1], st[2], st[3]
        end = (starts[j + 1][1] if j + 1 < len(starts) else len(raw)) - 1
        while end > k and not raw[end].strip(): end -= 1
        text = "\n".join(raw[k:end + 1])
        out.append({"name": full, "kind": "theorem" if kind == "lemma" else kind, "file": file,
                    "line": k + 1, "endLine": end + 1, "text": text,
                    "ns": full.rsplit(".", 1)[0] if "." in full else "", "opens": []})
    return out


def is_mathlib(t):
    if t in ML_NAMES: return True
    head = t.split(".")[0]
    return "." in t and head in ML_NS


def main():
    files = lean_files()
    decls = []
    for f in files: decls.extend(scan(f))
    seen = set()
    for d in decls:
        d["id"] = d["name"][len(NS):] if NS and d["name"].startswith(NS) else d["name"]
        while d["id"] in seen: d["id"] += "'"
        seen.add(d["id"])
    by_full = {}
    for d in decls: by_full.setdefault(d["name"], d)
    by_last = {}
    for d in decls: by_last.setdefault(d["name"].rsplit(".", 1)[-1], []).append(d)

    def resolve(tok, ctx_ns):
        if tok in by_full: return by_full[tok]
        parts = ctx_ns.split(".") if ctx_ns else []
        for i in range(len(parts), 0, -1):
            c = ".".join(parts[:i] + [tok])
            if c in by_full: return by_full[c]
        if NS and NS + tok in by_full: return by_full[NS + tok]
        # dotted suffix (e.g. `TwistExpr.fraction` written inside namespace RationalTangles)
        if "." in tok:
            cands = [e for e in decls if e["name"].endswith("." + tok)]
            return cands[0] if len(cands) == 1 else None
        return None

    def method(part):
        """`x.part` written on a local variable: the unique namespaced project decl named `part`."""
        c = [e for e in by_last.get(part, []) if "." in e["name"][len(NS):]]
        return c[0] if len(c) == 1 else None

    BINDER = re.compile(r"[({⦃]\s*([^(){}\[\]:⦃⦄]+?)\s*:\s*([A-Z][\w.']*)")
    def var_types(d):
        vt = {}
        for m in BINDER.finditer(d["statement"]):
            T = resolve(m.group(2), d["ns"])
            if T:
                for v in m.group(1).split(): vt[v] = T["name"]
        return vt

    def ret_type(e):
        """Head of the result type of a def (`def toStandard : TwistExpr → StandardExpr`)."""
        if e["kind"] not in ("def", "abbrev"): return None
        st, depth, last = e["statement"], 0, -1
        for i, c in enumerate(st):
            if c in OPEN: depth += 1
            elif c in CLOSE: depth = max(0, depth - 1)
            elif c == ":" and depth == 0 and not st.startswith(":=", i): last = i
        if last < 0: return None
        tail = re.split(r"→", st[last + 1:])[-1].strip()
        m = re.match(r"[A-Z][\w.']*", tail)
        T = resolve(m.group(0), e["ns"]) if m else None
        return T["name"] if T else None

    def resolve_tok(t, ctx_ns, vt=None):
        """[(offset within t, length, decl)] for a token, including `x.method` chains."""
        e = resolve(t, ctx_ns)
        if e: return [(0, len(t), e)]
        parts = t.split(".")
        for i in range(len(parts) - 1, 0, -1):  # `foo_lemma.trans`, `TwistExpr.fraction.symm`
            e = resolve(".".join(parts[:i]), ctx_ns)
            if e: return [(0, len(".".join(parts[:i])), e)]
        if len(parts) < 2 or not parts[0] or (parts[0][0].isupper() and parts[0] not in (vt or {})): return []
        out, off = [], len(parts[0]) + 1
        T = (vt or {}).get(parts[0])
        for p in parts[1:]:
            e = by_full.get(T + "." + p) if T else None
            if not e: e = method(p)
            if e: out.append((off, len(p), e)); T = ret_type(e)
            else: T = None
            off += len(p) + 1
        return out

    def ml_name(t):
        ps = t.split(".")
        # `Finset.univ.image`: link the first two components (a term, then a method on it)
        return ".".join(ps[:2]) if len(ps) > 2 and ps[1][:1].islower() else t

    for d in decls:
        d["statement"], d["proof"] = cut(d["text"], d["kind"])
    for d in decls:
        stmt, proof = d["statement"], d["proof"]
        vt = var_types(d); d["vt"] = vt
        meaning_text = stmt if d["kind"] == "theorem" else d["text"]
        def deps(text):
            out = []
            clean = "\n".join(strip_comments(text.split("\n")))
            for m in TOK.finditer(clean):
                if m.start() and clean[m.start() - 1] == ".": continue  # x.foo: a field/method, not a name
                t = m.group(0).rstrip(".")
                for _, _, e in resolve_tok(t, d["ns"], vt):
                    if e is not d and e["id"] not in out: out.append(e["id"])
            return out
        d["meaningDeps"] = deps(meaning_text)
        d["proofDeps"] = [x for x in deps(proof) if x not in d["meaningDeps"]] if d["kind"] == "theorem" else []
        ml = []
        for t in TOK.findall("\n".join(strip_comments(meaning_text.split("\n")))):
            t = t.rstrip(".")
            if is_mathlib(t) and not resolve(t, d["ns"]):
                n = ml_name(t)
                if "_" not in n.rsplit(".", 1)[-1] and n not in ml: ml.append(n)
        d["mathlib"] = ml
    ids = {d["id"]: d for d in decls}
    for h in HEADS:
        if h not in ids: raise SystemExit(f"headline {h} not found")
    used = {d["id"]: [] for d in decls}
    for e in decls:
        for x in e["meaningDeps"] + e["proofDeps"]: used[x].append(e["id"])
    dist = {h: 0 for h in HEADS}
    frontier = list(dist)
    while frontier:
        nxt = []
        for i in frontier:
            for j in ids[i]["meaningDeps"] + ids[i]["proofDeps"]:
                if j not in dist: dist[j] = dist[i] + 1; nxt.append(j)
        frontier = nxt
    out = []
    for d in sorted(decls, key=lambda d: d["id"]):
        out.append({"id": d["id"], "name": d["name"], "kind": d["kind"], "file": d["file"],
                    "module": d["file"].rsplit("/", 1)[-1][:-5], "line": d["line"], "endLine": d["endLine"],
                    "statement": d["statement"], "variables": [], "truncated": False,
                    "mathlib": d["mathlib"], "meaningDeps": d["meaningDeps"], "proofDeps": d["proofDeps"],
                    "usedBy": sorted(set(used[d["id"]])), "depth": dist.get(d["id"]), "extracted": False})
    json.dump(out, open(os.path.join(OUT, "decls.json"), "w", encoding="utf-8"), indent=1, ensure_ascii=False)

    # Heuristic xref (same format as build_xref.py) for every rendered .lean file.
    names, mods, ni, mi = [], [], {}, {}
    def nix(n):
        if n not in ni: ni[n] = len(names); names.append(n)
        return ni[n]
    def mix(m):
        if m not in mi: mi[m] = len(mods); mods.append(m)
        return mi[m]
    xfiles = {}
    for rel in files:
        rawb = open(os.path.join(ROOT, rel), "rb").read()
        text = rawb.decode("utf-8")
        here = [d for d in decls if d["file"] == rel]
        raw = text.split("\n")
        code_lines = strip_comments(raw)
        # namespace in force at each line
        ns, nsl = [], []
        for ln in raw:
            if m := re.match(r"^namespace\s+(\S+)", ln): ns.append(m.group(1))
            elif (m := re.match(r"^end\s+(\S+)\s*$", ln)) and ns and ns[-1] == m.group(1): ns.pop()
            nsl.append(".".join(ns))
        refs = []
        owner = {}
        for d in here:
            for l in range(d["line"] - 1, d["endLine"]): owner[l] = d
        for l0, code in enumerate(code_lines):
            for m in TOK.finditer(code):
                if m.start() and code[m.start() - 1] == ".": continue
                t = m.group(0).rstrip(".")
                c0 = len(raw[l0][:m.start()].encode("utf-16-le")) // 2
                c1 = c0 + len(t.encode("utf-16-le")) // 2
                hits = resolve_tok(t, nsl[l0], owner[l0]["vt"] if l0 in owner else None)
                u = lambda a: c0 + len(t[:a].encode("utf-16-le")) // 2
                for a, n, e in hits:
                    if not (e["file"] == rel and e["line"] == l0 + 1):
                        refs.append([l0, u(a), u(a + n), nix(e["name"]), mix("project")])
                if not hits and is_mathlib(t):
                    refs.append([l0, c0, c1, nix(ml_name(t)), mix("Mathlib")])
        xfiles[rel] = {"sha256": hashlib.sha256(rawb).hexdigest(),
                       "decls": [[nix(d["name"]), d["line"] - 1, d["endLine"] - 1] for d in here],
                       "refs": refs}
    json.dump({"version": 1, "heuristic": True, "names": names, "mods": mods, "files": xfiles},
              open(os.path.join(OUT, "xref.json"), "w", encoding="utf-8"), separators=(",", ":"), ensure_ascii=False)
    print(f"decls: {len(out)} ({sum(1 for d in out if d['depth'] is not None)} reachable); xref: {len(xfiles)} files, {sum(len(v['refs']) for v in xfiles.values())} refs")


if __name__ == "__main__":
    main()
