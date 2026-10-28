# Contributing explainers

The plain-English site lives in `learn/` and is served at <https://tangentproofs.github.io/eliahou-collatz-bounds/learn/>. The project homepage in `site/` is separate.

**The Lean is the ground truth.** An explainer is right only if it matches the statement exactly as written in `Collatz/`: its hypotheses, the order of its quantifiers, and what is `∃` and what is `∀`. Don't import claims from the paper that the Lean doesn't make. If you aren't sure, say so under `caveats`.

The node format, progress rules and quiz rules are the same as on the other tangentproofs sites (see [star-height's CONTRIBUTING.md](https://github.com/tangentproofs/star-height/blob/main/CONTRIBUTING.md)), with these differences:

- **ids** are the full Lean names (the project has no namespace), e.g. `eliahou_theorem_1_1`, `CollatzCycle.minElem`. Look them up in `learn/data/decls.json`.
- **Edit `learn/nodes_src/collatz.py`**, not `learn/nodes/*.md`. Then run `python3 learn/tools/write_nodes.py` to regenerate the Markdown, which keeps the YAML valid. CI checks that the two agree.
- **Lead with the surprise.** A node's `summary` should start with its most surprising takeaway.
- `learn/data/decls.json` and `xref.json` are read from the source text by `learn/tools/scan_decls.py` (no Lean build). Re-run it after changing any `.lean` file.

Run `cd learn && npm ci && npm test` before opening a PR. Keep `review: draft` unless a person has checked the node against the Lean.
