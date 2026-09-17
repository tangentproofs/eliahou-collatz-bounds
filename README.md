# eliahou-collatz-bounds

A Lean 4 formalization of Eliahou's 1993 results on Collatz cycle lengths
(*The 3x+1 problem: new lower bounds on nontrivial cycle lengths*,
Discrete Mathematics 118).

Notes on the math: For detailed notes about the mathematics, see
[Collatz/README.md](Collatz/README.md).

## Scope

This repository formalises **Eliahou's Theorem 1.1 in full linear form**:

> For an exact (injective) compressed Collatz cycle Ω with `min Ω > 2^40`,
>
> `Card Ω = 301994·a + 17087915·b + 85137581·c`
>
> for some `a, b, c ≥ 0` with `b > 0` and `a·c = 0`.

As a corollary, every such cycle has length at least **17,087,915**.

Paper-facing statements live in `Results.lean` and `Collatz/LinearForm.lean`.
The structure `ExactCollatzCycle` / injectivity hypothesis bridges Lean's
indexed `CollatzCycle L` to the paper's `Card Ω`.

Large power comparisons and Farey identities are proved with `norm_num`
(with a raised `exponentiation.threshold`); no `native_decide` remains in the
Lean sources.

## Building

This project depends on **Mathlib** (`v4.28.0`). Building Mathlib from source
takes a very long time, so you should use pre-built caches instead.

### Prerequisites

- [Lean 4](https://lean-lang.org/lean4/doc/setup.html) (v4.28.0, via `elan`)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (bundled with Lean)

### Steps

```bash
# 1. Clone the repo
git clone https://github.com/tangentproofs/eliahou-collatz-bounds.git
cd eliahou-collatz-bounds

# 2. Download pre-built Mathlib oleans (this is the key step!)
lake exe cache get

# 3. Build the project
lake build
```

The `lake exe cache get` command downloads pre-compiled `.olean` files for
Mathlib and its dependencies, so you don't have to build them from scratch
(which can take hours).

If `lake exe cache get` fails, make sure you have `curl` or `wget` available
and that your Lean toolchain version matches the one in `lean-toolchain`.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
