# eliahou-collatz

A Lean 4 formalization of results from Eliahou's work on the Collatz conjecture.

Notes on the math: For detailed notes about the mathematics, see [Collatz/README.md](Collatz/README.md).

## Building

This project depends on **Mathlib** (`v4.28.0`). Building Mathlib from source
takes a very long time, so you should use pre-built caches instead.

### Prerequisites

- [Lean 4](https://lean-lang.org/lean4/doc/setup.html) (v4.28.0, via `elan`)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (bundled with Lean)

### Steps

```bash
# 1. Clone the repo
git clone https://github.com/tangentstorm/eliahou-collatz.git
cd eliahou-collatz

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