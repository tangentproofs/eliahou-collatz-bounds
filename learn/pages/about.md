# About this site

**The theorem.** Shalom Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Mathematics 118 (1993) 45–56. For the compressed Collatz map T(n) = n/2 (n even), (3n+1)/2 (n odd), a cycle whose numbers all exceed 2⁴⁰ must have length 301994a + 17087915b + 85137581c with b ≥ 1 and ac = 0, so at least 17,087,915.

**The Lean.** [tangentproofs/eliahou-collatz-bounds](https://github.com/tangentproofs/eliahou-collatz-bounds): about 900 lines of Lean 4 on Mathlib (v4.28.0), produced with [Aristotle](https://aristotle.harmonic.fun) (Harmonic) and edited by Michal Wallace. The project's own summary page is the [project home](../).

**This site** reads the formal statements back into plain English, so you can judge whether they say what the headline claims. Each node is one Lean declaration with its verbatim Lean, a plain-English reading that leads with its most surprising point, faithfulness notes, and a short quiz. Tick **I think I understand this** when you do. A node counts as understood once everything its statement mentions is understood too. The four headline theorems have step-by-step proof outlines linked to their exact lines.

The [Lean source](src/index.html) is on the site, highlighted. Names defined in the project link to their definitions, Mathlib names link to the Mathlib docs, and every "File.lean lines a–b" reference opens those exact lines.

Start with [the statements](#/start), then read the [review](#/review) and what was and wasn't [checked](#/trust).

Proof outlines and quizzes are summaries, not evidence: the Lean is the ground truth.

**Credit.** Theorem: Shalom Eliahou. Lean proof: Aristotle (Harmonic) and Michal Wallace. Explanations: drafts by Grok Bot for Michal Wallace (`review: draft`), possibly wrong. Site engine: the tangentproofs proof-site kit (star-height, subexponential-sat).
