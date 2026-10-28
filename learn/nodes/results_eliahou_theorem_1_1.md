---
id: results_eliahou_theorem_1_1
title: 'Results.lean: the paper-facing statement of Theorem 1.1'
summary: '**The surprise:** Results.lean, the file meant for checking, restates each theorem by hand and proves
  it by citing the real one, so a reader can audit the statements in 64 lines.'
review: draft
authors:
- grok-bot
quiz:
- q: Is the Results.lean statement identical to the one in LinearForm.lean?
  type: choice
  choices:
  - Yes, up to names
  - No, it is weaker
  answer: 0
  explain: Same hypotheses and conclusion.
- q: How is it proved?
  type: choice
  choices:
  - By citing eliahou_theorem_1_1
  - From scratch
  answer: 0
  explain: '`:= eliahou_theorem_1_1 c hinj hmin`.'
- q: Why have such a file?
  type: choice
  choices:
  - To audit statements without reading proofs
  - For speed
  answer: 0
  explain: That is its role.
---
## Plain English

**Theorem (`results_eliahou_theorem_1_1`).** The same statement as [`eliahou_theorem_1_1`](#/node/eliahou_theorem_1_1), restated in Results.lean (lines 50-56) and proved by applying it.

Results.lean is a thin "comparator surface": ten theorems, each a restatement of a result in `Collatz/`, so the statements can be read without the proofs.
