---
id: farey_intermediate_coeffs
title: 'Between Farey neighbours: a positive combination'
summary: '**The surprise:** every fraction strictly between Farey neighbours is literally built from them: x = a·p
  + b·p'' and y = a·q + b·q'' with a, b ≥ 1.'
review: draft
authors:
- grok-bot
quiz:
- q: Write 2/3 between 1/2 and 1/1 as a combination
  type: choice
  choices:
  - a = 1, b = 1
  - a = 2, b = 1
  - a = 1, b = 2
  answer: 0
  explain: 2 = 1·1 + 1·1 and 3 = 1·2 + 1·1.
- q: Are a and b allowed to be 0?
  type: choice
  choices:
  - No, both are positive
  - 'Yes'
  answer: 0
  explain: The conclusion has `0 < a ∧ 0 < b`.
- q: How are a and b found?
  type: choice
  choices:
  - Explicit formulas p'y − q'x and qx − py
  - By search
  - By choice
  answer: 0
  explain: '`refine ⟨p'' * y - q'' * x, q * x - p * y, …⟩`.'
---
## Plain English

**Theorem (`farey_intermediate_coeffs`).** Under the hypotheses of [`farey_pair_bound`](#/node/farey_pair_bound), there are positive a, b with x = a·p + b·p' and y = a·q + b·q'.

The proof gives them explicitly: a = p'y − q'x and b = qx − py, and checks the identities using p'q − pq' = 1. This sharper form is what gives the *linear form* in [Theorem 1.1](#/node/eliahou_theorem_1_1).
