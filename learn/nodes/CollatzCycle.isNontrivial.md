---
id: CollatzCycle.isNontrivial
title: '"Nontrivial": defined but never used'
summary: '**The surprise:** the project defines "nontrivial" as min > 2, but no theorem uses it. The headlines assume
  min > 2⁴⁰ instead.'
review: draft
authors:
- grok-bot
quiz:
- q: Do any theorems use `isNontrivial`?
  type: choice
  choices:
  - 'No'
  - Yes, all headlines
  answer: 0
  explain: It is unused.
- q: What would be needed to go from isNontrivial to min > 2⁴⁰?
  type: choice
  choices:
  - A (formalized) check that all n ≤ 2⁴⁰ reach 1
  - Nothing
  answer: 0
  explain: That check is not in the Lean.
- q: isNontrivial means
  type: choice
  choices:
  - min > 2
  - min > 2⁴⁰
  answer: 0
  explain: As defined.
---
## Plain English

**Definition (`c.isNontrivial`).** 2 < c.minElem.

Our source scan finds no declaration that mentions it. The headline theorems use the much stronger, explicit hypothesis `2 ^ 40 < c.minElem`, and the step from "nontrivial" to "min > 2⁴⁰" (computer verification of the conjecture up to 2⁴⁰) is not formalized. Its docstring says as much.
