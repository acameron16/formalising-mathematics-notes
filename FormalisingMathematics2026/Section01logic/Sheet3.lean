/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro dP
  change True → False at dP
  apply dP
  trivial

example : False → ¬True := by
  intro a
  change True → False
  intro b
  assumption

example : ¬False → True := by
  intro a
  trivial

example : True → ¬False := by
  intro a
  change False → False
  intro a
  assumption

example : False → ¬P := by
  intro a
  change P → False
  intro b
  assumption

example : P → ¬P → False := by
  intro a b
  change P → False at b
  apply b at a
  assumption

example : P → ¬¬P := by
  intro a b
  change P → False at b
  apply b at a
  assumption

example : (P → Q) → ¬Q → ¬P := by
  intro a b c
  change Q → False at b
  apply a at c
  apply b at c
  assumption

example : ¬¬False → False := by
  intro a
  change ¬False → False at a
  apply a
  intro b
  assumption

example : ¬¬P → P := by
  intro a
  change ¬P → False at a
  by_contra b
  apply a at b
  assumption

example : (¬Q → ¬P) → P → Q := by
  intro a b
  by_contra x
  apply a at x
  change P → False at x
  apply x at b
  assumption
