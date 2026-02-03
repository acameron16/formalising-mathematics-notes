/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  constructor
  · intro a
    exact a
  · intro b
    exact b

example : (P ↔ Q) → (Q ↔ P) := by
  intro a
  rw [a]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro a
    rw[a]
  · intro b
    rw[b]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro a b
  rw[a]
  exact b
  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro a
    obtain ⟨left, right⟩ := a
    constructor
    all_goals assumption
  · intro b
    obtain ⟨left, right⟩ := b
    constructor
    all_goals assumption

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro a
    obtain ⟨left, right⟩ := a
    constructor
    · obtain ⟨left2, right2⟩ := left
      exact left2
    · obtain ⟨left3, right3⟩ := left
      constructor
      all_goals assumption
  · intro x
    obtain ⟨left, right⟩ := x
    obtain ⟨left2, right2⟩ := right
    constructor
    · constructor
      all_goals assumption
    · exact right2

example : P ↔ P ∧ True := by
  constructor
  · intro h1
    constructor
    · exact h1
    · trivial
  · intro h2
    obtain ⟨left, right⟩ := h2
    exact left

example : False ↔ P ∧ False := by
  constructor
  · intro f
    exfalso
    exact f
  · intro h
    obtain ⟨left, right⟩ := h
    exact right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro a b
  constructor
  · intro x
    rw[a] at x
    rw[b] at x
    exact x
  · intro y
    rw[a]
    rw[b]
    exact y

example : ¬(P ↔ ¬P) := by
  change (P ↔ ¬P) → False
  intro h
  obtain ⟨left, right⟩ := h
