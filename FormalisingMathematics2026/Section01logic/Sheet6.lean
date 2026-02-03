/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro h
  right
  exact h

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ h2 h3
  cases hPoQ with
  | inl h =>
    apply h2
    exact h
  | inr h =>
    apply h3
    exact h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ h2 h3
  obtain h | h := hPoQ
  · apply h2
    exact h
  · apply h3
    exact h

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (h | h) h1 h2
  · apply h1
    exact h
  · apply h2
    exact h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (hP | hQ)
  · right
    exact hP
  · left
    exact hQ


-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro ((hP | hQ) | hR)
    · left
      exact hP
    · right
      left
      exact hQ
    · right
      right
      exact hR
  · rintro (hP | hQ | hR)
    · left
      left
      exact hP
    · left
      right
      exact hQ
    · right
      exact hR


example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro a b
  rintro (c | d)
  · apply a at c
    left
    exact c
  · apply b at d
    right
    exact d


example : (P → Q) → P ∨ R → Q ∨ R := by
  intro a
  rintro (b | c)
  · apply a at b
    left
    exact b
  · right
    exact c

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro a b
  constructor
  · rintro (c | d)
    · rw[a] at c
      left
      exact c
    · rw[b] at d
      right
      exact d
  · rintro (e | f)
    · rw[a]
      left
      exact e
    · rw[b]
      right
      exact f

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro a
    change (P ∨ Q) → False at a
    constructor
    · change P → False
      intro b
      apply a
      left
      exact b
    · change Q → False
      intro c
      apply a
      right
      exact c
  · intro x
    obtain ⟨left, right⟩ := x
    change P ∨ Q → False
    rintro (y | z)
    · change P → False at left
      apply left at y
      exact y
    · change Q → False at right
      apply right at z
      exact z

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro a
    by_cases hP : P
    · right
      intro hQ
      apply a
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (x | y) ⟨z1, z2⟩
    · change P → False at x
      apply x
      exact z1
    · change Q → False at y
      apply y
      exact z2
