/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext t
  constructor
  · intro h
    rcases h with (left | right)
    all_goals assumption
  · intro h
    left
    exact h

example : A ∩ A = A := by
  ext t
  constructor
  · intro h
    rcases h with ⟨left, right⟩
    exact right
  · intro h
    constructor
    all_goals assumption

example : A ∩ ∅ = ∅ := by
  ext t
  constructor
  · intro h
    rcases h with ⟨left, right⟩
    exact right
  · intro h
    constructor
    · exfalso
      exact h
    · exact h

example : A ∪ univ = univ := by
  ext t
  constructor
  · intro h
    trivial
  · intro h
    right
    exact h

example : A ⊆ B → B ⊆ A → A = B := by
  intro h i
  ext t
  constructor
  · intro j
    apply h at j
    exact j
  · intro k
    apply i at k
    exact k

example : A ∩ B = B ∩ A := by
  ext t
  constructor
  · intro h
    rcases h with ⟨left, right⟩
    constructor
    all_goals assumption
  · intro h
    rcases h with ⟨left,right⟩
    constructor
    all_goals assumption

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext t
  constructor
  · intro h
    rcases h with ⟨h1,h2,h3⟩
    constructor
    · constructor
      · exact h1
      · exact h2
    · exact h3
  · intro h
    rcases h with ⟨h1,h2⟩
    rcases h1 with ⟨left,right⟩
    constructor
    · exact left
    · constructor
      all_goals assumption


example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext t
  constructor
  · intro h
    rcases h with (h1 | h2 | h3)
    left
    left
    exact h1
    left
    right
    exact h2
    right
    exact h3
  · intro h
    rcases h with (h1 | h2)
    rcases h1 with (h3 | h4)
    left
    exact h3
    right
    left
    exact h4
    right
    right
    exact h2

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext t
  constructor
  · intro h
    constructor
    · rcases h with (left | right)
      left
      exact left
      rcases right with ⟨h1,h2⟩
      right
      exact h1
    · rcases h with (left | right)
      left
      exact left
      rcases right with ⟨h3,h4⟩
      right
      exact h4
  · intro h
    rcases h with ⟨h1,h2⟩
    by_cases P : t ∈ A
    left
    exact P

    right
    constructor
    · rcases h1 with (left | right)
      apply P at left
      exfalso
      exact left
      exact right
    · rcases h2 with (left | right)
      apply P at left
      exfalso
      exact left
      exact right

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext t
  constructor
  · intro h
    rcases h with ⟨h1,h2⟩
    rcases h2 with (h3|h4)
    left
    constructor
    · assumption
    · assumption
    right
    constructor
    · assumption
    · assumption
  · intro h
    constructor
    rcases h with (h1|h2)
    rcases h1 with ⟨p,q⟩
    exact p
    rcases h2 with ⟨p,q⟩
    exact p
    rcases h with (h1|h2)
    rcases h1 with ⟨p,q⟩
    left
    exact q
    rcases h2 with ⟨p,q⟩
    right
    exact q
