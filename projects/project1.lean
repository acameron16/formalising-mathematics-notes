
import Mathlib.Tactic -- imports all the Lean tactics

/-- definition of the sequence a_n converging to t, i.e. a_n → t -/
def seq_lim (a : ℕ → ℝ) (t : ℝ) : Prop := ∀ ε > 0, ∃ B : ℕ, ∀n, B ≤ n → |a n - t| < ε

-- For rewriting purposes also from section 2, sheet 3
theorem seq_lim_def {a : ℕ → ℝ} {t : ℝ} :
  seq_lim a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀n, B ≤ n → |a n - t| < ε := by rfl

-- here is a sequence which does not converge according to the definition
-- (1, -1, 1, -1, ...)
theorem does_not_converge : ∀a:ℝ, ¬(seq_lim (fun n => (-1)^n) a) := by
  intro a h
  -- have arbitrary a ∈ ℝ and assume (-1)^n → a
  rw [seq_lim_def] at h   -- rewrite h using the definition
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num) -- specialising ε = 0.5 and thus
  -- for all n ≥ N, |(-1) ^ n - a| < 1/2
  have R1 : N ≤ 2*N := by linarith
  have R2 : N ≤ 2*N + 1 := by linarith  -- useful to work with

  have S1 : |(-1) ^ (2*N) - a| < 1/2 := hN (2*N) R1
  have S2 : |(-1) ^ (2*N + 1) - a| < 1/2 := hN (2*N + 1) R2

  rw [pow_mul] at S1
  rw [pow_succ, pow_mul] at S2
  norm_num at *
  -- using the triangle inqeuality
  have P1 : |(1+a)+(1-a)| ≤ |1+a| + |1-a| := by apply abs_add_le
  have P0 : |(1+a)+(1-a)| = 2 := by
    ring_nf
    norm_num
  rw [P0] at P1
  have S0 : -(1+a) = -1-a := by ring
  rw [← S0, abs_neg] at S2 -- |-x| = |x|
  have Z : |1 + a| + |1 - a| < 1/2 + 1/2 := add_lt_add S2 S1
  norm_num at Z
  have Z1 : (2:ℝ) < 1 := by -- obtain 2 < 1
    apply lt_of_le_of_lt P1 Z
  norm_num at Z1 -- exact the contradiction

-- If two real numbers are arbitrarily close, they are equal.
-- This lemma will be used later
lemma arb_eps (x y : ℝ) : (∀ε>0, |x-y| < ε) → x = y := by
  intro h  -- let ε > 0 be arbitrary
  specialize h |x-y|
  -- it remains to prove |x - y| > 0
  by_contra P -- suppose x ≠ y
  have Q : |x-y| > 0 := by exact abs_sub_pos.mpr P  -- positive definiteness of abs
  exact (lt_self_iff_false |x - y|).mp (h Q)  -- |x-y| < |x-y| is a contradiction


-- a convergent sequence has a unique limit
theorem unique_lim {a : ℕ → ℝ} {x y : ℝ}
  (h1 : seq_lim a x) (h2 : seq_lim a y) : x = y := by
  --Suffices to prove |x-y| < ε
  apply arb_eps
  intro ε hε
 -- a(n) is eventually within ε/2 of x and y
  obtain ⟨N1, hN1⟩ := h1 (ε/2) (by linarith)
  obtain ⟨N2, hN2⟩ := h2 (ε/2) (by linarith)
  let N := max N1 N2

  have L1 : N1 ≤ N := by exact Nat.le_max_left N1 N2
  have L2 : N2 ≤ N := by exact Nat.le_max_right N1 N2
  -- holds true for N1 ≤ N ≤ n
  have K1 : ∀ (n : ℕ), N ≤ n → |a n - x| < ε / 2 := by
    intro n hn
    have L : N1 ≤ n := by apply le_trans L1 hn
    specialize hN1 n
    have Z : |a n - x| < ε / 2 := hN1 L
    exact Z
  -- and for N2 ≤ N ≤ n
  have K2 : ∀ (n : ℕ), N ≤ n → |a n - y| < ε / 2 := by
    intro n hn
    have L : N2 ≤ n := by apply le_trans L2 hn
    specialize hN2 n
    have Z : |a n - y| < ε / 2 := hN2 L
    exact Z
  -- adding the inequalities preparing to use tbe triangle inequality
  have K3 : ∀ (n : ℕ), N ≤ n → |a n - x| + |a n - y| < ε / 2 + ε / 2 := by
    intro n hn
    specialize K1 n hn
    specialize K2 n hn
    exact add_lt_add K1 K2
  ring_nf at K3
  -- rewriting |x-y| and use triangle inequality
  have P0 : ∀ (n : ℕ), |x - y| = |(x - a n) + (a n - y)| := by
    ring_nf
    norm_num
  have P1 : ∀ (n : ℕ), |(x - a n) + (a n - y)| ≤ |x - a n| + |a n - y| := by
    exact fun n ↦ abs_add_le (x - a n) (a n - y)
  --combining previous statements
  have TI : ∀ (n : ℕ), |x - y| ≤ |x - a n| + |a n - y| := by
    intro n
    specialize P0 n
    rw [P0]
    exact abs_add_le (x - a n) (a n - y)
  have I : ∀ (n : ℕ), N ≤ n → |x - a n| + |a n - y| < ε → |x - y| < ε := by
    intro n hn h
    specialize TI n
    exact lt_of_le_of_lt TI h
  have Z : ∀ (n : ℕ), N ≤ n → |x-y| < ε := by
    intro n hn
    specialize I n hn
    specialize K3 n
    have Z1 : |a n - x| + |a n - y| < ε := K3 hn
    have R : |a n - x| = |x - a n| := by exact abs_sub_comm (a n) x
    rw [← R] at I
    have Z2 : |x - y| < ε := I Z1
    exact Z2
  specialize Z (2*N)
  have A : N ≤ 2 * N := by linarith
  have A1 : |x - y| < ε := Z A
  exact A1

/-- definition of a bounded sequence -/
def BoundedSeq (a : ℕ → ℝ) : Prop := ∃ M : ℝ, ∀ n : ℕ, |a n| ≤ M

-- for rewriting in proofs
theorem bdd_seq_def {a : ℕ → ℝ} : BoundedSeq a ↔ ∃ M : ℝ, ∀ n : ℕ, |a n| ≤ M := by rfl

-- convergent => bounded
theorem conv_imp_bdd {a : ℕ → ℝ} : (∃ t : ℝ, seq_lim a t) → BoundedSeq a := by
  intro h
  rcases h with ⟨t, h⟩  -- assume a(n) converges to t ∈ ℝ
  specialize h 1  -- use ε = 1
  have hc : ∃ B, ∀ (n : ℕ), B ≤ n → |a n - t| < 1 := h (by linarith) -- modus ponens

  obtain ⟨B,hB⟩ := hc  -- we have all terms after B within 1 of t
  let X : Finset ℝ := Finset.image |a| (Finset.range (B+1))
  -- this is the (finite) set X = {|a n| : n = 0, ..., B}

  have G : X.Nonempty := by grind only [Finset.image_nonempty, = Finset.nonempty_range_iff]
  -- this proves that X is non-empty

  use max (Finset.max' X G) (|t|+1) -- the candidate M = max{a(0), ..., a(B), |t|+1}
  -- proof candidate works
  intro n
  by_cases P : B ≤ n -- split into cases 1) B ≤ n
  · specialize hB n
    -- this is a proof of |a n| ≤ |t| + 1
    have P1 : |a n - t| < 1 := hB P
    have P2 : |a n| = |(a n - t) + t| := by ring_nf
    have P3 : |a n| ≤ |a n - t| + |t| := by --triangle inequality
      rw [P2]
      exact abs_add_le (a n - t) t
    have P4 : |a n - t| + |t| < |t| + 1 := by
      rw [add_comm]
      exact add_lt_add_right (hB P) |t|
    have P5 : |a n - t| + |t| ≤ |t| + 1 := by exact Std.le_of_lt P4
    have P6 : |a n| ≤ |t| + 1 := by
      exact Std.IsPreorder.le_trans |a n| (|a n - t| + |t|) (|t| + 1) P3 P5
    exact le_sup_of_le_right P6
  --2) B > n
  · apply Nat.lt_of_not_le at P
    apply Nat.le_of_succ_le at P
    have P1 : n ∈ Finset.range (B + 1) := by exact Finset.mem_range_succ_iff.mpr P
    have P2 : |a n| ∈ X := by exact Finset.mem_image_of_mem |a| P1
    have P3 : |a n| ≤ X.max' G := by exact Finset.le_max' X |a n| P2
    exact le_sup_of_le_left P3
    -- |a n| ∈ X → |a n| ≤ max X

/-- definition: f is continuous at a ∈ ℝ -/
def continuous_at_a (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, (x : ℝ) → |x - a| < δ → |f x - f a| < ε

-- rewrite in theorems
theorem cts_at_a_def {f : ℝ → ℝ} {a : ℝ} : continuous_at_a f a ↔
  ∀ ε, 0 < ε → ∃ δ > 0, (x : ℝ) → |x - a| < δ → |f x - f a| < ε := by rfl

/-- definition: f is continuous on ℝ -/
def continuous_on_R (f : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, continuous_at_a f a

-- any linear function is continuous on ℝ
theorem linear_cts {m c : ℝ} : continuous_on_R (fun x => m*x + c) := by
  intro a ε hε -- arbitrary a ∈ ℝ, ε > 0
  ring_nf
  by_cases P : m = 0
  -- first case m = 0
  · use 1
    rw [P]
    norm_num
    intro x h
    exact hε
  -- second case m ≠ 0
  · use ε/|m|
    field_simp
    ring_nf
    field_simp
    norm_num at *
    constructor
    · exact hε
    · intro x
      rw [mul_comm]
      tauto

#lint
