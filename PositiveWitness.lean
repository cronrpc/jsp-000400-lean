import Quantifiers

/-!
Elementary conversion of nonzero integer small values into positive natural
witnesses. The 3–4–5 identity removes zero coordinates at the cost of a factor
25 in the error. This familiar reduction also occurs in the public discussion
of Erdős problem 496. The small-values theorem is proved in `FinalTheorem`.
-/

namespace JSP400

/-- The integer small-values statement established in `FinalTheorem`. -/
def SmallValues (α : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ a b c : ℤ,
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
    0 < |value α a b c| ∧ |value α a b c| < δ

private theorem natAbs_sq (a : ℤ) :
    (a.natAbs : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

private theorem int_sq_ge_one {a : ℤ} (ha : a ≠ 0) :
    (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
  have : (1 : ℤ) ≤ a ^ 2 := by
    have := sq_pos_of_ne_zero ha
    omega
  exact_mod_cast this

/-- If a small-value witness has a zero coordinate, the Pythagorean identity
produces a positive witness without changing the parameter. -/
theorem positive_witness_of_integer {α ε : ℝ} {a b c : ℤ}
    (hab : a ≠ 0 ∨ b ≠ 0) (hc : c ≠ 0)
    (hε : 25 * |value α a b c| < ε) : HasApproximation α ε := by
  by_cases hzero : a = 0 ∨ b = 0
  · let n : ℕ := a.natAbs + b.natAbs
    have hn : 0 < n := by
      rcases hab with ha | hb
      · exact lt_of_lt_of_le (Int.natAbs_pos.mpr ha) (Nat.le_add_right _ _)
      · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hb) (Nat.le_add_left _ _)
    have hnsq : (n : ℝ) ^ 2 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      rcases hzero with rfl | rfl <;> simp [n]
    refine ⟨3 * n, 4 * n, 5 * c.natAbs,
      by omega, by omega, Nat.mul_pos (by norm_num) (Int.natAbs_pos.mpr hc), ?_⟩
    have heq : value α (3 * n) (4 * n) (5 * c.natAbs) =
        25 * value α a b c := by
      dsimp [value]
      calc
        _ = 25 * (n : ℝ) ^ 2 - 25 * α * (c.natAbs : ℝ) ^ 2 := by ring
        _ = _ := by rw [hnsq, natAbs_sq]; ring
    push_cast
    rw [heq, abs_mul]
    norm_num
    exact hε
  · have ha : a ≠ 0 := fun h => hzero (Or.inl h)
    have hb : b ≠ 0 := fun h => hzero (Or.inr h)
    refine ⟨a.natAbs, b.natAbs, c.natAbs,
      Int.natAbs_pos.mpr ha, Int.natAbs_pos.mpr hb, Int.natAbs_pos.mpr hc, ?_⟩
    simp only [value, natAbs_sq]
    dsimp [value] at hε
    nlinarith [abs_nonneg ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 - α * (c : ℝ) ^ 2)]

/-- Positive witnesses follow from the integer small-values statement. -/
theorem approximation_of_small_values {α : ℝ} (hα : 0 < α)
    (hsmall : SmallValues α) {ε : ℝ} (hε : 0 < ε) : HasApproximation α ε := by
  obtain ⟨a, b, c, hnz, _, herr⟩ :=
    hsmall (min 1 (min α (ε / 25))) (by positivity)
  have herr1 : |value α a b c| < 1 := herr.trans_le (min_le_left _ _)
  have herrα : |value α a b c| < α :=
    herr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have herrε : 25 * |value α a b c| < ε := by
    have := herr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hc : c ≠ 0 := by
    intro h
    subst c
    have hab : a ≠ 0 ∨ b ≠ 0 := by simpa using hnz
    have hsq : (1 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      rcases hab with ha | hb
      · nlinarith [int_sq_ge_one ha, sq_nonneg (b : ℝ)]
      · nlinarith [int_sq_ge_one hb, sq_nonneg (a : ℝ)]
    simp only [value, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      sub_zero, abs_of_nonneg (by positivity : 0 ≤ (a : ℝ)^2 + (b : ℝ)^2)] at herr1
    linarith
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    have hsq := int_sq_ge_one hc
    have heq : |value α (0 : ℤ) (0 : ℤ) c| = α * (c : ℝ) ^ 2 := by
      simp [value, abs_of_nonneg hα.le]
    rw [heq] at herrα
    nlinarith
  exact positive_witness_of_integer hab hc herrε

/-- Equivalence of the small-values and positive-witness formulations. -/
theorem small_values_iff_approximation {α : ℝ} (hα : 0 < α) (hi : Irrational α) :
    SmallValues α ↔ ∀ ε : ℝ, 0 < ε → HasApproximation α ε := by
  constructor
  · exact fun h ε hε => approximation_of_small_values hα h hε
  · intro h δ hδ
    obtain ⟨x, y, z, hx, hy, hz, herr⟩ := h δ hδ
    refine ⟨x, y, z, Or.inl (by exact_mod_cast Nat.ne_of_gt hx), ?_, ?_⟩
    · simpa only [Int.cast_natCast] using abs_pos.mpr (value_ne_zero hi x y z hz)
    · simpa only [Int.cast_natCast] using herr

end JSP400
