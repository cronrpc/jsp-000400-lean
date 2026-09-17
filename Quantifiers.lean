import Core

/-!
The two inequalities in Erdős's original question are equivalent for positive
irrational parameters. This module only proves that correspondence and its
elementary consequences; it does not assume or prove the Oppenheim theorem.
-/

namespace JSP400

/-- The first of the two inequalities in Erdős I.34. -/
def HasDualApproximation (α ε : ℝ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    |α * ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) - (z : ℝ) ^ 2| < ε

def DualStatement : Prop :=
  ∀ α : ℝ, 0 < α → Irrational α →
    ∀ ε : ℝ, 0 < ε → HasDualApproximation α ε

theorem dual_value_eq (α x y z : ℝ) (hα : α ≠ 0) :
    α * (x ^ 2 + y ^ 2) - z ^ 2 = α * value α⁻¹ x y z := by
  dsimp [value]
  field_simp

theorem dual_approximation_iff {α ε : ℝ} (hα : 0 < α) :
    HasDualApproximation α ε ↔ HasApproximation α⁻¹ (ε / α) := by
  unfold HasDualApproximation HasApproximation
  simp_rw [dual_value_eq _ _ _ _ (ne_of_gt hα), abs_mul, abs_of_pos hα,
    lt_div_iff₀ hα, mul_comm α]

theorem dual_statement_iff : DualStatement ↔ PositiveStatement := by
  constructor
  · intro h α hα hi ε hε
    have h' := h α⁻¹ (inv_pos.mpr hα) hi.inv (ε / α) (div_pos hε hα)
    have h'' := (dual_approximation_iff (inv_pos.mpr hα)).mp h'
    simpa only [inv_inv, div_inv_eq_mul, div_mul_cancel₀ _ (ne_of_gt hα)] using h''
  · intro h α hα hi ε hε
    exact (dual_approximation_iff hα).mpr
      (h α⁻¹ (inv_pos.mpr hα) hi.inv (ε / α) (div_pos hε hα))

/-- An irrational coefficient prevents any zero with a positive third coordinate. -/
theorem value_ne_zero {α : ℝ} (hi : Irrational α) (x y z : ℕ) (hz : 0 < z) :
    value α x y z ≠ 0 := by
  intro h
  apply hi
  refine ⟨((x : ℚ) ^ 2 + (y : ℚ) ^ 2) / (z : ℚ) ^ 2, ?_⟩
  push_cast
  apply (div_eq_iff (pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hz))).mpr
  dsimp [value] at h
  linarith

/-- Every finite collection of positive-denominator triples stays away from zero. -/
theorem finite_error_bound {α : ℝ} (hi : Irrational α)
    (s : Finset (ℕ × ℕ × ℕ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ s, 0 < p.2.2 →
      δ ≤ |value α p.1 p.2.1 p.2.2| := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    by_cases hz : 0 < a.2.2
    · refine ⟨min δ |value α a.1 a.2.1 a.2.2|,
        lt_min hδ (abs_pos.mpr (value_ne_zero hi _ _ _ hz)), ?_⟩
      intro p hp hpz
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound _ hp hpz)
    · refine ⟨δ, hδ, ?_⟩
      intro p hp hpz
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact (hz hpz).elim
      · exact hbound _ hp hpz

/-- Arbitrarily small errors force unbounded positive denominators. -/
theorem approximation_large_denominator {α : ℝ} (hα : 0 < α) (hi : Irrational α)
    (happrox : ∀ ε : ℝ, 0 < ε → HasApproximation α ε)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ N < z ∧
      |value α x y z| < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (α * (N : ℝ) ^ 2 + 1)
  let s : Finset (ℕ × ℕ × ℕ) :=
    Finset.range M ×ˢ (Finset.range M ×ˢ Finset.range (N + 1))
  obtain ⟨δ, hδ, hbound⟩ := finite_error_bound hi s
  obtain ⟨x, y, z, hx, hy, hz, herr⟩ :=
    happrox (min ε (min 1 δ)) (lt_min hε (lt_min (by norm_num) hδ))
  refine ⟨x, y, z, hx, hy, ?_, herr.trans_le (min_le_left _ _)⟩
  by_contra hn
  have hzN : z ≤ N := Nat.le_of_not_gt hn
  have herr1 : |value α x y z| < 1 :=
    herr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have herrδ : |value α x y z| < δ :=
    herr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzN' : (z : ℝ) ≤ N := by exact_mod_cast hzN
  have hzsq : (z : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzN')
      (add_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg z))]
  have hform := (abs_lt.mp herr1).2
  dsimp [value] at hform
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hαz := mul_le_mul_of_nonneg_left hzsq hα.le
  have hxM : x < M := by
    have : (x : ℝ) < M := by nlinarith [sq_nonneg (y : ℝ)]
    exact_mod_cast this
  have hyM : y < M := by
    have : (y : ℝ) < M := by nlinarith [sq_nonneg (x : ℝ)]
    exact_mod_cast this
  have hmem : (x, y, z) ∈ s := by
    simp only [s, Finset.mem_product, Finset.mem_range]
    exact ⟨hxM, hyM, Nat.lt_succ_of_le hzN⟩
  exact (not_lt_of_ge (hbound (x, y, z) hmem hz)) herrδ

end JSP400
