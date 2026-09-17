import LatticeSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Matrix.Normed

/-!
A compact set of actual unimodular matrices has a uniform positive lower bound
on its nonzero lattice vectors. This is the elementary representative-level
compactness direction; compact lifting from the quotient is a separate step.
-/

namespace JSP400

open scoped Matrix.Norms.Elementwise

theorem integerVector_norm_ge_one (v : IntegerVector3) (hv : v ≠ 0) :
    1 ≤ ‖integerVector v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hiabs : (1 : ℤ) ≤ |v i| := by
    have := abs_pos.mpr hi
    omega
  have hreal : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast hiabs
  have hnorm := norm_le_pi_norm (integerVector v) i
  simpa only [Real.norm_eq_abs, integerVector] using hreal.trans hnorm

/-- The factor 3 is the number of terms in each row, with entrywise sup norms. -/
theorem matrix_mulVec_norm_le (M : Matrix (Fin 3) (Fin 3) ℝ) (v : Vector3) :
    ‖M.mulVec v‖ ≤ 3 * ‖M‖ * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j : Fin 3, M i j * v j‖ ≤ _
  calc
    _ ≤ ∑ j : Fin 3, ‖M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖M‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i))
        (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem compact_representatives_lower_bound {C : Set SL3} (hC : IsCompact C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ C, ∀ v : IntegerVector3, v ≠ 0 →
      ε ≤ ‖g • integerVector v‖ := by
  have hcont : Continuous (fun g : SL3 => ‖g⁻¹.val‖) := by
    exact continuous_norm.comp (continuous_subtype_val.comp continuous_inv)
  obtain ⟨B, hB⟩ := hC.bddAbove_image hcont.continuousOn
  let A : ℝ := max 1 B
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨1 / (3 * A), by positivity, ?_⟩
  intro g hg v hv
  have hBg : ‖g⁻¹.val‖ ≤ A :=
    (hB (Set.mem_image_of_mem _ hg)).trans (le_max_right _ _)
  have hmul := matrix_mulVec_norm_le g⁻¹.val (g • integerVector v)
  change ‖g⁻¹ • (g • integerVector v)‖ ≤ _ at hmul
  rw [inv_smul_smul] at hmul
  have hlow := integerVector_norm_ge_one v hv
  apply (div_le_iff₀ (show 0 < 3 * A by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hBg (norm_nonneg (g • integerVector v))]

end JSP400
