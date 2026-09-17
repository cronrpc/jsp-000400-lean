import TernaryForm
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace JSP400

open Matrix

/-- Margulis's reference form `2u₀u₂ - u₁²`. -/
noncomputable def standardForm : QuadraticForm ℝ (Fin 3 → ℝ) :=
  (2 : ℝ) • QuadraticMap.proj 0 2 - QuadraticMap.proj 1 1

@[simp] theorem standardForm_apply (v : Fin 3 → ℝ) :
    standardForm v = 2 * v 0 * v 2 - v 1 ^ 2 := by
  simp [standardForm, QuadraticMap.proj, pow_two, mul_assoc]

/-- An explicit change of variables before determinant normalization. -/
noncomputable def changeMatrix (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, Real.sqrt α; 0, 1, 0; -(1 / 2), 0, Real.sqrt α / 2]

theorem changeMatrix_det (α : ℝ) : (changeMatrix α).det = Real.sqrt α := by
  simp [changeMatrix, Matrix.det_fin_three]
  ring

theorem standardForm_changeMatrix {α : ℝ} (hα : 0 ≤ α) (v : Fin 3 → ℝ) :
    standardForm ((changeMatrix α).mulVec v) = -ternaryForm α v := by
  simp [standardForm_apply, ternaryForm_apply, changeMatrix,
    dotProduct, Fin.sum_univ_succ, value]
  nlinarith [Real.sq_sqrt hα]

/-- The reciprocal cube root of the initial determinant. -/
noncomputable def determinantScale (α : ℝ) : ℝ :=
  ((Real.sqrt α) ^ ((3 : ℝ)⁻¹))⁻¹

theorem determinantScale_pos {α : ℝ} (hα : 0 < α) :
    0 < determinantScale α := by
  exact inv_pos.mpr (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hα) _)

theorem determinantScale_cube {α : ℝ} (hα : 0 < α) :
    determinantScale α ^ 3 * Real.sqrt α = 1 := by
  unfold determinantScale
  have hc : ((Real.sqrt α) ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = Real.sqrt α := by
    simpa using Real.rpow_inv_natCast_pow (Real.sqrt_nonneg α)
      (by norm_num : (3 : ℕ) ≠ 0)
  rw [inv_pow, hc]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hα))

/-- A genuine element of SL(3,ℝ), not merely an invertible matrix. -/
noncomputable def standardizingSL (α : ℝ) (hα : 0 < α) :
    Matrix.SpecialLinearGroup (Fin 3) ℝ :=
  ⟨determinantScale α • changeMatrix α, by
    rw [Matrix.det_smul, changeMatrix_det]
    simpa using determinantScale_cube hα⟩

/-- This is the exact scalar relation after determinant-one normalization. -/
theorem standardForm_standardizingSL {α : ℝ} (hα : 0 < α) (v : Fin 3 → ℝ) :
    standardForm ((standardizingSL α hα : Matrix (Fin 3) (Fin 3) ℝ).mulVec v) =
      -(determinantScale α ^ 2) * ternaryForm α v := by
  change standardForm ((determinantScale α • changeMatrix α).mulVec v) = _
  rw [Matrix.smul_mulVec, QuadraticMap.map_smul, standardForm_changeMatrix hα.le]
  simp only [smul_eq_mul]
  ring

end JSP400

#print axioms JSP400.standardForm_standardizingSL
