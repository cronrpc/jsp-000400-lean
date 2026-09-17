import AffineClassification
import UnipotentOneNormalizer

/-! The positive affine quotient represented by the actual matrices V₂(b)D(t). -/

namespace JSP400

open Matrix Set
open AffineClassification
noncomputable section

theorem diagonalFlow_mul (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) :
    diagonalFlow t ht * diagonalFlow u hu = diagonalFlow (t * u) (mul_ne_zero ht hu) := by
  apply Subtype.ext
  ext i j
  change ((diagonalFlow t ht).val * (diagonalFlow u hu).val) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, Matrix.mul_apply, Fin.sum_univ_succ, _root_.mul_inv_rev, mul_comm]

def affineMatrix (g : PositiveAffine) : SL3 :=
  unipotentTwo (offset g) *
    diagonalFlow (Real.sqrt (slope g)) (ne_of_gt (Real.sqrt_pos.mpr g.property))

theorem affineMatrix_one : affineMatrix 1 = 1 := by
  simp [affineMatrix, diagonalFlow_one, unipotentTwo_zero]

theorem affineMatrix_mul (g h : PositiveAffine) : affineMatrix (g * h) = affineMatrix g * affineMatrix h := by
  have hg : 0 < slope g := g.property
  have hh : 0 < slope h := h.property
  have hs : Real.sqrt (slope g * slope h) = Real.sqrt (slope g) * Real.sqrt (slope h) :=
    Real.sqrt_mul hg.le _
  have hdiag : diagonalFlow (Real.sqrt (slope (g * h)))
      (ne_of_gt (Real.sqrt_pos.mpr (g * h).property)) =
      diagonalFlow (Real.sqrt (slope g)) (ne_of_gt (Real.sqrt_pos.mpr hg)) *
        diagonalFlow (Real.sqrt (slope h)) (ne_of_gt (Real.sqrt_pos.mpr hh)) := by
    rw [diagonalFlow_mul]
    apply Subtype.ext
    simp only [diagonalFlow, slope_mul, hs]
  unfold affineMatrix
  rw [hdiag, offset_mul, unipotentTwo_add]
  have hd := diagonalFlow_unipotentTwo (Real.sqrt (slope g))
    (ne_of_gt (Real.sqrt_pos.mpr hg)) (offset h)
  rw [Real.sq_sqrt hg.le] at hd
  simp only [mul_assoc]
  rw [← mul_assoc (diagonalFlow _ _) (unipotentTwo _) (diagonalFlow _ _), hd]
  simp only [mul_assoc]

def affineMatrixHom : PositiveAffine →* SL3 where
  toFun := affineMatrix
  map_one' := affineMatrix_one
  map_mul' := affineMatrix_mul

theorem continuous_affineMatrix : Continuous affineMatrix := by
  have hs : Continuous (fun g : PositiveAffine => Real.sqrt (slope g)) :=
    Real.continuous_sqrt.comp continuous_slope
  have hi : Continuous (fun g : PositiveAffine => (Real.sqrt (slope g))⁻¹) :=
    hs.inv₀ (fun g => ne_of_gt (Real.sqrt_pos.mpr g.property))
  unfold affineMatrix
  apply Continuous.mul
  · apply Continuous.subtype_mk
    have hb := continuous_offset
    fun_prop
  · apply Continuous.subtype_mk
    fun_prop

theorem affineMatrix_translation (b : ℝ) : affineMatrix (translation b) = unipotentTwo b := by
  simp [affineMatrix, diagonalFlow_one]

theorem affineMatrix_fixedDilation (r t : ℝ) (ht : 0 < t) :
    affineMatrix (fixedDilation r (t ^ 2) (sq_pos_of_pos ht)) =
      unipotentTwo r * diagonalFlow t (ne_of_gt ht) * (unipotentTwo r)⁻¹ := by
  have hs : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht.le
  have hdiag : diagonalFlow (Real.sqrt (t ^ 2)) (ne_of_gt (Real.sqrt_pos.mpr (sq_pos_of_pos ht))) =
      diagonalFlow t (ne_of_gt ht) := by
    apply Subtype.ext
    simp only [diagonalFlow, hs]
  change unipotentTwo ((1 - t ^ 2) * r) * diagonalFlow (Real.sqrt (t ^ 2)) _ = _
  rw [hdiag]
  have hinv : (unipotentTwo r)⁻¹ = unipotentTwo (-r) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← unipotentTwo_add, add_neg_cancel, unipotentTwo_zero]
  rw [hinv, mul_assoc, diagonalFlow_unipotentTwo, ← mul_assoc, ← unipotentTwo_add]
  congr 2
  ring

theorem affineMatrix_coordinates (s b t : ℝ) (ht : 0 < t) :
    let g := unipotentOne s * unipotentTwo b * diagonalFlow t (ne_of_gt ht)
    g.val 0 0 = t ∧ g.val 0 1 = s ∧ t * g.val 0 2 - s ^ 2 / 2 = b := by
  dsimp
  change (((unipotentOne s).val * (unipotentTwo b).val) * (diagonalFlow t _).val) 0 0 = t ∧
    (((unipotentOne s).val * (unipotentTwo b).val) * (diagonalFlow t _).val) 0 1 = s ∧
    t * (((unipotentOne s).val * (unipotentTwo b).val) * (diagonalFlow t _).val) 0 2 - s ^ 2 / 2 = b
  have hn : t ≠ 0 := ne_of_gt ht
  simp [unipotentOne, unipotentTwo, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_succ]
  field_simp
  ring

end
end JSP400
