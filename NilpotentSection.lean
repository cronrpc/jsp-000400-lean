import ShearFixedSpace
import DiagonalContraction
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
An explicit continuous local section of the regular nilpotent adjoint orbit.
The cyclic frame has columns q²e₂, qe₂, e₂. It is normalized to determinant one
on the open neighborhood where its determinant is positive.
-/

namespace JSP400

open Matrix Set
open scoped Topology

def nilpotentFrame (q : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(q ^ 2) 0 2, q 0 2, 0; (q ^ 2) 1 2, q 1 2, 0; (q ^ 2) 2 2, q 2 2, 1]

theorem continuous_nilpotentFrame : Continuous nilpotentFrame := by
  unfold nilpotentFrame
  fun_prop

theorem nilpotentFrame_fixedLine (t : ℝ) :
    nilpotentFrame (shearFixedLine t) = (upperUnipotent t 0 0).val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentFrame, shearFixedLine, upperUnipotent, pow_two, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem nilpotentFrame_fixedLine_det (t : ℝ) :
    (nilpotentFrame (shearFixedLine t)).det = 1 := by
  rw [nilpotentFrame_fixedLine]
  exact (upperUnipotent t 0 0).property

theorem nilpotentFrame_intertwines (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : IsNilpotent q) : nilpotentFrame q * shearFixedLine 0 = q * nilpotentFrame q := by
  have hc := (matrix3_isNilpotent_iff_cube q).mp hq
  have he (i : Fin 3) : (q ^ 3) i 2 = 0 := congrArg (fun x => x i 2) hc
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [nilpotentFrame, shearFixedLine, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals try simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals first
    | simpa [show (3 : ℕ) = 2 + 1 by rfl, pow_succ', Matrix.mul_apply,
        Fin.sum_univ_succ] using (he 0).symm
    | simpa [show (3 : ℕ) = 2 + 1 by rfl, pow_succ', Matrix.mul_apply,
        Fin.sum_univ_succ] using (he 1).symm
    | simpa [show (3 : ℕ) = 2 + 1 by rfl, pow_succ', Matrix.mul_apply,
        Fin.sum_univ_succ] using (he 2).symm

def nilpotentSectionDomain : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {q | 0 < (nilpotentFrame q).det}

theorem isOpen_nilpotentSectionDomain : IsOpen nilpotentSectionDomain :=
  isOpen_lt continuous_const continuous_nilpotentFrame.matrix_det

noncomputable def nilpotentSectionScale (q : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ((nilpotentFrame q).det ^ ((3 : ℝ)⁻¹))⁻¹

theorem nilpotentSectionScale_cube (q : nilpotentSectionDomain) :
    nilpotentSectionScale q ^ 3 * (nilpotentFrame q).det = 1 := by
  unfold nilpotentSectionScale
  have hc : ((nilpotentFrame q).det ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) =
      (nilpotentFrame q).det := by
    simpa using Real.rpow_inv_natCast_pow q.property.le (by decide : (3 : ℕ) ≠ 0)
  rw [inv_pow, hc]
  exact inv_mul_cancel₀ (ne_of_gt q.property)

noncomputable def nilpotentSection (q : nilpotentSectionDomain) : SL3 :=
  ⟨nilpotentSectionScale q • nilpotentFrame q, by
    rw [Matrix.det_smul]
    simpa using nilpotentSectionScale_cube q⟩

theorem continuous_nilpotentSection : Continuous nilpotentSection := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun q : nilpotentSectionDomain => (nilpotentFrame q).det) :=
    continuous_nilpotentFrame.matrix_det.comp continuous_subtype_val
  have hp : Continuous (fun q : nilpotentSectionDomain =>
      (nilpotentFrame q).det ^ ((3 : ℝ)⁻¹)) := by
    exact hc.rpow_const (fun q => Or.inl (ne_of_gt q.property))
  have hi : Continuous (fun q : nilpotentSectionDomain => nilpotentSectionScale q) :=
    hp.inv₀ (fun q => ne_of_gt (Real.rpow_pos_of_pos q.property _))
  exact hi.smul (continuous_nilpotentFrame.comp continuous_subtype_val)

theorem nilpotentSection_conjugates (q : nilpotentSectionDomain)
    (hq : IsNilpotent q.val) :
    (nilpotentSection q).val * shearFixedLine 0 * (nilpotentSection q)⁻¹.val = q.val := by
  have he : (nilpotentSection q).val * shearFixedLine 0 = q.val * (nilpotentSection q).val := by
    change (nilpotentSectionScale q • nilpotentFrame q) * shearFixedLine 0 =
      q.val * (nilpotentSectionScale q • nilpotentFrame q)
    rw [Matrix.smul_mul, Matrix.mul_smul, nilpotentFrame_intertwines q hq]
  have hi : (nilpotentSection q).val * (nilpotentSection q)⁻¹.val = 1 :=
    congrArg Subtype.val (mul_inv_cancel (nilpotentSection q))
  rw [he, mul_assoc, hi, mul_one]

theorem nilpotentSection_fixedLine (t : ℝ) :
    nilpotentSection ⟨shearFixedLine t, by
      change 0 < (nilpotentFrame (shearFixedLine t)).det
      rw [nilpotentFrame_fixedLine_det]; norm_num⟩ = upperUnipotent t 0 0 := by
  apply Subtype.ext
  change nilpotentSectionScale (shearFixedLine t) • nilpotentFrame (shearFixedLine t) = _
  simp [nilpotentSectionScale, nilpotentFrame_fixedLine]

end JSP400
