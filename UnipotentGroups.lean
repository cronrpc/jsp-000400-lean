import FormStabilizer

namespace JSP400

noncomputable section

open Matrix

/-- The first unipotent one-parameter group in Margulis §4. -/
def unipotentOne (t : ℝ) : SL3 :=
  ⟨!![1, t, t ^ 2 / 2; 0, 1, t; 0, 0, 1], by
    simp [Matrix.det_fin_three]⟩

/-- The commuting central one-parameter group in Margulis §4. -/
def unipotentTwo (t : ℝ) : SL3 :=
  ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], by
    simp [Matrix.det_fin_three]⟩

theorem unipotentOne_add (s t : ℝ) :
    unipotentOne (s + t) = unipotentOne s * unipotentOne t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (unipotentOne (s + t)).val i j =
    ((unipotentOne s).val * (unipotentOne t).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentOne, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem unipotentTwo_add (s t : ℝ) :
    unipotentTwo (s + t) = unipotentTwo s * unipotentTwo t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (unipotentTwo (s + t)).val i j =
    ((unipotentTwo s).val * (unipotentTwo t).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentTwo, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

theorem unipotentOne_commute_unipotentTwo (s t : ℝ) :
    Commute (unipotentOne s) (unipotentTwo t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((unipotentOne s).val * (unipotentTwo t).val) i j =
    ((unipotentTwo t).val * (unipotentOne s).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentOne, unipotentTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem unipotentOne_mem_standardStabilizer (t : ℝ) :
    unipotentOne t ∈ formStabilizer standardForm := by
  intro v
  change standardForm ((unipotentOne t).val.mulVec v) = standardForm v
  simp [unipotentOne, standardForm_apply, dotProduct, Fin.sum_univ_succ]
  ring

theorem unipotentTwo_mem_standardStabilizer_iff (t : ℝ) :
    unipotentTwo t ∈ formStabilizer standardForm ↔ t = 0 := by
  constructor
  · intro h
    have ht := h ![0, 0, 1]
    change standardForm ((unipotentTwo t).val.mulVec ![0, 0, 1]) = _ at ht
    simp [unipotentTwo, standardForm_apply] at ht
    linarith
  · rintro rfl v
    change standardForm ((unipotentTwo 0).val.mulVec v) = standardForm v
    simp [unipotentTwo, standardForm_apply, dotProduct, Fin.sum_univ_succ]

/-- The diagonal subgroup element. Positivity can be imposed on `t` where
the identity component is needed; algebraically nonzero is enough. -/
noncomputable def diagonalFlow (t : ℝ) (ht : t ≠ 0) : SL3 :=
  ⟨!![t, 0, 0; 0, 1, 0; 0, 0, t⁻¹], by
    simp [Matrix.det_fin_three, ht]⟩

theorem diagonalFlow_mem_standardStabilizer (t : ℝ) (ht : t ≠ 0) :
    diagonalFlow t ht ∈ formStabilizer standardForm := by
  intro v
  change standardForm ((diagonalFlow t ht).val.mulVec v) = standardForm v
  simp [diagonalFlow, standardForm_apply, dotProduct, Fin.sum_univ_succ]
  field_simp

theorem diagonalFlow_unipotentOne (t : ℝ) (ht : t ≠ 0) (s : ℝ) :
    diagonalFlow t ht * unipotentOne s =
      unipotentOne (t * s) * diagonalFlow t ht := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((diagonalFlow t ht).val * (unipotentOne s).val) i j =
    ((unipotentOne (t * s)).val * (diagonalFlow t ht).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, unipotentOne, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp

theorem diagonalFlow_unipotentTwo (t : ℝ) (ht : t ≠ 0) (s : ℝ) :
    diagonalFlow t ht * unipotentTwo s =
      unipotentTwo (t ^ 2 * s) * diagonalFlow t ht := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((diagonalFlow t ht).val * (unipotentTwo s).val) i j =
    ((unipotentTwo (t ^ 2 * s)).val * (diagonalFlow t ht).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, unipotentTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp

end

end JSP400

#print axioms JSP400.unipotentOne_mem_standardStabilizer
#print axioms JSP400.diagonalFlow_unipotentOne
#print axioms JSP400.diagonalFlow_unipotentTwo
