import Core
import Mathlib.LinearAlgebra.QuadraticForm.Radical

namespace JSP400

/-- The real quadratic form with diagonal coefficients `1, 1, -α`. -/
noncomputable def ternaryForm (α : ℝ) : QuadraticForm ℝ (Fin 3 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ ![1, 1, -α]

@[simp] theorem ternaryForm_apply (α : ℝ) (v : Fin 3 → ℝ) :
    ternaryForm α v = value α (v 0) (v 1) (v 2) := by
  simp [ternaryForm, QuadraticMap.weightedSumSquares_apply,
    Fin.sum_univ_succ, value, pow_two, sub_eq_add_neg, add_assoc]

/-- The form takes a positive value, uniformly in the parameter. -/
theorem ternaryForm_positive_value (α : ℝ) :
    ∃ v : Fin 3 → ℝ, 0 < ternaryForm α v := by
  refine ⟨![1, 0, 0], ?_⟩
  simp [value]

/-- A positive parameter gives a negative value as well. -/
theorem ternaryForm_negative_value {α : ℝ} (hα : 0 < α) :
    ∃ v : Fin 3 → ℝ, ternaryForm α v < 0 := by
  refine ⟨![0, 0, 1], ?_⟩
  simpa [value] using neg_lt_zero.mpr hα

/-- Indefiniteness is expressed by actual values of both signs. -/
theorem ternaryForm_indefinite {α : ℝ} (hα : 0 < α) :
    (∃ v, 0 < ternaryForm α v) ∧ (∃ v, ternaryForm α v < 0) :=
  ⟨ternaryForm_positive_value α, ternaryForm_negative_value hα⟩

/-- No diagonal coefficient vanishes when α is nonzero. -/
theorem ternaryForm_nondegenerate {α : ℝ} (hα : α ≠ 0) :
    (ternaryForm α).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, ternaryForm,
    QuadraticForm.radical_weightedSumSquares]
  have hw : {i : Fin 3 | (![1, 1, -α] : Fin 3 → ℝ) i = 0} = ∅ := by
    ext i
    fin_cases i <;> simp [hα]
  rw [hw]
  ext v
  simp [Pi.mem_spanSubset_iff, funext_iff]

/-- A real form is proportional to a rational form if its values on rational
vectors agree with a nonzero real multiple of a rational quadratic form. -/
def ProportionalToRational (Q : QuadraticForm ℝ (Fin 3 → ℝ)) : Prop :=
  ∃ (c : ℝ) (R : QuadraticForm ℚ (Fin 3 → ℚ)), c ≠ 0 ∧
    ∀ v : Fin 3 → ℚ, Q (fun i => (v i : ℝ)) = c * (R v : ℝ)

/-- The first and third unit vectors force α to be rational if the whole
form is proportional to a rational form. -/
theorem ternaryForm_not_proportionalToRational {α : ℝ} (hα : Irrational α) :
    ¬ ProportionalToRational (ternaryForm α) := by
  rintro ⟨c, R, hc, hR⟩
  let a : ℚ := R ![1, 0, 0]
  let b : ℚ := R ![0, 0, 1]
  have ha : (1 : ℝ) = c * (a : ℝ) := by
    simpa [a, value] using hR ![1, 0, 0]
  have hb : -α = c * (b : ℝ) := by
    simpa [b, value] using hR ![0, 0, 1]
  have hane : (a : ℝ) ≠ 0 := by
    intro h
    simp [h] at ha
  apply hα.ne_rat (-b / a)
  push_cast
  apply (eq_div_iff hane).mpr
  nlinarith [congrArg (fun t : ℝ => t * (b : ℝ)) ha,
    congrArg (fun t : ℝ => t * (a : ℝ)) hb]

end JSP400

#print axioms JSP400.ternaryForm_indefinite
#print axioms JSP400.ternaryForm_nondegenerate
#print axioms JSP400.ternaryForm_not_proportionalToRational
