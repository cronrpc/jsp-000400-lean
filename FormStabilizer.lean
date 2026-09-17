import StandardForm

namespace JSP400

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) ℝ
abbrev Vector3 := Fin 3 → ℝ

/-- The actual subgroup of determinant-one matrices preserving a quadratic form. -/
def formStabilizer (Q : QuadraticForm ℝ Vector3) : Subgroup SL3 where
  carrier := {g | ∀ v, Q (g • v) = Q v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    rw [mul_smul, hg, hh]
  inv_mem' := by
    intro g hg v
    simpa using (hg (g⁻¹ • v)).symm

@[simp] theorem mem_formStabilizer (Q : QuadraticForm ℝ Vector3) (g : SL3) :
    g ∈ formStabilizer Q ↔ ∀ v, Q (g • v) = Q v := Iff.rfl

/-- A scalar equivalence of forms gives a genuine conjugacy of stabilizers. -/
theorem conjugate_mem_formStabilizer_iff
    (P Q : QuadraticForm ℝ Vector3) (s g : SL3) {c : ℝ} (hc : c ≠ 0)
    (hchange : ∀ v, P (s • v) = c * Q v) :
    s * g * s⁻¹ ∈ formStabilizer P ↔ g ∈ formStabilizer Q := by
  constructor
  · intro hg v
    have heq : P (s • (g • v)) = P (s • v) := by
      simpa only [mul_smul, inv_smul_smul] using hg (s • v)
    rw [hchange, hchange] at heq
    exact mul_left_cancel₀ hc heq
  · intro hg v
    calc
      P ((s * g * s⁻¹) • v) = P (s • (g • (s⁻¹ • v))) := by rw [mul_smul, mul_smul]
      _ = c * Q (g • (s⁻¹ • v)) := hchange _
      _ = c * Q (s⁻¹ • v) := by rw [hg]
      _ = P (s • (s⁻¹ • v)) := (hchange _).symm
      _ = P v := by rw [smul_inv_smul]

/-- The form-preserving group in the original question is conjugate inside
SL(3,ℝ) to the fixed group used by Margulis. -/
theorem standardizingSL_conjugates {α : ℝ} (hα : 0 < α) (g : SL3) :
    standardizingSL α hα * g * (standardizingSL α hα)⁻¹ ∈
      formStabilizer standardForm ↔ g ∈ formStabilizer (ternaryForm α) := by
  apply conjugate_mem_formStabilizer_iff
    standardForm (ternaryForm α) (standardizingSL α hα) g
    (c := -(determinantScale α ^ 2))
  · exact neg_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt (determinantScale_pos hα)))
  · intro v
    simpa only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
      using standardForm_standardizingSL hα v

end JSP400

#print axioms JSP400.conjugate_mem_formStabilizer_iff
#print axioms JSP400.standardizingSL_conjugates
