import ShearFixedSpace

namespace JSP400

open Set Matrix

noncomputable def shearNormalize (x : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := (x 0 1)⁻¹ • x

theorem continuousAt_shearNormalize
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 ≠ 0) :
    ContinuousAt shearNormalize x := by
  have hc : Continuous (fun y : Matrix (Fin 3) (Fin 3) ℝ => y 0 1) := by fun_prop
  exact (hc.continuousAt.inv₀ hx).smul continuousAt_id

theorem shearNormalize_entry (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 ≠ 0) :
    shearNormalize x 0 1 = 1 := by
  simp [shearNormalize, hx]

theorem shearNormalize_eq_self (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1) :
    shearNormalize x = x := by simp [shearNormalize, hx]

theorem shearNormalize_isNilpotent {x : Matrix (Fin 3) (Fin 3) ℝ}
    (hx : IsNilpotent x) : IsNilpotent (shearNormalize x) :=
  matrix_smul_isNilpotent hx _

theorem shearLieAlgebra_smul {x : Matrix (Fin 3) (Fin 3) ℝ}
    (hx : x ∈ shearLieAlgebra) (c : ℝ) : c • x ∈ shearLieAlgebra := by
  obtain ⟨a, b, rfl⟩ := hx
  refine ⟨c * a, c * b, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem shearNormalize_not_mem_lieAlgebra
    {x : Matrix (Fin 3) (Fin 3) ℝ} (hx : x 0 1 ≠ 0)
    (hnot : x ∉ shearLieAlgebra) : shearNormalize x ∉ shearLieAlgebra := by
  intro h
  have hm := shearLieAlgebra_smul h (x 0 1)
  apply hnot
  simpa only [shearNormalize, smul_smul, mul_inv_cancel₀ hx, one_smul] using hm

/-- The normalized image excludes exactly the points where the denominator
vanishes. This restriction is open and contains the relevant base point. -/
def normalizedShearSet (Y : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  shearNormalize '' (Y ∩ {x | x 0 1 ≠ 0})

theorem mem_closure_normalizedShearSet
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1) (hcl : x ∈ closure Y) :
    x ∈ closure (normalizedShearSet Y) := by
  have hne : x 0 1 ≠ 0 := by rw [hx]; norm_num
  have ho : IsOpen {y : Matrix (Fin 3) (Fin 3) ℝ | y 0 1 ≠ 0} := by
    have hc : IsClosed {y : Matrix (Fin 3) (Fin 3) ℝ | y 0 1 = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    exact hc.isOpen_compl
  have hloc : x ∈ closure (Y ∩ {y | y 0 1 ≠ 0}) := ho.closure_inter ⟨hcl, hne⟩
  have h := mem_closure_image (continuousAt_shearNormalize x hne) hloc
  simpa only [normalizedShearSet, shearNormalize_eq_self x hx] using h

theorem normalizedShearSet_properties
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hnil : ∀ x ∈ Y, IsNilpotent x) (hnot : ∀ x ∈ Y, x ∉ shearLieAlgebra) :
    ∀ z ∈ normalizedShearSet Y,
      z 0 1 = 1 ∧ IsNilpotent z ∧ z ∉ shearLieAlgebra := by
  rintro z ⟨x, ⟨hxY, hx⟩, rfl⟩
  exact ⟨shearNormalize_entry x hx, shearNormalize_isNilpotent (hnil x hxY),
    shearNormalize_not_mem_lieAlgebra hx (hnot x hxY)⟩

theorem shearConjugate_smul (x : Matrix (Fin 3) (Fin 3) ℝ) (c s t : ℝ) :
    shearConjugate (c • x) s t = c • shearConjugate x s t := by
  simp only [shearConjugate, Matrix.mul_smul, Matrix.smul_mul]

theorem shearConjugate_recover_from_normalization
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 ≠ 0) (s t : ℝ) :
    shearConjugate x s t = x 0 1 • shearConjugate (shearNormalize x) s t := by
  rw [shearNormalize, shearConjugate_smul, smul_smul, mul_inv_cancel₀ hx, one_smul]

end JSP400
