import ShearFixedSpace

/-! Actual adjoint-orbit closures for the two-dimensional shear group. -/

namespace JSP400

open Matrix Set

theorem shearElement_mul (s t u v : ℝ) :
    shearElement s t * shearElement u v = shearElement (s + u) (t + v + s * u) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((shearElement s t).val * (shearElement u v).val) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [shearElement, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem shearElement_zero : shearElement 0 0 = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [shearElement]

theorem shearConjugate_comp (x : Matrix (Fin 3) (Fin 3) ℝ) (s t u v : ℝ) :
    shearConjugate (shearConjugate x u v) s t =
      shearConjugate x (s + u) (t + v + s * u) := by
  unfold shearConjugate
  rw [← shearElement_mul s t u v, _root_.mul_inv_rev]
  change (shearElement s t).val *
      ((shearElement u v).val * x * (shearElement u v)⁻¹.val) * (shearElement s t)⁻¹.val =
    ((shearElement s t).val * (shearElement u v).val) * x *
      ((shearElement u v)⁻¹.val * (shearElement s t)⁻¹.val)
  noncomm_ring

theorem continuous_shearConjugate_fixed_parameters (s t : ℝ) :
    Continuous (fun x : Matrix (Fin 3) (Fin 3) ℝ => shearConjugate x s t) := by
  unfold shearConjugate
  fun_prop

def shearOrbitUnion (Y : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {z | ∃ x ∈ Y, ∃ s t : ℝ, z = shearConjugate x s t}

theorem subset_shearOrbitUnion (Y : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Y ⊆ shearOrbitUnion Y := by
  intro x hx
  exact ⟨x, hx, 0, 0, (shearConjugate_zero x).symm⟩

theorem shearOrbitUnion_invariant (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    {x : Matrix (Fin 3) (Fin 3) ℝ} (hx : x ∈ shearOrbitUnion Y) (s t : ℝ) :
    shearConjugate x s t ∈ shearOrbitUnion Y := by
  obtain ⟨y, hy, u, v, rfl⟩ := hx
  exact ⟨y, hy, s + u, t + v + s * u, shearConjugate_comp y s t u v⟩

theorem closure_shearOrbitUnion_invariant (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    {x : Matrix (Fin 3) (Fin 3) ℝ} (hx : x ∈ closure (shearOrbitUnion Y)) (s t : ℝ) :
    shearConjugate x s t ∈ closure (shearOrbitUnion Y) := by
  have hi : shearConjugate x s t ∈
      closure ((fun z => shearConjugate z s t) '' shearOrbitUnion Y) :=
    mem_closure_image (continuous_shearConjugate_fixed_parameters s t).continuousAt hx
  apply closure_mono ?_ hi
  rintro z ⟨a, ha, rfl⟩
  exact shearOrbitUnion_invariant Y ha s t

theorem closure_shearOrbitUnion_nilpotent (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hY : ∀ x ∈ Y, IsNilpotent x) :
    ∀ x ∈ closure (shearOrbitUnion Y), IsNilpotent x := by
  exact fun _ hx => closure_shear_orbits_nilpotent Y hY hx

theorem closure_shearOrbitUnion_minimal
    {Y A : Set (Matrix (Fin 3) (Fin 3) ℝ)} (hA : IsClosed A) (hYA : Y ⊆ A)
    (hinv : ∀ x ∈ A, ∀ s t, shearConjugate x s t ∈ A) :
    closure (shearOrbitUnion Y) ⊆ A := by
  apply closure_minimal _ hA
  rintro z ⟨x, hx, s, t, rfl⟩
  exact hinv x (hYA hx) s t

end JSP400
