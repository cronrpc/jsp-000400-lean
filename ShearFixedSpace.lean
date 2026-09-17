import ShearLemma6C
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace JSP400

open Matrix Set Polynomial

/-- For real three by three matrices, nilpotence has the fixed polynomial
equation required for the closedness argument in Margulis §8. -/
theorem matrix3_isNilpotent_iff_cube (x : Matrix (Fin 3) (Fin 3) ℝ) :
    IsNilpotent x ↔ x ^ 3 = 0 := by
  constructor
  · intro h
    have hpoly : x.charpoly = X ^ 3 := by
      have hz := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
      simpa using sub_eq_zero.mp hz
    have hc := Matrix.aeval_self_charpoly x
    simpa [hpoly] using hc
  · exact fun h => ⟨3, h⟩

theorem isClosed_nilpotentMatrices :
    IsClosed {x : Matrix (Fin 3) (Fin 3) ℝ | IsNilpotent x} := by
  simp_rw [matrix3_isNilpotent_iff_cube]
  exact isClosed_eq (continuous_id.pow 3) continuous_const

theorem nilpotent_matrix_trace_zero {x : Matrix (Fin 3) (Fin 3) ℝ}
    (h : IsNilpotent x) : x.trace = 0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent h).eq_zero

theorem shearConjugate_eq_self_iff_commute
    (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearConjugate x s t = x ↔
      (shearElement s t).val * x = x * (shearElement s t).val := by
  have hi : (shearElement s t)⁻¹.val * (shearElement s t).val = 1 :=
    congrArg Subtype.val (inv_mul_cancel (shearElement s t))
  have hi' : (shearElement s t).val * (shearElement s t)⁻¹.val = 1 :=
    congrArg Subtype.val (mul_inv_cancel (shearElement s t))
  constructor
  · intro h
    have hm := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ =>
      A * (shearElement s t).val) h
    simpa only [shearConjugate, mul_assoc, hi, mul_one] using hm
  · intro h
    unfold shearConjugate
    rw [h, mul_assoc, hi', mul_one]

/-- In the trace-zero matrix space, the fixed space of the actual adjoint
action of V is precisely its two-dimensional Lie algebra. -/
theorem shear_fixed_iff_mem_lieAlgebra
    (x : Matrix (Fin 3) (Fin 3) ℝ) (htrace : x.trace = 0) :
    (∀ s t : ℝ, shearConjugate x s t = x) ↔ x ∈ shearLieAlgebra := by
  constructor
  · intro h
    have hm := (shearConjugate_eq_self_iff_commute x 1 0).mp (h 1 0)
    have he (i j : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hm
    have h00 := he 0 0
    have h01 := he 0 1
    have h02 := he 0 2
    have h10 := he 1 0
    have h11 := he 1 1
    have h12 := he 1 2
    simp [shearElement, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12
    have ht : x 0 0 + x 1 1 + x 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_succ, add_assoc] using htrace
    refine ⟨x 0 1, x 0 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro ⟨a, b, rfl⟩ s t
    rw [shearConjugate_eq_self_iff_commute]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shearElement, Matrix.mul_apply, Fin.sum_univ_succ]
    all_goals ring

/-- The affine line denoted x₀ + V₂ in Margulis's proof. -/
def shearFixedLine (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, t; 0, 0, 1; 0, 0, 0]

theorem shear_lieAlgebra_slice_eq_line :
    shearLieAlgebra ∩ {x | x 0 1 = 1} = Set.range shearFixedLine := by
  ext x
  constructor
  · rintro ⟨⟨a, b, rfl⟩, h⟩
    have ha : a = 1 := h
    subst a
    exact ⟨b, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨⟨1, t, rfl⟩, rfl⟩

theorem shearFixedLine_isNilpotent (t : ℝ) : IsNilpotent (shearFixedLine t) := by
  rw [matrix3_isNilpotent_iff_cube]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearFixedLine, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem shearConjugate_pow (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) (n : ℕ) :
    shearConjugate x s t ^ n = shearConjugate (x ^ n) s t := by
  have hi : (shearElement s t)⁻¹.val * (shearElement s t).val = 1 :=
    congrArg Subtype.val (inv_mul_cancel (shearElement s t))
  have hi' : (shearElement s t).val * (shearElement s t)⁻¹.val = 1 :=
    congrArg Subtype.val (mul_inv_cancel (shearElement s t))
  induction n with
  | zero => simp only [pow_zero, shearConjugate, mul_one, hi']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [shearConjugate]
    calc
      _ = (shearElement s t).val * x ^ n *
          ((shearElement s t)⁻¹.val * (shearElement s t).val) * x *
          (shearElement s t)⁻¹.val := by noncomm_ring
      _ = _ := by rw [hi]; noncomm_ring

theorem shearConjugate_isNilpotent
    {x : Matrix (Fin 3) (Fin 3) ℝ} (h : IsNilpotent x) (s t : ℝ) :
    IsNilpotent (shearConjugate x s t) := by
  rw [matrix3_isNilpotent_iff_cube, shearConjugate_pow,
    (matrix3_isNilpotent_iff_cube x).mp h]
  simp [shearConjugate]

theorem matrix_smul_isNilpotent {x : Matrix (Fin 3) (Fin 3) ℝ}
    (h : IsNilpotent x) (c : ℝ) : IsNilpotent (c • x) := by
  rw [matrix3_isNilpotent_iff_cube, smul_pow,
    (matrix3_isNilpotent_iff_cube x).mp h, smul_zero]

/-- Closure of the actual union of adjoint orbits stays in the nilpotent cone. -/
theorem closure_shear_orbits_nilpotent
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hY : ∀ x ∈ Y, IsNilpotent x) :
    closure {z | ∃ x ∈ Y, ∃ s t : ℝ, z = shearConjugate x s t} ⊆
      {z | IsNilpotent z} := by
  apply closure_minimal _ isClosed_nilpotentMatrices
  rintro z ⟨x, hx, s, t, rfl⟩
  exact shearConjugate_isNilpotent (hY x hx) s t

end JSP400
