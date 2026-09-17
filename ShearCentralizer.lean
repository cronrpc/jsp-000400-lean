import ShearOrbitClosure
import Mathlib.Topology.Algebra.Group.Matrix

namespace JSP400

open Matrix Set

/-- The actual adjoint action of SL(3,ℝ) on real matrices. -/
noncomputable def adjointAction (g : SL3) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := g.val * x * g⁻¹.val

theorem adjointAction_mul (g h : SL3) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction (g * h) x = adjointAction g (adjointAction h x) := by
  unfold adjointAction
  rw [_root_.mul_inv_rev]
  change (g.val * h.val) * x * (h⁻¹.val * g⁻¹.val) =
    g.val * (h.val * x * h⁻¹.val) * g⁻¹.val
  noncomm_ring

@[simp] theorem adjointAction_one (x : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction 1 x = x := by simp [adjointAction]

theorem adjointAction_eq_self_iff_commute (g : SL3) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction g x = x ↔ g.val * x = x * g.val := by
  have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hi' : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  constructor
  · intro h
    have hm := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A * g.val) h
    simpa only [adjointAction, mul_assoc, hi, mul_one] using hm
  · intro h
    unfold adjointAction
    rw [h, mul_assoc, hi', mul_one]

theorem adjointAction_pow (g : SL3) (x : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) :
    adjointAction g x ^ n = adjointAction g (x ^ n) := by
  have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hi' : g.val * g⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel g)
  induction n with
  | zero => simp only [pow_zero, adjointAction, mul_one, hi']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [adjointAction]
    calc
      _ = g.val * x ^ n * (g⁻¹.val * g.val) * x * g⁻¹.val := by noncomm_ring
      _ = _ := by rw [hi]; noncomm_ring

theorem adjointAction_isNilpotent (g : SL3) {x : Matrix (Fin 3) (Fin 3) ℝ}
    (hx : IsNilpotent x) : IsNilpotent (adjointAction g x) := by
  rw [matrix3_isNilpotent_iff_cube, adjointAction_pow,
    (matrix3_isNilpotent_iff_cube x).mp hx]
  simp [adjointAction]

theorem continuous_adjointAction :
    Continuous (fun p : SL3 × Matrix (Fin 3) (Fin 3) ℝ => adjointAction p.1 p.2) := by
  unfold adjointAction
  fun_prop

def shearGroup : Subgroup SL3 where
  carrier := {g | ∃ s t : ℝ, g = shearElement s t}
  one_mem' := ⟨0, 0, shearElement_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨s, t, rfl⟩ ⟨u, v, rfl⟩
    exact ⟨s + u, t + v + s * u, shearElement_mul s t u v⟩
  inv_mem' := by
    rintro g ⟨s, t, rfl⟩
    exact ⟨-s, s ^ 2 - t, shearElement_inv s t⟩

theorem mem_shearGroup (g : SL3) :
    g ∈ shearGroup ↔ ∃ s t : ℝ, g = shearElement s t := Iff.rfl

theorem adjointAction_shearElement (s t : ℝ) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction (shearElement s t) x = shearConjugate x s t := rfl

/-- The centralizer of the regular nilpotent base matrix in the actual special
linear group is precisely the two-parameter shear group. -/
theorem adjointAction_base_eq_iff_mem_shearGroup (g : SL3) :
    adjointAction g (shearFixedLine 0) = shearFixedLine 0 ↔ g ∈ shearGroup := by
  constructor
  · intro h
    have hm := (adjointAction_eq_self_iff_commute g (shearFixedLine 0)).mp h
    have he (i j : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hm
    have h00 := he 0 0
    have h01 := he 0 1
    have h02 := he 0 2
    have h10 := he 1 0
    have h11 := he 1 1
    have h12 := he 1 2
    simp [shearFixedLine, Matrix.mul_apply,
      Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12
    have hz10 : g.val 1 0 = 0 := by linarith
    have hz20 : g.val 2 0 = 0 := by linarith
    have hz21 : g.val 2 1 = 0 := by linarith
    have hd11 : g.val 1 1 = g.val 0 0 := by linarith
    have hd22 : g.val 2 2 = g.val 0 0 := by linarith
    have hcube : (g.val 0 0) ^ 3 = 1 := by
      calc
        _ = g.val.det := by
          rw [Matrix.det_fin_three, hz10, hz20, hz21, hd11, hd22]
          ring
        _ = 1 := g.property
    have hdiag : g.val 0 0 = 1 := by
      have hfactor : (g.val 0 0 - 1) * ((g.val 0 0) ^ 2 + g.val 0 0 + 1) = 0 := by
        nlinarith [hcube]
      rcases mul_eq_zero.mp hfactor with hzero | hzero
      · linarith
      · nlinarith [sq_nonneg (g.val 0 0 + 1 / 2)]
    refine ⟨g.val 0 1, g.val 0 2, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [shearElement, hz10, hz20, hz21, hd11, hd22, hdiag]
    exact h02.symm
  · rintro ⟨s, t, rfl⟩
    change shearConjugate (shearFixedLine 0) s t = shearFixedLine 0
    apply (shear_fixed_iff_mem_lieAlgebra (shearFixedLine 0)
      (nilpotent_matrix_trace_zero (shearFixedLine_isNilpotent 0))).mpr ⟨1, 0, rfl⟩

end JSP400
