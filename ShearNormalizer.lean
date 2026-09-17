import ShearCentralizer
import ShearB1
import Mathlib.Algebra.GroupWithZero.Action.Units

namespace JSP400

open Matrix Set

@[simp] theorem adjointAction_inv_apply (g : SL3) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction g⁻¹ (adjointAction g x) = x := by
  rw [← adjointAction_mul, inv_mul_cancel, adjointAction_one]

theorem adjointAction_injective (g : SL3) : Function.Injective (adjointAction g) :=
  (show Function.LeftInverse (adjointAction g⁻¹) (adjointAction g) from
    adjointAction_inv_apply g).injective

def shearLieElement (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, a, b; 0, 0, a; 0, 0, 0]

theorem shearLieElement_polynomial (a b : ℝ) :
    shearLieElement a b = a • shearFixedLine 0 + b • shearFixedLine 0 ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearLieElement, shearFixedLine, pow_two]

theorem shearLieElement_sq (a b : ℝ) :
    shearLieElement a b ^ 2 = a ^ 2 • shearFixedLine 0 ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearLieElement, shearFixedLine, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]

theorem commute_shearLieElement_iff (g : SL3) (a b : ℝ) (ha : a ≠ 0) :
    Commute g.val (shearLieElement a b) ↔ Commute g.val (shearFixedLine 0) := by
  constructor
  · intro h
    have hsq := h.pow_right 2
    rw [shearLieElement_sq] at hsq
    have hN2 := (Commute.smul_right_iff₀ (pow_ne_zero 2 ha)).mp hsq
    have hlin := h.sub_right (hN2.smul_right b)
    rw [shearLieElement_polynomial, add_sub_cancel_right] at hlin
    exact (Commute.smul_right_iff₀ ha).mp hlin
  · intro h
    rw [shearLieElement_polynomial]
    exact (h.smul_right a).add_right ((h.pow_right 2).smul_right b)

theorem mem_normalizer_of_adjoint_base_mem_lie
    (g : SL3) (hg : adjointAction g (shearFixedLine 0) ∈ shearLieAlgebra) :
    g ∈ Subgroup.normalizer (shearGroup : Set SL3) := by
  obtain ⟨a, b, hy⟩ := hg
  change adjointAction g (shearFixedLine 0) = shearLieElement a b at hy
  have ha : a ≠ 0 := by
    intro ha
    have hz : adjointAction g (shearFixedLine 0 ^ 2) = 0 := by
      rw [← adjointAction_pow, hy, shearLieElement_sq, ha]
      simp
    have hN : shearFixedLine 0 ^ 2 = 0 := by
      apply adjointAction_injective g
      simpa [adjointAction] using hz
    have hentry := congrArg (fun x : Matrix (Fin 3) (Fin 3) ℝ => x 0 2) hN
    norm_num [shearFixedLine, pow_two, Matrix.mul_apply, Fin.sum_univ_succ] at hentry
  have hcent (u : SL3) :
      adjointAction u (adjointAction g (shearFixedLine 0)) =
        adjointAction g (shearFixedLine 0) ↔ u ∈ shearGroup := by
    rw [adjointAction_eq_self_iff_commute, hy]
    change Commute u.val (shearLieElement a b) ↔ _
    rw [commute_shearLieElement_iff u a b ha]
    exact (adjointAction_eq_self_iff_commute u (shearFixedLine 0)).symm.trans
      (adjointAction_base_eq_iff_mem_shearGroup u)
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  change u ∈ shearGroup ↔ g * u * g⁻¹ ∈ shearGroup
  rw [← adjointAction_base_eq_iff_mem_shearGroup u, ← hcent (g * u * g⁻¹)]
  rw [adjointAction_mul, adjointAction_mul, adjointAction_inv_apply]
  exact (adjointAction_injective g).eq_iff.symm

def adjointBaseImage (M : Set SL3) : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  (fun g => adjointAction g (shearFixedLine 0)) '' M

theorem continuous_adjoint_base :
    Continuous (fun g : SL3 => adjointAction g (shearFixedLine 0)) := by
  have hp : Continuous (fun g : SL3 => (g, shearFixedLine 0)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using continuous_adjointAction.comp hp

/-- The complete adjoint-orbit assertion (A2) in the proof of Lemma 6. -/
theorem margulis_lemma6_A2 (M : Set SL3)
    (hbase : (1 : SL3) ∈ closure M)
    (hout : ∀ g ∈ M, g ∉ Subgroup.normalizer (shearGroup : Set SL3)) :
    shearFixedLine '' Ici 0 ⊆ closure (shearOrbitUnion (adjointBaseImage M)) ∨
      shearFixedLine '' Iic 0 ⊆ closure (shearOrbitUnion (adjointBaseImage M)) := by
  apply margulis_lemma6_B1
  · rintro x ⟨g, hg, rfl⟩
    exact adjointAction_isNilpotent g (shearFixedLine_isNilpotent 0)
  · rintro x ⟨g, hg, rfl⟩ hlie
    exact hout g hg (mem_normalizer_of_adjoint_base_mem_lie g hlie)
  · have h := mem_closure_image continuous_adjoint_base.continuousAt hbase
    simpa only [adjointAction_one, adjointBaseImage] using h

end JSP400

#print axioms JSP400.margulis_lemma6_A2
