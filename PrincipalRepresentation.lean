import GramQuotient
import GramHull
import ShearNormalizer

namespace JSP400

open Matrix Set
noncomputable section

theorem unipotentOne_inv (t : ℝ) : (unipotentOne t)⁻¹ = unipotentOne (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← unipotentOne_add, add_neg_cancel, unipotentOne_zero]

/-- The actual one-parameter regular unipotent subgroup V₁. -/
def principalUnipotent : Subgroup SL3 where
  carrier := {g | ∃ t : ℝ, g = unipotentOne t}
  one_mem' := ⟨0, unipotentOne_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, (unipotentOne_add s t).symm⟩
  inv_mem' := by
    rintro g ⟨t, rfl⟩
    exact ⟨-t, unipotentOne_inv t⟩

theorem unipotentOne_eq_shearElement (t : ℝ) :
    unipotentOne t = shearElement t (t ^ 2 / 2) := rfl

theorem principalUnipotent_eq_inf :
    principalUnipotent = shearGroup ⊓ formStabilizer standardForm := by
  ext g
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t, t ^ 2 / 2, rfl⟩, unipotentOne_mem_standardStabilizer t⟩
  · rintro ⟨⟨s, t, rfl⟩, hh⟩
    have hb : unipotentTwo (t - s ^ 2 / 2) ∈ formStabilizer standardForm := by
      have h := (formStabilizer standardForm).mul_mem
        ((formStabilizer standardForm).inv_mem (unipotentOne_mem_standardStabilizer s)) hh
      rw [shearElement_unipotent_factor] at h
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
    have ht := (unipotentTwo_mem_standardStabilizer_iff _).mp hb
    refine ⟨s, ?_⟩
    rw [shearElement_unipotent_factor, ht, unipotentTwo_zero, mul_one]

/-- The covariant form action dual to actual conjugation on endomorphisms. -/
def coadjointForm (g : SL3) (q : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := g⁻¹.val.transpose * q * g⁻¹.val

abbrev PrincipalSpace := Matrix (Fin 3) (Fin 3) ℝ × Matrix (Fin 3) (Fin 3) ℝ

def principalAction (g : SL3) (p : PrincipalSpace) : PrincipalSpace :=
  (adjointAction g p.1, coadjointForm g p.2)

def principalBase : PrincipalSpace := (shearFixedLine 0, standardGram)

def principalOrbitMap (g : SL3) : PrincipalSpace := principalAction g principalBase

theorem coadjointForm_standard (g : SL3) :
    coadjointForm g standardGram = gramMatrix g⁻¹ := rfl

theorem principalOrbitMap_eq (g : SL3) :
    principalOrbitMap g = (adjointAction g (shearFixedLine 0), gramMatrix g⁻¹) := rfl

theorem coadjointForm_mul (g h : SL3) (q : Matrix (Fin 3) (Fin 3) ℝ) :
    coadjointForm (g * h) q = coadjointForm g (coadjointForm h q) := by
  unfold coadjointForm
  rw [_root_.mul_inv_rev]
  change (h⁻¹.val * g⁻¹.val).transpose * q * (h⁻¹.val * g⁻¹.val) = _
  simp only [Matrix.transpose_mul, mul_assoc]

theorem principalAction_mul (g h : SL3) (p : PrincipalSpace) :
    principalAction (g * h) p = principalAction g (principalAction h p) := by
  exact Prod.ext (adjointAction_mul g h p.1) (coadjointForm_mul g h p.2)

@[simp] theorem principalAction_one (p : PrincipalSpace) : principalAction 1 p = p := by
  apply Prod.ext
  · exact adjointAction_one p.1
  · change coadjointForm 1 p.2 = p.2
    simp [coadjointForm]

theorem continuous_principalAction : Continuous (fun p : SL3 × PrincipalSpace =>
    principalAction p.1 p.2) := by
  unfold principalAction coadjointForm adjointAction
  fun_prop

theorem continuous_principalOrbitMap : Continuous principalOrbitMap := by
  have hp : Continuous (fun g : SL3 => (g, principalBase)) :=
    continuous_id.prodMk continuous_const
  change Continuous (fun g : SL3 => principalAction g principalBase)
  simpa only [Function.comp_def, id_eq] using continuous_principalAction.comp hp

theorem principalOrbitMap_eq_base_iff (g : SL3) :
    principalOrbitMap g = principalBase ↔ g ∈ principalUnipotent := by
  rw [principalUnipotent_eq_inf]
  change (adjointAction g (shearFixedLine 0), gramMatrix g⁻¹) =
    (shearFixedLine 0, standardGram) ↔ _
  rw [Prod.mk.injEq, adjointAction_base_eq_iff_mem_shearGroup, gramMatrix_eq_standard_iff]
  simp only [Subgroup.mem_inf, Subgroup.inv_mem_iff]

theorem principalAction_injective (g : SL3) : Function.Injective (principalAction g) := by
  have hleft : Function.LeftInverse (principalAction g⁻¹) (principalAction g) := by
    intro p
    rw [← principalAction_mul, inv_mul_cancel, principalAction_one]
  exact hleft.injective

theorem principalOrbitMap_eq_iff_inv_mul_mem (g h : SL3) :
    principalOrbitMap g = principalOrbitMap h ↔ h⁻¹ * g ∈ principalUnipotent := by
  rw [← principalOrbitMap_eq_base_iff]
  change principalAction g principalBase = principalAction h principalBase ↔
    principalAction (h⁻¹ * g) principalBase = principalBase
  rw [principalAction_mul]
  constructor
  · intro he
    rw [he, ← principalAction_mul, inv_mul_cancel, principalAction_one]
  · intro he
    apply principalAction_injective h⁻¹
    rw [he, ← principalAction_mul, inv_mul_cancel, principalAction_one]

theorem principalBase_skew :
    (shearFixedLine 0).transpose * standardGram + standardGram * shearFixedLine 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [shearFixedLine, standardGram, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ]

theorem adjoint_coadjoint_skew (g : SL3) (x q : Matrix (Fin 3) (Fin 3) ℝ)
    (h : x.transpose * q + q * x = 0) :
    (adjointAction g x).transpose * coadjointForm g q +
      coadjointForm g q * adjointAction g x = 0 := by
  have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have hit : g.val.transpose * g⁻¹.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, hi, Matrix.transpose_one]
  have hfirst : (adjointAction g x).transpose * coadjointForm g q =
      g⁻¹.val.transpose * (x.transpose * q) * g⁻¹.val := by
    unfold adjointAction coadjointForm
    simp only [Matrix.transpose_mul]
    calc
      _ = g⁻¹.val.transpose * x.transpose * (g.val.transpose * g⁻¹.val.transpose) * q * g⁻¹.val := by noncomm_ring
      _ = _ := by rw [hit]; noncomm_ring
  have hsecond : coadjointForm g q * adjointAction g x =
      g⁻¹.val.transpose * (q * x) * g⁻¹.val := by
    unfold adjointAction coadjointForm
    calc
      _ = g⁻¹.val.transpose * q * (g⁻¹.val * g.val) * x * g⁻¹.val := by noncomm_ring
      _ = _ := by rw [hi]; noncomm_ring
  rw [hfirst, hsecond, ← add_mul, ← mul_add, h, mul_zero, zero_mul]

theorem principalOrbitMap_skew (g : SL3) :
    (principalOrbitMap g).1.transpose * (principalOrbitMap g).2 +
      (principalOrbitMap g).2 * (principalOrbitMap g).1 = 0 :=
  adjoint_coadjoint_skew g _ _ principalBase_skew

end
end JSP400

#print axioms JSP400.principalOrbitMap_eq_base_iff
#print axioms JSP400.principalOrbitMap_skew
