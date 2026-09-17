import PrincipalFixed
import NilpotentSection

namespace JSP400

open Matrix Set
noncomputable section

def principalSectionDomain : Set PrincipalSpace :=
  Prod.fst ⁻¹' nilpotentSectionDomain

theorem isOpen_principalSectionDomain : IsOpen principalSectionDomain :=
  isOpen_nilpotentSectionDomain.preimage continuous_fst

theorem principalBase_mem_sectionDomain : principalBase ∈ principalSectionDomain := by
  change 0 < (nilpotentFrame (shearFixedLine 0)).det
  rw [nilpotentFrame_fixedLine_det]
  norm_num

def principalFrame (p : principalSectionDomain) : SL3 :=
  nilpotentSection ⟨p.val.1, p.property⟩

def principalCorrection (p : principalSectionDomain) : ℝ :=
  ((principalFrame p).val.transpose * p.val.2 * (principalFrame p).val) 2 2

def principalSection (p : principalSectionDomain) : SL3 :=
  principalFrame p * unipotentTwo (-principalCorrection p / 2)

theorem continuous_principalFrame : Continuous principalFrame := by
  exact continuous_nilpotentSection.comp
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _)

theorem continuous_principalCorrection : Continuous principalCorrection := by
  have hf : Continuous (fun p : principalSectionDomain => (principalFrame p).val) := by
    have hv : Continuous (fun g : SL3 => g.val) := by fun_prop
    exact hv.comp continuous_principalFrame
  have hq : Continuous (fun p : principalSectionDomain => p.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hc := (hf.matrix_transpose.mul hq).mul hf
  exact (hc.matrix_elem 2 2)

theorem continuous_principalSection : Continuous principalSection := by
  have hu : Continuous unipotentTwo := by unfold unipotentTwo; fun_prop
  exact continuous_principalFrame.mul
    (hu.comp (continuous_principalCorrection.neg.div_const 2))

theorem principalFrame_base :
    principalFrame ⟨principalBase, principalBase_mem_sectionDomain⟩ = 1 := by
  change nilpotentSection ⟨shearFixedLine 0, _⟩ = 1
  rw [nilpotentSection_fixedLine, upperUnipotent_zero]

theorem principalSection_base :
    principalSection ⟨principalBase, principalBase_mem_sectionDomain⟩ = 1 := by
  have hc : principalCorrection ⟨principalBase, principalBase_mem_sectionDomain⟩ = 0 := by
    unfold principalCorrection
    rw [principalFrame_base]
    simp [principalBase, standardGram]
  rw [principalSection, principalFrame_base, hc]
  simpa using unipotentTwo_zero

/-- On the genuine orbit, the section differs from the original matrix by
an element of exactly V₁. The second form removes the extra V₂ freedom in the
nilpotent frame, rather than assuming a general homogeneous-space section. -/
theorem principalSection_right_coset (p : principalSectionDomain) (g : SL3)
    (hp : p.val = principalOrbitMap g) :
    ∃ t : ℝ, principalSection p = g * unipotentOne t := by
  let s := principalFrame p
  have hnil : IsNilpotent p.val.1 := by
    rw [hp]
    exact adjointAction_isNilpotent g (shearFixedLine_isNilpotent 0)
  have hconj : adjointAction s (shearFixedLine 0) = adjointAction g (shearFixedLine 0) := by
    have he := nilpotentSection_conjugates ⟨p.val.1, p.property⟩ hnil
    change adjointAction s (shearFixedLine 0) = p.val.1 at he
    simpa only [hp, principalOrbitMap_eq, Prod.fst] using he
  have hw : g⁻¹ * s ∈ shearGroup := by
    apply (adjointAction_base_eq_iff_mem_shearGroup _).mp
    rw [adjointAction_mul, hconj, adjointAction_inv_apply]
  obtain ⟨a, b, hw⟩ := hw
  have hs : s = g * shearElement a b := by
    rw [← hw]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
  have hQ : s.val.transpose * p.val.2 * s.val = gramMatrix (shearElement a b) := by
    have hpq : p.val.2 = gramMatrix g⁻¹ := by rw [hp]; rfl
    rw [hpq, ← gramMatrix_mul, hw]
  have hc : principalCorrection p = 2 * (b - a ^ 2 / 2) := by
    change (s.val.transpose * p.val.2 * s.val) 2 2 = _
    rw [hQ, shearElement_unipotent_factor,
      gramMatrix_mul_left_stabilizer _ _ (unipotentOne_mem_standardStabilizer a),
      gramMatrix_unipotentTwo]
    rfl
  refine ⟨a, ?_⟩
  change s * unipotentTwo (-principalCorrection p / 2) = _
  rw [hs, shearElement_unipotent_factor, hc]
  have hneg : -(2 * (b - a ^ 2 / 2)) / 2 = -(b - a ^ 2 / 2) := by ring
  rw [hneg, mul_assoc, mul_assoc, ← unipotentTwo_add, add_neg_cancel, unipotentTwo_zero]
  simp

theorem principalOrbitMap_principalSection (p : principalSectionDomain)
    (hp : p.val ∈ range principalOrbitMap) : principalOrbitMap (principalSection p) = p.val := by
  obtain ⟨g, hg⟩ := hp
  obtain ⟨t, ht⟩ := principalSection_right_coset p g hg.symm
  rw [ht, hg.symm]
  apply (principalOrbitMap_eq_iff_inv_mul_mem _ _).mpr
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using
    (show unipotentOne t ∈ principalUnipotent from ⟨t, rfl⟩)

/-- The actual orbit is relatively closed in the displayed open neighborhood.
This follows from the proved continuous section and equality on the orbit. -/
theorem principalOrbitMap_principalSection_of_closure (p : principalSectionDomain)
    (hp : p.val ∈ closure (range principalOrbitMap)) :
    principalOrbitMap (principalSection p) = p.val := by
  have hcl : p ∈ closure (Subtype.val ⁻¹' range principalOrbitMap) := by
    rw [← isOpen_principalSectionDomain.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (range principalOrbitMap)]
    exact hp
  have he : closure (Subtype.val ⁻¹' range principalOrbitMap) ⊆
      {q : principalSectionDomain | principalOrbitMap (principalSection q) = q.val} := by
    apply closure_minimal ?_
      (isClosed_eq (continuous_principalOrbitMap.comp continuous_principalSection) continuous_subtype_val)
    exact fun q hq => principalOrbitMap_principalSection q hq
  exact he hcl

end
end JSP400

#print axioms JSP400.principalSection_right_coset
