import NilpotentSection
import ShearCentralizer
import UpperUnipotentCompact

/-! Lifting actual adjoint-orbit closure points to the double orbit V M V. -/

namespace JSP400

open Matrix Set

def shearDoubleOrbit (M : Set SL3) : Set SL3 :=
  {g | ∃ v ∈ shearGroup, ∃ m ∈ M, ∃ w ∈ shearGroup, g = v * m * w}

theorem nilpotentSection_mem_shearDoubleOrbit (M : Set SL3)
    (q : nilpotentSectionDomain)
    (hq : q.val ∈ shearOrbitUnion ((fun g => adjointAction g (shearFixedLine 0)) '' M)) :
    nilpotentSection q ∈ shearDoubleOrbit M := by
  obtain ⟨x, ⟨m, hm, rfl⟩, s, t, hq⟩ := hq
  have haction : q.val = adjointAction (shearElement s t * m) (shearFixedLine 0) := by
    rw [adjointAction_mul, adjointAction_shearElement]
    exact hq
  have hnil : IsNilpotent q.val := by
    rw [haction]
    exact adjointAction_isNilpotent _ (shearFixedLine_isNilpotent 0)
  have hsection : adjointAction (nilpotentSection q) (shearFixedLine 0) =
      adjointAction (shearElement s t * m) (shearFixedLine 0) :=
    (nilpotentSection_conjugates q hnil).trans haction
  let w := (shearElement s t * m)⁻¹ * nilpotentSection q
  have hw : w ∈ shearGroup := by
    apply (adjointAction_base_eq_iff_mem_shearGroup w).mp
    change adjointAction ((shearElement s t * m)⁻¹ * nilpotentSection q) _ = _
    rw [adjointAction_mul, hsection, ← adjointAction_mul,
      inv_mul_cancel, adjointAction_one]
  refine ⟨shearElement s t, ⟨s, t, rfl⟩, m, hm, w, hw, ?_⟩
  simp [w, mul_assoc]

/-- Every point of the fixed affine line in the actual adjoint closure lifts
to the explicit upper-unipotent representative in the double-orbit closure. -/
theorem fixedLine_closure_lifts_to_shearDoubleOrbit (M : Set SL3) (t : ℝ)
    (ht : shearFixedLine t ∈
      closure (shearOrbitUnion ((fun g => adjointAction g (shearFixedLine 0)) '' M))) :
    upperUnipotent t 0 0 ∈ closure (shearDoubleOrbit M) := by
  let Z := shearOrbitUnion ((fun g => adjointAction g (shearFixedLine 0)) '' M)
  have hdom : shearFixedLine t ∈ nilpotentSectionDomain := by
    change 0 < (nilpotentFrame (shearFixedLine t)).det
    rw [nilpotentFrame_fixedLine_det]
    norm_num
  let q : nilpotentSectionDomain := ⟨shearFixedLine t, hdom⟩
  have hq : q ∈ closure (Subtype.val ⁻¹' Z) := by
    rw [← isOpen_nilpotentSectionDomain.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val Z]
    exact ht
  have hi := mem_closure_image continuous_nilpotentSection.continuousAt hq
  have hsub : nilpotentSection '' (Subtype.val ⁻¹' Z) ⊆ shearDoubleOrbit M := by
    rintro g ⟨x, hx, rfl⟩
    exact nilpotentSection_mem_shearDoubleOrbit M x hx
  have hc := closure_mono hsub hi
  simpa only [q, nilpotentSection_fixedLine] using hc

theorem shearDoubleOrbit_mul_right (M : Set SL3) {g w : SL3}
    (hg : g ∈ shearDoubleOrbit M) (hw : w ∈ shearGroup) : g * w ∈ shearDoubleOrbit M := by
  obtain ⟨v, hv, m, hm, u, hu, rfl⟩ := hg
  exact ⟨v, hv, m, hm, u * w, shearGroup.mul_mem hu hw, mul_assoc _ _ _⟩

theorem closure_shearDoubleOrbit_mul_right (M : Set SL3) {g w : SL3}
    (hg : g ∈ closure (shearDoubleOrbit M)) (hw : w ∈ shearGroup) :
    g * w ∈ closure (shearDoubleOrbit M) := by
  have hc : Continuous (fun x : SL3 => x * w) := continuous_id.mul continuous_const
  have hi := mem_closure_image hc.continuousAt hg
  apply closure_mono ?_ hi
  rintro x ⟨y, hy, rfl⟩
  exact shearDoubleOrbit_mul_right M hy hw

theorem upperUnipotent_shear_factor (a b c : ℝ) :
    upperUnipotent a b c = upperUnipotent (a - c) 0 0 *
      shearElement c (b - (a - c) * c) := by
  have hs : shearElement c (b - (a - c) * c) =
      upperUnipotent c (b - (a - c) * c) c := rfl
  rw [hs, upperUnipotent_mul]
  congr 1 <;> ring

/-- The affine-line lift covers every upper-unipotent matrix with the same
adjoint parameter a−c, not just a chosen representative. -/
theorem upperUnipotent_mem_closure_of_fixedLine (M : Set SL3) (a b c : ℝ)
    (ht : shearFixedLine (a - c) ∈
      closure (shearOrbitUnion ((fun g => adjointAction g (shearFixedLine 0)) '' M))) :
    upperUnipotent a b c ∈ closure (shearDoubleOrbit M) := by
  rw [upperUnipotent_shear_factor]
  exact closure_shearDoubleOrbit_mul_right M
    (fixedLine_closure_lifts_to_shearDoubleOrbit M (a - c) ht) ⟨c, _, rfl⟩

end JSP400
