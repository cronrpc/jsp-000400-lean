import GramSection
import GramHull

namespace JSP400

open Matrix Set

/-- The Gram map detects closures of H-left-invariant sets. This is proved
using the explicit continuous local section, not a quotient-map assumption. -/
theorem mem_closure_of_gramMatrix_mem_closure
    (S : Set SL3)
    (hleft : ∀ h ∈ formStabilizer standardForm, ∀ g ∈ S, h * g ∈ S)
    (u : SL3) (hu : gramMatrix u ∈ closure (gramMatrix '' S)) :
    u ∈ closure S := by
  let F : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun q => u⁻¹.val.transpose * q * u⁻¹.val
  have hF : Continuous F := by dsimp [F]; fun_prop
  let T : Set SL3 := (fun m => m * u⁻¹) '' S
  let Z : Set (Matrix (Fin 3) (Fin 3) ℝ) := gramMatrix '' T
  have hFbase : F (gramMatrix u) = standardGram := by
    change u⁻¹.val.transpose * gramMatrix u * u⁻¹.val = standardGram
    rw [← gramMatrix_mul u u⁻¹, mul_inv_cancel, gramMatrix_one]
  have hFimage : F '' (gramMatrix '' S) ⊆ Z := by
    rintro q ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m * u⁻¹, ⟨m, hm, rfl⟩, gramMatrix_mul m u⁻¹⟩
  have hbase : standardGram ∈ closure Z := by
    rw [← hFbase]
    exact closure_mono hFimage (mem_closure_image hF.continuousAt hu)
  let q0 : GramSection.sectionDomain :=
    ⟨standardGram, GramSection.standardGram_mem_sectionDomain⟩
  have hq0 : q0 ∈ closure (Subtype.val ⁻¹' Z) := by
    rw [← GramSection.isOpen_sectionDomain.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val Z]
    exact hbase
  have hmap : Continuous (fun q : GramSection.sectionDomain => GramSection.gramSection q * u) :=
    GramSection.continuous_gramSection.mul continuous_const
  have hsub : (fun q : GramSection.sectionDomain => GramSection.gramSection q * u) ''
      (Subtype.val ⁻¹' Z) ⊆ S := by
    rintro g ⟨q, hq, rfl⟩
    obtain ⟨m', ⟨m, hm, rfl⟩, hqm⟩ := hq
    have hsymm : q.val.IsSymm := hqm ▸ gramMatrix_isSymm (m * u⁻¹)
    have hdet : q.val.det = 1 := hqm ▸ gramMatrix_det (m * u⁻¹)
    have heq : gramMatrix (GramSection.gramSection q) = gramMatrix (m * u⁻¹) :=
      (GramSection.gramMatrix_gramSection q hsymm hdet).trans hqm.symm
    have hh := (gramMatrix_eq_iff_mul_inv_mem (GramSection.gramSection q) (m * u⁻¹)).mp heq
    have hin := hleft _ hh m hm
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hin
  have hi := closure_mono hsub (mem_closure_image hmap.continuousAt hq0)
  simpa only [q0, GramSection.gramSection_standardGram, one_mul] using hi

theorem unipotentTwo_mem_closure_hull_of_gram (M : Set SL3) (t : ℝ)
    (ht : gramFixed 1 (2 * t) ∈ closure (gramOrbitUnion (gramMatrix '' M))) :
    unipotentTwo t ∈ closure (lemma7Hull M) := by
  apply mem_closure_of_gramMatrix_mem_closure (lemma7Hull M)
    (fun h hh g hg => lemma7Hull_left_invariant M hg hh)
  rw [gramMatrix_unipotentTwo]
  exact closure_mono (gramOrbitUnion_subset_hull_image M) ht

end JSP400

#print axioms JSP400.mem_closure_of_gramMatrix_mem_closure
