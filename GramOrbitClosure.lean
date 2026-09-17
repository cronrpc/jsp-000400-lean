import GramDescent
import ShearFixedRays

namespace JSP400

open Matrix Set

def gramOrbitUnion (Y : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {z | ∃ q ∈ Y, ∃ t : ℝ, z = gramShear q t}

theorem subset_gramOrbitUnion (Y : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Y ⊆ gramOrbitUnion Y := fun q hq => ⟨q, hq, 0, (gramShear_zero q).symm⟩

theorem gramOrbitUnion_invariant (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    {q : Matrix (Fin 3) (Fin 3) ℝ} (hq : q ∈ gramOrbitUnion Y) (t : ℝ) :
    gramShear q t ∈ gramOrbitUnion Y := by
  obtain ⟨r, hr, s, rfl⟩ := hq
  exact ⟨r, hr, s + t, gramShear_add r s t⟩

theorem closure_gramOrbitUnion_invariant (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    {q : Matrix (Fin 3) (Fin 3) ℝ} (hq : q ∈ closure (gramOrbitUnion Y)) (t : ℝ) :
    gramShear q t ∈ closure (gramOrbitUnion Y) := by
  have hc : Continuous (fun r : Matrix (Fin 3) (Fin 3) ℝ => gramShear r t) := by
    simpa only [Function.comp_def, id_eq] using
      continuous_gramShear.comp (continuous_id.prodMk continuous_const)
  have hi := mem_closure_image hc.continuousAt hq
  apply closure_mono ?_ hi
  rintro r ⟨a, ha, rfl⟩
  exact gramOrbitUnion_invariant Y ha t

theorem closure_gramOrbitUnion_det (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hY : ∀ q ∈ Y, q.det = 1) :
    ∀ q ∈ closure (gramOrbitUnion Y), q.det = 1 := by
  apply closure_minimal ?_ (isClosed_eq (by fun_prop) continuous_const)
  rintro q ⟨r, hr, t, rfl⟩
  change (gramShear r t).det = 1
  rw [gramShear_det, hY r hr]

theorem gram_fixed_line_contains_ray
    (S : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hclosed : IsClosed S) (hconn : IsPreconnected S)
    (hzero : gramFixed 1 0 ∈ S) (hnoncompact : ¬IsCompact S)
    (hline : S ⊆ range (gramFixed 1)) :
    gramFixed 1 '' Ici 0 ⊆ S ∨ gramFixed 1 '' Iic 0 ⊆ S := by
  have hc : Continuous (gramFixed 1) := by unfold gramFixed; fun_prop
  let T : Set ℝ := gramFixed 1 ⁻¹' S
  have himage : gramFixed 1 '' T = S := Set.image_preimage_eq_iff.mpr hline
  have hcoord : T = (fun q : Matrix (Fin 3) (Fin 3) ℝ => q 2 2) '' S := by
    ext t
    constructor
    · intro ht
      exact ⟨gramFixed 1 t, ht, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨s, rfl⟩ := hline hq
      exact hq
  have hTconn : IsPreconnected T := by
    rw [hcoord]
    exact hconn.image _ (by fun_prop)
  have hTclosed : IsClosed T := hclosed.preimage hc
  have hTnoncompact : ¬IsCompact T := by
    intro hT
    apply hnoncompact
    rw [← himage]
    exact hT.image hc
  rcases noncompact_real_connected_contains_ray T hTclosed hTconn hzero hTnoncompact with h | h
  · exact Or.inl (fun q hq => by obtain ⟨t, ht, rfl⟩ := hq; exact h ht)
  · exact Or.inr (fun q hq => by obtain ⟨t, ht, rfl⟩ := hq; exact h ht)

/-- The affine-ray conclusion for genuine symmetric determinant-one forms.
This is the form-space closure-enlargement step needed in Lemma 7. -/
theorem gram_orbit_closure_contains_ray
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hsymm : ∀ q ∈ Y, q.IsSymm) (hdet : ∀ q ∈ Y, q.det = 1)
    (hnot : ∀ q ∈ Y, q ∉ gramFlag 2)
    (hbase : standardGram ∈ closure Y) :
    gramFixed 1 '' Ici 0 ⊆ closure (gramOrbitUnion Y) ∨
      gramFixed 1 '' Iic 0 ⊆ closure (gramOrbitUnion Y) := by
  let A := closure (gramOrbitUnion Y)
  have hpEq : standardGram = gramFixed 1 0 := rfl
  have hYA : Y ⊆ A := (subset_gramOrbitUnion Y).trans subset_closure
  have hpA : standardGram ∈ A := closure_mono (subset_gramOrbitUnion Y) hbase
  have hpF : standardGram ∈ gramFlag 2 := (mem_gramFlag_two _).mpr ⟨1, 0, rfl⟩
  have hpD : standardGram ∈ gramFixedDomain A := ⟨hpA, hpF⟩
  have hYlayer : Y ⊆ gramLayer A 6 \ (gramFlag 2 : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
    intro q hq
    exact ⟨⟨hYA hq, (mem_gramFlag_six q).mpr (hsymm q hq)⟩, hnot q hq⟩
  have hcl := closure_mono hYlayer hbase
  have hnoncompact := gram_fixed_component_noncompact_of_layer A isClosed_closure
    (fun q hq t => closure_gramOrbitUnion_invariant Y hq t)
    4 (by decide) standardGram hpD hcl
  let C := connectedComponentIn (gramFixedDomain A) standardGram
  have hDclosed : IsClosed (gramFixedDomain A) := isClosed_closure.inter (isClosed_gramFlag 2)
  have hCclosed : IsClosed C := by
    apply closure_subset_iff_isClosed.mp
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hpD))
      (closure_minimal (connectedComponentIn_subset _ _) hDclosed)
  have hCline : C ⊆ range (gramFixed 1) := by
    intro q hq
    have hd := connectedComponentIn_subset (gramFixedDomain A) standardGram hq
    obtain ⟨b, hb⟩ := gramFixed_of_det_one q hd.2 (closure_gramOrbitUnion_det Y hdet q hd.1)
    exact ⟨b, hb.symm⟩
  have hCA : C ⊆ A := fun q hq => (connectedComponentIn_subset (gramFixedDomain A) standardGram hq).1
  rcases gram_fixed_line_contains_ray C hCclosed isPreconnected_connectedComponentIn
    (hpEq ▸ mem_connectedComponentIn hpD) hnoncompact hCline with h | h
  · exact Or.inl (h.trans hCA)
  · exact Or.inr (h.trans hCA)

end JSP400

#print axioms JSP400.gram_orbit_closure_contains_ray
