import PrincipalDescent
import PrincipalSection

namespace JSP400

open Matrix Set

def principalOrbitUnion (Y : Set PrincipalSpace) : Set PrincipalSpace :=
  {p | ∃ q ∈ Y, ∃ t : ℝ, p = principalAction (unipotentOne t) q}

def principalDoubleOrbit (M : Set SL3) : Set SL3 :=
  {g | ∃ s : ℝ, ∃ m ∈ M, ∃ t : ℝ, g = unipotentOne s * m * unipotentOne t}

theorem subset_principalOrbitUnion (Y : Set PrincipalSpace) : Y ⊆ principalOrbitUnion Y := by
  intro p hp
  exact ⟨p, hp, 0, by rw [unipotentOne_zero, principalAction_one]⟩

theorem closure_principalOrbitUnion_invariant (Y : Set PrincipalSpace) {p : PrincipalSpace}
    (hp : p ∈ closure (principalOrbitUnion Y)) (t : ℝ) :
    principalAction (unipotentOne t) p ∈ closure (principalOrbitUnion Y) := by
  have hc : Continuous (fun q => principalAction (unipotentOne t) q) := by
    simpa only [Function.comp_def, id_eq] using
      continuous_principalAction.comp (continuous_const.prodMk continuous_id)
  apply closure_mono ?_ (mem_closure_image hc.continuousAt hp)
  rintro z ⟨q, ⟨r, hr, s, rfl⟩, rfl⟩
  refine ⟨r, hr, t + s, ?_⟩
  rw [unipotentOne_add, principalAction_mul]

theorem principalOrbitUnion_subset_range (M : Set SL3) :
    principalOrbitUnion (principalOrbitMap '' M) ⊆ range principalOrbitMap := by
  rintro p ⟨q, ⟨m, hm, rfl⟩, t, rfl⟩
  exact ⟨unipotentOne t * m, principalAction_mul _ _ _⟩

theorem principalSection_mem_doubleOrbit (M : Set SL3) (p : principalSectionDomain)
    (hp : p.val ∈ principalOrbitUnion (principalOrbitMap '' M)) :
    principalSection p ∈ principalDoubleOrbit M := by
  obtain ⟨q, ⟨m, hm, rfl⟩, t, hp⟩ := hp
  have he : p.val = principalOrbitMap (unipotentOne t * m) := by
    rw [principalOrbitMap, principalAction_mul]
    exact hp
  obtain ⟨s, hs⟩ := principalSection_right_coset p (unipotentOne t * m) he
  exact ⟨t, m, hm, s, hs⟩

theorem principalSection_mem_closure_doubleOrbit (M : Set SL3) (p : principalSectionDomain)
    (hp : p.val ∈ closure (principalOrbitUnion (principalOrbitMap '' M))) :
    principalSection p ∈ closure (principalDoubleOrbit M) := by
  let Z := principalOrbitUnion (principalOrbitMap '' M)
  have hcl : p ∈ closure (Subtype.val ⁻¹' Z) := by
    rw [← isOpen_principalSectionDomain.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val Z]
    exact hp
  apply closure_mono ?_ (mem_closure_image continuous_principalSection.continuousAt hcl)
  rintro g ⟨q, hq, rfl⟩
  exact principalSection_mem_doubleOrbit M q hq

theorem mem_closure_diff_singleton_of_preconnected_noncompact
    {X : Type*} [TopologicalSpace X] [T1Space X] (C : Set X)
    (hC : IsPreconnected C) (p : X) (hp : p ∈ C) (hnc : ¬IsCompact C) :
    p ∈ closure (C \ {p}) := by
  have hne : ∃ q ∈ C, q ≠ p := by
    by_contra h
    push Not at h
    have he : C = {p} := Set.Subset.antisymm
      (fun q hq => h q hq) (singleton_subset_iff.mpr hp)
    exact hnc (he ▸ isCompact_singleton)
  obtain ⟨q, hq, hqp⟩ := hne
  by_contra hn
  let U := (closure (C \ {p}))ᶜ
  let V := ({p} : Set X)ᶜ
  have hcover : C ⊆ U ∪ V := by
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact Or.inl hn
    · exact Or.inr hxp
  obtain ⟨z, hzC, hzU, hzV⟩ := hC U V isClosed_closure.isOpen_compl
    isClosed_singleton.isOpen_compl hcover ⟨p, hp, hn⟩ ⟨q, hq, hqp⟩
  exact hzU (subset_closure ⟨hzC, hzV⟩)

def principalNormalizerReturn (M : Set SL3) : Set SL3 :=
  {g | g ∈ Subgroup.normalizer (principalUnipotent : Set SL3) ∧
    g ∈ closure (principalDoubleOrbit M) ∧ g ∉ principalUnipotent}

/-- The concrete V₁ case of Margulis's unipotent normalizer enlargement. A
true orbit section and the finite-dimensional descent supply normalizer
elements outside V₁ arbitrarily close to the identity. -/
theorem principal_normalizer_enlargement_of_outside_normalizer (M : Set SL3)
    (hbase : (1 : SL3) ∈ closure M)
    (hout : ∀ g ∈ M, g ∉ Subgroup.normalizer (principalUnipotent : Set SL3)) :
    (1 : SL3) ∈ closure (principalNormalizerReturn M) := by
  let Y := principalOrbitMap '' M
  let A := closure (principalOrbitUnion Y)
  have hYA : Y ⊆ A := (subset_principalOrbitUnion Y).trans subset_closure
  have hbY : principalBase ∈ closure Y := by
    have he := mem_closure_image continuous_principalOrbitMap.continuousAt hbase
    simpa only [principalOrbitMap, principalAction_one] using he
  have hpA : principalBase ∈ A := closure_mono (subset_principalOrbitUnion Y) hbY
  have hpF : principalBase ∈ principalFlag 4 := by
    apply (mem_principalFlag_four _).mpr
    exact ⟨⟨1, 0, rfl⟩, (mem_gramFlag_two _).mpr ⟨1, 0, rfl⟩⟩
  have hpD : principalBase ∈ principalFixedDomain A := ⟨hpA, hpF⟩
  have hYlayer : Y ⊆ principalLayer A 14 \ (principalFlag 4 : Set PrincipalSpace) := by
    rintro p hp
    obtain ⟨g, hg, rfl⟩ := hp
    refine ⟨⟨hYA ⟨g, hg, rfl⟩, ?_⟩, ?_⟩
    · apply (mem_principalFlag_fourteen _).mpr
      exact ⟨nilpotent_matrix_trace_zero (adjointAction_isNilpotent g (shearFixedLine_isNilpotent 0)),
        gramMatrix_isSymm g⁻¹⟩
    · intro hf
      exact hout g hg (mem_principalNormalizer_of_fixed_orbit g (principalFlag_four_fixed _ hf))
  have hnoncompact := principal_fixed_component_noncompact_of_layer A isClosed_closure
    (fun p hp t => closure_principalOrbitUnion_invariant Y hp t)
    10 (by decide) principalBase hpD (closure_mono hYlayer hbY)
  let C := connectedComponentIn (principalFixedDomain A) principalBase
  have hbaseC : principalBase ∈ closure (C \ {principalBase}) :=
    mem_closure_diff_singleton_of_preconnected_noncompact C isPreconnected_connectedComponentIn
      principalBase (mem_connectedComponentIn hpD) hnoncompact
  let p0 : principalSectionDomain := ⟨principalBase, principalBase_mem_sectionDomain⟩
  have hcl : p0 ∈ closure (Subtype.val ⁻¹' (C \ {principalBase})) := by
    rw [← isOpen_principalSectionDomain.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (C \ {principalBase})]
    exact hbaseC
  have hsub : principalSection '' (Subtype.val ⁻¹' (C \ {principalBase})) ⊆
      principalNormalizerReturn M := by
    rintro g ⟨p, hp, rfl⟩
    have hpD' := connectedComponentIn_subset (principalFixedDomain A) principalBase hp.1
    have hprange : p.val ∈ closure (range principalOrbitMap) :=
      closure_mono (principalOrbitUnion_subset_range M) hpD'.1
    have hsection := principalOrbitMap_principalSection_of_closure p hprange
    refine ⟨mem_principalNormalizer_of_fixed_orbit _ ?_,
      principalSection_mem_closure_doubleOrbit M p hpD'.1, ?_⟩
    · intro t
      rw [hsection]
      exact principalFlag_four_fixed _ hpD'.2 t
    · intro hV
      have hb := (principalOrbitMap_eq_base_iff _).mpr hV
      rw [hsection] at hb
      exact hp.2 hb
  have hi := closure_mono hsub (mem_closure_image continuous_principalSection.continuousAt hcl)
  simpa only [p0, principalSection_base] using hi

theorem principalDoubleOrbit_mono {M N : Set SL3} (hMN : M ⊆ N) :
    principalDoubleOrbit M ⊆ principalDoubleOrbit N := by
  rintro g ⟨s, m, hm, t, hg⟩
  exact ⟨s, m, hMN hm, t, hg⟩

theorem principalNormalizerReturn_mono {M N : Set SL3} (hMN : M ⊆ N) :
    principalNormalizerReturn M ⊆ principalNormalizerReturn N :=
  fun _ h => ⟨h.1, closure_mono (principalDoubleOrbit_mono hMN) h.2.1, h.2.2⟩

theorem subset_principalDoubleOrbit (M : Set SL3) : M ⊆ principalDoubleOrbit M := by
  intro g hg
  exact ⟨0, g, hg, 0, by simp [unipotentOne_zero]⟩

/-- The full V₁ enlargement, allowing M to meet its normalizer. This handles
that case by the actual normalizer elements already in M. -/
theorem principal_normalizer_enlargement (M : Set SL3)
    (hbase : (1 : SL3) ∈ closure M) (hout : ∀ g ∈ M, g ∉ principalUnipotent) :
    (1 : SL3) ∈ closure (principalNormalizerReturn M) := by
  let N : Set SL3 := Subgroup.normalizer (principalUnipotent : Set SL3)
  by_cases hnear : (1 : SL3) ∈ closure (M \ N)
  · have h := principal_normalizer_enlargement_of_outside_normalizer (M \ N) hnear
      (fun g hg => hg.2)
    exact closure_mono (principalNormalizerReturn_mono sdiff_subset) h
  · have hcover : M ⊆ (M \ N) ∪ (M ∩ N) := by
      intro g hg
      by_cases hn : g ∈ N
      · exact Or.inr ⟨hg, hn⟩
      · exact Or.inl ⟨hg, hn⟩
    have hb := closure_mono hcover hbase
    rw [closure_union] at hb
    have hin : (1 : SL3) ∈ closure (M ∩ N) := hb.resolve_left hnear
    apply closure_mono ?_ hin
    intro g hg
    exact ⟨hg.2, subset_closure (subset_principalDoubleOrbit M hg.1), hout g hg.1⟩

end JSP400

#print axioms JSP400.principal_normalizer_enlargement_of_outside_normalizer
#print axioms JSP400.principal_normalizer_enlargement
