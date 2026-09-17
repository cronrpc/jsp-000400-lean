import CurveTruncation

/-! A compact connected set's component inside a proper closed subset reaches
that subset's boundary. This supplies the boundary step in the dimension descent. -/

namespace JSP400

open Set Filter TopologicalSpace
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Compact Hausdorff component neighborhoods admit clopen refinements. -/
theorem exists_clopen_component_neighborhood [CompactSpace X] (p : X)
    {U : Set X} (hU : IsOpen U) (hCU : connectedComponent p ⊆ U) :
    ∃ V : Set X, IsClopen V ∧ p ∈ V ∧ V ⊆ U := by
  let I := {s : Set X // IsClopen s ∧ p ∈ s}
  have hd : Disjoint Uᶜ (⋂ i : I, (i : Set X)) := by
    change Disjoint Uᶜ (⋂ i : {s : Set X // IsClopen s ∧ p ∈ s}, (i : Set X))
    rw [← connectedComponent_eq_iInter_isClopen]
    exact disjoint_compl_left_iff_subset.mpr hCU
  obtain ⟨F, hF⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun i : I => (i : Set X)) (fun i => i.2.1.isClosed) hd
  refine ⟨⋂ i ∈ F, (i : Set X), isClopen_biInter_finset (fun i _ => i.2.1),
    mem_iInter₂.mpr (fun i _ => i.2.2), ?_⟩
  exact disjoint_compl_left_iff_subset.mp hF

/-- Boundary bumping for a proper closed subset of a compact continuum. -/
theorem compact_connected_boundary_bumping [CompactSpace X] [ConnectedSpace X]
    {A : Set X} (hA : IsClosed A) (hproper : A ≠ univ) {p : X} (hp : p ∈ A) :
    (connectedComponentIn A p ∩ closure Aᶜ).Nonempty := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  by_contra hn
  have havoid : connectedComponent (⟨p, hp⟩ : A) ⊆
      (Subtype.val ⁻¹' (closure Aᶜ)ᶜ) := by
    intro q hq hqb
    apply hn
    refine ⟨q.val, ?_, hqb⟩
    rw [connectedComponentIn_eq_image hp]
    exact ⟨q, hq, rfl⟩
  obtain ⟨V, hV, hpV, hVU⟩ := exists_clopen_component_neighborhood (⟨p, hp⟩ : A)
    (isClosed_closure.isOpen_compl.preimage continuous_subtype_val) havoid
  have himageClosed : IsClosed (Subtype.val '' V : Set X) :=
    (hV.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hVI : (Subtype.val '' V : Set X) ⊆ interior A := by
    rintro x ⟨a, ha, rfl⟩
    have h := hVU ha
    simpa only [mem_preimage, closure_compl, compl_compl] using h
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV.isOpen
  have he : (Subtype.val '' V : Set X) = O ∩ interior A := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, hVI hx⟩
      obtain ⟨a, ha, rfl⟩ := hx
      rw [← hOV] at ha
      exact ha
    · rintro ⟨hxO, hxI⟩
      refine ⟨⟨x, interior_subset hxI⟩, ?_, rfl⟩
      rw [← hOV]
      exact hxO
  have himageOpen : IsOpen (Subtype.val '' V : Set X) := he ▸ hO.inter isOpen_interior
  have hall : (Subtype.val '' V : Set X) = univ :=
    (show IsClopen (Subtype.val '' V : Set X) from ⟨himageClosed, himageOpen⟩).eq_univ
      ⟨p, ⟨⟨p, hp⟩, hpV, rfl⟩⟩
  apply hproper
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ (Subtype.val '' V : Set X) := hall ▸ mem_univ x
  obtain ⟨a, _, rfl⟩ := hx
  exact a.property

/-- The ambient-set form of boundary bumping, with its actual relative closure. -/
theorem compact_connected_set_boundary_bumping {K F : Set X}
    (hK : IsCompact K) (hconn : IsConnected K) (hF : IsClosed F)
    (hnot : ¬K ⊆ F) {p : X} (hpK : p ∈ K) (hpF : p ∈ F) :
    (connectedComponentIn (K ∩ F) p ∩ closure (K \ F)).Nonempty := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hconn
  let A : Set K := Subtype.val ⁻¹' F
  have hA : IsClosed A := hF.preimage continuous_subtype_val
  have hproper : A ≠ univ := by
    intro he
    apply hnot
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ A := he ▸ mem_univ _
    exact this
  let pK : K := ⟨p, hpK⟩
  have hpA : pK ∈ A := hpF
  obtain ⟨q, hqcomp, hqbd⟩ := compact_connected_boundary_bumping hA hproper hpA
  refine ⟨q.val, ?_, ?_⟩
  · have hc : IsPreconnected (Subtype.val '' connectedComponentIn A pK : Set X) :=
      isPreconnected_connectedComponentIn.image Subtype.val continuous_subtype_val.continuousOn
    apply hc.subset_connectedComponentIn
      ⟨pK, mem_connectedComponentIn hpA, rfl⟩ _ ⟨q, hqcomp, rfl⟩
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a.property, connectedComponentIn_subset A pK ha⟩
  · have hqim : q.val ∈ closure (Subtype.val '' Aᶜ : Set X) :=
      mem_closure_image continuous_subtype_val.continuousAt hqbd
    apply closure_mono ?_ hqim
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a.property, ha⟩

/-- The boundary point used for dimension descent: if the fixed-set component
is compact, an unbounded-curve upper limit forces that component to touch the
closure of the nonfixed part. -/
theorem upper_limit_fixed_component_boundary
    {E : Type*} [MetricSpace E] [ProperSpace E] [SecondCountableTopology E]
    (S : ℕ → Set E) (f : ℕ → ℝ → E) (p : E)
    (hf : ∀ n, ContinuousOn (f n) (Ici 0))
    (hmem : ∀ n t, 0 ≤ t → f n t ∈ S n)
    (hunb : ∀ n R, ∃ t : ℝ, 0 ≤ t ∧ R < dist (f n t) p)
    (hp : Tendsto (fun n => f n 0) atTop (𝓝 p))
    {A F : Set E} (hA : upperSetLimit S ⊆ A) (hF : IsClosed F) (hpF : p ∈ F)
    (hc : IsCompact (connectedComponentIn (A ∩ F) p)) :
    (connectedComponentIn (A ∩ F) p ∩ closure (A \ F)).Nonempty := by
  obtain ⟨M, hM⟩ := hc.bddAbove_image (continuous_id.dist continuous_const).continuousOn
  obtain ⟨L, hLS, hconn, hpL, q, hqL, hqR⟩ :=
    upper_limit_connected_witness S f p hf hmem hunb hp (max M 0 + 1) (by positivity)
  have hLA : (L : Set E) ⊆ A := hLS.trans hA
  have hnot : ¬(L : Set E) ⊆ F := by
    intro hLF
    have hLC := hconn.subset_connectedComponentIn hpL (subset_inter hLA hLF)
    have hbd : dist q p ≤ M := hM ⟨q, hLC hqL, rfl⟩
    have he : dist q p = max M 0 + 1 := hqR
    have : M ≤ max M 0 := le_max_left _ _
    linarith
  obtain ⟨b, hbcomp, hbbd⟩ := compact_connected_set_boundary_bumping L.isCompact
    ⟨⟨p, hpL⟩, hconn⟩ hF hnot hpL hpF
  refine ⟨b, ?_, closure_mono (sdiff_subset_sdiff_left hLA) hbbd⟩
  exact (isPreconnected_connectedComponentIn (F := (L : Set E) ∩ F) (x := p)).subset_connectedComponentIn
    (mem_connectedComponentIn (F := (L : Set E) ∩ F) ⟨hpL, hpF⟩)
    ((connectedComponentIn_subset ((L : Set E) ∩ F) p).trans
      (inter_subset_inter_left F hLA)) hbcomp

end JSP400
