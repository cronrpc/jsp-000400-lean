import MinimalHitting
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.LocallyCompact

/-! The compact local-cover argument underlying Margulis Lemma 4. -/

namespace JSP400

open Set
open scoped Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [T2Space X] [MulAction G X] [ContinuousSMul G X]

omit [T2Space X] in
/-- A compact local set of orbit representatives and minimality give compactness
of the actual subgroup/stabilizer quotient, with its quotient topology. -/
theorem compact_stabilizer_quotient_of_local_cover (F : Subgroup G) (y : X)
    {Y : Set X} (hY : IsCompact Y) (hy : y ∈ Y) (hYi : subgroupInvariant F Y)
    (hmin : ∀ z ∈ Y, closure (MulAction.orbit F z) = Y)
    (C : Set F) (hC : IsCompact C) (O : Set X) (hO : IsOpen O) (hyO : y ∈ O)
    (hlocal : O ∩ Y ⊆ (fun f : F => f • y) '' C) :
    CompactSpace (F ⧸ MulAction.stabilizer F y) := by
  classical
  let V : F → Set X := fun f => {z | f • z ∈ O}
  have hV : ∀ f, IsOpen (V f) := fun f =>
    hO.preimage (continuous_const_smul f)
  have hcover : Y ⊆ ⋃ f : F, V f := by
    intro z hz
    have hcl : y ∈ closure (MulAction.orbit F z) := hmin z hz ▸ hy
    obtain ⟨w, hwO, hw⟩ := mem_closure_iff.mp hcl O hO hyO
    obtain ⟨f, rfl⟩ := hw
    exact mem_iUnion.mpr ⟨f, hwO⟩
  obtain ⟨I, hI⟩ := hY.elim_finite_subcover V hV hcover
  let Q := F ⧸ MulAction.stabilizer F y
  let p : F → Q := QuotientGroup.mk
  let K : Set Q := ⋃ f ∈ I, (fun k : F => p (f⁻¹ * k)) '' C
  have hK : IsCompact K := I.isCompact_biUnion (fun f _ =>
    hC.image (QuotientGroup.continuous_mk.comp (continuous_const.mul continuous_id)))
  have hKall : K = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hgy : g • y ∈ Y := hYi g.val g.property y hy
    obtain ⟨f, hfI, hfg⟩ := mem_iUnion₂.mp (hI hgy)
    have hfgY : f • (g • y) ∈ Y := hYi f.val f.property _ hgy
    obtain ⟨k, hk, hkeq⟩ := hlocal ⟨hfg, hfgY⟩
    change k • y = f • (g • y) at hkeq
    apply mem_iUnion₂.mpr
    refine ⟨f, hfI, k, hk, ?_⟩
    apply QuotientGroup.eq.mpr
    change (f⁻¹ * k)⁻¹ * g ∈ MulAction.stabilizer F y
    rw [MulAction.mem_stabilizer_iff]
    have he : (f⁻¹ * k) • y = g • y := by
      rw [mul_smul, hkeq, inv_smul_smul]
    rw [mul_smul, ← he, inv_smul_smul]
  exact ⟨hKall ▸ hK⟩

/-- Margulis Lemma 4 for a locally compact group with an open orbit map.
The conclusion uses genuine return points outside the given closed subgroup. -/
theorem margulis_lemma4_of_open_orbit [LocallyCompactSpace G]
    (F : Subgroup G) (hF : IsClosed (F : Set G)) (y : X)
    (hopen : IsOpenMap (fun g : G => g • y))
    (hc : IsCompact (closure (MulAction.orbit F y)))
    (hmin : ∀ z ∈ closure (MulAction.orbit F y),
      closure (MulAction.orbit F z) = closure (MulAction.orbit F y))
    (hnc : ¬ CompactSpace (F ⧸ MulAction.stabilizer F y)) :
    (1 : G) ∈ closure {g : G | g ∉ F ∧ g • y ∈ MulAction.orbit F y} := by
  classical
  by_contra hn
  let S : Set G := {g | g ∉ F ∧ g • y ∈ MulAction.orbit F y}
  obtain ⟨K, hK, h1K, hKS⟩ := exists_compact_subset isClosed_closure.isOpen_compl hn
  let C : Set F := Subtype.val ⁻¹' K
  have hC : IsCompact C := hF.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  let O : Set X := (fun g : G => g • y) '' interior K
  have hO : IsOpen O := hopen _ isOpen_interior
  have hyO : y ∈ O := ⟨1, h1K, one_smul G y⟩
  have hloc : O ∩ MulAction.orbit F y ⊆ (fun f : F => f • y) '' C := by
    rintro z ⟨⟨g, hg, rfl⟩, hz⟩
    have hgf : g ∈ F := by
      by_contra hgf
      exact hKS (interior_subset hg) (subset_closure ⟨hgf, hz⟩)
    refine ⟨⟨g, hgf⟩, ?_, rfl⟩
    change g ∈ K
    exact interior_subset hg
  have hlocal : O ∩ closure (MulAction.orbit F y) ⊆
      (fun f : F => f • y) '' C := by
    exact hO.inter_closure.trans (closure_minimal hloc
      (hC.image (continuous_id.smul continuous_const)).isClosed)
  have hy : y ∈ closure (MulAction.orbit F y) :=
    subset_closure (MulAction.mem_orbit_self y)
  have hYi : subgroupInvariant F (closure (MulAction.orbit F y)) := by
    intro f hf z hz
    exact smul_closure_orbit_subset (⟨f, hf⟩ : F) y ⟨z, hz, rfl⟩
  exact hnc (compact_stabilizer_quotient_of_local_cover F y hc hy hYi hmin C hC O hO hyO hlocal)

end JSP400
