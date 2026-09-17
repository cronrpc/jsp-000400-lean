import MinimalCollision
import Mathlib.GroupTheory.GroupAction.Quotient

namespace JSP400

open Set

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

theorem isCompact_orbit_of_compact_stabilizer_quotient (F : Subgroup G) (y : X)
    [CompactSpace (F ⧸ MulAction.stabilizer F y)] : IsCompact (MulAction.orbit F y) := by
  have hc : Continuous (MulAction.ofQuotientStabilizer F y) := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact continuous_id.smul continuous_const
  have hi := isCompact_univ.image hc
  have he : MulAction.ofQuotientStabilizer F y '' univ = MulAction.orbit F y := by
    ext z
    constructor
    · rintro ⟨q, _, rfl⟩
      exact MulAction.ofQuotientStabilizer_mem_orbit F y q
    · rintro ⟨f, rfl⟩
      exact ⟨QuotientGroup.mk f, mem_univ _, rfl⟩
  rwa [he] at hi

omit [IsTopologicalGroup G] [ContinuousSMul G X] in
/-- Absence of transverse returns near the identity turns accumulation of one
subgroup orbit at y into actual membership in the subgroup orbit of y. -/
theorem mem_orbit_of_no_transverse_returns (F : Subgroup G) (y z : X) (K : Set X)
    (hopen : IsOpenMap (fun g : G => g • y))
    (hcl : y ∈ closure (MulAction.orbit F z)) (hK : MulAction.orbit F z ⊆ K)
    (hno : (1 : G) ∉ closure {g : G | g ∉ F ∧ g • y ∈ K}) :
    z ∈ MulAction.orbit F y := by
  let U : Set G := (closure {g : G | g ∉ F ∧ g • y ∈ K})ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  have h1 : (1 : G) ∈ U := hno
  have hO := hopen _ hU
  have hy : y ∈ (fun g : G => g • y) '' U := ⟨1, h1, one_smul G y⟩
  obtain ⟨w, ⟨g, hg, hgw⟩, ⟨f, hfw⟩⟩ := mem_closure_iff.mp hcl _ hO hy
  change g • y = w at hgw
  change f.val • z = w at hfw
  have hgyK : g • y ∈ K := hgw.symm ▸ hK ⟨f, hfw⟩
  have hgf : g ∈ F := by
    by_contra hn
    exact hg (subset_closure ⟨hn, hgyK⟩)
  refine ⟨f⁻¹ * (⟨g, hgf⟩ : F), ?_⟩
  change (f.val⁻¹ * g) • y = z
  rw [mul_smul, hgw, ← hfw, inv_smul_smul]

end JSP400
