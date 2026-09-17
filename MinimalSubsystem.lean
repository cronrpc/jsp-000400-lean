import MinimalHitting

/-! Compact minimal subsystems for the actual restricted subgroup action. -/

namespace JSP400

open Set

variable {G X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]

theorem exists_compact_minimal_subgroup (F : Subgroup G) {K : Set X}
    (hK : IsCompact K) (hKclosed : IsClosed K) (hKne : K.Nonempty)
    (hKi : subgroupInvariant F K) :
    ∃ Y : Set X, Y ⊆ K ∧ IsCompact Y ∧ IsClosed Y ∧ Y.Nonempty ∧
      subgroupInvariant F Y ∧ ∀ y ∈ Y, closure (MulAction.orbit F y) = Y := by
  have hKi' : Invariant (G := F) K := fun f => hKi f.val f.property
  obtain ⟨Y, hYK, hYclosed, hYne, hYi, hmin⟩ :=
    exists_minimal_closed_invariant hK hKclosed hKne hKi'
  refine ⟨Y, hYK, hK.of_isClosed_subset hYclosed hYK, hYclosed, hYne, ?_, ?_⟩
  · intro f hf
    exact hYi ⟨f, hf⟩
  · intro y hy
    exact minimal_invariant_orbit_closure hYclosed hYi hmin hy

theorem subgroupInvariant_orbit_closure (F : Subgroup G) (y : X) :
    subgroupInvariant F (closure (MulAction.orbit F y)) := by
  intro f hf z hz
  exact smul_closure_orbit_subset (⟨f, hf⟩ : F) y ⟨z, hz, rfl⟩

theorem exists_minimal_subsystem_of_compact_orbit_closure (F : Subgroup G) (y : X)
    (hc : IsCompact (closure (MulAction.orbit F y))) :
    ∃ Y : Set X, Y ⊆ closure (MulAction.orbit F y) ∧ IsCompact Y ∧ IsClosed Y ∧
      Y.Nonempty ∧ subgroupInvariant F Y ∧
        ∀ z ∈ Y, closure (MulAction.orbit F z) = Y :=
  exists_compact_minimal_subgroup F hc isClosed_closure
    (MulAction.nonempty_orbit y).closure (subgroupInvariant_orbit_closure F y)

end JSP400
