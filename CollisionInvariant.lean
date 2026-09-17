import MargulisLemma5
import MinimalHitting

namespace JSP400

open Set

section General

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The actual setwise preserving subgroup, expressed by both inclusions. -/
def preservingSubgroup (Y : Set X) : Subgroup G where
  carrier := {g | (∀ y ∈ Y, g • y ∈ Y) ∧ (∀ y ∈ Y, g⁻¹ • y ∈ Y)}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨hg, hgi⟩ ⟨hh, hhi⟩
    constructor
    · intro y hy
      simpa only [mul_smul] using hg _ (hh y hy)
    · intro y hy
      simpa only [mul_inv_rev, mul_smul] using hhi _ (hgi y hy)
  inv_mem' := by
    rintro g ⟨hg, hgi⟩
    exact ⟨hgi, by simpa using hg⟩

theorem preservingSubgroup_isClosed {Y : Set X} (hY : IsClosed Y) :
    IsClosed (preservingSubgroup (G := G) Y : Set G) := by
  change IsClosed {g : G | (∀ y ∈ Y, g • y ∈ Y) ∧ (∀ y ∈ Y, g⁻¹ • y ∈ Y)}
  have hforward : IsClosed {g : G | ∀ y ∈ Y, g • y ∈ Y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      hY.preimage (continuous_id.smul continuous_const)))
  have hback : IsClosed {g : G | ∀ y ∈ Y, g⁻¹ • y ∈ Y} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun y => isClosed_iInter (fun _ =>
      hY.preimage (continuous_inv.smul continuous_const)))
  exact hforward.inter hback

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [ContinuousSMul G X] in
theorem mem_preservingSubgroup_of_image_eq {Y : Set X} {g : G}
    (h : (fun y => g • y) '' Y = Y) : g ∈ preservingSubgroup Y := by
  constructor
  · intro y hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro y hy
    rw [← h] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx

end General

theorem principalDoubleOrbit_eq_mixedDoubleSet (M : Set SL3) :
    principalDoubleOrbit M = mixedDoubleSet principalUnipotent principalUnipotent M := by
  ext g
  constructor
  · rintro ⟨s, m, hm, t, h⟩
    exact ⟨unipotentOne s, ⟨s, rfl⟩, m, hm, unipotentOne t, ⟨t, rfl⟩, h⟩
  · rintro ⟨q, ⟨s, rfl⟩, m, hm, p, ⟨t, rfl⟩, h⟩
    exact ⟨s, m, hm, t, h⟩

/-- Every element of the full closed generated group of Lemma 5 preserves
the compact minimal set. This discharges the dynamical use of Lemma 3. -/
theorem principalEnlargementGroup_invariant (M : Set SL3) {Y : Set LatticeSpace}
    (hY : IsCompact Y) (hYc : IsClosed Y)
    (hV : subgroupInvariant principalUnipotent Y)
    (hM : M ⊆ hittingSet Y Y)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit principalUnipotent y) = Y) :
    subgroupInvariant (principalEnlargementGroup M) Y := by
  have hgeneration : Subgroup.closure
      ((Subgroup.normalizer (principalUnipotent : Set SL3) : Set SL3) ∩
        closure (principalDoubleOrbit M)) ≤ preservingSubgroup Y := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    apply mem_preservingSubgroup_of_image_eq
    apply margulis_lemma3 principalUnipotent principalUnipotent M hY hYc hV le_rfl hM hmin hg.1
    simpa only [principalDoubleOrbit_eq_mixedDoubleSet] using hg.2
  have hclosed : principalEnlargementGroup M ≤ preservingSubgroup Y := by
    exact closure_minimal hgeneration (preservingSubgroup_isClosed hYc)
  intro g hg y hy
  exact (hclosed hg).1 y hy

end JSP400

