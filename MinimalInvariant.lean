import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Compactness.Compact

/-!
The minimal closed invariant subset used in Margulis's compact-orbit argument.
Its existence is proved from Zorn's lemma and the compact intersection theorem.
No assumption about a homogeneous orbit's compactness is discharged here.
-/

namespace JSP400

open Set
open scoped Pointwise

variable {G X : Type*} [Monoid G] [TopologicalSpace X] [MulAction G X]

def Invariant (Y : Set X) : Prop := ∀ g : G, ∀ x ∈ Y, g • x ∈ Y

/-- A genuine minimal closed invariant subset of any nonempty compact closed
invariant set, without an assumed minimal-set selection oracle. -/
theorem exists_minimal_closed_invariant {K : Set X}
    (hK : IsCompact K) (hKc : IsClosed K) (hKn : K.Nonempty)
    (hKi : Invariant (G := G) K) :
    ∃ Y : Set X, Y ⊆ K ∧ IsClosed Y ∧ Y.Nonempty ∧ Invariant (G := G) Y ∧
      ∀ Z : Set X, Z ⊆ Y → IsClosed Z → Z.Nonempty → Invariant (G := G) Z → Z = Y := by
  classical
  let S : Set (Set X) := {Y | Y ⊆ K ∧ IsClosed Y ∧ Y.Nonempty ∧ Invariant (G := G) Y}
  have hKS : K ∈ S := ⟨Subset.rfl, hKc, hKn, hKi⟩
  have H : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain hne
    obtain ⟨t, ht⟩ := hne
    have : Nonempty c := ⟨⟨t, ht⟩⟩
    refine ⟨⋂₀ c, ⟨?_, ?_, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
    · exact (sInter_subset_of_mem ht).trans (hc ht).1
    · exact isClosed_sInter (fun s hs => (hc hs).2.1)
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (by
          intro a ha b hb
          rcases hchain.total ha hb with hab | hba
          · exact ⟨a, ha, Subset.rfl, hab⟩
          · exact ⟨b, hb, hba, Subset.rfl⟩)
        (fun s hs => (hc hs).2.2.1)
        (fun s hs => hK.of_isClosed_subset (hc hs).2.1 (hc hs).1)
        (fun s hs => (hc hs).2.1)
    · intro g x hx
      apply mem_sInter.mpr
      intro s hs
      exact (hc hs).2.2.2 g x (mem_sInter.mp hx s hs)
  obtain ⟨Y, hYK, hY⟩ := zorn_superset_nonempty S H K hKS
  refine ⟨Y, hYK, hY.prop.2.1, hY.prop.2.2.1, hY.prop.2.2.2, ?_⟩
  intro Z hZY hZc hZn hZi
  exact hY.eq_of_subset ⟨hZY.trans hYK, hZc, hZn, hZi⟩ hZY

/-- The resulting subset has dense orbits in exactly the needed relative sense. -/
theorem minimal_invariant_orbit_closure [ContinuousConstSMul G X]
    {Y : Set X} (hYc : IsClosed Y) (hYi : Invariant (G := G) Y)
    (hmin : ∀ Z : Set X, Z ⊆ Y → IsClosed Z → Z.Nonempty →
      Invariant (G := G) Z → Z = Y)
    {x : X} (hx : x ∈ Y) : closure (MulAction.orbit G x) = Y := by
  apply hmin
  · apply closure_minimal _ hYc
    rintro y ⟨g, rfl⟩
    exact hYi g x hx
  · exact isClosed_closure
  · exact (MulAction.nonempty_orbit x).closure
  · intro g y hy
    exact smul_closure_orbit_subset g x ⟨y, hy, rfl⟩

end JSP400
