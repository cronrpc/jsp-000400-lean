import CompactRepresentatives
import Mathlib.Topology.Compactness.LocallyCompact

namespace JSP400

open Set Topology

/-- A compact set in an open quotient has a compact collection of representatives.
This is a finite-cover argument; it does not require the whole preimage compact. -/
theorem compact_lift_of_open_quotient {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [WeaklyLocallyCompactSpace X]
    {f : X → Y} (hf : IsOpenQuotientMap f) {K : Set Y} (hK : IsCompact K) :
    ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  classical
  choose x hx using hf.surjective
  choose C hC hCx using fun y : Y => exists_compact_mem_nhds (x y)
  have hcover : K ⊆ ⋃ y : Y, f '' interior (C y) := by
    intro y hy
    exact mem_iUnion.mpr ⟨y, x y, mem_interior_iff_mem_nhds.mpr (hCx y), hx y⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun y => f '' interior (C y))
    (fun y => hf.isOpenMap _ isOpen_interior) hcover
  refine ⟨⋃ y ∈ I, C y, I.isCompact_biUnion (fun y hy => hC y), ?_⟩
  intro y hy
  obtain ⟨z, hzI, p, hp, hpy⟩ := mem_iUnion₂.mp (hI hy)
  exact ⟨p, mem_iUnion₂.mpr ⟨z, hzI, interior_subset hp⟩, hpy⟩

/-- Actual compact lifting for the space SL(3,ℝ)/SL(3,ℤ). -/
theorem compact_lattice_representatives {K : Set LatticeSpace} (hK : IsCompact K) :
    ∃ C : Set SL3, IsCompact C ∧ K ⊆ (QuotientGroup.mk : SL3 → LatticeSpace) '' C := by
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  have : WeaklyLocallyCompactSpace SL3 :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.weaklyLocallyCompactSpace
  exact compact_lift_of_open_quotient QuotientGroup.isOpenQuotientMap_mk hK

/-- Every actual compact family of unimodular lattices has a uniform positive
lower bound for the norm of every nonzero lattice vector. -/
theorem compact_lattices_lower_bound {K : Set LatticeSpace} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ L ∈ K, ∀ w ∈ quotientLatticePoints L,
      w ≠ 0 → ε ≤ ‖w‖ := by
  obtain ⟨C, hC, hcover⟩ := compact_lattice_representatives hK
  obtain ⟨ε, hε, hbound⟩ := compact_representatives_lower_bound hC
  refine ⟨ε, hε, ?_⟩
  intro L hL w hw hnz
  obtain ⟨g, hg, rfl⟩ := hcover hL
  obtain ⟨v, rfl⟩ := hw
  apply hbound g hg v
  intro hv
  apply hnz
  subst v
  have hz : integerVector (0 : IntegerVector3) = 0 := by
    ext i
    simp [integerVector]
  simp only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, hz]
  exact Matrix.mulVec_zero g.val

end JSP400
