import MinimalCollision
import CompactLattices
import Mathlib.Topology.Algebra.ProperAction.Basic

/-! Margulis Lemma 4 for the actual lattice space SL(3,R)/SL(3,Z). -/

namespace JSP400

open Set

theorem isOpenMap_latticeOrbit (y : LatticeSpace) :
    IsOpenMap (fun g : SL3 => g • y) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  change IsOpenMap (fun g : SL3 => QuotientGroup.mk (g * h))
  exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap.comp (isOpenMap_mul_right h)

/-- A noncompact subgroup orbit with compact minimal closure has genuine
returning elements outside the subgroup arbitrarily close to the identity. -/
theorem margulis_lemma4 (F : Subgroup SL3) (hF : IsClosed (F : Set SL3))
    (y : LatticeSpace) (hc : IsCompact (closure (MulAction.orbit F y)))
    (hmin : ∀ z ∈ closure (MulAction.orbit F y),
      closure (MulAction.orbit F z) = closure (MulAction.orbit F y))
    (hnc : ¬ CompactSpace (F ⧸ (MulAction.stabilizer SL3 y).comap F.subtype)) :
    (1 : SL3) ∈ closure {g : SL3 | g ∉ F ∧ g • y ∈ MulAction.orbit F y} := by
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  have : WeaklyLocallyCompactSpace SL3 :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.weaklyLocallyCompactSpace
  exact margulis_lemma4_of_open_orbit F hF y (isOpenMap_latticeOrbit y) hc hmin hnc

end JSP400
