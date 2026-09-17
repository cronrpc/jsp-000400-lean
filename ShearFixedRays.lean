import ShearFixedSpace
import Mathlib.Topology.Order.IntermediateValue

namespace JSP400

open Set Matrix

/-- A closed connected noncompact subset of the real line containing zero
contains at least one of the two full rays from zero. -/
theorem noncompact_real_connected_contains_ray
    (S : Set ℝ) (hclosed : IsClosed S) (hconn : IsPreconnected S)
    (hzero : 0 ∈ S) (hnoncompact : ¬ IsCompact S) :
    Ici 0 ⊆ S ∨ Iic 0 ⊆ S := by
  by_contra h
  obtain ⟨hp, hm⟩ := not_or.mp h
  obtain ⟨p, hp0, hpS⟩ := Set.not_subset.mp hp
  obtain ⟨m, hm0, hmS⟩ := Set.not_subset.mp hm
  have hbound : S ⊆ Icc m p := by
    intro x hx
    constructor
    · by_contra hmx
      have hxm : x ≤ m := le_of_lt (lt_of_not_ge hmx)
      exact hmS (hconn.ordConnected.out hx hzero ⟨hxm, hm0⟩)
    · by_contra hxp
      have hpx : p ≤ x := le_of_lt (lt_of_not_ge hxp)
      exact hpS (hconn.ordConnected.out hzero hx ⟨hp0, hpx⟩)
  exact hnoncompact (isCompact_Icc.of_isClosed_subset hclosed hbound)

theorem continuous_shearFixedLine : Continuous shearFixedLine := by
  unfold shearFixedLine
  fun_prop

/-- The final affine-line step of Lemma 6(B2). Its hypotheses are properties
of an actual closed connected subset, rather than a prescribed ray. -/
theorem shear_fixed_line_contains_ray
    (S : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hclosed : IsClosed S) (hconn : IsPreconnected S)
    (hzero : shearFixedLine 0 ∈ S) (hnoncompact : ¬ IsCompact S)
    (hline : S ⊆ Set.range shearFixedLine) :
    shearFixedLine '' Ici 0 ⊆ S ∨ shearFixedLine '' Iic 0 ⊆ S := by
  let T : Set ℝ := shearFixedLine ⁻¹' S
  have himage : shearFixedLine '' T = S := Set.image_preimage_eq_iff.mpr hline
  have hcoord : T = (fun x : Matrix (Fin 3) (Fin 3) ℝ => x 0 2) '' S := by
    ext t
    constructor
    · intro ht
      exact ⟨shearFixedLine t, ht, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, rfl⟩ := hline hx
      exact hx
  have hTconn : IsPreconnected T := by
    rw [hcoord]
    exact hconn.image _ (by fun_prop)
  have hTclosed : IsClosed T := hclosed.preimage continuous_shearFixedLine
  have hTnoncompact : ¬ IsCompact T := by
    intro hT
    apply hnoncompact
    rw [← himage]
    exact hT.image continuous_shearFixedLine
  rcases noncompact_real_connected_contains_ray T hTclosed hTconn hzero hTnoncompact with h | h
  · exact Or.inl (fun x hx => by obtain ⟨t, ht, rfl⟩ := hx; exact h ht)
  · exact Or.inr (fun x hx => by obtain ⟨t, ht, rfl⟩ := hx; exact h ht)

end JSP400
