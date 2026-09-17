import CompactLattices
import Mathlib.GroupTheory.GroupAction.Quotient

namespace JSP400

open Set

theorem compactSpace_of_compact_subgroup_quotient {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [WeaklyLocallyCompactSpace G]
    (H : Subgroup G) (hH : IsCompact (H : Set G)) [CompactSpace (G ⧸ H)] :
    CompactSpace G := by
  obtain ⟨C, hC, hcover⟩ := compact_lift_of_open_quotient
    (QuotientGroup.isOpenQuotientMap_mk (N := H)) isCompact_univ
  have hcomp := (hC.prod hH).image (continuous_fst.mul continuous_snd)
  have he : (fun p : G × G => p.1 * p.2) '' (C ×ˢ (H : Set G)) = univ := by
    apply eq_univ_of_forall
    intro g
    obtain ⟨c, hc, heq⟩ := hcover (mem_univ (QuotientGroup.mk g : G ⧸ H))
    have hh : c⁻¹ * g ∈ H := QuotientGroup.eq.mp heq
    exact ⟨(c, c⁻¹ * g), ⟨hc, hh⟩, mul_inv_cancel_left c g⟩
  exact ⟨he ▸ hcomp⟩

theorem compact_quotient_of_surjective_hom {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f)
    (A : Subgroup G) (B : Subgroup H) (hAB : ∀ a ∈ A, f a ∈ B)
    [CompactSpace (G ⧸ A)] : CompactSpace (H ⧸ B) := by
  let p : G ⧸ A → H ⧸ B := Quotient.lift (fun g => QuotientGroup.mk (f g)) (by
    intro g h hgh
    apply QuotientGroup.eq.mpr
    have hmem := hAB (g⁻¹ * h) (QuotientGroup.eq.mp (Quotient.sound hgh))
    simpa only [map_mul, map_inv] using hmem)
  have hp : Continuous p := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact QuotientGroup.continuous_mk.comp hf
  have hsur : Function.Surjective p := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, rfl⟩ := hs h
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hi := isCompact_univ.image hp
  rw [image_univ, hsur.range_eq] at hi
  exact ⟨hi⟩

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X]

/-- Right translation transports the compact stabilizer quotient along an
actual orbit, without identifying the quotient topology with the orbit topology. -/
theorem compact_stabilizer_quotient_smul (y : X) (g : G)
    [CompactSpace (G ⧸ MulAction.stabilizer G y)] :
    CompactSpace (G ⧸ MulAction.stabilizer G (g • y)) := by
  let f : G ⧸ MulAction.stabilizer G y → G ⧸ MulAction.stabilizer G (g • y) :=
    Quotient.lift (fun h : G => QuotientGroup.mk (h * g⁻¹)) (by
      intro a b hab
      apply QuotientGroup.eq.mpr
      have h : a⁻¹ * b ∈ MulAction.stabilizer G y :=
        QuotientGroup.eq.mp (Quotient.sound hab)
      rw [MulAction.mem_stabilizer_iff] at h ⊢
      simp only [_root_.mul_inv_rev, inv_inv, mul_smul, inv_smul_smul]
      simpa only [mul_smul] using congrArg (fun x : X => g • x) h)
  have hf : Continuous f := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  have hs : Function.Surjective f := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨QuotientGroup.mk (h * g), ?_⟩
    change QuotientGroup.mk (h * g * g⁻¹) = QuotientGroup.mk h
    rw [mul_inv_cancel_right]
  have hi := isCompact_univ.image hf
  rw [Set.image_univ, hs.range_eq] at hi
  exact ⟨hi⟩

end JSP400
