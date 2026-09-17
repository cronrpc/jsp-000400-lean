import IrrationalIntegerStabilizer
import CompactGroupQuotient
import UnipotentOneNormalizer

namespace JSP400

open Matrix Set

theorem standardStabilizer_not_isCompact : ¬ IsCompact (formStabilizer standardForm : Set SL3) := by
  intro hc
  have hf : Continuous (fun g : SL3 => g.val 0 0) :=
    (continuous_apply 0).comp (Matrix.SpecialLinearGroup.continuous_apply id continuous_id 0)
  obtain ⟨B, hB⟩ := hc.bddAbove_image hf.continuousOn
  let t := max 1 (B + 1)
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hb := hB (mem_image_of_mem _ (diagonalFlow_mem_standardStabilizer t (ne_of_gt ht)))
  change t ≤ B at hb
  have hlt : B < t := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  linarith

theorem ternaryStabilizer_not_isCompact {α : ℝ} (hα : 0 < α) :
    ¬ IsCompact (formStabilizer (ternaryForm α) : Set SL3) := by
  intro hc
  let s := standardizingSL α hα
  have hcont : Continuous (fun g : SL3 => s * g * s⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have himg := hc.image hcont
  have he : (fun g : SL3 => s * g * s⁻¹) '' (formStabilizer (ternaryForm α) : Set SL3) =
      (formStabilizer standardForm : Set SL3) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact (standardizingSL_conjugates hα h).mpr hh
    · intro hg
      refine ⟨s⁻¹ * g * s, ?_, by simp [mul_assoc]⟩
      apply (standardizingSL_conjugates hα _).mp
      change s * (s⁻¹ * g * s) * s⁻¹ ∈ formStabilizer standardForm
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      exact hg
  rw [he] at himg
  exact standardStabilizer_not_isCompact himg

/-- For the irrational form, its real stabilizer modulo its actual integer
stabilizer cannot be compact. The proof uses the explicit bounded integer
stabilizer and the noncompact diagonal subgroup after standardization. -/
theorem irrational_ternary_stabilizer_quotient_not_compact {α : ℝ}
    (hα : 0 < α) (hi : Irrational α) :
    ¬ CompactSpace ((formStabilizer (ternaryForm α)) ⧸
      integerGamma.comap (formStabilizer (ternaryForm α)).subtype) := by
  intro hquot
  let H := formStabilizer (ternaryForm α)
  let S := integerGamma.comap H.subtype
  have : CompactSpace (H ⧸ S) := hquot
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  have : WeaklyLocallyCompactSpace SL3 :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.weaklyLocallyCompactSpace
  have hHclosed : IsClosed (H : Set SL3) := ternaryStabilizer_isClosed α
  have : WeaklyLocallyCompactSpace H :=
    hHclosed.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace
  have hS : IsCompact (S : Set H) := by
    have he : (S : Set H) = Subtype.val ⁻¹'
        (((H ⊓ integerGamma : Subgroup SL3) : Set SL3)) := by
      ext g
      change g.val ∈ integerGamma ↔ g.val ∈ H ∧ g.val ∈ integerGamma
      exact ⟨fun h => ⟨g.property, h⟩, And.right⟩
    rw [he]
    exact hHclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
      (irrational_integer_stabilizer_isCompact hi)
  have : CompactSpace H := compactSpace_of_compact_subgroup_quotient S hS
  have hc : IsCompact (H : Set SL3) := by
    have h := isCompact_univ.image (continuous_subtype_val : Continuous (Subtype.val : H → SL3))
    have he : Subtype.val '' (univ : Set H) = (H : Set SL3) := by
      ext g
      exact ⟨fun ⟨x, _, hx⟩ => hx ▸ x.property, fun hg => ⟨⟨g, hg⟩, mem_univ _, rfl⟩⟩
    rwa [he] at h
  exact ternaryStabilizer_not_isCompact hα hc

end JSP400
