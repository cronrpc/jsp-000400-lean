import PositiveNormalizerQuotient
import CompactHOrbit

namespace JSP400

open Matrix Set

theorem diagonal_translation_commutator (t : ℝ) (ht : t ≠ 0) (r : ℝ) :
    diagonalFlow t ht *
      (unipotentTwo r * diagonalFlow t⁻¹ (inv_ne_zero ht) * (unipotentTwo r)⁻¹) =
        unipotentTwo ((t ^ 2 - 1) * r) := by
  have hinv : (unipotentTwo r)⁻¹ = unipotentTwo (-r) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← unipotentTwo_add, add_neg_cancel, unipotentTwo_zero]
  rw [← diagonalFlow_inv_eq t ht, hinv]
  rw [← mul_assoc, ← mul_assoc, diagonalFlow_unipotentTwo]
  simp only [mul_assoc, mul_inv_cancel, one_mul]
  rw [← unipotentTwo_add]
  congr 1
  ring

theorem compact_standard_invariant_no_signed_ray {K : Set LatticeSpace}
    (hK : IsCompact K) (hKc : IsClosed K)
    (hH : subgroupInvariant (formStabilizer standardForm) K)
    (y : LatticeSpace) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (hray : ∀ b : ℝ, 0 < σ * b → unipotentTwo b • y ∈ K) : False := by
  have hsub : signedShearOrbit y σ ⊆ K := by
    rintro z ⟨t, ht, a, b, hb, rfl⟩
    simp only [mul_smul]
    exact hH _ (diagonalFlow_mem_standardStabilizer _ _) _
      (hH _ (unipotentOne_mem_standardStabilizer a) _ (hray b hb))
  exact margulis_lemma11 y σ hσ
    (hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hKc))

/-- The compactness step after Lemma 5(II): a preserving subgroup cannot have
translations or dilations about a nonzero point. Therefore the selected set
is invariant under the original positive diagonal group. -/
theorem diagonal_invariant_of_subgroup_alternative (T : Subgroup SL3)
    {Y K : Set LatticeSpace} (hYn : Y.Nonempty) (hYK : Y ⊆ K)
    (hTY : subgroupInvariant T Y) (hK : IsCompact K) (hKc : IsClosed K)
    (hH : subgroupInvariant (formStabilizer standardForm) K)
    (halt : (∀ b : ℝ, unipotentTwo b ∈ T) ∨
      ∃ r : ℝ, ∀ t : ℝ, ∀ ht : 0 < t,
        unipotentTwo r * diagonalFlow t (ne_of_gt ht) * (unipotentTwo r)⁻¹ ∈ T) :
    ∀ t : ℝ, ∀ ht : 0 < t, ∀ y ∈ Y, diagonalFlow t (ne_of_gt ht) • y ∈ Y := by
  obtain ⟨y, hy⟩ := hYn
  rcases halt with htr | ⟨r, hd⟩
  · exact False.elim (compact_standard_invariant_no_signed_ray hK hKc hH y 1 (by norm_num)
      (fun b _ => hYK (hTY _ (htr b) y hy)))
  · have hr0 : r = 0 := by
      by_contra hr
      have hray (b : ℝ) (hb : 0 < b / r) : unipotentTwo b • y ∈ K := by
        let t := Real.sqrt (1 + b / r)
        have htp : 0 < t := Real.sqrt_pos.mpr (by linarith)
        have hs : (t ^ 2 - 1) * r = b := by
          dsimp [t]
          rw [Real.sq_sqrt (by linarith : 0 ≤ 1 + b / r)]
          field_simp
          ring
        have hmem := hTY _ (hd t⁻¹ (inv_pos.mpr htp)) y hy
        have hKmem := hH _ (diagonalFlow_mem_standardStabilizer t (ne_of_gt htp)) _ (hYK hmem)
        rw [← mul_smul, diagonal_translation_commutator, hs] at hKmem
        exact hKmem
      rcases lt_or_gt_of_ne hr with hn | hp
      · exact compact_standard_invariant_no_signed_ray hK hKc hH y (-1) (by norm_num)
          (fun b hb => hray b (div_pos_of_neg_of_neg (by nlinarith) hn))
      · exact compact_standard_invariant_no_signed_ray hK hKc hH y 1 (by norm_num)
          (fun b hb => hray b (div_pos (by simpa using hb) hp))
    subst r
    intro t ht x hx
    have hdt := hd t ht
    simp only [unipotentTwo_zero, one_mul, inv_one, mul_one] at hdt
    exact hTY _ hdt x hx

end JSP400
