import PrincipalRepresentation

namespace JSP400

open Set

theorem principalUnipotent_le_standardStabilizer :
    principalUnipotent ≤ formStabilizer standardForm := by
  rintro g ⟨t, rfl⟩
  exact unipotentOne_mem_standardStabilizer t

theorem unipotentTwo_conjugates_one (b a : ℝ) :
    unipotentTwo b * unipotentOne a * (unipotentTwo b)⁻¹ = unipotentOne a := by
  rw [← (unipotentOne_commute_unipotentTwo a b).eq, mul_assoc,
    mul_inv_cancel, mul_one]

theorem unipotentTwo_mem_principalNormalizer (b : ℝ) :
    unipotentTwo b ∈ Subgroup.normalizer (principalUnipotent : Set SL3) := by
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    rw [unipotentTwo_conjugates_one]
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have he := congrArg (fun x : SL3 => (unipotentTwo b)⁻¹ * x * unipotentTwo b) ha
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at he
    calc
      g = (unipotentTwo b)⁻¹ * unipotentOne a * unipotentTwo b := by
        simpa only [mul_assoc] using he
      _ = unipotentOne a := by
        rw [mul_assoc, (unipotentOne_commute_unipotentTwo a b).eq, ← mul_assoc,
          inv_mul_cancel, one_mul]

theorem diagonalFlow_conjugates_one (t : ℝ) (ht : t ≠ 0) (a : ℝ) :
    diagonalFlow t ht * unipotentOne a * (diagonalFlow t ht)⁻¹ =
      unipotentOne (t * a) := by
  rw [diagonalFlow_unipotentOne, mul_assoc, mul_inv_cancel, mul_one]

theorem diagonalFlow_mem_principalNormalizer (t : ℝ) (ht : t ≠ 0) :
    diagonalFlow t ht ∈ Subgroup.normalizer (principalUnipotent : Set SL3) := by
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    rw [diagonalFlow_conjugates_one]
    exact ⟨t * a, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨t⁻¹ * a, ?_⟩
    have he := congrArg (fun x : SL3 => (diagonalFlow t ht)⁻¹ * x * diagonalFlow t ht) ha
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at he
    calc
      g = (diagonalFlow t ht)⁻¹ * unipotentOne a * diagonalFlow t ht := by
        simpa only [mul_assoc] using he
      _ = unipotentOne (t⁻¹ * a) := by
        conv_lhs => rw [diagonalFlow_inv_eq]
        rw [diagonalFlow_unipotentOne]
        rw [mul_assoc, ← diagonalFlow_inv_eq t ht, inv_mul_cancel, mul_one]

end JSP400
