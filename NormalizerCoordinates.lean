import PrincipalFixed

namespace JSP400

open Matrix Set

theorem adjointAction_sub (g : SL3) (x y : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction g (x - y) = adjointAction g x - adjointAction g y := by
  simp [adjointAction, mul_sub, sub_mul]

theorem unipotentOne_log_polynomial (t : ℝ) :
    (unipotentOne t).val - 1 - (1 / 2 : ℝ) • ((unipotentOne t).val - 1) ^ 2 =
      t • shearFixedLine 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [unipotentOne, shearFixedLine, pow_two, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_succ]
  ring

theorem principalNormalizer_adjoint_base (g : SL3)
    (hg : g ∈ Subgroup.normalizer (principalUnipotent : Set SL3)) :
    ∃ a : ℝ, a ≠ 0 ∧ adjointAction g (shearFixedLine 0) = a • shearFixedLine 0 := by
  have hnorm := (Subgroup.mem_set_normalizer_iff.mp hg) (unipotentOne 1)
  change unipotentOne 1 ∈ principalUnipotent ↔
    g * unipotentOne 1 * g⁻¹ ∈ principalUnipotent at hnorm
  obtain ⟨a, ha⟩ := hnorm.mp ⟨1, rfl⟩
  have he : adjointAction g (unipotentOne 1).val = (unipotentOne a).val :=
    congrArg Subtype.val ha
  have hlog := congrArg (adjointAction g) (unipotentOne_log_polynomial 1)
  rw [adjointAction_sub, adjointAction_sub, adjointAction_smul, ← adjointAction_pow,
    adjointAction_sub, adjointAction_matrix_one, he, unipotentOne_log_polynomial] at hlog
  have hscaled : adjointAction g (shearFixedLine 0) = a • shearFixedLine 0 := by
    simpa only [one_smul] using hlog.symm
  have hane : a ≠ 0 := by
    intro hz
    have heq : adjointAction g (shearFixedLine 0) = adjointAction g 0 := by
      rw [hscaled, hz]
      simp [adjointAction]
    have hN := adjointAction_injective g heq
    have he01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 1) hN
    norm_num [shearFixedLine] at he01
  exact ⟨a, hane, hscaled⟩

/-- Explicit factorization of a matrix scaling the regular nilpotent N. This
uses only its actual entries and determinant one. The diagonal parameter may
have either sign; its positive component is the affine-group model. -/
theorem factor_of_adjoint_base_scaled (g : SL3) (a : ℝ) (ha : a ≠ 0)
    (hg : adjointAction g (shearFixedLine 0) = a • shearFixedLine 0) :
    g = unipotentOne (g.val 0 1) *
      unipotentTwo (a * g.val 0 2 - (g.val 0 1) ^ 2 / 2) * diagonalFlow a ha := by
  have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
  have he := congrArg (fun x : Matrix (Fin 3) (Fin 3) ℝ => x * g.val) hg
  have hm : g.val * shearFixedLine 0 = (a • shearFixedLine 0) * g.val := by
    simpa only [adjointAction, mul_assoc, hi, mul_one] using he
  have hentry (i j : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hm
  have h00 := hentry 0 0
  have h01 := hentry 0 1
  have h02 := hentry 0 2
  have h12 := hentry 1 2
  have h21 := hentry 2 1
  have h22 := hentry 2 2
  simp [shearFixedLine, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h01 h02 h12 h21 h22
  have h10 : g.val 1 0 = 0 := h00.resolve_left ha
  have hdiag2 : g.val 2 2 = g.val 1 1 / a := by apply (eq_div_iff ha).mpr; nlinarith [h12]
  have hcube : (g.val 1 1) ^ 3 = 1 := by
    calc
      _ = g.val.det := by
        rw [Matrix.det_fin_three, h10, h21, h22, h01, hdiag2]
        field_simp
        ring
      _ = 1 := g.property
  have hdiag1 : g.val 1 1 = 1 := by
    have hp : (g.val 1 1 - 1) * ((g.val 1 1) ^ 2 + g.val 1 1 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · linarith
    · nlinarith [sq_nonneg (g.val 1 1 + 1 / 2)]
  have hdiag0 : g.val 0 0 = a := by simpa [hdiag1] using h01
  have hdiag2' : g.val 2 2 = a⁻¹ := by simpa [hdiag1] using hdiag2
  have hupper : g.val 1 2 = g.val 0 1 / a := by apply (eq_div_iff ha).mpr; nlinarith [h02]
  apply Subtype.ext
  ext i j
  change g.val i j =
    (((unipotentOne (g.val 0 1)).val *
      (unipotentTwo (a * g.val 0 2 - (g.val 0 1) ^ 2 / 2)).val) * (diagonalFlow a ha).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentOne, unipotentTwo, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_succ,
      h10, h21, h22, hdiag0, hdiag1, hdiag2', hupper]
  all_goals field_simp

theorem principalNormalizer_factor (g : SL3)
    (hg : g ∈ Subgroup.normalizer (principalUnipotent : Set SL3)) :
    ∃ a : ℝ, ∃ ha : a ≠ 0, ∃ s b : ℝ,
      g = unipotentOne s * unipotentTwo b * diagonalFlow a ha := by
  obtain ⟨a, ha, hscaled⟩ := principalNormalizer_adjoint_base g hg
  exact ⟨a, ha, g.val 0 1, a * g.val 0 2 - (g.val 0 1) ^ 2 / 2,
    factor_of_adjoint_base_scaled g a ha hscaled⟩

end JSP400

#print axioms JSP400.principalNormalizer_factor
