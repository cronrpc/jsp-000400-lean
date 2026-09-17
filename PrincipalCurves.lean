import PrincipalFlag
import GramCurves

namespace JSP400

open Matrix Set
open scoped Matrix.Norms.Elementwise

theorem principal_adjoint_has_linear_coordinate (x : Matrix (Fin 3) (Fin 3) ℝ)
    (htrace : x.trace = 0) (hnot : x ∉ shearLieAlgebra) :
    ∃ j : Fin 8, ∃ a b : ℝ, b ≠ 0 ∧ ∀ t : ℝ,
      shearCoordinates (shearConjugate x t (t ^ 2 / 2)) j = a + t * b := by
  by_cases h20 : x 2 0 = 0
  · by_cases h10 : x 1 0 = 0
    · by_cases h21 : x 2 1 = 0
      · by_cases hd1 : x 1 1 - x 0 0 = 0
        · by_cases hd2 : x 2 2 - 2 * x 1 1 + x 0 0 = 0
          · have hdiag : x 0 0 = 0 ∧ x 1 1 = 0 ∧ x 2 2 = 0 := by
              have ht := htrace
              simp [Matrix.trace, Fin.sum_univ_succ] at ht
              exact ⟨by linarith, by linarith, by linarith⟩
            have hb : x 1 2 - x 0 1 ≠ 0 := by
              intro hb
              apply hnot
              refine ⟨x 0 1, x 0 2, ?_⟩
              ext i j
              fin_cases i <;> fin_cases j <;> simp_all [sub_eq_zero]
            refine ⟨0, x 0 2, x 1 2 - x 0 1, hb, ?_⟩
            intro t
            rw [shearConjugate_coordinates]
            simp [h20, h10, h21, hdiag.1, hdiag.2.1, hdiag.2.2]
            ring
          · refine ⟨2, x 1 2 - x 0 1, x 2 2 - 2 * x 1 1 + x 0 0, hd2, ?_⟩
            intro t
            rw [shearConjugate_coordinates]
            simp [h20, h10, h21]
            ring
        · refine ⟨1, x 0 1, x 1 1 - x 0 0, hd1, ?_⟩
          intro t
          rw [shearConjugate_coordinates]
          simp [h20, h10, h21]
      · refine ⟨4, x 1 1, x 2 1, h21, ?_⟩
        intro t
        rw [shearConjugate_coordinates]
        simp [h20, h10]
    · refine ⟨3, x 0 0, x 1 0, h10, ?_⟩
      intro t
      rw [shearConjugate_coordinates]
      simp [h20]
  · refine ⟨5, x 1 0, x 2 0, h20, ?_⟩
    intro t
    rw [shearConjugate_coordinates]
    rfl

theorem shearCoordinate_abs_le (x : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 8) :
    |shearCoordinates x j| ≤ 2 * ‖x‖ := by
  have hb (i j : Fin 3) : |x i j| ≤ ‖x‖ := norm_entry_le_entrywise_sup_norm x
  have hn := norm_nonneg x
  fin_cases j
  all_goals simp [shearCoordinates]
  all_goals first
    | linarith [hb 0 2]
    | linarith [hb 0 1]
    | linarith [abs_sub (x 1 2) (x 0 1), hb 1 2, hb 0 1]
    | linarith [hb 0 0]
    | linarith [hb 1 1]
    | linarith [hb 1 0]
    | linarith [hb 2 1]
    | linarith [hb 2 0]

/-- A single positive-time V₁ orbit is already unbounded whenever its point
is outside the true fixed space of the principal representation. -/
theorem exists_unbounded_principal_curve (p : PrincipalSpace)
    (hp : p ∈ principalFlag 14) (hnot : p ∉ principalFlag 4) :
    ∃ f : ℝ → PrincipalSpace,
      ContinuousOn f (Ici 0) ∧ f 0 = p ∧
      (∀ t, 0 ≤ t → f t ∈ range (fun s => principalAction (unipotentOne s) p)) ∧
      ∀ R : ℝ, ∃ t : ℝ, 0 ≤ t ∧ R < ‖f t‖ := by
  let f : ℝ → PrincipalSpace := fun t => principalAction (unipotentOne t) p
  have hc : Continuous f := by
    have hu : Continuous unipotentOne := by unfold unipotentOne; fun_prop
    simpa only [f, Function.comp_def] using
      continuous_principalAction.comp (hu.prodMk continuous_const)
  refine ⟨f, hc.continuousOn, ?_, fun t _ => ⟨t, rfl⟩, ?_⟩
  · simp only [f, unipotentOne_zero, principalAction_one]
  · by_cases hx : p.1 ∈ shearLieAlgebra
    · have hqnot : p.2 ∉ gramFlag 2 := fun hq => hnot ((mem_principalFlag_four p).mpr ⟨hx, hq⟩)
      obtain ⟨j, a, b, hb, hlinear⟩ := gramShear_has_linear_coordinate p.2 hp.2.1 hqnot
      intro R
      obtain ⟨t, ht, hl⟩ := linear_ray_unbounded a (-b) (neg_ne_zero.mpr hb) (3 * R)
      have hbound := gramCoordinate_abs_le (gramShear p.2 (-t)) j
      rw [hlinear] at hbound
      have hnorm : ‖gramShear p.2 (-t)‖ ≤ ‖f t‖ := by
        simpa only [f, principalAction_unipotentOne] using norm_snd_le (f t)
      simp only [mul_neg, neg_mul] at hl hbound
      exact ⟨t, ht, by linarith⟩
    · obtain ⟨j, a, b, hb, hlinear⟩ := principal_adjoint_has_linear_coordinate p.1 hp.1 hx
      intro R
      obtain ⟨t, ht, hl⟩ := linear_ray_unbounded a b hb (2 * R)
      have hbound := shearCoordinate_abs_le (shearConjugate p.1 t (t ^ 2 / 2)) j
      rw [hlinear] at hbound
      have hnorm : ‖shearConjugate p.1 t (t ^ 2 / 2)‖ ≤ ‖f t‖ := by
        simpa only [f, principalAction_unipotentOne] using norm_fst_le (f t)
      exact ⟨t, ht, by linarith⟩

end JSP400

#print axioms JSP400.exists_unbounded_principal_curve
