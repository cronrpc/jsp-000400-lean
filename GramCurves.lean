import GramShear
import Mathlib.Analysis.Matrix.Normed

namespace JSP400

open Matrix Set
open scoped Matrix.Norms.Elementwise

/-- A non-fixed symmetric form has a coordinate growing linearly along its
actual unipotent orbit. The earlier vanishing coordinates remove all higher
degree terms, so no general polynomial-growth theorem is needed. -/
theorem gramShear_has_linear_coordinate (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q.IsSymm) (hnot : q ∉ gramFlag 2) :
    ∃ j : Fin 6, ∃ a b : ℝ, b ≠ 0 ∧
      ∀ t : ℝ, gramCoordinates (gramShear q t) j = a + t * b := by
  by_cases h00 : q 0 0 = 0
  · by_cases h01 : q 0 1 = 0
    · by_cases hsum : q 1 1 + q 0 2 = 0
      · have h12 : q 1 2 ≠ 0 := by
          intro hz
          apply hnot
          refine ⟨hq, ?_⟩
          intro j hj
          fin_cases j <;> norm_num at hj
          all_goals simp [gramCoordinates, hz, hsum, h01, h00]
        refine ⟨0, q 2 2, 2 * q 1 2, mul_ne_zero (by norm_num) h12, ?_⟩
        intro t
        rw [gramShear_coordinates q hq]
        simp [h00, h01, hsum]
        ring
      · refine ⟨2, q 1 2, q 1 1 + q 0 2, hsum, ?_⟩
        intro t
        rw [gramShear_coordinates q hq]
        simp [h00, h01]
    · refine ⟨3, q 1 1 + q 0 2, 3 * q 0 1, mul_ne_zero (by norm_num) h01, ?_⟩
      intro t
      rw [gramShear_coordinates q hq]
      simp [h00]
      ring
  · refine ⟨4, q 0 1, q 0 0, h00, ?_⟩
    intro t
    rw [gramShear_coordinates q hq]
    rfl

theorem gramCoordinate_abs_le (q : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 6) :
    |gramCoordinates q j| ≤ 3 * ‖q‖ := by
  have hb (i j : Fin 3) : |q i j| ≤ ‖q‖ := norm_entry_le_entrywise_sup_norm q
  have hn := norm_nonneg q
  fin_cases j
  · simpa [gramCoordinates] using (show |q 2 2| ≤ 3 * ‖q‖ by linarith [hb 2 2])
  · change |q 1 1 - 2 * q 0 2| ≤ _
    have ha := abs_sub (q 1 1) (2 * q 0 2)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
    linarith [hb 1 1, hb 0 2]
  · simpa [gramCoordinates] using (show |q 1 2| ≤ 3 * ‖q‖ by linarith [hb 1 2])
  · change |q 1 1 + q 0 2| ≤ _
    linarith [abs_add_le (q 1 1) (q 0 2), hb 1 1, hb 0 2]
  · simpa [gramCoordinates] using (show |q 0 1| ≤ 3 * ‖q‖ by linarith [hb 0 1])
  · simpa [gramCoordinates] using (show |q 0 0| ≤ 3 * ‖q‖ by linarith [hb 0 0])

theorem linear_ray_unbounded (a b : ℝ) (hb : b ≠ 0) (R : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ R < |a + t * b| := by
  let t := (|R| + |a| + 1) / |b|
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbt : |t * b| = |R| + |a| + 1 := by
    rw [abs_mul, abs_of_nonneg ht]
    exact div_mul_cancel₀ _ (abs_ne_zero.mpr hb)
  have htri : |t * b| ≤ |a + t * b| + |a| := by
    have he : t * b = (a + t * b) + (-a) := by ring
    calc
      |t * b| = |(a + t * b) + (-a)| := congrArg abs he
      _ ≤ |a + t * b| + |-a| := abs_add_le _ _
      _ = |a + t * b| + |a| := by rw [abs_neg]
  exact ⟨t, ht, by rw [hbt] at htri; linarith [le_abs_self R]⟩

/-- Every non-fixed symmetric form has a continuous unbounded positive-time
curve in its genuine V₁ pullback orbit, beginning at the given form. -/
theorem exists_unbounded_gram_curve (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q.IsSymm) (hnot : q ∉ gramFlag 2) :
    ∃ f : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      ContinuousOn f (Ici 0) ∧ f 0 = q ∧
      (∀ t, 0 ≤ t → f t ∈ range (gramShear q)) ∧
      ∀ R : ℝ, ∃ t : ℝ, 0 ≤ t ∧ R < ‖f t‖ := by
  obtain ⟨j, a, b, hb, hlinear⟩ := gramShear_has_linear_coordinate q hq hnot
  have hc : Continuous (gramShear q) := by
    have hp : Continuous (fun t : ℝ => (q, t)) := continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using continuous_gramShear.comp hp
  refine ⟨gramShear q, hc.continuousOn, gramShear_zero q,
    fun t _ => ⟨t, rfl⟩, ?_⟩
  intro R
  obtain ⟨t, ht, hlarge⟩ := linear_ray_unbounded a b hb (3 * R)
  refine ⟨t, ht, ?_⟩
  have hbound := gramCoordinate_abs_le (gramShear q t) j
  rw [hlinear] at hbound
  linarith

end JSP400

#print axioms JSP400.exists_unbounded_gram_curve
