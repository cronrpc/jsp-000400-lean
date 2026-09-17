import ShearFixedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed

namespace JSP400

open Set Matrix
open scoped Matrix.Norms.Elementwise

theorem exists_unbounded_shear_parameter_curve
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1) :
    ∃ p : ℝ → ℝ × ℝ, ContinuousOn p (Ici 0) ∧ p 0 = (0, 0) ∧
      (∀ u, 0 ≤ u → p u ∈ shearLevelSet x) ∧
      ∀ R : ℝ, ∃ u : ℝ, 0 ≤ u ∧ R < ‖p u‖ := by
  by_cases ha : x 2 1 = 0
  · refine ⟨fun u => (0, u), (continuous_const.prodMk continuous_id).continuousOn,
      rfl, ?_, ?_⟩
    · intro u hu
      simp [shearLevelSet, shearConjugate_entry01, hx, ha]
    · intro R
      refine ⟨|R| + 1, by positivity, ?_⟩
      have h := norm_snd_le ((0, |R| + 1) : ℝ × ℝ)
      simp only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ |R| + 1 by positivity)] at h
      linarith [le_abs_self R]
  · let σ : ℝ := if 0 ≤ x 2 0 * x 2 1 then -1 else 1
    have hσ : σ * x 2 0 * x 2 1 ≤ 0 := by
      dsimp [σ]
      split_ifs with h <;> nlinarith
    have hσabs : |σ| = 1 := by
      dsimp [σ]
      split_ifs <;> norm_num
    let p : ℝ → ℝ × ℝ := fun u =>
      (σ * u, ((σ * u) ^ 2 * x 1 0 - σ * u * (x 1 1 - x 0 0)) /
        (x 2 1 - σ * u * x 2 0))
    have hden : ∀ u ∈ Ici (0 : ℝ), x 2 1 - σ * u * x 2 0 ≠ 0 :=
      fun u hu => ray_denominator_ne_zero ha hσ hu
    refine ⟨p, ?_, by simp [p], ?_, ?_⟩
    · apply ContinuousOn.prodMk
      · exact (continuous_const.mul continuous_id).continuousOn
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · exact hden
    · intro u hu
      change shearConjugate x (σ * u)
        (((σ * u) ^ 2 * x 1 0 - σ * u * (x 1 1 - x 0 0)) /
          (x 2 1 - σ * u * x 2 0)) 0 1 = 1
      rw [shearConjugate_entry01, hx]
      field_simp [hden u hu]
      ring
    · intro R
      refine ⟨|R| + 1, by positivity, ?_⟩
      have h := norm_fst_le (p (|R| + 1))
      change |σ * (|R| + 1)| ≤ ‖p (|R| + 1)‖ at h
      rw [abs_mul, hσabs, one_mul,
        abs_of_nonneg (show 0 ≤ |R| + 1 by positivity)] at h
      linarith [le_abs_self R]

private theorem unbounded_after_continuous_leftInverse
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [ProperSpace F]
    (p : ℝ → E) (f : E → F) (r : F → E) (hr : Continuous r)
    (hleft : Function.LeftInverse r f)
    (hp : ∀ R : ℝ, ∃ u : ℝ, 0 ≤ u ∧ R < ‖p u‖) :
    ∀ R : ℝ, ∃ u : ℝ, 0 ≤ u ∧ R < ‖f (p u)‖ := by
  intro R
  by_contra h
  push Not at h
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : F) R).bddAbove_image
    (continuous_norm.comp hr).continuousOn
  obtain ⟨u, hu, hlarge⟩ := hp M
  have hmem : f (p u) ∈ Metric.closedBall (0 : F) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using h u hu
  have hb := hM ⟨f (p u), hmem, rfl⟩
  change ‖r (f (p u))‖ ≤ M at hb
  rw [hleft] at hb
  exact (not_le_of_gt hlarge) hb

theorem exists_unbounded_shear_curve_of_not_upper
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1)
    (hlower : x 2 0 ≠ 0 ∨ x 2 1 ≠ 0 ∨ x 1 0 ≠ 0) :
    ∃ f : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      ContinuousOn f (Ici 0) ∧ f 0 = x ∧
      (∀ u, 0 ≤ u → f u ∈ shearOrbitSlice x) ∧
      ∀ R : ℝ, ∃ u : ℝ, 0 ≤ u ∧ R < ‖f u‖ := by
  obtain ⟨p, hp, hp0, hlevel, hlarge⟩ := exists_unbounded_shear_parameter_curve x hx
  let F : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun q => shearConjugate x q.1 q.2
  obtain ⟨r, hr, hleft⟩ := shearConjugate_has_continuous_leftInverse x hlower
  refine ⟨F ∘ p, ?_, ?_, ?_, ?_⟩
  · exact (continuous_shearConjugate x).comp_continuousOn hp
  · simp only [Function.comp_apply, hp0]
    exact shearConjugate_zero x
  · intro u hu
    exact ⟨⟨p u, rfl⟩, hlevel u hu⟩
  · exact unbounded_after_continuous_leftInverse p F r hr hleft hlarge

theorem exists_unbounded_shear_curve
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1)
    (hnil : IsNilpotent x) (hnot : x ∉ shearLieAlgebra) :
    ∃ f : ℝ → Matrix (Fin 3) (Fin 3) ℝ,
      ContinuousOn f (Ici 0) ∧ f 0 = x ∧
      (∀ u, 0 ≤ u → f u ∈ shearOrbitSlice x) ∧
      ∀ R : ℝ, ∃ u : ℝ, 0 ≤ u ∧ R < ‖f u‖ := by
  by_cases h10 : x 1 0 = 0
  · by_cases h20 : x 2 0 = 0
    · by_cases h21 : x 2 1 = 0
      · have hupper : x.IsUpperTriangular := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all
        have hd := nilpotent_upperTriangular_diag_eq_zero x hupper hnil
        have h12 : x 1 2 ≠ 1 := by
          intro h
          apply hnot
          refine ⟨1, x 0 2, ?_⟩
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, hx, h, hd]
        let p : ℝ → ℝ × ℝ := fun u => (u / (x 1 2 - 1), 0)
        have hp : Continuous p := (continuous_id.div_const _).prodMk continuous_const
        let f : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun u =>
          shearConjugate x (u / (x 1 2 - 1)) 0
        have hf : Continuous f := by
          simpa only [Function.comp_def] using (continuous_shearConjugate x).comp hp
        refine ⟨f, hf.continuousOn, ?_, ?_, ?_⟩
        · simpa only [f, zero_div] using shearConjugate_zero x
        · intro u hu
          refine ⟨⟨p u, rfl⟩, ?_⟩
          change shearConjugate x (u / (x 1 2 - 1)) 0 0 1 = 1
          rw [shearConjugate_entry01]
          simp [hx, h10, h20, h21, hd]
        · intro R
          let u : ℝ := |R| + |x 0 2| + 1
          refine ⟨u, by dsimp [u]; positivity, ?_⟩
          have hbound : (f u) 0 2 ≤ ‖f u‖ :=
            (le_abs_self _).trans ((norm_le_pi_norm ((f u) 0) 2).trans
              (norm_le_pi_norm (f u) 0))
          change shearConjugate x (u / (x 1 2 - 1)) 0 0 2 ≤ ‖f u‖ at hbound
          rw [upper_shear_entry02 x (hd 0) (hd 1) h10, hx,
            div_mul_cancel₀ _ (sub_ne_zero.mpr h12)] at hbound
          dsimp [u] at hbound
          linarith [le_abs_self R, neg_abs_le (x 0 2)]
      · exact exists_unbounded_shear_curve_of_not_upper x hx (Or.inr (Or.inl h21))
    · exact exists_unbounded_shear_curve_of_not_upper x hx (Or.inl h20)
  · exact exists_unbounded_shear_curve_of_not_upper x hx (Or.inr (Or.inr h10))

end JSP400
