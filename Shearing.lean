import UnipotentGroups
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Compact

namespace JSP400

open Matrix Set

/-- Coordinates on the two-dimensional unipotent group `V` in Margulis §4. -/
noncomputable def shearElement (s t : ℝ) : SL3 :=
  ⟨!![1, s, t; 0, 1, s; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem shearElement_inv (s t : ℝ) :
    (shearElement s t)⁻¹ = shearElement (-s) (s ^ 2 - t) := by
  apply inv_eq_of_mul_eq_one_left
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((shearElement (-s) (s^2-t)).val * (shearElement s t).val) i j =
    (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  fin_cases i <;> fin_cases j <;>
    simp [shearElement, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

/-- The genuine matrix conjugation action, written in unipotent coordinates. -/
noncomputable def shearConjugate (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :=
  (shearElement s t).val * x * ((shearElement s t)⁻¹).val

/-- The specific polynomial used in the proof of Margulis Lemma 6(C). -/
theorem shearConjugate_entry01 (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearConjugate x s t 0 1 =
      x 0 1 + s * (x 1 1 - x 0 0) - s ^ 2 * x 1 0 +
        t * (x 2 1 - s * x 2 0) := by
  rw [shearConjugate, shearElement_inv]
  simp [shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

/-- The actual parameter fiber of the entry-`01` hyperplane. -/
def shearLevelSet (x : Matrix (Fin 3) (Fin 3) ℝ) : Set (ℝ × ℝ) :=
  {p | shearConjugate x p.1 p.2 0 1 = 1}

theorem ray_denominator_ne_zero {a b σ u : ℝ}
    (ha : a ≠ 0) (hσ : σ * b * a ≤ 0) (hu : 0 ≤ u) :
    a - σ * u * b ≠ 0 := by
  intro h
  have heq := congrArg (fun z : ℝ => z * a) h
  have hnonpos := mul_nonpos_of_nonpos_of_nonneg hσ hu
  nlinarith [sq_pos_of_ne_zero ha]

/-- The connected component through the identity parameter is noncompact.
This proves the polynomial-fiber step of Margulis Lemma 6(C), without
assuming any orbit-closure theorem. -/
theorem shearLevelSet_component_not_isCompact
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1) :
    ¬ IsCompact (connectedComponentIn (shearLevelSet x) (0, 0)) := by
  by_cases ha : x 2 1 = 0
  · let curve : ℝ → ℝ × ℝ := fun u => (0, u)
    have hcont : Continuous curve := continuous_const.prodMk continuous_id
    have hpre : IsPreconnected (Set.range curve) := isPreconnected_range hcont
    have hzero : (0, 0) ∈ Set.range curve := ⟨0, rfl⟩
    have hsub : Set.range curve ⊆ shearLevelSet x := by
      rintro _ ⟨u, rfl⟩
      simp [shearLevelSet, curve, shearConjugate_entry01, hx, ha]
    have hcomp := hpre.subset_connectedComponentIn hzero hsub
    intro hc
    obtain ⟨M, hM⟩ := hc.bddAbove_image continuous_snd.continuousOn
    have hb := hM ⟨curve (M + 1), hcomp ⟨M + 1, rfl⟩, rfl⟩
    change M + 1 ≤ M at hb
    linarith
  · let σ : ℝ := if 0 ≤ x 2 0 * x 2 1 then -1 else 1
    have hσ : σ * x 2 0 * x 2 1 ≤ 0 := by
      dsimp [σ]
      split_ifs with h
      · nlinarith
      · nlinarith
    have hσabs : |σ| = 1 := by
      dsimp [σ]
      split_ifs <;> norm_num
    let curve : ℝ → ℝ × ℝ := fun u =>
      (σ * u, ((σ * u) ^ 2 * x 1 0 - σ * u * (x 1 1 - x 0 0)) /
        (x 2 1 - σ * u * x 2 0))
    have hden : ∀ u ∈ Ici (0 : ℝ), x 2 1 - σ * u * x 2 0 ≠ 0 :=
      fun u hu => ray_denominator_ne_zero ha hσ hu
    have hcont : ContinuousOn curve (Ici 0) := by
      apply ContinuousOn.prodMk
      · exact (continuous_const.mul continuous_id).continuousOn
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · exact hden
    have hpre : IsPreconnected (curve '' Ici 0) := isPreconnected_Ici.image curve hcont
    have hzero : (0, 0) ∈ curve '' Ici 0 := by
      refine ⟨0, by simp, ?_⟩
      simp [curve]
    have hsub : curve '' Ici 0 ⊆ shearLevelSet x := by
      rintro _ ⟨u, hu, rfl⟩
      change shearConjugate x (σ * u)
        (((σ * u) ^ 2 * x 1 0 - σ * u * (x 1 1 - x 0 0)) /
          (x 2 1 - σ * u * x 2 0)) 0 1 = 1
      rw [shearConjugate_entry01, hx]
      field_simp [hden u hu]
      ring
    have hcomp := hpre.subset_connectedComponentIn hzero hsub
    intro hc
    obtain ⟨M, hM⟩ := hc.bddAbove_image continuous_fst.abs.continuousOn
    have hu : 0 ≤ |M| + 1 := by positivity
    have hb := hM ⟨curve (|M| + 1), hcomp ⟨|M| + 1, hu, rfl⟩, rfl⟩
    change |σ * (|M| + 1)| ≤ M at hb
    rw [abs_mul, hσabs, one_mul, abs_of_nonneg hu] at hb
    linarith [le_abs_self M]

end JSP400

#print axioms JSP400.shearConjugate_entry01
#print axioms JSP400.shearLevelSet_component_not_isCompact
