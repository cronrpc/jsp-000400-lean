import FormStabilizer
import PositiveWitness
import Mathlib.Analysis.Normed.Group.Constructions

/-!
The elementary implication from arbitrarily short nonzero vectors in a
form-preserving lattice orbit to small nonzero integer values. Proving that
such short vectors exist is proved in `FinalTheorem` using the lattice dynamics.
-/

namespace JSP400

/-- A concrete norm bound for the original form; the norm is the usual sup norm
on the actual finite product `Fin 3 → ℝ`. -/
theorem ternaryForm_abs_le_norm (α : ℝ) (v : Vector3) :
    |ternaryForm α v| ≤ (2 + |α|) * ‖v‖ ^ 2 := by
  have hs (i : Fin 3) : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    have hp := mul_nonneg (sub_nonneg.mpr h)
      (add_nonneg (norm_nonneg v) (abs_nonneg (v i)))
    nlinarith [sq_abs (v i)]
  rw [ternaryForm_apply]
  dsimp [value]
  calc
    _ ≤ |v 0 ^ 2 + v 1 ^ 2| + |α * v 2 ^ 2| := abs_sub _ _
    _ = v 0 ^ 2 + v 1 ^ 2 + |α| * v 2 ^ 2 := by
      rw [abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)),
        abs_mul, abs_of_nonneg (sq_nonneg (v 2))]
    _ ≤ _ := by
      nlinarith [hs 0, hs 1, mul_le_mul_of_nonneg_left (hs 2) (abs_nonneg α)]

/-- The irrational diagonal form has no nonzero integral isotropic vector. -/
theorem ternaryForm_integer_ne_zero {α : ℝ} (hi : Irrational α)
    (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    ternaryForm α (fun i => (v i : ℝ)) ≠ 0 := by
  rw [ternaryForm_apply]
  intro h
  dsimp [value] at h
  by_cases hz : v 2 = 0
  · have hx : (v 0 : ℝ) = 0 := by
      simp only [hz, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h
      nlinarith [sq_nonneg (v 1 : ℝ)]
    have hy : (v 1 : ℝ) = 0 := by
      simp only [hz, Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h
      nlinarith [sq_nonneg (v 0 : ℝ)]
    apply hv
    funext i
    fin_cases i
    · exact_mod_cast hx
    · exact_mod_cast hy
    · exact hz
  · apply hi
    refine ⟨((v 0 : ℚ) ^ 2 + (v 1 : ℚ) ^ 2) / (v 2 : ℚ) ^ 2, ?_⟩
    push_cast
    apply (div_eq_iff (pow_ne_zero _ (by exact_mod_cast hz))).mpr
    linarith

/-- This is an orbit property to establish from Margulis's argument. -/
def HasArbitrarilyShortVectors (α : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (g : SL3) (v : Fin 3 → ℤ),
    g ∈ formStabilizer (ternaryForm α) ∧ v ≠ 0 ∧
      ‖g • (fun i => (v i : ℝ))‖ < η

/-- Quantitative continuity turns short orbit vectors into nonzero small values. -/
theorem small_values_of_short_vectors {α : ℝ} (hi : Irrational α)
    (hshort : HasArbitrarilyShortVectors α) : SmallValues α := by
  intro δ hδ
  have hc : 0 < 2 + |α| := by positivity
  obtain ⟨g, v, hg, hv, hn⟩ :=
    hshort (min 1 (δ / (2 + |α|))) (lt_min (by norm_num) (div_pos hδ hc))
  let w : Vector3 := g • (fun i => (v i : ℝ))
  have hn1 : ‖w‖ < 1 := hn.trans_le (min_le_left _ _)
  have hnδ : ‖w‖ * (2 + |α|) < δ :=
    (lt_div_iff₀ hc).mp (hn.trans_le (min_le_right _ _))
  have hsmall : |ternaryForm α w| < δ := by
    have hnsq : ‖w‖ ^ 2 ≤ ‖w‖ := by
      nlinarith [norm_nonneg w]
    have hmul := mul_le_mul_of_nonneg_left hnsq hc.le
    have hb := ternaryForm_abs_le_norm α w
    nlinarith
  have hsame : ternaryForm α w = ternaryForm α (fun i => (v i : ℝ)) := hg _
  rw [hsame, ternaryForm_apply] at hsmall
  refine ⟨v 0, v 1, v 2, ?_, ?_, hsmall⟩
  · by_contra h
    push Not at h
    rcases h with ⟨h0, h1, h2⟩
    apply hv
    funext i
    fin_cases i <;> assumption
  · exact abs_pos.mpr (by
      simpa only [ternaryForm_apply] using ternaryForm_integer_ne_zero hi v hv)

end JSP400
