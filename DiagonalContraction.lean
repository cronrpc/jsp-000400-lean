import CompactStabilizers
import UnipotentGroups
import Mathlib.Analysis.SpecificLimits.Basic

namespace JSP400

open Filter
open scoped Topology

/-- The full upper unitriangular group, with its three actual coordinates. -/
noncomputable def upperUnipotent (a b c : ℝ) : SL3 :=
  ⟨!![1, a, b; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem diagonalFlow_upper (t : ℝ) (ht : t ≠ 0) (a b c : ℝ) :
    diagonalFlow t ht * upperUnipotent a b c =
      upperUnipotent (t * a) (t ^ 2 * b) (t * c) * diagonalFlow t ht := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((diagonalFlow t ht).val * (upperUnipotent a b c).val) i j =
    ((upperUnipotent (t*a) (t^2*b) (t*c)).val * (diagonalFlow t ht).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals field_simp

theorem upperUnipotent_zero : upperUnipotent 0 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent]

theorem upper_scaled_continuous (a b c : ℝ) :
    Continuous (fun r : ℝ => upperUnipotent (r * a) (r ^ 2 * b) (r * c)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/-- A concrete contracting sequence inside the positive diagonal group. -/
noncomputable def contractingDiagonal (n : ℕ) : SL3 :=
  diagonalFlow ((1 / 2 : ℝ) ^ n) (pow_ne_zero _ (by norm_num))

theorem contractingDiagonal_upper_tendsto_one (a b c : ℝ) :
    Tendsto (fun n => contractingDiagonal n * upperUnipotent a b c *
      (contractingDiagonal n)⁻¹) atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc := ((upper_scaled_continuous a b c).tendsto 0).comp hp
  have heq (n : ℕ) : contractingDiagonal n * upperUnipotent a b c *
      (contractingDiagonal n)⁻¹ =
        upperUnipotent (((1 / 2 : ℝ)^n) * a) (((1 / 2 : ℝ)^n)^2 * b)
          (((1 / 2 : ℝ)^n) * c) := by
    unfold contractingDiagonal
    rw [diagonalFlow_upper, mul_assoc, mul_inv_cancel, mul_one]
  simp only [zero_mul, zero_pow (by decide : 2 ≠ 0), upperUnipotent_zero] at hc
  simpa only [heq, Function.comp_def] using hc

/-- The actual orbit of a lattice under all positive diagonal elements. -/
def diagonalOrbit (y : LatticeSpace) : Set LatticeSpace :=
  Set.range (fun t : {r : ℝ // 0 < r} => diagonalFlow t.val (ne_of_gt t.property) • y)

/-- The stabilizer conclusion of Margulis Lemma 9: relative compactness of
the diagonal orbit excludes every nonidentity upper unitriangular stabilizer. -/
theorem upper_stabilizer_trivial_of_compact_diagonal_orbit
    (y : LatticeSpace) (hc : IsCompact (closure (diagonalOrbit y)))
    (a b c : ℝ) (hstab : upperUnipotent a b c • y = y) :
    upperUnipotent a b c = 1 := by
  by_contra hne
  have hescape := conjugating_stabilizer_escapes_compacts y (upperUnipotent a b c)
    hstab hne contractingDiagonal (contractingDiagonal_upper_tendsto_one a b c)
    (closure (diagonalOrbit y)) hc
  obtain ⟨n, hn⟩ := hescape.exists
  apply hn
  apply subset_closure
  refine ⟨⟨(1 / 2 : ℝ)^n, pow_pos (by norm_num) _⟩, ?_⟩
  rfl

end JSP400
