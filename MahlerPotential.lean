import CompactRepresentatives
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Topology.Instances.Int
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace JSP400.Mahler

open Matrix Set
open scoped Matrix.Norms.Elementwise

/-- Euclidean squared length, without changing the norm on the lattice space. -/
def energy (v : Vector3) : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

theorem energy_nonneg (v : Vector3) : 0 ≤ energy v := by
  unfold energy
  positivity

theorem energy_pos {v : Vector3} (hv : v ≠ 0) : 0 < energy v := by
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  by_contra h
  have he : energy v = 0 := le_antisymm (not_lt.mp h) (energy_nonneg v)
  apply hv
  ext i
  fin_cases i
  · change v 0 = 0; unfold energy at he; nlinarith
  · change v 1 = 0; unfold energy at he; nlinarith
  · change v 2 = 0; unfold energy at he; nlinarith

theorem coordinate_sq_le_energy (v : Vector3) (i : Fin 3) : v i ^ 2 ≤ energy v := by
  fin_cases i
  · change v 0 ^ 2 ≤ energy v; unfold energy; nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  · change v 1 ^ 2 ≤ energy v; unfold energy; nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
  · change v 2 ^ 2 ≤ energy v; unfold energy; nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem norm_le_sqrt_energy (v : Vector3) : ‖v‖ ≤ Real.sqrt (energy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact Real.abs_le_sqrt (coordinate_sq_le_energy v i)

theorem integerVector_norm (v : IntegerVector3) : ‖integerVector v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    simpa [integerVector, Int.norm_eq_abs] using norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (integerVector v))).mpr
    intro i
    simpa [integerVector, Int.norm_eq_abs] using norm_le_pi_norm (integerVector v) i

/-- The lattice image of a bounded Euclidean ball has only finitely many
integer preimages. This is the discreteness needed for minimum reduction. -/
theorem finite_integer_energy_sublevel (g : SL3) (R : ℝ) :
    Set.Finite {v : IntegerVector3 | energy (g • integerVector v) ≤ R} := by
  have hb : {v : IntegerVector3 | energy (g • integerVector v) ≤ R} ⊆
      Metric.closedBall (0 : IntegerVector3) (3 * ‖g⁻¹.val‖ * Real.sqrt (max R 0)) := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, ← integerVector_norm]
    have hn := matrix_mulVec_norm_le g⁻¹.val (g • integerVector v)
    change ‖g⁻¹ • (g • integerVector v)‖ ≤ _ at hn
    rw [inv_smul_smul] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left
      ((norm_le_sqrt_energy _).trans (Real.sqrt_le_sqrt (hv.trans (le_max_left _ _))))
      (by positivity))
  exact (isCompact_closedBall (0 : IntegerVector3) _).finite_of_discrete.subset hb

/-- A fixed lattice has a positive Euclidean energy lower bound. -/
theorem integer_energy_lower_bound (g : SL3) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : IntegerVector3, v ≠ 0 →
      δ ≤ energy (g • integerVector v) := by
  obtain ⟨ε, he, hb⟩ := compact_representatives_lower_bound (isCompact_singleton (x := g))
  refine ⟨ε ^ 2, sq_pos_of_pos he, ?_⟩
  intro v hv
  have h := (hb g (Set.mem_singleton g) v hv).trans (norm_le_sqrt_energy _)
  have hs := Real.sq_sqrt (energy_nonneg (g • integerVector v))
  nlinarith [Real.sqrt_nonneg (energy (g • integerVector v))]

/-- The genuine dual determinant-one matrix. -/
def dualMatrix (g : SL3) : SL3 :=
  ⟨g⁻¹.val.transpose, by rw [Matrix.det_transpose]; exact g⁻¹.property⟩

def firstColumn (A : Matrix (Fin 3) (Fin 3) ℝ) : Vector3 := fun i => A i 0
def lastInverseRow (A : SL3) : Vector3 := fun i => A⁻¹.val 2 i

/-- In dimension three the second squared exterior volume is the squared
length of the final row of the inverse matrix. -/
def potential (A : SL3) : ℝ := energy (firstColumn A.val) * energy (lastInverseRow A)

def integerFlag (γ : IntegerSL3) : IntegerVector3 × IntegerVector3 :=
  (fun i => γ.val i 0, fun i => γ⁻¹.val 2 i)

theorem firstColumn_mul (g : SL3) (γ : IntegerSL3) :
    firstColumn (g * integerSLHom γ).val = g • integerVector (integerFlag γ).1 := by
  ext i
  rfl

theorem lastInverseRow_mul (g : SL3) (γ : IntegerSL3) :
    lastInverseRow (g * integerSLHom γ) = dualMatrix g • integerVector (integerFlag γ).2 := by
  ext i
  change ((g * integerSLHom γ)⁻¹.val) 2 i = _
  rw [_root_.mul_inv_rev, ← map_inv]
  change (∑ j : Fin 3, (γ⁻¹.val 2 j : ℝ) * g⁻¹.val j i) =
    ∑ j : Fin 3, g⁻¹.val j i * (γ⁻¹.val 2 j : ℝ)
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem integerFlag_nonzero (γ : IntegerSL3) :
    (integerFlag γ).1 ≠ 0 ∧ (integerFlag γ).2 ≠ 0 := by
  constructor
  · intro hz
    have he := congrArg (fun A : IntegerSL3 => A.val 0 0) (inv_mul_cancel γ)
    change (∑ j : Fin 3, γ⁻¹.val 0 j * γ.val j 0) = 1 at he
    have hc : ∀ j, γ.val j 0 = 0 := fun j => congrFun hz j
    simp only [hc, mul_zero, Finset.sum_const_zero] at he
    omega
  · intro hz
    have he := congrArg (fun A : IntegerSL3 => A.val 2 2) (inv_mul_cancel γ)
    change (∑ j : Fin 3, γ⁻¹.val 2 j * γ.val j 2) = 1 at he
    have hc : ∀ j, γ⁻¹.val 2 j = 0 := fun j => congrFun hz j
    simp only [hc, zero_mul, Finset.sum_const_zero] at he
    omega

def flagPotential (g : SL3) (p : IntegerVector3 × IntegerVector3) : ℝ :=
  energy (g • integerVector p.1) * energy (dualMatrix g • integerVector p.2)

theorem potential_mul_eq_flag (g : SL3) (γ : IntegerSL3) :
    potential (g * integerSLHom γ) = flagPotential g (integerFlag γ) := by
  unfold potential flagPotential
  rw [firstColumn_mul, lastInverseRow_mul]

/-- Actual minimization over every determinant-one integer change of basis.
No algorithm termination or pre-existing reduction hypothesis is assumed. -/
theorem exists_minimum_potential (g : SL3) :
    ∃ γ : IntegerSL3, ∀ η : IntegerSL3,
      potential (g * integerSLHom γ) ≤ potential (g * integerSLHom η) := by
  obtain ⟨a, ha, hga⟩ := integer_energy_lower_bound g
  obtain ⟨b, hb, hgb⟩ := integer_energy_lower_bound (dualMatrix g)
  let P := flagPotential g (integerFlag 1)
  let S : Set (IntegerVector3 × IntegerVector3) :=
    {p | p ∈ Set.range integerFlag ∧ flagPotential g p ≤ P}
  have hfin : S.Finite := by
    apply ((finite_integer_energy_sublevel g (P / b)).prod
      (finite_integer_energy_sublevel (dualMatrix g) (P / a))).subset
    intro p hp
    obtain ⟨γ, rfl⟩ := hp.1
    have h1 := hga _ (integerFlag_nonzero γ).1
    have h2 := hgb _ (integerFlag_nonzero γ).2
    have hP := hp.2
    change energy (g • integerVector (integerFlag γ).1) *
      energy (dualMatrix g • integerVector (integerFlag γ).2) ≤ P at hP
    constructor
    · apply (le_div_iff₀ hb).mpr
      exact (mul_le_mul_of_nonneg_left h2 (energy_nonneg _)).trans hP
    · apply (le_div_iff₀ ha).mpr
      have hm := mul_le_mul_of_nonneg_right h1 (energy_nonneg
        (dualMatrix g • integerVector (integerFlag γ).2))
      nlinarith
  have hne : S.Nonempty := ⟨integerFlag 1, ⟨⟨1, rfl⟩, le_rfl⟩⟩
  obtain ⟨p, hp, hmin⟩ := Set.exists_min_image S (flagPotential g) hfin hne
  obtain ⟨γ, rfl⟩ := hp.1
  refine ⟨γ, fun η => ?_⟩
  simp only [potential_mul_eq_flag]
  by_cases hη : flagPotential g (integerFlag η) ≤ P
  · exact hmin _ ⟨⟨η, rfl⟩, hη⟩
  · exact hp.2.trans (le_of_not_ge hη)

end JSP400.Mahler



