import MahlerPotential
import Mathlib.Algebra.Order.Round

namespace JSP400.Mahler

open Matrix Set

def IsPotentialMinimum (A : SL3) : Prop :=
  ∀ γ : IntegerSL3, potential A ≤ potential (A * integerSLHom γ)

theorem exists_reduced_potential (g : SL3) :
    ∃ γ : IntegerSL3, IsPotentialMinimum (g * integerSLHom γ) := by
  obtain ⟨γ, hγ⟩ := exists_minimum_potential g
  refine ⟨γ, fun η => ?_⟩
  simpa only [map_mul, mul_assoc] using hγ (γ * η)

/-- Integer column additions, with determinant one. -/
def columnShear (m n k : ℤ) : IntegerSL3 :=
  ⟨!![1, m, k; 0, 1, n; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem columnShear_inv (m n k : ℤ) :
    (columnShear m n k)⁻¹ = columnShear (-m) (-n) (m*n-k) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  change ((columnShear m n k).val * (columnShear (-m) (-n) (m*n-k)).val) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [columnShear, Matrix.mul_apply, Fin.sum_univ_succ]

theorem firstColumn_columnShear (A : SL3) (m n k : ℤ) :
    firstColumn (A * integerSLHom (columnShear m n k)).val = firstColumn A.val := by
  ext i
  change (∑ j : Fin 3, A.val i j * ((columnShear m n k).val j 0 : ℝ)) = _
  simp [columnShear, firstColumn, Fin.sum_univ_succ]

theorem lastInverseRow_columnShear (A : SL3) (m n k : ℤ) :
    lastInverseRow (A * integerSLHom (columnShear m n k)) = lastInverseRow A := by
  ext i
  change ((A * integerSLHom (columnShear m n k))⁻¹.val) 2 i = _
  rw [_root_.mul_inv_rev, ← map_inv, columnShear_inv]
  change (∑ j : Fin 3, ((columnShear (-m) (-n) (m*n-k)).val 2 j : ℝ) * A⁻¹.val j i) = _
  simp [columnShear, lastInverseRow, Fin.sum_univ_succ]

theorem potential_columnShear (A : SL3) (m n k : ℤ) :
    potential (A * integerSLHom (columnShear m n k)) = potential A := by
  unfold potential
  rw [firstColumn_columnShear, lastInverseRow_columnShear]

theorem IsPotentialMinimum.shear_minimum {A : SL3} (hA : IsPotentialMinimum A) (m n k : ℤ) :
    IsPotentialMinimum (A * integerSLHom (columnShear m n k)) := by
  intro η
  rw [potential_columnShear]
  simpa only [map_mul, mul_assoc] using hA (columnShear m n k * η)

def swapFirst : IntegerSL3 :=
  ⟨!![0, -1, 0; 1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def swapLast : IntegerSL3 :=
  ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem swapFirst_inv : swapFirst⁻¹ =
    (⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩ : IntegerSL3) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  change (swapFirst.val * (!![0, 1, 0; -1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ)) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [swapFirst, Matrix.mul_apply, Fin.sum_univ_succ]

theorem swapLast_inv : swapLast⁻¹ =
    (⟨!![1, 0, 0; 0, 0, 1; 0, -1, 0], by simp [Matrix.det_fin_three]⟩ : IntegerSL3) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  change (swapLast.val * (!![1, 0, 0; 0, 0, 1; 0, -1, 0] : Matrix (Fin 3) (Fin 3) ℤ)) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [swapLast, Matrix.mul_apply, Fin.sum_univ_succ]

def column (A : Matrix (Fin 3) (Fin 3) ℝ) (j : Fin 3) : Vector3 := fun i => A i j

theorem potential_swapFirst (A : SL3) :
    potential (A * integerSLHom swapFirst) = energy (column A.val 1) * energy (lastInverseRow A) := by
  have hc : firstColumn (A * integerSLHom swapFirst).val = column A.val 1 := by
    ext i
    change (∑ j : Fin 3, A.val i j * (swapFirst.val j 0 : ℝ)) = _
    simp [swapFirst, column, Fin.sum_univ_succ]
  have hr : lastInverseRow (A * integerSLHom swapFirst) = lastInverseRow A := by
    ext i
    change ((A * integerSLHom swapFirst)⁻¹.val) 2 i = _
    rw [_root_.mul_inv_rev, ← map_inv, swapFirst_inv]
    change (∑ j : Fin 3, ((!![0, 1, 0; -1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℝ) * A⁻¹.val j i) = _
    simp [lastInverseRow, Fin.sum_univ_succ]
  simp only [potential, hc, hr]

theorem energy_neg (v : Vector3) : energy (-v) = energy v := by
  simp [energy]

theorem potential_swapLast (A : SL3) :
    potential (A * integerSLHom swapLast) = energy (firstColumn A.val) * energy (fun i => A⁻¹.val 1 i) := by
  have hc : firstColumn (A * integerSLHom swapLast).val = firstColumn A.val := by
    ext i
    change (∑ j : Fin 3, A.val i j * (swapLast.val j 0 : ℝ)) = _
    simp [swapLast, firstColumn, Fin.sum_univ_succ]
  have hr : lastInverseRow (A * integerSLHom swapLast) = -(fun i => A⁻¹.val 1 i) := by
    ext i
    change ((A * integerSLHom swapLast)⁻¹.val) 2 i = _
    rw [_root_.mul_inv_rev, ← map_inv, swapLast_inv]
    change (∑ j : Fin 3, ((!![1, 0, 0; 0, 0, 1; 0, -1, 0] : Matrix (Fin 3) (Fin 3) ℤ) 2 j : ℝ) * A⁻¹.val j i) = _
    simp [Fin.sum_univ_succ]
  simp only [potential, hc, hr, energy_neg]

theorem column_ne_zero (A : SL3) (j : Fin 3) : column A.val j ≠ 0 := by
  intro hz
  have he := congrArg (fun B : SL3 => B.val j j) (inv_mul_cancel A)
  change (∑ i : Fin 3, A⁻¹.val j i * A.val i j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) j j at he
  simp only [Matrix.one_apply_eq] at he
  have hc : ∀ i, A.val i j = 0 := fun i => congrFun hz i
  simp only [hc, mul_zero, Finset.sum_const_zero] at he
  norm_num at he

theorem inverseRow_ne_zero (A : SL3) (j : Fin 3) : (fun i => A⁻¹.val j i) ≠ 0 := by
  intro hz
  have he := congrArg (fun B : SL3 => B.val j j) (inv_mul_cancel A)
  change (∑ i : Fin 3, A⁻¹.val j i * A.val i j) = (1 : Matrix (Fin 3) (Fin 3) ℝ) j j at he
  simp only [Matrix.one_apply_eq] at he
  have hc : ∀ i, A⁻¹.val j i = 0 := fun i => congrFun hz i
  simp only [hc, zero_mul, Finset.sum_const_zero] at he
  norm_num at he

theorem IsPotentialMinimum.first_length {A : SL3} (hA : IsPotentialMinimum A) :
    energy (column A.val 0) ≤ energy (column A.val 1) := by
  have h := hA swapFirst
  rw [potential_swapFirst] at h
  exact (mul_le_mul_iff_left₀ (energy_pos (inverseRow_ne_zero A 2))).mp h

theorem IsPotentialMinimum.second_area {A : SL3} (hA : IsPotentialMinimum A) :
    energy (lastInverseRow A) ≤ energy (fun i => A⁻¹.val 1 i) := by
  have h := hA swapLast
  rw [potential_swapLast] at h
  exact (mul_le_mul_iff_right₀ (energy_pos (column_ne_zero A 0))).mp h

end JSP400.Mahler

