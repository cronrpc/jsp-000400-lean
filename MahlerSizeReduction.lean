import MahlerGram

namespace JSP400.Mahler

open Matrix
noncomputable section

theorem inner3_add_right (x y z : Vector3) : inner3 x (y+z) = inner3 x y+inner3 x z := by
  simp only [inner3, Pi.add_apply]
  ring

theorem columnShear_column_zero (A : SL3) (m n k : ℤ) :
    column (A * integerSLHom (columnShear m n k)).val 0 = column A.val 0 :=
  firstColumn_columnShear A m n k

theorem columnShear_column_one (A : SL3) (m n k : ℤ) :
    column (A * integerSLHom (columnShear m n k)).val 1 = (m:ℝ) • column A.val 0 + column A.val 1 := by
  ext i
  change (∑ j : Fin 3, A.val i j * ((columnShear m n k).val j 1 : ℝ)) = _
  simp [columnShear, column, Fin.sum_univ_succ, mul_comm]

theorem columnShear_column_two (A : SL3) (m n k : ℤ) :
    column (A * integerSLHom (columnShear m n k)).val 2 =
      (k:ℝ) • column A.val 0 + (n:ℝ) • column A.val 1 + column A.val 2 := by
  ext i
  change (∑ j : Fin 3, A.val i j * ((columnShear m n k).val j 2 : ℝ)) = _
  simp [columnShear, column, Fin.sum_univ_succ]
  ring

theorem columnShear_gramOne (A : SL3) (m n k : ℤ) :
    gramOne (A * integerSLHom (columnShear m n k)) = gramOne A :=
  columnShear_column_zero A m n k

theorem columnShear_mu21 (A : SL3) (m n k : ℤ) :
    mu21 (A * integerSLHom (columnShear m n k)) = mu21 A + m := by
  unfold mu21
  rw [columnShear_column_zero, columnShear_column_one, inner3_add_right,
    inner3_smul_right, inner3_self]
  have h := ne_of_gt (gramOne_energy_pos A)
  change energy (column A.val 0) ≠ 0 at h
  field_simp
  ring

theorem columnShear_gramTwo (A : SL3) (m n k : ℤ) :
    gramTwo (A * integerSLHom (columnShear m n k)) = gramTwo A := by
  rw [gramTwo, columnShear_column_one, columnShear_mu21, columnShear_gramOne, gramTwo]
  change (m:ℝ) • gramOne A + column A.val 1 - (mu21 A + m) • gramOne A = _
  rw [add_smul]
  abel

theorem columnShear_mu31 (A : SL3) (m n k : ℤ) :
    mu31 (A * integerSLHom (columnShear m n k)) = mu31 A + n * mu21 A + k := by
  unfold mu31
  rw [columnShear_gramOne, columnShear_column_two, inner3_add_right, inner3_add_right,
    inner3_smul_right, inner3_smul_right]
  change ((k:ℝ)*inner3 (gramOne A) (gramOne A)+(n:ℝ)*inner3 (gramOne A) (column A.val 1)+
      inner3 (gramOne A) (column A.val 2))/energy (gramOne A) = _
  rw [inner3_self]
  unfold mu21
  change ((k:ℝ)*energy (gramOne A)+(n:ℝ)*inner3 (gramOne A) (column A.val 1)+
      inner3 (gramOne A) (column A.val 2))/energy (gramOne A) =
    inner3 (gramOne A) (column A.val 2)/energy (gramOne A) +
      (n:ℝ)*(inner3 (gramOne A) (column A.val 1)/energy (gramOne A)) + k
  field_simp [ne_of_gt (gramOne_energy_pos A)]
  ring

theorem gram_two_column_one (A : SL3) : inner3 (gramTwo A) (column A.val 1) = energy (gramTwo A) := by
  rw [column_one_qr, inner3_add_right, inner3_smul_right,
    inner3_comm (gramTwo A) (gramOne A), gram_one_two_orthogonal, inner3_self]
  ring

theorem columnShear_mu32 (A : SL3) (m n k : ℤ) :
    mu32 (A * integerSLHom (columnShear m n k)) = mu32 A + n := by
  unfold mu32
  rw [columnShear_gramTwo, columnShear_column_two, inner3_add_right, inner3_add_right,
    inner3_smul_right, inner3_smul_right]
  change ((k:ℝ)*inner3 (gramTwo A) (gramOne A) + (n:ℝ)*inner3 (gramTwo A) (column A.val 1)+
      inner3 (gramTwo A) (column A.val 2))/energy (gramTwo A) = _
  rw [inner3_comm (gramTwo A) (gramOne A), gram_one_two_orthogonal, gram_two_column_one]
  field_simp [ne_of_gt (gramTwo_energy_pos A)]
  ring

theorem columnShear_gramThree (A : SL3) (m n k : ℤ) :
    gramThree (A * integerSLHom (columnShear m n k)) = gramThree A := by
  rw [gramThree, columnShear_column_two, columnShear_mu31, columnShear_mu32,
    columnShear_gramOne, columnShear_gramTwo, gramThree]
  rw [column_one_qr]
  change (k:ℝ) • gramOne A + (n:ℝ) • (mu21 A • gramOne A + gramTwo A) + column A.val 2 -
    (mu31 A + n * mu21 A + k) • gramOne A - (mu32 A + n) • gramTwo A = _
  simp only [add_smul, smul_add, mul_smul]
  abel

/-- A genuine integer shear simultaneously reduces all three Gram coefficients
and preserves both the lattice and its minimum-potential property. -/
theorem exists_size_reduction (A : SL3) :
    ∃ γ : IntegerSL3,
      |mu21 (A * integerSLHom γ)| ≤ 1/2 ∧
      |mu31 (A * integerSLHom γ)| ≤ 1/2 ∧
      |mu32 (A * integerSLHom γ)| ≤ 1/2 ∧
      (IsPotentialMinimum A → IsPotentialMinimum (A * integerSLHom γ)) := by
  let m : ℤ := -round (mu21 A)
  let n : ℤ := -round (mu32 A)
  let k : ℤ := -round (mu31 A + n * mu21 A)
  refine ⟨columnShear m n k, ?_, ?_, ?_, fun h => h.shear_minimum m n k⟩
  · rw [columnShear_mu21]
    simpa [m, sub_eq_add_neg] using abs_sub_round (mu21 A)
  · rw [columnShear_mu31]
    simpa [k, sub_eq_add_neg] using abs_sub_round (mu31 A + n * mu21 A)
  · rw [columnShear_mu32]
    simpa [n, sub_eq_add_neg] using abs_sub_round (mu32 A)

end
end JSP400.Mahler
