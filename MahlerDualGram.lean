import MahlerGram

namespace JSP400.Mahler

open Matrix
noncomputable section

def cross3 (v w : Vector3) : Vector3 :=
  ![v 1*w 2-v 2*w 1, v 2*w 0-v 0*w 2, v 0*w 1-v 1*w 0]

theorem cross3_energy (v w : Vector3) :
    energy (cross3 v w) = energy v * energy w - (inner3 v w)^2 := by
  simp [cross3, energy, inner3]
  ring

theorem cross3_smul_add_self (x y : Vector3) (a : ℝ) :
    cross3 x (a • x + y) = cross3 x y := by
  ext i
  fin_cases i <;> simp [cross3, Pi.smul_apply, smul_eq_mul] <;> ring

theorem inverse_last_row_cross (A : SL3) :
    lastInverseRow A = cross3 (column A.val 0) (column A.val 1) := by
  ext i
  change A⁻¹.val 2 i = _
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
  fin_cases i <;> simp [cross3, column] <;> ring

theorem inverse_middle_row_cross (A : SL3) :
    (fun i => A⁻¹.val 1 i) = -cross3 (column A.val 0) (column A.val 2) := by
  ext i
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
  fin_cases i <;> simp [cross3, column] <;> ring

/-- The squared area of the first two genuine columns is the last dual row's
energy, and equals the product of the first two Gram lengths squared. -/
theorem lastInverseRow_energy_gram (A : SL3) :
    energy (lastInverseRow A) = energy (gramOne A)*energy (gramTwo A) := by
  rw [inverse_last_row_cross, column_one_qr]
  change energy (cross3 (gramOne A) (mu21 A • gramOne A + gramTwo A)) = _
  rw [cross3_smul_add_self, cross3_energy, gram_one_two_orthogonal]
  ring

/-- The adjacent exterior-volume comparison uses the actual second dual row,
including its Gram coefficient; no orthogonal-basis hypothesis is assumed. -/
theorem inverse_middle_row_energy_gram (A : SL3) :
    energy (fun i => A⁻¹.val 1 i) = energy (gramOne A)*
      ((mu32 A)^2*energy (gramTwo A)+energy (gramThree A)) := by
  rw [inverse_middle_row_cross, energy_neg, column_two_qr, add_assoc]
  change energy (cross3 (gramOne A)
    (mu31 A • gramOne A + (mu32 A • gramTwo A + gramThree A))) = _
  rw [cross3_smul_add_self, cross3_energy]
  have hinner : inner3 (gramOne A) (mu32 A • gramTwo A + gramThree A) = 0 := by
    have h12 := gram_one_two_orthogonal A
    have h13 := gram_one_three_orthogonal A
    simp only [inner3, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
    linear_combination mu32 A * h12 + h13
  rw [hinner, energy_add, energy_smul, inner3_comm, inner3_smul_right,
    inner3_comm (gramThree A) (gramTwo A), gram_two_three_orthogonal]
  ring

end
end JSP400.Mahler
