import MahlerBasisChanges

namespace JSP400.Mahler

open Matrix
noncomputable section

def inner3 (v w : Vector3) : ℝ := v 0*w 0 + v 1*w 1 + v 2*w 2

def volume3 (x y z : Vector3) : ℝ :=
  x 0*(y 1*z 2-y 2*z 1) - y 0*(x 1*z 2-x 2*z 1) + z 0*(x 1*y 2-x 2*y 1)

theorem inner3_self (v : Vector3) : inner3 v v = energy v := by
  unfold inner3 energy
  ring

theorem inner3_comm (v w : Vector3) : inner3 v w = inner3 w v := by
  unfold inner3
  ring

theorem inner3_sub_right (v w z : Vector3) : inner3 v (w-z) = inner3 v w-inner3 v z := by
  simp only [inner3, Pi.sub_apply]
  ring

theorem inner3_smul_right (v w : Vector3) (a : ℝ) : inner3 v (a • w) = a*inner3 v w := by
  simp only [inner3, Pi.smul_apply, smul_eq_mul]
  ring

theorem energy_add (v w : Vector3) : energy (v+w) = energy v+2*inner3 v w+energy w := by
  simp only [energy, inner3, Pi.add_apply]
  ring

theorem energy_smul (a : ℝ) (v : Vector3) : energy (a • v) = a^2*energy v := by
  simp only [energy, Pi.smul_apply, smul_eq_mul]
  ring

theorem energy_zero : energy (0 : Vector3) = 0 := by simp [energy]

theorem volume3_qr (x y z : Vector3) (a b c : ℝ) :
    volume3 x (y-a•x) (z-b•x-c•(y-a•x)) = volume3 x y z := by
  simp only [volume3, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem volume3_second_reduce (x y z : Vector3) (a : ℝ) :
    volume3 x (y-a•x) z = volume3 x y z := by
  simpa using volume3_qr x y z a 0 0

theorem volume3_columns (A : SL3) : volume3 (column A.val 0) (column A.val 1) (column A.val 2) = 1 := by
  have hd := A.property
  rw [Matrix.det_fin_three] at hd
  unfold volume3 column
  nlinarith only [hd]

theorem volume3_gram (x y z : Vector3) :
    (volume3 x y z)^2 = energy x*energy y*energy z +
      2*inner3 x y*inner3 x z*inner3 y z - energy x*(inner3 y z)^2 -
      energy y*(inner3 x z)^2 - energy z*(inner3 x y)^2 := by
  unfold volume3 energy inner3
  ring

def mu21 (A : SL3) : ℝ := inner3 (column A.val 0) (column A.val 1) / energy (column A.val 0)
def gramOne (A : SL3) : Vector3 := column A.val 0
def gramTwo (A : SL3) : Vector3 := column A.val 1 - mu21 A • gramOne A
def mu31 (A : SL3) : ℝ := inner3 (gramOne A) (column A.val 2) / energy (gramOne A)
def mu32 (A : SL3) : ℝ := inner3 (gramTwo A) (column A.val 2) / energy (gramTwo A)
def gramThree (A : SL3) : Vector3 := column A.val 2 - mu31 A • gramOne A - mu32 A • gramTwo A

theorem gramOne_energy_pos (A : SL3) : 0 < energy (gramOne A) := energy_pos (column_ne_zero A 0)

theorem gram_volume (A : SL3) : volume3 (gramOne A) (gramTwo A) (gramThree A) = 1 := by
  unfold gramThree gramTwo gramOne
  rw [volume3_qr, volume3_columns]

theorem gramTwo_energy_pos (A : SL3) : 0 < energy (gramTwo A) := by
  apply energy_pos
  intro h
  have hv := gram_volume A
  rw [h] at hv
  simp [volume3] at hv

theorem gramThree_energy_pos (A : SL3) : 0 < energy (gramThree A) := by
  apply energy_pos
  intro h
  have hv := gram_volume A
  rw [h] at hv
  simp [volume3] at hv

theorem gram_one_two_orthogonal (A : SL3) : inner3 (gramOne A) (gramTwo A) = 0 := by
  rw [gramTwo, inner3_sub_right, inner3_smul_right, inner3_self]
  change inner3 (gramOne A) (column A.val 1) -
    (inner3 (gramOne A) (column A.val 1) / energy (gramOne A))*energy (gramOne A) = 0
  field_simp [ne_of_gt (gramOne_energy_pos A)]
  ring

theorem gram_one_three_orthogonal (A : SL3) : inner3 (gramOne A) (gramThree A) = 0 := by
  rw [gramThree, inner3_sub_right, inner3_sub_right,
    inner3_smul_right, inner3_smul_right, gram_one_two_orthogonal, inner3_self]
  unfold mu31
  field_simp [ne_of_gt (gramOne_energy_pos A)]
  ring

theorem gram_two_three_orthogonal (A : SL3) : inner3 (gramTwo A) (gramThree A) = 0 := by
  rw [gramThree, inner3_sub_right, inner3_sub_right,
    inner3_smul_right, inner3_smul_right, inner3_self,
    inner3_comm (gramTwo A) (gramOne A), gram_one_two_orthogonal]
  unfold mu32
  field_simp [ne_of_gt (gramTwo_energy_pos A)]
  ring

theorem gram_energy_product (A : SL3) :
    energy (gramOne A) * energy (gramTwo A) * energy (gramThree A) = 1 := by
  have h := volume3_gram (gramOne A) (gramTwo A) (gramThree A)
  rw [gram_volume, gram_one_two_orthogonal, gram_one_three_orthogonal,
    gram_two_three_orthogonal] at h
  nlinarith

theorem column_one_qr (A : SL3) : column A.val 1 = mu21 A • gramOne A + gramTwo A := by
  unfold gramTwo
  abel

theorem column_two_qr (A : SL3) :
    column A.val 2 = mu31 A • gramOne A + mu32 A • gramTwo A + gramThree A := by
  unfold gramThree
  abel

theorem energy_column_one (A : SL3) :
    energy (column A.val 1) = (mu21 A)^2*energy (gramOne A)+energy (gramTwo A) := by
  rw [column_one_qr, energy_add, energy_smul, inner3_comm, inner3_smul_right,
    inner3_comm (gramTwo A) (gramOne A), gram_one_two_orthogonal]
  ring

end
end JSP400.Mahler
