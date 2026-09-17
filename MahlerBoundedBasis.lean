import MahlerSizeReduction
import MahlerDualGram
import ReducedBasisBounds
import MahlerCompactness

namespace JSP400.Mahler

open Matrix Set
open scoped Matrix.Norms.Elementwise

theorem half_bound_sq {x : ℝ} (hx : |x| ≤ 1/2) : x^2 ≤ 1/4 := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  nlinarith

theorem reduced_first_gram_inequality {A : SL3} (hA : IsPotentialMinimum A)
    (hμ : |mu21 A| ≤ 1/2) : 3*energy (gramOne A) ≤ 4*energy (gramTwo A) := by
  have h := hA.first_length
  rw [energy_column_one] at h
  change energy (gramOne A) ≤ _ at h
  have hs := half_bound_sq hμ
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (le_of_lt (gramOne_energy_pos A))]

theorem reduced_second_gram_inequality {A : SL3} (hA : IsPotentialMinimum A)
    (hμ : |mu32 A| ≤ 1/2) : 3*energy (gramTwo A) ≤ 4*energy (gramThree A) := by
  have h := hA.second_area
  rw [lastInverseRow_energy_gram, inverse_middle_row_energy_gram] at h
  have hh := (mul_le_mul_iff_right₀ (gramOne_energy_pos A)).mp h
  have hs := half_bound_sq hμ
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (le_of_lt (gramTwo_energy_pos A))]

theorem energy_column_two (A : SL3) :
    energy (column A.val 2) = (mu31 A)^2*energy (gramOne A) +
      (mu32 A)^2*energy (gramTwo A) + energy (gramThree A) := by
  rw [column_two_qr, energy_add, energy_add, energy_smul, energy_smul]
  have he : inner3 (mu31 A • gramOne A) (mu32 A • gramTwo A) = 0 := by
    rw [inner3_smul_right, inner3_comm, inner3_smul_right,
      inner3_comm (gramTwo A) (gramOne A), gram_one_two_orthogonal]
    ring
  have hf : inner3 (mu31 A • gramOne A + mu32 A • gramTwo A) (gramThree A) = 0 := by
    rw [inner3_comm, inner3_add_right, inner3_smul_right, inner3_smul_right,
      inner3_comm (gramThree A) (gramOne A), gram_one_three_orthogonal,
      inner3_comm (gramThree A) (gramTwo A), gram_two_three_orthogonal]
    ring
  rw [he, hf]
  ring

theorem norm_sq_le_energy (v : Vector3) : ‖v‖^2 ≤ energy v := by
  have hn := norm_le_sqrt_energy v
  nlinarith [norm_nonneg v, Real.sqrt_nonneg (energy v), Real.sq_sqrt (energy_nonneg v)]

theorem matrix_norm_bound_of_reduced (A : SL3) (ε : ℝ) (hε : 0 < ε)
    (hA : IsPotentialMinimum A) (h21 : |mu21 A| ≤ 1/2)
    (h31 : |mu31 A| ≤ 1/2) (h32 : |mu32 A| ≤ 1/2)
    (hlow : ε ≤ ‖gramOne A‖) : ‖A.val‖ ≤ 4/ε^2 := by
  have heps : ε^2 ≤ energy (gramOne A) := by
    have hn := norm_sq_le_energy (gramOne A)
    nlinarith [norm_nonneg (gramOne A)]
  obtain ⟨ha, hb, hc⟩ := reduced_gram_lengths_sq_bound ε
    (energy (gramOne A)) (energy (gramTwo A)) (energy (gramThree A)) hε
    (gramOne_energy_pos A) (gramTwo_energy_pos A) (gramThree_energy_pos A) heps
    (reduced_first_gram_inequality hA h21) (reduced_second_gram_inequality hA h32)
    (gram_energy_product A)
  have hh21 := half_bound_sq h21
  have hh31 := half_bound_sq h31
  have hh32 := half_bound_sq h32
  have hecol : ∀ j : Fin 3, energy (column A.val j) ≤ 16/ε^4 := by
    intro j
    have hpos : 0 < ε^4 := pow_pos hε _
    have h16 : 16/ε^4 = 4*(4/ε^4) := by ring
    fin_cases j
    · change energy (gramOne A) ≤ _
      exact ha.trans (by gcongr; norm_num)
    · change energy (column A.val 1) ≤ _
      rw [energy_column_one]
      have hp := mul_le_mul_of_nonneg_right hh21 (energy_nonneg (gramOne A))
      have ht : 0 ≤ 4/ε^4 := by positivity
      rw [h16]
      nlinarith
    · change energy (column A.val 2) ≤ _
      rw [energy_column_two]
      have hp := mul_le_mul_of_nonneg_right hh31 (energy_nonneg (gramOne A))
      have hq := mul_le_mul_of_nonneg_right hh32 (energy_nonneg (gramTwo A))
      have ht : 0 ≤ 4/ε^4 := by positivity
      rw [h16]
      nlinarith
  have hcol : ∀ j : Fin 3, ‖column A.val j‖ ≤ 4/ε^2 := by
    intro j
    have hn := (norm_sq_le_energy _).trans (hecol j)
    have he : (4/ε^2)^2 = 16/ε^4 := by field_simp; ring
    have hp : 0 < 4/ε^2 := by positivity
    nlinarith [norm_nonneg (column A.val j)]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  exact (norm_le_pi_norm (column A.val j) i).trans (hcol j)

/-- Mahler's bounded-basis conclusion, with every reduction step discharged
by an actual determinant-one integer change of basis. -/
theorem bounded_reduced_representatives : BoundedReducedRepresentatives := by
  intro ε hε
  refine ⟨4/ε^2, ?_⟩
  intro g hlow
  obtain ⟨γ, hγ⟩ := exists_reduced_potential g
  obtain ⟨η, h21, h31, h32, hη⟩ := exists_size_reduction (g * integerSLHom γ)
  let A := (g * integerSLHom γ) * integerSLHom η
  have hfirst : gramOne A ∈ latticePoints g := by
    have hm : gramOne A ∈ latticePoints A := by
      refine ⟨Pi.single 0 1, ?_⟩
      ext i
      change (∑ j : Fin 3, A.val i j * (((Pi.single (0:Fin 3) (1:ℤ) : IntegerVector3) j : ℤ):ℝ)) = A.val i 0
      simp [Pi.single_apply]
    have he : latticePoints A = latticePoints g := by
      dsimp [A]
      rw [latticePoints_mul_integer, latticePoints_mul_integer]
    exact he ▸ hm
  obtain ⟨v, hv⟩ := hfirst
  change g • integerVector v = gramOne A at hv
  have hvn : v ≠ 0 := by
    intro h
    have hz : integerVector v = 0 := (integerVector_eq_zero_iff v).mpr h
    have hg0 : gramOne A = 0 := by
      rw [hz] at hv
      exact hv.symm.trans (Matrix.mulVec_zero g.val)
    exact (column_ne_zero A 0) hg0
  have hl : ε ≤ ‖gramOne A‖ := by simpa only [hv] using hlow v hvn
  refine ⟨γ*η, ?_⟩
  have hb := matrix_norm_bound_of_reduced A ε hε (hη hγ) h21 h31 h32 hl
  simpa only [A, map_mul, mul_assoc] using hb

end JSP400.Mahler

#print axioms JSP400.Mahler.bounded_reduced_representatives
