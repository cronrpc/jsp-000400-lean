import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Quantitative bounds for a reduced three-dimensional unimodular basis. -/

namespace JSP400

theorem reduced_gram_lengths_sq_bound (ε a b c : ℝ) (hε : 0 < ε)
    (ha : 0 < a) (_hb : 0 < b) (hc : 0 < c) (hmin : ε ^ 2 ≤ a)
    (hab : 3 * a ≤ 4 * b) (hbc : 3 * b ≤ 4 * c) (hdet : a * b * c = 1) :
    a ≤ 4 / ε ^ 4 ∧ b ≤ 4 / ε ^ 4 ∧ c ≤ 4 / ε ^ 4 := by
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have he4 : 0 < ε ^ 4 := pow_pos hε 4
  have heb : 3 * ε ^ 2 ≤ 4 * b := by linarith
  have hprod : 3 * ε ^ 4 ≤ 4 * a * b := by
    calc
      3 * ε ^ 4 = ε ^ 2 * (3 * ε ^ 2) := by ring
      _ ≤ a * (4 * b) := mul_le_mul hmin heb (by positivity) ha.le
      _ = 4 * a * b := by ring
  have hcp : 3 * ε ^ 4 * c ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_right hprod hc.le
    nlinarith [hdet]
  have hbp : 9 * ε ^ 4 * b ≤ 16 := by
    have hh := mul_le_mul_of_nonneg_left hbc (le_of_lt he4)
    nlinarith
  have hap : 27 * ε ^ 4 * a ≤ 64 := by
    have hh := mul_le_mul_of_nonneg_left hab (le_of_lt he4)
    nlinarith
  refine ⟨(le_div_iff₀ he4).mpr ?_, (le_div_iff₀ he4).mpr ?_, (le_div_iff₀ he4).mpr ?_⟩
  all_goals nlinarith

theorem reduced_gram_lengths_bound (ε x y z : ℝ) (hε : 0 < ε)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hmin : ε ≤ x)
    (hxy : 3 * x ^ 2 ≤ 4 * y ^ 2) (hyz : 3 * y ^ 2 ≤ 4 * z ^ 2)
    (hdet : x ^ 2 * y ^ 2 * z ^ 2 = 1) :
    x ≤ 2 / ε ^ 2 ∧ y ≤ 2 / ε ^ 2 ∧ z ≤ 2 / ε ^ 2 := by
  have hs := reduced_gram_lengths_sq_bound ε (x ^ 2) (y ^ 2) (z ^ 2) hε
    (sq_pos_of_pos hx) (sq_pos_of_pos hy) (sq_pos_of_pos hz) (by nlinarith) hxy hyz hdet
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hsq : (2 / ε ^ 2) ^ 2 = 4 / ε ^ 4 := by ring
  have hr : 0 < 2 / ε ^ 2 := div_pos (by norm_num) he2
  constructor
  · nlinarith [hs.1]
  constructor
  · nlinarith [hs.2.1]
  · nlinarith [hs.2.2]

/-- The Gram length bound controls every original QR column with reduced
coefficients, in any real normed vector space. Orthogonality is used upstream
to establish the determinant and successive-length hypotheses. -/
theorem reduced_qr_columns_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 < ε) (q1 q2 q3 : E) (μ21 μ31 μ32 : ℝ)
    (h1 : 0 < ‖q1‖) (h2 : 0 < ‖q2‖) (h3 : 0 < ‖q3‖)
    (hmin : ε ≤ ‖q1‖)
    (h12 : 3 * ‖q1‖ ^ 2 ≤ 4 * ‖q2‖ ^ 2)
    (h23 : 3 * ‖q2‖ ^ 2 ≤ 4 * ‖q3‖ ^ 2)
    (hdet : ‖q1‖ ^ 2 * ‖q2‖ ^ 2 * ‖q3‖ ^ 2 = 1)
    (hμ21 : |μ21| ≤ 1 / 2) (hμ31 : |μ31| ≤ 1 / 2) (hμ32 : |μ32| ≤ 1 / 2) :
    ‖q1‖ ≤ 4 / ε ^ 2 ∧ ‖μ21 • q1 + q2‖ ≤ 4 / ε ^ 2 ∧
      ‖μ31 • q1 + μ32 • q2 + q3‖ ≤ 4 / ε ^ 2 := by
  obtain ⟨hq1, hq2, hq3⟩ := reduced_gram_lengths_bound ε ‖q1‖ ‖q2‖ ‖q3‖ hε
    h1 h2 h3 hmin h12 h23 hdet
  have he : 0 < 2 / ε ^ 2 := by positivity
  have htwo : 2 / ε ^ 2 = 2 * (1 / ε ^ 2) := by ring
  have hfour : 4 / ε ^ 2 = 2 * (2 / ε ^ 2) := by ring
  have hsmul {μ : ℝ} {q : E} (hμ : |μ| ≤ 1 / 2) (hq : ‖q‖ ≤ 2 / ε ^ 2) :
      ‖μ • q‖ ≤ 1 / ε ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |μ| * ‖q‖ ≤ (1 / 2) * (2 / ε ^ 2) := mul_le_mul hμ hq (norm_nonneg _) (by norm_num)
      _ = 1 / ε ^ 2 := by ring
  have hb2 := norm_add_le (μ21 • q1) q2
  have hb3 := norm_add_le (μ31 • q1 + μ32 • q2) q3
  have hsum := norm_add_le (μ31 • q1) (μ32 • q2)
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith [hsmul hμ21 hq1]
  · linarith [hsmul hμ31 hq1, hsmul hμ32 hq2]

end JSP400
