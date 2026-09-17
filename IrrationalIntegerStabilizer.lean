import CompactStabilizers

/-! Integer stabilizers of the irrational diagonal form are compact.
Irrationality separates its two integral coefficient forms directly. -/

namespace JSP400

open Matrix Set
open scoped Matrix.Norms.Elementwise

theorem integer_coefficients_of_irrational_relation {α : ℝ} (hα : Irrational α)
    (a b : ℤ) (h : (a : ℝ) = α * (b : ℝ)) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply (irrational_iff_ne_rational α).mp hα a b hb
    exact (eq_div_iff (by exact_mod_cast hb : (b : ℝ) ≠ 0)).mpr h.symm
  refine ⟨?_, hb⟩
  simp only [hb, Int.cast_zero, mul_zero] at h
  exact_mod_cast h

theorem integral_column_separation {α : ℝ} (hα : Irrational α)
    (g : IntegerSL3) (hg : integerSLHom g ∈ formStabilizer (ternaryForm α))
    (j : Fin 3) :
    g.val 0 j ^ 2 + g.val 1 j ^ 2 = (if j = 2 then 0 else 1) ∧
      g.val 2 j ^ 2 = (if j = 2 then 1 else 0) := by
  have he := hg (Pi.single j 1)
  change ternaryForm α ((integerSLHom g).val.mulVec (Pi.single j 1)) =
    ternaryForm α (Pi.single j 1) at he
  have hm : (integerSLHom g).val.mulVec (Pi.single j 1) =
      fun i => (g.val i j : ℝ) := by
    ext i
    rw [Matrix.mulVec_single_one]
    rfl
  rw [hm, ternaryForm_apply, ternaryForm_apply] at he
  fin_cases j
  all_goals norm_num [value, Pi.single_apply] at he
  · have hc := integer_coefficients_of_irrational_relation hα
      (g.val 0 0 ^ 2 + g.val 1 0 ^ 2 - 1) (g.val 2 0 ^ 2) (by push_cast; linarith)
    change g.val 0 0 ^ 2 + g.val 1 0 ^ 2 = 1 ∧ g.val 2 0 ^ 2 = 0
    constructor <;> nlinarith [hc.1, hc.2]
  · have hc := integer_coefficients_of_irrational_relation hα
      (g.val 0 1 ^ 2 + g.val 1 1 ^ 2 - 1) (g.val 2 1 ^ 2) (by push_cast; linarith)
    change g.val 0 1 ^ 2 + g.val 1 1 ^ 2 = 1 ∧ g.val 2 1 ^ 2 = 0
    constructor <;> nlinarith [hc.1, hc.2]
  · have hc := integer_coefficients_of_irrational_relation hα
      (g.val 0 2 ^ 2 + g.val 1 2 ^ 2) (g.val 2 2 ^ 2 - 1) (by push_cast; linarith)
    change g.val 0 2 ^ 2 + g.val 1 2 ^ 2 = 0 ∧ g.val 2 2 ^ 2 = 1
    constructor <;> nlinarith [hc.1, hc.2]

theorem integral_stabilizer_entry_bound {α : ℝ} (hα : Irrational α)
    (g : IntegerSL3) (hg : integerSLHom g ∈ formStabilizer (ternaryForm α))
    (i j : Fin 3) : |g.val i j| ≤ 1 := by
  have hc := integral_column_separation hα g hg j
  have hnorm : g.val 0 j ^ 2 + g.val 1 j ^ 2 + g.val 2 j ^ 2 = 1 := by
    rw [hc.1, hc.2]
    split_ifs <;> norm_num
  have hb : g.val i j ^ 2 ≤ 1 := by
    fin_cases i <;> dsimp at * <;> nlinarith [sq_nonneg (g.val 0 j), sq_nonneg (g.val 1 j),
      sq_nonneg (g.val 2 j)]
  rw [abs_le]
  constructor <;> nlinarith

theorem irrational_integer_stabilizer_matrix_norm_le {α : ℝ} (hα : Irrational α)
    (g : SL3) (hΓ : g ∈ integerGamma) (hg : g ∈ formStabilizer (ternaryForm α)) :
    ‖g.val‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := hΓ
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro j
  change ‖(a.val i j : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs]
  exact_mod_cast integral_stabilizer_entry_bound hα a hg i j

theorem continuous_ternaryForm (α : ℝ) : Continuous (ternaryForm α : Vector3 → ℝ) := by
  have he : (ternaryForm α : Vector3 → ℝ) = fun v => value α (v 0) (v 1) (v 2) :=
    funext (ternaryForm_apply α)
  rw [he]
  exact (((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).sub
    (continuous_const.mul ((continuous_apply 2).pow 2))

theorem ternaryStabilizer_isClosed (α : ℝ) :
    IsClosed (formStabilizer (ternaryForm α) : Set SL3) := by
  have he : (formStabilizer (ternaryForm α) : Set SL3) =
      ⋂ v : Vector3, {g : SL3 | ternaryForm α (g.val.mulVec v) = ternaryForm α v} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  apply isClosed_iInter
  intro v
  have hc : Continuous (fun g : SL3 => g.val.mulVec v) := by
    fun_prop
  exact isClosed_eq ((continuous_ternaryForm α).comp hc) continuous_const

/-- Compactness of the actual integer stabilizer follows from the explicit
entry bound and closedness, without a density theorem for general lattices. -/
theorem irrational_integer_stabilizer_isCompact {α : ℝ} (hα : Irrational α) :
    IsCompact ((formStabilizer (ternaryForm α) ⊓ integerGamma : Subgroup SL3) : Set SL3) := by
  have hclosed : IsClosed ((formStabilizer (ternaryForm α) ⊓ integerGamma : Subgroup SL3) : Set SL3) :=
    (ternaryStabilizer_isClosed α).inter integerGamma_isClosed
  have : ProperSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (ProperSpace (Fin 3 → Fin 3 → ℝ))
  have hc := Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
    (isCompact_closedBall (0 : Matrix (Fin 3) (Fin 3) ℝ) 1)
  apply hc.of_isClosed_subset hclosed
  intro g hg
  change g.val ∈ Metric.closedBall 0 1
  rw [Metric.mem_closedBall, dist_zero_right]
  exact irrational_integer_stabilizer_matrix_norm_le hα g hg.2 hg.1

end JSP400
