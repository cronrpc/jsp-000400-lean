import MahlerBoundedBasis

/-!
# The positive-parameter approximation theorem of Margulis

For every positive irrational real coefficient and every positive tolerance,
both inequalities in Erdős's original I.34 have positive integer witnesses.
The short-vector and basis-reduction inputs are proved in this project.
-/

namespace JSP400

theorem arbitrarily_short_vectors {α : ℝ} (hα : 0 < α) (hi : Irrational α) :
    HasArbitrarilyShortVectors α :=
  short_vectors_of_bounded_representatives Mahler.bounded_reduced_representatives hα hi

theorem integer_small_values {α : ℝ} (hα : 0 < α) (hi : Irrational α) :
    SmallValues α :=
  small_values_of_short_vectors hi (arbitrarily_short_vectors hα hi)

/-- Full positive-parameter target, with no deep theorem left as a hypothesis. -/
theorem positive_statement : PositiveStatement := by
  intro α hα hi ε hε
  exact approximation_of_small_values hα (integer_small_values hα hi) hε

/-- The equivalent first inequality from Erdős I.34. -/
theorem dual_statement : DualStatement :=
  dual_statement_iff.mpr positive_statement

/-- Explicit positive natural witnesses, with no bound on the irrational coefficient. -/
theorem erdos_496 {α ε : ℝ} (hα : 0 < α) (hi : Irrational α) (hε : 0 < ε) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      |(x : ℝ)^2 + (y : ℝ)^2 - α*(z : ℝ)^2| < ε :=
  positive_statement α hα hi ε hε

/-- Arbitrarily small errors also occur at arbitrarily large denominators. -/
theorem erdos_496_large_denominator {α ε : ℝ} (hα : 0 < α) (hi : Irrational α)
    (N : ℕ) (hε : 0 < ε) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ N < z ∧
      |(x : ℝ)^2 + (y : ℝ)^2 - α*(z : ℝ)^2| < ε :=
  approximation_large_denominator hα hi (positive_statement α hα hi) N hε

end JSP400
