import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# JSP-000400: the positive-parameter ternary approximation problem

The mathematical result is due to G. A. Margulis. Erdős's 1961 paper,
I.34 (pp.238–239), places this question in the context of indefinite
quadratic forms. The explicit positive parameter below records that context.
-/

namespace JSP400

/-- The diagonal ternary form in the second inequality of Erdős I.34. -/
def value (α x y z : ℝ) : ℝ := x ^ 2 + y ^ 2 - α * z ^ 2

/-- Approximation with all three coordinates positive integers. -/
def HasApproximation (α ε : ℝ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    |value α x y z| < ε

/-- The positive-parameter statement proved in `FinalTheorem`. -/
def PositiveStatement : Prop :=
  ∀ α : ℝ, 0 < α → Irrational α →
    ∀ ε : ℝ, 0 < ε → HasApproximation α ε

end JSP400
