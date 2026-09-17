import GramShear
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Explicit indefinite triangular factorization near diag(2,-1,-2). -/

namespace JSP400.GramSection

open Matrix Set
noncomputable section

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def diagonalForm : Mat := !![2, 0, 0; 0, -1, 0; 0, 0, -2]
def firstPivot (q : Mat) : ℝ := q 0 0 / 2
def firstRoot (q : Mat) : ℝ := Real.sqrt (firstPivot q)
def upper01 (q : Mat) : ℝ := q 0 1 / (2 * firstRoot q)
def upper02 (q : Mat) : ℝ := q 0 2 / (2 * firstRoot q)
def secondPivot (q : Mat) : ℝ := 2 * upper01 q ^ 2 - q 1 1
def secondRoot (q : Mat) : ℝ := Real.sqrt (secondPivot q)
def upper12 (q : Mat) : ℝ := (2 * upper01 q * upper02 q - q 1 2) / secondRoot q
def thirdPivot (q : Mat) : ℝ := (2 * upper02 q ^ 2 - upper12 q ^ 2 - q 2 2) / 2
def thirdRoot (q : Mat) : ℝ := Real.sqrt (thirdPivot q)

def positivePivots (q : Mat) : Prop :=
  0 < firstPivot q ∧ 0 < secondPivot q ∧ 0 < thirdPivot q

def triangularFactor (q : Mat) : Mat :=
  !![firstRoot q, upper01 q, upper02 q;
    0, secondRoot q, upper12 q; 0, 0, thirdRoot q]

theorem triangularFactor_congruence (q : Mat) (hq : q.IsSymm) (hp : positivePivots q) :
    (triangularFactor q).transpose * diagonalForm * triangularFactor q = q := by
  have hr : firstRoot q ^ 2 = q 0 0 / 2 := Real.sq_sqrt hp.1.le
  have hs : secondRoot q ^ 2 = 2 * upper01 q ^ 2 - q 1 1 := Real.sq_sqrt hp.2.1.le
  have ht : thirdRoot q ^ 2 =
      (2 * upper02 q ^ 2 - upper12 q ^ 2 - q 2 2) / 2 := Real.sq_sqrt hp.2.2.le
  have hrne : firstRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp.1)
  have hsne : secondRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp.2.1)
  have hrb : 2 * firstRoot q * upper01 q = q 0 1 := by
    unfold upper01
    field_simp
  have hrc : 2 * firstRoot q * upper02 q = q 0 2 := by
    unfold upper02
    field_simp
  have hse : secondRoot q * upper12 q = 2 * upper01 q * upper02 q - q 1 2 := by
    unfold upper12
    field_simp
  have h10 := hq.apply 0 1
  have h20 := hq.apply 0 2
  have h21 := hq.apply 1 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triangularFactor, diagonalForm, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith

theorem triangularFactor_det_pos (q : Mat) (hp : positivePivots q) :
    0 < (triangularFactor q).det := by
  have hr : 0 < firstRoot q := Real.sqrt_pos.mpr hp.1
  have hs : 0 < secondRoot q := Real.sqrt_pos.mpr hp.2.1
  have ht : 0 < thirdRoot q := Real.sqrt_pos.mpr hp.2.2
  simpa [triangularFactor, Matrix.det_fin_three] using mul_pos (mul_pos hr hs) ht

theorem positivePivots_diagonalForm : positivePivots diagonalForm := by
  norm_num [positivePivots, firstPivot, secondPivot, thirdPivot, firstRoot,
    secondRoot, upper01, upper02, upper12, diagonalForm]

theorem triangularFactor_diagonalForm : triangularFactor diagonalForm = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triangularFactor, firstPivot, secondPivot, thirdPivot, firstRoot,
      secondRoot, thirdRoot, upper01, upper02, upper12, diagonalForm]

theorem continuousAt_entry (q : Mat) (i j : Fin 3) :
    ContinuousAt (fun p : Mat => p i j) q :=
  ((continuous_apply j).comp (continuous_apply i)).continuousAt

theorem continuousAt_firstPivot (q : Mat) : ContinuousAt firstPivot q :=
  (continuousAt_entry q 0 0).div_const 2

theorem continuousAt_secondPivot (q : Mat) (hq : 0 < firstPivot q) :
    ContinuousAt secondPivot q := by
  have hr : firstRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hroot : ContinuousAt firstRoot q := Real.continuous_sqrt.continuousAt.comp
    (continuousAt_firstPivot q)
  have h01 : ContinuousAt upper01 q := by
    exact (continuousAt_entry q 0 1).div
      (continuousAt_const.mul hroot) (mul_ne_zero (by norm_num) hr)
  exact (continuousAt_const.mul (h01.pow 2)).sub (continuousAt_entry q 1 1)

theorem continuousAt_thirdPivot (q : Mat) (hq : 0 < firstPivot q)
    (hs : 0 < secondPivot q) : ContinuousAt thirdPivot q := by
  have hr : firstRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hsne : secondRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  have hroot : ContinuousAt firstRoot q := Real.continuous_sqrt.continuousAt.comp
    (continuousAt_firstPivot q)
  have h01 : ContinuousAt upper01 q :=
    (continuousAt_entry q 0 1).div
      (continuousAt_const.mul hroot) (mul_ne_zero (by norm_num) hr)
  have h02 : ContinuousAt upper02 q :=
    (continuousAt_entry q 0 2).div
      (continuousAt_const.mul hroot) (mul_ne_zero (by norm_num) hr)
  have hsecond : ContinuousAt secondRoot q := Real.continuous_sqrt.continuousAt.comp
    (continuousAt_secondPivot q hq)
  have h12 : ContinuousAt upper12 q :=
    (((continuousAt_const.mul h01).mul h02).sub (continuousAt_entry q 1 2)).div hsecond hsne
  exact (((continuousAt_const.mul (h02.pow 2)).sub (h12.pow 2)).sub
    (continuousAt_entry q 2 2)).div_const 2

theorem continuousAt_triangularFactor (q : Mat) (hp : positivePivots q) :
    ContinuousAt triangularFactor q := by
  have hr : firstRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp.1)
  have hs : secondRoot q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp.2.1)
  have hroot : ContinuousAt firstRoot q := Real.continuous_sqrt.continuousAt.comp
    (continuousAt_firstPivot q)
  have h01 : ContinuousAt upper01 q := (continuousAt_entry q 0 1).div
    (continuousAt_const.mul hroot) (mul_ne_zero (by norm_num) hr)
  have h02 : ContinuousAt upper02 q := (continuousAt_entry q 0 2).div
    (continuousAt_const.mul hroot) (mul_ne_zero (by norm_num) hr)
  have hsecond : ContinuousAt secondRoot q := Real.continuous_sqrt.continuousAt.comp
    (continuousAt_secondPivot q hp.1)
  have h12 : ContinuousAt upper12 q :=
    (((continuousAt_const.mul h01).mul h02).sub (continuousAt_entry q 1 2)).div hsecond hs
  have hthird : ContinuousAt thirdRoot q := Real.continuous_sqrt.continuousAt.comp
    (continuousAt_thirdPivot q hp.1 hp.2.1)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> first | assumption | exact continuousAt_const

theorem isOpen_positivePivots : IsOpen {q : Mat | positivePivots q} := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have h1 := (continuousAt_firstPivot q).eventually (Ioi_mem_nhds hq.1)
  have h2 := (continuousAt_secondPivot q hq.1).eventually (Ioi_mem_nhds hq.2.1)
  have h3 := (continuousAt_thirdPivot q hq.1 hq.2.1).eventually (Ioi_mem_nhds hq.2.2)
  exact h1.and (h2.and h3)

end
end JSP400.GramSection
