import GramTriangular
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! An explicit continuous local section of the Gram map near the reference form. -/

namespace JSP400.GramSection

open Matrix Set
open scoped Topology
noncomputable section

def referenceBasis : Mat := !![1, 0, 1; 0, 1, 0; 1, 0, -1]
def referenceBasisInv : Mat := !![1 / 2, 0, 1 / 2; 0, 1, 0; 1 / 2, 0, -1 / 2]

theorem referenceBasis_mul_inv : referenceBasis * referenceBasisInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [referenceBasis, referenceBasisInv, Matrix.mul_apply, Fin.sum_univ_succ]

theorem referenceBasis_inv_mul : referenceBasisInv * referenceBasis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [referenceBasis, referenceBasisInv, Matrix.mul_apply, Fin.sum_univ_succ]

theorem referenceBasis_congruence :
    referenceBasis.transpose * standardGram * referenceBasis = diagonalForm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [referenceBasis, standardGram, diagonalForm, Matrix.mul_apply, Fin.sum_univ_succ]

def transformedGram (q : Mat) : Mat := referenceBasis.transpose * q * referenceBasis
def rawFrame (q : Mat) : Mat :=
  referenceBasis * triangularFactor (transformedGram q) * referenceBasisInv
def sectionDomain : Set Mat := {q | positivePivots (transformedGram q)}

theorem continuous_transformedGram : Continuous transformedGram := by
  unfold transformedGram
  exact (continuous_const.mul continuous_id).mul continuous_const

theorem isOpen_sectionDomain : IsOpen sectionDomain :=
  isOpen_positivePivots.preimage continuous_transformedGram

theorem standardGram_mem_sectionDomain : standardGram ∈ sectionDomain := by
  change positivePivots (referenceBasis.transpose * standardGram * referenceBasis)
  rw [referenceBasis_congruence]
  exact positivePivots_diagonalForm

theorem rawFrame_standardGram : rawFrame standardGram = 1 := by
  simp only [rawFrame, transformedGram, referenceBasis_congruence,
    triangularFactor_diagonalForm, mul_one, referenceBasis_mul_inv]

theorem rawFrame_det_pos (q : sectionDomain) : 0 < (rawFrame q).det := by
  have hp := triangularFactor_det_pos (transformedGram q) q.property
  have hb : referenceBasis.det = -2 := by
    norm_num [referenceBasis, Matrix.det_fin_three]
  have hi : referenceBasisInv.det = -1 / 2 := by
    norm_num [referenceBasisInv, Matrix.det_fin_three]
  simp only [rawFrame, Matrix.det_mul, hb, hi]
  nlinarith

theorem rawFrame_congruence (q : sectionDomain) (hq : q.val.IsSymm) :
    (rawFrame q).transpose * standardGram * rawFrame q = q.val := by
  have ht := triangularFactor_congruence (transformedGram q)
    (pullback_isSymm _ hq referenceBasis) q.property
  have hleft : referenceBasisInv.transpose * referenceBasis.transpose = 1 := by
    rw [← Matrix.transpose_mul, referenceBasis_mul_inv, Matrix.transpose_one]
  calc
    (rawFrame q).transpose * standardGram * rawFrame q =
        referenceBasisInv.transpose *
          ((triangularFactor (transformedGram q)).transpose *
            (referenceBasis.transpose * standardGram * referenceBasis) *
              triangularFactor (transformedGram q)) * referenceBasisInv := by
      simp only [rawFrame, Matrix.transpose_mul, mul_assoc]
    _ = referenceBasisInv.transpose * transformedGram q * referenceBasisInv := by
      rw [referenceBasis_congruence, ht]
    _ = q.val := by
      simp only [transformedGram, ← mul_assoc, hleft, one_mul]
      rw [mul_assoc, referenceBasis_mul_inv, mul_one]

theorem rawFrame_det_eq_one (q : sectionDomain) (hq : q.val.IsSymm)
    (hd : q.val.det = 1) : (rawFrame q).det = 1 := by
  have he := congrArg Matrix.det (rawFrame_congruence q hq)
  simp only [Matrix.det_mul, Matrix.det_transpose, standardGram_det, mul_one, hd] at he
  have hp := rawFrame_det_pos q
  nlinarith

theorem continuous_rawFrame : Continuous (fun q : sectionDomain => rawFrame q) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hbase : ContinuousAt (fun p : Mat => triangularFactor (transformedGram p)) q.val :=
    (continuousAt_triangularFactor (transformedGram q) q.property).comp
      continuous_transformedGram.continuousAt
  have hc : ContinuousAt (fun p : sectionDomain =>
      triangularFactor (transformedGram p)) q := hbase.comp continuous_subtype_val.continuousAt
  exact (continuousAt_const.mul hc).mul continuousAt_const

def sectionScale (q : Mat) : ℝ := ((rawFrame q).det ^ ((3 : ℝ)⁻¹))⁻¹

theorem sectionScale_cube (q : sectionDomain) :
    sectionScale q ^ 3 * (rawFrame q).det = 1 := by
  unfold sectionScale
  have hc : ((rawFrame q).det ^ ((3 : ℝ)⁻¹)) ^ (3 : ℕ) = (rawFrame q).det := by
    simpa using Real.rpow_inv_natCast_pow (rawFrame_det_pos q).le
      (by decide : (3 : ℕ) ≠ 0)
  rw [inv_pow, hc]
  exact inv_mul_cancel₀ (ne_of_gt (rawFrame_det_pos q))

def gramSection (q : sectionDomain) : SL3 :=
  ⟨sectionScale q • rawFrame q, by
    rw [Matrix.det_smul]
    simpa using sectionScale_cube q⟩

theorem continuous_gramSection : Continuous gramSection := by
  apply Continuous.subtype_mk
  have hc : Continuous (fun q : sectionDomain => (rawFrame q).det) :=
    continuous_rawFrame.matrix_det
  have hp : Continuous (fun q : sectionDomain => (rawFrame q).det ^ ((3 : ℝ)⁻¹)) :=
    hc.rpow_const (fun q => Or.inl (ne_of_gt (rawFrame_det_pos q)))
  have hi : Continuous (fun q : sectionDomain => sectionScale q) :=
    hp.inv₀ (fun q => ne_of_gt (Real.rpow_pos_of_pos (rawFrame_det_pos q) _))
  exact hi.smul continuous_rawFrame

theorem gramSection_standardGram :
    gramSection ⟨standardGram, standardGram_mem_sectionDomain⟩ = 1 := by
  apply Subtype.ext
  change sectionScale standardGram • rawFrame standardGram = (1 : Mat)
  simp [sectionScale, rawFrame_standardGram]

theorem gramMatrix_gramSection (q : sectionDomain) (hq : q.val.IsSymm)
    (hd : q.val.det = 1) : gramMatrix (gramSection q) = q.val := by
  have hc : sectionScale q = 1 := by simp [sectionScale, rawFrame_det_eq_one q hq hd]
  change (sectionScale q • rawFrame q).transpose * standardGram *
    (sectionScale q • rawFrame q) = _
  rw [hc, one_smul]
  exact rawFrame_congruence q hq

end
end JSP400.GramSection
