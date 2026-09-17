import GramShear

namespace JSP400

open Matrix

theorem standardGram_quad (v : Vector3) :
    v ⬝ᵥ standardGram *ᵥ v = standardForm v := by
  simp [standardForm_apply, standardGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem gramMatrix_quad (g : SL3) (v : Vector3) :
    v ⬝ᵥ gramMatrix g *ᵥ v = standardForm (g • v) := by
  rw [gramMatrix, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  exact standardGram_quad (g.val.mulVec v)

/-- Equality of the quadratic evaluations determines an actual symmetric
three-by-three real matrix. -/
theorem symmetric_matrix_eq_of_quad (q r : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q.IsSymm) (hr : r.IsSymm)
    (h : ∀ v : Vector3, v ⬝ᵥ q *ᵥ v = v ⬝ᵥ r *ᵥ v) : q = r := by
  have h0 := h ![1, 0, 0]
  have h1 := h ![0, 1, 0]
  have h2 := h ![0, 0, 1]
  have h01 := h ![1, 1, 0]
  have h02 := h ![1, 0, 1]
  have h12 := h ![0, 1, 1]
  have hq10 := hq.apply 0 1
  have hq20 := hq.apply 0 2
  have hq21 := hq.apply 1 2
  have hr10 := hr.apply 0 1
  have hr20 := hr.apply 0 2
  have hr21 := hr.apply 1 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h01 h02 h12
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals linarith

/-- The Gram fiber of J is exactly the existing form-preserving subgroup H. -/
theorem gramMatrix_eq_standard_iff (g : SL3) :
    gramMatrix g = standardGram ↔ g ∈ formStabilizer standardForm := by
  constructor
  · intro hg v
    rw [← gramMatrix_quad, hg, standardGram_quad]
  · intro hg
    apply symmetric_matrix_eq_of_quad _ _ (gramMatrix_isSymm g) standardGram_isSymm
    intro v
    rw [gramMatrix_quad, standardGram_quad]
    exact hg v

@[simp] theorem gramMatrix_one : gramMatrix (1 : SL3) = standardGram := by
  change (1 : Matrix (Fin 3) (Fin 3) ℝ).transpose * standardGram * 1 = _
  simp

theorem gramMatrix_mul (g h : SL3) :
    gramMatrix (g * h) = h.val.transpose * gramMatrix g * h.val := by
  change (g.val * h.val).transpose * standardGram * (g.val * h.val) = _
  simp only [gramMatrix, Matrix.transpose_mul, mul_assoc]

theorem gramMatrix_mul_left_stabilizer (g h : SL3) (hh : h ∈ formStabilizer standardForm) :
    gramMatrix (h * g) = gramMatrix g := by
  rw [gramMatrix_mul, (gramMatrix_eq_standard_iff h).mpr hh]
  rfl

/-- Equal Gram matrices give precisely the same H-left coset, inside SL₃. -/
theorem gramMatrix_eq_iff_mul_inv_mem (g h : SL3) :
    gramMatrix g = gramMatrix h ↔ g * h⁻¹ ∈ formStabilizer standardForm := by
  constructor
  · intro heq
    apply (gramMatrix_eq_standard_iff _).mp
    rw [gramMatrix_mul, heq, ← gramMatrix_mul, mul_inv_cancel, gramMatrix_one]
  · intro hh
    have heq := gramMatrix_mul_left_stabilizer h (g * h⁻¹) hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq

end JSP400

#print axioms JSP400.gramMatrix_eq_iff_mul_inv_mem
