import GramQuotient
import GramOrbitClosure
import SignedShearEscape

namespace JSP400

open Matrix Set

/-- The literal product H M D V₁ appearing in Margulis Lemma 7. D uses positive
diagonal parameters, exactly as in the original connected subgroup. -/
def lemma7Hull (M : Set SL3) : Set SL3 :=
  {g | ∃ h ∈ formStabilizer standardForm, ∃ m ∈ M,
    ∃ d : ℝ, ∃ hd : 0 < d, ∃ t : ℝ,
      g = h * m * diagonalFlow d (ne_of_gt hd) * unipotentOne t}

theorem subset_lemma7Hull (M : Set SL3) : M ⊆ lemma7Hull M := by
  intro m hm
  refine ⟨1, (formStabilizer standardForm).one_mem, m, hm, 1, by norm_num, 0, ?_⟩
  simp [diagonalFlow_one, unipotentOne_zero]

theorem lemma7Hull_left_invariant (M : Set SL3) {g h : SL3}
    (hg : g ∈ lemma7Hull M) (hh : h ∈ formStabilizer standardForm) :
    h * g ∈ lemma7Hull M := by
  obtain ⟨a, ha, m, hm, d, hd, t, rfl⟩ := hg
  exact ⟨h * a, (formStabilizer standardForm).mul_mem hh ha,
    m, hm, d, hd, t, by simp only [mul_assoc]⟩

theorem gramOrbitUnion_subset_hull_image (M : Set SL3) :
    gramOrbitUnion (gramMatrix '' M) ⊆ gramMatrix '' lemma7Hull M := by
  rintro q ⟨r, ⟨m, hm, rfl⟩, t, rfl⟩
  refine ⟨m * unipotentOne t, ?_, gramMatrix_mul_unipotentOne m t⟩
  exact ⟨1, (formStabilizer standardForm).one_mem, m, hm,
    1, by norm_num, t, by simp [diagonalFlow_one]⟩

theorem diagonalFlow_inv_eq (d : ℝ) (hd : d ≠ 0) :
    (diagonalFlow d hd)⁻¹ = diagonalFlow d⁻¹ (inv_ne_zero hd) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  ext i j
  change ((diagonalFlow d hd).val * (diagonalFlow d⁻¹ (inv_ne_zero hd)).val) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFlow, Matrix.mul_apply, Fin.sum_univ_succ, hd]

theorem unipotentTwo_zero : unipotentTwo 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentTwo]

theorem scaled_unipotentTwo_mem_lemma7Hull (M : Set SL3) (m : SL3) (hm : m ∈ M)
    (b : ℝ) (hb : unipotentTwo b * m⁻¹ ∈ formStabilizer standardForm)
    (d : ℝ) (hd : 0 < d) :
    unipotentTwo (d ^ 2 * b) ∈ lemma7Hull M := by
  let a := diagonalFlow d (ne_of_gt hd)
  have ha : a ∈ formStabilizer standardForm := diagonalFlow_mem_standardStabilizer _ _
  refine ⟨a * (unipotentTwo b * m⁻¹), (formStabilizer standardForm).mul_mem ha hb,
    m, hm, d⁻¹, inv_pos.mpr hd, 0, ?_⟩
  rw [unipotentOne_zero, mul_one, ← diagonalFlow_inv_eq d (ne_of_gt hd)]
  have hc := diagonalFlow_unipotentTwo d (ne_of_gt hd) b
  change a * unipotentTwo b = unipotentTwo (d ^ 2 * b) * a at hc
  calc
    unipotentTwo (d ^ 2 * b) = (a * unipotentTwo b) * a⁻¹ := by rw [hc]; simp
    _ = a * (unipotentTwo b * m⁻¹) * m * a⁻¹ := by simp only [mul_assoc, inv_mul_cancel, mul_one]

/-- If one form in the original set already lies in the fixed line, diagonal
conjugation supplies an entire one-sided V₂ orbit. -/
theorem lemma7_fixed_case (M : Set SL3) (hbase : (1 : SL3) ∈ closure M)
    (hout : ∀ g ∈ M, g ∉ formStabilizer standardForm)
    (m : SL3) (hm : m ∈ M) (hfixed : gramMatrix m ∈ gramFlag 2) :
    (∀ t : ℝ, 0 ≤ t → unipotentTwo t ∈ closure (lemma7Hull M)) ∨
      (∀ t : ℝ, t ≤ 0 → unipotentTwo t ∈ closure (lemma7Hull M)) := by
  obtain ⟨b, hb⟩ := gramFixed_of_det_one (gramMatrix m) hfixed (gramMatrix_det m)
  have heq : gramMatrix (unipotentTwo (b / 2)) = gramMatrix m := by
    rw [gramMatrix_unipotentTwo, hb]
    congr 1
    ring
  have hfactor := (gramMatrix_eq_iff_mul_inv_mem (unipotentTwo (b / 2)) m).mp heq
  have hb0 : b / 2 ≠ 0 := by
    intro hz
    have he : gramMatrix m = standardGram := by
      rw [← heq, hz, unipotentTwo_zero, gramMatrix_one]
    exact hout m hm ((gramMatrix_eq_standard_iff m).mp he)
  have hzero : unipotentTwo 0 ∈ closure (lemma7Hull M) := by
    rw [unipotentTwo_zero]
    exact closure_mono (subset_lemma7Hull M) hbase
  have hscale : ∀ t : ℝ, 0 < t / (b / 2) → unipotentTwo t ∈ closure (lemma7Hull M) := by
    intro t ht
    let d := Real.sqrt (t / (b / 2))
    have hd : 0 < d := Real.sqrt_pos.mpr ht
    have he : d ^ 2 * (b / 2) = t := by
      rw [Real.sq_sqrt ht.le]
      exact div_mul_cancel₀ _ hb0
    rw [← he]
    exact subset_closure (scaled_unipotentTwo_mem_lemma7Hull M m hm (b / 2) hfactor d hd)
  rcases lt_or_gt_of_ne hb0 with hn | hp
  · apply Or.inr
    intro t ht
    rcases ht.eq_or_lt with rfl | ht
    · exact hzero
    · exact hscale t (div_pos_of_neg_of_neg ht hn)
  · apply Or.inl
    intro t ht
    rcases ht.eq_or_lt with he | ht
    · exact he ▸ hzero
    · exact hscale t (div_pos ht hp)

end JSP400

#print axioms JSP400.lemma7_fixed_case
