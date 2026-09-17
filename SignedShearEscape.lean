import UpperDiagonalEscape

namespace JSP400

open Set Filter
open scoped Topology

theorem diagonalFlow_one : diagonalFlow 1 (by norm_num) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalFlow]

theorem unipotentOne_zero : unipotentOne 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentOne]

theorem shearElement_unipotent_factor (a b : ℝ) :
    shearElement a b = unipotentOne a * unipotentTwo (b - a ^ 2 / 2) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change (shearElement a b).val i j =
    ((unipotentOne a).val * (unipotentTwo (b - a ^ 2 / 2)).val) i j
  fin_cases i <;> fin_cases j <;>
    simp [shearElement, unipotentOne, unipotentTwo, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The actual orbit DV₁V₂⁺y for σ=1 and DV₁V₂⁻y for σ=−1. -/
def signedShearOrbit (L : LatticeSpace) (σ : ℝ) : Set LatticeSpace :=
  {M | ∃ t : ℝ, ∃ ht : 0 < t, ∃ a b : ℝ, 0 < σ * b ∧
    M = (diagonalFlow t (ne_of_gt ht) * unipotentOne a * unipotentTwo b) • L}

/-- Margulis Lemma 11, uniformly for both signs. -/
theorem margulis_lemma11 (L : LatticeSpace) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    ¬IsCompact (closure (signedShearOrbit L σ)) := by
  intro hc
  have : FirstCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
  have : FirstCountableTopology SL3 :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding.firstCountableTopology
  have : FirstCountableTopology LatticeSpace := inferInstance
  let x : ℕ → LatticeSpace := fun n => unipotentTwo (σ * ((n : ℝ) + 1)) • L
  have hx : ∀ n, x n ∈ closure (signedShearOrbit L σ) := by
    intro n
    apply subset_closure
    refine ⟨1, by norm_num, 0, σ * ((n : ℝ) + 1), ?_, ?_⟩
    · nlinarith [Nat.cast_nonneg (α := ℝ) n]
    · simp [x, diagonalFlow_one, unipotentOne_zero]
  obtain ⟨z, _, φ, hφ, hlim⟩ := hc.tendsto_subseq hx
  have hDV : diagonalShearOrbit z ⊆ closure (signedShearOrbit L σ) := by
    rintro M ⟨t, ht, w, ⟨a, b, rfl⟩, rfl⟩
    rw [shearElement_unipotent_factor, ← mul_assoc]
    let g := diagonalFlow t (ne_of_gt ht) * unipotentOne a * unipotentTwo (b - a ^ 2 / 2)
    have hcont : Continuous (fun y : LatticeSpace => g • y) := continuous_const_smul g
    apply isClosed_closure.mem_of_tendsto ((hcont.tendsto z).comp hlim)
    obtain ⟨N, hN⟩ := exists_nat_gt (-σ * (b - a ^ 2 / 2))
    filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
    apply subset_closure
    refine ⟨t, ht, a, (b - a ^ 2 / 2) + σ * ((φ n : ℝ) + 1), ?_, ?_⟩
    · have hnR : (N : ℝ) ≤ φ n := by exact_mod_cast hn
      nlinarith [Nat.cast_nonneg (α := ℝ) (φ n)]
    · change g • (unipotentTwo (σ * ((φ n : ℝ) + 1)) • L) = _
      rw [unipotentTwo_add]
      simp only [g, mul_smul]
  apply margulis_lemma10 z
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hDV isClosed_closure)

theorem positiveShearOrbit_not_relatively_compact (L : LatticeSpace) :
    ¬IsCompact (closure (signedShearOrbit L 1)) := margulis_lemma11 L 1 (by norm_num)

theorem negativeShearOrbit_not_relatively_compact (L : LatticeSpace) :
    ¬IsCompact (closure (signedShearOrbit L (-1))) := margulis_lemma11 L (-1) (by norm_num)

end JSP400
