import CompactLattices

namespace JSP400

open Filter
open scoped Topology
open scoped Matrix.Norms.Elementwise

theorem matrix_mul_norm_le (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    ‖M * N‖ ≤ 3 * ‖M‖ * ‖N‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  change ‖∑ k : Fin 3, M i k * N k j‖ ≤ _
  calc
    _ ≤ ∑ k : Fin 3, ‖M i k * N k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 3, ‖M‖ * ‖N‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (M i) k).trans (norm_le_pi_norm M i))
        ((norm_le_pi_norm (N k) j).trans (norm_le_pi_norm N k))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- A nonidentity integral matrix differs from the identity by at least one
in the entrywise norm. -/
theorem integerGamma_norm_sub_one {γ : SL3} (hγ : γ ∈ integerGamma) (hne : γ ≠ 1) :
    1 ≤ ‖γ.val - 1‖ := by
  have hm : γ.val ≠ 1 := by
    intro h
    apply hne
    exact Subtype.ext h
  obtain ⟨i, j, hij⟩ : ∃ i j, γ.val i j ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    by_contra h
    push Not at h
    exact hm (funext (fun i => funext (h i)))
  obtain ⟨a, ha⟩ := (mem_integerGamma_iff γ).mp hγ i j
  let b : ℤ := a - if i = j then 1 else 0
  have hb : (b : ℝ) = (γ.val - 1) i j := by
    simp [b, Matrix.sub_apply, Matrix.one_apply, ha]
  have hbne : b ≠ 0 := by
    intro h
    have : (γ.val - 1) i j = 0 := by rw [← hb, h, Int.cast_zero]
    exact hij (sub_eq_zero.mp this)
  have hbi : (1 : ℤ) ≤ |b| := by
    have := abs_pos.mpr hbne
    omega
  have hbR : (1 : ℝ) ≤ ‖(γ.val - 1) i j‖ := by
    rw [← hb, Real.norm_eq_abs]
    exact_mod_cast hbi
  exact hbR.trans ((norm_le_pi_norm ((γ.val - 1) i) j).trans
    (norm_le_pi_norm (γ.val - 1) i))

theorem conjugate_sub_one (g a : SL3) :
    (g⁻¹ * a * g).val - 1 = g⁻¹.val * (a.val - 1) * g.val := by
  have hi : g⁻¹.val * g.val = 1 := by
    exact congrArg Subtype.val (inv_mul_cancel g)
  change g⁻¹.val * a.val * g.val - 1 = _
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hi]

/-- Stabilizers of all lattices in one compact family are uniformly discrete
at the identity. This is the compactness input for Margulis's Lemma 9. -/
theorem compact_lattice_stabilizers_discrete {K : Set LatticeSpace} (hK : IsCompact K) :
    ∃ η : ℝ, 0 < η ∧ ∀ L ∈ K, ∀ a : SL3,
      a • L = L → ‖a.val - 1‖ < η → a = 1 := by
  obtain ⟨C, hC, hcover⟩ := compact_lattice_representatives hK
  let f : SL3 → ℝ := fun g => 9 * ‖g⁻¹.val‖ * ‖g.val‖
  have hf : Continuous f := by
    have hi : Continuous (fun g : SL3 => ‖g⁻¹.val‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_inv)
    have hv : Continuous (fun g : SL3 => ‖g.val‖) :=
      continuous_norm.comp continuous_subtype_val
    exact (continuous_const.mul hi).mul hv
  obtain ⟨B, hB⟩ := hC.bddAbove_image hf.continuousOn
  let A : ℝ := max 1 B
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨1 / A, by positivity, ?_⟩
  intro L hL a hstab hnear
  obtain ⟨g, hg, rfl⟩ := hcover hL
  have hγ : g⁻¹ * a * g ∈ integerGamma := by
    have hEq : (QuotientGroup.mk (a * g) : LatticeSpace) = QuotientGroup.mk g := hstab
    simpa only [mul_assoc] using QuotientGroup.eq.mp hEq.symm
  by_contra hne
  have hconjne : g⁻¹ * a * g ≠ 1 := by
    intro h
    apply hne
    calc
      a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hlow := integerGamma_norm_sub_one hγ hconjne
  rw [conjugate_sub_one] at hlow
  have h1 := matrix_mul_norm_le (g⁻¹.val * (a.val - 1)) g.val
  have h2 := matrix_mul_norm_le g⁻¹.val (a.val - 1)
  have h2' := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 3 * ‖g.val‖ by positivity)
  have hbound : f g ≤ A := (hB (Set.mem_image_of_mem _ hg)).trans (le_max_right _ _)
  have hbound' := mul_le_mul_of_nonneg_right hbound (norm_nonneg (a.val - 1))
  have hsmall : ‖a.val - 1‖ * A < 1 := (lt_div_iff₀ hA).mp hnear
  change 9 * ‖g⁻¹.val‖ * ‖g.val‖ * ‖a.val - 1‖ ≤ A * ‖a.val - 1‖ at hbound'
  nlinarith

/-- Nonidentity stabilizer elements converging to the identity force their
lattices to escape every compact subset. -/
theorem small_stabilizers_escape_compacts (a : ℕ → SL3) (L : ℕ → LatticeSpace)
    (hstab : ∀ n, a n • L n = L n) (hne : ∀ n, a n ≠ 1)
    (ha : Tendsto a atTop (𝓝 1)) :
    ∀ K : Set LatticeSpace, IsCompact K → ∀ᶠ n in atTop, L n ∉ K := by
  intro K hK
  obtain ⟨η, hη, hsep⟩ := compact_lattice_stabilizers_discrete hK
  have hf : Continuous (fun g : SL3 => ‖g.val - 1‖) :=
    continuous_norm.comp (continuous_subtype_val.sub continuous_const)
  have ht : Tendsto (fun n => ‖(a n).val - 1‖) atTop (𝓝 0) := by
    convert (hf.tendsto 1).comp ha using 1
    · rfl
    · simp
  filter_upwards [ht.eventually (eventually_lt_nhds hη)] with n hn
  intro hL
  exact hne n (hsep (L n) hL (a n) (hstab n) hn)

/-- The contraction criterion used in Margulis §5, specialized and proved for
the actual arithmetic quotient. -/
theorem conjugating_stabilizer_escapes_compacts (y : LatticeSpace) (γ : SL3)
    (hγ : γ • y = y) (hne : γ ≠ 1) (g : ℕ → SL3)
    (hconj : Tendsto (fun n => g n * γ * (g n)⁻¹) atTop (𝓝 1)) :
    ∀ K : Set LatticeSpace, IsCompact K → ∀ᶠ n in atTop, g n • y ∉ K := by
  apply small_stabilizers_escape_compacts (fun n => g n * γ * (g n)⁻¹)
    (fun n => g n • y)
  · intro n
    simp only [mul_smul, inv_smul_smul, hγ]
  · intro n h
    apply hne
    calc
      γ = (g n)⁻¹ * (g n * γ * (g n)⁻¹) * g n := by group
      _ = 1 := by rw [h]; simp
  · exact hconj

end JSP400
