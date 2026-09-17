import AffineSubgroup
import Mathlib.Analysis.SpecificLimits.Basic

namespace JSP400.AffineClassification

open Set Filter
open scoped Topology

theorem closed_addSubgroup_eq_top_of_zero_accumulation (S : AddSubgroup ℝ)
    (hS : IsClosed (S : Set ℝ)) (hzero : (0 : ℝ) ∈ closure ((S : Set ℝ) \ {0})) : S = ⊤ := by
  have hd : Dense (S : Set ℝ) := S.dense_of_not_isolated_zero (by
    intro ε hε
    obtain ⟨x, hxI, hxS, hxn⟩ := mem_closure_iff.mp hzero (Ioo (-ε) ε) isOpen_Ioo (by
      exact ⟨by linarith, hε⟩)
    have hxne : x ≠ 0 := hxn
    rcases lt_or_gt_of_ne hxne with hn | hp
    · exact ⟨-x, S.neg_mem hxS, by constructor <;> linarith [hxI.1]⟩
    · exact ⟨x, hxS, hp, hxI.2⟩)
  apply SetLike.coe_injective
  change (S : Set ℝ) = univ
  rw [← hS.closure_eq]
  exact hd.closure_eq

theorem closed_addSubgroup_eq_top_of_contraction (S : AddSubgroup ℝ)
    (hS : IsClosed (S : Set ℝ)) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hscale : ∀ x ∈ S, r * x ∈ S) (x : ℝ) (hx : x ∈ S) (hxn : x ≠ 0) : S = ⊤ := by
  apply closed_addSubgroup_eq_top_of_zero_accumulation S hS
  have hmem (n : ℕ) : r ^ n * x ∈ (S : Set ℝ) \ {0} := by
    refine ⟨?_, mul_ne_zero (pow_ne_zero n (ne_of_gt hr)) hxn⟩
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      change r ^ (n + 1) * x ∈ S
      rw [pow_succ', mul_assoc]
      exact hscale _ ih
  have ht : Tendsto (fun n : ℕ => r ^ n * x) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).mul_const x
  exact mem_closure_of_tendsto ht (Eventually.of_forall hmem)

theorem all_translations_of_nontrivial_translation_and_slope
    (K : Subgroup PositiveAffine) (hK : IsClosed (K : Set PositiveAffine))
    (g : PositiveAffine) (hg : g ∈ K) (ha : slope g ≠ 1)
    (b : ℝ) (hb : translation b ∈ K) (hb0 : b ≠ 0) :
    ∀ c : ℝ, translation c ∈ K := by
  have hscale (g : PositiveAffine) (hg : g ∈ K) :
      ∀ c ∈ translations K, slope g * c ∈ translations K := by
    intro c hc
    change translation (slope g * c) ∈ K
    rw [← conjugate_translation]
    exact K.mul_mem (K.mul_mem hg hc) (K.inv_mem hg)
  have htop : translations K = ⊤ := by
    rcases lt_or_gt_of_ne ha with hlo | hhi
    · exact closed_addSubgroup_eq_top_of_contraction (translations K)
        (isClosed_translations K hK) (slope g) g.property hlo (hscale g hg) b hb hb0
    · apply closed_addSubgroup_eq_top_of_contraction (translations K)
        (isClosed_translations K hK) (slope g⁻¹) g⁻¹.property ?_ (hscale g⁻¹ (K.inv_mem hg)) b hb hb0
      exact inv_lt_one_of_one_lt₀ hhi
  intro c
  change c ∈ translations K
  rw [htop]
  exact AddSubgroup.mem_top c

end JSP400.AffineClassification
