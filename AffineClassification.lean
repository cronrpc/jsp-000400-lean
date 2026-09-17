import AffineTranslations

namespace JSP400.AffineClassification

open Set

noncomputable section

theorem eq_translation_of_slope_one (g : PositiveAffine) (hg : slope g = 1) :
    g = translation (offset g) := ext hg rfl

theorem eq_one_of_slope_offset (g : PositiveAffine) (ha : slope g = 1)
    (hb : offset g = 0) : g = 1 := ext ha hb

theorem all_translations_of_only_translations
    (K : Subgroup PositiveAffine) (hK : IsClosed (K : Set PositiveAffine))
    (hnear : (1 : PositiveAffine) ∈ closure ((K : Set PositiveAffine) \ {1}))
    (hslope : ∀ g ∈ K, slope g = 1) : ∀ b : ℝ, translation b ∈ K := by
  have hzero : (0 : ℝ) ∈ closure ((translations K : Set ℝ) \ {0}) := by
    have hi := mem_closure_image continuous_offset.continuousAt hnear
    change (0 : ℝ) ∈ closure (offset '' ((K : Set PositiveAffine) \ {1})) at hi
    apply closure_mono (fun b hb => ?_) hi
    obtain ⟨g, ⟨hg, hgn⟩, rfl⟩ := hb
    refine ⟨?_, ?_⟩
    · change translation (offset g) ∈ K
      rw [← eq_translation_of_slope_one g (hslope g hg)]
      exact hg
    · intro he
      exact hgn (eq_one_of_slope_offset g (hslope g hg) he)
  have htop := closed_addSubgroup_eq_top_of_zero_accumulation (translations K)
    (isClosed_translations K hK) hzero
  intro b
  change b ∈ translations K
  rw [htop]
  exact AddSubgroup.mem_top b

def fixedDilationExp (r t : ℝ) : PositiveAffine := fixedDilation r (Real.exp t) (Real.exp_pos t)

theorem fixedDilationExp_zero (r : ℝ) : fixedDilationExp r 0 = 1 := by
  apply ext
  · change Real.exp 0 = 1
    exact Real.exp_zero
  · change (1 - Real.exp 0) * r = 0
    simp

theorem fixedDilationExp_add (r t u : ℝ) :
    fixedDilationExp r (t + u) = fixedDilationExp r t * fixedDilationExp r u := by
  apply ext
  · change Real.exp (t + u) = Real.exp t * Real.exp u
    exact Real.exp_add t u
  · change (1 - Real.exp (t + u)) * r =
      (1 - Real.exp t) * r + Real.exp t * ((1 - Real.exp u) * r)
    rw [Real.exp_add]
    ring

theorem fixedDilationExp_neg (r t : ℝ) :
    fixedDilationExp r (-t) = (fixedDilationExp r t)⁻¹ := by
  apply mul_right_cancel (b := fixedDilationExp r t)
  rw [← fixedDilationExp_add, neg_add_cancel, fixedDilationExp_zero, inv_mul_cancel]

theorem continuous_fixedDilationExp (r : ℝ) : Continuous (fixedDilationExp r) := by
  apply Continuous.subtype_mk
  exact Real.continuous_exp.prodMk ((continuous_const.sub Real.continuous_exp).mul continuous_const)

def fixedDilationTimes (K : Subgroup PositiveAffine) (r : ℝ) : AddSubgroup ℝ where
  carrier := {t | fixedDilationExp r t ∈ K}
  zero_mem' := by change fixedDilationExp r 0 ∈ K; rw [fixedDilationExp_zero]; exact K.one_mem
  add_mem' := by
    intro t u ht hu
    change fixedDilationExp r (t + u) ∈ K
    rw [fixedDilationExp_add]
    exact K.mul_mem ht hu
  neg_mem' := by
    intro t ht
    change fixedDilationExp r (-t) ∈ K
    rw [fixedDilationExp_neg]
    exact K.inv_mem ht

theorem isClosed_fixedDilationTimes (K : Subgroup PositiveAffine)
    (hK : IsClosed (K : Set PositiveAffine)) (r : ℝ) :
    IsClosed (fixedDilationTimes K r : Set ℝ) := hK.preimage (continuous_fixedDilationExp r)

theorem all_fixedDilations_of_common_fixed_point
    (K : Subgroup PositiveAffine) (hK : IsClosed (K : Set PositiveAffine))
    (hnear : (1 : PositiveAffine) ∈ closure ((K : Set PositiveAffine) \ {1}))
    (r : ℝ) (hfix : ∀ g ∈ K, offset g = (1 - slope g) * r) :
    ∀ a : ℝ, ∀ ha : 0 < a, fixedDilation r a ha ∈ K := by
  have hcont : Continuous (fun g : PositiveAffine => Real.log (slope g)) :=
    continuous_slope.log (fun g => ne_of_gt g.property)
  have hzero : (0 : ℝ) ∈ closure ((fixedDilationTimes K r : Set ℝ) \ {0}) := by
    have hi := mem_closure_image hcont.continuousAt hnear
    simp only [slope_one, Real.log_one] at hi
    apply closure_mono (fun t ht => ?_) hi
    obtain ⟨g, ⟨hg, hgn⟩, rfl⟩ := ht
    have hgp : 0 < slope g := g.property
    have he : fixedDilationExp r (Real.log (slope g)) = g := by
      apply ext
      · exact Real.exp_log hgp
      · change (1 - Real.exp (Real.log (slope g))) * r = offset g
        rw [Real.exp_log hgp, hfix g hg]
    refine ⟨?_, ?_⟩
    · change fixedDilationExp r (Real.log (slope g)) ∈ K
      rw [he]
      exact hg
    · intro ht
      have hgeq : g = 1 := by
        rw [← he, show Real.log (slope g) = 0 from ht, fixedDilationExp_zero]
      exact hgn hgeq
  have htop := closed_addSubgroup_eq_top_of_zero_accumulation (fixedDilationTimes K r)
    (isClosed_fixedDilationTimes K hK r) hzero
  intro a ha
  have hm : Real.log a ∈ fixedDilationTimes K r := by rw [htop]; exact AddSubgroup.mem_top _
  change fixedDilationExp r (Real.log a) ∈ K at hm
  simpa only [fixedDilationExp, Real.exp_log ha] using hm

/-- A non-discrete closed subgroup of the positive affine group contains all
translations or all dilations about a common point. Non-discreteness is stated
as genuine accumulation at the identity, not merely nontriviality. -/
theorem nondiscrete_closed_affine_subgroup
    (K : Subgroup PositiveAffine) (hK : IsClosed (K : Set PositiveAffine))
    (hnear : (1 : PositiveAffine) ∈ closure ((K : Set PositiveAffine) \ {1})) :
    (∀ b : ℝ, translation b ∈ K) ∨
      ∃ r : ℝ, ∀ a : ℝ, ∀ ha : 0 < a, fixedDilation r a ha ∈ K := by
  classical
  by_cases hs : ∀ g ∈ K, slope g = 1
  · exact Or.inl (all_translations_of_only_translations K hK hnear hs)
  · push Not at hs
    obtain ⟨g, hg, hga⟩ := hs
    by_cases ht : ∃ b : ℝ, translation b ∈ K ∧ b ≠ 0
    · obtain ⟨b, hb, hb0⟩ := ht
      exact Or.inl (all_translations_of_nontrivial_translation_and_slope K hK g hg hga b hb hb0)
    · have htriv : ∀ b : ℝ, translation b ∈ K → b = 0 := by simpa using ht
      let r := offset g / (1 - slope g)
      have hden : 1 - slope g ≠ 0 := sub_ne_zero.mpr (Ne.symm hga)
      have hfix : ∀ h ∈ K, offset h = (1 - slope h) * r := by
        intro h hh
        have hc : translation ((1 - slope h) * offset g - (1 - slope g) * offset h) ∈ K := by
          rw [← commutator_translation]
          exact K.mul_mem (K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)) (K.inv_mem hh)
        have hz := htriv _ hc
        dsimp [r]
        field_simp
        nlinarith
      exact Or.inr ⟨r, all_fixedDilations_of_common_fixed_point K hK hnear r hfix⟩

end
end JSP400.AffineClassification
