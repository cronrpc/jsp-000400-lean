import NoncompactTernaryStabilizer

namespace JSP400

open Set
noncomputable section

def standardToTernaryHom {α : ℝ} (hα : 0 < α) :
    formStabilizer standardForm →* formStabilizer (ternaryForm α) where
  toFun g := ⟨(standardizingSL α hα)⁻¹ * g.val * standardizingSL α hα, by
    apply (standardizingSL_conjugates hα _).mp
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    exact g.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp [mul_assoc]

theorem continuous_standardToTernaryHom {α : ℝ} (hα : 0 < α) :
    Continuous (standardToTernaryHom hα) := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem standardToTernaryHom_surjective {α : ℝ} (hα : 0 < α) :
    Function.Surjective (standardToTernaryHom hα) := by
  intro g
  refine ⟨⟨standardizingSL α hα * g.val * (standardizingSL α hα)⁻¹,
    (standardizingSL_conjugates hα g.val).mpr g.property⟩, ?_⟩
  apply Subtype.ext
  change (standardizingSL α hα)⁻¹ *
    (standardizingSL α hα * g.val * (standardizingSL α hα)⁻¹) * standardizingSL α hα = g.val
  simp [mul_assoc]

/-- Exact transport of the lattice stabilizer at the standardized lattice. -/
theorem standardToTernaryHom_stabilizer {α : ℝ} (hα : 0 < α)
    (g : formStabilizer standardForm)
    (hg : g ∈ MulAction.stabilizer (formStabilizer standardForm)
      (QuotientGroup.mk (standardizingSL α hα) : LatticeSpace)) :
    standardToTernaryHom hα g ∈ integerGamma.comap (formStabilizer (ternaryForm α)).subtype := by
  rw [MulAction.mem_stabilizer_iff] at hg
  change (QuotientGroup.mk (g.val * standardizingSL α hα) : LatticeSpace) =
    QuotientGroup.mk (standardizingSL α hα) at hg
  have hi := QuotientGroup.eq.mp hg.symm
  change (standardizingSL α hα)⁻¹ * g.val * standardizingSL α hα ∈ integerGamma
  simpa only [mul_assoc] using hi

/-- The standard form's stabilizer quotient at the actual standardized lattice
is noncompact for every positive irrational parameter. -/
theorem standardized_stabilizer_quotient_not_compact {α : ℝ} (hα : 0 < α)
    (hi : Irrational α) :
    ¬ CompactSpace ((formStabilizer standardForm) ⧸
      MulAction.stabilizer (formStabilizer standardForm)
        (QuotientGroup.mk (standardizingSL α hα) : LatticeSpace)) := by
  intro hc
  let _ := hc
  have hcompact := compact_quotient_of_surjective_hom (standardToTernaryHom hα)
    (continuous_standardToTernaryHom hα) (standardToTernaryHom_surjective hα)
    (MulAction.stabilizer (formStabilizer standardForm)
      (QuotientGroup.mk (standardizingSL α hα) : LatticeSpace))
    (integerGamma.comap (formStabilizer (ternaryForm α)).subtype)
    (standardToTernaryHom_stabilizer hα)
  exact irrational_ternary_stabilizer_quotient_not_compact hα hi hcompact

end
end JSP400
