import StandardizedQuotient
import MargulisTheorem2

namespace JSP400

open Set

theorem standardized_orbit_not_relatively_compact {α : ℝ} (hα : 0 < α)
    (hi : Irrational α) :
    ¬ IsCompact (closure (MulAction.orbit (formStabilizer standardForm)
      (QuotientGroup.mk (standardizingSL α hα) : LatticeSpace))) := by
  intro hc
  exact standardized_stabilizer_quotient_not_compact hα hi (margulis_theorem2_quotient _ hc)

/-- The actual orbit of the integer lattice under the stabilizer of the original
positive irrational diagonal form is not relatively compact. -/
theorem irrational_ternary_orbit_not_relatively_compact {α : ℝ} (hα : 0 < α)
    (hi : Irrational α) :
    ¬ IsCompact (closure (MulAction.orbit (formStabilizer (ternaryForm α))
      (QuotientGroup.mk (1 : SL3) : LatticeSpace))) := by
  intro hc
  let s := standardizingSL α hα
  let K := closure (MulAction.orbit (formStabilizer (ternaryForm α))
    (QuotientGroup.mk (1 : SL3) : LatticeSpace))
  have himg : IsCompact ((fun L : LatticeSpace => s • L) '' K) :=
    hc.image (continuous_const_smul s)
  have hsub : MulAction.orbit (formStabilizer standardForm)
      (QuotientGroup.mk s : LatticeSpace) ⊆ (fun L : LatticeSpace => s • L) '' K := by
    rintro L ⟨h, rfl⟩
    have hg : s⁻¹ * h.val * s ∈ formStabilizer (ternaryForm α) := by
      apply (standardizingSL_conjugates hα _).mp
      change s * (s⁻¹ * h.val * s) * s⁻¹ ∈ formStabilizer standardForm
      simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
      exact h.property
    let g : formStabilizer (ternaryForm α) := ⟨s⁻¹ * h.val * s, hg⟩
    refine ⟨g • (QuotientGroup.mk (1 : SL3) : LatticeSpace), subset_closure ⟨g, rfl⟩, ?_⟩
    change QuotientGroup.mk (s * ((s⁻¹ * h.val * s) * 1)) =
      (QuotientGroup.mk (h.val * s) : LatticeSpace)
    simp [mul_assoc]
  exact standardized_orbit_not_relatively_compact hα hi
    (himg.of_isClosed_subset isClosed_closure (closure_minimal hsub himg.isClosed))

end JSP400
