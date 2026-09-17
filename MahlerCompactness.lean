import CompactLattices
import NoncompactOrbit
import SmallVectors
import Mathlib.Topology.Algebra.ProperAction.Basic

namespace JSP400

open Set
open scoped Matrix.Norms.Elementwise

/-- The representative bound to be supplied by integer basis reduction. -/
def BoundedReducedRepresentatives : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ g : SL3,
    (∀ v : IntegerVector3, v ≠ 0 → ε ≤ ‖g • integerVector v‖) →
    ∃ γ : IntegerSL3, ‖(g * integerSLHom γ).val‖ ≤ R

def latticesWithLowerBound (ε : ℝ) : Set LatticeSpace :=
  {L | ∀ w ∈ quotientLatticePoints L, w ≠ 0 → ε ≤ ‖w‖}

theorem integerVector_eq_zero_iff (v : IntegerVector3) : integerVector v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    change (v i : ℝ) = 0 at hi
    exact_mod_cast hi
  · rintro rfl
    ext i
    simp [integerVector]

theorem smul_integerVector_ne_zero (g : SL3) {v : IntegerVector3} (hv : v ≠ 0) :
    g • integerVector v ≠ 0 := by
  intro h
  have hh := congrArg (fun w : Vector3 => g⁻¹ • w) h
  rw [inv_smul_smul] at hh
  have hz : g⁻¹ • (0 : Vector3) = 0 := Matrix.mulVec_zero _
  rw [hz] at hh
  exact hv ((integerVector_eq_zero_iff v).mp hh)

/-- Uniformly bounded bases give a compact set of representatives and hence
relative compactness of the actual quotient lattices. -/
theorem compact_closure_latticesWithLowerBound (hb : BoundedReducedRepresentatives)
    {ε : ℝ} (hε : 0 < ε) : IsCompact (closure (latticesWithLowerBound ε)) := by
  obtain ⟨R, hR⟩ := hb ε hε
  let C : Set SL3 := {g | ‖g.val‖ ≤ R}
  have : ProperSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (ProperSpace (Fin 3 → Fin 3 → ℝ))
  have hC : IsCompact C := by
    have hc : IsCompact ((fun g : SL3 => g.val) ⁻¹'
        Metric.closedBall (0 : Matrix (Fin 3) (Fin 3) ℝ) R) :=
      Matrix.SpecialLinearGroup.isClosedEmbedding_val.isCompact_preimage
      (isCompact_closedBall (0 : Matrix (Fin 3) (Fin 3) ℝ) R)
    simpa only [C, Metric.closedBall, dist_zero_right, Set.preimage_ofPred_eq] using hc
  have hcover : latticesWithLowerBound ε ⊆
      (QuotientGroup.mk : SL3 → LatticeSpace) '' C := by
    intro L hL
    induction L using Quotient.inductionOn with
    | h g =>
      obtain ⟨γ, hγ⟩ := hR g (fun v hv => hL _ ⟨v, rfl⟩ (smul_integerVector_ne_zero g hv))
      refine ⟨g * integerSLHom γ, hγ, ?_⟩
      exact quotient_eq_of_latticePoints_eq (latticePoints_mul_integer g γ)
  have hc : IsCompact ((QuotientGroup.mk : SL3 → LatticeSpace) '' C) :=
    hC.image QuotientGroup.continuous_mk
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hcover hc.isClosed)

/-- The contrapositive Mahler implication, with its basis-reduction input
explicit, applied to a genuinely non-relatively-compact family. -/
theorem short_vector_of_noncompact_family (hb : BoundedReducedRepresentatives)
    {K : Set LatticeSpace} (hK : ¬ IsCompact (closure K)) {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ K, ∃ w ∈ quotientLatticePoints L, w ≠ 0 ∧ ‖w‖ < ε := by
  by_contra h
  push Not at h
  have hsub : K ⊆ latticesWithLowerBound ε := fun L hL w hw hw0 => h L hL w hw hw0
  apply hK
  exact (compact_closure_latticesWithLowerBound hb hε).of_isClosed_subset
    isClosed_closure (closure_mono hsub)

/-- All parameters of the original diagonal form are retained. The basis
bound used here is proved in `MahlerBoundedBasis`. -/
theorem short_vectors_of_bounded_representatives (hb : BoundedReducedRepresentatives)
    {α : ℝ} (hα : 0 < α) (hi : Irrational α) : HasArbitrarilyShortVectors α := by
  intro ε hε
  obtain ⟨L, hL, w, hw, hw0, hn⟩ := short_vector_of_noncompact_family hb
    (irrational_ternary_orbit_not_relatively_compact hα hi) hε
  obtain ⟨g, rfl⟩ := hL
  change w ∈ latticePoints (g.val * 1) at hw
  rw [mul_one] at hw
  obtain ⟨v, rfl⟩ := hw
  refine ⟨g.val, v, g.property, ?_, hn⟩
  intro hv
  apply hw0
  change g.val • integerVector v = 0
  rw [(integerVector_eq_zero_iff v).mpr hv]
  exact Matrix.mulVec_zero _

end JSP400
