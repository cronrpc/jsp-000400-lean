import ShearNormalizer
import ShearClosureLift
import UpperGeneration

namespace JSP400

open Set

/-- The stronger half-space conclusion (A) used in Margulis's proof of Lemma 6. -/
theorem margulis_lemma6_A (M : Set SL3)
    (hbase : (1 : SL3) ∈ closure M)
    (hout : ∀ g ∈ M, g ∉ Subgroup.normalizer (shearGroup : Set SL3)) :
    (∀ a b c : ℝ, 0 ≤ a - c → upperUnipotent a b c ∈ closure (shearDoubleOrbit M)) ∨
      (∀ a b c : ℝ, a - c ≤ 0 → upperUnipotent a b c ∈ closure (shearDoubleOrbit M)) := by
  rcases margulis_lemma6_A2 M hbase hout with hplus | hminus
  · left
    intro a b c hac
    exact upperUnipotent_mem_closure_of_fixedLine M a b c (hplus ⟨a - c, hac, rfl⟩)
  · right
    intro a b c hac
    exact upperUnipotent_mem_closure_of_fixedLine M a b c (hminus ⟨a - c, hac, rfl⟩)

/-- Margulis, *Indefinite quadratic forms and unipotent flows on homogeneous
spaces* (1989), Lemma 6, printed p.403. If M lies outside the normalizer of V
and accumulates at the identity, W ∩ closure(V M V) algebraically generates W. -/
theorem margulis_lemma6 (M : Set SL3)
    (hbase : (1 : SL3) ∈ closure M)
    (hout : ∀ g ∈ M, g ∉ Subgroup.normalizer (shearGroup : Set SL3)) :
    Subgroup.closure ((upperGroup : Set SL3) ∩ closure (shearDoubleOrbit M)) = upperGroup :=
  generated_upper_inter_eq_of_half _ (margulis_lemma6_A M hbase hout)

end JSP400

#print axioms JSP400.margulis_lemma6
