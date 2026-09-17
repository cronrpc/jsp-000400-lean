import MinimalInvariant
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Algebra.MulAction

/-! Margulis's minimal-set collision lemmas, using genuine continuous actions. -/

namespace JSP400

open Set

variable {G X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]

def subgroupInvariant (F : Subgroup G) (Y : Set X) : Prop :=
  ∀ f ∈ F, ∀ y ∈ Y, f • y ∈ Y

def hittingSet (Y Z : Set X) : Set G := {g | ∃ y ∈ Y, g • y ∈ Z}

theorem isClosed_hittingSet {Y Z : Set X} (hY : IsCompact Y) (hZ : IsClosed Z) :
    IsClosed (hittingSet Y Z : Set G) := by
  let : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  have hcont : Continuous (fun p : G × Y => p.1 • p.2.val) :=
    continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  have hc := isClosedMap_fst_of_compactSpace _ (hZ.preimage hcont)
  convert hc using 1
  ext g
  constructor
  · rintro ⟨y, hy, hgy⟩
    exact ⟨(g, ⟨y, hy⟩), hgy, rfl⟩
  · rintro ⟨⟨h, y⟩, hgy, rfl⟩
    exact ⟨y.val, y.property, hgy⟩

/-- Dense F-orbits and a normalizer collision force the whole translate into Z. -/
theorem normalizer_minimal_hit_subset (F : Subgroup G) {Y Z : Set X}
    (hZ : IsClosed Z) (hZi : subgroupInvariant F Z)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit F y) = Y)
    {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G))
    (hhit : g ∈ hittingSet Y Z) : (fun y => g • y) '' Y ⊆ Z := by
  obtain ⟨y, hy, hgy⟩ := hhit
  have hclosed : IsClosed ((fun x : X => g • x) ⁻¹' Z) :=
    hZ.preimage (continuous_const_smul g)
  have horbit : MulAction.orbit F y ⊆ (fun x : X => g • x) ⁻¹' Z := by
    rintro x ⟨f, rfl⟩
    have hf : g * f.val * g⁻¹ ∈ F :=
      (Subgroup.mem_set_normalizer_iff.mp hg f.val).mp f.property
    have h := hZi (g * f.val * g⁻¹) hf (g • y) hgy
    change g • (f.val • y) ∈ Z
    simpa only [mul_smul, inv_smul_smul] using h
  have hc : Y ⊆ (fun x : X => g • x) ⁻¹' Z :=
    hmin y hy ▸ closure_minimal horbit hclosed
  rintro z ⟨x, hx, rfl⟩
  exact hc hx

/-- Margulis Lemma 2: normalizer translates of a minimal closed invariant set
are either disjoint from it or equal to it. -/
theorem margulis_lemma2 (F : Subgroup G) {Y : Set X}
    (hY : IsClosed Y) (hYi : subgroupInvariant F Y)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit F y) = Y)
    {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G))
    (hhit : g ∈ hittingSet Y Y) : (fun y => g • y) '' Y = Y := by
  apply Subset.antisymm (normalizer_minimal_hit_subset F hY hYi hmin hg hhit)
  have hhitinv : g⁻¹ ∈ hittingSet Y Y := by
    obtain ⟨y, hy, hgy⟩ := hhit
    exact ⟨g • y, hgy, by simpa using hy⟩
  have hinv := normalizer_minimal_hit_subset F hY hYi hmin
    ((Subgroup.normalizer (F : Set G)).inv_mem hg) hhitinv
  intro y hy
  exact ⟨g⁻¹ • y, hinv ⟨y, hy, rfl⟩, smul_inv_smul g y⟩

def mixedDoubleSet (P Q : Subgroup G) (M : Set G) : Set G :=
  {g | ∃ q ∈ Q, ∃ m ∈ M, ∃ p ∈ P, g = q * m * p}

omit [TopologicalSpace G] [TopologicalSpace X] [ContinuousSMul G X] in
theorem mixedDoubleSet_subset_hitting (P Q : Subgroup G) (M : Set G)
    {Y Z : Set X} (hY : subgroupInvariant P Y) (hZ : subgroupInvariant Q Z)
    (hM : M ⊆ hittingSet Y Z) : mixedDoubleSet P Q M ⊆ hittingSet Y Z := by
  rintro g ⟨q, hq, m, hm, p, hp, rfl⟩
  obtain ⟨y, hy, hmy⟩ := hM hm
  refine ⟨p⁻¹ • y, hY p⁻¹ (P.inv_mem hp) y hy, ?_⟩
  simpa only [mul_smul, smul_inv_smul] using hZ q hq (m • y) hmy

/-- Margulis Lemma 1, with subgroup invariance and dense orbits stated directly.
No closure-of-hitting-set premise is assumed. -/
theorem margulis_lemma1 (F P Q : Subgroup G) (M : Set G)
    {Y Z : Set X} (hY : IsCompact Y) (hZ : IsClosed Z)
    (hPY : subgroupInvariant P Y) (hQZ : subgroupInvariant Q Z) (hFQ : F ≤ Q)
    (hM : M ⊆ hittingSet Y Z)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit F y) = Y)
    {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G))
    (hgcl : g ∈ closure (mixedDoubleSet P Q M)) : (fun y => g • y) '' Y ⊆ Z := by
  have hhit : g ∈ hittingSet Y Z :=
    closure_minimal (mixedDoubleSet_subset_hitting P Q M hPY hQZ hM)
      (isClosed_hittingSet hY hZ) hgcl
  exact normalizer_minimal_hit_subset F hZ
    (fun f hf => hQZ f (hFQ hf)) hmin hg hhit

/-- Margulis Lemma 3: the collision closure in the normalizer preserves Y. -/
theorem margulis_lemma3 (F P : Subgroup G) (M : Set G)
    {Y : Set X} (hY : IsCompact Y) (hYclosed : IsClosed Y)
    (hPY : subgroupInvariant P Y) (hFP : F ≤ P)
    (hM : M ⊆ hittingSet Y Y)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit F y) = Y)
    {g : G} (hg : g ∈ Subgroup.normalizer (F : Set G))
    (hgcl : g ∈ closure (mixedDoubleSet P P M)) : (fun y => g • y) '' Y = Y := by
  apply margulis_lemma2 F hYclosed (fun f hf => hPY f (hFP hf)) hmin hg
  exact closure_minimal (mixedDoubleSet_subset_hitting P P M hPY hPY hM)
    (isClosed_hittingSet hY hYclosed) hgcl

end JSP400
