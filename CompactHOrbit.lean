import UnipotentOneNormalizer
import LatticeCollision
import MinimalSubsystem
import MargulisLemma7
import OrbitQuotientTopology
import CompactGroupQuotient

/-! The transverse-return exclusion in the proof of Margulis's compact-orbit theorem. -/

namespace JSP400

open Set

theorem lemma7Hull_subset_hitting {Y K : Set LatticeSpace} (M : Set SL3)
    (hV : subgroupInvariant principalUnipotent Y)
    (hD : ∀ t : ℝ, ∀ ht : 0 < t, ∀ y ∈ Y, diagonalFlow t (ne_of_gt ht) • y ∈ Y)
    (hH : subgroupInvariant (formStabilizer standardForm) K)
    (hM : M ⊆ hittingSet Y K) : lemma7Hull M ⊆ hittingSet Y K := by
  rintro g ⟨h, hh, m, hm, d, hd, t, rfl⟩
  obtain ⟨y, hy, hmy⟩ := hM hm
  let p := diagonalFlow d (ne_of_gt hd) * unipotentOne t
  have hpy : p⁻¹ • y ∈ Y := by
    change (diagonalFlow d (ne_of_gt hd) * unipotentOne t)⁻¹ • y ∈ Y
    rw [_root_.mul_inv_rev, mul_smul, unipotentOne_inv, diagonalFlow_inv_eq]
    exact hV _ ⟨-t, rfl⟩ _ (hD d⁻¹ (inv_pos.mpr hd) y hy)
  refine ⟨p⁻¹ • y, hpy, ?_⟩
  have he : h * m * diagonalFlow d (ne_of_gt hd) * unipotentOne t = h * m * p := by
    simp only [p, mul_assoc]
  rw [he, mul_smul, smul_inv_smul, mul_smul]
  exact hH h hh (m • y) hmy

/-- A compact H-invariant set cannot receive transverse returns approaching
the identity from a nonempty compact V₁-minimal set which is D-invariant.
This is the actual Lemmas 7 and 11 contradiction, prior to proving D-invariance. -/
theorem no_transverse_returns_of_diagonal_minimal {Y K : Set LatticeSpace}
    (hY : IsCompact Y) (hYn : Y.Nonempty)
    (hV : subgroupInvariant principalUnipotent Y)
    (hD : ∀ t : ℝ, ∀ ht : 0 < t, ∀ y ∈ Y, diagonalFlow t (ne_of_gt ht) • y ∈ Y)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit principalUnipotent y) = Y)
    (hK : IsCompact K) (hKc : IsClosed K)
    (hH : subgroupInvariant (formStabilizer standardForm) K) :
    (1 : SL3) ∉ closure {g : SL3 | g ∉ formStabilizer standardForm ∧
      g ∈ hittingSet Y K} := by
  intro hbase
  let M : Set SL3 := {g | g ∉ formStabilizer standardForm ∧ g ∈ hittingSet Y K}
  have hcl : closure (lemma7Hull M) ⊆ hittingSet Y K :=
    closure_minimal (lemma7Hull_subset_hitting M hV hD hH (fun _ h => h.2))
      (isClosed_hittingSet hY hKc)
  have hV' : subgroupInvariant principalUnipotent K :=
    fun g hg => hH g (principalUnipotent_le_standardStabilizer hg)
  have htranslate (b : ℝ) (hb : unipotentTwo b ∈ closure (lemma7Hull M)) :
      (fun y => unipotentTwo b • y) '' Y ⊆ K :=
    normalizer_minimal_hit_subset principalUnipotent hKc hV' hmin
      (unipotentTwo_mem_principalNormalizer b) (hcl hb)
  obtain ⟨y, hy⟩ := hYn
  have hcontr (σ : ℝ) (hs : σ ^ 2 = 1)
      (hray : ∀ b : ℝ, 0 < σ * b → unipotentTwo b ∈ closure (lemma7Hull M)) : False := by
    have hsub : signedShearOrbit y σ ⊆ K := by
      rintro z ⟨d, hd, a, b, hb, rfl⟩
      simp only [mul_smul]
      exact hH _ (diagonalFlow_mem_standardStabilizer d (ne_of_gt hd)) _
        (hH _ (unipotentOne_mem_standardStabilizer a) _
          (htranslate b (hray b hb) ⟨y, hy, rfl⟩))
    exact margulis_lemma11 y σ hs
      (hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hKc))
  rcases margulis_lemma7 M hbase (fun _ h => h.1) with hp | hn
  · exact hcontr 1 (by norm_num) (fun b hb => hp b (by simpa using hb.le))
  · exact hcontr (-1) (by norm_num) (fun b hb => hn b (by nlinarith))

theorem standardStabilizer_isClosed : IsClosed (formStabilizer standardForm : Set SL3) := by
  have he : (formStabilizer standardForm : Set SL3) =
      {g | gramMatrix g = standardGram} := by
    ext g
    exact (gramMatrix_eq_standard_iff g).symm
  rw [he]
  exact isClosed_eq continuous_gramMatrix continuous_const

/-- The final compact-orbit deduction in Theorem 2, once the D-invariance of
the selected V₁-minimal subsystem has been established. `MargulisTheorem2`
proves this invariance using Lemma 5(II) and obtains the full theorem. -/
theorem compact_H_orbit_of_diagonal_minimal (z : LatticeSpace)
    (hc : IsCompact (closure (MulAction.orbit (formStabilizer standardForm) z)))
    {X Y : Set LatticeSpace}
    (hXK : X ⊆ closure (MulAction.orbit (formStabilizer standardForm) z))
    (hXc : IsCompact X)
    (hXmin : ∀ x ∈ X, closure (MulAction.orbit (formStabilizer standardForm) x) = X)
    (hYX : Y ⊆ X) (hYc : IsCompact Y) (hYn : Y.Nonempty)
    (hV : subgroupInvariant principalUnipotent Y)
    (hD : ∀ t : ℝ, ∀ ht : 0 < t, ∀ y ∈ Y, diagonalFlow t (ne_of_gt ht) • y ∈ Y)
    (hYmin : ∀ y ∈ Y, closure (MulAction.orbit principalUnipotent y) = Y) :
    IsCompact (MulAction.orbit (formStabilizer standardForm) z) := by
  let H := formStabilizer standardForm
  let K := closure (MulAction.orbit H z)
  have hHK : subgroupInvariant H K := subgroupInvariant_orbit_closure H z
  have hno := no_transverse_returns_of_diagonal_minimal hYc hYn hV hD hYmin hc
    isClosed_closure hHK
  obtain ⟨y, hy⟩ := hYn
  have hyK : y ∈ K := hXK (hYX hy)
  have hno_y : (1 : SL3) ∉ closure {g : SL3 | g ∉ H ∧ g • y ∈ K} := by
    intro h
    apply hno
    apply closure_mono (fun g hg => ?_) h
    exact ⟨hg.1, y, hy, hg.2⟩
  have hquot : CompactSpace (H ⧸ (MulAction.stabilizer SL3 y).comap H.subtype) := by
    by_contra hn
    have hcy : IsCompact (closure (MulAction.orbit H y)) := hXmin y (hYX hy) ▸ hXc
    have hm : ∀ w ∈ closure (MulAction.orbit H y),
        closure (MulAction.orbit H w) = closure (MulAction.orbit H y) := by
      rw [hXmin y (hYX hy)]
      exact hXmin
    have hr := margulis_lemma4 H standardStabilizer_isClosed y hcy hm hn
    apply hno_y
    apply closure_mono (fun g hg => ?_) hr
    exact ⟨hg.1, hXK (by
      rw [← hXmin y (hYX hy)]
      exact subset_closure hg.2)⟩
  have : CompactSpace (H ⧸ MulAction.stabilizer H y) := hquot
  have hcy := isCompact_orbit_of_compact_stabilizer_quotient H y
  have hz : z ∈ MulAction.orbit H y :=
    mem_orbit_of_no_transverse_returns H y z K (isOpenMap_latticeOrbit y) hyK
      subset_closure hno_y
  obtain ⟨h, rfl⟩ := hz
  simpa only [MulAction.orbit_smul] using hcy

theorem compact_H_stabilizer_quotient_of_diagonal_minimal (z : LatticeSpace)
    (hc : IsCompact (closure (MulAction.orbit (formStabilizer standardForm) z)))
    {X Y : Set LatticeSpace}
    (hXK : X ⊆ closure (MulAction.orbit (formStabilizer standardForm) z))
    (hXc : IsCompact X)
    (hXmin : ∀ x ∈ X, closure (MulAction.orbit (formStabilizer standardForm) x) = X)
    (hYX : Y ⊆ X) (hYc : IsCompact Y) (hYn : Y.Nonempty)
    (hV : subgroupInvariant principalUnipotent Y)
    (hD : ∀ t : ℝ, ∀ ht : 0 < t, ∀ y ∈ Y, diagonalFlow t (ne_of_gt ht) • y ∈ Y)
    (hYmin : ∀ y ∈ Y, closure (MulAction.orbit principalUnipotent y) = Y) :
    CompactSpace ((formStabilizer standardForm) ⧸
      MulAction.stabilizer (formStabilizer standardForm) z) := by
  let H := formStabilizer standardForm
  let K := closure (MulAction.orbit H z)
  have hHK : subgroupInvariant H K := subgroupInvariant_orbit_closure H z
  have hno := no_transverse_returns_of_diagonal_minimal hYc hYn hV hD hYmin hc
    isClosed_closure hHK
  obtain ⟨y, hy⟩ := hYn
  have hyK : y ∈ K := hXK (hYX hy)
  have hno_y : (1 : SL3) ∉ closure {g : SL3 | g ∉ H ∧ g • y ∈ K} := by
    intro h
    apply hno
    apply closure_mono (fun g hg => ?_) h
    exact ⟨hg.1, y, hy, hg.2⟩
  have hquot : CompactSpace (H ⧸ (MulAction.stabilizer SL3 y).comap H.subtype) := by
    by_contra hn
    have hcy : IsCompact (closure (MulAction.orbit H y)) := hXmin y (hYX hy) ▸ hXc
    have hm : ∀ w ∈ closure (MulAction.orbit H y),
        closure (MulAction.orbit H w) = closure (MulAction.orbit H y) := by
      rw [hXmin y (hYX hy)]
      exact hXmin
    have hr := margulis_lemma4 H standardStabilizer_isClosed y hcy hm hn
    apply hno_y
    apply closure_mono (fun g hg => ?_) hr
    exact ⟨hg.1, hXK (by
      rw [← hXmin y (hYX hy)]
      exact subset_closure hg.2)⟩
  have : CompactSpace (H ⧸ MulAction.stabilizer H y) := hquot
  have hcy := isCompact_orbit_of_compact_stabilizer_quotient H y
  have hz : z ∈ MulAction.orbit H y :=
    mem_orbit_of_no_transverse_returns H y z K (isOpenMap_latticeOrbit y) hyK
      subset_closure hno_y
  obtain ⟨h, rfl⟩ := hz
  exact compact_stabilizer_quotient_smul y h


end JSP400

