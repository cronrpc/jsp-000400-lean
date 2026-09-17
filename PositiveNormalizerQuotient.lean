import AffineMatrixBridge
import NormalizerCoordinates

namespace JSP400

open Matrix Set
open AffineClassification
noncomputable section

def positiveMatrixDomain : Set SL3 := {g | 0 < g.val 0 0}

theorem continuous_SLentry (i j : Fin 3) : Continuous (fun g : SL3 => g.val i j) :=
  (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply id continuous_id i)

theorem isOpen_positiveMatrixDomain : IsOpen positiveMatrixDomain :=
  isOpen_lt continuous_const (continuous_SLentry 0 0)

theorem one_mem_positiveMatrixDomain : (1 : SL3) ∈ positiveMatrixDomain := by
  change (0 : ℝ) < 1
  norm_num

def positiveMatrixAffine (g : positiveMatrixDomain) : PositiveAffine :=
  ⟨((g.val.val 0 0) ^ 2, g.val.val 0 0 * g.val.val 0 2 - (g.val.val 0 1) ^ 2 / 2),
    sq_pos_of_pos g.property⟩

theorem continuous_positiveMatrixAffine : Continuous positiveMatrixAffine := by
  apply Continuous.subtype_mk
  have hc (i j : Fin 3) : Continuous (fun g : positiveMatrixDomain => g.val.val i j) :=
    (continuous_SLentry i j).comp continuous_subtype_val
  exact ((hc 0 0).pow 2).prodMk
    (((hc 0 0).mul (hc 0 2)).sub (((hc 0 1).pow 2).div_const 2))

theorem positiveMatrixAffine_one :
    positiveMatrixAffine ⟨1, one_mem_positiveMatrixDomain⟩ = 1 := by
  apply AffineClassification.ext
  · change (1 : ℝ) ^ 2 = 1
    norm_num
  · change (1 : ℝ) * 0 - 0 ^ 2 / 2 = 0
    norm_num

theorem positiveNormalizer_factor (g : positiveMatrixDomain)
    (hg : g.val ∈ Subgroup.normalizer (principalUnipotent : Set SL3)) :
    ∃ s : ℝ, g.val = unipotentOne s * affineMatrix (positiveMatrixAffine g) := by
  obtain ⟨a, ha, s, b, hfactor⟩ := principalNormalizer_factor g.val hg
  have hentry : g.val.val 0 0 = a := by
    rw [hfactor]
    change (((unipotentOne s).val * (unipotentTwo b).val) * (diagonalFlow a ha).val) 0 0 = a
    simp [unipotentOne, unipotentTwo, diagonalFlow, Matrix.mul_apply, Fin.sum_univ_succ]
  have hap : 0 < a := hentry ▸ g.property
  have hc := affineMatrix_coordinates s b a hap
  change (unipotentOne s * unipotentTwo b * diagonalFlow a ha).val 0 0 = a ∧ _ at hc
  have hcoords : g.val.val 0 1 = s ∧ a * g.val.val 0 2 - s ^ 2 / 2 = b := by
    simpa only [← hfactor] using hc.2
  have hp : positiveMatrixAffine g = (⟨(a ^ 2, b), sq_pos_of_pos hap⟩ : PositiveAffine) := by
    apply AffineClassification.ext
    · change (g.val.val 0 0) ^ 2 = a ^ 2
      rw [hentry]
    · change g.val.val 0 0 * g.val.val 0 2 - (g.val.val 0 1) ^ 2 / 2 = b
      rw [hentry, hcoords.1]
      exact hcoords.2
  have hd : diagonalFlow (Real.sqrt (a ^ 2)) (ne_of_gt (Real.sqrt_pos.mpr (sq_pos_of_pos hap))) =
      diagonalFlow a ha := by
    apply Subtype.ext
    simp only [diagonalFlow, Real.sqrt_sq hap.le]
  refine ⟨s, ?_⟩
  rw [hp]
  change g.val = unipotentOne s * (unipotentTwo b * diagonalFlow (Real.sqrt (a ^ 2)) _)
  rw [hd, ← mul_assoc]
  exact hfactor

/-- The affine quotient of an actual closed matrix subgroup remains closed,
and matrix accumulation outside V₁ gives non-discreteness of that quotient. -/
theorem affine_comap_nondiscrete (K : Subgroup SL3) (hV : principalUnipotent ≤ K)
    (M : Set SL3) (hbase : (1 : SL3) ∈ closure M)
    (hM : ∀ g ∈ M, g ∈ K ∧ g ∈ Subgroup.normalizer (principalUnipotent : Set SL3) ∧
      g ∉ principalUnipotent) :
    (1 : PositiveAffine) ∈ closure ((K.comap affineMatrixHom : Set PositiveAffine) \ {1}) := by
  let e : positiveMatrixDomain := ⟨1, one_mem_positiveMatrixDomain⟩
  have he : e ∈ closure (Subtype.val ⁻¹' M) := by
    rw [← isOpen_positiveMatrixDomain.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val M]
    exact hbase
  have hi := mem_closure_image continuous_positiveMatrixAffine.continuousAt he
  have hsub : positiveMatrixAffine '' (Subtype.val ⁻¹' M) ⊆
      (K.comap affineMatrixHom : Set PositiveAffine) \ {1} := by
    rintro q ⟨g, hg, rfl⟩
    obtain ⟨hKg, hnorm, hout⟩ := hM g.val hg
    obtain ⟨s, hs⟩ := positiveNormalizer_factor g hnorm
    refine ⟨?_, ?_⟩
    · change affineMatrix (positiveMatrixAffine g) ∈ K
      have hh := K.mul_mem (K.inv_mem (hV (show unipotentOne s ∈ principalUnipotent from ⟨s, rfl⟩))) hKg
      rw [hs, inv_mul_cancel_left] at hh
      exact hh
    · intro hq
      have hq' : positiveMatrixAffine g = 1 := hq
      rw [hq', affineMatrix_one, mul_one] at hs
      exact hout ⟨s, hs⟩
  have hout := closure_mono hsub hi
  simpa only [e, positiveMatrixAffine_one] using hout

theorem closed_matrix_subgroup_affine_alternative (K : Subgroup SL3)
    (hK : IsClosed (K : Set SL3)) (hV : principalUnipotent ≤ K)
    (M : Set SL3) (hbase : (1 : SL3) ∈ closure M)
    (hM : ∀ g ∈ M, g ∈ K ∧ g ∈ Subgroup.normalizer (principalUnipotent : Set SL3) ∧
      g ∉ principalUnipotent) :
    (∀ b : ℝ, unipotentTwo b ∈ K) ∨
      ∃ r : ℝ, ∀ t : ℝ, ∀ ht : 0 < t,
        unipotentTwo r * diagonalFlow t (ne_of_gt ht) * (unipotentTwo r)⁻¹ ∈ K := by
  have hclosed : IsClosed (K.comap affineMatrixHom : Set PositiveAffine) :=
    hK.preimage continuous_affineMatrix
  rcases nondiscrete_closed_affine_subgroup (K.comap affineMatrixHom) hclosed
      (affine_comap_nondiscrete K hV M hbase hM) with htr | hd
  · exact Or.inl (fun b => by simpa only [Subgroup.mem_comap, affineMatrixHom,
      MonoidHom.coe_mk, OneHom.coe_mk, affineMatrix_translation] using htr b)
  · obtain ⟨r, hr⟩ := hd
    refine Or.inr ⟨r, fun t ht => ?_⟩
    have h := hr (t ^ 2) (sq_pos_of_pos ht)
    change affineMatrix (fixedDilation r (t ^ 2) (sq_pos_of_pos ht)) ∈ K at h
    rwa [affineMatrix_fixedDilation r t ht] at h

end
end JSP400
