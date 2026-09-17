import ShearOrbit

namespace JSP400

open Matrix Set

private theorem upperTriangular_mul_diag
    (A B : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin 3) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

private theorem upperTriangular_pow_diag
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsUpperTriangular) (n : ℕ) (i : Fin 3) :
    (A ^ n) i i = A i i ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, upperTriangular_mul_diag _ _ (hA.pow n) hA, ih, pow_succ]

theorem nilpotent_upperTriangular_diag_eq_zero
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x.IsUpperTriangular)
    (hnil : IsNilpotent x) (i : Fin 3) : x i i = 0 := by
  obtain ⟨n, hn⟩ := hnil
  have hp := upperTriangular_pow_diag x hx n i
  rw [hn] at hp
  exact eq_zero_of_pow_eq_zero hp.symm

theorem upper_shear_entry02
    (x : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : x 0 0 = 0) (h11 : x 1 1 = 0)
    (h10 : x 1 0 = 0) (s : ℝ) :
    shearConjugate x s 0 0 2 = x 0 2 + s * (x 1 2 - x 0 1) := by
  rw [shearConjugate, shearElement_inv]
  simp [shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
    h00, h11, h10]
  ring

set_option maxHeartbeats 200000 in
theorem upper_shearOrbitSlice_component_not_isCompact
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1)
    (h00 : x 0 0 = 0) (h11 : x 1 1 = 0)
    (h10 : x 1 0 = 0) (h20 : x 2 0 = 0) (h21 : x 2 1 = 0)
    (h12 : x 1 2 ≠ 1) :
    ¬ IsCompact (connectedComponentIn (shearOrbitSlice x) x) := by
  let f : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => shearConjugate x s 0
  have hpair : Continuous (fun s : ℝ => (s, (0 : ℝ))) :=
    continuous_id.prodMk continuous_const
  have hf : Continuous f := by
    simpa only [Function.comp_def] using (continuous_shearConjugate x).comp hpair
  have hpre : IsPreconnected (Set.range f) := isPreconnected_range hf
  have hbase : x ∈ Set.range f := ⟨0, shearConjugate_zero x⟩
  have hsub : Set.range f ⊆ shearOrbitSlice x := by
    rintro y ⟨s, rfl⟩
    refine ⟨⟨(s, 0), rfl⟩, ?_⟩
    change shearConjugate x s 0 0 1 = 1
    rw [shearConjugate_entry01]
    simp only [hx, h10, h20, h21, h00, h11]
    ring
  have hcomp := hpre.subset_connectedComponentIn hbase hsub
  intro hc
  have hcoord : Continuous (fun y : Matrix (Fin 3) (Fin 3) ℝ => y 0 2) := by fun_prop
  obtain ⟨M, hM⟩ := hc.bddAbove_image hcoord.continuousOn
  let s := (M + 1 - x 0 2) / (x 1 2 - 1)
  have hb := hM ⟨f s, hcomp ⟨s, rfl⟩, rfl⟩
  change shearConjugate x s 0 0 2 ≤ M at hb
  rw [upper_shear_entry02 x h00 h11 h10, hx] at hb
  have hs : s * (x 1 2 - 1) = M + 1 - x 0 2 := by
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr h12)
  rw [hs] at hb
  linarith

/-- The Lie algebra of the two-parameter upper unipotent group, given by its
ordinary matrix entries. -/
def shearLieAlgebra : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {x | ∃ a b : ℝ, x = !![0, a, b; 0, 0, a; 0, 0, 0]}

/-- The complete assertion (C) in Margulis's proof of Lemma 6, §8:
for a nilpotent matrix in the entry-`01` hyperplane outside the unipotent
Lie algebra, the component of its orbit-hyperplane intersection is noncompact.
The non-upper and upper cases are both proved by explicit coordinates. -/
theorem margulis_lemma6_C
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1)
    (hnil : IsNilpotent x) (hnot : x ∉ shearLieAlgebra) :
    ¬ IsCompact (connectedComponentIn (shearOrbitSlice x) x) := by
  by_cases h10 : x 1 0 = 0
  · by_cases h20 : x 2 0 = 0
    · by_cases h21 : x 2 1 = 0
      · have hupper : x.IsUpperTriangular := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all
        have hd := nilpotent_upperTriangular_diag_eq_zero x hupper hnil
        have h12 : x 1 2 ≠ 1 := by
          intro h
          apply hnot
          refine ⟨1, x 0 2, ?_⟩
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, hx, h, hd]
        exact upper_shearOrbitSlice_component_not_isCompact x hx
          (hd 0) (hd 1) h10 h20 h21 h12
      · exact shearOrbitSlice_component_not_isCompact x hx (Or.inr (Or.inl h21))
    · exact shearOrbitSlice_component_not_isCompact x hx (Or.inl h20)
  · exact shearOrbitSlice_component_not_isCompact x hx (Or.inr (Or.inr h10))

end JSP400

#print axioms JSP400.margulis_lemma6_C
