import PrincipalRepresentation

namespace JSP400

open Matrix Set

theorem unipotentOne_matrix_polynomial (t : ℝ) :
    (unipotentOne t).val = 1 + t • shearFixedLine 0 +
      (t ^ 2 / 2) • shearFixedLine 0 ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unipotentOne, shearFixedLine, pow_two]

theorem adjointAction_add (g : SL3) (x y : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction g (x + y) = adjointAction g x + adjointAction g y := by
  simp [adjointAction, mul_add, add_mul]

theorem adjointAction_smul (g : SL3) (c : ℝ) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    adjointAction g (c • x) = c • adjointAction g x := by
  simp [adjointAction]

theorem adjointAction_matrix_one (g : SL3) :
    adjointAction g 1 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  change g.val * 1 * g⁻¹.val = _
  rw [mul_one]
  exact congrArg Subtype.val (mul_inv_cancel g)

theorem conjugate_unipotentOne_of_adjoint_base (g : SL3) (a : ℝ)
    (hg : adjointAction g (shearFixedLine 0) = a • shearFixedLine 0) (t : ℝ) :
    g * unipotentOne t * g⁻¹ = unipotentOne (a * t) := by
  apply Subtype.ext
  change adjointAction g (unipotentOne t).val = (unipotentOne (a * t)).val
  rw [unipotentOne_matrix_polynomial, adjointAction_add, adjointAction_add,
    adjointAction_matrix_one, adjointAction_smul, adjointAction_smul,
    ← adjointAction_pow, hg, unipotentOne_matrix_polynomial]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shearFixedLine, pow_two] <;> ring

theorem mem_principalNormalizer_of_adjoint_base (g : SL3) (a : ℝ) (ha : a ≠ 0)
    (hg : adjointAction g (shearFixedLine 0) = a • shearFixedLine 0) :
    g ∈ Subgroup.normalizer (principalUnipotent : Set SL3) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  change u ∈ principalUnipotent ↔ g * u * g⁻¹ ∈ principalUnipotent
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a * t, conjugate_unipotentOne_of_adjoint_base g a hg t⟩
  · rintro ⟨t, ht⟩
    have he : g * u * g⁻¹ = g * unipotentOne (t / a) * g⁻¹ := by
      rw [ht, conjugate_unipotentOne_of_adjoint_base g a hg]
      congr 1
      field_simp
    exact ⟨t / a, mul_left_cancel (mul_right_cancel he)⟩

theorem principal_adjoint_fixed_iff (x : Matrix (Fin 3) (Fin 3) ℝ) (htrace : x.trace = 0) :
    (∀ t : ℝ, adjointAction (unipotentOne t) x = x) ↔ x ∈ shearLieAlgebra := by
  constructor
  · intro hx
    have h1 := (adjointAction_eq_self_iff_commute (unipotentOne 1) x).mp (hx 1)
    have hm := (adjointAction_eq_self_iff_commute (unipotentOne (-1)) x).mp (hx (-1))
    change Commute (unipotentOne 1).val x at h1
    change Commute (unipotentOne (-1)).val x at hm
    have he : (unipotentOne 1).val - (unipotentOne (-1)).val = (2 : ℝ) • shearFixedLine 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [unipotentOne, shearFixedLine]
    have hcomm := h1.sub_left hm
    rw [he] at hcomm
    have hn := (Commute.smul_left_iff₀ (by norm_num : (2 : ℝ) ≠ 0)).mp hcomm
    have hentry (i j : Fin 3) := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A i j) hn.eq
    have h00 := hentry 0 0
    have h01 := hentry 0 1
    have h02 := hentry 0 2
    have h11 := hentry 1 1
    have h12 := hentry 1 2
    have h10 := hentry 1 0
    simp [shearFixedLine, Matrix.mul_apply, Fin.sum_univ_succ] at h00 h01 h02 h11 h12 h10
    have ht := htrace
    simp [Matrix.trace, Fin.sum_univ_succ] at ht
    have hd0 : x 0 0 = 0 := by linarith
    have hd1 : x 1 1 = 0 := by linarith
    have hd2 : x 2 2 = 0 := by linarith
    refine ⟨x 0 1, x 0 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · intro hx t
    rw [unipotentOne_eq_shearElement]
    exact (shear_fixed_iff_mem_lieAlgebra x htrace).mpr hx t (t ^ 2 / 2)

theorem gramShear_fixed_iff (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q.IsSymm) :
    (∀ t : ℝ, gramShear q t = q) ↔ q ∈ gramFlag 2 := by
  constructor
  · intro h
    have hc := congrArg gramCoordinates (h 1)
    rw [gramShear_coordinates q hq] at hc
    have h4 := congrFun hc 4
    have h3 := congrFun hc 3
    have h2 := congrFun hc 2
    have h0 := congrFun hc 0
    simp [gramCoordinates] at h4 h3 h2 h0
    refine ⟨hq, ?_⟩
    intro j hj
    fin_cases j <;> norm_num at hj
    all_goals simp [gramCoordinates]
    all_goals linarith
  · intro hq t
    obtain ⟨a, b, rfl⟩ := (mem_gramFlag_two q).mp hq
    exact gramShear_gramFixed a b t

theorem coadjointForm_unipotentOne (t : ℝ) (q : Matrix (Fin 3) (Fin 3) ℝ) :
    coadjointForm (unipotentOne t) q = gramShear q (-t) := by
  unfold coadjointForm gramShear
  rw [unipotentOne_inv]

/-- A fixed point of the concrete principal representation in the actual
SL₃ orbit comes from the true normalizer of V₁. -/
theorem mem_principalNormalizer_of_fixed_orbit (g : SL3)
    (hg : ∀ t : ℝ, principalAction (unipotentOne t) (principalOrbitMap g) = principalOrbitMap g) :
    g ∈ Subgroup.normalizer (principalUnipotent : Set SL3) := by
  have htrace : (principalOrbitMap g).1.trace = 0 :=
    nilpotent_matrix_trace_zero (adjointAction_isNilpotent g (shearFixedLine_isNilpotent 0))
  have hx : (principalOrbitMap g).1 ∈ shearLieAlgebra :=
    (principal_adjoint_fixed_iff _ htrace).mp (fun t => congrArg Prod.fst (hg t))
  have hq : (principalOrbitMap g).2 ∈ gramFlag 2 := by
    apply (gramShear_fixed_iff _ (gramMatrix_isSymm g⁻¹)).mp
    intro t
    have he := congrArg Prod.snd (hg (-t))
    change coadjointForm (unipotentOne (-t)) (principalOrbitMap g).2 = _ at he
    simpa only [coadjointForm_unipotentOne, neg_neg, principalOrbitMap_eq, Prod.snd] using he
  obtain ⟨a, b, hx⟩ := hx
  obtain ⟨c, hq⟩ := gramFixed_of_det_one _ hq (gramMatrix_det g⁻¹)
  have hskew := principalOrbitMap_skew g
  rw [hx, hq] at hskew
  have hb := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 2 2) hskew
  simp [gramFixed, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] at hb
  have hb0 : b = 0 := by linarith
  have hscaled : adjointAction g (shearFixedLine 0) = a • shearFixedLine 0 := by
    change (principalOrbitMap g).1 = _
    rw [hx, hb0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shearFixedLine]
  have ha : a ≠ 0 := by
    intro haz
    have he : adjointAction g (shearFixedLine 0) = adjointAction g 0 := by
      rw [hscaled, haz]
      simp [adjointAction]
    have hN := adjointAction_injective g he
    have h01 := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A 0 1) hN
    norm_num [shearFixedLine] at h01
  exact mem_principalNormalizer_of_adjoint_base g a ha hscaled

end JSP400

#print axioms JSP400.mem_principalNormalizer_of_fixed_orbit
