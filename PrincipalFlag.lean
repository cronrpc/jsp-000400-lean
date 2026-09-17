import PrincipalFixed

namespace JSP400

open Matrix Set

def principalCoordinates (p : PrincipalSpace) : Fin 14 → ℝ :=
  ![p.1 0 2, p.1 0 1, p.2 2 2, p.2 1 1 - 2 * p.2 0 2,
    p.1 1 2 - p.1 0 1, p.1 0 0, p.1 1 1, p.1 1 0, p.1 2 1, p.1 2 0,
    p.2 1 2, p.2 1 1 + p.2 0 2, p.2 0 1, p.2 0 0]

theorem principalCoordinates_add (p q : PrincipalSpace) :
    principalCoordinates (p + q) = principalCoordinates p + principalCoordinates q := by
  ext i
  fin_cases i <;> simp [principalCoordinates] <;> ring

theorem principalCoordinates_sub (p q : PrincipalSpace) :
    principalCoordinates (p - q) = principalCoordinates p - principalCoordinates q := by
  ext i
  fin_cases i <;> simp [principalCoordinates] <;> ring

theorem principalCoordinates_smul (c : ℝ) (p : PrincipalSpace) :
    principalCoordinates (c • p) = c • principalCoordinates p := by
  ext i
  fin_cases i <;> simp [principalCoordinates] <;> ring

def principalFlag (k : ℕ) : Submodule ℝ PrincipalSpace where
  carrier := {p | p.1.trace = 0 ∧ p.2.IsSymm ∧
    ∀ j : Fin 14, k ≤ j.val → principalCoordinates p j = 0}
  zero_mem' := by
    refine ⟨by simp, by simp [Matrix.IsSymm], ?_⟩
    intro j hj
    fin_cases j <;> simp [principalCoordinates]
  add_mem' := by
    rintro p q ⟨hp, hps, hpc⟩ ⟨hq, hqs, hqc⟩
    refine ⟨by simp [Matrix.trace_add, hp, hq], hps.add hqs, ?_⟩
    intro j hj
    simp only [principalCoordinates_add, Pi.add_apply, hpc j hj, hqc j hj, add_zero]
  smul_mem' := by
    rintro c p ⟨hp, hps, hpc⟩
    refine ⟨by simp [Matrix.trace_smul, hp], hps.smul c, ?_⟩
    intro j hj
    simp only [principalCoordinates_smul, Pi.smul_apply, hpc j hj, smul_zero]

theorem mem_principalFlag (p : PrincipalSpace) (k : ℕ) :
    p ∈ principalFlag k ↔ p.1.trace = 0 ∧ p.2.IsSymm ∧
      ∀ j : Fin 14, k ≤ j.val → principalCoordinates p j = 0 := Iff.rfl

theorem principalFlag_mono {i j : ℕ} (hij : i ≤ j) : principalFlag i ≤ principalFlag j := by
  rintro p ⟨ht, hs, hc⟩
  exact ⟨ht, hs, fun k hk => hc k (hij.trans hk)⟩

theorem mem_principalFlag_fourteen (p : PrincipalSpace) :
    p ∈ principalFlag 14 ↔ p.1.trace = 0 ∧ p.2.IsSymm := by
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · exact fun h => ⟨h.1, h.2, fun j hj => by omega⟩

theorem principalAction_unipotentOne (p : PrincipalSpace) (t : ℝ) :
    principalAction (unipotentOne t) p =
      (shearConjugate p.1 t (t ^ 2 / 2), gramShear p.2 (-t)) := by
  apply Prod.ext
  · rw [unipotentOne_eq_shearElement]
    rfl
  · exact coadjointForm_unipotentOne t p.2

theorem principalCoordinates_from_blocks (p : PrincipalSpace) :
    principalCoordinates p =
      ![shearCoordinates p.1 0, shearCoordinates p.1 1,
        gramCoordinates p.2 0, gramCoordinates p.2 1,
        shearCoordinates p.1 2, shearCoordinates p.1 3, shearCoordinates p.1 4,
        shearCoordinates p.1 5, shearCoordinates p.1 6, shearCoordinates p.1 7,
        gramCoordinates p.2 2, gramCoordinates p.2 3,
        gramCoordinates p.2 4, gramCoordinates p.2 5] := rfl

set_option maxHeartbeats 1500000 in
theorem principalAction_sub_mem_previousFlag (k : Fin 14) (p : PrincipalSpace)
    (hp : p ∈ principalFlag (k.val + 1)) (t : ℝ) :
    principalAction (unipotentOne t) p - p ∈ principalFlag k.val := by
  rw [principalAction_unipotentOne]
  refine ⟨?_, (gramShear_isSymm p.2 hp.2.1 (-t)).sub hp.2.1, ?_⟩
  · change (shearConjugate p.1 t (t ^ 2 / 2) - p.1).trace = 0
    rw [Matrix.trace_sub, shearConjugate_trace, sub_self]
  · have h0 := hp.2.2 0
    have h1 := hp.2.2 1
    have h2 := hp.2.2 2
    have h3 := hp.2.2 3
    have h4 := hp.2.2 4
    have h5 := hp.2.2 5
    have h6 := hp.2.2 6
    have h7 := hp.2.2 7
    have h8 := hp.2.2 8
    have h9 := hp.2.2 9
    have h10 := hp.2.2 10
    have h11 := hp.2.2 11
    have h12 := hp.2.2 12
    have h13 := hp.2.2 13
    have h22 : p.1 2 2 = -p.1 0 0 - p.1 1 1 := by
      have ht := hp.1
      simp [Matrix.trace, Fin.sum_univ_succ] at ht
      linarith
    intro j hj
    rw [principalCoordinates_sub, principalCoordinates_from_blocks
      (shearConjugate p.1 t (t ^ 2 / 2), gramShear p.2 (-t))]
    simp only [shearConjugate_coordinates, gramShear_coordinates p.2 hp.2.1]
    fin_cases k <;> fin_cases j
    all_goals norm_num at hj
    all_goals simp_all [principalCoordinates, sub_eq_zero]

theorem mem_principalFlag_four (p : PrincipalSpace) :
    p ∈ principalFlag 4 ↔ p.1 ∈ shearLieAlgebra ∧ p.2 ∈ gramFlag 2 := by
  constructor
  · intro hp
    have hX : p.1 ∈ shearFlag 2 := by
      refine ⟨hp.1, ?_⟩
      intro j hj
      fin_cases j <;> norm_num at hj
      all_goals
        first
        | simpa [shearCoordinates, principalCoordinates] using hp.2.2 4 (by decide)
        | simpa [shearCoordinates, principalCoordinates] using hp.2.2 5 (by decide)
        | simpa [shearCoordinates, principalCoordinates] using hp.2.2 6 (by decide)
        | simpa [shearCoordinates, principalCoordinates] using hp.2.2 7 (by decide)
        | simpa [shearCoordinates, principalCoordinates] using hp.2.2 8 (by decide)
        | simpa [shearCoordinates, principalCoordinates] using hp.2.2 9 (by decide)
    refine ⟨(mem_shearFlag_two p.1).mp hX, hp.2.1, ?_⟩
    intro j hj
    fin_cases j <;> norm_num at hj
    all_goals
      first
      | simpa [gramCoordinates, principalCoordinates] using hp.2.2 10 (by decide)
      | simpa [gramCoordinates, principalCoordinates] using hp.2.2 11 (by decide)
      | simpa [gramCoordinates, principalCoordinates] using hp.2.2 12 (by decide)
      | simpa [gramCoordinates, principalCoordinates] using hp.2.2 13 (by decide)
  · rintro ⟨hx, hq⟩
    obtain ⟨a, b, hx⟩ := hx
    obtain ⟨c, d, hq⟩ := (mem_gramFlag_two p.2).mp hq
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]
      simp [Matrix.trace, Fin.sum_univ_succ]
    · rw [hq]
      apply Matrix.IsSymm.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro j hj
      fin_cases j <;> norm_num at hj
      all_goals simp [principalCoordinates, hx, hq, gramFixed]

theorem principalFlag_four_fixed (p : PrincipalSpace) (hp : p ∈ principalFlag 4) (t : ℝ) :
    principalAction (unipotentOne t) p = p := by
  have hh := (mem_principalFlag_four p).mp hp
  apply Prod.ext
  · exact (principal_adjoint_fixed_iff p.1 hp.1).mpr hh.1 t
  · change coadjointForm (unipotentOne t) p.2 = p.2
    rw [coadjointForm_unipotentOne]
    exact (gramShear_fixed_iff p.2 hh.2.1).mpr hh.2 (-t)

theorem principalFlag_invariant (k : Fin 14) (p : PrincipalSpace)
    (hp : p ∈ principalFlag (k.val + 1)) (t : ℝ) :
    principalAction (unipotentOne t) p ∈ principalFlag (k.val + 1) := by
  have hd := principalFlag_mono (Nat.le_succ k.val) (principalAction_sub_mem_previousFlag k p hp t)
  simpa only [sub_add_cancel] using (principalFlag (k.val + 1)).add_mem hd hp

theorem principalFlag_step_coordinate (k : Fin 14) (p : PrincipalSpace)
    (hp : p ∈ principalFlag (k.val + 1)) :
    p ∈ principalFlag k.val ↔ principalCoordinates p k = 0 := by
  constructor
  · exact fun h => h.2.2 k le_rfl
  · intro hk
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro j hj
    by_cases h : k = j
    · simpa [← h] using hk
    · exact hp.2.2 j (by have hval : k.val ≠ j.val := fun heq => h (Fin.ext heq); omega)

theorem principalFlag_step_coordinate_invariant (k : Fin 14) (p : PrincipalSpace)
    (hp : p ∈ principalFlag (k.val + 1)) (t : ℝ) :
    principalCoordinates (principalAction (unipotentOne t) p) k = principalCoordinates p k := by
  have hd := (principalAction_sub_mem_previousFlag k p hp t).2.2 k le_rfl
  rw [principalCoordinates_sub] at hd
  exact sub_eq_zero.mp hd

theorem continuous_principalCoordinate (j : Fin 14) :
    Continuous (fun p : PrincipalSpace => principalCoordinates p j) := by
  fin_cases j <;> simp only [principalCoordinates] <;> fun_prop

theorem isClosed_principalFlag (k : ℕ) : IsClosed (principalFlag k : Set PrincipalSpace) := by
  have heq : (principalFlag k : Set PrincipalSpace) =
      {p | p.1.trace = 0} ∩ {p | p.2.transpose = p.2} ∩
        ⋂ j : Fin 14, ⋂ (_h : k ≤ j.val), {p | principalCoordinates p j = 0} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    exact and_assoc.symm
  rw [heq]
  refine ((isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq (by fun_prop) (by fun_prop))).inter ?_
  exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
    isClosed_eq (continuous_principalCoordinate j) continuous_const))

end JSP400

#print axioms JSP400.principalAction_sub_mem_previousFlag
