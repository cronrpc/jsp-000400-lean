import CollisionInvariant
import DiagonalInvariance

namespace JSP400

open Set

theorem principalUnipotent_isClosed : IsClosed (principalUnipotent : Set SL3) := by
  have he : (principalUnipotent : Set SL3) = {g | principalOrbitMap g = principalBase} := by
    ext g
    exact (principalOrbitMap_eq_base_iff g).symm
  rw [he]
  exact isClosed_eq continuous_principalOrbitMap continuous_const

theorem principalUnipotent_ne_bot : principalUnipotent ≠ ⊥ := by
  intro he
  have hm : unipotentOne 1 ∈ principalUnipotent := ⟨1, rfl⟩
  rw [he, Subgroup.mem_bot] at hm
  have hv := congrArg (fun g : SL3 => g.val 0 1) hm
  norm_num [unipotentOne] at hv

theorem principalUnipotent_upper (g : SL3) (hg : g ∈ principalUnipotent) :
    ∃ a b c : ℝ, g = upperUnipotent a b c := by
  obtain ⟨t, rfl⟩ := hg
  exact ⟨t, t ^ 2 / 2, t, rfl⟩

/-- The collision supplied by Lemma 4, rather than a new dynamical assumption,
makes each compact V₁-minimal subsystem of a compact H-invariant set D-invariant. -/
theorem compact_principal_minimal_diagonal_invariant {Y K : Set LatticeSpace}
    (hYc : IsCompact Y) (hYclosed : IsClosed Y) (hYn : Y.Nonempty)
    (hV : subgroupInvariant principalUnipotent Y)
    (hmin : ∀ y ∈ Y, closure (MulAction.orbit principalUnipotent y) = Y)
    (hYK : Y ⊆ K) (hK : IsCompact K) (hKclosed : IsClosed K)
    (hH : subgroupInvariant (formStabilizer standardForm) K) :
    ∀ t : ℝ, ∀ ht : 0 < t, ∀ y ∈ Y, diagonalFlow t (ne_of_gt ht) • y ∈ Y := by
  obtain ⟨y, hy⟩ := hYn
  have hD : IsCompact (closure (diagonalOrbit y)) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hKclosed
    rintro _ ⟨t, rfl⟩
    exact hH _ (diagonalFlow_mem_standardStabilizer _ _) y (hYK hy)
  have hnq := upper_stabilizer_quotient_not_compact y hD principalUnipotent
    principalUnipotent_upper principalUnipotent_ne_bot
  let M : Set SL3 := {g | g ∉ principalUnipotent ∧ g • y ∈ MulAction.orbit principalUnipotent y}
  have hbase : (1 : SL3) ∈ closure M := by
    apply margulis_lemma4 principalUnipotent principalUnipotent_isClosed y
      (hmin y hy ▸ hYc) _ hnq
    rw [hmin y hy]
    exact hmin
  have hM : M ⊆ hittingSet Y Y := by
    intro g hg
    refine ⟨y, hy, ?_⟩
    rw [← hmin y hy]
    exact subset_closure hg.2
  exact diagonal_invariant_of_subgroup_alternative (principalEnlargementGroup M)
    ⟨y, hy⟩ hYK (principalEnlargementGroup_invariant M hYc hYclosed hV hM hmin)
    hK hKclosed hH (margulis_lemma5_II_alternative M hbase (fun _ h => h.1))

/-- Margulis Theorem 2 on the actual space SL(3,ℝ)/SL(3,ℤ):
compactness of the genuine stabilizer quotient. All minimal-subsystem and
diagonal-invariance premises have been discharged. -/
theorem margulis_theorem2_quotient (z : LatticeSpace)
    (hc : IsCompact (closure (MulAction.orbit (formStabilizer standardForm) z))) :
    CompactSpace ((formStabilizer standardForm) ⧸
      MulAction.stabilizer (formStabilizer standardForm) z) := by
  let H := formStabilizer standardForm
  obtain ⟨X, hXK, hXc, hXclosed, hXn, hHX, hXmin⟩ :=
    exists_minimal_subsystem_of_compact_orbit_closure H z hc
  obtain ⟨Y, hYX, hYc, hYclosed, hYn, hV, hYmin⟩ :=
    exists_compact_minimal_subgroup principalUnipotent hXc hXclosed hXn
      (fun g hg => hHX g (principalUnipotent_le_standardStabilizer hg))
  have hD := compact_principal_minimal_diagonal_invariant hYc hYclosed hYn hV hYmin
    (hYX.trans hXK) hc isClosed_closure (subgroupInvariant_orbit_closure H z)
  exact compact_H_stabilizer_quotient_of_diagonal_minimal z hc hXK hXc hXmin
    hYX hYc hYn hV hD hYmin

/-- The compact-orbit consequence stated after Margulis Theorem 2. -/
theorem margulis_theorem2 (z : LatticeSpace)
    (hc : IsCompact (closure (MulAction.orbit (formStabilizer standardForm) z))) :
    IsCompact (MulAction.orbit (formStabilizer standardForm) z) := by
  let := margulis_theorem2_quotient z hc
  exact isCompact_orbit_of_compact_stabilizer_quotient (formStabilizer standardForm) z

end JSP400

#print axioms JSP400.margulis_theorem2_quotient
#print axioms JSP400.margulis_theorem2

