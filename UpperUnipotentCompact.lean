import DiagonalContraction
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace JSP400

theorem upperUnipotent_mul (a b c x y z : ℝ) :
    upperUnipotent a b c * upperUnipotent x y z =
      upperUnipotent (a + x) (b + y + a * z) (c + z) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change ((upperUnipotent a b c).val * (upperUnipotent x y z).val) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Exact powers, with subtraction performed in ℝ. -/
theorem upperUnipotent_pow (a b c : ℝ) (n : ℕ) :
    upperUnipotent a b c ^ n =
      upperUnipotent (n * a) (n * b + (n : ℝ) * ((n : ℝ) - 1) / 2 * a * c)
        (n * c) := by
  induction n with
  | zero => simp [upperUnipotent_zero]
  | succ n ih =>
    rw [pow_succ, ih, upperUnipotent_mul]
    push_cast
    congr 1 <;> ring

private theorem unbounded_linear_entry {U : Subgroup SL3}
    (hU : IsCompact (U : Set SL3)) (g : SL3) (hg : g ∈ U)
    (i j : Fin 3) (a : ℝ) (ha : a ≠ 0)
    (hpow : ∀ n : ℕ, (g ^ n).val i j = (n : ℝ) * a) : False := by
  have hf : Continuous (fun g : SL3 => |g.val i j|) :=
    ((continuous_apply j).comp
      (Matrix.SpecialLinearGroup.continuous_apply id continuous_id i)).abs
  obtain ⟨M, hM⟩ := hU.bddAbove_image hf.continuousOn
  obtain ⟨n, hn⟩ := exists_nat_gt (M / |a|)
  have hpos := abs_pos.mpr ha
  have hgt : M < (n : ℝ) * |a| := (div_lt_iff₀ hpos).mp hn
  have hle := hM (Set.mem_image_of_mem _ (U.pow_mem hg n))
  rw [hpow, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at hle
  linarith

/-- Upper unitriangular real matrices contain no nontrivial compact subgroup. -/
theorem upper_subgroup_not_isCompact (U : Subgroup SL3)
    (hupper : ∀ g ∈ U, ∃ a b c : ℝ, g = upperUnipotent a b c)
    (hne : U ≠ ⊥) : ¬ IsCompact (U : Set SL3) := by
  intro hcompact
  obtain ⟨g, hg, hgn⟩ : ∃ g ∈ U, g ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    ext g
    simp only [Subgroup.mem_bot]
    exact ⟨h g, fun heq => heq ▸ U.one_mem⟩
  obtain ⟨a, b, c, rfl⟩ := hupper g hg
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · have hb : b ≠ 0 := by
        intro hb
        exact hgn (by simpa [ha, hb, hc] using upperUnipotent_zero)
      exact unbounded_linear_entry hcompact _ hg 0 2 b hb (fun n => by
        rw [upperUnipotent_pow]
        simp [upperUnipotent, ha, hc])
    · exact unbounded_linear_entry hcompact _ hg 1 2 c hc (fun n => by
        rw [upperUnipotent_pow]
        simp [upperUnipotent])
  · exact unbounded_linear_entry hcompact _ hg 0 1 a ha (fun n => by
      rw [upperUnipotent_pow]
      simp [upperUnipotent])

/-- The intersection statement used for any subgroup of W in Margulis Lemma 9. -/
theorem upper_subgroup_stabilizer_inf_eq_bot (y : LatticeSpace)
    (hc : IsCompact (closure (diagonalOrbit y))) (U : Subgroup SL3)
    (hupper : ∀ g ∈ U, ∃ a b c : ℝ, g = upperUnipotent a b c) :
    U ⊓ MulAction.stabilizer SL3 y = ⊥ := by
  ext g
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  constructor
  · rintro ⟨hg, hgy⟩
    obtain ⟨a, b, c, rfl⟩ := hupper g hg
    exact upper_stabilizer_trivial_of_compact_diagonal_orbit y hc a b c hgy
  · rintro rfl
    exact ⟨U.one_mem, one_smul _ _⟩

/-- The full quotient noncompactness conclusion in Margulis Lemma 9, for the
actual subgroup quotient with its quotient topology. -/
theorem upper_stabilizer_quotient_not_compact (y : LatticeSpace)
    (hc : IsCompact (closure (diagonalOrbit y))) (U : Subgroup SL3)
    (hupper : ∀ g ∈ U, ∃ a b c : ℝ, g = upperUnipotent a b c)
    (hne : U ≠ ⊥) :
    ¬ CompactSpace (U ⧸ (MulAction.stabilizer SL3 y).comap U.subtype) := by
  have hbot : (MulAction.stabilizer SL3 y).comap U.subtype = ⊥ := by
    ext u
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    constructor
    · intro hu
      apply Subtype.ext
      change u.val • y = y at hu
      change u.val = 1
      obtain ⟨a, b, c, h⟩ := hupper u.val u.property
      rw [h] at hu ⊢
      exact upper_stabilizer_trivial_of_compact_diagonal_orbit y hc a b c hu
    · rintro rfl
      exact one_smul _ _
  rw [hbot]
  intro hcompact
  have : CompactSpace (U ⧸ (⊥ : Subgroup U)) := hcompact
  have hcont : Continuous (QuotientGroup.quotientBot : U ⧸ (⊥ : Subgroup U) → U) := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    exact continuous_id
  have hU : IsCompact (Set.univ : Set U) := by
    have h := isCompact_univ.image hcont
    simpa only [Set.image_univ, QuotientGroup.quotientBot.surjective.range_eq] using h
  have hUS : IsCompact (U : Set SL3) := by
    have h := hU.image continuous_subtype_val
    have hrange : Subtype.val '' (Set.univ : Set U) = (U : Set SL3) := by
      ext g
      simp
    rwa [hrange] at h
  exact upper_subgroup_not_isCompact U hupper hne hUS

end JSP400
