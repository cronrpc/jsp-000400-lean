import UpperGeneration
import ShearCentralizer

/-! A direct proof that DW-orbits of unimodular lattices are not relatively
compact. Only this consequence of Margulis Lemma 8 is needed here; the stronger
orbit-density assertion is not assumed or claimed. -/

namespace JSP400

open Matrix Set
open scoped Matrix.Norms.Elementwise

theorem lattice_has_nonzero_last_coordinate (L : LatticeSpace) :
    ∃ v ∈ quotientLatticePoints L, v 2 ≠ 0 := by
  induction L using Quotient.inductionOn with
  | h g =>
    have hrow : ∃ j : Fin 3, g.val 2 j ≠ 0 := by
      by_contra hn
      push Not at hn
      have hd := g.property
      change g.val.det = 1 at hd
      rw [Matrix.det_fin_three, hn 0, hn 1, hn 2] at hd
      norm_num at hd
    obtain ⟨j, hj⟩ := hrow
    refine ⟨g • integerVector (Pi.single j 1), ⟨Pi.single j 1, rfl⟩, ?_⟩
    simpa [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec,
      integerVector, Matrix.mulVec, dotProduct, Pi.single_apply] using hj

theorem upper_eliminate_first_coordinates (v : Vector3) (hv : v 2 ≠ 0) :
    upperUnipotent 0 (-v 0 / v 2) (-v 1 / v 2) • v = ![0, 0, v 2] := by
  change (upperUnipotent 0 (-v 0 / v 2) (-v 1 / v 2)).val.mulVec v = _
  ext i
  fin_cases i <;>
    simp [upperUnipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals field_simp [hv]
  all_goals ring

/-- A positive diagonal element contracts a vector whose first two coordinates
have been eliminated. -/
theorem diagonal_after_elimination_makes_vector_short (v : Vector3) (hv : v 2 ≠ 0)
    (w : SL3) (hw : w • v = ![0, 0, v 2])
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, ∃ ht : 0 < t,
      ‖(diagonalFlow t (ne_of_gt ht) * w) • v‖ < ε ∧
      (diagonalFlow t (ne_of_gt ht) * w) • v ≠ 0 := by
  let t := 2 * |v 2| / ε
  have ht : 0 < t := div_pos (mul_pos (by norm_num) (abs_pos.mpr hv)) hε
  have he : (diagonalFlow t (ne_of_gt ht) * w) • v = ![0, 0, t⁻¹ * v 2] := by
    rw [mul_smul]
    rw [hw]
    change (diagonalFlow t (ne_of_gt ht)).val.mulVec ![0, 0, v 2] = _
    ext i
    fin_cases i <;>
      simp [diagonalFlow, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have habs : |t⁻¹ * v 2| = ε / 2 := by
    rw [abs_mul, abs_inv, abs_of_pos ht]
    dsimp [t]
    field_simp
  refine ⟨t, ht, ?_, ?_⟩
  · rw [he, pi_norm_lt_iff hε]
    intro i
    fin_cases i
    · simpa using hε
    · simpa using hε
    · change |t⁻¹ * v 2| < ε
      rw [habs]
      linarith
  · rw [he]
    intro hz
    have hz2 := congrFun hz (2 : Fin 3)
    have hne := mul_ne_zero (inv_ne_zero (ne_of_gt ht)) hv
    exact hne hz2

/-- Any vector with nonzero last coordinate can be made arbitrarily short by
an actual positive diagonal element times an upper-unitriangular element. -/
theorem diagonal_upper_makes_vector_short (v : Vector3) (hv : v 2 ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, ∃ ht : 0 < t, ∃ w ∈ upperGroup,
      ‖(diagonalFlow t (ne_of_gt ht) * w) • v‖ < ε ∧
      (diagonalFlow t (ne_of_gt ht) * w) • v ≠ 0 := by
  obtain ⟨t, ht, hs, hn⟩ := diagonal_after_elimination_makes_vector_short v hv
    (upperUnipotent 0 (-v 0 / v 2) (-v 1 / v 2))
    (upper_eliminate_first_coordinates v hv) ε hε
  exact ⟨t, ht, _, ⟨0, _, _, rfl⟩, hs, hn⟩

def diagonalUpperOrbit (L : LatticeSpace) : Set LatticeSpace :=
  {M | ∃ t : ℝ, ∃ ht : 0 < t, ∃ w ∈ upperGroup,
    M = (diagonalFlow t (ne_of_gt ht) * w) • L}

/-- The non-relative-compactness consequence of Margulis Lemma 8, proved
directly using explicit lattice vectors and the compact-family lower bound. -/
theorem diagonalUpperOrbit_not_relatively_compact (L : LatticeSpace) :
    ¬IsCompact (closure (diagonalUpperOrbit L)) := by
  intro hc
  obtain ⟨ε, hε, hbound⟩ := compact_lattices_lower_bound hc
  obtain ⟨v, hvL, hv⟩ := lattice_has_nonzero_last_coordinate L
  obtain ⟨t, ht, w, hw, hshort, hnz⟩ := diagonal_upper_makes_vector_short v hv ε hε
  have hpoint : (diagonalFlow t (ne_of_gt ht) * w) • v ∈
      quotientLatticePoints ((diagonalFlow t (ne_of_gt ht) * w) • L) := by
    rw [quotientLatticePoints_smul]
    exact ⟨v, hvL, rfl⟩
  have hM : (diagonalFlow t (ne_of_gt ht) * w) • L ∈ closure (diagonalUpperOrbit L) :=
    subset_closure ⟨t, ht, w, hw, rfl⟩
  exact (not_lt_of_ge (hbound _ hM _ hpoint hnz)) hshort

/-- The smaller two-dimensional group V already eliminates both coordinates. -/
theorem shear_eliminate_first_coordinates (v : Vector3) (hv : v 2 ≠ 0) :
    shearElement (-v 1 / v 2) ((v 1 / v 2) ^ 2 - v 0 / v 2) • v =
      ![0, 0, v 2] := by
  change (shearElement (-v 1 / v 2) ((v 1 / v 2) ^ 2 - v 0 / v 2)).val.mulVec v = _
  ext i
  fin_cases i <;>
    simp [shearElement, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals field_simp [hv]
  all_goals ring

def diagonalShearOrbit (L : LatticeSpace) : Set LatticeSpace :=
  {M | ∃ t : ℝ, ∃ ht : 0 < t, ∃ w ∈ shearGroup,
    M = (diagonalFlow t (ne_of_gt ht) * w) • L}

/-- Margulis Lemma 10 for the actual lattice space SL₃(ℝ)/SL₃(ℤ), using
explicit short vectors. It holds for every lattice, without an orbit-density
or non-unimodular-group premise. -/
theorem margulis_lemma10 (L : LatticeSpace) :
    ¬IsCompact (closure (diagonalShearOrbit L)) := by
  intro hc
  obtain ⟨ε, hε, hbound⟩ := compact_lattices_lower_bound hc
  obtain ⟨v, hvL, hv⟩ := lattice_has_nonzero_last_coordinate L
  let w := shearElement (-v 1 / v 2) ((v 1 / v 2) ^ 2 - v 0 / v 2)
  have hw : w ∈ shearGroup := ⟨_, _, rfl⟩
  obtain ⟨t, ht, hshort, hnz⟩ := diagonal_after_elimination_makes_vector_short v hv w
    (shear_eliminate_first_coordinates v hv) ε hε
  have hpoint : (diagonalFlow t (ne_of_gt ht) * w) • v ∈
      quotientLatticePoints ((diagonalFlow t (ne_of_gt ht) * w) • L) := by
    rw [quotientLatticePoints_smul]
    exact ⟨v, hvL, rfl⟩
  have hM : (diagonalFlow t (ne_of_gt ht) * w) • L ∈ closure (diagonalShearOrbit L) :=
    subset_closure ⟨t, ht, w, hw, rfl⟩
  exact (not_lt_of_ge (hbound _ hM _ hpoint hnz)) hshort

end JSP400
