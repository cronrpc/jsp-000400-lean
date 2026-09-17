import Shearing
import Mathlib.Topology.Instances.Matrix

namespace JSP400

open Matrix Set

private theorem shearConjugate_entry00 (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearConjugate x s t 0 0 = x 0 0 + s * x 1 0 + t * x 2 0 := by
  rw [shearConjugate, shearElement_inv]
  simp [shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

private theorem shearConjugate_entry21 (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearConjugate x s t 2 1 = x 2 1 - s * x 2 0 := by
  rw [shearConjugate, shearElement_inv]
  simp [shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

private theorem shearConjugate_entry22 (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearConjugate x s t 2 2 = x 2 2 - s * x 2 1 + (s ^ 2 - t) * x 2 0 := by
  rw [shearConjugate, shearElement_inv]
  simp [shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

private theorem shearConjugate_entry12 (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearConjugate x s t 1 2 = x 1 2 + s * (x 2 2 - x 1 1) - s ^ 2 * x 2 1 +
      (s ^ 2 - t) * x 1 0 + s * (s ^ 2 - t) * x 2 0 := by
  rw [shearConjugate, shearElement_inv]
  simp [shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem continuous_shearConjugate (x : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (fun p : ℝ × ℝ => shearConjugate x p.1 p.2) := by
  simp_rw [shearConjugate, shearElement_inv]
  change Continuous (fun p : ℝ × ℝ =>
    (!![1, p.1, p.2; 0, 1, p.1; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℝ) * x *
      !![1, -p.1, p.1 ^ 2 - p.2; 0, 1, -p.1; 0, 0, 1])
  fun_prop

/-- When `x` is not upper triangular, its unipotent conjugacy orbit admits
a continuous coordinate inverse defined on the entire matrix space.
The three cases use the first nonzero strictly lower triangular entry. -/
theorem shearConjugate_has_continuous_leftInverse
    (x : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : x 2 0 ≠ 0 ∨ x 2 1 ≠ 0 ∨ x 1 0 ≠ 0) :
    ∃ R : Matrix (Fin 3) (Fin 3) ℝ → ℝ × ℝ,
      Continuous R ∧ Function.LeftInverse R (fun p : ℝ × ℝ => shearConjugate x p.1 p.2) := by
  by_cases h20 : x 2 0 = 0
  · by_cases h21 : x 2 1 = 0
    · have h10 : x 1 0 ≠ 0 := hx.resolve_left (not_not.mpr h20) |>.resolve_left (not_not.mpr h21)
      let R : Matrix (Fin 3) (Fin 3) ℝ → ℝ × ℝ := fun y =>
        let s := (y 0 0 - x 0 0) / x 1 0
        (s, s ^ 2 - (y 1 2 - x 1 2 - s * (x 2 2 - x 1 1)) / x 1 0)
      refine ⟨R, by dsimp [R]; fun_prop, ?_⟩
      rintro ⟨s,t⟩
      dsimp [R]
      rw [shearConjugate_entry00, shearConjugate_entry12, h20, h21]
      ext <;> field_simp <;> ring
    · let R : Matrix (Fin 3) (Fin 3) ℝ → ℝ × ℝ := fun y =>
        let s := (x 2 2 - y 2 2) / x 2 1
        (s, (y 0 1 - x 0 1 - s * (x 1 1 - x 0 0) + s ^ 2 * x 1 0) / x 2 1)
      refine ⟨R, by dsimp [R]; fun_prop, ?_⟩
      rintro ⟨s,t⟩
      dsimp [R]
      rw [shearConjugate_entry22, shearConjugate_entry01, h20]
      ext <;> field_simp <;> ring
  · let R : Matrix (Fin 3) (Fin 3) ℝ → ℝ × ℝ := fun y =>
      let s := (x 2 1 - y 2 1) / x 2 0
      (s, s ^ 2 - (y 2 2 - x 2 2 + s * x 2 1) / x 2 0)
    refine ⟨R, by dsimp [R]; fun_prop, ?_⟩
    rintro ⟨s,t⟩
    dsimp [R]
    rw [shearConjugate_entry21, shearConjugate_entry22]
    ext <;> field_simp <;> ring

theorem shearConjugate_isClosedEmbedding
    (x : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : x 2 0 ≠ 0 ∨ x 2 1 ≠ 0 ∨ x 1 0 ≠ 0) :
    Topology.IsClosedEmbedding (fun p : ℝ × ℝ => shearConjugate x p.1 p.2) := by
  obtain ⟨R, hR, hleft⟩ := shearConjugate_has_continuous_leftInverse x hx
  let f : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun p => shearConjugate x p.1 p.2
  have hf : Continuous f := continuous_shearConjugate x
  refine ⟨hleft.isEmbedding hR hf, ?_⟩
  have hrange : Set.range f = {y | f (R y) = y} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact congrArg f (hleft p)
    · intro hy
      exact ⟨R y, hy⟩
  change IsClosed (Set.range f)
  rw [hrange]
  exact isClosed_eq (hf.comp hR) continuous_id

@[simp] theorem shearConjugate_zero (x : Matrix (Fin 3) (Fin 3) ℝ) :
    shearConjugate x 0 0 = x := by
  rw [shearConjugate, shearElement_inv]
  have hzero : (shearElement 0 0).val = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shearElement]
  simpa using congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => A * x * A) hzero

/-- The intersection of the actual conjugacy orbit with the affine hyperplane. -/
def shearOrbitSlice (x : Matrix (Fin 3) (Fin 3) ℝ) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  Set.range (fun p : ℝ × ℝ => shearConjugate x p.1 p.2) ∩ {y | y 0 1 = 1}

/-- The non-upper-triangular case of Margulis Lemma 6(C), with an explicit
coordinate proof of properness instead of a general unipotent-orbit theorem. -/
theorem shearOrbitSlice_component_not_isCompact
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x 0 1 = 1)
    (hlower : x 2 0 ≠ 0 ∨ x 2 1 ≠ 0 ∨ x 1 0 ≠ 0) :
    ¬ IsCompact (connectedComponentIn (shearOrbitSlice x) x) := by
  let f : ℝ × ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun p => shearConjugate x p.1 p.2
  have hf : Continuous f := continuous_shearConjugate x
  obtain ⟨R, hR, hleft⟩ := shearConjugate_has_continuous_leftInverse x hlower
  have hbase : (0, 0) ∈ shearLevelSet x := by
    simpa [shearLevelSet] using hx
  have hSclosed : IsClosed (shearLevelSet x) := by
    exact isClosed_eq ((continuous_apply 1).comp ((continuous_apply 0).comp hf)) continuous_const
  have hCclosed : IsClosed (connectedComponentIn (shearLevelSet x) (0, 0)) := by
    apply closure_subset_iff_isClosed.mp
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hbase))
      (closure_minimal (connectedComponentIn_subset _ _) hSclosed)
  have hsub : f '' connectedComponentIn (shearLevelSet x) (0, 0) ⊆
      connectedComponentIn (shearOrbitSlice x) x := by
    apply (isPreconnected_connectedComponentIn.image f hf.continuousOn).subset_connectedComponentIn
    · exact ⟨(0, 0), mem_connectedComponentIn hbase, shearConjugate_zero x⟩
    · rintro y ⟨p, hp, rfl⟩
      exact ⟨⟨p, rfl⟩, connectedComponentIn_subset (shearLevelSet x) (0, 0) hp⟩
  intro hc
  apply shearLevelSet_component_not_isCompact x hx
  apply (hc.image hR).of_isClosed_subset hCclosed
  intro p hp
  exact ⟨f p, hsub ⟨p, hp, rfl⟩, hleft p⟩

end JSP400

#print axioms JSP400.shearConjugate_isClosedEmbedding
#print axioms JSP400.shearOrbitSlice_component_not_isCompact
