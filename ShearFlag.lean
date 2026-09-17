import ShearFixedSpace

namespace JSP400

open Matrix Set

/-- Coordinates on the actual eight-dimensional trace-zero matrix space,
ordered so that every adjoint shear is upper unitriangular. -/
def shearCoordinates (x : Matrix (Fin 3) (Fin 3) ℝ) : Fin 8 → ℝ :=
  ![x 0 2, x 0 1, x 1 2 - x 0 1, x 0 0, x 1 1, x 1 0, x 2 1, x 2 0]

theorem shearCoordinates_add (x y : Matrix (Fin 3) (Fin 3) ℝ) :
    shearCoordinates (x + y) = shearCoordinates x + shearCoordinates y := by
  ext i
  fin_cases i <;> simp [shearCoordinates]
  all_goals ring

theorem shearCoordinates_sub (x y : Matrix (Fin 3) (Fin 3) ℝ) :
    shearCoordinates (x - y) = shearCoordinates x - shearCoordinates y := by
  ext i
  fin_cases i <;> simp [shearCoordinates]
  all_goals ring

theorem shearCoordinates_smul (c : ℝ) (x : Matrix (Fin 3) (Fin 3) ℝ) :
    shearCoordinates (c • x) = c • shearCoordinates x := by
  ext i
  fin_cases i <;> simp [shearCoordinates]
  all_goals ring

def shearFlag (k : ℕ) : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  carrier := {x | x.trace = 0 ∧ ∀ j : Fin 8, k ≤ j.val → shearCoordinates x j = 0}
  zero_mem' := by
    refine ⟨by simp, ?_⟩
    intro j hj
    fin_cases j <;> simp [shearCoordinates]
  add_mem' := by
    rintro x y ⟨hxt, hx⟩ ⟨hyt, hy⟩
    refine ⟨by simp [Matrix.trace_add, hxt, hyt], ?_⟩
    intro j hj
    simp only [shearCoordinates_add, Pi.add_apply, hx j hj, hy j hj, add_zero]
  smul_mem' := by
    rintro c x ⟨hxt, hx⟩
    refine ⟨by simp [Matrix.trace_smul, hxt], ?_⟩
    intro j hj
    simp only [shearCoordinates_smul, Pi.smul_apply, hx j hj, smul_zero]

theorem mem_shearFlag (x : Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) :
    x ∈ shearFlag k ↔ x.trace = 0 ∧
      ∀ j : Fin 8, k ≤ j.val → shearCoordinates x j = 0 := Iff.rfl

theorem shearFlag_mono {i j : ℕ} (hij : i ≤ j) : shearFlag i ≤ shearFlag j := by
  rintro x ⟨hxt, hx⟩
  exact ⟨hxt, fun k hk => hx k (hij.trans hk)⟩

theorem shearFlag_zero : shearFlag 0 = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨hxt, hx⟩
  change x = 0
  have hcoords : ∀ j : Fin 8, shearCoordinates x j = 0 := fun j => hx j (Nat.zero_le _)
  have h0 := hcoords 0
  have h1 := hcoords 1
  have h2 := hcoords 2
  have h3 := hcoords 3
  have h4 := hcoords 4
  have h5 := hcoords 5
  have h6 := hcoords 6
  have h7 := hcoords 7
  simp [shearCoordinates] at h0 h1 h2 h3 h4 h5 h6 h7
  have h22 : x 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_succ, h3, h4] using hxt
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem mem_shearFlag_eight (x : Matrix (Fin 3) (Fin 3) ℝ) :
    x ∈ shearFlag 8 ↔ x.trace = 0 := by
  simp only [mem_shearFlag]
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, fun j hj => by omega⟩

theorem shearFlag_step_coordinate (k : Fin 8) (x : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : x ∈ shearFlag (k.val + 1)) :
    x ∈ shearFlag k.val ↔ shearCoordinates x k = 0 := by
  constructor
  · exact fun h => h.2 k le_rfl
  · intro hk
    refine ⟨hx.1, ?_⟩
    intro j hj
    by_cases h : k = j
    · simpa [← h] using hk
    · exact hx.2 j (by have hval : k.val ≠ j.val := fun heq => h (Fin.ext heq); omega)

theorem shearConjugate_trace (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    (shearConjugate x s t).trace = x.trace := by
  have hi : (shearElement s t)⁻¹.val * (shearElement s t).val = 1 :=
    congrArg Subtype.val (inv_mul_cancel (shearElement s t))
  unfold shearConjugate
  rw [Matrix.trace_mul_comm, ← mul_assoc, hi, one_mul]

theorem shearConjugate_coordinates (x : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    shearCoordinates (shearConjugate x s t) =
      ![x 0 2 - s * x 0 1 + (s ^ 2 - t) * x 0 0 + s * x 1 2 - s ^ 2 * x 1 1 +
          s * (s ^ 2 - t) * x 1 0 + t * x 2 2 - s * t * x 2 1 +
          t * (s ^ 2 - t) * x 2 0,
        x 0 1 + s * (x 1 1 - x 0 0) - s ^ 2 * x 1 0 + t * (x 2 1 - s * x 2 0),
        x 1 2 + s * (x 2 2 - x 1 1) - s ^ 2 * x 2 1 +
          (s ^ 2 - t) * x 1 0 + s * (s ^ 2 - t) * x 2 0 -
          (x 0 1 + s * (x 1 1 - x 0 0) - s ^ 2 * x 1 0 +
            t * (x 2 1 - s * x 2 0)),
        x 0 0 + s * x 1 0 + t * x 2 0,
        x 1 1 + s * x 2 1 - s * x 1 0 - s ^ 2 * x 2 0,
        x 1 0 + s * x 2 0, x 2 1 - s * x 2 0, x 2 0] := by
  rw [shearConjugate, shearElement_inv]
  ext i
  fin_cases i <;>
    simp [shearCoordinates, shearElement, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- Every adjoint shear acts trivially on each successive quotient of the
explicit flag. This is the concrete triangularity input for dimension descent. -/
theorem shearConjugate_sub_mem_previousFlag (k : Fin 8)
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x ∈ shearFlag (k.val + 1)) (s t : ℝ) :
    shearConjugate x s t - x ∈ shearFlag k.val := by
  refine ⟨by rw [Matrix.trace_sub, shearConjugate_trace, sub_self], ?_⟩
  have h0 := hx.2 0
  have h1 := hx.2 1
  have h2 := hx.2 2
  have h3 := hx.2 3
  have h4 := hx.2 4
  have h5 := hx.2 5
  have h6 := hx.2 6
  have h7 := hx.2 7
  have h22 : x 2 2 = -x 0 0 - x 1 1 := by
    have ht := hx.1
    simp [Matrix.trace, Fin.sum_univ_succ] at ht
    linarith
  intro j hj
  rw [shearCoordinates_sub, shearConjugate_coordinates]
  fin_cases k <;> fin_cases j
  all_goals norm_num at hj
  all_goals simp_all [shearCoordinates, sub_eq_zero]

/-- The second member of the flag is exactly the fixed space, so descent
through F₈,...,F₂ always retains that space. -/
theorem mem_shearFlag_two (x : Matrix (Fin 3) (Fin 3) ℝ) :
    x ∈ shearFlag 2 ↔ x ∈ shearLieAlgebra := by
  constructor
  · rintro ⟨ht, hx⟩
    have h2 := hx 2 (by decide)
    have h3 := hx 3 (by decide)
    have h4 := hx 4 (by decide)
    have h5 := hx 5 (by decide)
    have h6 := hx 6 (by decide)
    have h7 := hx 7 (by decide)
    simp [shearCoordinates, sub_eq_zero] at h2 h3 h4 h5 h6 h7
    have h22 : x 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_succ, h3, h4] using ht
    refine ⟨x 0 1, x 0 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro ⟨a, b, rfl⟩
    refine ⟨by simp [Matrix.trace, Fin.sum_univ_succ], ?_⟩
    intro j hj
    fin_cases j <;> norm_num at hj
    all_goals simp [shearCoordinates]

theorem shearFlag_invariant (k : Fin 8)
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x ∈ shearFlag (k.val + 1)) (s t : ℝ) :
    shearConjugate x s t ∈ shearFlag (k.val + 1) := by
  have hd := shearFlag_mono (Nat.le_succ k.val)
    (shearConjugate_sub_mem_previousFlag k x hx s t)
  simpa only [sub_add_cancel] using (shearFlag (k.val + 1)).add_mem hd hx

theorem shearFlag_contains_fixed {k : ℕ} (hk : 2 ≤ k)
    {x : Matrix (Fin 3) (Fin 3) ℝ} (hx : x ∈ shearLieAlgebra) : x ∈ shearFlag k :=
  shearFlag_mono hk ((mem_shearFlag_two x).mpr hx)

theorem continuous_shearCoordinate (j : Fin 8) :
    Continuous (fun x : Matrix (Fin 3) (Fin 3) ℝ => shearCoordinates x j) := by
  fin_cases j <;> simp only [shearCoordinates] <;> fun_prop

theorem isClosed_shearFlag (k : ℕ) :
    IsClosed (shearFlag k : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have heq : (shearFlag k : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
      {x | x.trace = 0} ∩ ⋂ j : Fin 8, ⋂ (_h : k ≤ j.val), {x | shearCoordinates x j = 0} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [heq]
  apply IsClosed.inter
  · apply isClosed_eq _ continuous_const
    fun_prop
  · exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_eq (continuous_shearCoordinate j) continuous_const))

theorem shearFlag_step_coordinate_invariant (k : Fin 8)
    (x : Matrix (Fin 3) (Fin 3) ℝ) (hx : x ∈ shearFlag (k.val + 1)) (s t : ℝ) :
    shearCoordinates (shearConjugate x s t) k = shearCoordinates x k := by
  have hd := (shearConjugate_sub_mem_previousFlag k x hx s t).2 k le_rfl
  rw [shearCoordinates_sub] at hd
  exact sub_eq_zero.mp hd

end JSP400
