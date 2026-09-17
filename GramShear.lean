import ShearFlag
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Topology.Algebra.Group.Matrix

namespace JSP400

open Matrix Set
noncomputable section

/-- The symmetric matrix of Margulis's reference quadratic form. -/
def standardGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem standardGram_isSymm : standardGram.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem standardGram_det : standardGram.det = 1 := by
  norm_num [standardGram, Matrix.det_fin_three]

/-- The actual Gram matrix of the form after change of variables by g. -/
def gramMatrix (g : SL3) : Matrix (Fin 3) (Fin 3) ℝ :=
  g.val.transpose * standardGram * g.val

def gramShear (q : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (unipotentOne t).val.transpose * q * (unipotentOne t).val

theorem pullback_isSymm (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q.IsSymm)
    (a : Matrix (Fin 3) (Fin 3) ℝ) : (a.transpose * q * a).IsSymm := by
  change (a.transpose * q * a).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hq.eq, mul_assoc]

theorem gramMatrix_isSymm (g : SL3) : (gramMatrix g).IsSymm :=
  pullback_isSymm _ standardGram_isSymm _

theorem gramShear_isSymm (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q.IsSymm) (t : ℝ) :
    (gramShear q t).IsSymm := pullback_isSymm _ hq _

theorem gramMatrix_det (g : SL3) : (gramMatrix g).det = 1 := by
  simp only [gramMatrix, Matrix.det_mul, Matrix.det_transpose, standardGram_det,
    g.property, one_mul]

theorem gramShear_det (q : Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) :
    (gramShear q t).det = q.det := by
  simp only [gramShear, Matrix.det_mul, Matrix.det_transpose,
    (unipotentOne t).property, one_mul, mul_one]

theorem gramMatrix_mul_unipotentOne (g : SL3) (t : ℝ) :
    gramMatrix (g * unipotentOne t) = gramShear (gramMatrix g) t := by
  change (g.val * (unipotentOne t).val).transpose * standardGram *
    (g.val * (unipotentOne t).val) = _
  simp only [gramShear, gramMatrix, Matrix.transpose_mul, mul_assoc]

theorem gramShear_add (q : Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    gramShear (gramShear q s) t = gramShear q (s + t) := by
  rw [gramShear, gramShear, gramShear, unipotentOne_add]
  change _ = ((unipotentOne s).val * (unipotentOne t).val).transpose * q *
    ((unipotentOne s).val * (unipotentOne t).val)
  simp only [Matrix.transpose_mul, mul_assoc]

/-- Coordinates with the two-dimensional fixed space first. -/
def gramCoordinates (q : Matrix (Fin 3) (Fin 3) ℝ) : Fin 6 → ℝ :=
  ![q 2 2, q 1 1 - 2 * q 0 2, q 1 2, q 1 1 + q 0 2, q 0 1, q 0 0]

theorem gramCoordinates_sub (q r : Matrix (Fin 3) (Fin 3) ℝ) :
    gramCoordinates (q - r) = gramCoordinates q - gramCoordinates r := by
  ext i
  fin_cases i <;> simp [gramCoordinates] <;> ring

theorem gramCoordinates_smul (c : ℝ) (q : Matrix (Fin 3) (Fin 3) ℝ) :
    gramCoordinates (c • q) = c • gramCoordinates q := by
  ext i
  fin_cases i <;> simp [gramCoordinates] <;> ring

theorem gramShear_coordinates (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q.IsSymm) (t : ℝ) :
    gramCoordinates (gramShear q t) =
      ![q 2 2 + 2 * t * q 1 2 + t ^ 2 * (q 1 1 + q 0 2) +
          t ^ 3 * q 0 1 + t ^ 4 / 4 * q 0 0,
        q 1 1 - 2 * q 0 2,
        q 1 2 + t * (q 1 1 + q 0 2) + 3 * t ^ 2 / 2 * q 0 1 +
          t ^ 3 / 2 * q 0 0,
        q 1 1 + q 0 2 + 3 * t * q 0 1 + 3 * t ^ 2 / 2 * q 0 0,
        q 0 1 + t * q 0 0, q 0 0] := by
  have h10 := hq.apply 0 1
  have h20 := hq.apply 0 2
  have h21 := hq.apply 1 2
  ext i
  fin_cases i <;>
    simp [gramCoordinates, gramShear, unipotentOne, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ, h10, h20, h21] <;> ring

def gramFlag (k : ℕ) : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℝ) where
  carrier := {q | q.IsSymm ∧ ∀ j : Fin 6, k ≤ j.val → gramCoordinates q j = 0}
  zero_mem' := by
    refine ⟨by simp [Matrix.IsSymm], ?_⟩
    intro j hj
    fin_cases j <;> simp [gramCoordinates]
  add_mem' := by
    rintro q r ⟨hq, hqc⟩ ⟨hr, hrc⟩
    refine ⟨hq.add hr, ?_⟩
    intro j hj
    have hqj := hqc j hj
    have hrj := hrc j hj
    fin_cases j <;> simp [gramCoordinates] at * <;> linarith
  smul_mem' := by
    rintro c q ⟨hq, hqc⟩
    refine ⟨hq.smul c, ?_⟩
    intro j hj
    simp only [gramCoordinates_smul, Pi.smul_apply, hqc j hj, smul_zero]

theorem mem_gramFlag (q : Matrix (Fin 3) (Fin 3) ℝ) (k : ℕ) :
    q ∈ gramFlag k ↔ q.IsSymm ∧
      ∀ j : Fin 6, k ≤ j.val → gramCoordinates q j = 0 := Iff.rfl

theorem gramFlag_mono {i j : ℕ} (hij : i ≤ j) : gramFlag i ≤ gramFlag j := by
  rintro q ⟨hq, hc⟩
  exact ⟨hq, fun k hk => hc k (hij.trans hk)⟩

theorem mem_gramFlag_six (q : Matrix (Fin 3) (Fin 3) ℝ) :
    q ∈ gramFlag 6 ↔ q.IsSymm := by
  simp only [mem_gramFlag]
  constructor
  · exact And.left
  · exact fun hq => ⟨hq, fun j hj => by omega⟩

theorem gramShear_sub_mem_previousFlag (k : Fin 6)
    (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q ∈ gramFlag (k.val + 1)) (t : ℝ) :
    gramShear q t - q ∈ gramFlag k.val := by
  refine ⟨(gramShear_isSymm q hq.1 t).sub hq.1, ?_⟩
  have h0 := hq.2 0
  have h1 := hq.2 1
  have h2 := hq.2 2
  have h3 := hq.2 3
  have h4 := hq.2 4
  have h5 := hq.2 5
  intro j hj
  rw [gramCoordinates_sub, gramShear_coordinates q hq.1]
  fin_cases k <;> fin_cases j
  all_goals norm_num at hj
  all_goals simp_all [gramCoordinates, sub_eq_zero]

def gramFixed (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, a; 0, -a, 0; a, 0, b]

theorem mem_gramFlag_two (q : Matrix (Fin 3) (Fin 3) ℝ) :
    q ∈ gramFlag 2 ↔ ∃ a b, q = gramFixed a b := by
  constructor
  · rintro ⟨hs, hc⟩
    have h2 := hc 2 (by decide)
    have h3 := hc 3 (by decide)
    have h4 := hc 4 (by decide)
    have h5 := hc 5 (by decide)
    simp [gramCoordinates] at h2 h3 h4 h5
    have h11 : q 1 1 = -q 0 2 := by linarith
    have h10 := hs.apply 0 1
    have h20 := hs.apply 0 2
    have h21 := hs.apply 1 2
    refine ⟨q 0 2, q 2 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [gramFixed]
  · rintro ⟨a, b, rfl⟩
    refine ⟨?_, ?_⟩
    · apply Matrix.IsSymm.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    · intro j hj
      fin_cases j <;> norm_num at hj
      all_goals simp [gramCoordinates, gramFixed]

theorem gramFixed_det (a b : ℝ) : (gramFixed a b).det = a ^ 3 := by
  simp [gramFixed, Matrix.det_fin_three]
  ring

theorem gramMatrix_unipotentTwo (t : ℝ) :
    gramMatrix (unipotentTwo t) = gramFixed 1 (2 * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramMatrix, gramFixed, standardGram, unipotentTwo, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ, two_mul]

@[simp] theorem gramShear_zero (q : Matrix (Fin 3) (Fin 3) ℝ) : gramShear q 0 = q := by
  have hz : (unipotentOne 0).val = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [unipotentOne]
  simp [gramShear, hz]

theorem gramShear_gramFixed (a b t : ℝ) : gramShear (gramFixed a b) t = gramFixed a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramShear, gramFixed, unipotentOne, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_succ] <;> ring

theorem gramFixed_of_det_one (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q ∈ gramFlag 2) (hd : q.det = 1) : ∃ b : ℝ, q = gramFixed 1 b := by
  obtain ⟨a, b, rfl⟩ := (mem_gramFlag_two q).mp hq
  rw [gramFixed_det] at hd
  have ha : a = 1 := by
    have hp : (a - 1) * (a ^ 2 + a + 1) = 0 := by nlinarith [hd]
    rcases mul_eq_zero.mp hp with h | h
    · linarith
    · nlinarith [sq_nonneg (a + 1 / 2)]
  exact ⟨b, by rw [ha]⟩

theorem gramFlag_step_coordinate (k : Fin 6) (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q ∈ gramFlag (k.val + 1)) :
    q ∈ gramFlag k.val ↔ gramCoordinates q k = 0 := by
  constructor
  · exact fun h => h.2 k le_rfl
  · intro hk
    refine ⟨hq.1, ?_⟩
    intro j hj
    by_cases h : k = j
    · simpa [← h] using hk
    · exact hq.2 j (by have hval : k.val ≠ j.val := fun heq => h (Fin.ext heq); omega)

theorem gramFlag_invariant (k : Fin 6)
    (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q ∈ gramFlag (k.val + 1)) (t : ℝ) :
    gramShear q t ∈ gramFlag (k.val + 1) := by
  have hd := gramFlag_mono (Nat.le_succ k.val) (gramShear_sub_mem_previousFlag k q hq t)
  simpa only [sub_add_cancel] using (gramFlag (k.val + 1)).add_mem hd hq

theorem gramFlag_step_coordinate_invariant (k : Fin 6)
    (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q ∈ gramFlag (k.val + 1)) (t : ℝ) :
    gramCoordinates (gramShear q t) k = gramCoordinates q k := by
  have hd := (gramShear_sub_mem_previousFlag k q hq t).2 k le_rfl
  rw [gramCoordinates_sub] at hd
  exact sub_eq_zero.mp hd

theorem continuous_gramCoordinate (j : Fin 6) :
    Continuous (fun q : Matrix (Fin 3) (Fin 3) ℝ => gramCoordinates q j) := by
  fin_cases j <;> simp only [gramCoordinates] <;> fun_prop

theorem isClosed_gramFlag (k : ℕ) :
    IsClosed (gramFlag k : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have heq : (gramFlag k : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
      {q | q.transpose = q} ∩ ⋂ j : Fin 6, ⋂ (_h : k ≤ j.val), {q | gramCoordinates q j = 0} := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_id
  · exact isClosed_iInter (fun j => isClosed_iInter (fun _ =>
      isClosed_eq (continuous_gramCoordinate j) continuous_const))

theorem continuous_gramShear : Continuous (fun p : Matrix (Fin 3) (Fin 3) ℝ × ℝ =>
    gramShear p.1 p.2) := by
  unfold gramShear unipotentOne
  fun_prop

theorem continuous_gramMatrix : Continuous gramMatrix := by
  unfold gramMatrix
  fun_prop

end
end JSP400

#print axioms JSP400.gramShear_sub_mem_previousFlag
