import ShearCurves
import ShearFlag
import BoundaryBumping
import Mathlib.Topology.Sequences

namespace JSP400

open Set Matrix Filter
open scoped Topology Matrix.Norms.Elementwise

def shearLayer (A : Set (Matrix (Fin 3) (Fin 3) ℝ)) (k : ℕ) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {x | x ∈ A ∧ x ∈ shearFlag k ∧ x 0 1 = 1}

def shearFixedDomain (A : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {x | x ∈ A ∧ x ∈ shearLieAlgebra ∧ x 0 1 = 1}

theorem shearLayer_inter_lie (A : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (k : ℕ) (hk : 2 ≤ k) : shearLayer A k ∩ shearLieAlgebra = shearFixedDomain A := by
  ext x
  constructor
  · rintro ⟨⟨hxA, hxF, hx1⟩, hxLie⟩
    exact ⟨hxA, hxLie, hx1⟩
  · rintro ⟨hxA, hxLie, hx1⟩
    exact ⟨⟨hxA, shearFlag_contains_fixed hk hxLie, hx1⟩, hxLie⟩

theorem isClosed_shearLieAlgebra : IsClosed shearLieAlgebra := by
  have heq : shearLieAlgebra = (shearFlag 2 : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
    ext x
    exact (mem_shearFlag_two x).symm
  rw [heq]
  exact isClosed_shearFlag 2

theorem isClosed_shearLayer (A : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hA : IsClosed A) (k : ℕ) : IsClosed (shearLayer A k) :=
  hA.inter ((isClosed_shearFlag k).inter (isClosed_eq (by fun_prop) continuous_const))

theorem isClosed_shearFixedDomain (A : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hA : IsClosed A) : IsClosed (shearFixedDomain A) :=
  hA.inter (isClosed_shearLieAlgebra.inter (isClosed_eq (by fun_prop) continuous_const))

theorem shearOrbitSlice_mem_flag (k : Fin 8) (x : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : x ∈ shearFlag (k.val + 1)) :
    shearOrbitSlice x ⊆ (shearFlag (k.val + 1) : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  rintro y ⟨⟨⟨s,t⟩, rfl⟩, hy⟩
  exact shearFlag_invariant k x hx s t

/-- A moving family of actual orbit slices drops by one level of the explicit
flag when its base points tend to a point in the common fixed space. -/
theorem upper_limit_shear_slices_previousFlag (k : Fin 8) (hk : 2 ≤ k.val)
    (x : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (p : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : ∀ n, x n ∈ shearFlag (k.val + 1)) (hp : p ∈ shearLieAlgebra)
    (ht : Tendsto x atTop (𝓝 p)) :
    upperSetLimit (fun n => shearOrbitSlice (x n)) ⊆
      (shearFlag k.val : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have hkeep := upperSetLimit_subset_of_eventually_subset_closed
    (fun n => shearOrbitSlice (x n)) (isClosed_shearFlag (k.val + 1))
    (Eventually.of_forall (fun n => shearOrbitSlice_mem_flag k (x n) (hx n)))
  have hp0 : shearCoordinates p k = 0 := (shearFlag_contains_fixed hk hp).2 k le_rfl
  have hc : Tendsto (fun n => shearCoordinates (x n) k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hp0, Function.comp_def] using ((continuous_shearCoordinate k).tendsto p).comp ht
  have hdrop := upperSetLimit_subset_continuous_fiber
    (fun n => shearOrbitSlice (x n)) (fun y => shearCoordinates y k)
    (continuous_shearCoordinate k) (fun n => shearCoordinates (x n) k) 0 hc
    (fun n y hy => by
      obtain ⟨⟨⟨s,t⟩, rfl⟩, hy⟩ := hy
      exact shearFlag_step_coordinate_invariant k (x n) (hx n) s t)
  intro y hy
  exact (shearFlag_step_coordinate k y (hkeep hy)).mpr (hdrop hy)

/-- The finite dimension descent behind Margulis Lemma 6(B2), specialized to
the explicit adjoint action. All geometry is supplied by actual curves and
their compact boundary limits. -/
theorem shear_fixed_component_noncompact_of_layer
    (A : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hA : IsClosed A)
    (hnil : ∀ x ∈ A, IsNilpotent x)
    (hinv : ∀ x ∈ A, ∀ s t : ℝ, shearConjugate x s t ∈ A) :
    ∀ n : ℕ, n + 2 ≤ 8 → ∀ p : Matrix (Fin 3) (Fin 3) ℝ,
      p ∈ shearFixedDomain A → p ∈ closure (shearLayer A (n + 2) \ shearLieAlgebra) →
      ¬ IsCompact (connectedComponentIn (shearFixedDomain A) p) := by
  intro n
  induction n with
  | zero =>
    intro hn p hp hcl
    have he : shearLayer A 2 \ shearLieAlgebra = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxnot⟩
      exact hxnot ((mem_shearFlag_two x).mp hx.2.1)
    simp only [Nat.zero_add, he, closure_empty, Set.mem_empty_iff_false] at hcl
  | succ n ih =>
    intro hn p hp hcl hc
    let k : Fin 8 := ⟨n + 2, by omega⟩
    let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
      inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
    obtain ⟨x, hx, ht⟩ := mem_closure_iff_seq_limit.mp hcl
    have hxA (m : ℕ) : x m ∈ A := (hx m).1.1
    have hxF (m : ℕ) : x m ∈ shearFlag (k.val + 1) := (hx m).1.2.1
    have hx1 (m : ℕ) : x m 0 1 = 1 := (hx m).1.2.2
    choose f hf hf0 hfmem hfunb using fun m =>
      exists_unbounded_shear_curve (x m) (hx1 m) (hnil (x m) (hxA m)) (hx m).2
    have hdist : ∀ m R, ∃ t : ℝ, 0 ≤ t ∧ R < dist (f m t) p := by
      intro m R
      obtain ⟨t, ht0, hlarge⟩ := hfunb m (R + ‖p‖)
      refine ⟨t, ht0, ?_⟩
      have hb := dist_triangle (f m t) p 0
      simp only [dist_zero_right] at hb
      linarith
    have hbase : Tendsto (fun m => f m 0) atTop (𝓝 p) := by simpa only [hf0] using ht
    have hdrop := upper_limit_shear_slices_previousFlag k (by dsimp [k]; omega)
      x p hxF hp.2.1 ht
    have hkeepA : upperSetLimit (fun m => shearOrbitSlice (x m)) ⊆ A := by
      apply upperSetLimit_subset_of_eventually_subset_closed _ hA
      apply Eventually.of_forall
      rintro m y ⟨⟨⟨s,t⟩, rfl⟩, hy⟩
      exact hinv (x m) (hxA m) s t
    have hkeepX : upperSetLimit (fun m => shearOrbitSlice (x m)) ⊆ {y | y 0 1 = 1} := by
      apply upperSetLimit_subset_of_eventually_subset_closed _
        (isClosed_eq (by fun_prop) continuous_const)
      exact Eventually.of_forall (fun m y hy => hy.2)
    have hlayer : upperSetLimit (fun m => shearOrbitSlice (x m)) ⊆ shearLayer A (n + 2) :=
      fun y hy => ⟨hkeepA hy, hdrop hy, hkeepX hy⟩
    have hceq := shearLayer_inter_lie A (n + 2) (by omega)
    obtain ⟨q, hqcomp, hqcl⟩ := upper_limit_fixed_component_boundary
      (fun m => shearOrbitSlice (x m)) f p hf hfmem hdist hbase
      hlayer isClosed_shearLieAlgebra hp.2.1 (by rwa [hceq])
    rw [hceq] at hqcomp
    have hq : q ∈ shearFixedDomain A := connectedComponentIn_subset _ _ hqcomp
    have hnc := ih (by omega) q hq hqcl
    exact hnc ((connectedComponentIn_eq hqcomp) ▸ hc)

end JSP400
