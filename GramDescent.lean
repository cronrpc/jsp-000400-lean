import GramCurves
import BoundaryBumping
import Mathlib.Topology.Sequences

namespace JSP400

open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

def gramLayer (A : Set (Matrix (Fin 3) (Fin 3) ℝ)) (k : ℕ) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) := A ∩ gramFlag k

def gramFixedDomain (A : Set (Matrix (Fin 3) (Fin 3) ℝ)) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) := A ∩ gramFlag 2

theorem gramLayer_inter_fixed (A : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (k : ℕ) (hk : 2 ≤ k) :
    gramLayer A k ∩ (gramFlag 2 : Set (Matrix (Fin 3) (Fin 3) ℝ)) =
      gramFixedDomain A := by
  ext q
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, gramFlag_mono hk h.2⟩, h.2⟩

theorem gramOrbit_mem_flag (k : Fin 6) (q : Matrix (Fin 3) (Fin 3) ℝ)
    (hq : q ∈ gramFlag (k.val + 1)) :
    range (gramShear q) ⊆ (gramFlag (k.val + 1) : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  rintro y ⟨t, rfl⟩
  exact gramFlag_invariant k q hq t

theorem upper_limit_gram_orbits_previousFlag (k : Fin 6) (hk : 2 ≤ k.val)
    (x : ℕ → Matrix (Fin 3) (Fin 3) ℝ) (p : Matrix (Fin 3) (Fin 3) ℝ)
    (hx : ∀ n, x n ∈ gramFlag (k.val + 1)) (hp : p ∈ gramFlag 2)
    (ht : Tendsto x atTop (𝓝 p)) :
    upperSetLimit (fun n => range (gramShear (x n))) ⊆
      (gramFlag k.val : Set (Matrix (Fin 3) (Fin 3) ℝ)) := by
  have hkeep := upperSetLimit_subset_of_eventually_subset_closed
    (fun n => range (gramShear (x n))) (isClosed_gramFlag (k.val + 1))
    (Eventually.of_forall (fun n => gramOrbit_mem_flag k (x n) (hx n)))
  have hp0 : gramCoordinates p k = 0 := (gramFlag_mono hk hp).2 k le_rfl
  have hc : Tendsto (fun n => gramCoordinates (x n) k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hp0, Function.comp_def] using ((continuous_gramCoordinate k).tendsto p).comp ht
  have hdrop := upperSetLimit_subset_continuous_fiber
    (fun n => range (gramShear (x n))) (fun y => gramCoordinates y k)
    (continuous_gramCoordinate k) (fun n => gramCoordinates (x n) k) 0 hc
    (fun n y hy => by
      obtain ⟨t, rfl⟩ := hy
      exact gramFlag_step_coordinate_invariant k (x n) (hx n) t)
  intro y hy
  exact (gramFlag_step_coordinate k y (hkeep hy)).mpr (hdrop hy)

/-- A concrete form of the unipotent closure-enlargement argument on symmetric
matrices. It uses the six explicit flag levels and the actual unbounded orbit
curves, without a general Lie--Kolchin or orbit-classification premise. -/
theorem gram_fixed_component_noncompact_of_layer
    (A : Set (Matrix (Fin 3) (Fin 3) ℝ)) (hA : IsClosed A)
    (hinv : ∀ x ∈ A, ∀ t : ℝ, gramShear x t ∈ A) :
    ∀ n : ℕ, n + 2 ≤ 6 → ∀ p : Matrix (Fin 3) (Fin 3) ℝ,
      p ∈ gramFixedDomain A →
      p ∈ closure (gramLayer A (n + 2) \ (gramFlag 2 : Set (Matrix (Fin 3) (Fin 3) ℝ))) →
      ¬IsCompact (connectedComponentIn (gramFixedDomain A) p) := by
  intro n
  induction n with
  | zero =>
    intro hn p hp hcl
    have he : gramLayer A 2 \ (gramFlag 2 : Set (Matrix (Fin 3) (Fin 3) ℝ)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact fun x h => h.2 h.1.2
    simp only [Nat.zero_add, he, closure_empty, Set.mem_empty_iff_false] at hcl
  | succ n ih =>
    intro hn p hp hcl hc
    let k : Fin 6 := ⟨n + 2, by omega⟩
    let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
      inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
    obtain ⟨x, hx, ht⟩ := mem_closure_iff_seq_limit.mp hcl
    have hxA (m : ℕ) : x m ∈ A := (hx m).1.1
    have hxF (m : ℕ) : x m ∈ gramFlag (k.val + 1) := (hx m).1.2
    choose f hf hf0 hfmem hfunb using fun m =>
      exists_unbounded_gram_curve (x m) (hxF m).1 (hx m).2
    have hdist : ∀ m R, ∃ t : ℝ, 0 ≤ t ∧ R < dist (f m t) p := by
      intro m R
      obtain ⟨t, ht0, hlarge⟩ := hfunb m (R + ‖p‖)
      refine ⟨t, ht0, ?_⟩
      have hb := dist_triangle (f m t) p 0
      simp only [dist_zero_right] at hb
      linarith
    have hbase : Tendsto (fun m => f m 0) atTop (𝓝 p) := by simpa only [hf0] using ht
    have hdrop := upper_limit_gram_orbits_previousFlag k (by dsimp [k]; omega)
      x p hxF hp.2 ht
    have hkeepA : upperSetLimit (fun m => range (gramShear (x m))) ⊆ A := by
      apply upperSetLimit_subset_of_eventually_subset_closed _ hA
      apply Eventually.of_forall
      rintro m y ⟨t, rfl⟩
      exact hinv (x m) (hxA m) t
    have hlayer : upperSetLimit (fun m => range (gramShear (x m))) ⊆ gramLayer A (n + 2) :=
      fun y hy => ⟨hkeepA hy, hdrop hy⟩
    have hceq := gramLayer_inter_fixed A (n + 2) (by omega)
    obtain ⟨q, hqcomp, hqcl⟩ := upper_limit_fixed_component_boundary
      (fun m => range (gramShear (x m))) f p hf hfmem hdist hbase
      hlayer (isClosed_gramFlag 2) hp.2 (by rwa [hceq])
    rw [hceq] at hqcomp
    have hq : q ∈ gramFixedDomain A := connectedComponentIn_subset _ _ hqcomp
    have hnc := ih (by omega) q hq hqcl
    exact hnc ((connectedComponentIn_eq hqcomp) ▸ hc)

end JSP400

#print axioms JSP400.gram_fixed_component_noncompact_of_layer
