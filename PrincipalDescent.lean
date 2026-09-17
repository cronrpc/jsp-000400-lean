import PrincipalCurves
import BoundaryBumping
import Mathlib.Topology.Sequences

namespace JSP400

open Matrix Set Filter
open scoped Topology Matrix.Norms.Elementwise

def principalOrbit (p : PrincipalSpace) : Set PrincipalSpace :=
  range (fun t : ℝ => principalAction (unipotentOne t) p)

def principalLayer (A : Set PrincipalSpace) (k : ℕ) : Set PrincipalSpace := A ∩ principalFlag k

def principalFixedDomain (A : Set PrincipalSpace) : Set PrincipalSpace := A ∩ principalFlag 4

theorem principalLayer_inter_fixed (A : Set PrincipalSpace) (k : ℕ) (hk : 4 ≤ k) :
    principalLayer A k ∩ (principalFlag 4 : Set PrincipalSpace) = principalFixedDomain A := by
  ext p
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · exact fun h => ⟨⟨h.1, principalFlag_mono hk h.2⟩, h.2⟩

theorem principalOrbit_mem_flag (k : Fin 14) (p : PrincipalSpace)
    (hp : p ∈ principalFlag (k.val + 1)) :
    principalOrbit p ⊆ (principalFlag (k.val + 1) : Set PrincipalSpace) := by
  rintro q ⟨t, rfl⟩
  exact principalFlag_invariant k p hp t

theorem upper_limit_principal_orbits_previousFlag (k : Fin 14) (hk : 4 ≤ k.val)
    (x : ℕ → PrincipalSpace) (p : PrincipalSpace)
    (hx : ∀ n, x n ∈ principalFlag (k.val + 1)) (hp : p ∈ principalFlag 4)
    (ht : Tendsto x atTop (𝓝 p)) :
    upperSetLimit (fun n => principalOrbit (x n)) ⊆ (principalFlag k.val : Set PrincipalSpace) := by
  have hkeep := upperSetLimit_subset_of_eventually_subset_closed
    (fun n => principalOrbit (x n)) (isClosed_principalFlag (k.val + 1))
    (Eventually.of_forall (fun n => principalOrbit_mem_flag k (x n) (hx n)))
  have hp0 : principalCoordinates p k = 0 := (principalFlag_mono hk hp).2.2 k le_rfl
  have hc : Tendsto (fun n => principalCoordinates (x n) k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hp0, Function.comp_def] using ((continuous_principalCoordinate k).tendsto p).comp ht
  have hdrop := upperSetLimit_subset_continuous_fiber
    (fun n => principalOrbit (x n)) (fun y => principalCoordinates y k)
    (continuous_principalCoordinate k) (fun n => principalCoordinates (x n) k) 0 hc
    (fun n y hy => by
      obtain ⟨t, rfl⟩ := hy
      exact principalFlag_step_coordinate_invariant k (x n) (hx n) t)
  intro y hy
  exact (principalFlag_step_coordinate k y (hkeep hy)).mpr (hdrop hy)

/-- The closure-enlargement argument for the actual representation with
stabilizer V₁, proved by its explicit fourteen-dimensional invariant flag. -/
theorem principal_fixed_component_noncompact_of_layer
    (A : Set PrincipalSpace) (hA : IsClosed A)
    (hinv : ∀ p ∈ A, ∀ t : ℝ, principalAction (unipotentOne t) p ∈ A) :
    ∀ n : ℕ, n + 4 ≤ 14 → ∀ p : PrincipalSpace,
      p ∈ principalFixedDomain A →
      p ∈ closure (principalLayer A (n + 4) \ (principalFlag 4 : Set PrincipalSpace)) →
      ¬IsCompact (connectedComponentIn (principalFixedDomain A) p) := by
  intro n
  induction n with
  | zero =>
    intro hn p hp hcl
    have he : principalLayer A 4 \ (principalFlag 4 : Set PrincipalSpace) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      exact fun x h => h.2 h.1.2
    simp only [Nat.zero_add, he, closure_empty, Set.mem_empty_iff_false] at hcl
  | succ n ih =>
    intro hn p hp hcl hc
    let k : Fin 14 := ⟨n + 4, by omega⟩
    let : FirstCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
      inferInstanceAs (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
    obtain ⟨x, hx, ht⟩ := mem_closure_iff_seq_limit.mp hcl
    have hxA (m : ℕ) : x m ∈ A := (hx m).1.1
    have hxF (m : ℕ) : x m ∈ principalFlag (k.val + 1) := (hx m).1.2
    have hxFull (m : ℕ) : x m ∈ principalFlag 14 :=
      principalFlag_mono (by dsimp [k]; omega) (hxF m)
    choose f hf hf0 hfmem hfunb using fun m =>
      exists_unbounded_principal_curve (x m) (hxFull m) (hx m).2
    have hdist : ∀ m R, ∃ t : ℝ, 0 ≤ t ∧ R < dist (f m t) p := by
      intro m R
      obtain ⟨t, ht0, hlarge⟩ := hfunb m (R + ‖p‖)
      refine ⟨t, ht0, ?_⟩
      have hb := dist_triangle (f m t) p 0
      simp only [dist_zero_right] at hb
      linarith
    have hbase : Tendsto (fun m => f m 0) atTop (𝓝 p) := by simpa only [hf0] using ht
    have hdrop := upper_limit_principal_orbits_previousFlag k (by dsimp [k]; omega)
      x p hxF hp.2 ht
    have hkeepA : upperSetLimit (fun m => principalOrbit (x m)) ⊆ A := by
      apply upperSetLimit_subset_of_eventually_subset_closed _ hA
      apply Eventually.of_forall
      rintro m y ⟨t, rfl⟩
      exact hinv (x m) (hxA m) t
    have hlayer : upperSetLimit (fun m => principalOrbit (x m)) ⊆ principalLayer A (n + 4) :=
      fun y hy => ⟨hkeepA hy, hdrop hy⟩
    have hceq := principalLayer_inter_fixed A (n + 4) (by omega)
    obtain ⟨q, hqcomp, hqcl⟩ := upper_limit_fixed_component_boundary
      (fun m => principalOrbit (x m)) f p hf hfmem hdist hbase
      hlayer (isClosed_principalFlag 4) hp.2 (by rwa [hceq])
    rw [hceq] at hqcomp
    have hq : q ∈ principalFixedDomain A := connectedComponentIn_subset _ _ hqcomp
    have hnc := ih (by omega) q hq hqcl
    exact hnc ((connectedComponentIn_eq hqcomp) ▸ hc)

end JSP400

#print axioms JSP400.principal_fixed_component_noncompact_of_layer
