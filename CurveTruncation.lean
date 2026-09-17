import ConnectedCompactLimits
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
Compact connected initial segments of unbounded continuous curves. This is the
boundary step needed for the concrete shear curves in Margulis's argument.
-/

namespace JSP400

open Set Filter TopologicalSpace
open scoped Topology

/-- The first crossing of a real level leaves the preceding interval below it. -/
theorem exists_first_level {g : ℝ → ℝ} {T R : ℝ} (hT : 0 ≤ T)
    (hg : ContinuousOn g (Icc 0 T)) (h0 : g 0 ≤ R) (h1 : R ≤ g T) :
    ∃ t ∈ Icc 0 T, g t = R ∧ ∀ s ∈ Icc 0 t, g s ≤ R := by
  have hne : (Icc 0 T ∩ g ⁻¹' {R}).Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hT hg ⟨h0, h1⟩
    exact ⟨t, ht, he⟩
  have hc : IsCompact (Icc 0 T ∩ g ⁻¹' {R}) :=
    isCompact_Icc.of_isClosed_subset
      (hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨t, ht, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro s hs
  by_contra h
  have hgs : R < g s := lt_of_not_ge h
  obtain ⟨u, hu, he⟩ := intermediate_value_Icc hs.1
    (hg.mono (Icc_subset_Icc_right (hs.2.trans ht.1.2))) ⟨h0, hgs.le⟩
  have htu : t ≤ u := hmin ⟨⟨hu.1, hu.2.trans (hs.2.trans ht.1.2)⟩, he⟩
  have hst : s = t := le_antisymm hs.2 (htu.trans hu.2)
  have hgt : g t = R := ht.2
  rw [hst, hgt] at hgs
  exact lt_irrefl _ hgs

variable {X : Type*} [MetricSpace X]

/-- An unbounded ray starting in a closed ball has a compact connected initial
segment inside that ball which reaches its sphere. -/
theorem unbounded_curve_compact_segment (f : ℝ → X)
    (hf : ContinuousOn f (Ici 0)) (p : X) (R : ℝ)
    (h0 : dist (f 0) p ≤ R)
    (hunb : ∀ A : ℝ, ∃ t : ℝ, 0 ≤ t ∧ A < dist (f t) p) :
    ∃ K : Compacts X, f 0 ∈ (K : Set X) ∧
      (K : Set X) ⊆ Metric.closedBall p R ∧
      IsPreconnected (K : Set X) ∧
      ((K : Set X) ∩ Metric.sphere p R).Nonempty ∧
      (K : Set X) ⊆ f '' Ici 0 := by
  obtain ⟨T, hT, hTout⟩ := hunb R
  have hdist : ContinuousOn (fun t => dist (f t) p) (Icc 0 T) :=
    continuous_dist.comp_continuousOn
      ((hf.mono Icc_subset_Ici_self).prodMk continuousOn_const)
  obtain ⟨t, ht, he, hbelow⟩ := exists_first_level hT hdist h0 hTout.le
  have hft : ContinuousOn f (Icc 0 t) := hf.mono Icc_subset_Ici_self
  let K : Compacts X := ⟨f '' Icc 0 t, isCompact_Icc.image_of_continuousOn hft⟩
  refine ⟨K, ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨s, hs, rfl⟩
    exact hbelow s hs
  · exact isPreconnected_Icc.image f hft
  · exact ⟨f t, ⟨t, ⟨ht.1, le_rfl⟩, rfl⟩, he⟩
  · exact image_mono Icc_subset_Ici_self

/-- Passing to a cofinal subsequence cannot enlarge the upper set limit. -/
theorem upperSetLimit_subsequence_subset (S : ℕ → Set X) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) : upperSetLimit (S ∘ φ) ⊆ upperSetLimit S := by
  intro x hx
  apply mem_iInter.mpr
  intro N
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hφ.eventually (eventually_ge_atTop N))
  have hxM := mem_iInter.mp hx M
  apply closure_mono ?_ hxM
  intro y hy
  obtain ⟨n, hyn⟩ := mem_iUnion.mp hy
  obtain ⟨hn, hyn⟩ := mem_iUnion.mp hyn
  exact mem_iUnion.mpr ⟨φ n, mem_iUnion.mpr ⟨hM n hn, hyn⟩⟩

/-- Unbounded curves based at points converging to `p` force every positive
sphere to meet a connected compact subset of the upper set limit containing `p`. -/
theorem upper_limit_connected_witness [ProperSpace X] [SecondCountableTopology X]
    (S : ℕ → Set X) (f : ℕ → ℝ → X) (p : X)
    (hf : ∀ n, ContinuousOn (f n) (Ici 0))
    (hmem : ∀ n t, 0 ≤ t → f n t ∈ S n)
    (hunb : ∀ n A, ∃ t : ℝ, 0 ≤ t ∧ A < dist (f n t) p)
    (hp : Tendsto (fun n => f n 0) atTop (𝓝 p)) (R : ℝ) (hR : 0 < R) :
    ∃ L : Compacts X, (L : Set X) ⊆ upperSetLimit S ∧
      IsPreconnected (L : Set X) ∧ p ∈ (L : Set X) ∧
      ((L : Set X) ∩ Metric.sphere p R).Nonempty := by
  have hball : ∀ᶠ n in atTop, dist (f n 0) p < R :=
    hp.eventually (Metric.ball_mem_nhds p hR)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hball
  let σ : ℕ → ℕ := fun n => n + N
  have hσ : StrictMono σ := fun a b hab => Nat.add_lt_add_right hab N
  have hstart : ∀ n, dist (f (σ n) 0) p ≤ R :=
    fun n => (hN (σ n) (Nat.le_add_left N n)).le
  choose K hK0 hKR hKconn hKsphere hKrange using
    fun n => unbounded_curve_compact_segment (f (σ n)) (hf (σ n)) p R
      (hstart n) (hunb (σ n))
  obtain ⟨L, φ, hφ, hlim, _, hconn, hpL, hLF⟩ :=
    exists_connected_compact_limit K (isCompact_closedBall p R) Metric.isClosed_sphere
      hKR hKconn hKsphere (fun n => f (σ n) 0) p (hp.comp hσ.tendsto_atTop) hK0
  refine ⟨L, ?_, hconn, hpL, hLF⟩
  have hKS : ∀ n, (K n : Set X) ⊆ (S ∘ σ) n := by
    intro n y hy
    obtain ⟨t, ht, rfl⟩ := hKrange n hy
    exact hmem (σ n) t ht
  exact (compact_subsequence_limit_subset_upperSetLimit K (S ∘ σ) hKS L φ hφ hlim).trans
    (upperSetLimit_subsequence_subset S σ hσ.tendsto_atTop)

/-- The base-point component of the upper limit is noncompact. All geometric
input is expressed by actual continuous unbounded curves, not assumed limit
components. -/
theorem upper_limit_component_not_compact [ProperSpace X] [SecondCountableTopology X]
    (S : ℕ → Set X) (f : ℕ → ℝ → X) (p : X)
    (hf : ∀ n, ContinuousOn (f n) (Ici 0))
    (hmem : ∀ n t, 0 ≤ t → f n t ∈ S n)
    (hunb : ∀ n A, ∃ t : ℝ, 0 ≤ t ∧ A < dist (f n t) p)
    (hp : Tendsto (fun n => f n 0) atTop (𝓝 p)) :
    ¬IsCompact (connectedComponentIn (upperSetLimit S) p) := by
  intro hc
  obtain ⟨M, hM⟩ := hc.bddAbove_image (continuous_id.dist continuous_const).continuousOn
  obtain ⟨L, hLS, hconn, hpL, q, hqL, hqR⟩ :=
    upper_limit_connected_witness S f p hf hmem hunb hp (max M 0 + 1) (by positivity)
  have hqcomp := hconn.subset_connectedComponentIn hpL hLS hqL
  have hbd : dist q p ≤ M := hM ⟨q, hqcomp, rfl⟩
  have he : dist q p = max M 0 + 1 := hqR
  have : M ≤ max M 0 := le_max_left _ _
  linarith

end JSP400
