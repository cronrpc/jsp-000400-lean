import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
Auxiliary compact-set limit facts for the topological step in Margulis Lemma 12.
The topology on compact sets is the actual Vietoris topology.
-/

namespace JSP400

open Set Filter TopologicalSpace
open scoped Topology

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]

/-- A Vietoris limit of connected compact sets is connected. -/
theorem preconnected_compact_limit {l : Filter ι} [NeBot l]
    (K : ι → Compacts X) (L : Compacts X)
    (hK : ∀ i, IsPreconnected (K i : Set X)) (ht : Tendsto K l (𝓝 L)) :
    IsPreconnected (L : Set X) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed L.isCompact.isClosed]
  intro u v hu hv hcover huv
  by_contra h
  obtain ⟨hnu, hnv⟩ := not_or.mp h
  obtain ⟨x, hxL, hxu⟩ := Set.not_subset.mp hnu
  obtain ⟨y, hyL, hyv⟩ := Set.not_subset.mp hnv
  have hxv : x ∈ v := (hcover hxL).resolve_left hxu
  have hyu : y ∈ u := (hcover hyL).resolve_right hyv
  obtain ⟨U, V, hU, hV, huU, hvV, hUV⟩ := normal_separation hu hv huv
  have hecover : ∀ᶠ i in l, (K i : Set X) ⊆ U ∪ V :=
    ht.eventually ((Compacts.isOpen_subsets_of_isOpen (hU.union hV)).mem_nhds
      (hcover.trans (union_subset_union huU hvV)))
  have heU : ∀ᶠ i in l, ((K i : Set X) ∩ U).Nonempty :=
    ht.eventually ((Compacts.isOpen_inter_nonempty_of_isOpen hU).mem_nhds
      ⟨y, hyL, huU hyu⟩)
  have heV : ∀ᶠ i in l, ((K i : Set X) ∩ V).Nonempty :=
    ht.eventually ((Compacts.isOpen_inter_nonempty_of_isOpen hV).mem_nhds
      ⟨x, hxL, hvV hxv⟩)
  obtain ⟨i, hi, hiU, hiV⟩ := (hecover.and (heU.and heV)).exists
  obtain ⟨z, hzK, hzU, hzV⟩ := hK i U V hU hV hi hiU hiV
  exact Set.disjoint_left.mp hUV hzU hzV

omit [T2Space X] [NormalSpace X] in
/-- Meeting a fixed closed boundary is retained by a compact-set limit. -/
theorem compact_limit_meets_closed {l : Filter ι} [NeBot l]
    (K : ι → Compacts X) (L : Compacts X) (ht : Tendsto K l (𝓝 L))
    {F : Set X} (hF : IsClosed F) (hKF : ∀ᶠ i in l, ((K i : Set X) ∩ F).Nonempty) :
    ((L : Set X) ∩ F).Nonempty :=
  (Compacts.isClosed_inter_nonempty_of_isClosed hF).mem_of_tendsto ht hKF

omit [NormalSpace X] in
/-- A limit of chosen points remains in the limiting compact set. -/
theorem compact_limit_contains_point {l : Filter ι} [NeBot l]
    (K : ι → Compacts X) (L : Compacts X) (ht : Tendsto K l (𝓝 L))
    (x : ι → X) (p : X) (hx : Tendsto x l (𝓝 p))
    (hmem : ∀ᶠ i in l, x i ∈ (K i : Set X)) : p ∈ (L : Set X) := by
  have ho : IsOpen {q : Compacts X × X | q.2 ∉ (q.1 : Set X)} := by
    have hf : Continuous (fun q : Compacts X × X => (q.1, ({q.2} : Compacts X))) :=
      continuous_fst.prodMk (Compacts.continuous_singleton.comp continuous_snd)
    have h := Compacts.isOpen_setOfPred_disjoint_coe.preimage hf
    simpa using h
  have hc : IsClosed {q : Compacts X × X | q.2 ∈ (q.1 : Set X)} := by
    convert ho.isClosed_compl using 1
    ext q
    simp
  exact hc.mem_of_tendsto (ht.prodMk_nhds hx) hmem

/-- Connected compact witnesses in a common compact set have a connected
compact limit preserving both the moving base point and a fixed closed boundary. -/
theorem exists_connected_compact_limit [SecondCountableTopology X]
    (K : ℕ → Compacts X) {C F : Set X} (hC : IsCompact C) (hF : IsClosed F)
    (hKC : ∀ n, (K n : Set X) ⊆ C)
    (hconn : ∀ n, IsPreconnected (K n : Set X))
    (hKF : ∀ n, ((K n : Set X) ∩ F).Nonempty)
    (x : ℕ → X) (p : X) (hx : Tendsto x atTop (𝓝 p))
    (hxm : ∀ n, x n ∈ (K n : Set X)) :
    ∃ (L : Compacts X) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (K ∘ φ) atTop (𝓝 L) ∧ (L : Set X) ⊆ C ∧
      IsPreconnected (L : Set X) ∧ p ∈ (L : Set X) ∧ ((L : Set X) ∩ F).Nonempty := by
  obtain ⟨L, hLC, φ, hφ, ht⟩ :=
    (Compacts.isCompact_subsets_of_isCompact hC).tendsto_subseq hKC
  refine ⟨L, φ, hφ, ht, hLC, preconnected_compact_limit _ _ (fun n => hconn (φ n)) ht,
    ?_, ?_⟩
  · exact compact_limit_contains_point (K ∘ φ) L ht (x ∘ φ) p
      (hx.comp hφ.tendsto_atTop) (Eventually.of_forall (fun n => hxm (φ n)))
  · exact compact_limit_meets_closed (K ∘ φ) L ht hF
      (Eventually.of_forall (fun n => hKF (φ n)))

/-- The sequential upper set limit, expressed without a chosen subsequence. -/
def upperSetLimit (S : ℕ → Set X) : Set X :=
  ⋂ N : ℕ, closure (⋃ n : ℕ, ⋃ (_h : N ≤ n), S n)

omit [T2Space X] [NormalSpace X] in
theorem compact_subsequence_limit_subset_upperSetLimit
    (K : ℕ → Compacts X) (S : ℕ → Set X) (hKS : ∀ n, (K n : Set X) ⊆ S n)
    (L : Compacts X) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ht : Tendsto (K ∘ φ) atTop (𝓝 L)) : (L : Set X) ⊆ upperSetLimit S := by
  intro x hx
  apply mem_iInter.mpr
  intro N
  have hN : ∀ᶠ n in atTop, N ≤ φ n :=
    hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
  have hev : ∀ᶠ n in atTop, (K (φ n) : Set X) ⊆
      closure (⋃ m : ℕ, ⋃ (_h : N ≤ m), S m) := by
    filter_upwards [hN] with n hn
    intro y hy
    exact subset_closure (mem_iUnion.mpr ⟨φ n, mem_iUnion.mpr ⟨hn, hKS _ hy⟩⟩)
  exact (Compacts.isClosed_subsets_of_isClosed isClosed_closure).mem_of_tendsto ht hev hx

omit [T2Space X] [NormalSpace X] in
theorem isClosed_upperSetLimit (S : ℕ → Set X) : IsClosed (upperSetLimit S) :=
  isClosed_iInter (fun _ => isClosed_closure)

omit [T2Space X] [NormalSpace X] in
/-- A closed set eventually containing every set also contains the upper limit. -/
theorem upperSetLimit_subset_of_eventually_subset_closed (S : ℕ → Set X)
    {C : Set X} (hC : IsClosed C) (hSC : ∀ᶠ n in atTop, S n ⊆ C) :
    upperSetLimit S ⊆ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSC
  intro x hx
  apply closure_minimal ?_ hC (mem_iInter.mp hx N)
  rintro y hy
  obtain ⟨n, hn⟩ := mem_iUnion.mp hy
  obtain ⟨hn, hy⟩ := mem_iUnion.mp hn
  exact hN n hn hy

omit [T2Space X] [NormalSpace X] in
/-- A continuous coordinate constant on each moving set takes its limiting
value on the upper set limit. -/
theorem upperSetLimit_subset_continuous_fiber {Y : Type*} [MetricSpace Y]
    (S : ℕ → Set X) (f : X → Y) (hf : Continuous f)
    (c : ℕ → Y) (a : Y) (hc : Tendsto c atTop (𝓝 a))
    (hSc : ∀ n x, x ∈ S n → f x = c n) :
    upperSetLimit S ⊆ {x | f x = a} := by
  intro x hx
  by_contra hn
  have hpos : 0 < dist (f x) a := dist_pos.mpr hn
  have he : ∀ᶠ n in atTop, c n ∈ Metric.ball a (dist (f x) a / 2) :=
    hc.eventually (Metric.ball_mem_nhds a (half_pos hpos))
  have hbound : upperSetLimit S ⊆ f ⁻¹' Metric.closedBall a (dist (f x) a / 2) := by
    apply upperSetLimit_subset_of_eventually_subset_closed S
      (Metric.isClosed_closedBall.preimage hf)
    filter_upwards [he] with n hn'
    intro y hy
    change dist (f y) a ≤ dist (f x) a / 2
    rw [hSc n y hy]
    exact le_of_lt hn'
  have hle : dist (f x) a ≤ dist (f x) a / 2 := hbound hx
  linarith

omit [T2Space X] [NormalSpace X] in
theorem upperSetLimit_contains_limit_point (S : ℕ → Set X) (x : ℕ → X) (p : X)
    (hx : Tendsto x atTop (𝓝 p)) (hmem : ∀ n, x n ∈ S n) : p ∈ upperSetLimit S := by
  apply mem_iInter.mpr
  intro N
  apply isClosed_closure.mem_of_tendsto hx
  filter_upwards [eventually_ge_atTop N] with n hn
  exact subset_closure (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, hmem n⟩⟩)

end JSP400
