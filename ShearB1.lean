import ShearLemma6B2
import ShearNormalization

/-! The normalization reduction from Margulis Lemma 6(B1) to (B2).
Localizing the original set is essential: normalization factors must tend to one.
-/

namespace JSP400

open Matrix Set Filter
open scoped Topology

private theorem shearOrbitUnion_mono {Y Z : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (h : Y ⊆ Z) : shearOrbitUnion Y ⊆ shearOrbitUnion Z := by
  rintro x ⟨y, hy, s, t, rfl⟩
  exact ⟨y, h hy, s, t, rfl⟩

private theorem normalizedShearSet_mono {Y Z : Set (Matrix (Fin 3) (Fin 3) ℝ)}
    (h : Y ⊆ Z) : normalizedShearSet Y ⊆ normalizedShearSet Z :=
  image_mono (inter_subset_inter_left _ h)

/-- A point missing from the original orbit closure also misses the normalized
orbit closure after restricting sources to a sufficiently small neighborhood
of the base point. -/
theorem missing_point_local_normalization
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (q : Matrix (Fin 3) (Fin 3) ℝ) (hq : q ∉ closure (shearOrbitUnion Y)) :
    ∃ O : Set (Matrix (Fin 3) (Fin 3) ℝ), IsOpen O ∧ shearFixedLine 0 ∈ O ∧
      q ∉ closure (shearOrbitUnion (normalizedShearSet (Y ∩ O))) := by
  have hcont : Continuous (fun z : ℝ × Matrix (Fin 3) (Fin 3) ℝ => z.1 • z.2) := by
    fun_prop
  have hnh : (fun z : ℝ × Matrix (Fin 3) (Fin 3) ℝ => z.1 • z.2) ⁻¹'
      (closure (shearOrbitUnion Y))ᶜ ∈ 𝓝 ((1 : ℝ), q) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using isClosed_closure.isOpen_compl.mem_nhds hq
  obtain ⟨U, V, hU, h1U, hV, hqV, hUV⟩ := mem_nhds_prod_iff'.mp hnh
  let O : Set (Matrix (Fin 3) (Fin 3) ℝ) := {x | x 0 1 ∈ U}
  have hO : IsOpen O := hU.preimage (by fun_prop)
  refine ⟨O, hO, h1U, ?_⟩
  intro hqcl
  obtain ⟨z, hzV, hz⟩ := mem_closure_iff_nhds.mp hqcl V (hV.mem_nhds hqV)
  obtain ⟨x, hx, s, t, rfl⟩ := hz
  obtain ⟨y, ⟨⟨hyY, hyO⟩, hyne⟩, rfl⟩ := hx
  have hyU : y 0 1 ∈ U := hyO
  have hmissing : y 0 1 • shearConjugate (shearNormalize y) s t ∉
      closure (shearOrbitUnion Y) := hUV
        (show (y 0 1, shearConjugate (shearNormalize y) s t) ∈ U ×ˢ V from ⟨hyU, hzV⟩)
  rw [← shearConjugate_recover_from_normalization y hyne s t] at hmissing
  exact hmissing (subset_closure ⟨y, hyY, s, t, rfl⟩)

/-- Margulis §8, assertion (B1), in the stronger form allowing every nilpotent
source set. The actual adjoint orbit of x₀ is contained in this cone. -/
theorem margulis_lemma6_B1
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hnil : ∀ x ∈ Y, IsNilpotent x)
    (hnot : ∀ x ∈ Y, x ∉ shearLieAlgebra)
    (hbase : shearFixedLine 0 ∈ closure Y) :
    shearFixedLine '' Ici 0 ⊆ closure (shearOrbitUnion Y) ∨
      shearFixedLine '' Iic 0 ⊆ closure (shearOrbitUnion Y) := by
  by_contra h
  obtain ⟨hplus, hminus⟩ := not_or.mp h
  obtain ⟨q, hqray, hq⟩ := Set.not_subset.mp hplus
  obtain ⟨r, hrray, hr⟩ := Set.not_subset.mp hminus
  obtain ⟨O, hO, hpO, hqO⟩ := missing_point_local_normalization Y q hq
  obtain ⟨P, hP, hpP, hrP⟩ := missing_point_local_normalization Y r hr
  let Z := Y ∩ (O ∩ P)
  have hZY : Z ⊆ Y := inter_subset_left
  have hZcl : shearFixedLine 0 ∈ closure Z :=
    (hO.inter hP).closure_inter ⟨hbase, hpO, hpP⟩
  have hnormcl := mem_closure_normalizedShearSet Z (shearFixedLine 0) rfl hZcl
  have hprops := normalizedShearSet_properties Z
    (fun x hx => hnil x (hZY hx)) (fun x hx => hnot x (hZY hx))
  have hleft : closure (shearOrbitUnion (normalizedShearSet Z)) ⊆
      closure (shearOrbitUnion (normalizedShearSet (Y ∩ O))) :=
    closure_mono (shearOrbitUnion_mono (normalizedShearSet_mono
      (fun x hx => ⟨hx.1, hx.2.1⟩)))
  have hright : closure (shearOrbitUnion (normalizedShearSet Z)) ⊆
      closure (shearOrbitUnion (normalizedShearSet (Y ∩ P))) :=
    closure_mono (shearOrbitUnion_mono (normalizedShearSet_mono
      (fun x hx => ⟨hx.1, hx.2.2⟩)))
  rcases margulis_lemma6_B2 (normalizedShearSet Z)
    (fun x hx => (hprops x hx).1) (fun x hx => (hprops x hx).2.1)
    (fun x hx => (hprops x hx).2.2) hnormcl with hp | hm
  · exact hqO (hleft (hp hqray))
  · exact hrP (hright (hm hrray))

end JSP400
