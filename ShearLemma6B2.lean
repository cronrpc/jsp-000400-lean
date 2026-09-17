import ShearDescent
import ShearOrbitClosure
import ShearFixedRays

namespace JSP400

open Matrix Set

/-- Margulis §8, assertion (B2), with the genuine nilpotent cone, affine
hyperplane, adjoint action and Euclidean closure. The proof supplies the
complete finite-dimensional descent rather than assuming Lemma 12. -/
theorem margulis_lemma6_B2
    (Y : Set (Matrix (Fin 3) (Fin 3) ℝ))
    (hentry : ∀ x ∈ Y, x 0 1 = 1)
    (hnil : ∀ x ∈ Y, IsNilpotent x)
    (hnot : ∀ x ∈ Y, x ∉ shearLieAlgebra)
    (hbase : shearFixedLine 0 ∈ closure Y) :
    shearFixedLine '' Ici 0 ⊆ closure (shearOrbitUnion Y) ∨
      shearFixedLine '' Iic 0 ⊆ closure (shearOrbitUnion Y) := by
  let A := closure (shearOrbitUnion Y)
  let p := shearFixedLine 0
  have hYA : Y ⊆ A := (subset_shearOrbitUnion Y).trans subset_closure
  have hpA : p ∈ A := closure_mono (subset_shearOrbitUnion Y) hbase
  have hpLie : p ∈ shearLieAlgebra := ⟨1, 0, rfl⟩
  have hpD : p ∈ shearFixedDomain A := ⟨hpA, hpLie, rfl⟩
  have hYlayer : Y ⊆ shearLayer A 8 \ shearLieAlgebra := by
    intro x hx
    exact ⟨⟨hYA hx, (mem_shearFlag_eight x).mpr
      (nilpotent_matrix_trace_zero (hnil x hx)), hentry x hx⟩, hnot x hx⟩
  have hcl : p ∈ closure (shearLayer A 8 \ shearLieAlgebra) := closure_mono hYlayer hbase
  have hnoncompact := shear_fixed_component_noncompact_of_layer A isClosed_closure
    (closure_shearOrbitUnion_nilpotent Y hnil)
    (fun x hx s t => closure_shearOrbitUnion_invariant Y hx s t)
    6 (by decide) p hpD hcl
  let C := connectedComponentIn (shearFixedDomain A) p
  have hCclosed : IsClosed C := by
    apply closure_subset_iff_isClosed.mp
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hpD))
      (closure_minimal (connectedComponentIn_subset _ _) (isClosed_shearFixedDomain A isClosed_closure))
  have hCline : C ⊆ Set.range shearFixedLine := by
    intro x hx
    have hd := connectedComponentIn_subset (shearFixedDomain A) p hx
    rw [← shear_lieAlgebra_slice_eq_line]
    exact ⟨hd.2.1, hd.2.2⟩
  have hCA : C ⊆ A := fun x hx => (connectedComponentIn_subset (shearFixedDomain A) p hx).1
  rcases shear_fixed_line_contains_ray C hCclosed isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hpD) hnoncompact hCline with h | h
  · exact Or.inl (h.trans hCA)
  · exact Or.inr (h.trans hCA)

end JSP400

#print axioms JSP400.margulis_lemma6_B2
