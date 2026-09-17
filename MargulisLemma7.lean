import GramClosureLift

namespace JSP400

open Matrix Set

/-- Margulis Lemma 7 for the actual matrix groups. The ordinary closure of
H M D V₁ contains one full one-sided V₂ subgroup when M avoids H and approaches
the identity. The stronger closed rays include the identity. -/
theorem margulis_lemma7 (M : Set SL3)
    (hbase : (1 : SL3) ∈ closure M)
    (hout : ∀ g ∈ M, g ∉ formStabilizer standardForm) :
    (∀ t : ℝ, 0 ≤ t → unipotentTwo t ∈ closure (lemma7Hull M)) ∨
      (∀ t : ℝ, t ≤ 0 → unipotentTwo t ∈ closure (lemma7Hull M)) := by
  by_cases hf : ∃ m ∈ M, gramMatrix m ∈ gramFlag 2
  · obtain ⟨m, hm, hfixed⟩ := hf
    exact lemma7_fixed_case M hbase hout m hm hfixed
  · have hnot : ∀ q ∈ gramMatrix '' M, q ∉ gramFlag 2 := by
      rintro q ⟨m, hm, rfl⟩ hq
      exact hf ⟨m, hm, hq⟩
    have hb : standardGram ∈ closure (gramMatrix '' M) := by
      simpa only [gramMatrix_one] using
        mem_closure_image continuous_gramMatrix.continuousAt hbase
    have hsymm : ∀ q ∈ gramMatrix '' M, q.IsSymm := by
      rintro q ⟨m, hm, rfl⟩
      exact gramMatrix_isSymm m
    have hdet : ∀ q ∈ gramMatrix '' M, q.det = 1 := by
      rintro q ⟨m, hm, rfl⟩
      exact gramMatrix_det m
    rcases gram_orbit_closure_contains_ray (gramMatrix '' M) hsymm hdet hnot hb with h | h
    · exact Or.inl (fun t ht => unipotentTwo_mem_closure_hull_of_gram M t
        (h ⟨2 * t, by change 0 ≤ 2 * t; positivity, rfl⟩))
    · exact Or.inr (fun t ht => unipotentTwo_mem_closure_hull_of_gram M t
        (h ⟨2 * t, by change 2 * t ≤ 0; linarith, rfl⟩))

end JSP400

#print axioms JSP400.margulis_lemma7
