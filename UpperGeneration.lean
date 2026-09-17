import UpperUnipotentCompact
import Mathlib.Algebra.Group.Subgroup.Lattice

namespace JSP400

theorem upperUnipotent_inv (a b c : ℝ) :
    (upperUnipotent a b c)⁻¹ = upperUnipotent (-a) (a * c - b) (-c) := by
  apply inv_eq_of_mul_eq_one_left
  rw [upperUnipotent_mul]
  convert upperUnipotent_zero using 1
  congr 1 <;> ring

/-- The actual full upper-unitriangular subgroup W. -/
def upperGroup : Subgroup SL3 where
  carrier := {g | ∃ a b c : ℝ, g = upperUnipotent a b c}
  one_mem' := ⟨0, 0, 0, upperUnipotent_zero.symm⟩
  mul_mem' := by
    rintro g h ⟨a, b, c, rfl⟩ ⟨x, y, z, rfl⟩
    exact ⟨a + x, b + y + a * z, c + z, upperUnipotent_mul a b c x y z⟩
  inv_mem' := by
    rintro g ⟨a, b, c, rfl⟩
    exact ⟨-a, a * c - b, -c, upperUnipotent_inv a b c⟩

theorem upperGroup_le_of_nonnegative_half (S : Subgroup SL3)
    (hS : ∀ a b c : ℝ, 0 ≤ a - c → upperUnipotent a b c ∈ S) : upperGroup ≤ S := by
  rintro g ⟨a, b, c, rfl⟩
  by_cases h : 0 ≤ a - c
  · exact hS a b c h
  · have hi := S.inv_mem (hS (-a) (a * c - b) (-c) (by linarith))
    rwa [← upperUnipotent_inv, inv_inv] at hi

theorem upperGroup_le_of_nonpositive_half (S : Subgroup SL3)
    (hS : ∀ a b c : ℝ, a - c ≤ 0 → upperUnipotent a b c ∈ S) : upperGroup ≤ S := by
  rintro g ⟨a, b, c, rfl⟩
  by_cases h : a - c ≤ 0
  · exact hS a b c h
  · have hi := S.inv_mem (hS (-a) (a * c - b) (-c) (by linarith))
    rwa [← upperUnipotent_inv, inv_inv] at hi

/-- Either closed half of W generates the entire group. `Subgroup.closure`
here is the algebraically generated subgroup, so no topological closure or
Lie-theoretic assumption is hidden in the conclusion. -/
theorem generated_upper_inter_eq_of_half (A : Set SL3)
    (hA : (∀ a b c : ℝ, 0 ≤ a - c → upperUnipotent a b c ∈ A) ∨
      (∀ a b c : ℝ, a - c ≤ 0 → upperUnipotent a b c ∈ A)) :
    Subgroup.closure ((upperGroup : Set SL3) ∩ A) = upperGroup := by
  apply le_antisymm
  · exact (Subgroup.closure_le upperGroup).mpr (fun g hg => hg.1)
  · rcases hA with h | h
    · apply upperGroup_le_of_nonnegative_half
      intro a b c hac
      exact Subgroup.subset_closure ⟨⟨a, b, c, rfl⟩, h a b c hac⟩
    · apply upperGroup_le_of_nonpositive_half
      intro a b c hac
      exact Subgroup.subset_closure ⟨⟨a, b, c, rfl⟩, h a b c hac⟩

end JSP400
