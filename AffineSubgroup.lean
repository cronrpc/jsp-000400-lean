import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Tactic

/-! Concrete positive affine transformations of the real line. -/

namespace JSP400.AffineClassification

noncomputable section

open Set Filter
open scoped Topology

abbrev PositiveAffine := {p : ℝ × ℝ // 0 < p.1}

def slope (g : PositiveAffine) : ℝ := g.val.1
def offset (g : PositiveAffine) : ℝ := g.val.2

instance : One PositiveAffine := ⟨⟨(1, 0), by norm_num⟩⟩
instance : Mul PositiveAffine := ⟨fun g h =>
  ⟨(slope g * slope h, offset g + slope g * offset h), mul_pos g.property h.property⟩⟩
instance : Inv PositiveAffine := ⟨fun g =>
  ⟨((slope g)⁻¹, -(slope g)⁻¹ * offset g), inv_pos.mpr g.property⟩⟩

instance : Group PositiveAffine where
  mul_assoc g h k := by
    apply Subtype.ext
    apply Prod.ext
    · change (slope g * slope h) * slope k = slope g * (slope h * slope k)
      ring
    · change (offset g + slope g * offset h) + (slope g * slope h) * offset k =
        offset g + slope g * (offset h + slope h * offset k)
      ring
  one_mul g := by
    apply Subtype.ext
    apply Prod.ext
    · change 1 * slope g = slope g
      exact one_mul _
    · change 0 + 1 * offset g = offset g
      ring
  mul_one g := by
    apply Subtype.ext
    apply Prod.ext
    · change slope g * 1 = slope g
      exact mul_one _
    · change offset g + slope g * 0 = offset g
      ring
  inv_mul_cancel g := by
    apply Subtype.ext
    apply Prod.ext
    · change (slope g)⁻¹ * slope g = 1
      exact inv_mul_cancel₀ (ne_of_gt g.property)
    · change -(slope g)⁻¹ * offset g + (slope g)⁻¹ * offset g = 0
      ring

@[simp] theorem slope_one : slope (1 : PositiveAffine) = 1 := rfl
@[simp] theorem offset_one : offset (1 : PositiveAffine) = 0 := rfl
@[simp] theorem slope_mul (g h : PositiveAffine) : slope (g * h) = slope g * slope h := rfl
@[simp] theorem offset_mul (g h : PositiveAffine) :
    offset (g * h) = offset g + slope g * offset h := rfl
@[simp] theorem slope_inv (g : PositiveAffine) : slope g⁻¹ = (slope g)⁻¹ := rfl
@[simp] theorem offset_inv (g : PositiveAffine) : offset g⁻¹ = -(slope g)⁻¹ * offset g := rfl

theorem ext {g h : PositiveAffine} (ha : slope g = slope h) (hb : offset g = offset h) : g = h :=
  Subtype.ext (Prod.ext ha hb)

theorem continuous_slope : Continuous slope := continuous_fst.comp continuous_subtype_val
theorem continuous_offset : Continuous offset := continuous_snd.comp continuous_subtype_val

instance : IsTopologicalGroup PositiveAffine where
  continuous_mul := by
    apply Continuous.subtype_mk
    exact ((continuous_slope.comp continuous_fst).mul
      (continuous_slope.comp continuous_snd)).prodMk
        ((continuous_offset.comp continuous_fst).add
          ((continuous_slope.comp continuous_fst).mul (continuous_offset.comp continuous_snd)))
  continuous_inv := by
    apply Continuous.subtype_mk
    have hi := continuous_slope.inv₀ (fun g => ne_of_gt g.property)
    exact hi.prodMk (hi.neg.mul continuous_offset)

def translation (b : ℝ) : PositiveAffine := ⟨(1, b), by norm_num⟩
def dilation (a : ℝ) (ha : 0 < a) : PositiveAffine := ⟨(a, 0), ha⟩
def fixedDilation (r a : ℝ) (ha : 0 < a) : PositiveAffine := ⟨(a, (1 - a) * r), ha⟩

@[simp] theorem slope_translation (b : ℝ) : slope (translation b) = 1 := rfl
@[simp] theorem offset_translation (b : ℝ) : offset (translation b) = b := rfl

theorem translation_zero : translation 0 = 1 := rfl
theorem translation_add (b c : ℝ) : translation (b + c) = translation b * translation c := by
  apply ext <;> simp

theorem translation_neg (b : ℝ) : translation (-b) = (translation b)⁻¹ := by
  apply ext <;> simp

theorem continuous_translation : Continuous translation := by
  apply Continuous.subtype_mk
  exact continuous_const.prodMk continuous_id

def translations (K : Subgroup PositiveAffine) : AddSubgroup ℝ where
  carrier := {b | translation b ∈ K}
  zero_mem' := K.one_mem
  add_mem' := by
    intro b c hb hc
    change translation (b + c) ∈ K
    rw [translation_add]
    exact K.mul_mem hb hc
  neg_mem' := by
    intro b hb
    change translation (-b) ∈ K
    rw [translation_neg]
    exact K.inv_mem hb

theorem isClosed_translations (K : Subgroup PositiveAffine) (hK : IsClosed (K : Set PositiveAffine)) :
    IsClosed (translations K : Set ℝ) := hK.preimage continuous_translation

theorem conjugate_translation (g : PositiveAffine) (b : ℝ) :
    g * translation b * g⁻¹ = translation (slope g * b) := by
  apply ext
  · simp only [slope_mul, slope_inv, slope_translation, mul_one]
    exact mul_inv_cancel₀ (ne_of_gt g.property)
  · simp only [offset_mul, offset_inv, slope_mul, slope_translation, offset_translation]
    have ha : slope g ≠ 0 := ne_of_gt g.property
    field_simp
    ring

theorem commutator_translation (g h : PositiveAffine) :
    g * h * g⁻¹ * h⁻¹ =
      translation ((1 - slope h) * offset g - (1 - slope g) * offset h) := by
  apply ext
  · simp only [slope_mul, slope_inv, slope_translation]
    have ha : slope g ≠ 0 := ne_of_gt g.property
    have hb : slope h ≠ 0 := ne_of_gt h.property
    field_simp
  · simp only [offset_mul, offset_inv, slope_mul, slope_inv,
      offset_translation]
    have ha : slope g ≠ 0 := ne_of_gt g.property
    have hb : slope h ≠ 0 := ne_of_gt h.property
    field_simp
    ring

end
end JSP400.AffineClassification
