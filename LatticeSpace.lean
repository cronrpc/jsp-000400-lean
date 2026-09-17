import FormStabilizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Normed.Group.Uniform

namespace JSP400

abbrev IntegerVector3 := Fin 3 → ℤ
abbrev IntegerSL3 := Matrix.SpecialLinearGroup (Fin 3) ℤ

/-- The standard coordinatewise embedding of the integer lattice. -/
def integerVector (v : IntegerVector3) : Vector3 := fun i => (v i : ℝ)

/-- The ordinary entrywise inclusion `SL(3,ℤ) → SL(3,ℝ)`. -/
def integerSLHom : IntegerSL3 →* SL3 :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)

/-- The arithmetic subgroup used in the homogeneous space. -/
def integerGamma : Subgroup SL3 := integerSLHom.range

theorem mem_integerGamma_iff (g : SL3) :
    g ∈ integerGamma ↔ ∀ i j, ∃ z : ℤ, (z : ℝ) = g.val i j := by
  constructor
  · rintro ⟨a, rfl⟩ i j
    exact ⟨a.val i j, rfl⟩
  · intro hg
    choose a ha using hg
    let A : Matrix (Fin 3) (Fin 3) ℤ := fun i j => a i j
    have hm : A.map (Int.castRingHom ℝ) = g.val := by
      ext i j
      exact ha i j
    have hdet : A.det = 1 := by
      have hd := congrArg Matrix.det hm
      change ((Int.castRingHom ℝ).mapMatrix A).det = g.val.det at hd
      rw [← (Int.castRingHom ℝ).map_det] at hd
      rw [g.property] at hd
      change ((A.det : ℤ) : ℝ) = 1 at hd
      exact_mod_cast hd
    refine ⟨⟨A, hdet⟩, ?_⟩
    apply Subtype.ext
    exact hm

theorem integerGamma_isClosed : IsClosed (integerGamma : Set SL3) := by
  have hset : (integerGamma : Set SL3) =
      ⋂ i : Fin 3, ⋂ j : Fin 3, {g : SL3 | g.val i j ∈ Set.range (Int.cast : ℤ → ℝ)} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_range]
    exact mem_integerGamma_iff g
  rw [hset]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact Real.isClosed_range_intCast.preimage
    ((continuous_apply j).comp
      (Matrix.SpecialLinearGroup.continuous_apply id continuous_id i))

instance : IsClosed (integerGamma : Set SL3) := integerGamma_isClosed

/-- The space `SL(3,ℝ)/SL(3,ℤ)` with its standard quotient topology and action. -/
abbrev LatticeSpace := SL3 ⧸ integerGamma

theorem integerSLHom_smul (g : IntegerSL3) (v : IntegerVector3) :
    integerSLHom g • integerVector v = integerVector (g • v) := by
  ext i
  change (∑ j : Fin 3, (g.val i j : ℝ) * (v j : ℝ)) =
    ((∑ j : Fin 3, g.val i j * v j : ℤ) : ℝ)
  simp

/-- The actual set of vectors in the unimodular lattice represented by `g`. -/
def latticePoints (g : SL3) : Set Vector3 :=
  Set.range (fun v : IntegerVector3 => g • integerVector v)

theorem latticePoints_mul_integer (g : SL3) (a : IntegerSL3) :
    latticePoints (g * integerSLHom a) = latticePoints g := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨a • v, ?_⟩
    simp only [mul_smul, integerSLHom_smul]
  · rintro ⟨v, rfl⟩
    refine ⟨a⁻¹ • v, ?_⟩
    simp only [mul_smul, integerSLHom_smul, smul_inv_smul]

theorem latticePoints_mul_gamma (g : SL3) {γ : SL3} (hγ : γ ∈ integerGamma) :
    latticePoints (g * γ) = latticePoints g := by
  obtain ⟨a, rfl⟩ := hγ
  exact latticePoints_mul_integer g a

/-- Equality of cosets gives equality of the actual lattice sets. -/
theorem latticePoints_eq_of_quotient_eq {g h : SL3}
    (heq : (QuotientGroup.mk g : LatticeSpace) = QuotientGroup.mk h) :
    latticePoints g = latticePoints h := by
  have hγ : g⁻¹ * h ∈ integerGamma := QuotientGroup.eq.mp heq
  have hp := latticePoints_mul_gamma g hγ
  simpa using hp.symm

/-- Vectors of a quotient lattice, independent of the representative. -/
def quotientLatticePoints : LatticeSpace → Set Vector3 :=
  Quotient.lift latticePoints (by
    intro g h hgh
    exact latticePoints_eq_of_quotient_eq (Quotient.sound hgh))

@[simp] theorem quotientLatticePoints_mk (g : SL3) :
    quotientLatticePoints (QuotientGroup.mk g) = latticePoints g := rfl

theorem latticePoints_left_mul (g h : SL3) :
    latticePoints (g * h) = (fun v : Vector3 => g • v) '' latticePoints h := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨h • integerVector v, ⟨v, rfl⟩, by simp only [mul_smul]⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v, by simp only [mul_smul]⟩

theorem mem_integerGamma_of_latticePoints_eq_one {g : SL3}
    (hg : latticePoints g = latticePoints 1) : g ∈ integerGamma := by
  apply (mem_integerGamma_iff g).mpr
  intro i j
  have hj : g • integerVector (Pi.single j 1) ∈ latticePoints g :=
    ⟨Pi.single j 1, rfl⟩
  rw [hg] at hj
  obtain ⟨v, hv⟩ := hj
  simp only [one_smul] at hv
  refine ⟨v i, ?_⟩
  have hi := congrFun hv i
  change (integerVector v) i = ((g : Matrix (Fin 3) (Fin 3) ℝ).mulVec
    (integerVector (Pi.single j 1))) i at hi
  simpa [integerVector, Matrix.mulVec, dotProduct, Pi.single_apply] using hi

/-- The converse uses the three standard basis vectors, forcing all columns
of the relative change of basis to be integral. -/
theorem quotient_eq_of_latticePoints_eq {g h : SL3}
    (heq : latticePoints g = latticePoints h) :
    (QuotientGroup.mk g : LatticeSpace) = QuotientGroup.mk h := by
  apply QuotientGroup.eq.mpr
  apply mem_integerGamma_of_latticePoints_eq_one
  calc
    latticePoints (g⁻¹ * h) =
        (fun v : Vector3 => g⁻¹ • v) '' latticePoints h := latticePoints_left_mul _ _
    _ = (fun v : Vector3 => g⁻¹ • v) '' latticePoints g := by rw [heq]
    _ = latticePoints (g⁻¹ * g) := (latticePoints_left_mul _ _).symm
    _ = latticePoints 1 := by rw [inv_mul_cancel]

/-- Different quotient lattices have different actual point sets. -/
theorem quotientLatticePoints_injective : Function.Injective quotientLatticePoints := by
  intro L M
  induction L using Quotient.inductionOn with
  | h g =>
    induction M using Quotient.inductionOn with
    | h h => exact quotient_eq_of_latticePoints_eq

/-- The homogeneous-space action really sends lattice vectors to their
matrix images. -/
theorem quotientLatticePoints_smul (g : SL3) (L : LatticeSpace) :
    quotientLatticePoints (g • L) =
      (fun v : Vector3 => g • v) '' quotientLatticePoints L := by
  induction L using Quotient.inductionOn with
  | h h => exact latticePoints_left_mul g h

end JSP400

#print axioms JSP400.quotientLatticePoints_smul
