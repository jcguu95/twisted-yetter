import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.Data.Fintype.Sigma
import TwistedYetter.Fusion.EGNOTraceCyclicity
import TwistedYetter.Fusion.Insertion

/-!
# A finite semisimple fusion-category interface

EGNO Definition 4.1.1 defines a fusion category over an algebraically closed
field as a finite semisimple tensor category.  The ambient Lean assumptions in
this file record the linear, abelian, rigid, and bilinear monoidal parts.
`FusionCategoryData` records the remaining finite semisimple content:

* a finite, duplicate-free, complete list of simple representatives;
* an explicit finite biproduct decomposition of every object;
* the tensor unit as one of the simple representatives, the finite-semisimple
  form of EGNO's `End(𝟙) ≅ K` condition;
* closure of the representative list under the selected right dual.

The decomposition is an actual categorical isomorphism, not a family name or
a numerical fusion table.  Schur's lemma then derives the scalar
identification `End(𝟙) ≃ K`; it is not an arbitrary evaluator field.
-/

namespace TwistedYetter.Fusion.EGNO

open scoped BigOperators
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.Insertion

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance abelianHasFiniteBiproducts :
    HasFiniteBiproducts C :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/--
Proof-relevant finite semisimple data for an EGNO fusion category.

The ambient assumptions carry the algebraically closed field, abelian linear
category, rigid monoidal structure, and bilinearity of tensor product.  This
structure supplies a finite skeleton of all simple isomorphism classes and
explicit decompositions.
-/
structure FusionCategoryData where
  simple : S → C
  simple_isSimple : (s : S) → Simple (simple s)
  simple_pairwise :
    {s t : S} → Nonempty (simple s ≅ simple t) → s = t
  simple_complete :
    (X : C) → Simple X → ∃ s, Nonempty (X ≅ simple s)
  hom_finite :
    (X Y : C) → FiniteDimensional K (X ⟶ Y)
  multiplicity : C → S → ℕ
  decomposition :
    (X : C) →
      (⨁ fun p : Σ s, Fin (multiplicity X s) => simple p.1) ≅ X
  unitIndex : S
  unitIso : simple unitIndex ≅ 𝟙_ C
  dualIndex : S → S
  dualIso : (s : S) → (simple s)ᘁ ≅ simple (dualIndex s)

namespace FusionCategoryData

variable (data : FusionCategoryData (K := K) (C := C) (S := S))

/-- The finite type indexing all simple summands in the chosen decomposition. -/
abbrev SummandIndex (X : C) : Type :=
  Σ s, Fin (data.multiplicity X s)

/-- The object attached to one summand index. -/
abbrev summand (X : C) (p : data.SummandIndex X) : C :=
  data.simple p.1

/-- The stored biproduct decomposition, with its source written by name. -/
def decompositionIso (X : C) :
    (⨁ data.summand X) ≅ X :=
  data.decomposition X

omit [IsAlgClosed K] [MonoidalPreadditive C] [MonoidalLinear K C]
  [DecidableEq S] in
/-- Every listed representative is genuinely simple. -/
theorem simple_is_simple (s : S) : Simple (data.simple s) :=
  data.simple_isSimple s

omit [IsAlgClosed K] [MonoidalPreadditive C] [MonoidalLinear K C]
  [DecidableEq S] in
/-- Every simple object is isomorphic to one of the listed representatives. -/
theorem everySimple_is_represented
    (X : C) [Simple X] :
    ∃ s, Nonempty (X ≅ data.simple s) :=
  data.simple_complete X inferInstance

omit [IsAlgClosed K] [MonoidalPreadditive C] [MonoidalLinear K C]
  [DecidableEq S] in
/-- Two listed simple representatives are isomorphic exactly when their indices agree. -/
theorem simple_iso_iff_eq (s t : S) :
    Nonempty (data.simple s ≅ data.simple t) ↔ s = t := by
  constructor
  · exact data.simple_pairwise
  · intro h
    subst h
    exact ⟨Iso.refl _⟩

omit [IsAlgClosed K] [MonoidalPreadditive C] [MonoidalLinear K C]
  [DecidableEq S] in
include data in
/-- The selected tensor unit is simple because it is isomorphic to a listed simple. -/
theorem unit_isSimple : Simple (𝟙_ C) := by
  letI : Simple (data.simple data.unitIndex) :=
    data.simple_isSimple data.unitIndex
  exact Simple.of_iso data.unitIso.symm

omit [IsAlgClosed K] [MonoidalPreadditive C] [MonoidalLinear K C]
  [DecidableEq S] in
/-- The selected right dual of a listed simple is represented by `dualIndex`. -/
theorem dual_is_represented (s : S) :
    Nonempty ((data.simple s)ᘁ ≅ data.simple (data.dualIndex s)) :=
  ⟨data.dualIso s⟩

/-- The multiplicity of `c` in the tensor product of representatives `a` and `b`. -/
def fusionMultiplicity (a b c : S) : ℕ :=
  data.multiplicity (data.simple a ⊗ data.simple b) c

/-- The stored semisimple decomposition specialized to a tensor product. -/
def tensorDecomposition (a b : S) :
    (⨁ fun p : Σ c, Fin (data.fusionMultiplicity a b c) =>
      data.simple p.1) ≅
      data.simple a ⊗ data.simple b :=
  data.decomposition (data.simple a ⊗ data.simple b)

omit [MonoidalPreadditive C] [MonoidalLinear K C] in
/-- Schur's lemma computes every Hom dimension between listed simples. -/
theorem simpleHom_finrank (s t : S) :
    Module.finrank K (data.simple s ⟶ data.simple t) =
      if s = t then 1 else 0 := by
  letI : Simple (data.simple s) := data.simple_isSimple s
  letI : Simple (data.simple t) := data.simple_isSimple t
  letI : ∀ X Y : C, FiniteDimensional K (X ⟶ Y) :=
    data.hom_finite
  rw [CategoryTheory.finrank_hom_simple_simple K]
  simp only [data.simple_iso_iff_eq]

/-- Scalar multiplication of the identity as a linear map into endomorphisms. -/
def scalarEndLinearMap (X : C) : K →ₗ[K] (X ⟶ X) where
  toFun scalar := scalar • 𝟙 X
  map_add' left right := by simp [add_smul]
  map_smul' left right := by simp [mul_smul]

omit [IsAlgClosed K] [MonoidalCategory C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear K C] in
/-- On a simple object, the scalar endomorphism map is injective. -/
theorem scalarEndLinearMap_injective
    (X : C) [Simple X] :
    Function.Injective (scalarEndLinearMap (K := K) X) := by
  intro left right equality
  change left • 𝟙 X = right • 𝟙 X at equality
  have zero_smul :
      (left - right) • 𝟙 X = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr equality
  by_contra not_equal
  exact
    (smul_ne_zero (sub_ne_zero.mpr not_equal) (CategoryTheory.id_nonzero X))
      zero_smul

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
include data in
/-- On a simple object, Schur's lemma makes every endomorphism scalar. -/
theorem scalarEndLinearMap_surjective
    (X : C) [Simple X] :
    Function.Surjective (scalarEndLinearMap (K := K) X) := by
  letI : FiniteDimensional K (X ⟶ X) := data.hom_finite X X
  intro f
  obtain ⟨scalar, scalar_sound⟩ :=
    CategoryTheory.endomorphism_simple_eq_smul_id K f
  exact ⟨scalar, scalar_sound⟩

include data in
/--
Canonical scalar identification for the endomorphisms of any simple object.

This is derived from Schur's lemma over the algebraically closed field `K`.
-/
noncomputable def simpleEndLinearEquiv
    (X : C) [Simple X] :
    K ≃ₗ[K] (X ⟶ X) :=
  LinearEquiv.ofBijective
    (scalarEndLinearMap (K := K) X)
    ⟨scalarEndLinearMap_injective (K := K) X,
      data.scalarEndLinearMap_surjective X⟩

include data in
/-- The EGNO condition `End(𝟙) ≅ K`, derived from simplicity of the unit. -/
noncomputable def unitEndLinearEquiv :
    K ≃ₗ[K] (𝟙_ C ⟶ 𝟙_ C) := by
  letI : Simple (𝟙_ C) := data.unit_isSimple
  exact data.simpleEndLinearEquiv (𝟙_ C)

include data in
/-- Scalarization of a closed categorical morphism. -/
noncomputable def closedScalar (f : 𝟙_ C ⟶ 𝟙_ C) : K :=
  data.unitEndLinearEquiv.symm f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Scalarization sends the identity of the tensor unit to `1`. -/
theorem closedScalar_identity :
    data.closedScalar (𝟙 (𝟙_ C)) = 1 := by
  apply data.unitEndLinearEquiv.injective
  simp [closedScalar, unitEndLinearEquiv, simpleEndLinearEquiv,
    scalarEndLinearMap]

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Scalarization is additive. -/
theorem closedScalar_add
    (left right : 𝟙_ C ⟶ 𝟙_ C) :
    data.closedScalar (left + right) =
      data.closedScalar left + data.closedScalar right :=
  data.unitEndLinearEquiv.symm.map_add left right

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Scalarization is `K`-linear. -/
theorem closedScalar_smul
    (scalar : K)
    (f : 𝟙_ C ⟶ 𝟙_ C) :
    data.closedScalar (scalar • f) =
      scalar * data.closedScalar f := by
  simpa only [smul_eq_mul] using
    data.unitEndLinearEquiv.symm.map_smul scalar f

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Scalarization carries composition of closed morphisms to multiplication. -/
theorem closedScalar_comp
    (left right : 𝟙_ C ⟶ 𝟙_ C) :
    data.closedScalar (left ≫ right) =
      data.closedScalar left * data.closedScalar right := by
  have scalar_sound (f : 𝟙_ C ⟶ 𝟙_ C) :
      data.closedScalar f • 𝟙 (𝟙_ C) = f := by
    change
      data.unitEndLinearEquiv (data.unitEndLinearEquiv.symm f) = f
    exact data.unitEndLinearEquiv.apply_symm_apply f
  let leftScalar := data.closedScalar left
  let rightScalar := data.closedScalar right
  have left_sound :
      leftScalar • 𝟙 (𝟙_ C) = left :=
    scalar_sound left
  have right_sound :
      rightScalar • 𝟙 (𝟙_ C) = right :=
    scalar_sound right
  calc
    data.closedScalar (left ≫ right) =
        data.closedScalar
          ((leftScalar • 𝟙 (𝟙_ C)) ≫
            (rightScalar • 𝟙 (𝟙_ C))) := by
          rw [left_sound, right_sound]
    _ = data.closedScalar
          ((leftScalar * rightScalar) • 𝟙 (𝟙_ C)) := by
          congr 1
          simp [mul_comm, ← mul_smul]
    _ = leftScalar * rightScalar := by
          rw [closedScalar_smul, closedScalar_identity, mul_one]
    _ = data.closedScalar left * data.closedScalar right := rfl

/--
Projection from an object to one selected simple summand of its decomposition.
-/
noncomputable def projection (X : C) (p : data.SummandIndex X) :
    X ⟶ data.summand X p :=
  (data.decompositionIso X).inv ≫ biproduct.π (data.summand X) p

/--
Inclusion of one selected simple summand into the decomposed object.
-/
noncomputable def inclusion (X : C) (p : data.SummandIndex X) :
    data.summand X p ⟶ X :=
  biproduct.ι (data.summand X) p ≫ (data.decompositionIso X).hom

omit [IsAlgClosed K] [MonoidalPreadditive C] [MonoidalLinear K C]
  [DecidableEq S] in
/-- The stored decomposition gives an exact finite resolution of the identity. -/
theorem sum_projection_inclusion (X : C) :
    ∑ p : data.SummandIndex X,
        data.projection X p ≫ data.inclusion X p =
      𝟙 X := by
  simp only [projection, inclusion, Category.assoc]
  rw [← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp]
  rw [biproduct.total]
  simp

/--
The finite biproduct decomposition, exposed in the older identity-resolution
interface with unit weights.
-/
noncomputable def identityResolution (X : C) :
    IdentityResolution
      (R := K)
      (S := S)
      (I := fun s => Fin (data.multiplicity X s))
      X where
  simple := data.simple
  weight := fun _ => 1
  projection s i := data.projection X ⟨s, i⟩
  inclusion s i := data.inclusion X ⟨s, i⟩
  sound := by
    simp only [one_smul]
    rw [← Fintype.sum_sigma']
    exact data.sum_projection_inclusion X
  source_ref := "ref:egno-tensor-categories-2015"
  source_locator := "Definition 4.1.1, printed page 65"

/-- The exact identity resolution specialized to a tensor product of simples. -/
noncomputable def tensorIdentityResolution (a b : S) :
    IdentityResolution
      (R := K)
      (S := S)
      (I := fun c => Fin (data.fusionMultiplicity a b c))
      (data.simple a ⊗ data.simple b) :=
  data.identityResolution (data.simple a ⊗ data.simple b)

end FusionCategoryData

section Ribbon

variable [BraidedCategory C]

/--
The finite semisimple data and ribbon structure bound to one category.

All pivotal, spherical, trace, and dimension data below are derived; none are
additional fields.
-/
structure RibbonFusionCategoryData
    extends FusionCategoryData (K := K) (C := C) (S := S) where
  ribbon : RibbonStructure C

namespace RibbonFusionCategoryData

variable (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))

/-- The Step 3 canonical pivotal structure of the recorded ribbon structure. -/
def pivotal : PivotalStructure C :=
  canonicalPivotalStructure data.ribbon

/-- The Step 4 canonical spherical structure of the recorded ribbon structure. -/
def spherical : SphericalStructure (C := C) :=
  canonicalSphericalStructure data.ribbon

/-- The Step 5 trace-cyclicity package of the canonical spherical structure. -/
def traceLaws : SphericalTraceLaws data.spherical :=
  canonicalSphericalTraceLaws data.ribbon

/-- The categorical pivotal dimension of one simple representative. -/
def categoricalDimension (s : S) :
    𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension data.pivotal (data.simple s)

/-- The scalar quantum dimension of one simple representative. -/
noncomputable def quantumDimension (s : S) : K :=
  data.toFusionCategoryData.closedScalar (data.categoricalDimension s)

end RibbonFusionCategoryData

end Ribbon

end TwistedYetter.Fusion.EGNO
