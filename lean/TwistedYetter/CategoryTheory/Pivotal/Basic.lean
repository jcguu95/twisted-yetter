module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Pivotal and spherical structures

The definitions follow EGNO, Definitions 4.7.7, 4.7.11, and 4.7.14. Mathlib
provides the chosen duals and their action on morphisms. The monoidal structure
on the double-dual functor is an ambient parameter, following Mathlib's usual
design for monoidal functor structures; a pivotal structure cannot silently
choose a second, incompatible tensorator.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/-- The right double-dual endofunctor `X ↦ X**`. -/
public abbrev rightDoubleDualFunctor : C ⥤ C where
  obj X := (Xᘁ)ᘁ
  map f := (fᘁ)ᘁ
  map_id X := by simp
  map_comp f g := by simp only [comp_rightAdjointMate]

/-- The monoidality condition in EGNO, Definition 4.7.7. -/
def IsPivotalIso [(rightDoubleDualFunctor C).Monoidal]
    (iso : 𝟭 C ≅ rightDoubleDualFunctor C) : Prop :=
  NatTrans.IsMonoidal iso.hom

/-- A pivotal structure in the sense of EGNO, Definition 4.7.7. -/
structure PivotalStructure [(rightDoubleDualFunctor C).Monoidal] where
  iso : 𝟭 C ≅ rightDoubleDualFunctor C
  monoidal : IsPivotalIso C iso

/-- A rigid monoidal category equipped with a pivotal structure. -/
class PivotalCategory [(rightDoubleDualFunctor C).Monoidal] where
  pivotalStructure : PivotalStructure C

variable {C}

/--
Taking the selected right mate twice is conjugation by the pivotal
isomorphism.  This is the basic dual-functor identity used when transporting
simple-object arguments across right duality.
-/
theorem rightAdjointMate_rightAdjointMate
    [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C)
    {X Y : C} (f : X ⟶ Y) :
    (fᘁ)ᘁ =
      pivotal.iso.inv.app X ≫ f ≫ pivotal.iso.hom.app Y := by
  change
    (rightDoubleDualFunctor C).map f =
      pivotal.iso.inv.app X ≫ (𝟭 C).map f ≫ pivotal.iso.hom.app Y
  rw [← cancel_mono (pivotal.iso.inv.app Y)]
  rw [pivotal.iso.inv.naturality]
  have h := congrArg
    (fun q => pivotal.iso.inv.app X ≫ (𝟭 C).map f ≫ q)
    (pivotal.iso.hom_inv_id_app Y)
  simpa only [Category.assoc, Category.comp_id] using h.symm

/-- EGNO left categorical trace, equation (4.8), for `a : X ⟶ X**`. -/
def leftCategoricalTrace {X : C} (a : X ⟶ (Xᘁ)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫
    (a ⊗ₘ 𝟙 (Xᘁ)) ≫
    ε_ (Xᘁ) ((Xᘁ)ᘁ)

/-- The pivotal trace of an endomorphism, as in EGNO equation (8.40). -/
def pivotalTrace [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C)
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftCategoricalTrace (f ≫ pivotal.iso.hom.app X)

/-- EGNO, Definition 4.7.11: pivotal dimension. -/
def pivotalDimension [(rightDoubleDualFunctor C).Monoidal]
    (pivotal : PivotalStructure C) (X : C) :
    𝟙_ C ⟶ 𝟙_ C :=
  leftCategoricalTrace (pivotal.iso.hom.app X)

/--
A spherical structure in the sense of EGNO, Definition 4.7.14:
`dim(X) = dim(X*)` for every object.
-/
structure SphericalStructure [(rightDoubleDualFunctor C).Monoidal]
    extends PivotalStructure C where
  dimension_dual (X : C) :
    pivotalDimension toPivotalStructure X =
      pivotalDimension toPivotalStructure (Xᘁ)

/-- A rigid monoidal category equipped with a spherical structure. -/
class SphericalCategory [(rightDoubleDualFunctor C).Monoidal] where
  sphericalStructure : SphericalStructure (C := C)

end CategoryTheory
