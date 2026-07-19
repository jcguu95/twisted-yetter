import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Monoidal.Rigid.Functor

/-!
# EGNO pivotal, spherical, balancing, and ribbon structures

This module records the category structures used by the Kirby layer directly
from Etingof--Gelaki--Nikshych--Ostrik, *Tensor Categories*:

* Definition 4.7.7, page 74: pivotal structure;
* equations (4.8) and (8.40), pages 73 and 220: left pivotal trace;
* Definition 4.7.14, page 75: spherical structure;
* Definition 8.10.1, page 216: balancing and ribbon structure.

Mathlib v4.29.1 has rigid dual functors but deliberately leaves their monoidal
equivalence, pivotal categories, and spherical categories as future work.
Consequently the canonical monoidal structure on the double-dual functor is
explicit data here. Its compatibility with the pivotal natural isomorphism is
an actual `NatTrans.IsMonoidal` proposition, rather than an opaque boolean or
an untyped source claim.

The operational cyclicity statement is isolated in `SphericalTraceLaws`, so
the Kirby layer exposes exactly which theorem it consumes.  The separate
`EGNOTraceCyclicity` module constructs this structure from a pivotal structure
by a direct proof using mate identities and pivotal naturality.  No concrete
fusion category is selected in this module.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

section Pivotal

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/--
The right double-dual endofunctor `X ↦ X**`.

The underlying functor is available from Mathlib's chosen right duals, so this
definition deliberately asks only for `RightRigidCategory`. A
canonical monoidal structure exists mathematically, but is not yet supplied by
Mathlib v4.29.1.
-/
def rightDoubleDualFunctor : C ⥤ C where
  obj X := (Xᘁ)ᘁ
  map f := (fᘁ)ᘁ
  map_id X := by simp
  map_comp f g := by simp only [comp_rightAdjointMate]

/-- The precise monoidality condition in EGNO Definition 4.7.7. -/
def IsPivotalIso
    (doubleDualMonoidal : (rightDoubleDualFunctor C).Monoidal)
    (iso : 𝟭 C ≅ rightDoubleDualFunctor C) : Prop :=
  letI := doubleDualMonoidal
  NatTrans.IsMonoidal iso.hom

/--
A pivotal structure in the sense of EGNO Definition 4.7.7.

The field `doubleDualMonoidal` is a selected monoidal structure on `(**)`;
`monoidal` says that `iso : id_C ≅ (**)` is an isomorphism of monoidal
functors, not merely a natural isomorphism. The type alone cannot assert that
the selected structure agrees with an independently constructed
duality-induced standard structure. Any such identification must be recorded
by the construction or its source-bound characterization.
-/
structure PivotalStructure where
  doubleDualMonoidal : (rightDoubleDualFunctor C).Monoidal
  iso : 𝟭 C ≅ rightDoubleDualFunctor C
  monoidal : IsPivotalIso C doubleDualMonoidal iso

variable {C}

/-- EGNO left categorical trace, equation (4.8), for `a : X ⟶ X**`. -/
def leftCategoricalTrace {X : C} (a : X ⟶ (Xᘁ)ᘁ) :
    𝟙_ C ⟶ 𝟙_ C :=
  η_ X (Xᘁ) ≫
    (a ⊗ₘ 𝟙 (Xᘁ)) ≫
    ε_ (Xᘁ) ((Xᘁ)ᘁ)

/-- The pivotal trace of an endomorphism, as in EGNO equation (8.40). -/
def pivotalTrace (pivotal : PivotalStructure C)
    {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  leftCategoricalTrace (f ≫ pivotal.iso.hom.app X)

/-- EGNO Definition 4.7.11: pivotal dimension. -/
def pivotalDimension (pivotal : PivotalStructure C) (X : C) :
    𝟙_ C ⟶ 𝟙_ C :=
  leftCategoricalTrace (pivotal.iso.hom.app X)

/--
A spherical structure in the sense of EGNO Definition 4.7.14:
`dim(X) = dim(X*)` for every object.
-/
structure SphericalStructure extends PivotalStructure C where
  dimension_dual : (X : C) →
    pivotalDimension toPivotalStructure X =
      pivotalDimension toPivotalStructure (Xᘁ)

/--
The operational trace theorem used to move a cut around a closed component.

This interface keeps the source and the exact equation visible at the Kirby
boundary.  `EGNOTraceCyclicity.sphericalTraceLaws` derives it from the pivotal
structure using EGNO Proposition 4.7.3(4); callers do not supply the equality
by hand.
-/
structure SphericalTraceLaws
    (spherical : SphericalStructure (C := C)) where
  cyclic : {X Y : C} → (f : X ⟶ Y) → (g : Y ⟶ X) →
    pivotalTrace spherical.toPivotalStructure (f ≫ g) =
      pivotalTrace spherical.toPivotalStructure (g ≫ f)
  source_ref : String := "ref:egno-tensor-categories-2015"
  source_locator : String :=
    "Proposition 4.7.3(4), printed page 74"

end Pivotal

section Ribbon

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
A twist or balancing transformation from EGNO Definition 8.10.1,
equation (8.32).
-/
structure BalancedTwist where
  iso : 𝟭 C ≅ 𝟭 C
  tensor : (X Y : C) →
    iso.hom.app (X ⊗ Y) =
      (β_ X Y).hom ≫ (β_ Y X).hom ≫
        (iso.hom.app X ⊗ₘ iso.hom.app Y)

/--
A ribbon structure from EGNO Definition 8.10.1.

The `dual` field is exactly `(theta_X)^* = theta_(X*)`.
-/
structure RibbonStructure extends BalancedTwist C where
  dual : (X : C) →
    (toBalancedTwist.iso.hom.app X)ᘁ =
      toBalancedTwist.iso.hom.app (Xᘁ)

end Ribbon

end TwistedYetter.Fusion.EGNO
