import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TwistedYetter.Fusion.EGNOFusionCategory

/-!
# EGNO premodular and modular categories

This file follows EGNO Section 8.13 over an algebraically closed field of
characteristic zero.

* Definition 8.13.1: a premodular category is a ribbon fusion category,
  equivalently a braided fusion category equipped with a spherical structure.
* Definition 8.13.4: a premodular category is modular when its S-matrix is
  nondegenerate.
* Proposition 8.10.12 supplies the ribbon/spherical characterization.
* Remark 8.19.3 and Theorem 8.20.7 identify modularity with braided
  nondegeneracy and with trivial Mueger center.

Primitive category coherence belongs here. Kirby sliding and cancellation
are downstream theorems, not additional fields in the definition of a modular
category.
-/

namespace TwistedYetter.Fusion.EGNO

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance premodularSelectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/--
EGNO Definition 8.13.1.

A premodular category is definitionally a ribbon fusion category. Constructing
a value already supplies the finite semisimple, rigid, braided, balanced, and
ribbon coherence data.
-/
abbrev PremodularCategory :=
  RibbonFusionCategoryData (K := K) (C := C) (S := S)

/--
The equivalent EGNO presentation as a braided fusion category equipped with a
spherical structure.
-/
structure BraidedSphericalFusionCategory
    extends FusionCategoryData (K := K) (C := C) (S := S) where
  spherical : SphericalStructure (C := C)

/-- Ribbon data gives the canonical spherical presentation. -/
def PremodularCategory.toBraidedSpherical
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    BraidedSphericalFusionCategory (K := K) (C := C) (S := S) where
  toFusionCategoryData := 𝒞.toFusionCategoryData
  spherical := 𝒞.spherical

/--
The exact reconstruction supplied by EGNO Proposition 8.10.12.

It contains the ribbon structure obtained from the spherical pivotal structure
and Drinfeld isomorphism, together with the statement that the reconstructed
ribbon structure induces the original spherical structure.
-/
structure SphericalRibbonReconstruction
    (𝒞 :
      BraidedSphericalFusionCategory (K := K) (C := C) (S := S)) where
  ribbon : RibbonStructure C
  canonicalSpherical_eq :
    canonicalSphericalStructure ribbon = 𝒞.spherical

/--
EGNO Proposition 8.10.12, converse direction.

The explicit twist construction is retained as one standard textbook input
until it is expanded locally.
-/
axiom sphericalRibbonReconstruction
    (𝒞 :
      BraidedSphericalFusionCategory (K := K) (C := C) (S := S)) :
    SphericalRibbonReconstruction 𝒞

/-- The ribbon structure reconstructed by EGNO Proposition 8.10.12. -/
noncomputable def ribbonStructureOfSpherical
    (𝒞 :
      BraidedSphericalFusionCategory (K := K) (C := C) (S := S)) :
    RibbonStructure C :=
  (sphericalRibbonReconstruction 𝒞).ribbon

/-- The reconstructed ribbon structure induces the original spherical one. -/
theorem canonicalSpherical_ribbonStructureOfSpherical
    (𝒞 :
      BraidedSphericalFusionCategory (K := K) (C := C) (S := S)) :
    canonicalSphericalStructure (ribbonStructureOfSpherical 𝒞) =
      𝒞.spherical :=
  (sphericalRibbonReconstruction 𝒞).canonicalSpherical_eq

/-- Convert the equivalent spherical presentation to Definition 8.13.1. -/
noncomputable def BraidedSphericalFusionCategory.toPremodular
    (𝒞 :
      BraidedSphericalFusionCategory (K := K) (C := C) (S := S)) :
    PremodularCategory (K := K) (C := C) (S := S) where
  toFusionCategoryData := 𝒞.toFusionCategoryData
  ribbon := ribbonStructureOfSpherical 𝒞

/-- EGNO equation (8.46), before scalarization to the ground field. -/
def premodularSMatrixCategoricalEntry
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (s t : S) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalTrace 𝒞.pivotal
    ((β_ (𝒞.simple s) (𝒞.simple t)).hom ≫
      (β_ (𝒞.simple t) (𝒞.simple s)).hom)

/-- EGNO Definition 8.13.2: the scalar S-matrix. -/
noncomputable def premodularSMatrix
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    Matrix S S K :=
  fun s t =>
    𝒞.toFusionCategoryData.closedScalar
      (premodularSMatrixCategoricalEntry 𝒞 s t)

/-- Nondegeneracy in EGNO Definition 8.13.4. -/
def SMatrixNondegenerate
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) : Prop :=
  Matrix.det (premodularSMatrix 𝒞) ≠ 0

/--
EGNO Definition 8.13.4: a modular category is premodular and has
nondegenerate S-matrix.
-/
structure ModularCategory where
  toPremodularCategory :
    PremodularCategory (K := K) (C := C) (S := S)
  sMatrix_nondegenerate :
    SMatrixNondegenerate toPremodularCategory

namespace ModularCategory

variable
  (𝒞 : ModularCategory (K := K) (C := C) (S := S))

/-- The underlying ribbon fusion category. -/
abbrev premodular :
    PremodularCategory (K := K) (C := C) (S := S) :=
  𝒞.toPremodularCategory

/-- The modular category's S-matrix is nondegenerate by construction. -/
theorem sMatrixNondegenerate :
    SMatrixNondegenerate 𝒞.premodular :=
  𝒞.sMatrix_nondegenerate

end ModularCategory

/-- Double braiding with every object is categorical transparency. -/
def IsTransparentObject (X : C) : Prop :=
  ∀ Y : C,
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)

/--
EGNO Remark 8.19.3 and Theorem 8.20.7, specialized to the complete finite
simple skeleton: S-matrix nondegeneracy is equivalent to trivial Mueger center.
-/
axiom sMatrixNondegenerate_iff_trivialMuegerCenter
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    SMatrixNondegenerate 𝒞 ↔
      ∀ s : S,
        IsTransparentObject (𝒞.simple s) ↔
          s = 𝒞.toFusionCategoryData.unitIndex

/-- A modular category has trivial Mueger center. -/
theorem ModularCategory.transparent_iff_unit
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (s : S) :
    IsTransparentObject (𝒞.premodular.simple s) ↔
      s = 𝒞.premodular.toFusionCategoryData.unitIndex :=
  (sMatrixNondegenerate_iff_trivialMuegerCenter 𝒞.premodular).1
    𝒞.sMatrixNondegenerate s

/-- Global dimension formed from the canonical ribbon quantum dimensions. -/
noncomputable def PremodularCategory.globalDimension
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) : K :=
  ∑ s, 𝒞.quantumDimension s * 𝒞.quantumDimension s

/--
Characteristic-zero modular categories have nonzero global dimension.

This is EGNO Proposition 8.14.2 and Remark 8.14.3, retained as a standard
domain theorem input until their semisimple proof is expanded locally.
-/
axiom ModularCategory.globalDimension_ne_zero
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    𝒞.premodular.globalDimension ≠ 0

end TwistedYetter.Fusion.EGNO
