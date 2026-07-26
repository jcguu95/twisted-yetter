import TwistedYetter.Kirby.DualHandleConvention
import TwistedYetter.Kirby.EGNOModularKirbyMoves

/-!
# The Tham `k = 3` vacuum check in the dual convention

Tham's Definition 5.11 does not treat its index-three handle as a scalar
normalization alone.  It projects every strand crossing the three-handle
co-core to the tensor-unit channel.  This file records the algebraic part of
that projection for a homological tensor-automorphism coupon.

In this repository the evaluated decomposition is upside down.  Therefore
this Tham `k = 3` map belongs to a *primal one-handle*, represented by the
special dotted component.  A primal three-handle is instead a Tham `k = 1`
map and contributes the familiar inverse-dimension normalization.

The key point is small but decisive: a monoidal natural automorphism acts as
the identity on the tensor unit.  Consequently every integral power of the
twisting coupon is invisible after the vacuum projection.  This is exactly
the algebraic mechanism required for a primal cancelling 1--2 pair, which is
a dual cancelling 2--3 pair.

This file does not claim that the serialized special-dotted link evaluator
has already been identified with the complete Tham vacuum map for every dual
degree-three boundary.  That bridge remains a visible proof obligation.
-/

namespace TwistedYetter.Kirby.ThamThreeHandleVacuum

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
A monoidal natural automorphism of the identity acts trivially on the listed
simple object representing the tensor unit.
-/
theorem automorphismSimpleScalar_unitIndex
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    data.automorphismSimpleScalar automorphism data.unitIndex = 1 := by
  letI : Simple (data.simple data.unitIndex) :=
    data.simple_isSimple data.unitIndex
  have appUnit :
      automorphism.iso.hom.app (data.simple data.unitIndex) =
        𝟙 (data.simple data.unitIndex) := by
    apply (cancel_mono data.unitIso.hom).1
    simpa [automorphism.unit_hom] using
      (automorphism.iso.hom.naturality data.unitIso.hom).symm
  calc
    data.automorphismSimpleScalar automorphism data.unitIndex =
        data.simpleScalar (data.simple data.unitIndex)
          (automorphism.iso.hom.app (data.simple data.unitIndex)) := rfl
    _ = data.simpleScalar (data.simple data.unitIndex)
          (𝟙 (data.simple data.unitIndex)) := by rw [appUnit]
    _ = 1 := data.simpleScalar_identity (data.simple data.unitIndex)

/-- Every integral power of the twisting coupon is trivial on the unit. -/
theorem automorphismScalarPower_unitIndex
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    data.automorphismScalarPower automorphism data.unitIndex exponent = 1 := by
  simp [FusionCategoryData.automorphismScalarPower,
    FusionCategoryData.automorphismSimpleUnit,
    automorphismSimpleScalar_unitIndex data automorphism]

/--
The coefficient remaining after an idealized three-handle vacuum projection.

Only the tensor-unit simple survives.  This is the scalar shadow of Tham's
`k = 3` handle map, not a replacement for the full skein map.
-/
noncomputable def vacuumProjectedRegularWeight
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ) : K :=
  ∑ simple,
    if simple = 𝒞.toFusionCategoryData.unitIndex then
      𝒞.quantumDimension simple *
        𝒞.toFusionCategoryData.automorphismScalarPower
          automorphism simple exponent
    else
      0

/--
The vacuum-projected regular colour is independent of the homological
coefficient and has unit weight.
-/
theorem vacuumProjectedRegularWeight_eq_one
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    vacuumProjectedRegularWeight 𝒞 automorphism exponent = 1 := by
  classical
  simp [vacuumProjectedRegularWeight,
    𝒞.quantumDimension_unit,
    automorphismScalarPower_unitIndex
      𝒞.toFusionCategoryData automorphism exponent]

/--
Unit-sector neutrality for a dual cancelling 2--3 pair.
-/
theorem cancelingTwoThreeBoundaryCoefficient_is_vacuum_neutral
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (left right : ℤ) :
    vacuumProjectedRegularWeight 𝒞 automorphism left =
      vacuumProjectedRegularWeight 𝒞 automorphism right := by
  rw [vacuumProjectedRegularWeight_eq_one,
    vacuumProjectedRegularWeight_eq_one]

/--
The same theorem in primal language: the dotted component of a cancelling
1--2 pair is the Tham `k = 3` vacuum projector.
-/
theorem primalOneTwoBoundaryCoefficient_is_vacuum_neutral
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (left right : ℤ) :
    vacuumProjectedRegularWeight 𝒞 automorphism left =
      vacuumProjectedRegularWeight 𝒞 automorphism right :=
  cancelingTwoThreeBoundaryCoefficient_is_vacuum_neutral
    𝒞 automorphism left right

/-- Machine-visible status of the algebraic vacuum-sector calculation. -/
def currentStatus : String :=
  "PASS_THAM_K3_DUAL_THREE_HANDLE_PRIMAL_ONE_HANDLE_UNIT_SECTOR_NEUTRALITY"

/-- The exact remaining geometric scope, kept out of theorem names. -/
def remainingGeometricScope : String :=
  "Prove that the serialized specially dotted component realizes the Tham "
    ++ "k=3 vacuum projector for every dual d3-boundary representative; do "
    ++ "not attach this obligation to primal three-handles."

end TwistedYetter.Kirby.ThamThreeHandleVacuum
