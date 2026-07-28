import TwistedYetter.Kirby.RoleAwarePremodularEvaluator
import TwistedYetter.Kirby.RoleAwareComponentDiagram
import TwistedYetter.Kirby.ThamThreeHandleVacuum
import TwistedYetter.Kirby.PivotalClosure

/-!
# Premodular 1--2 cancellation after special dotted cutting

This file closes the scalar part of the cancellation.  The new ordinary
two-handle coordinate has exponent zero, but the theorem is stated for an
arbitrary exponent because the tensor-unit cut removes the character coupon
in every case.
-/

namespace TwistedYetter.Kirby.PremodularOneTwoCutCancellation

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.PremodularPivotalClosure
open TwistedYetter.Kirby.PremodularDottedCutting
open TwistedYetter.Kirby.ThamThreeHandleVacuum

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Actual closed value of the normalized special cut on one simple meridian.

Unlike `specialOneTwoPairValue`, this is the pivotal closure of the morphism
used by the role-aware evaluator.
-/
noncomputable def specialCutMeridianClosedValue
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (s : S) : K :=
  𝒞.toFusionCategoryData.closedScalar
    (pivotalClosure 𝒞 (𝒞.simple s)
      (specialDottedCutOperator 𝒞 (𝒞.simple s)))

/-- The actual closed cut is `1` on the tensor unit and zero otherwise. -/
theorem specialCutMeridianClosedValue_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (s : S) :
    specialCutMeridianClosedValue 𝒞 s =
      if s = 𝒞.toFusionCategoryData.unitIndex then
        1
      else
        0 := by
  classical
  rw [specialCutMeridianClosedValue,
    specialDottedCutOperator_simple]
  by_cases unitCase : s = 𝒞.toFusionCategoryData.unitIndex
  · subst s
    simp only [if_pos]
    rw [pivotalClosure_identity_closedScalar,
      𝒞.quantumDimension_unit]
  · simp only [unitCase, if_false]
    rw [show
      pivotalClosure 𝒞 (𝒞.simple s) 0 = 0 by
        exact map_zero (pivotalClosureLinearMap 𝒞 (𝒞.simple s))]
    unfold FusionCategoryData.closedScalar
    exact
      (𝒞.toFusionCategoryData.unitEndLinearEquiv.symm).map_zero

/--
The complete ordinary meridian label sum of the actual role-aware local
diagram is exactly one.
-/
theorem specialCutMeridianSum_eq_one
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    (∑ s : S,
      𝒞.quantumDimension s *
        specialCutMeridianClosedValue 𝒞 s) =
      1 := by
  classical
  simp [specialCutMeridianClosedValue_eq,
    𝒞.quantumDimension_unit]

/-- The free role-aware local pair computes the actual closed cut value. -/
theorem oneTwoCutPair_closedScalar
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (labelOf : String → S) :
    𝒞.toFusionCategoryData.closedScalar
        (Diagram.eval C
          ((RoleAwareDiagram.oneTwoCutPair dottedId twoHandleId).interpret
            𝒞 η labelOf)) =
      specialCutMeridianClosedValue 𝒞 (labelOf twoHandleId) := by
  rw [RoleAwareDiagram.oneTwoCutPair_eval_eq_pivotalClosure]
  rfl

/--
Local scalar of a canceling special-dotted/ordinary 1--2 pair.

This is the complete ordinary meridian label sum after projection to the
unit sector.  Tham's index-three cut carries no additional scalar.
-/
noncomputable def specialOneTwoPairValue
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) : K :=
  vacuumProjectedRegularWeight 𝒞 η exponent

/-- The pair contributes exactly one. -/
theorem specialOneTwoPairValue_eq_one
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    specialOneTwoPairValue 𝒞 η exponent =
      1 := by
  rw [specialOneTwoPairValue,
    vacuumProjectedRegularWeight_eq_one]

/-- In particular, the newly born two-handle's zero exponent is neutral. -/
theorem specialOneTwoPairValue_zero
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C) :
    specialOneTwoPairValue 𝒞 η 0 =
      1 :=
  specialOneTwoPairValue_eq_one 𝒞 η 0

end TwistedYetter.Kirby.PremodularOneTwoCutCancellation
