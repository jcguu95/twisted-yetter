import TwistedYetter.Kirby.RoleAwarePremodularEvaluator
import TwistedYetter.Kirby.RoleAwareComponentDiagram
import TwistedYetter.Kirby.ThamThreeHandleVacuum
import TwistedYetter.Kirby.ModularOpenKilling

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
open TwistedYetter.Kirby.ModularOpenKilling
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

/-- The actual closed cut is `D` on the tensor unit and zero otherwise. -/
theorem specialCutMeridianClosedValue_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (s : S) :
    specialCutMeridianClosedValue 𝒞 s =
      if s = 𝒞.toFusionCategoryData.unitIndex then
        𝒞.globalDimension
      else
        0 := by
  classical
  rw [specialCutMeridianClosedValue,
    specialDottedCutOperator_simple]
  by_cases unitCase : s = 𝒞.toFusionCategoryData.unitIndex
  · subst s
    simp only [if_pos]
    rw [pivotalClosure_smul,
      𝒞.toFusionCategoryData.closedScalar_smul,
      pivotalClosure_identity_closedScalar,
      𝒞.quantumDimension_unit,
      mul_one]
  · simp only [unitCase, if_false]
    rw [show
      pivotalClosure 𝒞 (𝒞.simple s) 0 = 0 by
        exact map_zero (pivotalClosureLinearMap 𝒞 (𝒞.simple s))]
    unfold FusionCategoryData.closedScalar
    exact
      (𝒞.toFusionCategoryData.unitEndLinearEquiv.symm).map_zero

/--
The complete ordinary meridian label sum of the actual role-aware local
diagram is exactly one global dimension.
-/
theorem specialCutMeridianSum_eq_globalDimension
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    (∑ s : S,
      𝒞.quantumDimension s *
        specialCutMeridianClosedValue 𝒞 s) =
      𝒞.globalDimension := by
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

The first factor belongs to the normalized special cut.  The second is the
complete ordinary meridian label sum after projection to the unit sector.
-/
noncomputable def specialOneTwoPairValue
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) : K :=
  𝒞.globalDimension *
    vacuumProjectedRegularWeight 𝒞 η exponent

/-- The pair contributes exactly one global-dimension factor. -/
theorem specialOneTwoPairValue_eq_globalDimension
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    specialOneTwoPairValue 𝒞 η exponent =
      𝒞.globalDimension := by
  rw [specialOneTwoPairValue,
    vacuumProjectedRegularWeight_eq_one, mul_one]

/-- In particular, the newly born two-handle's zero exponent is neutral. -/
theorem specialOneTwoPairValue_zero
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C) :
    specialOneTwoPairValue 𝒞 η 0 =
      𝒞.globalDimension :=
  specialOneTwoPairValue_eq_globalDimension 𝒞 η 0

/-- The role-aware normalization expects exactly that same factor. -/
theorem roleAware_oneTwoFactor_eq_globalDimension
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    (roleAwareNormalizationProfile 𝒞).oneTwoFactor =
      𝒞.globalDimension := by
  simp [roleAwareNormalizationProfile,
    GlobalDimensionProfile.oneTwoFactor]

/--
The local pair value is exactly the denominator ratio used by a 1--2 birth.
-/
theorem specialOneTwoPairValue_eq_normalizationFactor
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    specialOneTwoPairValue 𝒞 η exponent =
      (roleAwareNormalizationProfile 𝒞).oneTwoFactor := by
  rw [specialOneTwoPairValue_eq_globalDimension,
    roleAware_oneTwoFactor_eq_globalDimension]

/-- Death uses the identical local factor read in the reverse direction. -/
theorem specialOneTwoDeathPairValue_eq_normalizationFactor
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ) :
    (roleAwareNormalizationProfile 𝒞).oneTwoFactor =
      specialOneTwoPairValue 𝒞 η exponent :=
  (specialOneTwoPairValue_eq_normalizationFactor 𝒞 η exponent).symm

/--
Complete normalization cancellation for a role-aware 1--2 birth.

The only remaining premise is the source-bound raw-numerator factorization;
the global-dimension arithmetic itself is proved here.
-/
theorem normalized_eq_of_birth_raw_factor
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (before after : EvaluationState (K := K))
    (countsSound : after.counts = before.counts.addOneTwo)
    (rawSound :
      after.rawNumerator =
        𝒞.globalDimension * before.rawNumerator) :
    after.normalized (roleAwareNormalizationProfile 𝒞) =
      before.normalized (roleAwareNormalizationProfile 𝒞) := by
  rw [EvaluationState.normalized, EvaluationState.normalized,
    rawSound, countsSound,
    GlobalDimensionProfile.denominator_addOneTwo,
    roleAware_oneTwoFactor_eq_globalDimension]
  exact mul_div_mul_left _ _ 𝒞.globalDimension_ne_zero

/-- Death is the same proved cancellation read in the reverse direction. -/
theorem normalized_eq_of_death_raw_factor
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (before after : EvaluationState (K := K))
    (countsSound : before.counts = after.counts.addOneTwo)
    (rawSound :
      before.rawNumerator =
        𝒞.globalDimension * after.rawNumerator) :
    before.normalized (roleAwareNormalizationProfile 𝒞) =
      after.normalized (roleAwareNormalizationProfile 𝒞) := by
  exact normalized_eq_of_birth_raw_factor
    𝒞 after before countsSound rawSound

end TwistedYetter.Kirby.PremodularOneTwoCutCancellation
