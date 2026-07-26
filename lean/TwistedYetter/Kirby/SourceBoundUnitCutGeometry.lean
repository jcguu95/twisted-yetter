import TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
import TwistedYetter.Kirby.RoleAwareCharacterCouponBridge
import TwistedYetter.Kirby.RoleAwareSameComponentTransport
import TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams
import TwistedYetter.Kirby.SimultaneousDottedCutGeometry

/-!
# Source-bound topology windows for special dotted slides

This module defines category-neutral certificate data binding exact source
and target presentations to a one-hole free-diagram context.  It declares no
global existence axiom and contains no category, character, scalar, projector
equation, or evaluation equality.
-/

namespace TwistedYetter.Kirby.SourceBoundUnitCutGeometry

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwareCharacterCouponBridge
open TwistedYetter.Kirby.RoleAwareSameComponentTransport
open TwistedYetter.Kirby.RoleAwareUnitCutSlideDiagrams
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The chain equivalence used by a 1/1 request is the literature compiler's. -/
theorem oneOverOne_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    (enrichedMove
        (.oneOverOne metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.oneOverOne metadata countsSound)).chainEquivalence := by
  rfl

/-- Exact cycle-coordinate transport for a 1/1 slide. -/
noncomputable def oneOverOneExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    SameComponentCycleExponentTransport source target
      (Request.oneOverOne metadata countsSound).sameComponentChange
      sourceCycle
      ((Request.oneOverOne metadata countsSound).targetCycle sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).oneOverOneCoordinates
      metadata countsSound
  refine { exponent_sound := ?_ }
  intro targetIndex
  change
    target.topology.cycleComponentExponent
        (forwardDegreeTwoCycle
          (MarkedH2Transport.chainEquivalence
            (TableTwoMove.homologyTransport
              (enrichedMove (.oneOverOne metadata countsSound))))
          sourceCycle)
        (componentAt target.topology.formal targetIndex) =
      source.topology.cycleComponentExponent sourceCycle
        (componentAt source.topology.formal
          ((Request.oneOverOne metadata countsSound).sameComponentChange.targetToSource
            targetIndex))
  rw [oneOverOne_enriched_chainEquivalence metadata countsSound]
  exact coordinateLaw.exponent_sound sourceCycle targetIndex

/-- The chain equivalence used by a 2/1 request is the literature compiler's. -/
theorem twoOverOne_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    (enrichedMove
        (.twoOverOne metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.twoOverOne metadata countsSound)).chainEquivalence := by
  rfl

/-- Exact cycle-coordinate transport for a 2/1 slide. -/
noncomputable def twoOverOneExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    SameComponentCycleExponentTransport source target
      (Request.twoOverOne metadata countsSound).sameComponentChange
      sourceCycle
      ((Request.twoOverOne metadata countsSound).targetCycle sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).twoOverOneCoordinates
      metadata countsSound
  refine { exponent_sound := ?_ }
  intro targetIndex
  change
    target.topology.cycleComponentExponent
        (forwardDegreeTwoCycle
          (MarkedH2Transport.chainEquivalence
            (TableTwoMove.homologyTransport
              (enrichedMove (.twoOverOne metadata countsSound))))
          sourceCycle)
        (componentAt target.topology.formal targetIndex) =
      source.topology.cycleComponentExponent sourceCycle
        (componentAt source.topology.formal
          ((Request.twoOverOne metadata countsSound).sameComponentChange.targetToSource
            targetIndex))
  rw [twoOverOne_enriched_chainEquivalence metadata countsSound]
  exact coordinateLaw.exponent_sound sourceCycle targetIndex

/-- Exact free topology window for one source-bound 2/1 slide. -/
inductive TwoOverOneMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology) :
    Type (uH + 1)
  | positive
      (sourceGeometry : Geometry source)
      (targetGeometry : Geometry target)
      (dottedId : String)
      (punctureBoundary movingBoundary : ComponentBoundary)
      (context :
        RoleAwareDiagram.Context
          (.tensor punctureBoundary movingBoundary)
          (.tensor movingBoundary punctureBoundary)
          .unit .unit)
      (source_factorization :
        sourceGeometry.cutDiagram =
          context.plug
            (twoOverOnePositiveTopologyBefore dottedId
              punctureBoundary movingBoundary))
      (target_factorization :
        targetGeometry.cutDiagram =
          context.plug
            (twoOverOnePositiveAfterBoundary dottedId
              punctureBoundary movingBoundary))
      (orientation_sound :
        HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit =
          BandOrientation.positive) :
      TwoOverOneMovie source target metadata
  | negative
      (sourceGeometry : Geometry source)
      (targetGeometry : Geometry target)
      (dottedId : String)
      (punctureBoundary movingBoundary : ComponentBoundary)
      (context :
        RoleAwareDiagram.Context
          (.tensor movingBoundary punctureBoundary)
          (.tensor punctureBoundary movingBoundary)
          .unit .unit)
      (source_factorization :
        sourceGeometry.cutDiagram =
          context.plug
            (twoOverOneNegativeTopologyBefore dottedId
              punctureBoundary movingBoundary))
      (target_factorization :
        targetGeometry.cutDiagram =
          context.plug
            (twoOverOneNegativeAfterBoundary dottedId
              punctureBoundary movingBoundary))
      (orientation_sound :
        HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit =
          BandOrientation.negative) :
      TwoOverOneMovie source target metadata

/-- Exact free topology window for one source-bound 1/1 slide. -/
structure OneOverOneMovie
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (_metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology) where
  sourceGeometry : Geometry source
  targetGeometry : Geometry target
  leftDottedId : String
  rightDottedId : String
  leftBoundary : ComponentBoundary
  rightBoundary : ComponentBoundary
  context :
    RoleAwareDiagram.Context
      (.tensor leftBoundary rightBoundary)
      (.tensor leftBoundary rightBoundary)
      .unit .unit
  source_factorization :
    sourceGeometry.cutDiagram =
      context.plug
        (oneOverOneTopologyBefore leftDottedId rightDottedId
          leftBoundary rightBoundary)
  target_factorization :
    targetGeometry.cutDiagram =
      context.plug
        (oneOverOneTopologyAfter leftDottedId rightDottedId
          leftBoundary rightBoundary)

namespace TwoOverOneMovie

/-- Source simultaneous-cut geometry selected by the exact movie. -/
def sourceGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology} :
    TwoOverOneMovie source target metadata → Geometry source
  | .positive geometry _ _ _ _ _ _ _ _ => geometry
  | .negative geometry _ _ _ _ _ _ _ _ => geometry

/-- Target simultaneous-cut geometry selected by the exact movie. -/
def targetGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology} :
    TwoOverOneMovie source target metadata → Geometry target
  | .positive _ geometry _ _ _ _ _ _ _ => geometry
  | .negative _ geometry _ _ _ _ _ _ _ => geometry

/-- The exact source-local syntax after inserting the visible character coupon. -/
def augmentedSource
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology}
    (movie : TwoOverOneMovie source target metadata)
    (exponent : ℤ) :
    RoleAwareDiagram .unit .unit :=
  match movie with
  | .positive _ _ dottedId punctureBoundary movingBoundary context _ _ _ =>
      context.plug
        (twoOverOnePositiveBeforeBoundary dottedId
          punctureBoundary movingBoundary exponent)
  | .negative _ _ dottedId punctureBoundary movingBoundary context _ _ _ =>
      context.plug
        (twoOverOneNegativeBeforeBoundary dottedId
          punctureBoundary movingBoundary exponent)

/-- The exact target-local syntax; the projector has absorbed the coupon. -/
def augmentedTarget
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology}
    (movie : TwoOverOneMovie source target metadata) :
    RoleAwareDiagram .unit .unit :=
  match movie with
  | .positive _ _ dottedId punctureBoundary movingBoundary context _ _ _ =>
      context.plug
        (twoOverOnePositiveAfterBoundary dottedId
          punctureBoundary movingBoundary)
  | .negative _ _ dottedId punctureBoundary movingBoundary context _ _ _ =>
      context.plug
        (twoOverOneNegativeAfterBoundary dottedId
          punctureBoundary movingBoundary)

/--
The source-bound 2/1 character calculation.

The topology movie selects the exact free window; the equality itself is a
kernel-checked consequence of tensor-unit cutting.
-/
theorem augmented_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology}
    (movie : TwoOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (exponent : ℤ) :
    Diagram.eval C ((movie.augmentedSource exponent).interpret 𝒞 η labelOf) =
      Diagram.eval C (movie.augmentedTarget.interpret 𝒞 η labelOf) := by
  cases movie with
  | positive sourceGeometry targetGeometry dottedId punctureBoundary
      movingBoundary context sourceFactorization targetFactorization
      orientationSound =>
      exact twoOverOnePositiveBoundary_eval_eq_inContext
        𝒞 η labelOf dottedId punctureBoundary movingBoundary exponent context
  | negative sourceGeometry targetGeometry dottedId punctureBoundary
      movingBoundary context sourceFactorization targetFactorization
      orientationSound =>
      exact twoOverOneNegativeBoundary_eval_eq_inContext
        𝒞 η labelOf dottedId punctureBoundary movingBoundary exponent context

/--
For one ordinary-label sector, the exact source-bound 2/1 movie identifies
the actual role-aware evaluator terms.  The zero coupon used internally is
the identity; all nonzero character data remains in the evaluator weight and
is transported separately.
-/
theorem roleAwareTerm_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology}
    (movie : TwoOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (sourceLabeling :
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) source) :
    Diagram.eval C
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
          𝒞 η source movie.sourceGeometry sourceLabeling) =
      Diagram.eval C
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
          𝒞 η target movie.targetGeometry
          (TwistedYetter.Kirby.RoleAwareSameComponentTransport.OrdinaryTransport.ordinaryLabelingEquiv
            change sourceLabeling)) := by
  have labelTransport :
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
          𝒞 target
          (TwistedYetter.Kirby.RoleAwareSameComponentTransport.OrdinaryTransport.ordinaryLabelingEquiv
            change sourceLabeling) =
        RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
          𝒞 source sourceLabeling := by
    funext componentId
    exact RoleAwareSameComponentTransport.roleAwareLabelOf_transport
      𝒞 source target change sourceLabeling componentId
  cases movie with
  | positive sourceGeometry targetGeometry dottedId punctureBoundary
      movingBoundary context sourceFactorization targetFactorization
      orientationSound =>
      simp only [
        RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram,
        TwoOverOneMovie.sourceGeometry, TwoOverOneMovie.targetGeometry]
      rw [sourceFactorization, targetFactorization, labelTransport]
      let localContext :
          RoleAwareDiagram.Context punctureBoundary punctureBoundary
            (.tensor punctureBoundary movingBoundary)
            (.tensor movingBoundary punctureBoundary) :=
        .compose
          (.tensorLeft
            (.ordinary (.identity movingBoundary)))
          (.compRight
            (.ordinary
              (.crossingPositive punctureBoundary movingBoundary)))
      let fullContext := RoleAwareDiagram.Context.compose localContext context
      have zeroBridge :=
        scalar_smul_specialCut_eval_eq_characterCouponCut_eval_inContext
            𝒞 η
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
              𝒞 source sourceLabeling)
            dottedId punctureBoundary 0 fullContext
      have topologyToCoupon :
          Diagram.eval C
              ((context.plug
                (twoOverOnePositiveTopologyBefore dottedId
                  punctureBoundary movingBoundary)).interpret
                    𝒞 η
                    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
                      𝒞 source sourceLabeling)) =
            Diagram.eval C
              ((context.plug
                (twoOverOnePositiveBeforeBoundary dottedId
                  punctureBoundary movingBoundary 0)).interpret
                    𝒞 η
                    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
                      𝒞 source sourceLabeling)) := by
        simpa [fullContext, localContext,
          RoleAwareDiagram.Context.plug,
          twoOverOnePositiveTopologyBefore,
          twoOverOnePositiveBeforeBoundary,
          ComponentBoundaryCharacter.boundaryCharacterPower] using zeroBridge
      exact topologyToCoupon.trans
        (TwoOverOneMovie.augmented_eval_eq
          (.positive sourceGeometry targetGeometry dottedId
            punctureBoundary movingBoundary context sourceFactorization
            targetFactorization orientationSound)
          𝒞 η
          (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
            𝒞 source sourceLabeling)
          0)
  | negative sourceGeometry targetGeometry dottedId punctureBoundary
      movingBoundary context sourceFactorization targetFactorization
      orientationSound =>
      simp only [
        RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram,
        TwoOverOneMovie.sourceGeometry, TwoOverOneMovie.targetGeometry]
      rw [sourceFactorization, targetFactorization, labelTransport]
      let localContext :
          RoleAwareDiagram.Context punctureBoundary punctureBoundary
            (.tensor movingBoundary punctureBoundary)
            (.tensor punctureBoundary movingBoundary) :=
        .compose
          (.tensorRight
            (.ordinary (.identity movingBoundary)))
          (.compRight
            (.ordinary
              (.crossingNegative movingBoundary punctureBoundary)))
      let fullContext := RoleAwareDiagram.Context.compose localContext context
      have zeroBridge :=
        scalar_smul_specialCut_eval_eq_cutCharacterCoupon_eval_inContext
            𝒞 η
            (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
              𝒞 source sourceLabeling)
            dottedId punctureBoundary 0 fullContext
      have topologyToCoupon :
          Diagram.eval C
              ((context.plug
                (twoOverOneNegativeTopologyBefore dottedId
                  punctureBoundary movingBoundary)).interpret
                    𝒞 η
                    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
                      𝒞 source sourceLabeling)) =
            Diagram.eval C
              ((context.plug
                (twoOverOneNegativeBeforeBoundary dottedId
                  punctureBoundary movingBoundary 0)).interpret
                    𝒞 η
                    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
                      𝒞 source sourceLabeling)) := by
        simpa [fullContext, localContext,
          RoleAwareDiagram.Context.plug,
          twoOverOneNegativeTopologyBefore,
          twoOverOneNegativeBeforeBoundary,
          ComponentBoundaryCharacter.boundaryCharacterPower] using zeroBridge
      exact topologyToCoupon.trans
        (TwoOverOneMovie.augmented_eval_eq
          (.negative sourceGeometry targetGeometry dottedId
            punctureBoundary movingBoundary context sourceFactorization
            targetFactorization orientationSound)
          𝒞 η
          (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
            𝒞 source sourceLabeling)
          0)

end TwoOverOneMovie

namespace OneOverOneMovie

/-- Exact source-local syntax with both visible character coupons. -/
def augmentedSource
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology}
    (movie : OneOverOneMovie source target metadata)
    (leftExponent rightExponent : ℤ) :
    RoleAwareDiagram .unit .unit :=
  movie.context.plug
    (oneOverOneBeforeBoundary movie.leftDottedId movie.rightDottedId
      movie.leftBoundary movie.rightBoundary leftExponent rightExponent)

/-- Exact target-local syntax after both projector absorptions. -/
def augmentedTarget
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology}
    (movie : OneOverOneMovie source target metadata)
    (leftExponent rightExponent : ℤ) :
    RoleAwareDiagram .unit .unit :=
  movie.context.plug
    (oneOverOneAfterBoundary movie.leftDottedId movie.rightDottedId
      movie.leftBoundary movie.rightBoundary leftExponent rightExponent)

/-- Kernel-checked source-bound 1/1 character calculation. -/
theorem augmented_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology}
    (movie : OneOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (leftExponent rightExponent : ℤ) :
    Diagram.eval C
        ((movie.augmentedSource leftExponent rightExponent).interpret
          𝒞 η labelOf) =
      Diagram.eval C
        ((movie.augmentedTarget leftExponent rightExponent).interpret
          𝒞 η labelOf) := by
  exact oneOverOneBoundary_eval_eq_inContext
    𝒞 η labelOf movie.leftDottedId movie.rightDottedId
    movie.leftBoundary movie.rightBoundary leftExponent rightExponent
    movie.context

/-- One ordinary-label sector of the actual role-aware 1/1 evaluator. -/
theorem roleAwareTerm_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology}
    (movie : OneOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (change :
      SameComponentIndexChange
        source.topology.formal target.topology.formal)
    (sourceLabeling :
      RoleAwarePremodularEvaluator.CanonicalPresentation.OrdinaryLabeling
        (S := S) source) :
    Diagram.eval C
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
          𝒞 η source movie.sourceGeometry sourceLabeling) =
      Diagram.eval C
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram
          𝒞 η target movie.targetGeometry
          (TwistedYetter.Kirby.RoleAwareSameComponentTransport.OrdinaryTransport.ordinaryLabelingEquiv
              change sourceLabeling)) := by
  have labelTransport :
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
          𝒞 target
          (TwistedYetter.Kirby.RoleAwareSameComponentTransport.OrdinaryTransport.ordinaryLabelingEquiv
              change sourceLabeling) =
        RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
          𝒞 source sourceLabeling := by
    funext componentId
    exact RoleAwareSameComponentTransport.roleAwareLabelOf_transport
      𝒞 source target change sourceLabeling componentId
  simp only [
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareTermDiagram]
  rw [movie.source_factorization, movie.target_factorization, labelTransport]
  exact oneOverOneTopologyBoundary_eval_eq_inContext
    𝒞 η
    (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLabelOf
      𝒞 source sourceLabeling)
    movie.leftDottedId movie.rightDottedId
    movie.leftBoundary movie.rightBoundary movie.context

end OneOverOneMovie

/--
Complete denominator-safe role-aware 2/1 evaluation equality.
-/
theorem twoOverOne_roleAwareLinearDiagram_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (movie : TwoOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η source movie.sourceGeometry sourceCycle) =
      LinearDiagram.eval
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η target movie.targetGeometry
            ((Request.twoOverOne metadata countsSound).targetCycle
              sourceCycle)) := by
  exact RoleAwareSameComponentTransport.roleAwareLinearDiagram_eval_transport
      𝒞 η movie.sourceGeometry movie.targetGeometry
      (Request.twoOverOne metadata countsSound).sameComponentChange
      (twoOverOneExponentTransport metadata countsSound sourceCycle)
      (movie.roleAwareTerm_eval_eq 𝒞 η
        (Request.twoOverOne metadata countsSound).sameComponentChange)

/--
Complete denominator-safe role-aware 1/1 evaluation equality.
-/
theorem oneOverOne_roleAwareLinearDiagram_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (movie : OneOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η source movie.sourceGeometry sourceCycle) =
      LinearDiagram.eval
        (RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareLinearDiagram
            𝒞 η target movie.targetGeometry
            ((Request.oneOverOne metadata countsSound).targetCycle
              sourceCycle)) := by
  exact RoleAwareSameComponentTransport.roleAwareLinearDiagram_eval_transport
      𝒞 η movie.sourceGeometry movie.targetGeometry
      (Request.oneOverOne metadata countsSound).sameComponentChange
      (oneOverOneExponentTransport metadata countsSound sourceCycle)
      (movie.roleAwareTerm_eval_eq 𝒞 η
        (Request.oneOverOne metadata countsSound).sameComponentChange)

/-- Source-bound normalized 2/1 invariance for the role-aware evaluator. -/
theorem twoOverOne_roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (movie : TwoOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η source movie.sourceGeometry sourceCycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η target movie.targetGeometry
        ((Request.twoOverOne metadata countsSound).targetCycle
          sourceCycle) := by
  exact RoleAwareSameComponentTransport.roleAwareCycleEval_transport
    𝒞 η movie.sourceGeometry movie.targetGeometry countsSound
    (Request.twoOverOne metadata countsSound).sameComponentChange
    (twoOverOneExponentTransport metadata countsSound sourceCycle)
    (movie.roleAwareTerm_eval_eq 𝒞 η
      (Request.twoOverOne metadata countsSound).sameComponentChange)

/-- Source-bound normalized 1/1 invariance for the role-aware evaluator. -/
theorem oneOverOne_roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (movie : OneOverOneMovie source target metadata)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η source movie.sourceGeometry sourceCycle =
      RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
        𝒞 η target movie.targetGeometry
        ((Request.oneOverOne metadata countsSound).targetCycle
          sourceCycle) := by
  exact RoleAwareSameComponentTransport.roleAwareCycleEval_transport
    𝒞 η movie.sourceGeometry movie.targetGeometry countsSound
    (Request.oneOverOne metadata countsSound).sameComponentChange
    (oneOverOneExponentTransport metadata countsSound sourceCycle)
    (movie.roleAwareTerm_eval_eq 𝒞 η
      (Request.oneOverOne metadata countsSound).sameComponentChange)

end TwistedYetter.Kirby.SourceBoundUnitCutGeometry
