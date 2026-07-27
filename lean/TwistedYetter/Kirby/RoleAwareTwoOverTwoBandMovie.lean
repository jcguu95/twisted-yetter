import TwistedYetter.Kirby.RoleAwareSameComponentTransport
import TwistedYetter.Kirby.TwoOverTwoFusionChannel
import TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

/-!
# A role-aware exterior for the premodular 2/2 band movie

The only literature input in this file is the open Bärenz--Barrett band
movie for an arbitrary endomorphism of the exposed two-strand object.  The
input does not mention a tensor-identity automorphism, component exponents,
Kirby weights, or a closed evaluator value.
-/

namespace TwistedYetter.Kirby.RoleAwareTwoOverTwoBandMovie

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareSameComponentTransport
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.TwoOverTwoFusionChannel
open TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
One shared role-aware exterior exposing the two ordinary strands of a 2/2
slide.  This is free diagram syntax only.
-/
structure Window
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) where
  sourceGeometry : Geometry source
  targetGeometry : Geometry target
  exterior :
    RoleAwareDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      .unit .unit
  sourceLocal :
    RoleAwareDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  targetLocal :
    RoleAwareDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  source_factorization :
    sourceGeometry.cutDiagram =
      exterior.plug
        (sourceLocal.plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (localBoundary metadata countsSound))))
  target_factorization :
    targetGeometry.cutDiagram =
      exterior.plug
        (targetLocal.plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (localBoundary metadata countsSound))))

namespace Window

/-- The categorical source endpoint context after interpreting the exterior. -/
noncomputable def sourceContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :=
  CategoricalTangle.Context.compose
    (window.sourceLocal.interpret 𝒞 η labelOf)
    (window.exterior.interpret 𝒞 η labelOf)

/-- The categorical target endpoint context after interpreting the exterior. -/
noncomputable def targetContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :=
  CategoricalTangle.Context.compose
    (window.targetLocal.interpret 𝒞 η labelOf)
    (window.exterior.interpret 𝒞 η labelOf)

/--
The single premodular graphical input used by the open band movie.

An arbitrary endomorphism coupon may be transported through the exact
source-bound ribbon band recorded by `window`.  The statement is deliberately
independent of the orientation of the band: positive and negative
Bärenz--Barrett movies are the two orientation-specialized theorems below.

The input does not select a tensor-identity automorphism component, a
character exponent, a fusion channel, a Kirby weight, or a closed evaluator
value.  Those data enter only when the already proved channel calculation
chooses the endomorphism `f`.
-/
axiom premodularCouponTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (f :
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote ⟶
        ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote) :
    LinearContext.evalContextLinearMap (R := K)
        (window.sourceContext 𝒞 η labelOf) f =
      LinearContext.evalContextLinearMap (R := K)
        (window.targetContext 𝒞 η labelOf) f

/--
The positive open Bärenz--Barrett band movie, derived from the common
premodular coupon-transport input.

The orientation proof prevents a positive endpoint from being silently used
as a negative endpoint.  It contributes no evaluator equality.
-/
theorem baerenzBarrett_positiveBandMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (_orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation = .positive)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (f :
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote ⟶
        ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote) :
    LinearContext.evalContextLinearMap (R := K)
        (window.sourceContext 𝒞 η labelOf) f =
      LinearContext.evalContextLinearMap (R := K)
        (window.targetContext 𝒞 η labelOf) f :=
  window.premodularCouponTransport 𝒞 η labelOf f

/--
The negative open Bärenz--Barrett band movie, derived from the same common
premodular coupon-transport input.

As above, the orientation proof only binds this theorem to the negative
endpoint convention.
-/
theorem baerenzBarrett_negativeBandMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (_orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation = .negative)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (f :
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote ⟶
        ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote) :
    LinearContext.evalContextLinearMap (R := K)
        (window.sourceContext 𝒞 η labelOf) f =
      LinearContext.evalContextLinearMap (R := K)
        (window.targetContext 𝒞 η labelOf) f :=
  window.premodularCouponTransport 𝒞 η labelOf f

/-- Exhaustive orientation dispatch for the two derived theorems above. -/
theorem baerenzBarrett_bandMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    (f :
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote ⟶
        ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote) :
    LinearContext.evalContextLinearMap (R := K)
        (window.sourceContext 𝒞 η labelOf) f =
      LinearContext.evalContextLinearMap (R := K)
        (window.targetContext 𝒞 η labelOf) f := by
  cases orientationSound :
      (Request.twoOverTwo metadata countsSound).orientation with
  | positive =>
      exact window.baerenzBarrett_positiveBandMovie orientationSound
        𝒞 η labelOf f
  | negative =>
      exact window.baerenzBarrett_negativeBandMovie orientationSound
        𝒞 η labelOf f

/-- Plugging identity into the source endpoint recovers the source term. -/
theorem source_eval_eq_identity
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :
    Diagram.eval C
        (window.sourceGeometry.cutDiagram.interpret 𝒞 η labelOf) =
      LinearContext.evalContextLinearMap (R := K)
        (window.sourceContext 𝒞 η labelOf)
        (𝟙 ((localBoundary metadata countsSound).interpret
          𝒞 labelOf).denote) := by
  rw [window.source_factorization]
  rw [RoleAwareDiagram.Context.interpret_plug]
  rw [RoleAwareDiagram.Context.interpret_plug]
  let inner := window.sourceLocal.interpret 𝒞 η labelOf
  let outer := window.exterior.interpret 𝒞 η labelOf
  let identityDiagram :=
    Diagram.identity
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf)
  exact
    (LinearContext.evalContextLinearMap_diagram outer
      (CategoricalTangle.Context.plug C inner identityDiagram)).symm.trans
      (congrArg
        (LinearContext.evalContextLinearMap (R := K) outer)
        (LinearContext.evalContextLinearMap_diagram
          inner identityDiagram).symm)

/-- Plugging identity into the target endpoint recovers the target term. -/
theorem target_eval_eq_identity
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :
    Diagram.eval C
        (window.targetGeometry.cutDiagram.interpret 𝒞 η labelOf) =
      LinearContext.evalContextLinearMap (R := K)
        (window.targetContext 𝒞 η labelOf)
        (𝟙 ((localBoundary metadata countsSound).interpret
          𝒞 labelOf).denote) := by
  rw [window.target_factorization]
  rw [RoleAwareDiagram.Context.interpret_plug]
  rw [RoleAwareDiagram.Context.interpret_plug]
  let inner := window.targetLocal.interpret 𝒞 η labelOf
  let outer := window.exterior.interpret 𝒞 η labelOf
  let identityDiagram :=
    Diagram.identity
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf)
  exact
    (LinearContext.evalContextLinearMap_diagram outer
      (CategoricalTangle.Context.plug C inner identityDiagram)).symm.trans
      (congrArg
        (LinearContext.evalContextLinearMap (R := K) outer)
        (LinearContext.evalContextLinearMap_diagram
          inner identityDiagram).symm)

/--
The open band movie gives the fixed-label term equality used by the finite
sum.  The character is not discarded: it remains in the separately proved
role-aware weight transport.
-/
theorem term_eval_transport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :
    Diagram.eval C
        (window.sourceGeometry.cutDiagram.interpret 𝒞 η labelOf) =
      Diagram.eval C
        (window.targetGeometry.cutDiagram.interpret 𝒞 η labelOf) := by
  rw [window.source_eval_eq_identity 𝒞 η labelOf]
  rw [window.target_eval_eq_identity 𝒞 η labelOf]
  exact window.baerenzBarrett_bandMovie 𝒞 η labelOf
    (𝟙 ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote)

/-- Complete normalized role-aware 2/2 invariance. -/
theorem roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source window.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target window.targetGeometry
        ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle) := by
  let request := Request.twoOverTwo metadata countsSound
  apply RoleAwareSameComponentTransport.roleAwareCycleEval_transport
    𝒞 η window.sourceGeometry window.targetGeometry countsSound
    request.sameComponentChange
    (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoExponentTransport
      metadata countsSound sourceCycle)
  intro sourceLabeling
  let targetLabeling :=
    OrdinaryTransport.ordinaryLabelingEquiv
      request.sameComponentChange sourceLabeling
  have labelsEq :
      CanonicalPresentation.roleAwareLabelOf
          𝒞 target targetLabeling =
        CanonicalPresentation.roleAwareLabelOf
          𝒞 source sourceLabeling := by
    funext componentId
    exact roleAwareLabelOf_transport
      𝒞 source target request.sameComponentChange sourceLabeling componentId
  unfold CanonicalPresentation.roleAwareTermDiagram
  rw [labelsEq]
  exact window.term_eval_transport
    𝒞 η (CanonicalPresentation.roleAwareLabelOf 𝒞 source sourceLabeling)

end Window

end TwistedYetter.Kirby.RoleAwareTwoOverTwoBandMovie
