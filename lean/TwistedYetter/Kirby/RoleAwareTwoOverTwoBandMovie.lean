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
    ComponentRibbonDiagram.ComponentDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  targetLocal :
    ComponentRibbonDiagram.ComponentDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  source_factorization :
    sourceGeometry.cutDiagram =
      exterior.plug
        ((RoleAwareDiagram.Context.ordinary sourceLocal).plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (localBoundary metadata countsSound))))
  target_factorization :
    targetGeometry.cutDiagram =
      exterior.plug
        ((RoleAwareDiagram.Context.ordinary targetLocal).plug
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
    (window.sourceLocal.interpret 𝒞 labelOf)
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
    (window.targetLocal.interpret 𝒞 labelOf)
    (window.exterior.interpret 𝒞 η labelOf)

/--
The untwisted Bärenz--Barrett band core.

The local before and after contexts are components of one natural
endomorphism of the identity functor.  The two endpoint equations contain no
tensor-identity automorphism, character exponent, or closed scalar equality.
They are the literature-backed ordinary band-slide input; arbitrary coupon
transport is proved from their naturality below.
-/
structure PremodularBandCore
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S) where
  transformation : 𝟭 C ⟶ 𝟭 C
  source_local :
    (f :
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote ⟶
        ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote) →
      LinearContext.evalContextLinearMap (R := K)
          (window.sourceLocal.interpret 𝒞 labelOf) f =
        transformation.app
            ((localBoundary metadata countsSound).interpret
              𝒞 labelOf).denote ≫ f
  target_local :
    (f :
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote ⟶
        ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote) →
      LinearContext.evalContextLinearMap (R := K)
          (window.targetLocal.interpret 𝒞 labelOf) f =
        f ≫ transformation.app
          ((localBoundary metadata countsSound).interpret 𝒞 labelOf).denote

/--
Bärenz--Barrett's ordinary open band-slide law, bound to the exact ordinary
local contexts selected by `window`.

This is the remaining literature input.  It has no `η` argument and cannot
state the twisted answer.
-/
axiom baerenzBarrettPremodularBandCore
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S) :
    PremodularBandCore window 𝒞 labelOf

/--
An arbitrary coupon crosses the band by naturality of the untwisted core.

Unlike the former axiom, this theorem makes `f` visible only after the
ordinary Bärenz--Barrett input has been fixed.
-/
theorem premodularCouponTransport
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
  let core := window.baerenzBarrettPremodularBandCore 𝒞 labelOf
  change
    LinearContext.evalContextLinearMap (R := K)
        (window.exterior.interpret 𝒞 η labelOf)
        (LinearContext.evalContextLinearMap (R := K)
          (window.sourceLocal.interpret 𝒞 labelOf) f) =
      LinearContext.evalContextLinearMap (R := K)
        (window.exterior.interpret 𝒞 η labelOf)
        (LinearContext.evalContextLinearMap (R := K)
          (window.targetLocal.interpret 𝒞 labelOf) f)
  rw [core.source_local f, core.target_local f]
  apply congrArg
    (LinearContext.evalContextLinearMap (R := K)
      (window.exterior.interpret 𝒞 η labelOf))
  simpa using (core.transformation.naturality f).symm

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
  simp only [RoleAwareDiagram.Context.interpret_ordinary,
    RoleAwareDiagram.interpret, sourceContext]
  let inner := window.sourceLocal.interpret 𝒞 labelOf
  let outer := window.exterior.interpret 𝒞 η labelOf
  let identityDiagram :=
    Diagram.identity
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf)
  exact
    (LinearContext.evalContextLinearMap_diagram outer
      (CategoricalTangle.Context.plug C inner identityDiagram)).symm.trans
      (congrArg
        (LinearContext.evalContextLinearMap (R := K) outer)
        (LinearContext.evalContextLinearMap_diagram (R := K)
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
  simp only [RoleAwareDiagram.Context.interpret_ordinary,
    RoleAwareDiagram.interpret, targetContext]
  let inner := window.targetLocal.interpret 𝒞 labelOf
  let outer := window.exterior.interpret 𝒞 η labelOf
  let identityDiagram :=
    Diagram.identity
      ((localBoundary metadata countsSound).interpret 𝒞 labelOf)
  exact
    (LinearContext.evalContextLinearMap_diagram outer
      (CategoricalTangle.Context.plug C inner identityDiagram)).symm.trans
      (congrArg
        (LinearContext.evalContextLinearMap (R := K) outer)
        (LinearContext.evalContextLinearMap_diagram (R := K)
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
