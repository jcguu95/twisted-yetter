import TwistedYetter.Kirby.CanonicalCycleMoveGeometry

/-!
# Whole-sum slide geometry for the canonical modular evaluator

Kirby colours are finite linear combinations.  A local slide proof must
therefore have the complete explicit-cycle linear diagrams as its endpoints;
it is not enough to postulate one equality for every fixed global labeling.

This module provides two closed proof grammars:

* ordinary 1-over-1 and 2-over-1 slides use the exact formal ordinary Kirby
  colour retained by `OrdinaryHandleSlide`; and
* 2-over-2 slides expand the twisted sliding colour label by label and derive
  every term from the ordinary Kirby-colour sliding theorem.  This is the
  identity-functor specialization in Bärenz--Barrett Remark 3.5.

Every atomic proof is bound to the directed move metadata, including band
orientation, presentation hashes, and both participating component IDs.
There is no constructor from a diagram-evaluation equality or a scalar
equality.

The endpoint geometries use the explicit target cycle obtained from the
forward handle-chain map.  Consequently, no arbitrary homology
representative is required to commute with a Kirby move.
-/

namespace TwistedYetter.Kirby.CanonicalCycleSlideGeometry

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The ordinary sliding law canonically selected by a modular category. -/
noncomputable def canonicalOrdinarySlidingLaw
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    TwistedYetter.Kirby.HandleSlide.SourcedSlidingLaw C :=
  (baerenzBarrett_ordinaryKirbySliding 𝒞).toSourcedSlidingLaw

/--
Linear closure of ordinary slides with complete source-bound metadata.

An atom is already a slide of the exact formal ordinary Kirby colour.  The
linear constructors only place such atoms inside a finite formal sum.
-/
inductive BoundOrdinaryLinearSlide
    (law : TwistedYetter.Kirby.HandleSlide.SourcedSlidingLaw C)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK uC vC)
  | atom
      {before after : Diagram C .unit .unit}
      (slide : OrdinaryHandleSlide before after)
      (law_sound : ordinaryLaw slide = law)
      (kind_sound : (ordinaryMetadata slide).kind = kind)
      (orientation_sound :
        (ordinaryMetadata slide).orientation = orientation)
      (move_id_sound : (ordinaryMetadata slide).moveId = moveId)
      (source_hash_sound :
        (ordinaryMetadata slide).sourcePresentationHash = sourceHash)
      (target_hash_sound :
        (ordinaryMetadata slide).targetPresentationHash = targetHash)
      (sliding_component_id_sound :
        (ordinaryMetadata slide).slidingComponentId =
          slidingComponentId)
      (stationary_component_id_sound :
        (ordinaryMetadata slide).stationaryComponentId =
          stationaryComponentId) :
      BoundOrdinaryLinearSlide law kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (LinearDiagram.atom (R := K) before)
        (LinearDiagram.atom (R := K) after)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundOrdinaryLinearSlide law kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId
          leftBefore leftAfter →
      BoundOrdinaryLinearSlide law kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId
          rightBefore rightAfter →
      BoundOrdinaryLinearSlide law kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundOrdinaryLinearSlide law kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId before after →
      BoundOrdinaryLinearSlide law kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (scalar • before) (scalar • after)
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundOrdinaryLinearSlide law kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId first middle →
      BoundOrdinaryLinearSlide law kind orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId middle last →
      BoundOrdinaryLinearSlide law kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId first last

namespace BoundOrdinaryLinearSlide

/-- Soundness is derived recursively from the closed ordinary-slide grammar. -/
theorem eval_eq
    {law : TwistedYetter.Kirby.HandleSlide.SourcedSlidingLaw C}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (slide :
      BoundOrdinaryLinearSlide law kind orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction slide with
  | atom slide _ _ _ _ _ _ _ _ =>
      simpa only [LinearDiagram.eval_atom] using slide.sound
  | add _ _ leftSound rightSound =>
      simpa only [map_add] using
        congrArg₂ (· + ·) leftSound rightSound
  | smul scalar _ sound =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) sound
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end BoundOrdinaryLinearSlide

/--
Linear closure of complete fixed-label ordinary-slide windows with
source-bound metadata.

The base constructor consumes the whole label-indexed finite sum.  Its
soundness is derived from ordinary Kirby-colour sliding and naturality; no
independent generalized-sliding axiom is used.
-/
inductive BoundGeneralizedLinearSlide
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK uC vC)
  | window
      (metadata : SlideMetadata)
      (kind_sound : metadata.kind = .twoOverTwo)
      (orientation_sound : metadata.orientation = orientation)
      (move_id_sound : metadata.moveId = moveId)
      (source_hash_sound :
        metadata.sourcePresentationHash = sourceHash)
      (target_hash_sound :
        metadata.targetPresentationHash = targetHash)
      (sliding_component_id_sound :
        metadata.slidingComponentId = slidingComponentId)
      (stationary_component_id_sound :
        metadata.stationaryComponentId = stationaryComponentId)
      (_lineage : ComponentLineage metadata)
      (closedWindow :
        OrdinaryLabelIndexedSlidingWindow
          𝒞.premodular
          (baerenzBarrett_ordinaryKirbySliding 𝒞))
      (coefficient : S → K) :
      BoundGeneralizedLinearSlide 𝒞 orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (closedWindow.linearBefore coefficient)
        (closedWindow.linearAfter coefficient)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundGeneralizedLinearSlide 𝒞 orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId
          leftBefore leftAfter →
      BoundGeneralizedLinearSlide 𝒞 orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId
          rightBefore rightAfter →
      BoundGeneralizedLinearSlide 𝒞 orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundGeneralizedLinearSlide 𝒞 orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId before after →
      BoundGeneralizedLinearSlide 𝒞 orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (scalar • before) (scalar • after)
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundGeneralizedLinearSlide 𝒞 orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId first middle →
      BoundGeneralizedLinearSlide 𝒞 orientation
          moveId sourceHash targetHash
          slidingComponentId stationaryComponentId middle last →
      BoundGeneralizedLinearSlide 𝒞 orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId first last

namespace BoundGeneralizedLinearSlide

/--
Soundness follows from the derived fixed-label ordinary window and linearity.
-/
theorem eval_eq
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    {before after :
      LinearDiagram (R := K) (C := C) .unit .unit}
    (slide :
      BoundGeneralizedLinearSlide 𝒞 orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction slide with
  | window _ _ _ _ _ _ _ _ _ closedWindow coefficient =>
      exact closedWindow.linear_eval_sound coefficient
  | add _ _ leftSound rightSound =>
      simpa only [map_add] using
        congrArg₂ (· + ·) leftSound rightSound
  | smul scalar _ sound =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) sound
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end BoundGeneralizedLinearSlide

/--
Exact whole-sum geometry for a 1-over-1 or 2-over-1 move on one explicit
cycle.
-/
structure OrdinaryCycleSlideGeometry
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
    (transport : MarkedH2Transport source.topology target.topology)
    (kind : SlideKind)
    (recipeOrientation orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) where
  recipe_orientation_sound : recipeOrientation = orientation
  linearSlide :
    (sourceCycle : source.DegreeTwoCycle) →
      BoundOrdinaryLinearSlide
        (canonicalOrdinarySlidingLaw 𝒞)
        kind orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle)
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle))

namespace OrdinaryCycleSlideGeometry

/-- The complete explicit-cycle linear evaluations agree. -/
theorem cycleLinearDiagram_eval_transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {transport : MarkedH2Transport source.topology target.topology}
    {kind : SlideKind}
    {recipeOrientation orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    (geometry :
      OrdinaryCycleSlideGeometry 𝒞 automorphism source target transport
        kind recipeOrientation orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle)) :=
  (geometry.linearSlide sourceCycle).eval_eq

end OrdinaryCycleSlideGeometry

/-- Exact whole-sum geometry for a generalized 2-over-2 slide. -/
structure GeneralizedCycleSlideGeometry
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation manifold H2)
    (transport : MarkedH2Transport source.topology target.topology)
    (recipeOrientation orientation : BandOrientation)
    (moveId sourceHash targetHash : String)
    (slidingComponentId stationaryComponentId : String) where
  recipe_orientation_sound : recipeOrientation = orientation
  linearSlide :
    (sourceCycle : source.DegreeTwoCycle) →
      BoundGeneralizedLinearSlide 𝒞 orientation
        moveId sourceHash targetHash
        slidingComponentId stationaryComponentId
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle)
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle))

namespace GeneralizedCycleSlideGeometry

/-- The complete generalized explicit-cycle sums have equal evaluations. -/
theorem cycleLinearDiagram_eval_transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation manifold H2}
    {transport : MarkedH2Transport source.topology target.topology}
    {recipeOrientation orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {slidingComponentId stationaryComponentId : String}
    (geometry :
      GeneralizedCycleSlideGeometry 𝒞 automorphism source target transport
        recipeOrientation orientation moveId sourceHash targetHash
        slidingComponentId stationaryComponentId)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 automorphism sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 automorphism
          ((CycleTransport.ofMarkedH2Transport source target transport)
            |>.targetCycle sourceCycle)) :=
  (geometry.linearSlide sourceCycle).eval_eq

end GeneralizedCycleSlideGeometry

end TwistedYetter.Kirby.CanonicalCycleSlideGeometry
