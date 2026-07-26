import TwistedYetter.Kirby.CanonicalCycleSlideGeometry
import TwistedYetter.Kirby.CanonicalSourceBackedMove

/-!
# Source-bound canonical slide movies

This module gives the three slide families one shared proof-relevant route:

1. bind the exact source and target trace windows;
2. attach the tensor-automorphism coupons with the restricted coupon grammar;
3. transport the ordinary Kirby colour by Bärenz--Barrett sliding; and
4. detach the transported coupons with the same restricted grammar.

The three handle-role cases are constructors of `Request`.  The imported
diagrammatic input is therefore one denominator indexed by an exact request,
not three unrelated axioms with parallel endpoint conventions.
-/

namespace TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalCycleSlideGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalMoveGeometry
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Exact common-component correspondence stored by a 1-over-1 edit. -/
def oneOverOneSameOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneOverOne)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .oneOverOne _ _ _ _,
      .oneOverOne _ _ _ _ same _ _ _ => same

/-- Exact pair of components stored by a 1-over-1 edit. -/
def oneOverOneComponentsOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneOverOne)
    (change : ComponentIndexChange source target edit) :
    ResolvedSlideComponentPair source target
      (oneOverOneSameOfEdit edit change)
      (HandleEdit.oneOverOneSlidingId edit)
      (HandleEdit.oneOverOneStationaryId edit) :=
  match edit, change with
  | .oneOverOne _ _ _ _,
      .oneOverOne _ _ _ _ _ components _ _ => components

/-- Exact common-component correspondence stored by a 1-over-1 recipe. -/
def oneOverOneSame
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  oneOverOneSameOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Exact pair of components stored by a 1-over-1 recipe. -/
def oneOverOneComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      (oneOverOneSame metadata)
      (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit) :=
  oneOverOneComponentsOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Exact common-component correspondence stored by a 2-over-1 edit. -/
def twoOverOneSameOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverOne)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .twoOverOne _ _ _ _,
      .twoOverOne _ _ _ _ same _ _ _ => same

/-- Exact pair of components stored by a 2-over-1 edit. -/
def twoOverOneComponentsOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverOne)
    (change : ComponentIndexChange source target edit) :
    ResolvedSlideComponentPair source target
      (twoOverOneSameOfEdit edit change)
      (HandleEdit.twoOverOneSlidingId edit)
      (HandleEdit.twoOverOneStationaryId edit) :=
  match edit, change with
  | .twoOverOne _ _ _ _,
      .twoOverOne _ _ _ _ _ components _ _ => components

/-- Exact common-component correspondence stored by a 2-over-1 recipe. -/
def twoOverOneSame
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  twoOverOneSameOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Exact pair of components stored by a 2-over-1 recipe. -/
def twoOverOneComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      (twoOverOneSame metadata)
      (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit) :=
  twoOverOneComponentsOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Exact common-component correspondence stored by a 2-over-2 edit. -/
def twoOverTwoSameOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverTwo)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .twoOverTwo _ _ _ _,
      .twoOverTwo _ _ _ _ same _ _ _ => same

/-- Exact pair of components stored by a 2-over-2 edit. -/
def twoOverTwoComponentsOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverTwo)
    (change : ComponentIndexChange source target edit) :
    ResolvedSlideComponentPair source target
      (twoOverTwoSameOfEdit edit change)
      (HandleEdit.twoOverTwoSlidingId edit)
      (HandleEdit.twoOverTwoStationaryId edit) :=
  match edit, change with
  | .twoOverTwo _ _ _ _,
      .twoOverTwo _ _ _ _ _ components _ _ => components

/-- Exact common-component correspondence stored by a 2-over-2 recipe. -/
def twoOverTwoSame
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  twoOverTwoSameOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- Exact pair of components stored by a 2-over-2 recipe. -/
def twoOverTwoComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      (twoOverTwoSame metadata)
      (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit) :=
  twoOverTwoComponentsOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

/-- The three exact source-bound slide families. -/
inductive Request
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2) : Type (uH + 1)
  | oneOverOne
      (metadata :
        TableTwoMoveMetadata .oneOverOne
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts) :
      Request source target
  | twoOverOne
      (metadata :
        TableTwoMoveMetadata .twoOverOne
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts) :
      Request source target
  | twoOverTwo
      (metadata :
        TableTwoMoveMetadata .twoOverTwo
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts) :
      Request source target

namespace Request

def slideKind
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → SlideKind
  | .oneOverOne _ _ => .oneOverOne
  | .twoOverOne _ _ => .twoOverOne
  | .twoOverTwo _ _ => .twoOverTwo

def orientation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → BandOrientation
  | .oneOverOne metadata _ =>
      HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit
  | .twoOverOne metadata _ =>
      HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit
  | .twoOverTwo metadata _ =>
      HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit

def moveId
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → String
  | .oneOverOne metadata _ => metadata.moveId
  | .twoOverOne metadata _ => metadata.moveId
  | .twoOverTwo metadata _ => metadata.moveId

def sourceHash
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → String
  | .oneOverOne metadata _ => metadata.sourcePresentationHash
  | .twoOverOne metadata _ => metadata.sourcePresentationHash
  | .twoOverTwo metadata _ => metadata.sourcePresentationHash

def targetHash
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → String
  | .oneOverOne metadata _ => metadata.targetPresentationHash
  | .twoOverOne metadata _ => metadata.targetPresentationHash
  | .twoOverTwo metadata _ => metadata.targetPresentationHash

def slidingComponentId
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → String
  | .oneOverOne metadata _ =>
      HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit
  | .twoOverOne metadata _ =>
      HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit
  | .twoOverTwo metadata _ =>
      HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit

def stationaryComponentId
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target → String
  | .oneOverOne metadata _ =>
      HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit
  | .twoOverOne metadata _ =>
      HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit
  | .twoOverTwo metadata _ =>
      HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit

def window
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    (request : Request source target) →
      PresentationWindowEdit
        source.topology.formal target.topology.formal
  | .oneOverOne metadata _ => metadata.recipe.window
  | .twoOverOne metadata _ => metadata.recipe.window
  | .twoOverTwo metadata _ => metadata.recipe.window

def topologicalMove
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target →
      TopologicalTableTwoMove source.topology target.topology
  | .oneOverOne metadata countsSound =>
      .oneOverOne metadata countsSound
  | .twoOverOne metadata countsSound =>
      .twoOverOne metadata countsSound
  | .twoOverTwo metadata countsSound =>
      .twoOverTwo metadata countsSound

def sameComponentChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    Request source target →
      SameComponentIndexChange
        source.topology.formal target.topology.formal
  | .oneOverOne metadata _ =>
      oneOverOneSame metadata
  | .twoOverOne metadata _ =>
      twoOverOneSame metadata
  | .twoOverTwo metadata _ =>
      twoOverTwoSame metadata

def resolvedComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      request.sameComponentChange
      request.slidingComponentId request.stationaryComponentId := by
  cases request with
  | oneOverOne metadata countsSound =>
      exact oneOverOneComponents metadata
  | twoOverOne metadata countsSound =>
      exact twoOverOneComponents metadata
  | twoOverTwo metadata countsSound =>
      exact twoOverTwoComponents metadata

abbrev Block
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target) :=
  CanonicalSlideBlocks.Block (S := S) request.resolvedComponents

noncomputable def targetCycle
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target)
    (sourceCycle : source.DegreeTwoCycle) :
    target.DegreeTwoCycle :=
  (CycleTransport.ofMarkedH2Transport source target
      (enrichedMove request.topologicalMove).homologyTransport)
    |>.targetCycle sourceCycle

end Request

/-- The ordinary fixed-label graphical window used in the middle phase. -/
abbrev OrdinaryWindow
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :=
  OrdinaryLabelIndexedSlidingWindow
    𝒞.premodular
    (baerenzBarrett_ordinaryKirbySliding 𝒞.premodular)

/--
The exact attach-side calculation for one request.

This is only a readable name for the displayed proposition.  It does not
store proofs or combine separate obligations.
-/
abbrev AttachCalculation
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : request.Block (S := S))
    (ordinaryWindow : OrdinaryWindow 𝒞)
    (coefficient : S → K) :=
  (movingLabel stationaryLabel : S) →
    FusionLinearGeneratedCalculation
      𝒞.premodular.toFusionCategoryData η
      (CanonicalSlideBlocks.sourceWeight
          𝒞 η request.resolvedComponents sourceCycle remaining
          movingLabel stationaryLabel •
        LinearDiagram.atom (R := K)
          (CanonicalSlideBlocks.sourceTerm
            𝒞 request.resolvedComponents remaining
            movingLabel stationaryLabel))
      (coefficient movingLabel •
        (𝒞.premodular.quantumDimension stationaryLabel •
          LinearDiagram.atom (R := K)
            (ordinaryWindow.expandedBeforeTerm
              movingLabel stationaryLabel)))

/--
The exact detach-side calculation for one request.

Like `AttachCalculation`, this is a transparent abbreviation for one
proposition, not a proof-carrying package.
-/
abbrev DetachCalculation
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : request.Block (S := S))
    (ordinaryWindow : OrdinaryWindow 𝒞)
    (coefficient : S → K) :=
  (movingLabel stationaryLabel : S) →
    FusionLinearGeneratedCalculation
      𝒞.premodular.toFusionCategoryData η
      (coefficient movingLabel •
        (𝒞.premodular.quantumDimension stationaryLabel •
          LinearDiagram.atom (R := K)
            (ordinaryWindow.expandedAfterTerm
              movingLabel stationaryLabel)))
      (CanonicalSlideBlocks.targetWeight
          𝒞 η request.sameComponentChange
          request.resolvedComponents
          (request.targetCycle sourceCycle) remaining
          movingLabel stationaryLabel •
        LinearDiagram.atom (R := K)
          (CanonicalSlideBlocks.targetTerm
            𝒞 request.sameComponentChange
            request.resolvedComponents remaining
            movingLabel stationaryLabel))

/--
The visible attach--transport--detach movie for one exact source-bound block.

`attach` and `detach` live in the restricted tensor-automorphism coupon
grammar.  The middle transport is not a field: it is forced by
`ordinaryWindow` and hence proved by the cited ordinary Kirby-colour sliding
law.  `traceWindow` binds this categorical movie to the exact serialized
source and target event windows.
-/
structure Movie
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : request.Block (S := S)) where
  traceWindow :
    SourceBoundTraceWindow source target request.window
  ordinaryWindow : OrdinaryWindow 𝒞
  coefficient : S → K
  attach :
    AttachCalculation 𝒞 η request sourceCycle remaining
      ordinaryWindow coefficient
  detach :
    DetachCalculation 𝒞 η request sourceCycle remaining
      ordinaryWindow coefficient

namespace Movie

/-- Replay the three visible phases into the existing termwise slide grammar. -/
noncomputable def toTermWindow
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {request : Request source target}
    {sourceCycle : source.DegreeTwoCycle}
    {remaining : request.Block (S := S)}
    (movie : Movie 𝒞 η request sourceCycle remaining) :
    TermwiseCouponAdaptedKirbyColourSlideWindow 𝒞 η
      request.slideKind request.orientation
      request.moveId request.sourceHash request.targetHash
      request.slidingComponentId request.stationaryComponentId
      (CanonicalSlideBlocks.sourceWeight
        𝒞 η request.resolvedComponents sourceCycle remaining)
      (CanonicalSlideBlocks.targetWeight
        𝒞 η request.sameComponentChange request.resolvedComponents
        (request.targetCycle sourceCycle) remaining)
      (CanonicalSlideBlocks.sourceTerm
        𝒞 request.resolvedComponents remaining)
      (CanonicalSlideBlocks.targetTerm
        𝒞 request.sameComponentChange request.resolvedComponents remaining) where
  closedWindow := movie.ordinaryWindow
  coefficient := movie.coefficient
  beforeTermConversion := movie.attach
  afterTermConversion := movie.detach

end Movie

/--
Build a premodular slide movie from the four obligations written out as
separate arguments.

For a one-over-one or two-over-one slide this is the premodular route: the
caller must provide the direct tensor-unit cutting attach and detach
calculations.  No conversion of a dotted component into an ordinary
Kirby-coloured component occurs in this definition, and no modularity
hypothesis is available.
-/
noncomputable def premodularMovieOfExplicitCalculations
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : request.Block (S := S))
    (ordinaryWindow : OrdinaryWindow 𝒞)
    (coefficient : S → K)
    (directUnitCutAttach :
      AttachCalculation 𝒞 η request sourceCycle remaining
        ordinaryWindow coefficient)
    (directUnitCutDetach :
      DetachCalculation 𝒞 η request sourceCycle remaining
        ordinaryWindow coefficient) :
    Movie 𝒞 η request sourceCycle remaining where
  traceWindow :=
    SourceBoundTraceWindow.ofPresentationWindow
      source target request.window
  ordinaryWindow := ordinaryWindow
  coefficient := coefficient
  attach := directUnitCutAttach
  detach := directUnitCutDetach

/-
The old `standardMovie` axiom bundled every item below into one opaque value.
The declarations are deliberately split so an axiom audit exposes the exact
remaining obligations.
-/

/-!
### Modular-only one-handle reductions

The declarations in the next two sections are temporary procurement
boundaries, not independent target theorems.  In the modular proof they must
be replaced by derived constructions with this exact route:

1. replace every dotted one-handle boundary by its ordinary Kirby-coloured
   encircling component using modular open killing;
2. apply the two-over-two movie proved below; and
3. reverse the dotted-boundary replacement.

That derivation uses modularity and is intentionally unavailable to the
future premodular proof.  The premodular route must instead use the direct
tensor-unit cutting rule at a dotted component.
-/

/-! #### One-handle over one-handle -/

axiom premodularOneOverOneOrdinaryWindow
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    OrdinaryWindow 𝒞

axiom premodularOneOverOneCoefficient
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.oneOverOne metadata countsSound).Block (S := S)) :
    S → K

axiom modularOneOverOneAttach
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.oneOverOne metadata countsSound).Block (S := S)) :
    AttachCalculation 𝒞.premodular η
      (Request.oneOverOne metadata countsSound) sourceCycle remaining
      (premodularOneOverOneOrdinaryWindow
        𝒞.premodular metadata countsSound)
      (premodularOneOverOneCoefficient
        𝒞.premodular η metadata countsSound sourceCycle remaining)

axiom modularOneOverOneDetach
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.oneOverOne metadata countsSound).Block (S := S)) :
    DetachCalculation 𝒞.premodular η
      (Request.oneOverOne metadata countsSound) sourceCycle remaining
      (premodularOneOverOneOrdinaryWindow
        𝒞.premodular metadata countsSound)
      (premodularOneOverOneCoefficient
        𝒞.premodular η metadata countsSound sourceCycle remaining)

/-! #### Two-handle over one-handle -/

axiom premodularTwoOverOneOrdinaryWindow
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    OrdinaryWindow 𝒞

axiom premodularTwoOverOneCoefficient
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverOne metadata countsSound).Block (S := S)) :
    S → K

axiom modularTwoOverOneAttach
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverOne metadata countsSound).Block (S := S)) :
    AttachCalculation 𝒞.premodular η
      (Request.twoOverOne metadata countsSound) sourceCycle remaining
      (premodularTwoOverOneOrdinaryWindow
        𝒞.premodular metadata countsSound)
      (premodularTwoOverOneCoefficient
        𝒞.premodular η metadata countsSound sourceCycle remaining)

axiom modularTwoOverOneDetach
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverOne metadata countsSound).Block (S := S)) :
    DetachCalculation 𝒞.premodular η
      (Request.twoOverOne metadata countsSound) sourceCycle remaining
      (premodularTwoOverOneOrdinaryWindow
        𝒞.premodular metadata countsSound)
      (premodularTwoOverOneCoefficient
        𝒞.premodular η metadata countsSound sourceCycle remaining)

/-!
### Fundamental two-handle over two-handle theorem

This is the category-theoretic core shared by the modular proof and the
future premodular proof.  It contains no dotted-component replacement.
-/

axiom premodularTwoOverTwoOrdinaryWindow
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    OrdinaryWindow 𝒞

/--
The common coefficient in a 2-over-2 block is the source weight with the
stationary label specialized to the tensor unit.

This removes the stationary Kirby-colour dimension and tensor-automorphism
scalar, both of which are one on the unit.  The attach/detach calculations
must prove that the general stationary-label factor is represented by the
visible coupon movie; it is no longer hidden in an arbitrary coefficient.
-/
noncomputable def premodularTwoOverTwoCoefficient
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S)) :
    S → K :=
  fun movingLabel =>
    CanonicalSlideBlocks.sourceWeight
      𝒞 η
      (Request.twoOverTwo metadata countsSound).resolvedComponents
      sourceCycle remaining movingLabel
      𝒞.premodular.toFusionCategoryData.unitIndex

theorem twoOverTwo_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    (enrichedMove
        (.twoOverTwo metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.twoOverTwo metadata countsSound)).chainEquivalence := by
  rfl

noncomputable def premodularTwoOverTwoExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    SameComponentCycleExponentTransport source target
      (Request.twoOverTwo metadata countsSound).sameComponentChange
      sourceCycle
      ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).twoOverTwoCoordinates
      metadata countsSound
  refine { exponent_sound := ?_ }
  intro targetIndex
  change
    target.topology.cycleComponentExponent
        (forwardDegreeTwoCycle
          (MarkedH2Transport.chainEquivalence
            (TableTwoMove.homologyTransport
              (enrichedMove (.twoOverTwo metadata countsSound))))
          sourceCycle)
        (componentAt target.topology.formal targetIndex) =
      source.topology.cycleComponentExponent sourceCycle
        (componentAt source.topology.formal
          ((twoOverTwoSame metadata).targetToSource targetIndex))
  rw [twoOverTwo_enriched_chainEquivalence metadata countsSound]
  exact coordinateLaw.exponent_sound sourceCycle targetIndex

theorem premodularTwoOverTwoCoefficient_apply
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel : S) :
    premodularTwoOverTwoCoefficient
        𝒞 η metadata countsSound sourceCycle remaining movingLabel =
      CanonicalSlideBlocks.sourceWeight
        𝒞 η
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        sourceCycle remaining movingLabel
      𝒞.premodular.toFusionCategoryData.unitIndex := by
  rfl

theorem premodularTwoOverTwoCoefficient_eq_targetUnitWeight
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel : S) :
    premodularTwoOverTwoCoefficient
        𝒞 η metadata countsSound sourceCycle remaining movingLabel =
      CanonicalSlideBlocks.targetWeight
        𝒞 η
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle)
        remaining movingLabel
        𝒞.premodular.toFusionCategoryData.unitIndex := by
  unfold premodularTwoOverTwoCoefficient
  unfold CanonicalSlideBlocks.sourceWeight
  unfold CanonicalSlideBlocks.targetWeight
  unfold CanonicalSlideBlocks.targetLabeling
  exact
    SameComponentCycleExponentTransport.cycleGlobalWeight_transport
      𝒞 η
      (Request.twoOverTwo metadata countsSound).sameComponentChange
      (premodularTwoOverTwoExponentTransport
        metadata countsSound sourceCycle)
      (CanonicalSlideBlocks.sourceLabeling
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel
        𝒞.premodular.toFusionCategoryData.unitIndex)

noncomputable axiom premodularTwoOverTwoAttachContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    Context C
      (.atom (𝒞.premodular.simple stationaryLabel))
      (.atom (𝒞.premodular.simple stationaryLabel))
      .unit .unit

noncomputable def premodularTwoOverTwoSourceStationaryExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  source.cycleComponentExponent sourceCycle
    (componentAt source.topology.formal
      (Request.resolvedComponents
        (Request.twoOverTwo metadata countsSound)).stationarySourceIndex)

axiom premodularTwoOverTwoSourceTerm_eq_attachIdentity
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalSlideBlocks.sourceTerm 𝒞
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel =
      Context.plug C
        (premodularTwoOverTwoAttachContext
          𝒞 η metadata countsSound sourceCycle remaining
          movingLabel stationaryLabel)
        (atomicCoupon "identity"
          (𝟙 (𝒞.premodular.simple stationaryLabel)))

axiom premodularTwoOverTwoExpandedBefore_eq_attachCoupon
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    OrdinaryLabelIndexedSlidingWindow.expandedBeforeTerm
        (premodularTwoOverTwoOrdinaryWindow 𝒞 metadata countsSound)
        movingLabel stationaryLabel =
      Context.plug C
        (premodularTwoOverTwoAttachContext
          𝒞 η metadata countsSound sourceCycle remaining
          movingLabel stationaryLabel)
        (atomicCoupon "tensor-automorphism-power"
          (𝒞.premodular.toFusionCategoryData.automorphismCouponPower
            η stationaryLabel
            (premodularTwoOverTwoSourceStationaryExponent
              metadata countsSound sourceCycle)))

noncomputable def premodularTwoOverTwoAttach
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S)) :
    AttachCalculation 𝒞 η
      (Request.twoOverTwo metadata countsSound) sourceCycle remaining
      (premodularTwoOverTwoOrdinaryWindow 𝒞 metadata countsSound)
      (premodularTwoOverTwoCoefficient
        𝒞 η metadata countsSound sourceCycle remaining) := by
  intro movingLabel stationaryLabel
  let request := Request.twoOverTwo metadata countsSound
  let context :=
    premodularTwoOverTwoAttachContext
      𝒞 η metadata countsSound sourceCycle remaining
      movingLabel stationaryLabel
  let exponent :=
    premodularTwoOverTwoSourceStationaryExponent
      metadata countsSound sourceCycle
  have calculation :=
    FusionLinearGeneratedCalculation.symm
      (FusionLinearGeneratedCalculation.simplePower
        (data := 𝒞.premodular.toFusionCategoryData)
        (automorphism := η)
        stationaryLabel exponent context)
  have scaled :=
    FusionLinearGeneratedCalculation.smul
      (premodularTwoOverTwoCoefficient
          𝒞 η metadata countsSound sourceCycle remaining movingLabel *
        𝒞.premodular.quantumDimension stationaryLabel)
      calculation
  rw [CanonicalSlideBlocks.sourceWeight_factor_stationary]
  rw [premodularTwoOverTwoSourceTerm_eq_attachIdentity
    𝒞 η metadata countsSound sourceCycle remaining
      movingLabel stationaryLabel]
  rw [premodularTwoOverTwoExpandedBefore_eq_attachCoupon
    𝒞 η metadata countsSound sourceCycle remaining
      movingLabel stationaryLabel]
  unfold CanonicalPresentation.cycleComponentWeight
  simpa only [request, context, exponent,
    premodularTwoOverTwoCoefficient,
    premodularTwoOverTwoSourceStationaryExponent,
    smul_smul, mul_assoc, mul_left_comm, mul_comm] using scaled

noncomputable def premodularTwoOverTwoTargetStationaryExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  let request := Request.twoOverTwo metadata countsSound
  target.cycleComponentExponent (request.targetCycle sourceCycle)
    (componentAt target.topology.formal
      request.resolvedComponents.stationaryTargetIndex)

noncomputable axiom premodularTwoOverTwoDetachContext
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    Context C
      (.atom (𝒞.premodular.simple stationaryLabel))
      (.atom (𝒞.premodular.simple stationaryLabel))
      .unit .unit

axiom premodularTwoOverTwoExpandedAfter_eq_detachCoupon
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    OrdinaryLabelIndexedSlidingWindow.expandedAfterTerm
        (premodularTwoOverTwoOrdinaryWindow 𝒞 metadata countsSound)
        movingLabel stationaryLabel =
      Context.plug C
        (premodularTwoOverTwoDetachContext
          𝒞 η metadata countsSound sourceCycle remaining
          movingLabel stationaryLabel)
        (atomicCoupon "tensor-automorphism-power"
          (𝒞.premodular.toFusionCategoryData.automorphismCouponPower
            η stationaryLabel
            (premodularTwoOverTwoTargetStationaryExponent
              metadata countsSound sourceCycle)))

axiom premodularTwoOverTwoTargetTerm_eq_detachIdentity
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S))
    (movingLabel stationaryLabel : S) :
    CanonicalSlideBlocks.targetTerm 𝒞
        (Request.twoOverTwo metadata countsSound).sameComponentChange
        (Request.twoOverTwo metadata countsSound).resolvedComponents
        remaining movingLabel stationaryLabel =
      Context.plug C
        (premodularTwoOverTwoDetachContext
          𝒞 η metadata countsSound sourceCycle remaining
          movingLabel stationaryLabel)
        (atomicCoupon "identity"
          (𝟙 (𝒞.premodular.simple stationaryLabel)))

noncomputable def premodularTwoOverTwoDetach
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S)) :
    DetachCalculation 𝒞 η
      (Request.twoOverTwo metadata countsSound) sourceCycle remaining
      (premodularTwoOverTwoOrdinaryWindow 𝒞 metadata countsSound)
      (premodularTwoOverTwoCoefficient
        𝒞 η metadata countsSound sourceCycle remaining) := by
  intro movingLabel stationaryLabel
  let request := Request.twoOverTwo metadata countsSound
  let context :=
    premodularTwoOverTwoDetachContext
      𝒞 η metadata countsSound sourceCycle remaining
      movingLabel stationaryLabel
  let exponent :=
    premodularTwoOverTwoTargetStationaryExponent
      metadata countsSound sourceCycle
  have calculation :=
    FusionLinearGeneratedCalculation.simplePower
      (data := 𝒞.premodular.toFusionCategoryData)
      (automorphism := η)
      stationaryLabel exponent context
  have scaled :=
    FusionLinearGeneratedCalculation.smul
      (premodularTwoOverTwoCoefficient
          𝒞 η metadata countsSound sourceCycle remaining movingLabel *
        𝒞.premodular.quantumDimension stationaryLabel)
      calculation
  rw [CanonicalSlideBlocks.targetWeight_factor_stationary]
  rw [premodularTwoOverTwoExpandedAfter_eq_detachCoupon
    𝒞 η metadata countsSound sourceCycle remaining
      movingLabel stationaryLabel]
  rw [premodularTwoOverTwoTargetTerm_eq_detachIdentity
    𝒞 η metadata countsSound sourceCycle remaining
      movingLabel stationaryLabel]
  rw [← premodularTwoOverTwoCoefficient_eq_targetUnitWeight
    𝒞 η metadata countsSound sourceCycle remaining movingLabel]
  unfold CanonicalPresentation.cycleComponentWeight
  simpa only [request, context, exponent,
    premodularTwoOverTwoTargetStationaryExponent,
    smul_smul, mul_assoc, mul_left_comm, mul_comm] using scaled

/--
The complete source-bound 2-over-2 movie needs only a premodular category.

All character-dependent coefficient and coupon calculations are the derived
definitions above.  The remaining inputs are the standard ordinary sliding
window and its exact diagrammatic endpoint binding.
-/
noncomputable def premodularTwoOverTwoMovie
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S)) :
    Movie 𝒞 η (Request.twoOverTwo metadata countsSound)
      sourceCycle remaining where
  traceWindow :=
    SourceBoundTraceWindow.ofPresentationWindow
      source target metadata.recipe.window
  ordinaryWindow :=
    premodularTwoOverTwoOrdinaryWindow 𝒞 metadata countsSound
  coefficient :=
    premodularTwoOverTwoCoefficient
      𝒞 η metadata countsSound sourceCycle remaining
  attach :=
    premodularTwoOverTwoAttach
      𝒞 η metadata countsSound sourceCycle remaining
  detach :=
    premodularTwoOverTwoDetach
      𝒞 η metadata countsSound sourceCycle remaining

/--
One complete fixed-complement 2-over-2 block preserves evaluation.

The moving and stationary labels are both still summed.  Therefore this
statement cannot hide cancellation by dropping a simple-label sector.
-/
theorem premodularTwoOverTwoBlock_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      (Request.twoOverTwo metadata countsSound).Block (S := S)) :
    LinearDiagram.eval
        (CanonicalSlideBlocks.sourceBlock
          𝒞 η
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          sourceCycle remaining) =
      LinearDiagram.eval
        (CanonicalSlideBlocks.targetBlock
          𝒞 η
          (Request.twoOverTwo metadata countsSound).sameComponentChange
          (Request.twoOverTwo metadata countsSound).resolvedComponents
          ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle)
          remaining) := by
  exact
    CouponAdaptedKirbyColourSlideWindow.eval_eq
      ((premodularTwoOverTwoMovie
        𝒞 η metadata countsSound sourceCycle remaining).toTermWindow.toWindow)

/--
Premodular twisted evaluation is invariant under the complete 2-over-2
handle slide, before normalization.

This is the full finite-label statement: Lean derives both denominator
decompositions and sums the blockwise theorem over every complementary
labeling.
-/
theorem premodularTwoOverTwo_cycleLinearDiagram_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 η sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 η
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle)) := by
  classical
  rw [CanonicalSlideBlocks.source_decomposition
    𝒞 η
    (Request.twoOverTwo metadata countsSound).resolvedComponents
    sourceCycle]
  rw [CanonicalSlideBlocks.target_decomposition
    𝒞 η
    (Request.twoOverTwo metadata countsSound).sameComponentChange
    (Request.twoOverTwo metadata countsSound).resolvedComponents
    ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro remaining _
  exact premodularTwoOverTwoBlock_eval_eq
    𝒞 η metadata countsSound sourceCycle remaining

/--
Assemble the explicitly listed obligations.  This theorem is no longer an
axiom and contributes no additional mathematical assumption.
-/
noncomputable def standardMovie
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (request : Request source target)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : request.Block (S := S)) :
    Movie 𝒞.premodular η request sourceCycle remaining := by
  cases request with
  | oneOverOne metadata countsSound =>
      exact
        { traceWindow :=
            SourceBoundTraceWindow.ofPresentationWindow
              source target metadata.recipe.window
          ordinaryWindow :=
            premodularOneOverOneOrdinaryWindow
              𝒞.premodular metadata countsSound
          coefficient :=
            premodularOneOverOneCoefficient
              𝒞.premodular η metadata countsSound sourceCycle remaining
          attach :=
            modularOneOverOneAttach
              𝒞 η metadata countsSound sourceCycle remaining
          detach :=
            modularOneOverOneDetach
              𝒞 η metadata countsSound sourceCycle remaining }
  | twoOverOne metadata countsSound =>
      exact
        { traceWindow :=
            SourceBoundTraceWindow.ofPresentationWindow
              source target metadata.recipe.window
          ordinaryWindow :=
            premodularTwoOverOneOrdinaryWindow
              𝒞.premodular metadata countsSound
          coefficient :=
            premodularTwoOverOneCoefficient
              𝒞.premodular η metadata countsSound sourceCycle remaining
          attach :=
            modularTwoOverOneAttach
              𝒞 η metadata countsSound sourceCycle remaining
          detach :=
            modularTwoOverOneDetach
              𝒞 η metadata countsSound sourceCycle remaining }
  | twoOverTwo metadata countsSound =>
      exact
        { traceWindow :=
            SourceBoundTraceWindow.ofPresentationWindow
              source target metadata.recipe.window
          ordinaryWindow :=
            premodularTwoOverTwoOrdinaryWindow
              𝒞.premodular metadata countsSound
          coefficient :=
            premodularTwoOverTwoCoefficient
              𝒞.premodular η metadata countsSound sourceCycle remaining
          attach :=
            premodularTwoOverTwoAttach
              𝒞.premodular η metadata countsSound sourceCycle remaining
          detach :=
            premodularTwoOverTwoDetach
              𝒞.premodular η metadata countsSound sourceCycle remaining }

end TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
