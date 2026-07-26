import TwistedYetter.Kirby.CanonicalCycleLocalInvariance
import TwistedYetter.Kirby.CanonicalCancellationTraceBinding
import TwistedYetter.Kirby.CanonicalComponentSupport
import TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
import TwistedYetter.Kirby.CanonicalSourceBackedMove

/-!
# Literature boundary for canonical graphical endpoint realization

This module isolates the remaining diagrammatic input not reconstructed from
serialized planar embeddings:

1. an exact special-Kirby local recipe compiles to one of the restricted
   eight cycle-safe graphical proof grammars.

This diagrammatic/topological realization statement does not state that an
evaluator is invariant and cannot return an equality in the ground field.
All categorical soundness, finite Kirby-colour sums, normalization, and
reverse-move bookkeeping are proved after this boundary.

Selected sources:

* Bärenz--Barrett, Lemmas 3.1, 3.3--3.4, Table 2, and Theorem 3.9,
  journal pages 680--687;
* Shum's coherence theorem for tortile categories for the framed ribbon
  graphical calculus.

Lean does not reconstruct ambient planar isotopies, attaching-band
neighbourhoods, or the placement of every coupon cut from the raw serialized
event list in this module.  That exact limitation is intentionally visible
in six explicit inputs below.  Five inputs record category-neutral cycle
geometry; one source-bound movie covers all three slide roles without hiding
their exact request metadata.

There is deliberately no unproved global dual-boundary movie axiom hidden in
this file.  The former apparent counterexample used the primal handle chain
where Tham's evaluator uses the upside-down dual chain; it remains only a
regression test for that convention error.  The actual remaining obligation
is to compile every dual `d3` boundary change through the primal dotted
one-handle and its Tham `k = 3` vacuum projector.
-/

namespace TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalCycleSlideGeometry
open TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundGeometricH2Compilation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Exact denominator of the imported diagrammatic statements. -/
inductive AssumptionClass where
  | framedIsotopyTypedDerivation
  | sourceBoundCouponAdaptedSlideMovie
  | oneTwoBirthTypedDerivation
  | oneTwoDeathTypedDerivation
  | twoThreeBirthTypedDerivation
  | twoThreeDeathTypedDerivation
  deriving Repr, BEq, DecidableEq

def requiredAssumptionClasses : List AssumptionClass :=
  [
    .framedIsotopyTypedDerivation,
    .sourceBoundCouponAdaptedSlideMovie,
    .oneTwoBirthTypedDerivation,
    .oneTwoDeathTypedDerivation,
    .twoThreeBirthTypedDerivation,
    .twoThreeDeathTypedDerivation
  ]

theorem required_assumption_class_count :
    requiredAssumptionClasses.length = 6 := by
  rfl

theorem required_assumption_classes_unique :
    requiredAssumptionClasses.Nodup := by
  decide

/-- Stable repository references for the imported geometric statements. -/
def sourceRefs : List String :=
  [
    "ref:baerenz-barrett-dichromatic-2018",
    "ref:shum-tortile-1994"
  ]

/-- Exact imported meaning of the first diagrammatic statement. -/
def tableTwoEndpointExactScope : String :=
  "Each source-bound special-Kirby Table 2 recipe, interpreted by the "
    ++ "canonical component trace and the chain-transported explicit cycle, "
    ++ "has a proof in exactly one restricted framed-isotopy, whole-sum "
    ++ "slide, or isolated-cancellation grammar."

/-- Machine-visible scope of the still-open global dual-boundary bridge. -/
def dualBoundaryIntegrationScope : String :=
  "The wrong-primal-chain counterexample is retracted. Lean now compiles a "
    ++ "complete dotted-boundary GeometrySystem through the Tham k=3 vacuum "
    ++ "identity and proves H2 representative independence. The final "
    ++ "presentation domain now carries this geometry certification, so no "
    ++ "global geometry axiom is asserted for malformed raw syntax."

/-- What none of the remaining diagrammatic inputs is allowed to say. -/
def sourceScopeCaveat : String :=
  "The six inputs supply no scalar equality, final EvalC equality, "
    ++ "arbitrary evaluator, a homology map, or a Kirby-completeness theorem. "
    ++ "Lean does not compile raw planar coordinates and attaching-band "
    ++ "neighbourhoods into these proof terms."

/--
The eight transparent graphical realizations of source-bound Table 2 moves.

Each constructor records only the local ribbon/coupon/cycle geometry needed
by its named move.  It contains no evaluator value, scalar equality, or
`LocalCycleCalculation`; categorical invariance is derived below.
-/
inductive GraphicalMoveRealization
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2} :
    (move : TopologicalTableTwoMove source.topology target.topology) →
      Type (max (max uK uC) (max vC (uH + 1)))
  | framedIsotopy
      (metadata :
        TableTwoMoveMetadata .framedIsotopy
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (geometry :
        FramedIsotopyCycleGeometry source target
          (enrichedMove
            (.framedIsotopy metadata countsSound)).homologyTransport.targetClass) :
      GraphicalMoveRealization 𝒞 η
        (.framedIsotopy metadata countsSound)
  | oneOverOne
      (metadata :
        TableTwoMoveMetadata .oneOverOne
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (geometry :
        OrdinaryCycleSlideGeometry 𝒞.premodular η source target
          (enrichedMove
            (.oneOverOne metadata countsSound)).homologyTransport
          .oneOverOne
          (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
          metadata.moveId
          metadata.sourcePresentationHash metadata.targetPresentationHash
          (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
          (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit)) :
      GraphicalMoveRealization 𝒞 η
        (.oneOverOne metadata countsSound)
  | twoOverOne
      (metadata :
        TableTwoMoveMetadata .twoOverOne
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (geometry :
        OrdinaryCycleSlideGeometry 𝒞.premodular η source target
          (enrichedMove
            (.twoOverOne metadata countsSound)).homologyTransport
          .twoOverOne
          (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
          metadata.moveId
          metadata.sourcePresentationHash metadata.targetPresentationHash
          (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
          (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit)) :
      GraphicalMoveRealization 𝒞 η
        (.twoOverOne metadata countsSound)
  | twoOverTwo
      (metadata :
        TableTwoMoveMetadata .twoOverTwo
          source.topology target.topology)
      (countsSound : source.topology.counts = target.topology.counts)
      (geometry :
        GeneralizedCycleSlideGeometry 𝒞.premodular η source target
          (enrichedMove
            (.twoOverTwo metadata countsSound)).homologyTransport
          (HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit)
          metadata.moveId
          metadata.sourcePresentationHash metadata.targetPresentationHash
          (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
          (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit)) :
      GraphicalMoveRealization 𝒞 η
        (.twoOverTwo metadata countsSound)
  | oneTwoBirth
      (metadata :
        TableTwoMoveMetadata .oneTwoBirth
          source.topology target.topology)
      (countsSound :
        target.topology.counts = source.topology.counts.addOneTwo)
      (geometry :
        OneTwoBirthCycleGeometry source target
          (enrichedMove
            (.oneTwoBirth metadata countsSound)).homologyTransport.targetClass) :
      GraphicalMoveRealization 𝒞 η
        (.oneTwoBirth metadata countsSound)
  | oneTwoDeath
      (metadata :
        TableTwoMoveMetadata .oneTwoDeath
          source.topology target.topology)
      (countsSound :
        source.topology.counts = target.topology.counts.addOneTwo)
      (geometry :
        OneTwoDeathCycleGeometry source target
          (enrichedMove
            (.oneTwoDeath metadata countsSound)).homologyTransport) :
      GraphicalMoveRealization 𝒞 η
        (.oneTwoDeath metadata countsSound)
  | twoThreeBirth
      (metadata :
        TableTwoMoveMetadata .twoThreeBirth
          source.topology target.topology)
      (countsSound :
        target.topology.counts = source.topology.counts.addTwoThree)
      (geometry :
        TwoThreeBirthCycleGeometry source target
          (enrichedMove
            (.twoThreeBirth metadata countsSound)).homologyTransport.targetClass) :
      GraphicalMoveRealization 𝒞 η
        (.twoThreeBirth metadata countsSound)
  | twoThreeDeath
      (metadata :
        TableTwoMoveMetadata .twoThreeDeath
          source.topology target.topology)
      (countsSound :
        source.topology.counts = target.topology.counts.addTwoThree)
      (geometry :
        TwoThreeDeathCycleGeometry source target
          (enrichedMove
            (.twoThreeDeath metadata countsSound)).homologyTransport) :
      GraphicalMoveRealization 𝒞 η
        (.twoThreeDeath metadata countsSound)

namespace GraphicalMoveRealization

/--
Compile transparent graphical geometry to the restricted categorical proof
grammar.  This is the exact eight-case topology-to-algebra correspondence.
-/
noncomputable def toLocalCycleCalculation
    {𝒞 : ModularFusionCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {move : TopologicalTableTwoMove source.topology target.topology}
    (realization : GraphicalMoveRealization 𝒞 η move) :
    LocalCycleCalculation 𝒞 η (enrichedMove move) := by
  cases realization with
  | framedIsotopy metadata countsSound geometry =>
      exact .framedIsotopy metadata countsSound
        (enrichedMove (.framedIsotopy metadata countsSound)).homologyTransport
        geometry
  | oneOverOne metadata countsSound geometry =>
      exact .oneOverOne metadata countsSound
        (enrichedMove
          (.oneOverOne metadata countsSound)).homologyTransport
        geometry
  | twoOverOne metadata countsSound geometry =>
      exact .twoOverOne metadata countsSound
        (enrichedMove
          (.twoOverOne metadata countsSound)).homologyTransport
        geometry
  | twoOverTwo metadata countsSound geometry =>
      exact .twoOverTwo metadata countsSound
        (enrichedMove
          (.twoOverTwo metadata countsSound)).homologyTransport
        geometry
  | oneTwoBirth metadata countsSound geometry =>
      exact .oneTwoBirth metadata countsSound
        (enrichedMove (.oneTwoBirth metadata countsSound)).homologyTransport
        geometry
  | oneTwoDeath metadata countsSound geometry =>
      exact .oneTwoDeath metadata countsSound
        (enrichedMove (.oneTwoDeath metadata countsSound)).homologyTransport
        geometry
  | twoThreeBirth metadata countsSound geometry =>
      exact .twoThreeBirth metadata countsSound
        (enrichedMove (.twoThreeBirth metadata countsSound)).homologyTransport
        geometry
  | twoThreeDeath metadata countsSound geometry =>
      exact .twoThreeDeath metadata countsSound
        (enrichedMove (.twoThreeDeath metadata countsSound)).homologyTransport
        geometry

end GraphicalMoveRealization

/-
The literature boundary is deliberately split by directed move kind.

Five inputs below are category-neutral cycle geometry.  The one shared slide
movie mentions `𝒞` and `η`, because its proof object contains the actual
Kirby-colour sliding calculation.  The three slide roles remain explicit
constructors of its request type, while sharing one exact procurement
boundary.
-/

/--
The component correspondence already stored in a framed-isotopy recipe.

This projection is total because the recipe's `ComponentIndexChange` is
indexed by the exact `HandleEdit`; a correspondence for another move kind
cannot inhabit this type.
-/
def framedIsotopyComponentChangeOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .framedIsotopy)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  framedIsotopySameChangeOfEdit edit change

/-- Project the same-component correspondence from exact move metadata. -/
def framedIsotopyComponentChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  framedIsotopyComponentChangeOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem framedIsotopy_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    (enrichedMove
        (.framedIsotopy metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.framedIsotopy metadata countsSound)).chainEquivalence := by
  rfl

/--
Exact exponent transport for framed isotopy, derived from standard
handle-chain coordinate naturality rather than graphical input.
-/
noncomputable def framedIsotopyExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    SameComponentCycleExponentTransport source target
      (framedIsotopyComponentChange metadata)
      sourceCycle
      ((CycleTransport.ofMarkedH2Transport source target
        (enrichedMove
          (.framedIsotopy metadata countsSound)).homologyTransport)
        |>.targetCycle sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).framedIsotopyCoordinates
      metadata countsSound
  refine { exponent_sound := ?_ }
  intro targetIndex
  change
    target.topology.cycleComponentExponent
        (forwardDegreeTwoCycle
          ((enrichedMove
            (.framedIsotopy metadata countsSound)).homologyTransport.chainEquivalence)
          sourceCycle)
        (componentAt target.topology.formal targetIndex) =
      source.topology.cycleComponentExponent sourceCycle
        (componentAt source.topology.formal
          ((framedIsotopySameChange metadata).targetToSource targetIndex))
  rw [framedIsotopy_enriched_chainEquivalence metadata countsSound]
  exact coordinateLaw.exponent_sound sourceCycle targetIndex

/--
The genuinely missing typed movie for a framed isotopy.

The component correspondence is no longer supplied here: it is projected
from the source-bound recipe, and standard handle-chain naturality derives
cycle-coordinate transport.  This witness contains only the typed
free-diagram isotopy that cannot yet be reconstructed from the current
serialized `GraphicalEditProgram`.
-/
structure FramedIsotopyTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) where
  termIsotopy :
    GeneratedIsotopy
      source.componentTermDiagram target.componentTermDiagram

/--
Endpoint-bound local movie for one framed-isotopy recipe.

The marked handle-chain map is fixed by `enrichedMove`; this input cannot
replace it with an independently chosen cycle transport.
-/
axiom standardFramedIsotopyTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    FramedIsotopyTypedDerivation source target metadata countsSound

/--
Assemble the endpoint movie from the recipe-owned component correspondence
and the remaining typed derivation.
-/
noncomputable def standardFramedIsotopyEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    FramedIsotopyEndpointMovie source target
      (enrichedMove
        (.framedIsotopy metadata countsSound)).homologyTransport where
  componentChange := framedIsotopyComponentChange metadata
  exponentTransport :=
    framedIsotopyExponentTransport metadata countsSound
  termIsotopy :=
    (standardFramedIsotopyTypedDerivation metadata countsSound)
      |>.termIsotopy

/--
Complete framed-isotopy cycle geometry derived from the endpoint movie and
the canonical marked handle-chain transport.
-/
noncomputable def standardFramedIsotopyCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .framedIsotopy
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    FramedIsotopyCycleGeometry source target
      (enrichedMove
        (.framedIsotopy metadata countsSound)).homologyTransport.targetClass :=
  (standardFramedIsotopyEndpointMovie metadata countsSound).toCycleGeometry

/-- Project the same-component correspondence from a 1-over-1 edit. -/
def oneOverOneComponentChangeOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneOverOne)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .oneOverOne _ _ _ _,
      .oneOverOne _ _ _ _ same _ _ _ => same

/-- Resolve the two actual component indices named by a 1-over-1 edit. -/
def oneOverOneResolvedComponentsOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneOverOne)
    (change : ComponentIndexChange source target edit) :
    ResolvedSlideComponentPair source target
      (oneOverOneComponentChangeOfEdit edit change)
      (HandleEdit.oneOverOneSlidingId edit)
      (HandleEdit.oneOverOneStationaryId edit) :=
  match edit, change with
  | .oneOverOne _ _ _ _,
      .oneOverOne _ _ _ _ _ components _ _ => components

/-- Project the same-component correspondence from exact 1-over-1 metadata. -/
def oneOverOneComponentChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  CanonicalSourceBoundSlideMovie.oneOverOneSame metadata

/-- The source/target finite indices selected by exact 1-over-1 metadata. -/
def oneOverOneResolvedComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      (oneOverOneComponentChange metadata)
      (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit) :=
  CanonicalSourceBoundSlideMovie.oneOverOneComponents metadata

/--
The coupon-adapted local dotted-over-dotted window for one canonical
double-sum block.

This is the remaining literature/topology input.  It must expose the actual
closed window, coefficient, restricted coupon conversions, and source-bound
move metadata; it cannot assert an evaluator equality or denominator
completeness.
-/
noncomputable def standardOneOverOneCycleTermWindow
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      CanonicalSlideBlocks.Block (S := S)
        (oneOverOneResolvedComponents metadata)) :
    TermwiseCouponAdaptedKirbyColourSlideWindow 𝒞.premodular η
      .oneOverOne
      (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit)
      (CanonicalSlideBlocks.sourceWeight
        𝒞.premodular η (oneOverOneResolvedComponents metadata)
        sourceCycle remaining)
      (CanonicalSlideBlocks.targetWeight
        𝒞.premodular η (oneOverOneComponentChange metadata)
        (oneOverOneResolvedComponents metadata)
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.oneOverOne metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)
        remaining)
      (CanonicalSlideBlocks.sourceTerm
        𝒞.premodular (oneOverOneResolvedComponents metadata) remaining)
      (CanonicalSlideBlocks.targetTerm
        𝒞.premodular (oneOverOneComponentChange metadata)
        (oneOverOneResolvedComponents metadata) remaining) := by
  let request :
      CanonicalSourceBoundSlideMovie.Request source target :=
    .oneOverOne metadata countsSound
  let requestRemaining :
      request.Block (S := S) := by
    simpa only [
      request,
      CanonicalSourceBoundSlideMovie.Request.Block,
      CanonicalSourceBoundSlideMovie.Request.resolvedComponents,
      oneOverOneResolvedComponents,
      oneOverOneResolvedComponentsOfEdit,
      id_eq
    ] using remaining
  simpa only [
    request,
    requestRemaining,
    CanonicalSourceBoundSlideMovie.Request.slideKind,
    CanonicalSourceBoundSlideMovie.Request.orientation,
    CanonicalSourceBoundSlideMovie.Request.moveId,
    CanonicalSourceBoundSlideMovie.Request.sourceHash,
    CanonicalSourceBoundSlideMovie.Request.targetHash,
    CanonicalSourceBoundSlideMovie.Request.slidingComponentId,
    CanonicalSourceBoundSlideMovie.Request.stationaryComponentId,
    CanonicalSourceBoundSlideMovie.Request.sameComponentChange,
    CanonicalSourceBoundSlideMovie.Request.resolvedComponents,
    CanonicalSourceBoundSlideMovie.Request.targetCycle,
    CanonicalSourceBoundSlideMovie.Request.topologicalMove,
    oneOverOneComponentChange,
    oneOverOneComponentChangeOfEdit,
    oneOverOneResolvedComponents,
    oneOverOneResolvedComponentsOfEdit,
    id_eq
  ] using
    (CanonicalSourceBoundSlideMovie.standardMovie
      𝒞 η request sourceCycle requestRemaining).toTermWindow

/--
Reassemble the exact 1-over-1 double-sum window from its labelwise coupon
movies.
-/
noncomputable def standardOneOverOneCycleBlockWindow
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      CanonicalSlideBlocks.Block (S := S)
        (oneOverOneResolvedComponents metadata)) :
    CouponAdaptedKirbyColourSlideWindow 𝒞.premodular η
      .oneOverOne
      (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit)
      (CanonicalSlideBlocks.sourceBlock
        𝒞.premodular η (oneOverOneResolvedComponents metadata)
        sourceCycle remaining)
      (CanonicalSlideBlocks.targetBlock
        𝒞.premodular η (oneOverOneComponentChange metadata)
        (oneOverOneResolvedComponents metadata)
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.oneOverOne metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)
        remaining) := by
  simpa only [
    CanonicalSlideBlocks.sourceBlock,
    CanonicalSlideBlocks.targetBlock
  ] using
    (standardOneOverOneCycleTermWindow
      𝒞 η metadata countsSound sourceCycle remaining).toWindow

/-- Package the complete local proof grammar from coupon-adapted windows. -/
noncomputable def standardOneOverOneCycleBlockProof
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalOrdinarySlideBlockProof
      𝒞.premodular η source target
      (oneOverOneComponentChange metadata)
      (oneOverOneResolvedComponents metadata)
      sourceCycle
      ((CycleTransport.ofMarkedH2Transport source target
        (enrichedMove
          (.oneOverOne metadata countsSound)).homologyTransport)
        |>.targetCycle sourceCycle)
      .oneOverOne
      (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash where
  slide remaining :=
    standardOneOverOneCycleBlockWindow
      𝒞 η metadata countsSound sourceCycle remaining

/-- Reassemble the exact 1-over-1 whole-sum decomposition in the kernel. -/
noncomputable def standardOneOverOneCycleBlockDecomposition
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    OrdinarySlideBlockDecomposition
      𝒞.premodular η
      .oneOverOne
      (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit)
      (source.cycleLinearDiagram 𝒞.premodular η sourceCycle)
      (target.cycleLinearDiagram 𝒞.premodular η
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.oneOverOne metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)) :=
  (standardOneOverOneCycleBlockProof
    𝒞 η metadata countsSound sourceCycle).toDecomposition

/-- Assemble complete 1-over-1 geometry from its finite block partition. -/
noncomputable def standardOneOverOneCycleSlideGeometry
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    OrdinaryCycleSlideGeometry 𝒞.premodular η source target
      (enrichedMove
        (.oneOverOne metadata countsSound)).homologyTransport
      .oneOverOne
      (HandleEdit.oneOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.oneOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.oneOverOneStationaryId metadata.recipe.handleEdit) where
  blockDecomposition :=
    standardOneOverOneCycleBlockDecomposition
      𝒞 η metadata countsSound

/-- Project the same-component correspondence from a 2-over-1 edit. -/
def twoOverOneComponentChangeOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverOne)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .twoOverOne _ _ _ _,
      .twoOverOne _ _ _ _ same _ _ _ => same

/-- Resolve the two actual component indices named by a 2-over-1 edit. -/
def twoOverOneResolvedComponentsOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverOne)
    (change : ComponentIndexChange source target edit) :
    ResolvedSlideComponentPair source target
      (twoOverOneComponentChangeOfEdit edit change)
      (HandleEdit.twoOverOneSlidingId edit)
      (HandleEdit.twoOverOneStationaryId edit) :=
  match edit, change with
  | .twoOverOne _ _ _ _,
      .twoOverOne _ _ _ _ _ components _ _ => components

/-- Project the same-component correspondence from exact 2-over-1 metadata. -/
def twoOverOneComponentChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  CanonicalSourceBoundSlideMovie.twoOverOneSame metadata

/-- The source/target finite indices selected by exact 2-over-1 metadata. -/
def twoOverOneResolvedComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      (twoOverOneComponentChange metadata)
      (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit) :=
  CanonicalSourceBoundSlideMovie.twoOverOneComponents metadata

/--
The coupon-adapted local two-handle-over-dotted window for one canonical
block.
-/
noncomputable def standardTwoOverOneCycleTermWindow
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      CanonicalSlideBlocks.Block (S := S)
        (twoOverOneResolvedComponents metadata)) :
    TermwiseCouponAdaptedKirbyColourSlideWindow 𝒞.premodular η
      .twoOverOne
      (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit)
      (CanonicalSlideBlocks.sourceWeight
        𝒞.premodular η (twoOverOneResolvedComponents metadata)
        sourceCycle remaining)
      (CanonicalSlideBlocks.targetWeight
        𝒞.premodular η (twoOverOneComponentChange metadata)
        (twoOverOneResolvedComponents metadata)
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.twoOverOne metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)
        remaining)
      (CanonicalSlideBlocks.sourceTerm
        𝒞.premodular (twoOverOneResolvedComponents metadata) remaining)
      (CanonicalSlideBlocks.targetTerm
        𝒞.premodular (twoOverOneComponentChange metadata)
        (twoOverOneResolvedComponents metadata) remaining) := by
  let request :
      CanonicalSourceBoundSlideMovie.Request source target :=
    .twoOverOne metadata countsSound
  let requestRemaining :
      request.Block (S := S) := by
    simpa only [
      request,
      CanonicalSourceBoundSlideMovie.Request.Block,
      CanonicalSourceBoundSlideMovie.Request.resolvedComponents,
      twoOverOneResolvedComponents,
      twoOverOneResolvedComponentsOfEdit,
      id_eq
    ] using remaining
  simpa only [
    request,
    requestRemaining,
    CanonicalSourceBoundSlideMovie.Request.slideKind,
    CanonicalSourceBoundSlideMovie.Request.orientation,
    CanonicalSourceBoundSlideMovie.Request.moveId,
    CanonicalSourceBoundSlideMovie.Request.sourceHash,
    CanonicalSourceBoundSlideMovie.Request.targetHash,
    CanonicalSourceBoundSlideMovie.Request.slidingComponentId,
    CanonicalSourceBoundSlideMovie.Request.stationaryComponentId,
    CanonicalSourceBoundSlideMovie.Request.sameComponentChange,
    CanonicalSourceBoundSlideMovie.Request.resolvedComponents,
    CanonicalSourceBoundSlideMovie.Request.targetCycle,
    CanonicalSourceBoundSlideMovie.Request.topologicalMove,
    twoOverOneComponentChange,
    twoOverOneComponentChangeOfEdit,
    twoOverOneResolvedComponents,
    twoOverOneResolvedComponentsOfEdit,
    id_eq
  ] using
    (CanonicalSourceBoundSlideMovie.standardMovie
      𝒞 η request sourceCycle requestRemaining).toTermWindow

/--
Reassemble the exact 2-over-1 double-sum window from its labelwise coupon
movies.
-/
noncomputable def standardTwoOverOneCycleBlockWindow
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      CanonicalSlideBlocks.Block (S := S)
        (twoOverOneResolvedComponents metadata)) :
    CouponAdaptedKirbyColourSlideWindow 𝒞.premodular η
      .twoOverOne
      (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit)
      (CanonicalSlideBlocks.sourceBlock
        𝒞.premodular η (twoOverOneResolvedComponents metadata)
        sourceCycle remaining)
      (CanonicalSlideBlocks.targetBlock
        𝒞.premodular η (twoOverOneComponentChange metadata)
        (twoOverOneResolvedComponents metadata)
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.twoOverOne metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)
        remaining) := by
  simpa only [
    CanonicalSlideBlocks.sourceBlock,
    CanonicalSlideBlocks.targetBlock
  ] using
    (standardTwoOverOneCycleTermWindow
      𝒞 η metadata countsSound sourceCycle remaining).toWindow

/-- Package the complete local proof grammar from coupon-adapted windows. -/
noncomputable def standardTwoOverOneCycleBlockProof
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalOrdinarySlideBlockProof
      𝒞.premodular η source target
      (twoOverOneComponentChange metadata)
      (twoOverOneResolvedComponents metadata)
      sourceCycle
      ((CycleTransport.ofMarkedH2Transport source target
        (enrichedMove
          (.twoOverOne metadata countsSound)).homologyTransport)
        |>.targetCycle sourceCycle)
      .twoOverOne
      (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash where
  slide remaining :=
    standardTwoOverOneCycleBlockWindow
      𝒞 η metadata countsSound sourceCycle remaining

/-- Reassemble the exact 2-over-1 whole-sum decomposition in the kernel. -/
noncomputable def standardTwoOverOneCycleBlockDecomposition
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    OrdinarySlideBlockDecomposition
      𝒞.premodular η
      .twoOverOne
      (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit)
      (source.cycleLinearDiagram 𝒞.premodular η sourceCycle)
      (target.cycleLinearDiagram 𝒞.premodular η
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.twoOverOne metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)) :=
  (standardTwoOverOneCycleBlockProof
    𝒞 η metadata countsSound sourceCycle).toDecomposition

/-- Assemble complete 2-over-1 geometry from its finite block partition. -/
noncomputable def standardTwoOverOneCycleSlideGeometry
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverOne
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    OrdinaryCycleSlideGeometry 𝒞.premodular η source target
      (enrichedMove
        (.twoOverOne metadata countsSound)).homologyTransport
      .twoOverOne
      (HandleEdit.twoOverOneOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverOneSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverOneStationaryId metadata.recipe.handleEdit) where
  blockDecomposition :=
    standardTwoOverOneCycleBlockDecomposition
      𝒞 η metadata countsSound

/-- Project the same-component correspondence from a 2-over-2 edit. -/
def twoOverTwoComponentChangeOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverTwo)
    (change : ComponentIndexChange source target edit) :
    SameComponentIndexChange source target :=
  match edit, change with
  | .twoOverTwo _ _ _ _,
      .twoOverTwo _ _ _ _ same _ _ _ => same

/-- Resolve the two actual component indices named by a 2-over-2 edit. -/
def twoOverTwoResolvedComponentsOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoOverTwo)
    (change : ComponentIndexChange source target edit) :
    ResolvedSlideComponentPair source target
      (twoOverTwoComponentChangeOfEdit edit change)
      (HandleEdit.twoOverTwoSlidingId edit)
      (HandleEdit.twoOverTwoStationaryId edit) :=
  match edit, change with
  | .twoOverTwo _ _ _ _,
      .twoOverTwo _ _ _ _ _ components _ _ => components

/-- Project the same-component correspondence from exact 2-over-2 metadata. -/
def twoOverTwoComponentChange
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology) :
    SameComponentIndexChange
      source.topology.formal target.topology.formal :=
  CanonicalSourceBoundSlideMovie.twoOverTwoSame metadata

/-- The source/target finite indices selected by exact 2-over-2 metadata. -/
def twoOverTwoResolvedComponents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology) :
    ResolvedSlideComponentPair
      source.topology.formal target.topology.formal
      (twoOverTwoComponentChange metadata)
      (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit) :=
  CanonicalSourceBoundSlideMovie.twoOverTwoComponents metadata

/--
The coupon-adapted local two-handle-over-two-handle window for one canonical
block.

Both participating component labels remain visibly summed.  This input must
identify each twisted endpoint with the corresponding ordinary Kirby-colour
double sum through the restricted coupon grammar; all evaluation and
denominator reasoning is derived elsewhere.
-/
noncomputable def standardTwoOverTwoCycleTermWindow
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      CanonicalSlideBlocks.Block (S := S)
        (twoOverTwoResolvedComponents metadata)) :
    TermwiseCouponAdaptedKirbyColourSlideWindow 𝒞.premodular η
      .twoOverTwo
      (HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit)
      (CanonicalSlideBlocks.sourceWeight
        𝒞.premodular η (twoOverTwoResolvedComponents metadata)
        sourceCycle remaining)
      (CanonicalSlideBlocks.targetWeight
        𝒞.premodular η (twoOverTwoComponentChange metadata)
        (twoOverTwoResolvedComponents metadata)
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.twoOverTwo metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)
        remaining)
      (CanonicalSlideBlocks.sourceTerm
        𝒞.premodular (twoOverTwoResolvedComponents metadata) remaining)
      (CanonicalSlideBlocks.targetTerm
        𝒞.premodular (twoOverTwoComponentChange metadata)
        (twoOverTwoResolvedComponents metadata) remaining) := by
  let request :
      CanonicalSourceBoundSlideMovie.Request source target :=
    .twoOverTwo metadata countsSound
  let requestRemaining :
      request.Block (S := S) := by
    simpa only [
      request,
      CanonicalSourceBoundSlideMovie.Request.Block,
      CanonicalSourceBoundSlideMovie.Request.resolvedComponents,
      twoOverTwoResolvedComponents,
      twoOverTwoResolvedComponentsOfEdit,
      id_eq
    ] using remaining
  simpa only [
    request,
    requestRemaining,
    CanonicalSourceBoundSlideMovie.Request.slideKind,
    CanonicalSourceBoundSlideMovie.Request.orientation,
    CanonicalSourceBoundSlideMovie.Request.moveId,
    CanonicalSourceBoundSlideMovie.Request.sourceHash,
    CanonicalSourceBoundSlideMovie.Request.targetHash,
    CanonicalSourceBoundSlideMovie.Request.slidingComponentId,
    CanonicalSourceBoundSlideMovie.Request.stationaryComponentId,
    CanonicalSourceBoundSlideMovie.Request.sameComponentChange,
    CanonicalSourceBoundSlideMovie.Request.resolvedComponents,
    CanonicalSourceBoundSlideMovie.Request.targetCycle,
    CanonicalSourceBoundSlideMovie.Request.topologicalMove,
    twoOverTwoComponentChange,
    twoOverTwoComponentChangeOfEdit,
    twoOverTwoResolvedComponents,
    twoOverTwoResolvedComponentsOfEdit,
    id_eq
  ] using
    (CanonicalSourceBoundSlideMovie.standardMovie
      𝒞 η request sourceCycle requestRemaining).toTermWindow

/--
Reassemble the exact 2-over-2 double-sum window from its labelwise coupon
movies.
-/
noncomputable def standardTwoOverTwoCycleBlockWindow
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining :
      CanonicalSlideBlocks.Block (S := S)
        (twoOverTwoResolvedComponents metadata)) :
    CouponAdaptedKirbyColourSlideWindow 𝒞.premodular η
      .twoOverTwo
      (HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit)
      (CanonicalSlideBlocks.sourceBlock
        𝒞.premodular η (twoOverTwoResolvedComponents metadata)
        sourceCycle remaining)
      (CanonicalSlideBlocks.targetBlock
        𝒞.premodular η (twoOverTwoComponentChange metadata)
        (twoOverTwoResolvedComponents metadata)
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.twoOverTwo metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)
        remaining) := by
  simpa only [
    CanonicalSlideBlocks.sourceBlock,
    CanonicalSlideBlocks.targetBlock
  ] using
    (standardTwoOverTwoCycleTermWindow
      𝒞 η metadata countsSound sourceCycle remaining).toWindow

/-- Package the complete generalized proof grammar from coupon-adapted windows. -/
noncomputable def standardTwoOverTwoCycleBlockProof
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalGeneralizedSlideBlockProof
      𝒞.premodular η source target
      (twoOverTwoComponentChange metadata)
      (twoOverTwoResolvedComponents metadata)
      sourceCycle
      ((CycleTransport.ofMarkedH2Transport source target
        (enrichedMove
          (.twoOverTwo metadata countsSound)).homologyTransport)
        |>.targetCycle sourceCycle)
      (HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash where
  slide remaining :=
    standardTwoOverTwoCycleBlockWindow
      𝒞 η metadata countsSound sourceCycle remaining

/-- Reassemble the exact 2-over-2 whole-sum decomposition in the kernel. -/
noncomputable def standardTwoOverTwoCycleBlockDecomposition
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    GeneralizedSlideBlockDecomposition 𝒞.premodular η
      (HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit)
      (source.cycleLinearDiagram 𝒞.premodular η sourceCycle)
      (target.cycleLinearDiagram 𝒞.premodular η
        ((CycleTransport.ofMarkedH2Transport source target
          (enrichedMove
            (.twoOverTwo metadata countsSound)).homologyTransport)
          |>.targetCycle sourceCycle)) :=
  (standardTwoOverTwoCycleBlockProof
    𝒞 η metadata countsSound sourceCycle).toDecomposition

/-- Assemble complete 2-over-2 geometry from its coupon-adapted slide input. -/
noncomputable def standardTwoOverTwoCycleSlideGeometry
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo
        source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) :
    GeneralizedCycleSlideGeometry 𝒞.premodular η source target
      (enrichedMove
        (.twoOverTwo metadata countsSound)).homologyTransport
      (HandleEdit.twoOverTwoOrientation metadata.recipe.handleEdit)
      metadata.moveId
      metadata.sourcePresentationHash metadata.targetPresentationHash
      (HandleEdit.twoOverTwoSlidingId metadata.recipe.handleEdit)
      (HandleEdit.twoOverTwoStationaryId metadata.recipe.handleEdit) where
  blockDecomposition :=
    standardTwoOverTwoCycleBlockDecomposition
      𝒞 η metadata countsSound

/-- Recipe-owned finite component data for a 1--2 birth. -/
structure OneTwoBirthIndexData
    (source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation)
    (newDottedId newTwoHandleId : String) where
  added : AddedComponentIndexChange source target 2
  added_dotted_component_id :
    (componentAt target
      (added.targetDecomposition.symm
        (Sum.inr firstOfTwo))).componentId =
      newDottedId
  added_two_handle_component_id :
    (componentAt target
      (added.targetDecomposition.symm
        (Sum.inr secondOfTwo))).componentId =
      newTwoHandleId

/-- Extract both newly born components from the indexed recipe data. -/
def oneTwoBirthIndexDataOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneTwoBirth)
    (change : ComponentIndexChange source target edit) :
    OneTwoBirthIndexData source target
      (HandleEdit.oneTwoBirthDottedId edit)
      (HandleEdit.oneTwoBirthTwoHandleId edit) :=
  match edit, change with
  | .oneTwoBirth _ _ _,
      .oneTwoBirth _ _ _ added dottedIdSound _
        twoHandleIdSound _ =>
      ⟨added, dottedIdSound, twoHandleIdSound⟩

theorem oneTwoBirthIndexDataOfEdit_added
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneTwoBirth)
    (change : ComponentIndexChange source target edit) :
    (oneTwoBirthIndexDataOfEdit edit change).added =
      oneTwoBirthAddedChangeOfEdit edit change := by
  cases edit with
  | oneTwoBirth newDottedId newTwoHandleId distinct =>
      cases change
      rfl

/-- Extract the 1--2 birth component data from exact move metadata. -/
def oneTwoBirthIndexData
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology) :
    OneTwoBirthIndexData
      source.topology.formal target.topology.formal
      (HandleEdit.oneTwoBirthDottedId metadata.recipe.handleEdit)
      (HandleEdit.oneTwoBirthTwoHandleId metadata.recipe.handleEdit) :=
  oneTwoBirthIndexDataOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem oneTwoBirthIndexData_added
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology) :
    (oneTwoBirthIndexData metadata).added =
      oneTwoBirthAddedChange metadata := by
  exact oneTwoBirthIndexDataOfEdit_added
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem oneTwoBirth_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo) :
    (enrichedMove
        (.oneTwoBirth metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.oneTwoBirth metadata countsSound)).chainEquivalence := by
  rfl

/--
The exact exponent transport for a 1--2 birth, derived from the standard
handle-chain coordinate law rather than supplied by graphical input.
-/
noncomputable def oneTwoBirthExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo)
    (sourceCycle : source.DegreeTwoCycle) :
    AddedComponentCycleExponentTransport source target
      (oneTwoBirthIndexData metadata).added
      sourceCycle
      ((CycleTransport.ofMarkedH2Transport source target
        (enrichedMove
          (.oneTwoBirth metadata countsSound)).homologyTransport)
        |>.targetCycle sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).oneTwoBirthCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      added_exponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro sourceIndex
    rw [oneTwoBirthIndexData_added metadata]
    change
      target.topology.cycleComponentExponent
          (forwardDegreeTwoCycle
            ((enrichedMove
              (.oneTwoBirth metadata countsSound)).homologyTransport.chainEquivalence)
            sourceCycle)
          (componentAt target.topology.formal
            ((oneTwoBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inl sourceIndex))) =
        source.topology.cycleComponentExponent sourceCycle
          (componentAt source.topology.formal sourceIndex)
    rw [oneTwoBirth_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.common_exponent_sound sourceCycle sourceIndex
  · intro addedIndex
    rw [oneTwoBirthIndexData_added metadata]
    change
      target.topology.cycleComponentExponent
          (forwardDegreeTwoCycle
            ((enrichedMove
              (.oneTwoBirth metadata countsSound)).homologyTransport.chainEquivalence)
            sourceCycle)
          (componentAt target.topology.formal
            ((oneTwoBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inr addedIndex))) =
        0
    rw [oneTwoBirth_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.added_exponent_zero sourceCycle addedIndex

/--
The remaining typed endpoint calculation for a 1--2 birth.

The recipe fixes both new component IDs, their distinctness, their finite
indices, and the local Hopf-pair diagram.  Standard handle-chain naturality
now derives the cycle-coordinate calculation, so this witness contains only
the generated ribbon-diagram isotopy.
-/
structure OneTwoBirthTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo) where
  diagram_isotopy :
    GeneratedIsotopy target.componentTermDiagram
      (ComponentDiagram.closedTensor
        (ComponentDiagram.oneTwoHopfPair
          (HandleEdit.oneTwoBirthDottedId metadata.recipe.handleEdit)
          (HandleEdit.oneTwoBirthTwoHandleId metadata.recipe.handleEdit))
        source.componentTermDiagram)

/-- Endpoint-bound local movie for creating one cancelling one--two pair. -/
axiom standardOneTwoBirthTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo) :
    OneTwoBirthTypedDerivation source target metadata countsSound

/-- Assemble the 1--2 endpoint movie from recipe-owned and derived data. -/
noncomputable def standardOneTwoBirthEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo) :
    let transport :=
      (enrichedMove
        (.oneTwoBirth metadata countsSound)).homologyTransport
    OneTwoBirthEndpointMovie source target transport.targetClass
      (CycleTransport.ofMarkedH2Transport source target transport) := by
  let derivation :=
    standardOneTwoBirthTypedDerivation metadata countsSound
  let indexData := oneTwoBirthIndexData metadata
  exact
    { added :=
        { componentChange := indexData.added
          exponentTransport :=
            oneTwoBirthExponentTransport metadata countsSound
          localDiagram :=
            ComponentDiagram.oneTwoHopfPair
              (HandleEdit.oneTwoBirthDottedId
                metadata.recipe.handleEdit)
              (HandleEdit.oneTwoBirthTwoHandleId
                metadata.recipe.handleEdit)
          diagram_isotopy := derivation.diagram_isotopy }
      newDottedId :=
        HandleEdit.oneTwoBirthDottedId metadata.recipe.handleEdit
      newTwoHandleId :=
        HandleEdit.oneTwoBirthTwoHandleId metadata.recipe.handleEdit
      distinct_ids :=
        HandleEdit.oneTwoBirthDistinct metadata.recipe.handleEdit
      added_dotted_component_id :=
        indexData.added_dotted_component_id
      added_two_handle_component_id :=
        indexData.added_two_handle_component_id
      local_diagram_sound := rfl
      added_exponent_zero := by
        intro sourceCycle addedIndex
        rfl }

/-- Derived complete cycle geometry for a cancelling one--two birth. -/
noncomputable def standardOneTwoBirthCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addOneTwo) :
    OneTwoBirthCycleGeometry source target
      (enrichedMove
        (.oneTwoBirth metadata countsSound)).homologyTransport.targetClass :=
  (standardOneTwoBirthEndpointMovie metadata countsSound).toCycleGeometry

/-- Recipe-owned reverse-birth component data for a 1--2 death. -/
structure OneTwoDeathReverseIndexData
    (source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation)
    (removedDottedId removedTwoHandleId : String) where
  added : AddedComponentIndexChange target source 2
  added_dotted_component_id :
    (componentAt source
      (added.targetDecomposition.symm
        (Sum.inr firstOfTwo))).componentId =
      removedDottedId
  added_two_handle_component_id :
    (componentAt source
      (added.targetDecomposition.symm
        (Sum.inr secondOfTwo))).componentId =
      removedTwoHandleId

/-- Read exact 1--2 removal data backwards without selecting a new map. -/
def oneTwoDeathReverseIndexDataOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneTwoDeath)
    (change : ComponentIndexChange source target edit) :
    OneTwoDeathReverseIndexData source target
      (HandleEdit.oneTwoDeathDottedId edit)
      (HandleEdit.oneTwoDeathTwoHandleId edit) :=
  match edit, change with
  | .oneTwoDeath _ _ _,
      .oneTwoDeath _ _ _ removed dottedIdSound _
        twoHandleIdSound _ =>
      ⟨removed.reverseAdded, dottedIdSound, twoHandleIdSound⟩

theorem oneTwoDeathReverseIndexDataOfEdit_added
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .oneTwoDeath)
    (change : ComponentIndexChange source target edit) :
    (oneTwoDeathReverseIndexDataOfEdit edit change).added =
      (oneTwoDeathRemovedChangeOfEdit edit change).reverseAdded := by
  cases edit with
  | oneTwoDeath removedDottedId removedTwoHandleId distinct =>
      cases change
      rfl

/-- Extract reverse-birth data from exact 1--2 death metadata. -/
def oneTwoDeathReverseIndexData
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology) :
    OneTwoDeathReverseIndexData
      source.topology.formal target.topology.formal
      (HandleEdit.oneTwoDeathDottedId metadata.recipe.handleEdit)
      (HandleEdit.oneTwoDeathTwoHandleId metadata.recipe.handleEdit) :=
  oneTwoDeathReverseIndexDataOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem oneTwoDeathReverseIndexData_added
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology) :
    (oneTwoDeathReverseIndexData metadata).added =
      (oneTwoDeathRemovedChange metadata).reverseAdded :=
  oneTwoDeathReverseIndexDataOfEdit_added
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem oneTwoDeath_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo) :
    (enrichedMove
        (.oneTwoDeath metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.oneTwoDeath metadata countsSound)).chainEquivalence := by
  rfl

/-- Exact reverse exponent transport for a 1--2 death. -/
noncomputable def oneTwoDeathExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo)
    (targetCycle : target.DegreeTwoCycle) :
    AddedComponentCycleExponentTransport target source
      (oneTwoDeathReverseIndexData metadata).added
      targetCycle
      ((CycleTransport.ofMarkedH2TransportInverse source target
        (enrichedMove
          (.oneTwoDeath metadata countsSound)).homologyTransport)
        |>.targetCycle targetCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).oneTwoDeathCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      added_exponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro targetIndex
    rw [oneTwoDeathReverseIndexData_added metadata]
    change
      source.topology.cycleComponentExponent
          (backwardDegreeTwoCycle
            ((enrichedMove
              (.oneTwoDeath metadata countsSound)).homologyTransport.chainEquivalence)
            targetCycle)
          (componentAt source.topology.formal
            ((oneTwoDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inl targetIndex))) =
        target.topology.cycleComponentExponent targetCycle
          (componentAt target.topology.formal targetIndex)
    rw [oneTwoDeath_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.common_exponent_sound targetCycle targetIndex
  · intro removedIndex
    rw [oneTwoDeathReverseIndexData_added metadata]
    change
      source.topology.cycleComponentExponent
          (backwardDegreeTwoCycle
            ((enrichedMove
              (.oneTwoDeath metadata countsSound)).homologyTransport.chainEquivalence)
            targetCycle)
          (componentAt source.topology.formal
            ((oneTwoDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inr removedIndex))) =
        0
    rw [oneTwoDeath_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.removed_exponent_zero targetCycle removedIndex

/--
The remaining typed reverse-birth calculation for a 1--2 death.

All finite component data and cycle-coordinate transport are derived by
reversing the death recipe and applying standard handle-chain naturality.
This witness contains only the generated ribbon-diagram isotopy.
-/
structure OneTwoDeathTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo) where
  diagram_isotopy :
    GeneratedIsotopy source.componentTermDiagram
      (ComponentDiagram.closedTensor
        (ComponentDiagram.oneTwoHopfPair
          (HandleEdit.oneTwoDeathDottedId metadata.recipe.handleEdit)
          (HandleEdit.oneTwoDeathTwoHandleId metadata.recipe.handleEdit))
        target.componentTermDiagram)

/-- Endpoint-bound local movie for deleting one cancelling one--two pair. -/
axiom standardOneTwoDeathTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo) :
    OneTwoDeathTypedDerivation source target metadata countsSound

/-- Assemble the reverse-birth endpoint movie for a 1--2 death. -/
noncomputable def standardOneTwoDeathEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo) :
    OneTwoDeathEndpointMovie source target
      (enrichedMove
        (.oneTwoDeath metadata countsSound)).homologyTransport := by
  let derivation :=
    standardOneTwoDeathTypedDerivation metadata countsSound
  let indexData := oneTwoDeathReverseIndexData metadata
  exact
    { reverseBirth :=
        { added :=
            { componentChange := indexData.added
              exponentTransport :=
                oneTwoDeathExponentTransport metadata countsSound
              localDiagram :=
                ComponentDiagram.oneTwoHopfPair
                  (HandleEdit.oneTwoDeathDottedId
                    metadata.recipe.handleEdit)
                  (HandleEdit.oneTwoDeathTwoHandleId
                    metadata.recipe.handleEdit)
              diagram_isotopy := derivation.diagram_isotopy }
          newDottedId :=
            HandleEdit.oneTwoDeathDottedId metadata.recipe.handleEdit
          newTwoHandleId :=
            HandleEdit.oneTwoDeathTwoHandleId metadata.recipe.handleEdit
          distinct_ids :=
            HandleEdit.oneTwoDeathDistinct metadata.recipe.handleEdit
          added_dotted_component_id :=
            indexData.added_dotted_component_id
          added_two_handle_component_id :=
            indexData.added_two_handle_component_id
          local_diagram_sound := rfl
          added_exponent_zero := by
            intro targetCycle addedIndex
            rfl } }

/-- Derived complete cycle geometry for a cancelling one--two death. -/
noncomputable def standardOneTwoDeathCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo) :
    OneTwoDeathCycleGeometry source target
      (enrichedMove
        (.oneTwoDeath metadata countsSound)).homologyTransport :=
  (standardOneTwoDeathEndpointMovie metadata countsSound).toCycleGeometry

/-- Recipe-owned finite component data for a 2--3 birth. -/
structure TwoThreeBirthIndexData
    (source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation)
    (newTwoHandleId : String) where
  added : AddedComponentIndexChange source target 1
  added_component_id :
    (componentAt target
      (added.targetDecomposition.symm
        (Sum.inr onlyOne))).componentId =
      newTwoHandleId

/-- Extract the one newly born component from the indexed recipe data. -/
def twoThreeBirthIndexDataOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoThreeBirth)
    (change : ComponentIndexChange source target edit) :
    TwoThreeBirthIndexData source target
      (HandleEdit.twoThreeBirthTwoHandleId edit) :=
  match edit, change with
  | .twoThreeBirth _, .twoThreeBirth _ added idSound _ =>
      ⟨added, idSound⟩

theorem twoThreeBirthIndexDataOfEdit_added
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoThreeBirth)
    (change : ComponentIndexChange source target edit) :
    (twoThreeBirthIndexDataOfEdit edit change).added =
      twoThreeBirthAddedChangeOfEdit edit change := by
  cases edit with
  | twoThreeBirth newTwoHandleId =>
      cases change
      rfl

/-- Extract the 2--3 birth component data from exact move metadata. -/
def twoThreeBirthIndexData
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology) :
    TwoThreeBirthIndexData
      source.topology.formal target.topology.formal
      (HandleEdit.twoThreeBirthTwoHandleId
        metadata.recipe.handleEdit) :=
  twoThreeBirthIndexDataOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem twoThreeBirthIndexData_added
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology) :
    (twoThreeBirthIndexData metadata).added =
      twoThreeBirthAddedChange metadata :=
  twoThreeBirthIndexDataOfEdit_added
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem twoThreeBirth_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree) :
    (enrichedMove
        (.twoThreeBirth metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.twoThreeBirth metadata countsSound)).chainEquivalence := by
  rfl

/-- Exact exponent transport for a 2--3 birth. -/
noncomputable def twoThreeBirthExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree)
    (sourceCycle : source.DegreeTwoCycle) :
    AddedComponentCycleExponentTransport source target
      (twoThreeBirthIndexData metadata).added sourceCycle
      ((CycleTransport.ofMarkedH2Transport source target
        (enrichedMove
          (.twoThreeBirth metadata countsSound)).homologyTransport)
        |>.targetCycle sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).twoThreeBirthCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      added_exponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro sourceIndex
    rw [twoThreeBirthIndexData_added metadata]
    change
      target.topology.cycleComponentExponent
          (forwardDegreeTwoCycle
            ((enrichedMove
              (.twoThreeBirth metadata countsSound)).homologyTransport.chainEquivalence)
            sourceCycle)
          (componentAt target.topology.formal
            ((twoThreeBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inl sourceIndex))) =
        source.topology.cycleComponentExponent sourceCycle
          (componentAt source.topology.formal sourceIndex)
    rw [twoThreeBirth_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.common_exponent_sound sourceCycle sourceIndex
  · intro addedIndex
    rw [twoThreeBirthIndexData_added metadata]
    change
      target.topology.cycleComponentExponent
          (forwardDegreeTwoCycle
            ((enrichedMove
              (.twoThreeBirth metadata countsSound)).homologyTransport.chainEquivalence)
            sourceCycle)
          (componentAt target.topology.formal
            ((twoThreeBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inr addedIndex))) =
        0
    rw [twoThreeBirth_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.added_exponent_zero sourceCycle addedIndex

/--
The remaining typed endpoint calculation for a 2--3 birth.

The added component, its ID, and the local zero-framed unknot are fixed by
the recipe.  Standard handle-chain naturality now derives the cycle-coordinate
calculation, so only the generated ribbon-diagram isotopy remains external.
-/
structure TwoThreeBirthTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree) where
  diagram_isotopy :
    GeneratedIsotopy target.componentTermDiagram
      (ComponentDiagram.closedTensor
        (ComponentDiagram.zeroFramedUnknot
          (HandleEdit.twoThreeBirthTwoHandleId
            metadata.recipe.handleEdit))
        source.componentTermDiagram)

/-- Endpoint-bound local movie for creating one cancelling two--three pair. -/
theorem standardTwoThreeBirthTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree) :
    TwoThreeBirthTypedDerivation source target metadata countsSound := by
  exact
    ⟨CanonicalCancellationTraceBinding.twoThreeBirth_componentTermDiagram_isotopy
      metadata⟩

/-- Assemble the complete endpoint movie from recipe-owned and derived data. -/
noncomputable def standardTwoThreeBirthEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree) :
    let transport :=
      (enrichedMove
        (.twoThreeBirth metadata countsSound)).homologyTransport
    TwoThreeBirthEndpointMovie source target transport.targetClass
      (CycleTransport.ofMarkedH2Transport source target transport) := by
  let derivation :=
    standardTwoThreeBirthTypedDerivation metadata countsSound
  let indexData := twoThreeBirthIndexData metadata
  exact
    { added :=
        { componentChange := indexData.added
          exponentTransport :=
            twoThreeBirthExponentTransport metadata countsSound
          localDiagram :=
            ComponentDiagram.zeroFramedUnknot
              (HandleEdit.twoThreeBirthTwoHandleId
                metadata.recipe.handleEdit)
          diagram_isotopy := derivation.diagram_isotopy }
      newTwoHandleId :=
        HandleEdit.twoThreeBirthTwoHandleId
          metadata.recipe.handleEdit
      added_component_id := indexData.added_component_id
      local_diagram_sound := rfl
      added_exponent_zero := by
        intro sourceCycle
        rfl }

/-- Derived complete cycle geometry for a cancelling two--three birth. -/
noncomputable def standardTwoThreeBirthCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology)
    (countsSound :
      target.topology.counts = source.topology.counts.addTwoThree) :
    TwoThreeBirthCycleGeometry source target
      (enrichedMove
        (.twoThreeBirth metadata countsSound)).homologyTransport.targetClass :=
  (standardTwoThreeBirthEndpointMovie metadata countsSound).toCycleGeometry

/-- Recipe-owned reverse-birth component data for a 2--3 death. -/
structure TwoThreeDeathReverseIndexData
    (source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation)
    (removedTwoHandleId : String) where
  added : AddedComponentIndexChange target source 1
  added_component_id :
    (componentAt source
      (added.targetDecomposition.symm
        (Sum.inr onlyOne))).componentId =
      removedTwoHandleId

/-- Read exact 2--3 removal data backwards without selecting a new map. -/
def twoThreeDeathReverseIndexDataOfEdit
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoThreeDeath)
    (change : ComponentIndexChange source target edit) :
    TwoThreeDeathReverseIndexData source target
      (HandleEdit.twoThreeDeathTwoHandleId edit) :=
  match edit, change with
  | .twoThreeDeath _,
      .twoThreeDeath _ removed twoHandleIdSound _ =>
      ⟨removed.reverseAdded, twoHandleIdSound⟩

theorem twoThreeDeathReverseIndexDataOfEdit_added
    {source target :
      TwistedYetter.Kirby.Presentation.FormalPresentation}
    (edit : HandleEdit .twoThreeDeath)
    (change : ComponentIndexChange source target edit) :
    (twoThreeDeathReverseIndexDataOfEdit edit change).added =
      (twoThreeDeathRemovedChangeOfEdit edit change).reverseAdded := by
  cases edit with
  | twoThreeDeath removedTwoHandleId =>
      cases change
      rfl

/-- Extract reverse-birth data from exact 2--3 death metadata. -/
def twoThreeDeathReverseIndexData
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology) :
    TwoThreeDeathReverseIndexData
      source.topology.formal target.topology.formal
      (HandleEdit.twoThreeDeathTwoHandleId metadata.recipe.handleEdit) :=
  twoThreeDeathReverseIndexDataOfEdit
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem twoThreeDeathReverseIndexData_added
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology) :
    (twoThreeDeathReverseIndexData metadata).added =
      (twoThreeDeathRemovedChange metadata).reverseAdded :=
  twoThreeDeathReverseIndexDataOfEdit_added
    metadata.recipe.handleEdit metadata.recipe.componentIndexChange

theorem twoThreeDeath_enriched_chainEquivalence
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree) :
    (enrichedMove
        (.twoThreeDeath metadata countsSound)).homologyTransport.chainEquivalence =
      ((standardHandleChainNaturality H2).compile
        (.twoThreeDeath metadata countsSound)).chainEquivalence := by
  rfl

/-- Exact reverse exponent transport for a 2--3 death. -/
noncomputable def twoThreeDeathExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree)
    (targetCycle : target.DegreeTwoCycle) :
    AddedComponentCycleExponentTransport target source
      (twoThreeDeathReverseIndexData metadata).added targetCycle
      ((CycleTransport.ofMarkedH2TransportInverse source target
        (enrichedMove
          (.twoThreeDeath metadata countsSound)).homologyTransport)
        |>.targetCycle targetCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).twoThreeDeathCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      added_exponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro targetIndex
    rw [twoThreeDeathReverseIndexData_added metadata]
    change
      source.topology.cycleComponentExponent
          (backwardDegreeTwoCycle
            ((enrichedMove
              (.twoThreeDeath metadata countsSound)).homologyTransport.chainEquivalence)
            targetCycle)
          (componentAt source.topology.formal
            ((twoThreeDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inl targetIndex))) =
        target.topology.cycleComponentExponent targetCycle
          (componentAt target.topology.formal targetIndex)
    rw [twoThreeDeath_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.common_exponent_sound targetCycle targetIndex
  · intro removedIndex
    rw [twoThreeDeathReverseIndexData_added metadata]
    change
      source.topology.cycleComponentExponent
          (backwardDegreeTwoCycle
            ((enrichedMove
              (.twoThreeDeath metadata countsSound)).homologyTransport.chainEquivalence)
            targetCycle)
          (componentAt source.topology.formal
            ((twoThreeDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inr removedIndex))) =
        0
    rw [twoThreeDeath_enriched_chainEquivalence metadata countsSound]
    exact coordinateLaw.removed_exponent_zero targetCycle removedIndex

/--
The remaining typed reverse-birth calculation for a 2--3 death.

The reverse finite correspondence, component identity, and cycle-coordinate
transport are forced by the death recipe and standard handle-chain naturality.
Only the generated ribbon-diagram isotopy remains external.
-/
structure TwoThreeDeathTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree) where
  diagram_isotopy :
    GeneratedIsotopy source.componentTermDiagram
      (ComponentDiagram.closedTensor
        (ComponentDiagram.zeroFramedUnknot
          (HandleEdit.twoThreeDeathTwoHandleId
            metadata.recipe.handleEdit))
        target.componentTermDiagram)

/-- Endpoint-bound local movie for deleting one cancelling two--three pair. -/
theorem standardTwoThreeDeathTypedDerivation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree) :
    TwoThreeDeathTypedDerivation source target metadata countsSound := by
  exact
    ⟨CanonicalCancellationTraceBinding.twoThreeDeath_componentTermDiagram_isotopy
      metadata⟩

/-- Assemble the reverse-birth endpoint movie for a 2--3 death. -/
noncomputable def standardTwoThreeDeathEndpointMovie
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree) :
    TwoThreeDeathEndpointMovie source target
      (enrichedMove
        (.twoThreeDeath metadata countsSound)).homologyTransport := by
  let derivation :=
    standardTwoThreeDeathTypedDerivation metadata countsSound
  let indexData := twoThreeDeathReverseIndexData metadata
  exact
    { reverseBirth :=
        { added :=
            { componentChange := indexData.added
              exponentTransport :=
                twoThreeDeathExponentTransport metadata countsSound
              localDiagram :=
                ComponentDiagram.zeroFramedUnknot
                  (HandleEdit.twoThreeDeathTwoHandleId
                    metadata.recipe.handleEdit)
              diagram_isotopy := derivation.diagram_isotopy }
          newTwoHandleId :=
            HandleEdit.twoThreeDeathTwoHandleId
              metadata.recipe.handleEdit
          added_component_id := indexData.added_component_id
          local_diagram_sound := rfl
          added_exponent_zero := by
            intro targetCycle
            rfl } }

/-- Derived complete cycle geometry for a cancelling two--three death. -/
noncomputable def standardTwoThreeDeathCycleGeometry
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree) :
    TwoThreeDeathCycleGeometry source target
      (enrichedMove
        (.twoThreeDeath metadata countsSound)).homologyTransport :=
  (standardTwoThreeDeathEndpointMovie metadata countsSound).toCycleGeometry

/--
Assemble the eight small local inputs into the existing closed certificate
type.  This theorem is only exhaustive case analysis; it is no longer an
axiom.
-/
noncomputable def standardGraphicalMoveRealization
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (move :
      TopologicalTableTwoMove source.topology target.topology) :
    GraphicalMoveRealization 𝒞 η move := by
  cases move with
  | framedIsotopy metadata countsSound =>
      exact .framedIsotopy metadata countsSound
        (standardFramedIsotopyCycleGeometry metadata countsSound)
  | oneOverOne metadata countsSound =>
      exact .oneOverOne metadata countsSound
        (standardOneOverOneCycleSlideGeometry
          𝒞 η metadata countsSound)
  | twoOverOne metadata countsSound =>
      exact .twoOverOne metadata countsSound
        (standardTwoOverOneCycleSlideGeometry
          𝒞 η metadata countsSound)
  | twoOverTwo metadata countsSound =>
      exact .twoOverTwo metadata countsSound
        (standardTwoOverTwoCycleSlideGeometry
          𝒞 η metadata countsSound)
  | oneTwoBirth metadata countsSound =>
      exact .oneTwoBirth metadata countsSound
        (standardOneTwoBirthCycleGeometry metadata countsSound)
  | oneTwoDeath metadata countsSound =>
      exact .oneTwoDeath metadata countsSound
        (standardOneTwoDeathCycleGeometry metadata countsSound)
  | twoThreeBirth metadata countsSound =>
      exact .twoThreeBirth metadata countsSound
        (standardTwoThreeBirthCycleGeometry metadata countsSound)
  | twoThreeDeath metadata countsSound =>
      exact .twoThreeDeath metadata countsSound
        (standardTwoThreeDeathCycleGeometry metadata countsSound)

/--
The former direct axiom is now a derived definition: categorical invariance is
compiled from the visible eight-case graphical realization.
-/
noncomputable def standardLocalCycleCalculation
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (move :
      TopologicalTableTwoMove source.topology target.topology) :
    LocalCycleCalculation 𝒞 η (enrichedMove move) :=
  (standardGraphicalMoveRealization 𝒞 η move).toLocalCycleCalculation

end TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput
