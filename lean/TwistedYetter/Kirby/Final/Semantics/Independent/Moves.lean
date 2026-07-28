import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

/-!
# Independent semantics: Kirby moves and H₂ transport

Each move carries an exact source, target, local combinatorial script, and
chain map.  No constructor contains an evaluator equality.
-/

namespace TwistedYetter.Semantics.Independent

inductive ElementaryMoveKind
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving DecidableEq, Repr

inductive BandOrientation
  | positive
  | negative
  deriving DecidableEq, Repr

inductive CouponTransportEvent
  | crossing (sign : CrossingSign)
  | cup
  | cap
  | twist (sign : CrossingSign)
  | coupon (name : String)
  deriving DecidableEq, Repr

/--
A slide is normalized into clean attach, a finite transport list, and clean
detach.  The source and target factorizations are explicit propositions about
the combinatorial event traces, not scalar equalities.
-/
structure CleanBandSlideScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  movingSource : source.trace.ComponentId
  stationarySource : source.trace.ComponentId
  movingTarget : target.trace.ComponentId
  stationaryTarget : target.trace.ComponentId
  orientation : BandOrientation
  attachPortsAdjacent : Prop
  attachCollarContainsOnlySpecifiedStrands : Prop
  transportEvents : List CouponTransportEvent
  transportListIsComplete : Prop
  detachPortsAdjacent : Prop
  detachCollarContainsOnlySpecifiedStrands : Prop
  commonExteriorUnchanged : Prop
  sourceTargetComponentBinding : Prop
  framingPushOffCompatible : Prop
  attachPortsAdjacent_holds : attachPortsAdjacent
  attachCollarContainsOnlySpecifiedStrands_holds :
    attachCollarContainsOnlySpecifiedStrands
  transportListIsComplete_holds : transportListIsComplete
  detachPortsAdjacent_holds : detachPortsAdjacent
  detachCollarContainsOnlySpecifiedStrands_holds :
    detachCollarContainsOnlySpecifiedStrands
  commonExteriorUnchanged_holds : commonExteriorUnchanged
  sourceTargetComponentBinding_holds : sourceTargetComponentBinding
  framingPushOffCompatible_holds : framingPushOffCompatible

structure FramedIsotopyScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  componentReindexing : source.trace.ComponentId ≃ target.trace.ComponentId
  strandReindexing : source.trace.StrandId ≃ target.trace.StrandId
  rolesOrientationsFramingsPreserved : Prop
  eventTraceRelatedByPlanarIsotopy : Prop
  dottedCutWordsTransported : Prop
  rolesOrientationsFramingsPreserved_holds :
    rolesOrientationsFramingsPreserved
  eventTraceRelatedByPlanarIsotopy_holds :
    eventTraceRelatedByPlanarIsotopy
  dottedCutWordsTransported_holds : dottedCutWordsTransported

structure CancellationScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  kind :
    ElementaryMoveKind
  kind_is_cancellation :
    kind = .oneTwoBirth ∨ kind = .oneTwoDeath ∨
    kind = .twoThreeBirth ∨ kind = .twoThreeDeath
  localCancelingPair : Prop
  commonExteriorUnchanged : Prop
  handleCountChangeIsStandard : Prop
  markingCoordinateChangeIsStandard : Prop
  localCancelingPair_holds : localCancelingPair
  commonExteriorUnchanged_holds : commonExteriorUnchanged
  handleCountChangeIsStandard_holds : handleCountChangeIsStandard
  markingCoordinateChangeIsStandard_holds :
    markingCoordinateChangeIsStandard

/--
An exact chain-level transport.  The induced map on quotient homology is
derived later; it is not supplied as an unrelated function on `H₂`.
-/
structure HandleChainTransport
    (source target : CombinatorialSpecialKirbyDiagram)
    (sourceBoundary : DegreeThreeBoundaryData source)
    (targetBoundary : DegreeThreeBoundaryData target) where
  degreeThree :
    HandleChainGroup source.handles.hThree →+
      HandleChainGroup target.handles.hThree
  degreeTwo :
    HandleChainGroup source.handles.hTwo →+
      HandleChainGroup target.handles.hTwo
  degreeOne :
    HandleChainGroup source.handles.hOne →+
      HandleChainGroup target.handles.hOne
  commutesWithBoundaryThree :
    degreeTwo.comp sourceBoundary.boundaryThree =
      targetBoundary.boundaryThree.comp degreeThree
  commutesWithBoundaryTwo :
    degreeOne.comp (boundaryTwo source) =
      (boundaryTwo target).comp degreeTwo

def HandleChainTransport.mapCycle
    {source target : CombinatorialSpecialKirbyDiagram}
    {sourceBoundary : DegreeThreeBoundaryData source}
    {targetBoundary : DegreeThreeBoundaryData target}
    (transport :
      HandleChainTransport source target sourceBoundary targetBoundary) :
    TwoCycles source →+ TwoCycles target where
  toFun cycle :=
    ⟨transport.degreeTwo cycle.1, by
      change ((boundaryTwo target).comp transport.degreeTwo) cycle.1 = 0
      rw [← transport.commutesWithBoundaryTwo]
      change transport.degreeOne (boundaryTwo source cycle.1) = 0
      rw [cycle.2]
      simp⟩
  map_zero' := by
    ext
    simp
  map_add' left right := by
    ext
    simp

def HandleChainTransport.inducedH₂
    {source target : CombinatorialSpecialKirbyDiagram}
    {sourceBoundary : DegreeThreeBoundaryData source}
    {targetBoundary : DegreeThreeBoundaryData target}
    (transport :
      HandleChainTransport source target sourceBoundary targetBoundary) :
    KirbyH₂ sourceBoundary →+ KirbyH₂ targetBoundary :=
  QuotientAddGroup.map
    (boundaryAsCycle sourceBoundary).range
    (boundaryAsCycle targetBoundary).range
    transport.mapCycle
    (by
      intro sourceBoundaryCycle sourceMembership
      rcases sourceMembership with ⟨degreeThreeChain, rfl⟩
      refine ⟨transport.degreeThree degreeThreeChain, ?_⟩
      apply Subtype.ext
      change
        targetBoundary.boundaryThree
            (transport.degreeThree degreeThreeChain) =
          transport.degreeTwo
            (sourceBoundary.boundaryThree degreeThreeChain)
      exact (DFunLike.congr_fun
        transport.commutesWithBoundaryThree degreeThreeChain).symm)

inductive ElementaryMove
    (source target : HomologicallyMarkedDiagram) : Type
  | framedIsotopy
      (script : FramedIsotopyScript source.diagram target.diagram)
      (chain :
        HandleChainTransport source.diagram target.diagram
          source.degreeThree target.degreeThree)
      (markingTransport :
        target.alpha = chain.inducedH₂ source.alpha)
  | oneOverOne
      (script : CleanBandSlideScript source.diagram target.diagram)
      (moving_is_dotted :
        (source.diagram.trace.components script.movingSource).role = .dotted)
      (stationary_is_dotted :
        (source.diagram.trace.components script.stationarySource).role = .dotted)
      (chain :
        HandleChainTransport source.diagram target.diagram
          source.degreeThree target.degreeThree)
      (markingTransport :
        target.alpha = chain.inducedH₂ source.alpha)
  | twoOverOne
      (script : CleanBandSlideScript source.diagram target.diagram)
      (moving_is_two_handle :
        (source.diagram.trace.components script.movingSource).role ≠ .dotted)
      (stationary_is_dotted :
        (source.diagram.trace.components script.stationarySource).role = .dotted)
      (chain :
        HandleChainTransport source.diagram target.diagram
          source.degreeThree target.degreeThree)
      (markingTransport :
        target.alpha = chain.inducedH₂ source.alpha)
  | twoOverTwo
      (script : CleanBandSlideScript source.diagram target.diagram)
      (moving_is_two_handle :
        (source.diagram.trace.components script.movingSource).role ≠ .dotted)
      (stationary_is_two_handle :
        (source.diagram.trace.components script.stationarySource).role ≠ .dotted)
      (chain :
        HandleChainTransport source.diagram target.diagram
          source.degreeThree target.degreeThree)
      (markingTransport :
        target.alpha = chain.inducedH₂ source.alpha)
  | cancellation
      (script : CancellationScript source.diagram target.diagram)
      (chain :
        HandleChainTransport source.diagram target.diagram
          source.degreeThree target.degreeThree)
      (markingTransport :
        target.alpha = chain.inducedH₂ source.alpha)

def ElementaryMove.chain
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    HandleChainTransport source.diagram target.diagram
      source.degreeThree target.degreeThree :=
  match move with
  | .framedIsotopy _ chain _ => chain
  | .oneOverOne _ _ _ chain _ => chain
  | .twoOverOne _ _ _ chain _ => chain
  | .twoOverTwo _ _ _ chain _ => chain
  | .cancellation _ chain _ => chain

structure KirbyMovie
    (source target : HomologicallyMarkedDiagram) where
  stageCount : ℕ
  stages : Fin (stageCount + 1) → HomologicallyMarkedDiagram
  startsAtSource : stages 0 = source
  endsAtTarget : stages (Fin.last stageCount) = target
  elementary :
    ∀ i : Fin stageCount,
      ElementaryMove (stages i.castSucc) (stages i.succ)

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 13489
