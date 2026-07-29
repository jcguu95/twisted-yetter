import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

/-!
# Independent semantics: Kirby moves and H₂ transport

Each move carries an exact source, target, local combinatorial script, and
chain map.  No constructor contains an evaluator equality.
-/

namespace TwistedYetter.Semantics.Independent

noncomputable section

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

opaque CleanAttachSite
    (source : CombinatorialSpecialKirbyDiagram)
    (moving stationary : source.trace.ComponentId) :
    Prop

opaque CompleteCouponTransport
    (source target : CombinatorialSpecialKirbyDiagram)
    (events : List CouponTransportEvent) :
    Prop

opaque CleanDetachSite
    (target : CombinatorialSpecialKirbyDiagram)
    (moving stationary : target.trace.ComponentId) :
    Prop

opaque SlideCommonExteriorUnchanged
    (source target : CombinatorialSpecialKirbyDiagram) :
    Prop

opaque SlideComponentBinding
    (source target : CombinatorialSpecialKirbyDiagram)
    (movingSource stationarySource : source.trace.ComponentId)
    (movingTarget stationaryTarget : target.trace.ComponentId) :
    Prop

opaque SlideFramingPushOffCompatible
    (source target : CombinatorialSpecialKirbyDiagram)
    (orientation : BandOrientation) :
    Prop

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
  transportEvents : List CouponTransportEvent
  attachIsClean :
    CleanAttachSite source movingSource stationarySource
  transportListIsComplete :
    CompleteCouponTransport source target transportEvents
  detachIsClean :
    CleanDetachSite target movingTarget stationaryTarget
  commonExteriorUnchanged :
    SlideCommonExteriorUnchanged source target
  sourceTargetComponentBinding :
    SlideComponentBinding source target
      movingSource stationarySource movingTarget stationaryTarget
  framingPushOffCompatible :
    SlideFramingPushOffCompatible source target orientation

opaque IsotopyPreservesRolesOrientationsFramings
    (source target : CombinatorialSpecialKirbyDiagram) :
    Prop

opaque EventTracesAreRelatedByPlanarIsotopy
    (source target : CombinatorialSpecialKirbyDiagram) :
    Prop

opaque IsotopyTransportsDottedCutWords
    (source target : CombinatorialSpecialKirbyDiagram) :
    Prop

structure FramedIsotopyScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  componentReindexing : source.trace.ComponentId ≃ target.trace.ComponentId
  strandReindexing : source.trace.StrandId ≃ target.trace.StrandId
  rolesOrientationsFramingsPreserved :
    IsotopyPreservesRolesOrientationsFramings source target
  eventTraceRelatedByPlanarIsotopy :
    EventTracesAreRelatedByPlanarIsotopy source target
  dottedCutWordsTransported :
    IsotopyTransportsDottedCutWords source target

opaque IsStandardLocalCancelingPair
    (source target : CombinatorialSpecialKirbyDiagram)
    (kind : ElementaryMoveKind) :
    Prop

opaque CancellationCommonExteriorUnchanged
    (source target : CombinatorialSpecialKirbyDiagram) :
    Prop

opaque CancellationHandleCountChangeIsStandard
    (source target : CombinatorialSpecialKirbyDiagram)
    (kind : ElementaryMoveKind) :
    Prop

opaque CancellationMarkingCoordinateChangeIsStandard
    (source target : CombinatorialSpecialKirbyDiagram)
    (kind : ElementaryMoveKind) :
    Prop

structure CancellationScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  kind :
    ElementaryMoveKind
  kind_is_cancellation :
    kind = .oneTwoBirth ∨ kind = .oneTwoDeath ∨
    kind = .twoThreeBirth ∨ kind = .twoThreeDeath
  localCancelingPair :
    IsStandardLocalCancelingPair source target kind
  commonExteriorUnchanged :
    CancellationCommonExteriorUnchanged source target
  handleCountChangeIsStandard :
    CancellationHandleCountChangeIsStandard source target kind
  markingCoordinateChangeIsStandard :
    CancellationMarkingCoordinateChangeIsStandard source target kind

/--
An exact chain-level transport for the primal handle complexes, using ordinary
Kirby-calculus indices.  The induced map on quotient homology is derived.
-/
structure PrimalHandleChainTransport
    (source target : CombinatorialSpecialKirbyDiagram)
    (sourceBoundary : PrimalDegreeThreeBoundaryData source)
    (targetBoundary : PrimalDegreeThreeBoundaryData target) where
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
    degreeOne.comp (primalBoundaryTwo source) =
      (primalBoundaryTwo target).comp degreeTwo

def PrimalHandleChainTransport.mapCycle
    {source target : CombinatorialSpecialKirbyDiagram}
    {sourceBoundary : PrimalDegreeThreeBoundaryData source}
    {targetBoundary : PrimalDegreeThreeBoundaryData target}
    (transport :
      PrimalHandleChainTransport source target
        sourceBoundary targetBoundary) :
    PrimalTwoCycles source →+ PrimalTwoCycles target where
  toFun cycle :=
    ⟨transport.degreeTwo cycle.1, by
      change
        ((primalBoundaryTwo target).comp transport.degreeTwo) cycle.1 = 0
      rw [← transport.commutesWithBoundaryTwo]
      change transport.degreeOne (primalBoundaryTwo source cycle.1) = 0
      rw [cycle.2]
      simp⟩
  map_zero' := by
    ext
    simp
  map_add' left right := by
    ext
    simp

def PrimalHandleChainTransport.inducedH₂
    {source target : CombinatorialSpecialKirbyDiagram}
    {sourceBoundary : PrimalDegreeThreeBoundaryData source}
    {targetBoundary : PrimalDegreeThreeBoundaryData target}
    (transport :
      PrimalHandleChainTransport source target
        sourceBoundary targetBoundary) :
    PrimalKirbyH₂ sourceBoundary →+ PrimalKirbyH₂ targetBoundary :=
  QuotientAddGroup.map
    (primalBoundaryAsCycle sourceBoundary).range
    (primalBoundaryAsCycle targetBoundary).range
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

/--
An exact chain-level transport for the THAM-side turned-over complexes.
The handle degrees are `primal 1,2,3 = THAM 3,2,1`.
-/
structure ThamHandleChainTransport
    (source target : HomologicallyMarkedDiagram) where
  degreeThree :
    HandleChainGroup source.diagram.handles.hOne →+
      HandleChainGroup target.diagram.handles.hOne
  degreeTwo :
    HandleChainGroup source.diagram.handles.hTwo →+
      HandleChainGroup target.diagram.handles.hTwo
  degreeOne :
    HandleChainGroup source.diagram.handles.hThree →+
      HandleChainGroup target.diagram.handles.hThree
  commutesWithBoundaryThree :
    degreeTwo.comp source.turnedOver.thamBoundaryThree =
      target.turnedOver.thamBoundaryThree.comp degreeThree
  commutesWithBoundaryTwo :
    degreeOne.comp source.turnedOver.thamBoundaryTwo =
      target.turnedOver.thamBoundaryTwo.comp degreeTwo

def ThamHandleChainTransport.mapCycle
    {source target : HomologicallyMarkedDiagram}
    (transport : ThamHandleChainTransport source target) :
    ThamTwoCycles source.turnedOver →+
      ThamTwoCycles target.turnedOver where
  toFun cycle :=
    ⟨transport.degreeTwo cycle.1, by
      change
        (target.turnedOver.thamBoundaryTwo.comp
          transport.degreeTwo) cycle.1 = 0
      rw [← transport.commutesWithBoundaryTwo]
      change
        transport.degreeOne
          (source.turnedOver.thamBoundaryTwo cycle.1) = 0
      rw [cycle.2]
      simp⟩
  map_zero' := by
    ext
    simp
  map_add' left right := by
    ext
    simp

def ThamHandleChainTransport.inducedH₂
    {source target : HomologicallyMarkedDiagram}
    (transport : ThamHandleChainTransport source target) :
    ThamKirbyH₂ source.turnedOver →+
      ThamKirbyH₂ target.turnedOver :=
  QuotientAddGroup.map
    (thamBoundaryAsCycle source.turnedOver).range
    (thamBoundaryAsCycle target.turnedOver).range
    transport.mapCycle
    (by
      intro sourceBoundaryCycle sourceMembership
      rcases sourceMembership with ⟨degreeThreeChain, rfl⟩
      refine ⟨transport.degreeThree degreeThreeChain, ?_⟩
      apply Subtype.ext
      change
        target.turnedOver.thamBoundaryThree
            (transport.degreeThree degreeThreeChain) =
          transport.degreeTwo
            (source.turnedOver.thamBoundaryThree degreeThreeChain)
      exact (DFunLike.congr_fun
        transport.commutesWithBoundaryThree degreeThreeChain).symm)

/--
The complete category-neutral marking transport for one move.

The final equation is the explicit naturality square between ordinary
Kirby-side `H₂` and THAM-side turned-over `H₂`.  It prevents either side from
silently reusing the other's raw degree-two coordinates.
-/
structure MoveHomologyTransport
    (source target : HomologicallyMarkedDiagram) where
  primal :
    PrimalHandleChainTransport source.diagram target.diagram
      source.primalBoundary target.primalBoundary
  tham : ThamHandleChainTransport source target
  turnover_natural :
    ∀ alpha : PrimalKirbyH₂ source.primalBoundary,
      target.turnover.equiv (primal.inducedH₂ alpha) =
        tham.inducedH₂ (source.turnover.equiv alpha)

inductive ElementaryMove
    (source target : HomologicallyMarkedDiagram) : Type
  | framedIsotopy
      (script : FramedIsotopyScript source.diagram target.diagram)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | oneOverOne
      (script : CleanBandSlideScript source.diagram target.diagram)
      (moving_is_dotted :
        (source.diagram.trace.components script.movingSource).role = .dotted)
      (stationary_is_dotted :
        (source.diagram.trace.components script.stationarySource).role = .dotted)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | twoOverOne
      (script : CleanBandSlideScript source.diagram target.diagram)
      (moving_is_two_handle :
        (source.diagram.trace.components script.movingSource).role ≠ .dotted)
      (stationary_is_dotted :
        (source.diagram.trace.components script.stationarySource).role = .dotted)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | twoOverTwo
      (script : CleanBandSlideScript source.diagram target.diagram)
      (moving_is_two_handle :
        (source.diagram.trace.components script.movingSource).role ≠ .dotted)
      (stationary_is_two_handle :
        (source.diagram.trace.components script.stationarySource).role ≠ .dotted)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | cancellation
      (script : CancellationScript source.diagram target.diagram)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)

def ElementaryMove.homology
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    MoveHomologyTransport source target :=
  match move with
  | .framedIsotopy _ homology _ => homology
  | .oneOverOne _ _ _ homology _ => homology
  | .twoOverOne _ _ _ homology _ => homology
  | .twoOverTwo _ _ _ homology _ => homology
  | .cancellation _ homology _ => homology

def ElementaryMove.primalMarkingTransport
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    target.alpha = move.homology.primal.inducedH₂ source.alpha :=
  match move with
  | .framedIsotopy _ _ markingTransport => markingTransport
  | .oneOverOne _ _ _ _ markingTransport => markingTransport
  | .twoOverOne _ _ _ _ markingTransport => markingTransport
  | .twoOverTwo _ _ _ _ markingTransport => markingTransport
  | .cancellation _ _ markingTransport => markingTransport

theorem ElementaryMove.thamMarkingTransport
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    target.thamAlpha =
      move.homology.tham.inducedH₂ source.thamAlpha := by
  unfold HomologicallyMarkedDiagram.thamAlpha
  rw [move.primalMarkingTransport]
  exact move.homology.turnover_natural source.alpha

structure KirbyMovie
    (source target : HomologicallyMarkedDiagram) where
  stageCount : ℕ
  stages : Fin (stageCount + 1) → HomologicallyMarkedDiagram
  startsAtSource : stages 0 = source
  endsAtTarget : stages (Fin.last stageCount) = target
  elementary :
    ∀ i : Fin stageCount,
      ElementaryMove (stages i.castSucc) (stages i.succ)

end

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 3825
