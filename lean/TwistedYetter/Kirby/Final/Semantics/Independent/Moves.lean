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

/--
A finite topology-side route for coupon transport.

The list records only the finitely many kinds of local events met along the
stationary component.  It does not pretend that the transported character
coupon is part of a Kirby diagram.  The actual before/after expressions and
their naturality proof live in the typed graphical semantics.
-/
structure FiniteCouponTransport
    (attached detachable : CombinatorialSpecialKirbyDiagram) where
  events : List CouponTransportEvent
  stages :
    Fin (events.length + 1) → CombinatorialSpecialKirbyDiagram
  startsAtAttached : stages 0 = attached
  endsAtDetachable : stages (Fin.last events.length) = detachable

/--
External handle-topology boundary: the listed finite stages are the complete
route followed by the attaching coupon along the stationary component.  In
particular, no unlisted crossing, cup, cap, twist, or coupon is skipped.

This predicate is category-neutral.  It says nothing about evaluation or
about the character coupon's categorical naturality.
-/
axiom FiniteCouponTransportRealizesCompletePath
    {attached detachable : CombinatorialSpecialKirbyDiagram} :
    FiniteCouponTransport attached detachable → Prop

/-- The visible component data of one oriented band slide. -/
structure CleanBandSlideScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  movingSource : source.trace.ComponentId
  stationarySource : source.trace.ComponentId
  movingTarget : target.trace.ComponentId
  stationaryTarget : target.trace.ComponentId
  orientation : BandOrientation

/--
The category-neutral topology content of a band slide:

`clean attach → finitely many coupon transports → clean detach`.

The intermediate diagrams and finite proof are existential topology data.
This structure contains no category, character, projector, graphical
evaluation, or scalar equality.
-/
structure CleanBandSlideDecomposition
    {source target : CombinatorialSpecialKirbyDiagram}
    (script : CleanBandSlideScript source target) where
  attached : CombinatorialSpecialKirbyDiagram
  detachable : CombinatorialSpecialKirbyDiagram
  transport :
    FiniteCouponTransport attached detachable

/--
The complete combinatorial input for one band slide.  Kirby--Cerf
completeness must supply this data as part of the elementary move; it is not
selected later by a separate topology axiom.

Red-team note: this structure is intentionally data-only.  Its exact endpoint,
common-exterior, and framing validity conditions must remain visible in the
move grammar rather than being hidden in an existential witness axiom.
-/
structure CleanBandSlide
    (source target : CombinatorialSpecialKirbyDiagram) where
  script : CleanBandSlideScript source target
  decomposition : CleanBandSlideDecomposition script

/--
External handle-topology boundary: the source and target diagrams, component
roles, orientation, framing push-off, clean attaching site, common exterior,
transport window, and clean detaching site in this record realize one
standard oriented Kirby band slide.

This predicate contains no category, character, projector, or evaluation
equality.
-/
axiom CleanBandSlideRealizesStandardKirbySlide
    {source target : CombinatorialSpecialKirbyDiagram} :
    CleanBandSlide source target → Prop

structure FramedIsotopyScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  componentReindexing : source.trace.ComponentId ≃ target.trace.ComponentId
  strandReindexing : source.trace.StrandId ≃ target.trace.StrandId

/--
External handle-topology boundary: the two exact combinatorial diagrams and
the displayed reindexings are related by a framed ambient isotopy preserving
component roles, orientations, framings, dotted cut words, and the common
exterior.

This is a topology statement only; it does not assert graphical evaluation
equality.
-/
axiom FramedIsotopyScriptRealizesFramedIsotopy
    {source target : CombinatorialSpecialKirbyDiagram} :
    FramedIsotopyScript source target → Prop

def CancellationHandleCountChangeIsStandard
    (source target : CombinatorialSpecialKirbyDiagram)
    (kind : ElementaryMoveKind) : Prop :=
  match kind with
  | .oneTwoBirth =>
      target.handles.hOne = source.handles.hOne + 1 ∧
        target.handles.hTwo = source.handles.hTwo + 1 ∧
        target.handles.hThree = source.handles.hThree
  | .oneTwoDeath =>
      source.handles.hOne = target.handles.hOne + 1 ∧
        source.handles.hTwo = target.handles.hTwo + 1 ∧
        source.handles.hThree = target.handles.hThree
  | .twoThreeBirth =>
      target.handles.hOne = source.handles.hOne ∧
        target.handles.hTwo = source.handles.hTwo + 1 ∧
        target.handles.hThree = source.handles.hThree + 1
  | .twoThreeDeath =>
      source.handles.hOne = target.handles.hOne ∧
        source.handles.hTwo = target.handles.hTwo + 1 ∧
        source.handles.hThree = target.handles.hThree + 1
  | _ => False

structure CancellationScript
    (source target : CombinatorialSpecialKirbyDiagram) where
  kind :
    ElementaryMoveKind
  kind_is_cancellation :
    kind = .oneTwoBirth ∨ kind = .oneTwoDeath ∨
    kind = .twoThreeBirth ∨ kind = .twoThreeDeath
  handleCountChangeIsStandard :
    CancellationHandleCountChangeIsStandard source target kind

/--
External handle-topology boundary: the exact source and target contain the
same common exterior and differ only by the standard local canceling
one--two or two--three handle pair specified by `script.kind`.

This predicate does not contain the normalization or evaluation equality
which must later be proved categorically.
-/
axiom CancellationScriptRealizesStandardCancellation
    {source target : CombinatorialSpecialKirbyDiagram} :
    CancellationScript source target → Prop

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
      (scriptRealizes :
        FramedIsotopyScriptRealizesFramedIsotopy script)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | oneOverOne
      (slide : CleanBandSlide source.diagram target.diagram)
      (slideRealizes :
        CleanBandSlideRealizesStandardKirbySlide slide)
      (transportComplete :
        FiniteCouponTransportRealizesCompletePath
          slide.decomposition.transport)
      (moving_is_dotted :
        (source.diagram.trace.components
          slide.script.movingSource).role = .dotted)
      (stationary_is_dotted :
        (source.diagram.trace.components
          slide.script.stationarySource).role = .dotted)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | twoOverOne
      (slide : CleanBandSlide source.diagram target.diagram)
      (slideRealizes :
        CleanBandSlideRealizesStandardKirbySlide slide)
      (transportComplete :
        FiniteCouponTransportRealizesCompletePath
          slide.decomposition.transport)
      (moving_is_two_handle :
        (source.diagram.trace.components
          slide.script.movingSource).role ≠ .dotted)
      (stationary_is_dotted :
        (source.diagram.trace.components
          slide.script.stationarySource).role = .dotted)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | twoOverTwo
      (slide : CleanBandSlide source.diagram target.diagram)
      (slideRealizes :
        CleanBandSlideRealizesStandardKirbySlide slide)
      (transportComplete :
        FiniteCouponTransportRealizesCompletePath
          slide.decomposition.transport)
      (moving_is_two_handle :
        (source.diagram.trace.components
          slide.script.movingSource).role ≠ .dotted)
      (stationary_is_two_handle :
        (source.diagram.trace.components
          slide.script.stationarySource).role ≠ .dotted)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)
  | cancellation
      (script : CancellationScript source.diagram target.diagram)
      (scriptRealizes :
        CancellationScriptRealizesStandardCancellation script)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.alpha = homology.primal.inducedH₂ source.alpha)

def ElementaryMove.homology
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    MoveHomologyTransport source target :=
  match move with
  | .framedIsotopy _ _ homology _ => homology
  | .oneOverOne _ _ _ _ _ homology _ => homology
  | .twoOverOne _ _ _ _ _ homology _ => homology
  | .twoOverTwo _ _ _ _ _ homology _ => homology
  | .cancellation _ _ homology _ => homology

def ElementaryMove.primalMarkingTransport
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    target.alpha = move.homology.primal.inducedH₂ source.alpha :=
  match move with
  | .framedIsotopy _ _ _ markingTransport => markingTransport
  | .oneOverOne _ _ _ _ _ _ markingTransport => markingTransport
  | .twoOverOne _ _ _ _ _ _ markingTransport => markingTransport
  | .twoOverTwo _ _ _ _ _ _ markingTransport => markingTransport
  | .cancellation _ _ _ markingTransport => markingTransport

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

-- semantic-freeze-padding: 1604
