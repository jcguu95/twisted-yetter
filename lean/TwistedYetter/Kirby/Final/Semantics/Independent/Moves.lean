import TwistedYetter.Kirby.Final.Semantics.Independent.LocalReplacementSyntax

/-!
# Independent semantics: Kirby moves and H₂ transport

Each move carries an exact source, target, local combinatorial script, and
chain map.  No constructor contains an evaluator equality.
-/

namespace TwistedYetter.Semantics.Independent

noncomputable section

universe uL

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
    degreeTwo.comp source.primalBoundary.thamBoundaryThree =
      target.primalBoundary.thamBoundaryThree.comp degreeThree
  commutesWithBoundaryTwo :
    degreeOne.comp source.primalBoundary.thamBoundaryTwo =
      target.primalBoundary.thamBoundaryTwo.comp degreeTwo

def ThamHandleChainTransport.mapCycle
    {source target : HomologicallyMarkedDiagram}
    (transport : ThamHandleChainTransport source target) :
    ThamTwoCycles source.primalBoundary →+
      ThamTwoCycles target.primalBoundary where
  toFun cycle :=
    ⟨transport.degreeTwo cycle.1, by
      change
        (target.primalBoundary.thamBoundaryTwo.comp
          transport.degreeTwo) cycle.1 = 0
      rw [← transport.commutesWithBoundaryTwo]
      change
        transport.degreeOne
          (source.primalBoundary.thamBoundaryTwo cycle.1) = 0
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
    ThamKirbyH₂ source.primalBoundary →+
      ThamKirbyH₂ target.primalBoundary :=
  QuotientAddGroup.map
    (thamBoundaryAsCycle source.primalBoundary).range
    (thamBoundaryAsCycle target.primalBoundary).range
    transport.mapCycle
    (by
      intro sourceBoundaryCycle sourceMembership
      rcases sourceMembership with ⟨degreeThreeChain, rfl⟩
      refine ⟨transport.degreeThree degreeThreeChain, ?_⟩
      apply Subtype.ext
      change
        target.primalBoundary.thamBoundaryThree
            (transport.degreeThree degreeThreeChain) =
          transport.degreeTwo
            (source.primalBoundary.thamBoundaryThree degreeThreeChain)
      exact (DFunLike.congr_fun
        transport.commutesWithBoundaryThree degreeThreeChain).symm)

/-- The category-neutral primal and THAM handle-chain transports for one move. -/
structure MoveHomologyTransport
    (source target : HomologicallyMarkedDiagram) where
  primal :
    PrimalHandleChainTransport source.diagram target.diagram
      source.primalBoundary target.primalBoundary
  tham : ThamHandleChainTransport source target

/--
Explicit coordinate normal form for adding one primal two-handle.

The equivalence says exactly which target coordinate is the new handle.
The two equations prove that the THAM-side cycle transport preserves every
old coefficient and assigns coefficient zero to the new handle.
-/
structure AddedTwoHandleCoordinates
    (lower higher : HomologicallyMarkedDiagram)
    (transport : ThamHandleChainTransport lower higher) where
  indexEquiv :
    (Fin lower.diagram.handles.hTwo ⊕ Unit) ≃
      Fin higher.diagram.handles.hTwo
  oldCoefficient :
    ∀ (cycle : ThamTwoCycles lower.primalBoundary)
      (i : Fin lower.diagram.handles.hTwo),
      (transport.mapCycle cycle).1 (indexEquiv (Sum.inl i)) =
        cycle.1 i
  newCoefficientZero :
    ∀ cycle : ThamTwoCycles lower.primalBoundary,
      (transport.mapCycle cycle).1 (indexEquiv (Sum.inr ())) = 0

def AddedTwoHandleCoordinates.mergeLabeling
    {lower higher : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport lower higher}
    (coordinates :
      AddedTwoHandleCoordinates lower higher transport)
    {Label : Type uL}
    (lowerLabeling : Fin lower.diagram.handles.hTwo → Label)
    (newLabel : Label) :
    Fin higher.diagram.handles.hTwo → Label :=
  fun i =>
    match coordinates.indexEquiv.symm i with
    | .inl old => lowerLabeling old
    | .inr _ => newLabel

def AddedTwoHandleCoordinates.labelingEquiv
    {lower higher : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport lower higher}
    (coordinates :
      AddedTwoHandleCoordinates lower higher transport)
    (Label : Type uL) :
    ((Fin lower.diagram.handles.hTwo → Label) × Label) ≃
      (Fin higher.diagram.handles.hTwo → Label) where
  toFun pair :=
    coordinates.mergeLabeling pair.1 pair.2
  invFun higherLabeling :=
    (fun i => higherLabeling (coordinates.indexEquiv (Sum.inl i)),
      higherLabeling (coordinates.indexEquiv (Sum.inr ())))
  left_inv pair := by
    rcases pair with ⟨lowerLabeling, newLabel⟩
    apply Prod.ext
    · funext i
      simp [AddedTwoHandleCoordinates.mergeLabeling]
    · simp [AddedTwoHandleCoordinates.mergeLabeling]
  right_inv higherLabeling := by
    funext i
    cases equality : coordinates.indexEquiv.symm i with
    | inl old =>
        have back := coordinates.indexEquiv.apply_symm_apply i
        rw [equality] at back
        simp [AddedTwoHandleCoordinates.mergeLabeling, equality, back]
    | inr new =>
        obtain rfl : new = () := Subsingleton.elim _ _
        have back := coordinates.indexEquiv.apply_symm_apply i
        rw [equality] at back
        simp [AddedTwoHandleCoordinates.mergeLabeling, equality, back]

/--
Explicit coordinate normal form for removing one primal two-handle.

An arbitrary high-side cycle is first replaced by a homologous representative
whose canceling coordinate is zero.  This is the precise chain-contraction
content needed for a death move; evaluation independence of that replacement
is proved separately.
-/
structure RemovedTwoHandleCoordinates
    (higher lower : HomologicallyMarkedDiagram)
    (transport : ThamHandleChainTransport higher lower) where
  indexEquiv :
    (Fin lower.diagram.handles.hTwo ⊕ Unit) ≃
      Fin higher.diagram.handles.hTwo
  safeCycle :
    ThamTwoCycles higher.primalBoundary →
      ThamTwoCycles higher.primalBoundary
  safeCycle_sameClass :
    ∀ cycle,
      thamCycleClass higher.primalBoundary (safeCycle cycle) =
        thamCycleClass higher.primalBoundary cycle
  safe_newCoefficientZero :
    ∀ cycle,
      (safeCycle cycle).1 (indexEquiv (Sum.inr ())) = 0
  transportedOldCoefficient :
    ∀ (cycle : ThamTwoCycles higher.primalBoundary)
      (i : Fin lower.diagram.handles.hTwo),
      (transport.mapCycle (safeCycle cycle)).1 i =
        (safeCycle cycle).1 (indexEquiv (Sum.inl i))

def RemovedTwoHandleCoordinates.splitSafeLabeling
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport)
    {Label : Type uL}
    (higherLabeling : Fin higher.diagram.handles.hTwo → Label) :
    (Fin lower.diagram.handles.hTwo → Label) × Label :=
  (fun i => higherLabeling (coordinates.indexEquiv (Sum.inl i)),
    higherLabeling (coordinates.indexEquiv (Sum.inr ())))

def RemovedTwoHandleCoordinates.mergeLabeling
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport)
    {Label : Type uL}
    (lowerLabeling : Fin lower.diagram.handles.hTwo → Label)
    (removedLabel : Label) :
    Fin higher.diagram.handles.hTwo → Label :=
  fun i =>
    match coordinates.indexEquiv.symm i with
    | .inl old => lowerLabeling old
    | .inr _ => removedLabel

def RemovedTwoHandleCoordinates.labelingEquiv
    {higher lower : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport higher lower}
    (coordinates :
      RemovedTwoHandleCoordinates higher lower transport)
    (Label : Type uL) :
    ((Fin lower.diagram.handles.hTwo → Label) × Label) ≃
      (Fin higher.diagram.handles.hTwo → Label) where
  toFun pair :=
    coordinates.mergeLabeling pair.1 pair.2
  invFun := coordinates.splitSafeLabeling
  left_inv pair := by
    rcases pair with ⟨lowerLabeling, removedLabel⟩
    apply Prod.ext
    · funext i
      simp [RemovedTwoHandleCoordinates.mergeLabeling,
        RemovedTwoHandleCoordinates.splitSafeLabeling]
    · simp [RemovedTwoHandleCoordinates.mergeLabeling,
        RemovedTwoHandleCoordinates.splitSafeLabeling]
  right_inv higherLabeling := by
    funext i
    cases equality : coordinates.indexEquiv.symm i with
    | inl old =>
        have back := coordinates.indexEquiv.apply_symm_apply i
        rw [equality] at back
        simp [RemovedTwoHandleCoordinates.mergeLabeling,
          RemovedTwoHandleCoordinates.splitSafeLabeling, equality, back]
    | inr new =>
        obtain rfl : new = () := Subsingleton.elim _ _
        have back := coordinates.indexEquiv.apply_symm_apply i
        rw [equality] at back
        simp [RemovedTwoHandleCoordinates.mergeLabeling,
          RemovedTwoHandleCoordinates.splitSafeLabeling, equality, back]

/--
The coordinate equivalence for a one--two birth agrees with the literal
component ordering of the canonical local replacement.

Every old two-handle coordinate still names the same raw link component, and
the unique new coordinate names the newly appended ordinary meridian.  This
is finite combinatorial coherence data, not an evaluator equality or an
external topology theorem.
-/
def AddedTwoHandleCoordinates.MatchesOneTwoBirthMeridian
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport) : Prop :=
  (∀ i : Fin source.diagram.handles.hTwo,
    (target.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (source.diagram.handles.twoHandleIndex i).1.1) ∧
  (target.diagram.handles.twoHandleIndex
    (coordinates.indexEquiv (Sum.inr ()))).1.1 =
      source.diagram.trace.componentCount + 1

/--
The reverse coordinate coherence for a one--two death.

The high-side old coordinates agree with the surviving target components,
and the removed coordinate is exactly the ordinary meridian which follows
the target exterior in the canonical birth normal form.
-/
def RemovedTwoHandleCoordinates.MatchesOneTwoDeathMeridian
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport) : Prop :=
  (∀ i : Fin target.diagram.handles.hTwo,
    (source.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (target.diagram.handles.twoHandleIndex i).1.1) ∧
  (source.diagram.handles.twoHandleIndex
    (coordinates.indexEquiv (Sum.inr ()))).1.1 =
      target.diagram.trace.componentCount + 1

/--
Coordinate coherence for a two--three birth.  Old ordinary components retain
their literal component indices, while the unique new 2-handle coordinate is
the isolated ordinary component appended immediately after the source
exterior.
-/
def AddedTwoHandleCoordinates.MatchesTwoThreeBirthComponent
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      AddedTwoHandleCoordinates source target transport) : Prop :=
  (∀ i : Fin source.diagram.handles.hTwo,
    (target.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (source.diagram.handles.twoHandleIndex i).1.1) ∧
  (target.diagram.handles.twoHandleIndex
    (coordinates.indexEquiv (Sum.inr ()))).1.1 =
      source.diagram.trace.componentCount

def RemovedTwoHandleCoordinates.MatchesTwoThreeDeathComponent
    {source target : HomologicallyMarkedDiagram}
    {transport : ThamHandleChainTransport source target}
    (coordinates :
      RemovedTwoHandleCoordinates source target transport) : Prop :=
  (∀ i : Fin target.diagram.handles.hTwo,
    (source.diagram.handles.twoHandleIndex
      (coordinates.indexEquiv (Sum.inl i))).1.1 =
        (target.diagram.handles.twoHandleIndex i).1.1) ∧
  (source.diagram.handles.twoHandleIndex
    (coordinates.indexEquiv (Sum.inr ()))).1.1 =
      target.diagram.trace.componentCount

/--
The four explicit local normal forms accepted for cancellation events.

This is data carried by the move, not an axiom saying that evaluations are
equal.  Its handle-count equation comes from `CancellationScript`; its
coordinate equations are visible above.
-/
inductive CancellationLocalNormalForm
    {source target : HomologicallyMarkedDiagram}
    (script : CancellationScript source.diagram target.diagram)
    (homology : MoveHomologyTransport source target) : Type
  | oneTwoBirth
      (kind : script.kind = .oneTwoBirth)
      (coordinates :
        AddedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesOneTwoBirthMeridian)
      (normalForm :
        IsStandardOneTwoBirth source.diagram target.diagram)
  | oneTwoDeath
      (kind : script.kind = .oneTwoDeath)
      (coordinates :
        RemovedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesOneTwoDeathMeridian)
      (normalForm :
        IsStandardOneTwoDeath source.diagram target.diagram)
  | twoThreeBirth
      (kind : script.kind = .twoThreeBirth)
      (coordinates :
        AddedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesTwoThreeBirthComponent)
      (normalForm :
        IsStandardTwoThreeBirth source.diagram target.diagram)
  | twoThreeDeath
      (kind : script.kind = .twoThreeDeath)
      (coordinates :
        RemovedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesTwoThreeDeathComponent)
      (normalForm :
        IsStandardTwoThreeDeath source.diagram target.diagram)

inductive ElementaryMove
    (source target : HomologicallyMarkedDiagram) : Type
  | framedIsotopy
      (script : FramedIsotopyScript source.diagram target.diagram)
      (scriptRealizes :
        FramedIsotopyScriptRealizesFramedIsotopy script)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.thamAlpha = homology.tham.inducedH₂ source.thamAlpha)
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
        target.thamAlpha = homology.tham.inducedH₂ source.thamAlpha)
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
        target.thamAlpha = homology.tham.inducedH₂ source.thamAlpha)
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
        target.thamAlpha = homology.tham.inducedH₂ source.thamAlpha)
  | cancellation
      (script : CancellationScript source.diagram target.diagram)
      (homology : MoveHomologyTransport source target)
      (normalForm :
        CancellationLocalNormalForm script homology)
      (markingTransport :
        target.thamAlpha = homology.tham.inducedH₂ source.thamAlpha)

def ElementaryMove.homology
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    MoveHomologyTransport source target :=
  match move with
  | .framedIsotopy _ _ homology _ => homology
  | .oneOverOne _ _ _ _ _ homology _ => homology
  | .twoOverOne _ _ _ _ _ homology _ => homology
  | .twoOverTwo _ _ _ _ _ homology _ => homology
  | .cancellation _ homology _ _ => homology

def ElementaryMove.thamMarkingTransport
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    target.thamAlpha =
      move.homology.tham.inducedH₂ source.thamAlpha :=
  match move with
  | .framedIsotopy _ _ _ markingTransport => markingTransport
  | .oneOverOne _ _ _ _ _ _ markingTransport => markingTransport
  | .twoOverOne _ _ _ _ _ _ markingTransport => markingTransport
  | .twoOverTwo _ _ _ _ _ _ markingTransport => markingTransport
  | .cancellation _ _ _ markingTransport => markingTransport

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

-- semantic-freeze-padding: 6760
