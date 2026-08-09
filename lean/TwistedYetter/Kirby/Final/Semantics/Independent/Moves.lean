import TwistedYetter.Kirby.Final.Semantics.Independent.LocalReplacementSyntax
import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

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

/-- The four cancellation events, excluding slides and framed isotopy by type. -/
inductive CancellationKind
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving DecidableEq, Repr

def CancellationKind.toElementaryMoveKind : CancellationKind → ElementaryMoveKind
  | .oneTwoBirth => .oneTwoBirth
  | .oneTwoDeath => .oneTwoDeath
  | .twoThreeBirth => .twoThreeBirth
  | .twoThreeDeath => .twoThreeDeath

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
structure FiniteCouponTransport where
  events : List CouponTransportEvent

/--
External handle-topology boundary: the listed finite stages are the complete
route followed by the attaching coupon along the stationary component.  In
particular, no unlisted crossing, cup, cap, twist, or coupon is skipped.

This predicate is category-neutral.  It says nothing about evaluation or
about the character coupon's categorical naturality.
-/
axiom FiniteCouponTransportRealizesCompletePath
    (transport : FiniteCouponTransport) : Prop

/-- The visible component data of one oriented band slide. -/
structure CleanBandSlideScript
    (source target : SpecialKirbyDiagram) where
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
    {source target : SpecialKirbyDiagram}
    (script : CleanBandSlideScript source target) where
  sourceCut : DottedCutPresentation source
  targetCut : DottedCutPresentation target
  transport : FiniteCouponTransport

/--
The complete combinatorial input for one band slide.  Kirby--Cerf
completeness must supply this data as part of the elementary move; it is not
selected later by a separate topology axiom.

Red-team note: this structure is intentionally data-only.  Its exact endpoint,
common-exterior, and framing validity conditions must remain visible in the
move grammar rather than being hidden in an existential witness axiom.
-/
structure CleanBandSlide
    (source target : SpecialKirbyDiagram) where
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
    {source target : SpecialKirbyDiagram} :
    CleanBandSlide source target → Prop

structure FramedIsotopyScript
    (source target : SpecialKirbyDiagram) where
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
    {source target : SpecialKirbyDiagram} :
    FramedIsotopyScript source target → Prop

def CancellationHandleCountChangeIsStandard
    (source target : SpecialKirbyDiagram)
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
    (source target : SpecialKirbyDiagram) where
  cancellationKind : CancellationKind
  handleCountChangeIsStandard :
    CancellationHandleCountChangeIsStandard source target
      cancellationKind.toElementaryMoveKind

def CancellationScript.kind
    {source target : SpecialKirbyDiagram}
    (script : CancellationScript source target) : ElementaryMoveKind :=
  script.cancellationKind.toElementaryMoveKind

theorem CancellationScript.kind_is_cancellation
    {source target : SpecialKirbyDiagram}
    (script : CancellationScript source target) :
    script.kind = .oneTwoBirth ∨ script.kind = .oneTwoDeath ∨
      script.kind = .twoThreeBirth ∨ script.kind = .twoThreeDeath := by
  cases script.cancellationKind <;> simp [CancellationScript.kind,
    CancellationKind.toElementaryMoveKind]

/--
The exact transport visible to the evaluator.

Only primal one- and two-handle coordinates occur.  The commuting square says
that a visible THAM coboundary is sent to a visible THAM coboundary, so the
map descends to `ThamMarkingClass`.  No degree-three attaching map occurs.
-/
structure ThamHandleChainTransport
    (source target : HomologicallyMarkedDiagram) where
  degreeThree :
    HandleChainGroup source.diagram.handles.hOne →+
      HandleChainGroup target.diagram.handles.hOne
  degreeTwo :
    HandleChainGroup source.diagram.handles.hTwo →+
      HandleChainGroup target.diagram.handles.hTwo
  commutesWithVisibleCoboundary :
    degreeTwo.comp (thamVisibleCoboundary source.diagram) =
      (thamVisibleCoboundary target.diagram).comp degreeThree

def ThamHandleChainTransport.mapCoefficients
    {source target : HomologicallyMarkedDiagram}
    (transport : ThamHandleChainTransport source target) :
    ThamTwoHandleCoefficients source.diagram →+
      ThamTwoHandleCoefficients target.diagram :=
  transport.degreeTwo

def ThamHandleChainTransport.inducedMarking
    {source target : HomologicallyMarkedDiagram}
    (transport : ThamHandleChainTransport source target) :
    ThamMarkingClass source.diagram →+
      ThamMarkingClass target.diagram :=
  QuotientAddGroup.map
    (thamVisibleCoboundary source.diagram).range
    (thamVisibleCoboundary target.diagram).range
    transport.mapCoefficients
    (by
      intro sourceCoboundary sourceMembership
      rcases sourceMembership with ⟨degreeOneChain, rfl⟩
      refine ⟨transport.degreeThree degreeOneChain, ?_⟩
      change
        thamVisibleCoboundary target.diagram
            (transport.degreeThree degreeOneChain) =
          transport.degreeTwo
            (thamVisibleCoboundary source.diagram degreeOneChain)
      exact (DFunLike.congr_fun
        transport.commutesWithVisibleCoboundary degreeOneChain).symm)

/-- The category-neutral visible marking transport for one move. -/
structure MoveHomologyTransport
    (source target : HomologicallyMarkedDiagram) where
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
    ∀ (coefficients : ThamTwoHandleCoefficients lower.diagram)
      (i : Fin lower.diagram.handles.hTwo),
      transport.mapCoefficients coefficients (indexEquiv (Sum.inl i)) =
        coefficients i
  newCoefficientZero :
    ∀ coefficients : ThamTwoHandleCoefficients lower.diagram,
      transport.mapCoefficients coefficients (indexEquiv (Sum.inr ())) = 0

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
  safeCoefficients :
    ThamTwoHandleCoefficients higher.diagram →
      ThamTwoHandleCoefficients higher.diagram
  safeCoefficients_sameClass :
    ∀ coefficients,
      thamMarkingClass (safeCoefficients coefficients) =
        thamMarkingClass coefficients
  safe_newCoefficientZero :
    ∀ coefficients,
      safeCoefficients coefficients (indexEquiv (Sum.inr ())) = 0
  transportedOldCoefficient :
    ∀ (coefficients : ThamTwoHandleCoefficients higher.diagram)
      (i : Fin lower.diagram.handles.hTwo),
      transport.mapCoefficients (safeCoefficients coefficients) i =
        safeCoefficients coefficients (indexEquiv (Sum.inl i))

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
        IsStandardOneTwoBirth source.diagram target.diagram
          source.cut target.cut)
  | oneTwoDeath
      (kind : script.kind = .oneTwoDeath)
      (coordinates :
        RemovedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesOneTwoDeathMeridian)
      (normalForm :
        IsStandardOneTwoDeath source.diagram target.diagram
          source.cut target.cut)
  | twoThreeBirth
      (kind : script.kind = .twoThreeBirth)
      (coordinates :
        AddedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesTwoThreeBirthComponent)
      (normalForm :
        IsStandardTwoThreeBirth source.diagram target.diagram
          source.cut target.cut)
  | twoThreeDeath
      (kind : script.kind = .twoThreeDeath)
      (coordinates :
        RemovedTwoHandleCoordinates source target homology.tham)
      (coordinateBinding :
        coordinates.MatchesTwoThreeDeathComponent)
      (normalForm :
        IsStandardTwoThreeDeath source.diagram target.diagram
          source.cut target.cut)

inductive ElementaryMove
    (source target : HomologicallyMarkedDiagram) : Type
  | framedIsotopy
      (script : FramedIsotopyScript source.diagram target.diagram)
      (scriptRealizes :
        FramedIsotopyScriptRealizesFramedIsotopy script)
      (homology : MoveHomologyTransport source target)
      (markingTransport :
        target.thamAlpha = homology.tham.inducedMarking source.thamAlpha)
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
        target.thamAlpha = homology.tham.inducedMarking source.thamAlpha)
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
        target.thamAlpha = homology.tham.inducedMarking source.thamAlpha)
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
        target.thamAlpha = homology.tham.inducedMarking source.thamAlpha)
  | cancellation
      (script : CancellationScript source.diagram target.diagram)
      (homology : MoveHomologyTransport source target)
      (normalForm :
        CancellationLocalNormalForm script homology)
      (markingTransport :
        target.thamAlpha = homology.tham.inducedMarking source.thamAlpha)

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
      move.homology.tham.inducedMarking source.thamAlpha :=
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
