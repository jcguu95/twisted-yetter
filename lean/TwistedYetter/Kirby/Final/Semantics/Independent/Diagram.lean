import Mathlib

/-!
# Independent semantics: combinatorial special Kirby diagrams

This is the normative topology-side input for the evaluator.  It is finite
combinatorial data.  It is not a smooth knot, an embedded disk, or a parser
certificate borrowed from an existing implementation.

Handle names follow ordinary Kirby calculus throughout this file: dotted
components represent primal one-handles and ordinary framed components
represent primal two-handles.  THAM's turned-over evaluator indexing is a
separate semantic layer in `Homology` and `Evaluator`; it does not rename the
components stored here.
-/

namespace TwistedYetter.Semantics.Independent

inductive ComponentRole
  | ordinary
  | dotted
  | speciallyDotted
  deriving DecidableEq, Repr

inductive StrandOrientation
  | positive
  | negative
  deriving DecidableEq, Repr

inductive CrossingSign
  | positive
  | negative
  deriving DecidableEq, Repr

inductive PunctureDirection
  | withDiskOrientation
  | againstDiskOrientation
  deriving DecidableEq, Repr

def PunctureDirection.intersectionSign : PunctureDirection → ℤ
  | .withDiskOrientation => 1
  | .againstDiskOrientation => -1

structure Component where
  role : ComponentRole
  orientation : StrandOrientation
  integerFraming : ℤ
  deriving DecidableEq, Repr

structure Strand (componentCount : ℕ) where
  component : Fin componentCount
  orientation : StrandOrientation
  deriving DecidableEq, Repr

/--
The finite event grammar for a vertical sweep of a Kirby link diagram.

General categorical coupons do not belong here: they are typed morphisms in
`Graphical`.  A link trace has only cups, caps, crossings, framing twists, and
planar isotopies, so its declared components can genuinely be circles.
-/
inductive DiagramEvent (strandCount : ℕ)
  | birth (leftOutput rightOutput : Fin strandCount)
  | death (leftInput rightInput : Fin strandCount)
  | crossing
      (overInput underInput overOutput underOutput : Fin strandCount)
      (sign : CrossingSign)
  | framingTwist
      (input output : Fin strandCount)
      (sign : CrossingSign)
  | planarIsotopy
      (continuations : List (Fin strandCount × Fin strandCount))
  deriving DecidableEq, Repr

def DiagramEvent.beforeWord {strandCount : ℕ} :
    DiagramEvent strandCount → List (Fin strandCount)
  | .birth _ _ => []
  | .death left right => [left, right]
  | .crossing overInput underInput _ _ _ => [overInput, underInput]
  | .framingTwist input _ _ => [input]
  | .planarIsotopy continuations => continuations.map Prod.fst

def DiagramEvent.afterWord {strandCount : ℕ} :
    DiagramEvent strandCount → List (Fin strandCount)
  | .birth left right => [left, right]
  | .death _ _ => []
  | .crossing _ _ overOutput underOutput _ => [underOutput, overOutput]
  | .framingTwist _ output _ => [output]
  | .planarIsotopy continuations => continuations.map Prod.snd

/--
The local continuation pairing through one event.

At a crossing all four incident edges are explicit.  The over edge continues
only to the over edge, and the under edge only to the under edge.
-/
def DiagramEvent.continuationPairs {strandCount : ℕ} :
    DiagramEvent strandCount →
      List (Fin strandCount × Fin strandCount)
  | .birth leftOutput rightOutput =>
      [(leftOutput, rightOutput)]
  | .death leftInput rightInput =>
      [(leftInput, rightInput)]
  | .crossing overInput underInput overOutput underOutput _ =>
      [(overInput, overOutput), (underInput, underOutput)]
  | .framingTwist input output _ =>
      [(input, output)]
  | .planarIsotopy continuations =>
      continuations

/--
One event replaces one exact contiguous local word and leaves the common
exterior prefix and suffix unchanged.
-/
def EventTransition {strandCount : ℕ}
    (event : DiagramEvent strandCount)
    (before after : List (Fin strandCount)) : Prop :=
  ∃ (leftContext rightContext : List (Fin strandCount)),
    before = leftContext ++ event.beforeWord ++ rightContext ∧
    after = leftContext ++ event.afterWord ++ rightContext

def StrandOccursAsInput
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount)
    (strand : Fin strandCount)
    (i : Fin eventCount) : Prop :=
  strand ∈ (events i).beforeWord

def StrandOccursAsOutput
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount)
    (strand : Fin strandCount)
    (i : Fin eventCount) : Prop :=
  strand ∈ (events i).afterWord

/--
Two strand segments are adjacent when one event explicitly continues one into
the other.  This is an undirected relation by construction.
-/
def StrandsContinueAtEvent
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount)
    (first second : Fin strandCount) :
    Prop :=
  ∃ i : Fin eventCount,
    (first, second) ∈ (events i).continuationPairs ∨
      (second, first) ∈ (events i).continuationPairs

def EventPortsAreDistinct
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop :=
  ∀ i, ((events i).beforeWord ++ (events i).afterWord).Nodup

def DiagramEventContinuationsAreWellFormed
    {componentCount strandCount eventCount : ℕ}
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop :=
  ∀ i first second,
    (first, second) ∈ (events i).continuationPairs →
      (strands first).component = (strands second).component ∧
        match events i with
        | .birth _ _ | .death _ _ =>
            (strands first).orientation ≠ (strands second).orientation
        | .crossing _ _ _ _ _
        | .framingTwist _ _ _
        | .planarIsotopy _ =>
            (strands first).orientation = (strands second).orientation

def EveryStrandHasUniqueInputAndOutput
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop :=
  ∀ strand,
    (∃! i, StrandOccursAsInput events strand i) ∧
      (∃! i, StrandOccursAsOutput events strand i)

def EveryComponentIsConnected
    {componentCount strandCount eventCount : ℕ}
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop :=
  ∀ component,
    ∃ base,
      (strands base).component = component ∧
        ∀ strand,
          (strands strand).component = component →
            Relation.ReflTransGen
              (StrandsContinueAtEvent events)
              base strand

/--
The exact finite incidence conditions saying that every declared component is
one closed circle.  Unique input/output incidence makes every strand segment
two-valent; explicit event continuations pair all local ports, and
connectedness prevents one component ID from naming several disjoint circles.
-/
def ComponentsFormClosedCircles
    {componentCount strandCount eventCount : ℕ}
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop :=
  EventPortsAreDistinct events ∧
    DiagramEventContinuationsAreWellFormed strands events ∧
    EveryStrandHasUniqueInputAndOutput events ∧
    EveryComponentIsConnected strands events

def CrossingSign.toInteger : CrossingSign → ℤ
  | .positive => 1
  | .negative => -1

def DiagramEvent.framingContribution
    {componentCount strandCount : ℕ}
    (component : Fin componentCount)
    (strands : Fin strandCount → Strand componentCount)
    (event : DiagramEvent strandCount) : ℤ :=
  match event with
  | .framingTwist input _ sign =>
      if (strands input).component = component then sign.toInteger else 0
  | _ => 0

/--
The integer framing is exactly the signed number of recorded framing twists on
the component.  This is a transparent finite equation, not a certificate name.
-/
def FramingEventsMatchIntegerFramings
    {componentCount strandCount eventCount : ℕ}
    (components : Fin componentCount → Component)
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop :=
  ∀ component,
    (components component).integerFraming =
      ∑ i : Fin eventCount,
        (events i).framingContribution component strands

structure CombinatorialLinkTrace where
  componentCount : ℕ
  strandCount : ℕ
  eventCount : ℕ
  components : Fin componentCount → Component
  strands : Fin strandCount → Strand componentCount
  events : Fin eventCount → DiagramEvent strandCount
  activeOrder : Fin (eventCount + 1) → List (Fin strandCount)
  initialBoundaryEmpty : activeOrder 0 = []
  finalBoundaryEmpty : activeOrder (Fin.last eventCount) = []
  transitionValid :
    ∀ i : Fin eventCount,
      EventTransition (events i)
        (activeOrder i.castSucc)
        (activeOrder i.succ)
  activeWordsNoDuplicates :
    ∀ i, (activeOrder i).Nodup
  eventPortsAreDistinct :
    EventPortsAreDistinct events
  eventContinuationsAreWellFormed :
    DiagramEventContinuationsAreWellFormed strands events
  everyStrandHasUniqueInputAndOutput :
    EveryStrandHasUniqueInputAndOutput events
  everyComponentIsConnected :
    EveryComponentIsConnected strands events
  framingEventsMatchIntegerFraming :
    FramingEventsMatchIntegerFramings components strands events

theorem CombinatorialLinkTrace.componentIncidenceSatisfiesFiniteCycleConditions
    (trace : CombinatorialLinkTrace) :
    ComponentsFormClosedCircles trace.strands trace.events :=
  ⟨trace.eventPortsAreDistinct,
    trace.eventContinuationsAreWellFormed,
    trace.everyStrandHasUniqueInputAndOutput,
    trace.everyComponentIsConnected⟩

def CombinatorialLinkTrace.ComponentId
    (trace : CombinatorialLinkTrace) := Fin trace.componentCount

def CombinatorialLinkTrace.StrandId
    (trace : CombinatorialLinkTrace) := Fin trace.strandCount

structure DottedPuncture (trace : CombinatorialLinkTrace) where
  dottedComponent : trace.ComponentId
  twoHandleComponent : trace.ComponentId
  inputStrand : trace.StrandId
  outputStrand : trace.StrandId
  direction : PunctureDirection
  cutPosition : ℕ
  dotted_role :
    (trace.components dottedComponent).role = .dotted
  two_handle_role :
    (trace.components twoHandleComponent).role ≠ .dotted
  input_on_two_handle :
    (trace.strands inputStrand).component = twoHandleComponent
  output_on_two_handle :
    (trace.strands outputStrand).component = twoHandleComponent
  orientation_preserved :
    (trace.strands inputStrand).orientation =
      (trace.strands outputStrand).orientation

/--
The category-neutral event language of the tangle obtained after cutting all
dotted spanning disks simultaneously.

A `projectorHole` is not a category morphism.  It only marks the exact ordered
strand word where the evaluator must later insert the normalized tensor-unit
projector.  In particular, this syntax contains neither a Kirby colour nor an
evaluation equality.
-/
inductive CutOpenEvent (trace : CombinatorialLinkTrace)
  | birth (leftOutput rightOutput : trace.StrandId)
  | death (leftInput rightInput : trace.StrandId)
  | crossing
      (overInput underInput overOutput underOutput : trace.StrandId)
      (sign : CrossingSign)
  | framingTwist
      (input output : trace.StrandId)
      (sign : CrossingSign)
  | planarIsotopy
      (continuations : List (trace.StrandId × trace.StrandId))
  | projectorHole
      (dottedComponent : trace.ComponentId)
      (punctures : List (DottedPuncture trace))

def CutOpenEvent.beforeWord
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List trace.StrandId
  | .birth _ _ => []
  | .death left right => [left, right]
  | .crossing overInput underInput _ _ _ => [overInput, underInput]
  | .framingTwist input _ _ => [input]
  | .planarIsotopy continuations => continuations.map Prod.fst
  | .projectorHole _ punctures => punctures.map DottedPuncture.inputStrand

def CutOpenEvent.afterWord
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List trace.StrandId
  | .birth left right => [left, right]
  | .death _ _ => []
  | .crossing _ _ overOutput underOutput _ => [underOutput, overOutput]
  | .framingTwist _ output _ => [output]
  | .planarIsotopy continuations => continuations.map Prod.snd
  | .projectorHole _ punctures => punctures.map DottedPuncture.outputStrand

def CutOpenEvent.continuationPairs
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List (trace.StrandId × trace.StrandId)
  | .birth leftOutput rightOutput =>
      [(leftOutput, rightOutput)]
  | .death leftInput rightInput =>
      [(leftInput, rightInput)]
  | .crossing overInput underInput overOutput underOutput _ =>
      [(overInput, overOutput), (underInput, underOutput)]
  | .framingTwist input output _ =>
      [(input, output)]
  | .planarIsotopy continuations =>
      continuations
  | .projectorHole _ punctures =>
      punctures.map fun puncture =>
        (puncture.inputStrand, puncture.outputStrand)

/--
The category-neutral dual-pairing condition at a cup or cap.

Both strands belong to the same framed component, so every component labeling
assigns them the same simple object.  Their opposite orientations then make
one strand the chosen dual of the other.  This is exactly the information
needed later to interpret a birth or death as coevaluation or evaluation.
-/
def CutOpenEvent.StrandContinuationsAreWellFormed
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → Prop
  | .birth left right =>
      (trace.strands left).component = (trace.strands right).component ∧
        (trace.strands left).orientation ≠
          (trace.strands right).orientation
  | .death left right =>
      (trace.strands left).component = (trace.strands right).component ∧
        (trace.strands left).orientation ≠
          (trace.strands right).orientation
  | .crossing overInput underInput overOutput underOutput _ =>
      (trace.strands overInput).component =
          (trace.strands overOutput).component ∧
        (trace.strands overInput).orientation =
          (trace.strands overOutput).orientation ∧
        (trace.strands underInput).component =
          (trace.strands underOutput).component ∧
        (trace.strands underInput).orientation =
          (trace.strands underOutput).orientation
  | .framingTwist input output _ =>
      (trace.strands input).component =
          (trace.strands output).component ∧
        (trace.strands input).orientation =
          (trace.strands output).orientation
  | .planarIsotopy continuations =>
      ∀ pair ∈ continuations,
        (trace.strands pair.1).component =
            (trace.strands pair.2).component ∧
          (trace.strands pair.1).orientation =
            (trace.strands pair.2).orientation
  | .projectorHole _ punctures =>
      ∀ puncture ∈ punctures,
        (trace.strands puncture.inputStrand).component =
            (trace.strands puncture.outputStrand).component ∧
          (trace.strands puncture.inputStrand).orientation =
            (trace.strands puncture.outputStrand).orientation

def CutOpenEventTransition
    {trace : CombinatorialLinkTrace}
    (event : CutOpenEvent trace)
    (before after : List trace.StrandId) : Prop :=
  ∃ (leftContext rightContext : List trace.StrandId),
    before = leftContext ++ event.beforeWord ++ rightContext ∧
    after = leftContext ++ event.afterWord ++ rightContext

/--
The events allowed while putting a punctured dotted collar into standard
normal form.  The projector itself is deliberately excluded: these events
only bend and transport the original strands to and from the projector waist.
-/
def CutOpenEvent.IsDottedCollarBending
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → Prop
  | .projectorHole _ _ => False
  | _ => True

/--
A finite, category-neutral bending path between two exact strand words.

All correctness fields are transparent combinatorial propositions.  In
particular, this structure contains no category, object label, character,
projector, morphism, or evaluation equality.
-/
structure DottedCollarBendingPath
    (trace : CombinatorialLinkTrace)
    (source target : List trace.StrandId) where
  eventCount : ℕ
  events : Fin eventCount → CutOpenEvent trace
  activeOrder : Fin (eventCount + 1) → List trace.StrandId

/-- All combinatorial correctness conditions for one collar bending path. -/
def DottedCollarBendingPath.FollowsExactBendingTransitions
    {trace : CombinatorialLinkTrace}
    {source target : List trace.StrandId}
    (path : DottedCollarBendingPath trace source target) : Prop :=
  path.activeOrder 0 = source ∧
    path.activeOrder (Fin.last path.eventCount) = target ∧
    (∀ i : Fin path.eventCount,
      CutOpenEventTransition (path.events i)
        (path.activeOrder i.castSucc)
        (path.activeOrder i.succ)) ∧
    (∀ i : Fin path.eventCount,
      (path.events i).StrandContinuationsAreWellFormed) ∧
    (∀ i : Fin path.eventCount,
      (path.events i).IsDottedCollarBending)

/--
The category-neutral clean-collar normal form around one dotted disk.

The input and output words are the literal exterior strands recorded by the
punctures.  `waistWord` is reached by genuine finite cup/cap/braiding/isotopy
paths.  Object dualization is not stored here and will later be read only from
the orientations of the strands occurring in these words.
-/
structure DottedCollarScript
    (trace : CombinatorialLinkTrace)
    (punctures : List (DottedPuncture trace)) where
  waistWord : List trace.StrandId
  bendIn :
    DottedCollarBendingPath trace
      (punctures.map DottedPuncture.inputStrand)
      waistWord
  bendOut :
    DottedCollarBendingPath trace
      waistWord
      (punctures.map DottedPuncture.outputStrand)

/-- The two finite paths of a collar script satisfy their explicit rules. -/
def DottedCollarScript.HasExactBendingPaths
    {trace : CombinatorialLinkTrace}
    {punctures : List (DottedPuncture trace)}
    (script : DottedCollarScript trace punctures) : Prop :=
  script.bendIn.FollowsExactBendingTransitions ∧
    script.bendOut.FollowsExactBendingTransitions

/--
The complete exterior ribbon tangle after all dotted disks have been cut.

This is the data that was absent from frozen v3.  Puncture words alone say
which strands meet a disk, but do not determine how the rest of the tangle
connects those strands.  The event trace records that missing exterior.
-/
structure CutOpenExteriorTrace (trace : CombinatorialLinkTrace) where
  eventCount : ℕ
  events : Fin eventCount → CutOpenEvent trace
  activeOrder : Fin (eventCount + 1) → List trace.StrandId
  initialBoundaryEmpty : activeOrder 0 = []
  finalBoundaryEmpty : activeOrder (Fin.last eventCount) = []
  transitionValid :
    ∀ i : Fin eventCount,
      CutOpenEventTransition (events i)
        (activeOrder i.castSucc)
        (activeOrder i.succ)
  strandContinuationsAreWellFormed :
    ∀ i : Fin eventCount,
      (events i).StrandContinuationsAreWellFormed
  eventPortsAreDistinct :
    ∀ i, ((events i).beforeWord ++ (events i).afterWord).Nodup
  everyStrandHasUniqueInputAndOutput :
    ∀ strand,
      (∃! i : Fin eventCount, strand ∈ (events i).beforeWord) ∧
        (∃! i : Fin eventCount, strand ∈ (events i).afterWord)
  activeWordsNoDuplicates :
    ∀ i, (activeOrder i).Nodup
  activeStrandsAreTwoHandles :
    ∀ (i : Fin (eventCount + 1)) (strand : trace.StrandId),
      strand ∈ activeOrder i →
      (trace.components (trace.strands strand).component).role ≠ .dotted

def PunctureWordsHaveNoRepeatedOccurrences
    (trace : CombinatorialLinkTrace)
    (punctureWord :
      (dotted : trace.ComponentId) →
        (trace.components dotted).role = .dotted →
        List (DottedPuncture trace)) :
    Prop :=
  ∀ (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted)
    (index : Fin (punctureWord dotted role).length),
      let puncture := (punctureWord dotted role).get index
      puncture.dottedComponent = dotted ∧
        puncture.cutPosition = index.1

structure DottedCutData (trace : CombinatorialLinkTrace) where
  punctureWord :
    (dotted : trace.ComponentId) →
      (trace.components dotted).role = .dotted →
      List (DottedPuncture trace)
  exterior : CutOpenExteriorTrace trace
  projectorSite :
    (dotted : trace.ComponentId) →
      (role : (trace.components dotted).role = .dotted) →
      Fin exterior.eventCount
  projectorSite_exact :
    ∀ (dotted : trace.ComponentId)
      (role : (trace.components dotted).role = .dotted),
      exterior.events (projectorSite dotted role) =
        .projectorHole dotted (punctureWord dotted role)
  puncturesHaveNoRepeatedOccurrences :
    PunctureWordsHaveNoRepeatedOccurrences trace punctureWord

/--
Every projector marker in the cut-open trace is exactly the distinguished
marker of one literal dotted component.  Together with `projectorSite_exact`,
this says that dotted components and projector markers are in bijection: no
ordinary component creates a marker, and no additional marker is present.

This is a transparent combinatorial proposition.  It contains no category,
projector morphism, character, or evaluation equality.
-/
def DottedCutData.ProjectorEventsExactlyMatchDottedComponents
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  ∀ (i : Fin cut.exterior.eventCount)
    (dotted : trace.ComponentId)
    (punctures : List (DottedPuncture trace)),
      cut.exterior.events i = .projectorHole dotted punctures →
        ∃ role : (trace.components dotted).role = .dotted,
          i = cut.projectorSite dotted role

/--
The exact puncture word at any projector marker, derived from projector-event
completeness and the already-recorded distinguished site equation.
-/
theorem DottedCutData.projectorEvent_hasExactPunctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (complete : cut.ProjectorEventsExactlyMatchDottedComponents)
    (i : Fin cut.exterior.eventCount)
    (dotted : trace.ComponentId)
    (punctures : List (DottedPuncture trace))
    (event_eq : cut.exterior.events i = .projectorHole dotted punctures) :
    ∃ role : (trace.components dotted).role = .dotted,
      i = cut.projectorSite dotted role ∧
        punctures = cut.punctureWord dotted role := by
  obtain ⟨role, index_eq⟩ := complete i dotted punctures event_eq
  refine ⟨role, index_eq, ?_⟩
  have distinguished_eq :
      cut.exterior.events i =
        .projectorHole dotted (cut.punctureWord dotted role) := by
    rw [index_eq]
    exact cut.projectorSite_exact dotted role
  rw [event_eq] at distinguished_eq
  exact (CutOpenEvent.projectorHole.inj distinguished_eq).2

theorem DottedCutData.puncture_dottedComponent_eq
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted)
    (puncture : DottedPuncture trace)
    (puncture_mem : puncture ∈ cut.punctureWord dotted role) :
    puncture.dottedComponent = dotted := by
  obtain ⟨index, index_eq⟩ := List.mem_iff_get.mp puncture_mem
  rw [← index_eq]
  exact (cut.puncturesHaveNoRepeatedOccurrences dotted role index).1

/--
The handle information deliberately stops before encoding three-handle
attaching spheres.  Only the number `hThree` is retained.  The external claim
that these handles close the presented boundary belongs to the manifold
realization axiom; it is not represented by an arbitrary certificate type and
inhabitant.  Thus `hOne`, `hTwo`, and `hThree` use ordinary Kirby-calculus
indices.
-/
structure SpecialHandleData (trace : CombinatorialLinkTrace) where
  hOne : ℕ
  hTwo : ℕ
  hThree : ℕ
  oneHandleIndex :
    Fin hOne ≃ {component : trace.ComponentId //
      (trace.components component).role = .dotted}
  twoHandleIndex :
    Fin hTwo ≃ {component : trace.ComponentId //
      (trace.components component).role ≠ .dotted}

/--
The independent input object.  "Special" means exactly one zero-handle and
one four-handle; these two fixed handles are therefore not stored as counts.
-/
structure CombinatorialSpecialKirbyDiagram where
  trace : CombinatorialLinkTrace
  dottedCuts : DottedCutData trace
  handles : SpecialHandleData trace

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 1350
