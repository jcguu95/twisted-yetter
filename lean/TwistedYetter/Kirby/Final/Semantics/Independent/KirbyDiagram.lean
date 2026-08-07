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

/--
The two component roles of a special Kirby diagram.  Dotted components are
primal one-handles; ordinary framed components are primal two-handles.  There
is no third role whose handle index or evaluator meaning is left unspecified.
-/
inductive ComponentRole
  | ordinary
  | dotted
  deriving DecidableEq, Repr

inductive StrandOrientation
  | positive
  | negative
  deriving DecidableEq, Repr

inductive CrossingSign
  | positive
  | negative
  deriving DecidableEq, Repr

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

/--
The handle information deliberately stops before encoding three-handle
attaching spheres.  Only the number `hThree` is retained.  The external claim
that these handles close the presented boundary belongs to the manifold
realization axiom; it is not represented by an arbitrary certificate type and
inhabitant.  Thus `hOne`, `hTwo`, and `hThree` use ordinary Kirby-calculus
indices.
-/
abbrev HandleChainGroup (count : ℕ) := Fin count → ℤ

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
  boundaryTwo :
    HandleChainGroup hTwo →+ HandleChainGroup hOne
  boundaryThree :
    HandleChainGroup hThree →+ HandleChainGroup hTwo
  boundary_squared_zero :
    boundaryTwo.comp boundaryThree = 0

/--
The independent input object.  "Special" means exactly one zero-handle and
one four-handle; these two fixed handles are therefore not stored as counts.
-/
structure SpecialKirbyDiagram where
  trace : CombinatorialLinkTrace
  handles : SpecialHandleData trace

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 881
