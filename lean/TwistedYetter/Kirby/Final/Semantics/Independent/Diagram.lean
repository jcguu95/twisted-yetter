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

def PunctureDirection.characterExponentSign : PunctureDirection → ℤ
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
The complete finite event grammar for a vertical sweep of a closed ribbon
diagram.  A general coupon has an arbitrary finite input and output word.
-/
inductive DiagramEvent (strandCount : ℕ)
  | birth (left right : Fin strandCount)
  | death (left right : Fin strandCount)
  | crossing (overStrand underStrand : Fin strandCount) (sign : CrossingSign)
  | coupon (name : String) (inputs outputs : List (Fin strandCount))
  | framingTwist (strand : Fin strandCount) (sign : CrossingSign)
  | planarIsotopy (before after : List (Fin strandCount))
  deriving DecidableEq, Repr

def DiagramEvent.beforeWord {strandCount : ℕ} :
    DiagramEvent strandCount → List (Fin strandCount)
  | .birth _ _ => []
  | .death left right => [left, right]
  | .crossing overStrand underStrand _ => [overStrand, underStrand]
  | .coupon _ inputs _ => inputs
  | .framingTwist strand _ => [strand]
  | .planarIsotopy before _ => before

def DiagramEvent.afterWord {strandCount : ℕ} :
    DiagramEvent strandCount → List (Fin strandCount)
  | .birth left right => [left, right]
  | .death _ _ => []
  | .crossing overStrand underStrand _ => [underStrand, overStrand]
  | .coupon _ _ outputs => outputs
  | .framingTwist strand _ => [strand]
  | .planarIsotopy _ after => after

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

def StrandIsBorn
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount)
    (strand : Fin strandCount) : Prop :=
  ∃ i : Fin eventCount, strand ∈ (events i).afterWord

def StrandIsKilled
    {strandCount eventCount : ℕ}
    (events : Fin eventCount → DiagramEvent strandCount)
    (strand : Fin strandCount) : Prop :=
  ∃ i : Fin eventCount, strand ∈ (events i).beforeWord

/--
The finite trace has no hidden closure certificate.  Every strand is created
and removed by the event trace, and every declared component owns at least one
strand.  Together with the empty endpoint words and exact event transitions
stored below, this is the combinatorial closed-circle condition.
-/
def ComponentsFormClosedCircles
    {componentCount strandCount eventCount : ℕ}
    (_components : Fin componentCount → Component)
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount)
    (_activeOrder : Fin (eventCount + 1) → List (Fin strandCount)) :
    Prop :=
  (∀ strand, StrandIsBorn events strand ∧ StrandIsKilled events strand) ∧
    (∀ component, ∃ strand, (strands strand).component = component)

def CrossingSign.toInteger : CrossingSign → ℤ
  | .positive => 1
  | .negative => -1

def DiagramEvent.framingContribution
    {componentCount strandCount : ℕ}
    (component : Fin componentCount)
    (strands : Fin strandCount → Strand componentCount)
    (event : DiagramEvent strandCount) : ℤ :=
  match event with
  | .framingTwist strand sign =>
      if (strands strand).component = component then sign.toInteger else 0
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
  eachComponentIsClosed :
    ComponentsFormClosedCircles components strands events activeOrder
  framingEventsMatchIntegerFraming :
    FramingEventsMatchIntegerFramings components strands events

def CombinatorialLinkTrace.ComponentId
    (trace : CombinatorialLinkTrace) := Fin trace.componentCount

def CombinatorialLinkTrace.StrandId
    (trace : CombinatorialLinkTrace) := Fin trace.strandCount

structure DottedPuncture (trace : CombinatorialLinkTrace) where
  dottedComponent : trace.ComponentId
  twoHandleComponent : trace.ComponentId
  strand : trace.StrandId
  direction : PunctureDirection
  characterExponentSign : ℤ
  cutPosition : ℕ
  dotted_role :
    (trace.components dottedComponent).role = .dotted
  two_handle_role :
    (trace.components twoHandleComponent).role ≠ .dotted
  strand_on_two_handle :
    (trace.strands strand).component = twoHandleComponent
  exponent_matches_direction :
    characterExponentSign = direction.characterExponentSign

/--
The category-neutral event language of the tangle obtained after cutting all
dotted spanning disks simultaneously.

A `projectorHole` is not a category morphism.  It only marks the exact ordered
strand word where the evaluator must later insert the normalized tensor-unit
projector.  In particular, this syntax contains neither a Kirby colour nor an
evaluation equality.
-/
inductive CutOpenEvent (trace : CombinatorialLinkTrace)
  | birth (left right : trace.StrandId)
  | death (left right : trace.StrandId)
  | crossing
      (overStrand underStrand : trace.StrandId)
      (sign : CrossingSign)
  | framingTwist (strand : trace.StrandId) (sign : CrossingSign)
  | planarIsotopy
      (word : List trace.StrandId)
  | projectorHole
      (dottedComponent : trace.ComponentId)
      (punctures : List (DottedPuncture trace))

def CutOpenEvent.beforeWord
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List trace.StrandId
  | .birth _ _ => []
  | .death left right => [left, right]
  | .crossing overStrand underStrand _ => [overStrand, underStrand]
  | .framingTwist strand _ => [strand]
  | .planarIsotopy word => word
  | .projectorHole _ punctures => punctures.map DottedPuncture.strand

def CutOpenEvent.afterWord
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List trace.StrandId
  | .birth left right => [left, right]
  | .death _ _ => []
  | .crossing overStrand underStrand _ => [underStrand, overStrand]
  | .framingTwist strand _ => [strand]
  | .planarIsotopy word => word
  | .projectorHole _ punctures => punctures.map DottedPuncture.strand

/--
The category-neutral dual-pairing condition at a cup or cap.

Both strands belong to the same framed component, so every component labeling
assigns them the same simple object.  Their opposite orientations then make
one strand the chosen dual of the other.  This is exactly the information
needed later to interpret a birth or death as coevaluation or evaluation.
-/
def CutOpenEvent.PairingCompatible
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
  | .crossing _ _ _ => True
  | .framingTwist _ _ => True
  | .planarIsotopy _ => True
  | .projectorHole _ _ => True

def CutOpenEventTransition
    {trace : CombinatorialLinkTrace}
    (event : CutOpenEvent trace)
    (before after : List trace.StrandId) : Prop :=
  ∃ (leftContext rightContext : List trace.StrandId),
    before = leftContext ++ event.beforeWord ++ rightContext ∧
    after = leftContext ++ event.afterWord ++ rightContext

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
  pairingCompatible :
    ∀ i : Fin eventCount,
      (events i).PairingCompatible
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

def CutOpenWordsAreCompatible
    (trace : CombinatorialLinkTrace)
    (punctureWord :
      (dotted : trace.ComponentId) →
        (trace.components dotted).role = .dotted →
        List (DottedPuncture trace)) :
    Prop :=
  ∀ (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted)
    (puncture : DottedPuncture trace),
      puncture ∈ punctureWord dotted role →
        puncture.dottedComponent = dotted

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
  cutOpenWordsAreCompatible :
    CutOpenWordsAreCompatible trace punctureWord

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

-- semantic-freeze-padding: 1595
