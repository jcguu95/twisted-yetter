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

opaque ComponentsFormClosedCircles
    {componentCount strandCount eventCount : ℕ}
    (components : Fin componentCount → Component)
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount)
    (activeOrder : Fin (eventCount + 1) → List (Fin strandCount)) :
    Prop

opaque FramingEventsMatchIntegerFramings
    {componentCount strandCount eventCount : ℕ}
    (components : Fin componentCount → Component)
    (strands : Fin strandCount → Strand componentCount)
    (events : Fin eventCount → DiagramEvent strandCount) :
    Prop

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
  exponent_is_orientation_sign :
    characterExponentSign = 1 ∨ characterExponentSign = -1

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
  activeWordsNoDuplicates :
    ∀ i, (activeOrder i).Nodup
  activeStrandsAreTwoHandles :
    ∀ (i : Fin (eventCount + 1)) (strand : trace.StrandId),
      strand ∈ activeOrder i →
      (trace.components (trace.strands strand).component).role ≠ .dotted

opaque PunctureWordsHaveNoRepeatedOccurrences
    (trace : CombinatorialLinkTrace)
    (punctureWord :
      (dotted : trace.ComponentId) →
        (trace.components dotted).role = .dotted →
        List (DottedPuncture trace)) :
    Prop

opaque CutOpenWordsAreCompatible
    (trace : CombinatorialLinkTrace)
    (punctureWord :
      (dotted : trace.ComponentId) →
        (trace.components dotted).role = .dotted →
        List (DottedPuncture trace)) :
    Prop

opaque RegluingReturnsOriginalTrace
    (trace : CombinatorialLinkTrace)
    (exterior : CutOpenExteriorTrace trace)
    (punctureWord :
      (dotted : trace.ComponentId) →
        (trace.components dotted).role = .dotted →
        List (DottedPuncture trace)) :
    Prop

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
  reglueReturnsOriginalTrace :
    RegluingReturnsOriginalTrace trace exterior punctureWord

/--
The handle information deliberately stops before encoding three-handle
attaching spheres.  `hThree` and `closingBoundaryCertificate` are exactly the
finite primal closing data retained by this special presentation.  Thus
`hOne`, `hTwo`, and `hThree` use ordinary Kirby-calculus indices.
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
  closingBoundaryCertificate : Type
  closingBoundaryWitness : closingBoundaryCertificate

/--
The independent input object.  "Special" means exactly one zero-handle and
one four-handle; these two fixed handles are therefore not stored as counts.
-/
structure CombinatorialSpecialKirbyDiagram where
  trace : CombinatorialLinkTrace
  dottedCuts : DottedCutData trace
  handles : SpecialHandleData trace

/--
Narrow category-neutral topology predicate: the finite cut words are realized
by pairwise compatible spanning disks for the dotted unlink.  It says nothing
about labels, characters, graphical evaluation, or scalar equality.
-/
opaque DottedCutWordsTopologicallyRealizable :
  CombinatorialSpecialKirbyDiagram → Prop

axiom dottedCutWords_topologicallyRealizable
    (diagram : CombinatorialSpecialKirbyDiagram) :
    DottedCutWordsTopologicallyRealizable diagram

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 1617
