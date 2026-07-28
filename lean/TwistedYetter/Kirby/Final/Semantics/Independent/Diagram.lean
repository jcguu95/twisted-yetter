import Mathlib

/-!
# Independent semantics: combinatorial special Kirby diagrams

This is the normative topology-side input for the evaluator.  It is finite
combinatorial data.  It is not a smooth knot, an embedded disk, or a parser
certificate borrowed from an existing implementation.
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
  eachComponentIsClosed : Prop
  eachComponentIsClosed_holds : eachComponentIsClosed
  framingEventsMatchIntegerFraming : Prop
  framingEventsMatchIntegerFraming_holds : framingEventsMatchIntegerFraming

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

structure DottedCutData (trace : CombinatorialLinkTrace) where
  punctureWord :
    (dotted : trace.ComponentId) →
      (trace.components dotted).role = .dotted →
      List (DottedPuncture trace)
  puncturesHaveNoRepeatedOccurrences : Prop
  puncturesHaveNoRepeatedOccurrences_holds :
    puncturesHaveNoRepeatedOccurrences
  cutOpenWordsAreCompatible : Prop
  cutOpenWordsAreCompatible_holds : cutOpenWordsAreCompatible
  reglueReturnsOriginalTrace : Prop
  reglueReturnsOriginalTrace_holds : reglueReturnsOriginalTrace

/--
The handle information deliberately stops before encoding three-handle
attaching spheres.  `hThree` and `closingBoundaryCertificate` are exactly the
finite closing data retained by this special presentation.
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

-- semantic-freeze-padding: 11144
