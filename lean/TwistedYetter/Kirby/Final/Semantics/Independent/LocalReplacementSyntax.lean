import TwistedYetter.Kirby.Final.Semantics.Independent.Homology

/-!
# Shared transparent syntax for local Kirby replacements

This module contains only finite serialized diagram data and transparent
predicates.  It deliberately precedes the move grammar so that a move
constructor can require an exact normal-form proof without importing an axiom.
-/

namespace TwistedYetter.Semantics.Independent

structure SerializedStrand where
  component : ℕ
  orientation : StrandOrientation
  deriving DecidableEq, Repr

structure SerializedPuncture where
  dottedComponent : ℕ
  twoHandleComponent : ℕ
  inputStrand : ℕ
  outputStrand : ℕ
  direction : PunctureDirection
  cutPosition : ℕ
  deriving DecidableEq, Repr

inductive SerializedCutOpenEvent
  | birth (leftOutput rightOutput : ℕ)
  | death (leftInput rightInput : ℕ)
  | crossing
      (overInput underInput overOutput underOutput : ℕ)
      (sign : CrossingSign)
  | framingTwist (input output : ℕ) (sign : CrossingSign)
  | planarIsotopy (continuations : List (ℕ × ℕ))
  | projectorHole
      (dottedComponent : ℕ)
      (punctures : List SerializedPuncture)
  deriving DecidableEq, Repr

def serializeStrand
    {componentCount : ℕ}
    (strand : Strand componentCount) :
    SerializedStrand :=
  {
    component := strand.component.1
    orientation := strand.orientation
  }

def serializePuncture
    {trace : CombinatorialLinkTrace}
    (puncture : DottedPuncture trace) :
    SerializedPuncture :=
  {
    dottedComponent := puncture.dottedComponent.1
    twoHandleComponent := puncture.twoHandleComponent.1
    inputStrand := puncture.inputStrand.1
    outputStrand := puncture.outputStrand.1
    direction := puncture.direction
    cutPosition := puncture.cutPosition
  }

def serializeCutOpenEvent
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → SerializedCutOpenEvent
  | .birth left right =>
      .birth left.1 right.1
  | .death left right =>
      .death left.1 right.1
  | .crossing overInput underInput overOutput underOutput sign =>
      .crossing overInput.1 underInput.1 overOutput.1 underOutput.1 sign
  | .framingTwist input output sign =>
      .framingTwist input.1 output.1 sign
  | .planarIsotopy continuations =>
      .planarIsotopy
        (continuations.map fun pair => (pair.1.1, pair.2.1))
  | .projectorHole dotted punctures =>
      .projectorHole dotted.1 (punctures.map serializePuncture)

def serializedComponents
    (diagram : CombinatorialSpecialKirbyDiagram) :
    List Component :=
  List.ofFn diagram.trace.components

def serializedStrands
    (diagram : CombinatorialSpecialKirbyDiagram) :
    List SerializedStrand :=
  List.ofFn (fun i => serializeStrand (diagram.trace.strands i))

def serializedExteriorEvents
    (diagram : CombinatorialSpecialKirbyDiagram) :
    List SerializedCutOpenEvent :=
  List.ofFn
    (fun i =>
      serializeCutOpenEvent (diagram.dottedCuts.exterior.events i))

def serializedActiveOrders
    (diagram : CombinatorialSpecialKirbyDiagram) :
    List (List ℕ) :=
  List.ofFn
    (fun i =>
      (diagram.dottedCuts.exterior.activeOrder i).map Fin.val)

def oneTwoLocalComponents :
    List Component :=
  [
    {
      role := .dotted
      orientation := .positive
      integerFraming := 0
    },
    {
      role := .ordinary
      orientation := .positive
      integerFraming := 0
    }
  ]

def oneTwoLocalStrands
    (source : CombinatorialSpecialKirbyDiagram) :
    List SerializedStrand :=
  let twoHandle := source.trace.componentCount + 1
  [
    { component := twoHandle, orientation := .positive },
    { component := twoHandle, orientation := .negative },
    { component := twoHandle, orientation := .positive }
  ]

def oneTwoLocalPuncture
    (source : CombinatorialSpecialKirbyDiagram) :
    SerializedPuncture :=
  {
    dottedComponent := source.trace.componentCount
    twoHandleComponent := source.trace.componentCount + 1
    inputStrand := source.trace.strandCount
    outputStrand := source.trace.strandCount + 2
    direction := .withDiskOrientation
    cutPosition := 0
  }

def oneTwoLocalEvents
    (source : CombinatorialSpecialKirbyDiagram) :
    List SerializedCutOpenEvent :=
  let first := source.trace.strandCount
  let second := source.trace.strandCount + 1
  let third := source.trace.strandCount + 2
  let dotted := source.trace.componentCount
  [
    .birth first second,
    .projectorHole dotted [oneTwoLocalPuncture source],
    .death third second
  ]

def oneTwoLocalActiveOrders
    (source : CombinatorialSpecialKirbyDiagram) :
    List (List ℕ) :=
  let first := source.trace.strandCount
  let second := source.trace.strandCount + 1
  let third := source.trace.strandCount + 2
  [[], [first, second], [third, second]]

/--
The exact serialized normal form for a one--two birth.  It is finite,
category-neutral data: the source exterior is retained literally and the
target appends one dotted component, one zero-framed ordinary meridian, and
the three-event birth--projector--death window.
-/
def IsStandardOneTwoBirth
    (source target : CombinatorialSpecialKirbyDiagram) : Prop :=
  serializedComponents target =
      serializedComponents source ++ oneTwoLocalComponents ∧
    serializedStrands target =
      serializedStrands source ++ oneTwoLocalStrands source ∧
    serializedExteriorEvents target =
      oneTwoLocalEvents source ++ serializedExteriorEvents source ∧
    serializedActiveOrders target =
      oneTwoLocalActiveOrders source ++ serializedActiveOrders source ∧
    target.handles.hOne = source.handles.hOne + 1 ∧
    target.handles.hTwo = source.handles.hTwo + 1 ∧
    target.handles.hThree = source.handles.hThree

def IsStandardOneTwoDeath
    (source target : CombinatorialSpecialKirbyDiagram) : Prop :=
  IsStandardOneTwoBirth target source

def twoThreeLocalComponents :
    List Component :=
  [
    {
      role := .ordinary
      orientation := .positive
      integerFraming := 0
    }
  ]

def twoThreeLocalStrands
    (source : CombinatorialSpecialKirbyDiagram) :
    List SerializedStrand :=
  let component := source.trace.componentCount
  [
    { component := component, orientation := .positive },
    { component := component, orientation := .negative },
    { component := component, orientation := .positive }
  ]

def twoThreeLocalEvents
    (source : CombinatorialSpecialKirbyDiagram) :
    List SerializedCutOpenEvent :=
  let first := source.trace.strandCount
  let second := source.trace.strandCount + 1
  let third := source.trace.strandCount + 2
  [
    .birth first second,
    .framingTwist first third .positive,
    .death third second
  ]

def twoThreeLocalActiveOrders
    (source : CombinatorialSpecialKirbyDiagram) :
    List (List ℕ) :=
  let first := source.trace.strandCount
  let second := source.trace.strandCount + 1
  let third := source.trace.strandCount + 2
  [[], [first, second], [third, second]]

/--
The exact finite combinatorial normal form of a two--three birth.

The target is the source exterior preceded by one isolated zero-framed
ordinary loop.  Its finite ribbon trace is recorded explicitly as birth,
positive framing twist, and death; the twist must not be silently identified
with the identity on a general simple object.  The final handle equations
record the corresponding primal 2--3 cancellation pair.
-/
def IsStandardTwoThreeBirth
    (source target : CombinatorialSpecialKirbyDiagram) : Prop :=
  serializedComponents target =
      serializedComponents source ++ twoThreeLocalComponents ∧
    serializedStrands target =
      serializedStrands source ++ twoThreeLocalStrands source ∧
    serializedExteriorEvents target =
      twoThreeLocalEvents source ++ serializedExteriorEvents source ∧
    serializedActiveOrders target =
      twoThreeLocalActiveOrders source ++ serializedActiveOrders source ∧
    target.handles.hOne = source.handles.hOne ∧
    target.handles.hTwo = source.handles.hTwo + 1 ∧
    target.handles.hThree = source.handles.hThree + 1

def IsStandardTwoThreeDeath
    (source target : CombinatorialSpecialKirbyDiagram) : Prop :=
  IsStandardTwoThreeBirth target source

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 2393
