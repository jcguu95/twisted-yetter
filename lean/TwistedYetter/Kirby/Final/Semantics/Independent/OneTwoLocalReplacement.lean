import TwistedYetter.Kirby.Final.Semantics.Independent.Moves

/-!
# Exact proof-only normal form for a cancelling one--two pair

This module does not search a Kirby diagram for a cancelling pair. It gives a
finite, category-neutral proposition which an external Kirby-topology theorem
may prove. The normal form appends two components and three cut-open strand
segments, then places the standard birth--projector--death window before the
unchanged source exterior.
-/

namespace TwistedYetter.Semantics.Independent

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
    characterExponentSign := 1
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
The exact serialized normal form for a one--two birth.

No category, character, graphical expression, compiler, evaluation, or scalar
equality occurs here. The source exterior is retained literally; the target
is its canonical append-only reindexing with one dotted component, one
zero-framed ordinary meridian, and the three-event
birth--projector--death window.
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

/--
The sole external topology boundary for both directions. It asserts only
that a move already declared to be a one--two birth or death has the exact
finite local normal form above. It does not locate that form algorithmically.
-/
axiom standardOneTwoCancellation_hasLocalNormalForm
    {source target : CombinatorialSpecialKirbyDiagram}
    (script : CancellationScript source target)
    (isOneTwo :
      script.kind = .oneTwoBirth ∨
        script.kind = .oneTwoDeath) :
    match script.kind with
    | .oneTwoBirth => IsStandardOneTwoBirth source target
    | .oneTwoDeath => IsStandardOneTwoDeath source target
    | _ => False

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 18305
