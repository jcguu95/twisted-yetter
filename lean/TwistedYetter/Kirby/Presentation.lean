import Mathlib.Data.List.Basic
import Lean.Elab.Deriving.FromToJson

/-!
# Serializable framed-link and Kirby-presentation syntax

This is the combinatorial input layer.  It deliberately contains no category
objects or morphisms, so it can be serialized and content-addressed before an
evaluator interprets it.  A formal input is a raw presentation together with
the proof that the executable validator accepted every component, event, and
slice transition.
-/

namespace TwistedYetter.Kirby.Presentation

open Lean

/-- Role of a component in a Kirby-style diagram. -/
inductive ComponentRole
  | ordinary
  | dotted
  | speciallyDotted
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- Orientation used both for components and active strands. -/
inductive Orientation
  | positive
  | negative
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- Sign of a crossing or framing twist. -/
inductive CrossingSign
  | positive
  | negative
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- Immutable metadata for one closed component. -/
structure ComponentSpec where
  componentId : String
  role : ComponentRole
  orientation : Orientation
  integerFraming : Int
  blackboardWrithe : Int
  framingCorrection : Int
  kirbyLabel : String
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- One active strand in a horizontal Morse slice. -/
structure StrandState where
  strandId : String
  componentId : String
  orientation : Orientation
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/--
Primitive events in a vertically sliced regular diagram.

Birth and death carry both strand IDs, so lineage is not reconstructed from
positions.  Crossings, coupons, and twists may only reference active strands.
-/
inductive SliceEvent
  | birth
      (eventId componentId positiveStrand negativeStrand : String)
  | death
      (eventId componentId firstStrand secondStrand : String)
  | crossing
      (eventId overStrand underStrand : String)
      (sign : CrossingSign)
  | coupon
      (eventId couponId label : String)
      (strands : List String)
  | framingTwist
      (eventId strandId : String)
      (sign : CrossingSign)
  | planarIsotopy
      (eventId : String)
      (activeOrder : List String)
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

namespace SliceEvent

/-- Stable event identifier, independent of the constructor. -/
def eventId : SliceEvent → String
  | .birth id _ _ _ => id
  | .death id _ _ _ => id
  | .crossing id _ _ _ => id
  | .coupon id _ _ _ => id
  | .framingTwist id _ _ => id
  | .planarIsotopy id _ => id

/-- Components explicitly born at this event. -/
def bornComponent? : SliceEvent → Option String
  | .birth _ componentId _ _ => some componentId
  | _ => none

/-- Components explicitly closed at this event. -/
def deadComponent? : SliceEvent → Option String
  | .death _ componentId _ _ => some componentId
  | _ => none

end SliceEvent

/-- Raw, serializable presentation.  There is intentionally no alias field. -/
structure RawPresentation where
  schema : String
  presentationId : String
  sourceSnapshotHash : String
  components : List ComponentSpec
  events : List SliceEvent
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

namespace RawPresentation

def expectedSchema : String := "twisted-yetter.kirby-presentation.v1"

def stringIdsUnique (ids : List String) : Bool :=
  ids.eraseDups.length == ids.length

def sha256Shape (value : String) : Bool :=
  value.startsWith "sha256:" && value.length == 71

def component? (raw : RawPresentation) (componentId : String) :
    Option ComponentSpec :=
  raw.components.find? (fun component => component.componentId == componentId)

def strand? (state : List StrandState) (strandId : String) :
    Option StrandState :=
  state.find? (fun strand => strand.strandId == strandId)

def eraseStrand (state : List StrandState) (strandId : String) :
    List StrandState :=
  state.filter (fun strand => strand.strandId != strandId)

def activeIds (state : List StrandState) : List String :=
  state.map StrandState.strandId

def allActive (state : List StrandState) (ids : List String) : Bool :=
  ids.all (fun id => (strand? state id).isSome)

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some value => .ok value
  | none => .error message

def framingSound (component : ComponentSpec) : Bool :=
  component.blackboardWrithe + component.framingCorrection ==
    component.integerFraming

def componentsValid (raw : RawPresentation) : Bool :=
  let ids := raw.components.map ComponentSpec.componentId
  !ids.isEmpty &&
    ids.all (fun id => !id.isEmpty) &&
    stringIdsUnique ids &&
    raw.components.all (fun component =>
      !component.kirbyLabel.isEmpty && framingSound component)

def eventsValid (raw : RawPresentation) : Bool :=
  let ids := raw.events.map SliceEvent.eventId
  !ids.isEmpty &&
    ids.all (fun id => !id.isEmpty) &&
    stringIdsUnique ids

def everyComponentBornAndClosed (raw : RawPresentation) : Bool :=
  raw.components.all (fun component =>
    raw.events.any (fun event =>
      event.bornComponent? == some component.componentId) &&
    raw.events.any (fun event =>
      event.deadComponent? == some component.componentId))

/-- Execute one event, rejecting every broken lineage or boundary reference. -/
def applyEvent
    (raw : RawPresentation)
    (state : List StrandState) :
    SliceEvent → Except String (List StrandState)
  | .birth _ componentId positiveStrand negativeStrand => do
      let component ←
        requireSome
          ("birth references unknown component: " ++ componentId)
          (raw.component? componentId)
      if positiveStrand.isEmpty || negativeStrand.isEmpty then
        throw "birth strand IDs must be nonempty"
      if positiveStrand == negativeStrand then
        throw "birth strand IDs must be distinct"
      if (strand? state positiveStrand).isSome ||
          (strand? state negativeStrand).isSome then
        throw "birth reuses an active strand ID"
      return (
        { strandId := positiveStrand
          componentId := component.componentId
          orientation := .positive } ::
        { strandId := negativeStrand
          componentId := component.componentId
          orientation := .negative } ::
        state)
  | .death _ componentId firstStrand secondStrand => do
      if firstStrand == secondStrand then
        throw "death strand IDs must be distinct"
      let first ←
        requireSome
          ("death references inactive strand: " ++ firstStrand)
          (strand? state firstStrand)
      let second ←
        requireSome
          ("death references inactive strand: " ++ secondStrand)
          (strand? state secondStrand)
      if first.componentId != componentId ||
          second.componentId != componentId then
        throw "death crosses component lineage"
      return eraseStrand (eraseStrand state firstStrand) secondStrand
  | .crossing _ overStrand underStrand _ => do
      if overStrand == underStrand then
        throw "crossing requires two distinct active strands"
      if !(allActive state [overStrand, underStrand]) then
        throw "crossing references an inactive strand"
      return state
  | .coupon _ couponId label strands => do
      if couponId.isEmpty || label.isEmpty || strands.isEmpty then
        throw "coupon ID, label, and strand list must be nonempty"
      if !stringIdsUnique strands then
        throw "coupon repeats a strand ID"
      if !(allActive state strands) then
        throw "coupon references an inactive strand"
      return state
  | .framingTwist _ strandId _ => do
      if (strand? state strandId).isNone then
        throw "framing twist references an inactive strand"
      return state
  | .planarIsotopy _ order => do
      if !stringIdsUnique order || order.length != state.length then
        throw "planar isotopy has the wrong active boundary"
      if !(allActive state order) then
        throw "planar isotopy references an inactive strand"
      let reordered := order.filterMap (strand? state)
      if reordered.length != state.length then
        throw "planar isotopy lost component lineage"
      return reordered

/-- Execute all events and retain every Morse slice, including both ends. -/
def runEventsFrom (raw : RawPresentation) :
    List SliceEvent → List StrandState →
      Except String (List (List StrandState))
  | [], state => return [state]
  | event :: rest, state => do
      let next ← raw.applyEvent state event
      let tail ← raw.runEventsFrom rest next
      return state :: tail

def runEvents (raw : RawPresentation) :
    Except String (List (List StrandState)) :=
  raw.runEventsFrom raw.events []

/-- Fail-closed executable admission validator. -/
def validate (raw : RawPresentation) : Except String Unit := do
  if raw.schema != expectedSchema then
    throw "unsupported presentation schema"
  if raw.presentationId.isEmpty then
    throw "presentation ID must be nonempty"
  if !sha256Shape raw.sourceSnapshotHash then
    throw "source snapshot must be a sha256 content hash"
  if !raw.componentsValid then
    throw "invalid component registry or framing relation"
  if !raw.eventsValid then
    throw "invalid or duplicate event IDs"
  if !raw.everyComponentBornAndClosed then
    throw "every component must have recorded birth and death lineage"
  let slices ← raw.runEvents
  match slices.getLast? with
  | some [] => return ()
  | _ => throw "presentation has a nonempty terminal boundary"

/-- Parse raw JSON without granting formal status. -/
def fromJson (json : Json) : Except String RawPresentation :=
  Lean.fromJson? json

/-- Serialize the raw immutable payload. -/
def toJson (raw : RawPresentation) : Json :=
  Lean.toJson raw

end RawPresentation

/--
The only formal presentation input.  The proof field cannot be omitted, and
the underlying raw schema has no mutable alias.
-/
structure FormalPresentation where
  raw : RawPresentation
  admitted : raw.validate = Except.ok ()

namespace FormalPresentation

/-- Accept a parsed payload only when the executable validator succeeds. -/
def accept (raw : RawPresentation) : Except String FormalPresentation :=
  match h : raw.validate with
  | .ok () => .ok { raw := raw, admitted := h }
  | .error message => .error message

/-- JSON parsing and formal admission are deliberately one fail-closed step. -/
def fromJson (json : Json) : Except String FormalPresentation := do
  let raw ← RawPresentation.fromJson json
  accept raw

/--
Formal inputs expose only the content-addressed source snapshot.  There is no
alias projection to rebind.
-/
def pinnedSourceHash (formal : FormalPresentation) : String :=
  formal.raw.sourceSnapshotHash

/-- A formal presentation always exposes the exact validator witness. -/
theorem validation_witness (formal : FormalPresentation) :
    formal.raw.validate = Except.ok () :=
  formal.admitted

/-- The only source selector available on a formal presentation is its hash. -/
theorem pinned_source_hash_eq (formal : FormalPresentation) :
    formal.pinnedSourceHash = formal.raw.sourceSnapshotHash :=
  rfl

end FormalPresentation

/-- Small closed presentation used to kernel-check the generated JSON codec. -/
def roundTripFixture : RawPresentation where
  schema := RawPresentation.expectedSchema
  presentationId := "lean-round-trip-fixture"
  sourceSnapshotHash :=
    "sha256:bcaac3b51bcccde5acce97a5bf62c556398506ff20beabbfff339dd5039cb052"
  components := [
    {
      componentId := "K0"
      role := .ordinary
      orientation := .positive
      integerFraming := 0
      blackboardWrithe := 0
      framingCorrection := 0
      kirbyLabel := "omega"
    }
  ]
  events := [
    .birth "e0" "K0" "K0+" "K0-",
    .coupon "e1" "coupon-0" "identity" ["K0+"],
    .death "e2" "K0" "K0+" "K0-"
  ]

end TwistedYetter.Kirby.Presentation
