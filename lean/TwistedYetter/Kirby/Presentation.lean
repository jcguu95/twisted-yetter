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
  deriving Repr, BEq, DecidableEq

/-- Orientation used both for components and active strands. -/
inductive Orientation
  | positive
  | negative
  deriving Repr, BEq, DecidableEq

/-- Sign of a crossing or framing twist. -/
inductive CrossingSign
  | positive
  | negative
  deriving Repr, BEq, DecidableEq

/-- Immutable metadata for one closed component. -/
structure ComponentSpec where
  componentId : String
  role : ComponentRole
  orientation : Orientation
  integerFraming : Int
  blackboardWrithe : Int
  framingCorrection : Int
  kirbyLabel : String
  deriving Repr, BEq, DecidableEq

/-- One active strand in a horizontal Morse slice. -/
structure StrandState where
  strandId : String
  componentId : String
  orientation : Orientation
  deriving Repr, BEq, DecidableEq

/--
Primitive events in a vertically sliced regular diagram.

Birth and death carry both strand IDs, so lineage is not reconstructed from
positions.  Crossings, coupons, and twists may only reference active strands.
-/
inductive SliceEvent
  | birth
      (eventId componentId positiveStrand negativeStrand : String)
      (insertAt : Nat)
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
  deriving Repr, BEq, DecidableEq

namespace SliceEvent

/-- Stable event identifier, independent of the constructor. -/
def eventId : SliceEvent → String
  | .birth id _ _ _ _ => id
  | .death id _ _ _ => id
  | .crossing id _ _ _ => id
  | .coupon id _ _ _ => id
  | .framingTwist id _ _ => id
  | .planarIsotopy id _ => id

/-- Components explicitly born at this event. -/
def bornComponent? : SliceEvent → Option String
  | .birth _ componentId _ _ _ => some componentId
  | _ => none

/-- Components explicitly closed at this event. -/
def deadComponent? : SliceEvent → Option String
  | .death _ componentId _ _ => some componentId
  | _ => none

end SliceEvent

/-- One declared horizontal Morse slice from the shared JSON artifact. -/
structure DeclaredSlice where
  index : Nat
  activeStrands : List StrandState
  deriving Repr, BEq, DecidableEq

/--
Raw presentation matching the repository's canonical Python v1 schema.

There is intentionally no alias field.  `contentHash`, rather than the
provenance-only `sourceSnapshotHash`, is the immutable presentation identity.
-/
structure RawPresentation where
  schema : String
  presentationId : String
  sourceSnapshotHash : String
  sourceRef : String
  sourceLocator : String
  components : List ComponentSpec
  events : List SliceEvent
  declaredSlices : List DeclaredSlice
  contentHash : String
  deriving Repr, BEq, DecidableEq

namespace RawPresentation

def expectedSchema : String := "twisted-yetter.kirby-presentation.v1"

def stringIdsUnique (ids : List String) : Bool :=
  ids.eraseDups.length == ids.length

def sha256Shape (value : String) : Bool :=
  let isLowerHexDigit (character : Char) : Bool :=
    character.isDigit ||
      character == 'a' || character == 'b' || character == 'c' ||
      character == 'd' || character == 'e' || character == 'f'
  value.startsWith "sha256:" &&
    value.length == 71 &&
    (value.drop 7).toString.toList.all isLowerHexDigit

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

/-- Insert a block at an exact boundary position. -/
def insertAt?
    {α : Type}
    (values : List α) :
    Nat → List α → Option (List α)
  | 0, rest => some (values ++ rest)
  | _ + 1, [] => none
  | index + 1, head :: tail =>
      (insertAt? values index tail).map (fun result => head :: result)

/-- Two strand orientations may close only when they are opposite. -/
def orientationsOpposite (left right : Orientation) : Bool :=
  match left, right with
  | .positive, .negative => true
  | .negative, .positive => true
  | _, _ => false

/-- Remove one adjacent pair, accepting either listed order. -/
def removeAdjacentPair?
    (firstId secondId : String) :
    List StrandState → Option (List StrandState)
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if
          (first.strandId == firstId && second.strandId == secondId) ||
          (first.strandId == secondId && second.strandId == firstId)
      then
        some rest
      else
        (removeAdjacentPair? firstId secondId (second :: rest)).map
          (fun result => first :: result)

/-- Swap one adjacent pair, accepting either listed order. -/
def swapAdjacentPair?
    (firstId secondId : String) :
    List StrandState → Option (List StrandState)
  | [] => none
  | [_] => none
  | first :: second :: rest =>
      if
          (first.strandId == firstId && second.strandId == secondId) ||
          (first.strandId == secondId && second.strandId == firstId)
      then
        some (second :: first :: rest)
      else
        (swapAdjacentPair? firstId secondId (second :: rest)).map
          (fun result => first :: result)

def sameStringSet (left right : List String) : Bool :=
  left.length == right.length &&
    left.all (fun value => right.contains value) &&
    right.all (fun value => left.contains value)

/-- The selected strand IDs occupy one contiguous Morse-slice window. -/
def hasContiguousWindow
    (state : List StrandState)
    (ids : List String) : Bool :=
  if ids.isEmpty then
    false
  else
    let rec search : List StrandState → Bool
      | [] => false
      | current@(_ :: tail) =>
          sameStringSet
              (activeIds (current.take ids.length)) ids ||
            search tail
    search state

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
  | .birth _ componentId positiveStrand negativeStrand insertAt => do
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
      let inserted ←
        requireSome
          "birth insert_at is outside the active boundary"
          (insertAt? [
            {
              strandId := positiveStrand
              componentId := component.componentId
              orientation := .positive
            },
            {
              strandId := negativeStrand
              componentId := component.componentId
              orientation := .negative
            }
          ] insertAt state)
      return inserted
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
      if !orientationsOpposite first.orientation second.orientation then
        throw "death requires opposite strand orientations"
      return ←
        requireSome
          "death strands are not adjacent in the Morse slice"
          (removeAdjacentPair? firstStrand secondStrand state)
  | .crossing _ overStrand underStrand _ => do
      if overStrand == underStrand then
        throw "crossing requires two distinct active strands"
      if !(allActive state [overStrand, underStrand]) then
        throw "crossing references an inactive strand"
      return ←
        requireSome
          "crossing strands are not adjacent in the Morse slice"
          (swapAdjacentPair? overStrand underStrand state)
  | .coupon _ couponId label strands => do
      if couponId.isEmpty || label.isEmpty || strands.isEmpty then
        throw "coupon ID, label, and strand list must be nonempty"
      if !stringIdsUnique strands then
        throw "coupon repeats a strand ID"
      if !(allActive state strands) then
        throw "coupon references an inactive strand"
      if !hasContiguousWindow state strands then
        throw "coupon strands are not adjacent in the Morse slice"
      return state
  | .framingTwist _ strandId _ => do
      if (strand? state strandId).isNone then
        throw "framing twist references an inactive strand"
      return state
  | .planarIsotopy _ order => do
      if order != activeIds state then
        throw "planar isotopy has the wrong active boundary"
      return state

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

def crossingSignInt : CrossingSign → Int
  | .positive => 1
  | .negative => -1

def adjustWrithe
    (componentId : String)
    (delta : Int) :
    List (String × Int) → List (String × Int)
  | [] => []
  | (currentId, value) :: rest =>
      let updated :=
        if currentId == componentId then
          (currentId, value + delta)
        else
          (currentId, value)
      updated :: adjustWrithe componentId delta rest

def writheContribution
    (state : List StrandState) :
    SliceEvent → Option (String × Int)
  | .crossing _ overStrand underStrand sign =>
      match strand? state overStrand, strand? state underStrand with
      | some over, some under =>
          if over.componentId == under.componentId then
            some (over.componentId, crossingSignInt sign)
          else
            none
      | _, _ => none
  | .framingTwist _ strandId sign =>
      (strand? state strandId).map
        (fun strand => (strand.componentId, crossingSignInt sign))
  | _ => none

def runObservedWritheFrom
    (raw : RawPresentation) :
    List SliceEvent → List StrandState → List (String × Int) →
      Except String (List (String × Int))
  | [], _, ledger => return ledger
  | event :: rest, state, ledger => do
      let nextLedger :=
        match writheContribution state event with
        | some (componentId, delta) =>
            adjustWrithe componentId delta ledger
        | none => ledger
      let nextState ← raw.applyEvent state event
      raw.runObservedWritheFrom rest nextState nextLedger

def observedWrithe (raw : RawPresentation) :
    Except String (List (String × Int)) :=
  raw.runObservedWritheFrom raw.events []
    (raw.components.map (fun component => (component.componentId, 0)))

def writhe? (ledger : List (String × Int)) (componentId : String) :
    Option Int :=
  (ledger.find? (fun entry => entry.1 == componentId)).map Prod.snd

def observedWritheMatches
    (raw : RawPresentation)
    (ledger : List (String × Int)) : Bool :=
  raw.components.all (fun component =>
    writhe? ledger component.componentId ==
      some component.blackboardWrithe)

def declareSlicesFrom :
    Nat → List (List StrandState) → List DeclaredSlice
  | _, [] => []
  | index, state :: rest =>
      { index := index, activeStrands := state } ::
        declareSlicesFrom (index + 1) rest

/-- Every generated slice index is at least the ledger's starting index. -/
theorem index_le_of_mem_declareSlicesFrom
    {start : Nat}
    {states : List (List StrandState)}
    {slice : DeclaredSlice}
    (member : slice ∈ declareSlicesFrom start states) :
    start ≤ slice.index := by
  induction states generalizing start with
  | nil =>
      simp [declareSlicesFrom] at member
  | cons state rest inductionHypothesis =>
      simp only [declareSlicesFrom, List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_refl start
      · have lower :=
          inductionHypothesis (start := start + 1) member
        omega

/--
Generated declared slices are uniquely determined by their index.

This prevents a clean-move certificate from selecting a different slice with
the same advertised position.
-/
theorem eq_of_mem_declareSlicesFrom_of_index_eq
    {start : Nat}
    {states : List (List StrandState)}
    {first second : DeclaredSlice}
    (firstMember : first ∈ declareSlicesFrom start states)
    (secondMember : second ∈ declareSlicesFrom start states)
    (sameIndex : first.index = second.index) :
    first = second := by
  induction states generalizing start with
  | nil =>
      simp [declareSlicesFrom] at firstMember
  | cons state rest inductionHypothesis =>
      simp only [declareSlicesFrom, List.mem_cons] at firstMember secondMember
      rcases firstMember with rfl | firstMember
      · rcases secondMember with rfl | secondMember
        · rfl
        · have lower :=
            index_le_of_mem_declareSlicesFrom
              (start := start + 1) secondMember
          simp at sameIndex
          omega
      · rcases secondMember with rfl | secondMember
        · have lower :=
            index_le_of_mem_declareSlicesFrom
              (start := start + 1) firstMember
          simp at sameIndex
          omega
        · exact inductionHypothesis firstMember secondMember

/-- Fail-closed executable admission validator. -/
def validate (raw : RawPresentation) : Except String Unit := do
  if raw.schema != expectedSchema then
    throw "unsupported presentation schema"
  if raw.presentationId.isEmpty then
    throw "presentation ID must be nonempty"
  if !sha256Shape raw.sourceSnapshotHash then
    throw "source snapshot must be a sha256 content hash"
  if raw.sourceRef.isEmpty then
    throw "source reference must be nonempty"
  if raw.sourceLocator.isEmpty then
    throw "source locator must be nonempty"
  if !sha256Shape raw.contentHash then
    throw "content hash must be a lowercase sha256 content hash"
  if !raw.componentsValid then
    throw "invalid component registry or framing relation"
  if !raw.eventsValid then
    throw "invalid or duplicate event IDs"
  if !raw.everyComponentBornAndClosed then
    throw "every component must have recorded birth and death lineage"
  let slices ← raw.runEvents
  if raw.declaredSlices != declareSlicesFrom 0 slices then
    throw "declared Morse slices do not match event execution"
  let writhe ← raw.observedWrithe
  if !raw.observedWritheMatches writhe then
    throw "component blackboard writhe does not match event execution"
  match slices.getLast? with
  | some [] => return ()
  | _ => throw "presentation has a nonempty terminal boundary"

def requireExactKeys
    (json : Json)
    (expected : List String)
    (where_ : String) : Except String Unit := do
  let object ← json.getObj?
  let observedCount :=
    object.foldl (init := 0) (fun count _ _ => count + 1)
  if observedCount != expected.length then
    throw (where_ ++ " keys mismatch")
  for key in expected do
    if (object.get? key).isNone then
      throw (where_ ++ " is missing key: " ++ key)

def getString (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?

def getNat (json : Json) (key : String) : Except String Nat := do
  (← json.getObjVal? key).getNat?

def getInt (json : Json) (key : String) : Except String Int := do
  (← json.getObjVal? key).getInt?

def getStringList (json : Json) (key : String) :
    Except String (List String) := do
  Lean.fromJson? (← json.getObjVal? key)

def parseRole : String → Except String ComponentRole
  | "ordinary" => return .ordinary
  | "dotted" => return .dotted
  | "specially_dotted" => return .speciallyDotted
  | _ => throw "unknown component role"

def parseOrientation : String → Except String Orientation
  | "positive" => return .positive
  | "negative" => return .negative
  | _ => throw "unknown orientation"

def parseSign : Int → Except String CrossingSign
  | 1 => return .positive
  | -1 => return .negative
  | _ => throw "crossing or twist sign must be exactly -1 or 1"

def parseComponent (json : Json) : Except String ComponentSpec := do
  requireExactKeys json [
    "component_id",
    "role",
    "orientation",
    "integer_framing",
    "blackboard_writhe",
    "framing_correction",
    "kirby_label"
  ] "component"
  return {
    componentId := ← getString json "component_id"
    role := ← parseRole (← getString json "role")
    orientation := ← parseOrientation (← getString json "orientation")
    integerFraming := ← getInt json "integer_framing"
    blackboardWrithe := ← getInt json "blackboard_writhe"
    framingCorrection := ← getInt json "framing_correction"
    kirbyLabel := ← getString json "kirby_label"
  }

def parseStrand (json : Json) : Except String StrandState := do
  requireExactKeys json [
    "strand_id", "component_id", "orientation"
  ] "declared slice strand"
  return {
    strandId := ← getString json "strand_id"
    componentId := ← getString json "component_id"
    orientation := ← parseOrientation (← getString json "orientation")
  }

def parseDeclaredSlice (json : Json) : Except String DeclaredSlice := do
  requireExactKeys json [
    "index", "active_strands"
  ] "declared slice"
  let strandJsons ← (← json.getObjVal? "active_strands").getArr?
  return {
    index := ← getNat json "index"
    activeStrands := ← strandJsons.toList.mapM parseStrand
  }

def parseEvent (json : Json) : Except String SliceEvent := do
  let kind ← getString json "kind"
  match kind with
  | "birth" =>
      requireExactKeys json [
        "event_id",
        "kind",
        "component_id",
        "positive_strand",
        "negative_strand",
        "insert_at"
      ] "birth event"
      return .birth
        (← getString json "event_id")
        (← getString json "component_id")
        (← getString json "positive_strand")
        (← getString json "negative_strand")
        (← getNat json "insert_at")
  | "death" =>
      requireExactKeys json [
        "event_id",
        "kind",
        "component_id",
        "first_strand",
        "second_strand"
      ] "death event"
      return .death
        (← getString json "event_id")
        (← getString json "component_id")
        (← getString json "first_strand")
        (← getString json "second_strand")
  | "crossing" =>
      requireExactKeys json [
        "event_id",
        "kind",
        "over_strand",
        "under_strand",
        "sign"
      ] "crossing event"
      return .crossing
        (← getString json "event_id")
        (← getString json "over_strand")
        (← getString json "under_strand")
        (← parseSign (← getInt json "sign"))
  | "coupon" =>
      requireExactKeys json [
        "event_id",
        "kind",
        "coupon_id",
        "label",
        "strands"
      ] "coupon event"
      return .coupon
        (← getString json "event_id")
        (← getString json "coupon_id")
        (← getString json "label")
        (← getStringList json "strands")
  | "framing_twist" =>
      requireExactKeys json [
        "event_id",
        "kind",
        "strand_id",
        "sign"
      ] "framing twist event"
      return .framingTwist
        (← getString json "event_id")
        (← getString json "strand_id")
        (← parseSign (← getInt json "sign"))
  | "planar_isotopy" =>
      requireExactKeys json [
        "event_id",
        "kind",
        "active_order"
      ] "planar isotopy event"
      return .planarIsotopy
        (← getString json "event_id")
        (← getStringList json "active_order")
  | _ => throw ("unsupported event kind: " ++ kind)

/--
Parse the repository's strict snake-case JSON schema without granting formal
status. Unknown or missing fields are rejected before semantic validation.
-/
def fromJson (json : Json) : Except String RawPresentation := do
  requireExactKeys json [
    "schema",
    "presentation_id",
    "source_snapshot_hash",
    "source_ref",
    "source_locator",
    "components",
    "events",
    "declared_slices",
    "content_hash"
  ] "presentation"
  let componentJsons ← (← json.getObjVal? "components").getArr?
  let eventJsons ← (← json.getObjVal? "events").getArr?
  let sliceJsons ← (← json.getObjVal? "declared_slices").getArr?
  return {
    schema := ← getString json "schema"
    presentationId := ← getString json "presentation_id"
    sourceSnapshotHash := ← getString json "source_snapshot_hash"
    sourceRef := ← getString json "source_ref"
    sourceLocator := ← getString json "source_locator"
    components := ← componentJsons.toList.mapM parseComponent
    events := ← eventJsons.toList.mapM parseEvent
    declaredSlices := ← sliceJsons.toList.mapM parseDeclaredSlice
    contentHash := ← getString json "content_hash"
  }

def roleJson : ComponentRole → Json
  | .ordinary => "ordinary"
  | .dotted => "dotted"
  | .speciallyDotted => "specially_dotted"

def orientationJson : Orientation → Json
  | .positive => "positive"
  | .negative => "negative"

def signJson : CrossingSign → Json
  | .positive => (1 : Int)
  | .negative => (-1 : Int)

def componentJson (component : ComponentSpec) : Json :=
  Json.mkObj [
    ("component_id", component.componentId),
    ("role", roleJson component.role),
    ("orientation", orientationJson component.orientation),
    ("integer_framing", component.integerFraming),
    ("blackboard_writhe", component.blackboardWrithe),
    ("framing_correction", component.framingCorrection),
    ("kirby_label", component.kirbyLabel)
  ]

def strandJson (strand : StrandState) : Json :=
  Json.mkObj [
    ("strand_id", strand.strandId),
    ("component_id", strand.componentId),
    ("orientation", orientationJson strand.orientation)
  ]

def declaredSliceJson (slice : DeclaredSlice) : Json :=
  Json.mkObj [
    ("index", slice.index),
    ("active_strands",
      Json.arr (slice.activeStrands.map strandJson).toArray)
  ]

def eventJson : SliceEvent → Json
  | .birth eventId componentId positiveStrand negativeStrand insertAt =>
      Json.mkObj [
        ("event_id", eventId),
        ("kind", "birth"),
        ("component_id", componentId),
        ("positive_strand", positiveStrand),
        ("negative_strand", negativeStrand),
        ("insert_at", insertAt)
      ]
  | .death eventId componentId firstStrand secondStrand =>
      Json.mkObj [
        ("event_id", eventId),
        ("kind", "death"),
        ("component_id", componentId),
        ("first_strand", firstStrand),
        ("second_strand", secondStrand)
      ]
  | .crossing eventId overStrand underStrand sign =>
      Json.mkObj [
        ("event_id", eventId),
        ("kind", "crossing"),
        ("over_strand", overStrand),
        ("under_strand", underStrand),
        ("sign", signJson sign)
      ]
  | .coupon eventId couponId label strands =>
      Json.mkObj [
        ("event_id", eventId),
        ("kind", "coupon"),
        ("coupon_id", couponId),
        ("label", label),
        ("strands", Lean.toJson strands)
      ]
  | .framingTwist eventId strandId sign =>
      Json.mkObj [
        ("event_id", eventId),
        ("kind", "framing_twist"),
        ("strand_id", strandId),
        ("sign", signJson sign)
      ]
  | .planarIsotopy eventId activeOrder =>
      Json.mkObj [
        ("event_id", eventId),
        ("kind", "planar_isotopy"),
        ("active_order", Lean.toJson activeOrder)
      ]

/-- Serialize exactly the repository's immutable snake-case payload. -/
def toJson (raw : RawPresentation) : Json :=
  Json.mkObj [
    ("schema", raw.schema),
    ("presentation_id", raw.presentationId),
    ("source_snapshot_hash", raw.sourceSnapshotHash),
    ("source_ref", raw.sourceRef),
    ("source_locator", raw.sourceLocator),
    ("components", Json.arr (raw.components.map componentJson).toArray),
    ("events", Json.arr (raw.events.map eventJson).toArray),
    ("declared_slices",
      Json.arr (raw.declaredSlices.map declaredSliceJson).toArray),
    ("content_hash", raw.contentHash)
  ]

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

/-- Formal inputs expose only the presentation's immutable content hash. -/
def pinnedSourceHash (formal : FormalPresentation) : String :=
  formal.raw.contentHash

/-- The source snapshot hash remains visible only as provenance metadata. -/
def provenanceSourceHash (formal : FormalPresentation) : String :=
  formal.raw.sourceSnapshotHash

/-- A formal presentation always exposes the exact validator witness. -/
theorem validation_witness (formal : FormalPresentation) :
    formal.raw.validate = Except.ok () :=
  formal.admitted

/-- The only source selector available on a formal presentation is its hash. -/
theorem pinned_source_hash_eq (formal : FormalPresentation) :
    formal.pinnedSourceHash = formal.raw.contentHash :=
  rfl

end FormalPresentation

/-- Small closed presentation used to kernel-check the generated JSON codec. -/
def roundTripFixture : RawPresentation where
  schema := RawPresentation.expectedSchema
  presentationId := "lean-round-trip-fixture"
  sourceSnapshotHash :=
    "sha256:bcaac3b51bcccde5acce97a5bf62c556398506ff20beabbfff339dd5039cb052"
  sourceRef := "ref:lean-round-trip-synthetic-fixture"
  sourceLocator := "synthetic closed birth-coupon-death fixture"
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
    .birth "e0" "K0" "K0+" "K0-" 0,
    .coupon "e1" "coupon-0" "identity" ["K0+"],
    .death "e2" "K0" "K0+" "K0-"
  ]
  declaredSlices := [
    { index := 0, activeStrands := [] },
    {
      index := 1
      activeStrands := [
        {
          strandId := "K0+"
          componentId := "K0"
          orientation := .positive
        },
        {
          strandId := "K0-"
          componentId := "K0"
          orientation := .negative
        }
      ]
    },
    {
      index := 2
      activeStrands := [
        {
          strandId := "K0+"
          componentId := "K0"
          orientation := .positive
        },
        {
          strandId := "K0-"
          componentId := "K0"
          orientation := .negative
        }
      ]
    },
    { index := 3, activeStrands := [] }
  ]
  contentHash :=
    "sha256:0000000000000000000000000000000000000000000000000000000000000000"

end TwistedYetter.Kirby.Presentation
