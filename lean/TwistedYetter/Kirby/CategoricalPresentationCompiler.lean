import TwistedYetter.Kirby.HomologicallyTwistedInvariant
import TwistedYetter.Kirby.LinearDiagram
import TwistedYetter.Kirby.PresentationExecutionTrace

/-!
# Source-compiled categorical presentations

This module removes one important semantic shortcut: a decorated Kirby
presentation may no longer choose an arbitrary closed categorical diagram and
then merely attach the presentation hash.

`CategoricalEventCompiler` has one mandatory field for each constructor of
the serialized slice-event grammar. `compileTrace` composes those local
diagrams along the exact kernel-checked execution trace, and
`SourceBoundPresentationCompiler.decorate` derives both the closed diagram and
its raw scalar numerator.

This is a compiler mechanism, not a concrete categorical interpretation.
Constructing the six event fields from cups, caps, braidings, twists, coupon
morphisms, and planar identities remains an explicit instance obligation.
-/

namespace TwistedYetter.Kirby.CategoricalPresentationCompiler

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalTangle.Diagram
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationExecutionTrace

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/-- Deterministic right-associated boundary word with no redundant unit. -/
def boundaryWord
    {A : Type*}
    (objectOf : A → C) :
    List A → Boundary C
  | [] => .unit
  | value :: [] => .atom (objectOf value)
  | value :: next :: rest =>
      .tensor (.atom (objectOf value))
        (boundaryWord objectOf (next :: rest))

/-- Machine-visible denominator of serialized event compiler cases. -/
inductive EventCompilerCase where
  | birth
  | death
  | crossing
  | coupon
  | framingTwist
  | planarIsotopy
  deriving Repr, BEq, DecidableEq

/-- Every raw `SliceEvent` constructor appears exactly once. -/
def requiredEventCompilerCases : List EventCompilerCase :=
  [
    .birth,
    .death,
    .crossing,
    .coupon,
    .framingTwist,
    .planarIsotopy
  ]

theorem event_compiler_case_count :
    requiredEventCompilerCases.length = 6 := by
  rfl

theorem event_compiler_cases_unique :
    requiredEventCompilerCases.Nodup := by
  decide

/-- Primitive categorical meaning after resolving event signs. -/
inductive PrimitiveEventKind where
  | birth
  | death
  | crossingPositive
  | crossingNegative
  | coupon
  | twistPositive
  | twistNegative
  | planarIdentity
  deriving Repr, BEq, DecidableEq

def crossingPrimitiveKind :
    Presentation.CrossingSign → PrimitiveEventKind
  | .positive => .crossingPositive
  | .negative => .crossingNegative

def twistPrimitiveKind :
    Presentation.CrossingSign → PrimitiveEventKind
  | .positive => .twistPositive
  | .negative => .twistNegative

/--
Closed whitelist of categorical primitives allowed for one raw event.

The coupon constructor stores the intended morphism because a coupon is
genuine evaluator input. Every other constructor is fixed by categorical
structure.
-/
inductive PrimitiveEventDiagram
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C] :
    PrimitiveEventKind → Boundary C → Boundary C →
      Type (max uC vC)
  | birthRight
      (object dual : C)
      (pairing : ExactPairing object dual) :
      PrimitiveEventDiagram C .birth .unit
        (.tensor (.atom object) (.atom dual))
  | birthLeft
      (object dual : C)
      (pairing : ExactPairing dual object) :
      PrimitiveEventDiagram C .birth .unit
        (.tensor (.atom dual) (.atom object))
  | deathRight
      (object dual : C)
      (pairing : ExactPairing object dual) :
      PrimitiveEventDiagram C .death
        (.tensor (.atom dual) (.atom object)) .unit
  | deathLeft
      (object dual : C)
      (pairing : ExactPairing dual object) :
      PrimitiveEventDiagram C .death
        (.tensor (.atom object) (.atom dual)) .unit
  | crossingPositive (left right : Boundary C) :
      PrimitiveEventDiagram C .crossingPositive
        (.tensor left right) (.tensor right left)
  | crossingNegative (left right : Boundary C) :
      PrimitiveEventDiagram C .crossingNegative
        (.tensor left right) (.tensor right left)
  | coupon
      {source target : Boundary C}
      (couponId label : String)
      (morphism : source.denote ⟶ target.denote) :
      PrimitiveEventDiagram C .coupon source target
  | twistPositive (twist : NaturalTwist C) (object : C) :
      PrimitiveEventDiagram C .twistPositive
        (.atom object) (.atom object)
  | twistNegative (twist : NaturalTwist C) (object : C) :
      PrimitiveEventDiagram C .twistNegative
        (.atom object) (.atom object)
  | planarIdentity (boundary : Boundary C) :
      PrimitiveEventDiagram C .planarIdentity boundary boundary

namespace PrimitiveEventDiagram

/-- Forget only the primitive tag, retaining its exact categorical syntax. -/
def diagram
    {kind : PrimitiveEventKind}
    {source target : Boundary C}
    (primitive : PrimitiveEventDiagram C kind source target) :
    Diagram C source target := by
  cases primitive with
  | birthRight object dual pairing =>
      exact Diagram.exactCup object dual pairing
  | birthLeft object dual pairing =>
      exact Diagram.exactCup dual object pairing
  | deathRight object dual pairing =>
      exact Diagram.exactCap object dual pairing
  | deathLeft object dual pairing =>
      exact Diagram.exactCap dual object pairing
  | crossingPositive left right =>
      exact Diagram.crossing left right
  | crossingNegative left right =>
      exact Diagram.crossingInv left right
  | coupon couponId label morphism =>
      exact Diagram.coupon (couponId ++ ":" ++ label) morphism
  | twistPositive twist object =>
      exact atomicCoupon
        "positive-framing-twist" (twist.iso.hom.app object)
  | twistNegative twist object =>
      exact atomicCoupon
        "negative-framing-twist" (twist.iso.inv.app object)
  | planarIdentity =>
      exact Diagram.identity _

/-- Retain the serialized coupon identity in the primitive syntax. -/
def couponId?
    {kind : PrimitiveEventKind}
    {source target : Boundary C}
    (primitive : PrimitiveEventDiagram C kind source target) :
    Option String :=
  match primitive with
  | .coupon couponId _ _ => some couponId
  | _ => none

/-- Retain the serialized coupon label in the primitive syntax. -/
def couponLabel?
    {kind : PrimitiveEventKind}
    {source target : Boundary C}
    (primitive : PrimitiveEventDiagram C kind source target) :
    Option String :=
  match primitive with
  | .coupon _ label _ => some label
  | _ => none

end PrimitiveEventDiagram

/--
Closed grammar of coherence-only boundary adapters.

These are the only vertical maps allowed outside the distinguished event
primitive. In particular, this grammar has no arbitrary coupon or crossing
constructor.
-/
inductive StructuralDiagram
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] :
    Boundary C → Boundary C → Type (max uC vC)
  | identity (boundary : Boundary C) :
      StructuralDiagram C boundary boundary
  | associatorHom (left middle right : Boundary C) :
      StructuralDiagram C
        (.tensor (.tensor left middle) right)
        (.tensor left (.tensor middle right))
  | associatorInv (left middle right : Boundary C) :
      StructuralDiagram C
        (.tensor left (.tensor middle right))
        (.tensor (.tensor left middle) right)
  | leftUnitorHom (boundary : Boundary C) :
      StructuralDiagram C (.tensor .unit boundary) boundary
  | leftUnitorInv (boundary : Boundary C) :
      StructuralDiagram C boundary (.tensor .unit boundary)
  | rightUnitorHom (boundary : Boundary C) :
      StructuralDiagram C (.tensor boundary .unit) boundary
  | rightUnitorInv (boundary : Boundary C) :
      StructuralDiagram C boundary (.tensor boundary .unit)
  | tensor
      {a b c d : Boundary C} :
      StructuralDiagram C a b →
      StructuralDiagram C c d →
      StructuralDiagram C (.tensor a c) (.tensor b d)
  | comp
      {a b c : Boundary C} :
      StructuralDiagram C a b →
      StructuralDiagram C b c →
      StructuralDiagram C a c

namespace StructuralDiagram

/-- Interpret a structural adapter using only monoidal coherence maps. -/
def diagram
    {source target : Boundary C} :
    StructuralDiagram C source target →
      Diagram C source target
  | .identity boundary =>
      Diagram.identity boundary
  | .associatorHom left middle right =>
      Diagram.coupon "event-context-associator-hom"
        (α_ left.denote middle.denote right.denote).hom
  | .associatorInv left middle right =>
      Diagram.coupon "event-context-associator-inv"
        (α_ left.denote middle.denote right.denote).inv
  | .leftUnitorHom boundary =>
      Diagram.coupon "event-context-left-unitor-hom"
        (λ_ boundary.denote).hom
  | .leftUnitorInv boundary =>
      Diagram.coupon "event-context-left-unitor-inv"
        (λ_ boundary.denote).inv
  | .rightUnitorHom boundary =>
      Diagram.coupon "event-context-right-unitor-hom"
        (ρ_ boundary.denote).hom
  | .rightUnitorInv boundary =>
      Diagram.coupon "event-context-right-unitor-inv"
        (ρ_ boundary.denote).inv
  | .tensor left right =>
      left.diagram ⊗ᵈ right.diagram
  | .comp first second =>
      first.diagram ≫ᵈ second.diagram

/--
Expose one list concatenation as an explicit tensor product.

The recursion emits only associators and unitors. It is the shared structural
adapter used by every event window; individual fixtures cannot choose a
different parenthesization convention.
-/
def splitBoundaryWord
    {A : Type*}
    (objectOf : A → C) :
    (left right : List A) →
      StructuralDiagram C
        (boundaryWord objectOf (left ++ right))
        (.tensor
          (boundaryWord objectOf left)
          (boundaryWord objectOf right))
  | [], right =>
      .leftUnitorInv (boundaryWord objectOf right)
  | [value], [] =>
      .rightUnitorInv (.atom (objectOf value))
  | [_value], _ :: _ =>
      .identity _
  | value :: next :: rest, right =>
      .comp
        (.tensor
          (.identity (.atom (objectOf value)))
          (splitBoundaryWord objectOf (next :: rest) right))
        (.associatorInv
          (.atom (objectOf value))
          (boundaryWord objectOf (next :: rest))
          (boundaryWord objectOf right))

/-- Reassemble the tensor product exposed by `splitBoundaryWord`. -/
def joinBoundaryWord
    {A : Type*}
    (objectOf : A → C) :
    (left right : List A) →
      StructuralDiagram C
        (.tensor
          (boundaryWord objectOf left)
          (boundaryWord objectOf right))
        (boundaryWord objectOf (left ++ right))
  | [], right =>
      .leftUnitorHom (boundaryWord objectOf right)
  | [value], [] =>
      .rightUnitorHom (.atom (objectOf value))
  | [_value], _ :: _ =>
      .identity _
  | value :: next :: rest, right =>
      .comp
        (.associatorHom
          (.atom (objectOf value))
          (boundaryWord objectOf (next :: rest))
          (boundaryWord objectOf right))
        (.tensor
          (.identity (.atom (objectOf value)))
          (joinBoundaryWord objectOf (next :: rest) right))

end StructuralDiagram

/--
One-hole context whose vertical adapters are coherence-only and whose
horizontal complement is identity.
-/
inductive StructuralContext
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C] :
    Boundary C → Boundary C → Boundary C → Boundary C →
      Type (max uC vC)
  | hole (source target : Boundary C) :
      StructuralContext C source target source target
  | compLeft
      {holeSource holeTarget wholeSource : Boundary C}
      (before : StructuralDiagram C wholeSource holeSource) :
      StructuralContext C
        holeSource holeTarget wholeSource holeTarget
  | compRight
      {holeSource holeTarget wholeTarget : Boundary C}
      (after : StructuralDiagram C holeTarget wholeTarget) :
      StructuralContext C
        holeSource holeTarget holeSource wholeTarget
  | tensorLeft
      {holeSource holeTarget : Boundary C}
      (right : Boundary C) :
      StructuralContext C holeSource holeTarget
        (.tensor holeSource right) (.tensor holeTarget right)
  | tensorRight
      (left : Boundary C)
      {holeSource holeTarget : Boundary C} :
      StructuralContext C holeSource holeTarget
        (.tensor left holeSource) (.tensor left holeTarget)
  | compose
      {holeSource holeTarget middleSource middleTarget
        wholeSource wholeTarget : Boundary C}
      (inner :
        StructuralContext C
          holeSource holeTarget middleSource middleTarget)
      (outer :
        StructuralContext C
          middleSource middleTarget wholeSource wholeTarget) :
      StructuralContext C
        holeSource holeTarget wholeSource wholeTarget

namespace StructuralContext

/-- Plug a primitive using no nonstructural surrounding morphism. -/
def plug
    {holeSource holeTarget wholeSource wholeTarget : Boundary C}
    (context :
      StructuralContext C
        holeSource holeTarget wholeSource wholeTarget)
    (piece : Diagram C holeSource holeTarget) :
    Diagram C wholeSource wholeTarget :=
  match context with
  | .hole _ _ => piece
  | .compLeft before => before.diagram ≫ᵈ piece
  | .compRight after => piece ≫ᵈ after.diagram
  | .tensorLeft right =>
      piece ⊗ᵈ Diagram.identity right
  | .tensorRight left =>
      Diagram.identity left ⊗ᵈ piece
  | .compose inner outer =>
      outer.plug (inner.plug piece)

/--
Place one local list window inside exact prefix and suffix tensor words.

All surrounding morphisms are generated by `splitBoundaryWord`,
`joinBoundaryWord`, identities, associators, and unitors. No caller-supplied
coupon or crossing can enter the exterior through this constructor.
-/
def surroundBoundaryWord
    {A : Type*}
    (objectOf : A → C)
    (leading localSource localTarget suffix : List A) :
    StructuralContext C
      (boundaryWord objectOf localSource)
      (boundaryWord objectOf localTarget)
      (boundaryWord objectOf (leading ++ (localSource ++ suffix)))
      (boundaryWord objectOf (leading ++ (localTarget ++ suffix))) := by
  let suffixContext :
      StructuralContext C
        (boundaryWord objectOf localSource)
        (boundaryWord objectOf localTarget)
        (boundaryWord objectOf (localSource ++ suffix))
        (boundaryWord objectOf (localTarget ++ suffix)) :=
    .compose
      (.compose
        (.tensorLeft (boundaryWord objectOf suffix))
        (.compLeft
          (StructuralDiagram.splitBoundaryWord
            objectOf localSource suffix)))
      (.compRight
        (StructuralDiagram.joinBoundaryWord
          objectOf localTarget suffix))
  exact
    .compose
      (.compose
        suffixContext
        (.tensorRight (boundaryWord objectOf leading)))
      (.compose
        (.compLeft
          (StructuralDiagram.splitBoundaryWord objectOf leading
            (localSource ++ suffix)))
        (.compRight
          (StructuralDiagram.joinBoundaryWord objectOf leading
            (localTarget ++ suffix))))

end StructuralContext

/--
One primitive placed in a well-typed surrounding categorical context.

This is strictly stronger than accepting an arbitrary whole-event diagram:
the event's distinguished local node is retained as data and its sign is
fixed by the `kind` index.
-/
structure CompiledCategoricalEvent
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C]
    (kind : PrimitiveEventKind)
    (wholeSource wholeTarget : Boundary C) where
  localSource : Boundary C
  localTarget : Boundary C
  primitive :
    PrimitiveEventDiagram C kind localSource localTarget
  context :
    StructuralContext C
      localSource localTarget wholeSource wholeTarget

namespace CompiledCategoricalEvent

/-- The event diagram is derived by plugging the retained primitive. -/
def diagram
    {kind : PrimitiveEventKind}
    {wholeSource wholeTarget : Boundary C}
    (event :
      CompiledCategoricalEvent C kind wholeSource wholeTarget) :
    Diagram C wholeSource wholeTarget :=
  event.context.plug event.primitive.diagram

end CompiledCategoricalEvent

/--
A framing event whose local primitive is definitionally built from one fixed
twist.

The surrounding structural context may reassociate or insert unitors, but it
cannot replace the positive or negative twist by an unrelated natural
automorphism.
-/
structure CompiledFramingTwistEvent
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C]
    (twist : NaturalTwist C)
    (sign : Presentation.CrossingSign)
    (wholeSource wholeTarget : Boundary C) where
  object : C
  context :
    StructuralContext C
      (.atom object) (.atom object) wholeSource wholeTarget

namespace CompiledFramingTwistEvent

/-- The sign-indexed primitive uses exactly the retained twist. -/
def primitive
    {twist : NaturalTwist C}
    {sign : Presentation.CrossingSign}
    {wholeSource wholeTarget : Boundary C}
    (event :
      CompiledFramingTwistEvent
        C twist sign wholeSource wholeTarget) :
    PrimitiveEventDiagram C (twistPrimitiveKind sign)
      (.atom event.object) (.atom event.object) :=
  match sign with
  | .positive =>
      PrimitiveEventDiagram.twistPositive twist event.object
  | .negative =>
      PrimitiveEventDiagram.twistNegative twist event.object

/-- Plug the fixed-twist primitive into its coherence-only context. -/
def diagram
    {twist : NaturalTwist C}
    {sign : Presentation.CrossingSign}
    {wholeSource wholeTarget : Boundary C}
    (event :
      CompiledFramingTwistEvent
        C twist sign wholeSource wholeTarget) :
    Diagram C wholeSource wholeTarget :=
  event.context.plug event.primitive.diagram

end CompiledFramingTwistEvent

/--
One local categorical compiler for every raw slice-event constructor.

The result boundary is indexed by the exact before/after states accepted by
`RawPresentation.applyEvent`. A caller cannot omit a constructor or compile
an event against unrelated slice states.
-/
structure CategoricalEventCompiler
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C]
    (raw : RawPresentation) where
  framingTwistData : NaturalTwist C
  boundary : List StrandState → Boundary C
  empty_boundary_sound : boundary [] = .unit
  birth :
    (eventId componentId positiveStrand negativeStrand : String) →
    (insertAt : Nat) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.birth eventId componentId positiveStrand negativeStrand insertAt) =
        Except.ok after) →
      CompiledCategoricalEvent C .birth
        (boundary before) (boundary after)
  death :
    (eventId componentId firstStrand secondStrand : String) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.death eventId componentId firstStrand secondStrand) =
        Except.ok after) →
      CompiledCategoricalEvent C .death
        (boundary before) (boundary after)
  crossing :
    (eventId overStrand underStrand : String) →
    (sign : Presentation.CrossingSign) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.crossing eventId overStrand underStrand sign) =
        Except.ok after) →
      CompiledCategoricalEvent C (crossingPrimitiveKind sign)
        (boundary before) (boundary after)
  coupon :
    (eventId couponId label : String) →
    (inputStrands : List String) →
    (outputStrands : List StrandState) →
    (replaceAt : Nat) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.coupon eventId couponId label
            inputStrands outputStrands replaceAt) =
        Except.ok after) →
      CompiledCategoricalEvent C .coupon
        (boundary before) (boundary after)
  framingTwist :
    (eventId strandId : String) →
    (sign : Presentation.CrossingSign) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.framingTwist eventId strandId sign) =
        Except.ok after) →
      CompiledFramingTwistEvent C framingTwistData sign
        (boundary before) (boundary after)
  planarIsotopy :
    (eventId : String) →
    (activeOrder : List String) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.planarIsotopy eventId activeOrder) =
        Except.ok after) →
      CompiledCategoricalEvent C .planarIdentity
        (boundary before) (boundary after)
  compilerSchema : String
  compilerSnapshotHash : String
  compiler_snapshot_hash_shape :
    RawPresentation.sha256Shape compilerSnapshotHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace CategoricalEventCompiler

/-- Exhaustive dispatch over the six serialized event constructors. -/
def compileEvent
    {raw : RawPresentation}
    (compiler : CategoricalEventCompiler C raw)
    {before after : List StrandState}
    (event : SliceEvent)
    (step_sound : raw.applyEvent before event = Except.ok after) :
    Diagram C (compiler.boundary before) (compiler.boundary after) :=
  match event with
  | .birth eventId componentId positiveStrand negativeStrand insertAt =>
      (compiler.birth eventId componentId positiveStrand negativeStrand
        insertAt step_sound).diagram
  | .death eventId componentId firstStrand secondStrand =>
      (compiler.death
        eventId componentId firstStrand secondStrand step_sound).diagram
  | .crossing eventId overStrand underStrand sign =>
      (compiler.crossing
        eventId overStrand underStrand sign step_sound).diagram
  | .coupon eventId couponId label inputStrands outputStrands replaceAt =>
      (compiler.coupon eventId couponId label
        inputStrands outputStrands replaceAt step_sound).diagram
  | .framingTwist eventId strandId sign =>
      (compiler.framingTwist eventId strandId sign step_sound).diagram
  | .planarIsotopy eventId activeOrder =>
      (compiler.planarIsotopy eventId activeOrder step_sound).diagram

/-- Compose local event diagrams along the exact typed execution trace. -/
def compileTrace
    {raw : RawPresentation}
    (compiler : CategoricalEventCompiler C raw)
    {events : List SliceEvent}
    {before final : List StrandState} :
    ExecutionTrace raw events before final →
      Diagram C (compiler.boundary before) (compiler.boundary final)
  | .nil state =>
      Diagram.identity (compiler.boundary state)
  | .cons step_sound tail =>
      compiler.compileEvent _ step_sound ≫ᵈ
        compiler.compileTrace tail

/-- Compile a closed trace into a closed categorical diagram. -/
def compileClosed
    {formal : FormalPresentation}
    (compiler : CategoricalEventCompiler C formal.raw)
    (execution : ClosedExecutionCertificate formal) :
    Diagram C .unit .unit := by
  rw [← compiler.empty_boundary_sound]
  exact compiler.compileTrace execution.trace

end CategoricalEventCompiler

/--
One local primitive together with an exact list window.

This is the narrow semantic input accepted by the final event route. The
caller chooses the actual coupon morphism or recorded dual pairing inside the
primitive, but cannot choose the surrounding categorical diagram. Prefix,
suffix, and parenthesization are compiled by `surroundBoundaryWord`.
-/
structure WindowedCategoricalEvent
    (objectOf : StrandState → C)
    (kind : PrimitiveEventKind)
    (before after : List StrandState) where
  leading : List StrandState
  localSource : List StrandState
  localTarget : List StrandState
  suffix : List StrandState
  before_sound :
    before = leading ++ (localSource ++ suffix)
  after_sound :
    after = leading ++ (localTarget ++ suffix)
  primitive :
    PrimitiveEventDiagram C kind
      (boundaryWord objectOf localSource)
      (boundaryWord objectOf localTarget)

namespace WindowedCategoricalEvent

/-- Compile a retained local window into the unique coherence-only exterior. -/
def toCompiled
    {objectOf : StrandState → C}
    {kind : PrimitiveEventKind}
    {before after : List StrandState}
    (event : WindowedCategoricalEvent objectOf kind before after) :
    CompiledCategoricalEvent C kind
      (boundaryWord objectOf before)
      (boundaryWord objectOf after) := by
  let compiled :
      CompiledCategoricalEvent C kind
        (boundaryWord objectOf
          (event.leading ++ (event.localSource ++ event.suffix)))
        (boundaryWord objectOf
          (event.leading ++ (event.localTarget ++ event.suffix))) := {
    localSource := boundaryWord objectOf event.localSource
    localTarget := boundaryWord objectOf event.localTarget
    primitive := event.primitive
    context :=
      StructuralContext.surroundBoundaryWord objectOf
        event.leading event.localSource event.localTarget event.suffix
  }
  simpa only [event.before_sound, event.after_sound] using compiled

end WindowedCategoricalEvent

/--
A birth window bound to the exact serialized component and strand records.

The four equalities prevent a valid cup on two unrelated but
category-isomorphic strands from being substituted for the requested birth.
-/
structure BoundBirthEvent
    (objectOf : StrandState → C)
    (componentId positiveStrand negativeStrand : String)
    (before after : List StrandState) where
  window :
    WindowedCategoricalEvent objectOf .birth before after
  local_source_empty :
    window.localSource = []
  local_target_ids_sound :
    window.localTarget.map (fun strand => strand.strandId) =
      [positiveStrand, negativeStrand]
  local_target_components_sound :
    window.localTarget.map (fun strand => strand.componentId) =
      [componentId, componentId]
  local_target_orientations_sound :
    window.localTarget.map (fun strand => strand.orientation) =
      [.positive, .negative]

/--
A death window bound to the exact serialized component and two strand IDs.

The local source order is retained by the window because it selects the
right- or left-dual cap. The serialized pair may be listed in either order,
so the ID check uses the same finite-set predicate as the validator.
-/
structure BoundDeathEvent
    (objectOf : StrandState → C)
    (componentId firstStrand secondStrand : String)
    (before after : List StrandState) where
  window :
    WindowedCategoricalEvent objectOf .death before after
  local_target_empty :
    window.localTarget = []
  local_source_ids_sound :
    RawPresentation.sameStringSet
        (window.localSource.map (fun strand => strand.strandId))
        [firstStrand, secondStrand] =
      true
  local_source_components_sound :
    window.localSource.map (fun strand => strand.componentId) =
      [componentId, componentId]

/--
A crossing window bound to the exact ordered over/under pair.

The raw validator accepts only adjacent strands but does not record a
category morphism. This wrapper fixes the convention used by the categorical
compiler: the over strand is the left tensor factor before the crossing.
Presentations using the opposite serialization convention must first pass an
explicit convention adapter.
-/
structure BoundCrossingEvent
    (objectOf : StrandState → C)
    (kind : PrimitiveEventKind)
    (overStrand underStrand : String)
    (before after : List StrandState) where
  window :
    WindowedCategoricalEvent objectOf kind before after
  left : StrandState
  right : StrandState
  local_source_sound :
    window.localSource = [left, right]
  local_target_sound :
    window.localTarget = [right, left]
  ordered_ids_sound :
    [left.strandId, right.strandId] =
      [overStrand, underStrand]

/--
A coupon window bound to its exact ordered input and output words, coupon ID,
and label.

The morphism remains genuine category input. Its source and target, however,
must be the requested contiguous boundary window, and its serialized identity
cannot be silently renamed.
-/
structure BoundCouponEvent
    (objectOf : StrandState → C)
    (couponId label : String)
    (inputStrands : List String)
    (outputStrands : List StrandState)
    (before after : List StrandState) where
  window :
    WindowedCategoricalEvent objectOf .coupon before after
  localInput : List StrandState
  localOutput : List StrandState
  local_source_sound :
    window.localSource = localInput
  local_target_sound :
    window.localTarget = localOutput
  ordered_input_ids_sound :
    localInput.map (fun strand => strand.strandId) = inputStrands
  output_word_sound :
    localOutput = outputStrands
  coupon_id_sound :
    window.primitive.couponId? = some couponId
  coupon_label_sound :
    window.primitive.couponLabel? = some label

/--
One framing event localized to exactly one retained strand.

The primitive is not an input: `toCompiled` always uses the single twist
stored by the surrounding compiler.
-/
structure WindowedFramingTwistEvent
    (objectOf : StrandState → C)
    (strandId : String)
    (before after : List StrandState) where
  leading : List StrandState
  strand : StrandState
  suffix : List StrandState
  strand_id_sound :
    strand.strandId = strandId
  before_sound :
    before = leading ++ ([strand] ++ suffix)
  after_sound :
    after = leading ++ ([strand] ++ suffix)

namespace WindowedFramingTwistEvent

/-- Compile the one-strand window using exactly the retained framing twist. -/
def toCompiled
    {objectOf : StrandState → C}
    {strandId : String}
    {before after : List StrandState}
    (event :
      WindowedFramingTwistEvent objectOf strandId before after)
    (twist : NaturalTwist C)
    (sign : Presentation.CrossingSign) :
    CompiledFramingTwistEvent C twist sign
      (boundaryWord objectOf before)
      (boundaryWord objectOf after) := by
  let compiled :
      CompiledFramingTwistEvent C twist sign
        (boundaryWord objectOf
          (event.leading ++ ([event.strand] ++ event.suffix)))
        (boundaryWord objectOf
          (event.leading ++ ([event.strand] ++ event.suffix))) := {
    object := objectOf event.strand
    context :=
      StructuralContext.surroundBoundaryWord objectOf
        event.leading [event.strand] [event.strand] event.suffix
  }
  simpa only [event.before_sound, event.after_sound] using compiled

end WindowedFramingTwistEvent

/--
A planar-isotopy marker bound to the complete declared active order.

The current serialized event is an identity marker, not a free boundary
permutation. Consequently the categorical primitive must cover the complete
boundary and remain the identity there.
-/
structure BoundPlanarIsotopyEvent
    (objectOf : StrandState → C)
    (activeOrder : List String)
    (before after : List StrandState) where
  window :
    WindowedCategoricalEvent objectOf .planarIdentity before after
  local_source_sound :
    window.localSource = before
  local_target_sound :
    window.localTarget = after
  active_order_sound :
    before.map (fun strand => strand.strandId) = activeOrder

/--
The complete local semantic denominator for one serialized presentation.

Every field returns a single primitive in an exact list window. This is
strictly narrower than `CategoricalEventCompiler`: no field may return a
whole diagram or an arbitrary categorical exterior.
-/
structure WindowedCategoricalEventSemantics
    (raw : RawPresentation)
    (objectOf : StrandState → C)
    (framingTwistData : NaturalTwist C) where
  birth :
    (eventId componentId positiveStrand negativeStrand : String) →
    (insertAt : Nat) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.birth eventId componentId positiveStrand negativeStrand insertAt) =
        Except.ok after) →
      BoundBirthEvent objectOf componentId
        positiveStrand negativeStrand before after
  death :
    (eventId componentId firstStrand secondStrand : String) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.death eventId componentId firstStrand secondStrand) =
        Except.ok after) →
      BoundDeathEvent objectOf componentId
        firstStrand secondStrand before after
  crossing :
    (eventId overStrand underStrand : String) →
    (sign : Presentation.CrossingSign) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.crossing eventId overStrand underStrand sign) =
        Except.ok after) →
      BoundCrossingEvent objectOf
        (crossingPrimitiveKind sign)
        overStrand underStrand before after
  coupon :
    (eventId couponId label : String) →
    (inputStrands : List String) →
    (outputStrands : List StrandState) →
    (replaceAt : Nat) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.coupon eventId couponId label
            inputStrands outputStrands replaceAt) =
        Except.ok after) →
      BoundCouponEvent objectOf couponId label
        inputStrands outputStrands before after
  framingTwist :
    (eventId strandId : String) →
    (sign : Presentation.CrossingSign) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.framingTwist eventId strandId sign) =
        Except.ok after) →
      WindowedFramingTwistEvent objectOf strandId before after
  planarIsotopy :
    (eventId : String) →
    (activeOrder : List String) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.planarIsotopy eventId activeOrder) =
        Except.ok after) →
      BoundPlanarIsotopyEvent objectOf activeOrder before after
  semanticsSchema : String
  semanticsSnapshotHash : String
  semantics_snapshot_hash_shape :
    RawPresentation.sha256Shape semanticsSnapshotHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace WindowedCategoricalEventSemantics

/--
Derive the old six-case compiler by exhaustive dispatch.

The boundary, framing twist, local contexts, and whole event diagrams are all
definitions; none remains a caller field.
-/
def toCategoricalEventCompiler
    {raw : RawPresentation}
    {objectOf : StrandState → C}
    {framingTwistData : NaturalTwist C}
    (semantics :
      WindowedCategoricalEventSemantics
        (C := C) raw objectOf framingTwistData) :
    CategoricalEventCompiler C raw where
  framingTwistData := framingTwistData
  boundary := boundaryWord objectOf
  empty_boundary_sound := rfl
  birth := fun eventId componentId positiveStrand negativeStrand
      insertAt before after step_sound =>
    (semantics.birth eventId componentId positiveStrand negativeStrand
      insertAt (before := before) (after := after) step_sound)
      |>.window.toCompiled
  death := fun eventId componentId firstStrand secondStrand
      before after step_sound =>
    (semantics.death eventId componentId firstStrand secondStrand
      (before := before) (after := after) step_sound)
      |>.window.toCompiled
  crossing := fun eventId overStrand underStrand sign
      before after step_sound =>
    (semantics.crossing eventId overStrand underStrand sign
      (before := before) (after := after) step_sound)
      |>.window.toCompiled
  coupon := fun eventId couponId label inputStrands outputStrands replaceAt
      before after step_sound =>
    (semantics.coupon eventId couponId label
      inputStrands outputStrands replaceAt
      (before := before) (after := after) step_sound)
      |>.window.toCompiled
  framingTwist := fun eventId strandId sign before after step_sound =>
    (semantics.framingTwist eventId strandId sign
      (before := before) (after := after) step_sound).toCompiled
      framingTwistData sign
  planarIsotopy := fun eventId activeOrder before after step_sound =>
    (semantics.planarIsotopy eventId activeOrder
      (before := before) (after := after) step_sound)
      |>.window.toCompiled
  compilerSchema :=
    "twisted-yetter.windowed-categorical-event-compiler.v1"
  compilerSnapshotHash := semantics.semanticsSnapshotHash
  compiler_snapshot_hash_shape := semantics.semantics_snapshot_hash_shape
  sourceRefs := semantics.sourceRefs
  exactScope := semantics.exactScope
  sourceScopeCaveat := semantics.sourceScopeCaveat

omit [Preadditive C] [MonoidalPreadditive C] in
theorem derived_boundary_is_boundaryWord
    {raw : RawPresentation}
    {objectOf : StrandState → C}
    {framingTwistData : NaturalTwist C}
    (semantics :
      WindowedCategoricalEventSemantics
        (C := C) raw objectOf framingTwistData) :
    semantics.toCategoricalEventCompiler.boundary =
      boundaryWord objectOf := by
  rfl

omit [Preadditive C] [MonoidalPreadditive C] in
theorem derived_twist_is_retained_twist
    {raw : RawPresentation}
    {objectOf : StrandState → C}
    {framingTwistData : NaturalTwist C}
    (semantics :
      WindowedCategoricalEventSemantics
        (C := C) raw objectOf framingTwistData) :
    semantics.toCategoricalEventCompiler.framingTwistData =
      framingTwistData := by
  rfl

end WindowedCategoricalEventSemantics

/--
A source-bound presentation compiler for one manifold and shared `H2` model.

The two certificate hashes cover the whole `H2`-indexed compiler family for
one presentation. The actual diagram and raw numerator are definitions below,
not fields that a caller may choose independently.
-/
structure SourceBoundPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2] where
  eventCompiler :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
      CategoricalEventCompiler C topology.formal.raw
  diagramCertificateHash :
    SpecialKirbyPresentation H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (decorationCertificateHash topology) = true
  sourceRefs : List String
  exactEventScope : String
  sourceScopeCaveat : String

namespace SourceBoundPresentationCompiler

/-- The closed diagram is definitionally compiled from the typed trace. -/
def compileDiagram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    Diagram C .unit .unit :=
  (compiler.eventCompiler topology alpha).compileClosed topology.execution

/--
Derive the R11 decorated presentation. Counts and raw scalarization are
definitionally fixed by the topology and compiled diagram.
-/
noncomputable def decorate
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData H2)
    (topology : SpecialKirbyPresentation H2) :
    DecoratedKirbyPresentation categoryData topology where
  diagram := compiler.compileDiagram topology
  evaluationState := fun alpha => {
    counts := topology.counts
    rawNumerator :=
      categoryData.closedScalar
        (Diagram.eval C (compiler.compileDiagram topology alpha))
  }
  counts_sound := fun _ => rfl
  raw_numerator_sound := fun _ => rfl
  compiledCategorySnapshotHash := categoryData.categorySnapshotHash
  category_snapshot_hash_sound := rfl
  compiledPresentationSnapshotHash := topology.formal.pinnedSourceHash
  presentation_snapshot_hash_sound := rfl
  compiledH2ModelCertificateHash := topology.h2ModelCertificateHash
  h2_model_certificate_hash_sound := rfl
  diagramCertificateHash := compiler.diagramCertificateHash topology
  diagram_certificate_hash_shape :=
    compiler.diagram_certificate_hash_shape topology
  decorationCertificateHash := compiler.decorationCertificateHash topology
  decoration_certificate_hash_shape :=
    compiler.decoration_certificate_hash_shape topology

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
theorem decorate_diagram_is_trace_compiled
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    (compiler.decorate topology).diagram alpha =
      compiler.compileDiagram topology alpha := by
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
theorem decorate_raw_numerator_is_compiled_scalar
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    ((compiler.decorate topology).evaluationState alpha).rawNumerator =
      categoryData.closedScalar
        (Diagram.eval C (compiler.compileDiagram topology alpha)) := by
  rfl

end SourceBoundPresentationCompiler

/--
A source-bound compiler for a genuine formal Kirby-colour expansion.

`Labeling topology alpha` is one *global* assignment for the complete
presentation.  The same assignment is passed to every event in the closed
execution trace.  This rules out the incorrect eventwise interpretation in
which one component could silently change its simple label between two
Morse slices.

The result is a finite linear combination of complete closed diagrams.  It is
collapsed to an ordinary unit endomorphism only after the whole trace for
every global labeling has been compiled.  Thus a formal Kirby colour is never
pretended to be one object of `C`.
-/
structure FiniteLabelPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2] where
  Labeling :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) → Type uS
  labelingFintype :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) → Fintype (Labeling topology alpha)
  weight :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) → Labeling topology alpha → K
  eventCompiler :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (labeling : Labeling topology alpha) →
      CategoricalEventCompiler C topology.formal.raw
  diagramCertificateHash :
    SpecialKirbyPresentation H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (decorationCertificateHash topology) = true
  labelExpansionCertificateHash :
    SpecialKirbyPresentation H2 → String
  label_expansion_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (labelExpansionCertificateHash topology) = true
  sourceRefs : List String
  exactEventScope : String
  exactLabelScope : String
  sourceScopeCaveat : String

namespace FiniteLabelPresentationCompiler

/-- The retained formal sum of globally and consistently labelled traces. -/
noncomputable def linearDiagram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    LinearDiagram (R := K) (C := C) .unit .unit := by
  letI := compiler.labelingFintype topology alpha
  exact LinearDiagram.weightedSum
    (compiler.weight topology alpha)
    (fun labeling =>
      (compiler.eventCompiler topology alpha labeling).compileClosed
        topology.execution)

/--
Collapse only after compiling each complete globally labelled trace.

The collapsed coupon is an API representation of the already formed linear
combination; it is not an object-level interpretation of a Kirby colour.
-/
noncomputable def compileDiagram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    Diagram C .unit .unit :=
  LinearDiagram.collapse
    (R := K) "global-finite-kirby-colour-expansion"
    (compiler.linearDiagram topology alpha)

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
@[simp]
theorem compileDiagram_eval
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    Diagram.eval C (compiler.compileDiagram topology alpha) =
      LinearDiagram.eval (R := K)
        (compiler.linearDiagram topology alpha) := by
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- Evaluation exposes the exact finite sum of complete trace evaluations. -/
theorem compileDiagram_eval_eq_global_weighted_sum
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    Diagram.eval C (compiler.compileDiagram topology alpha) =
      letI := compiler.labelingFintype topology alpha
      ∑ labeling,
        compiler.weight topology alpha labeling •
          Diagram.eval C
            ((compiler.eventCompiler topology alpha labeling).compileClosed
              topology.execution) := by
  rw [compiler.compileDiagram_eval]
  letI := compiler.labelingFintype topology alpha
  exact LinearDiagram.eval_weightedSum
    (compiler.weight topology alpha)
    (fun labeling =>
      (compiler.eventCompiler topology alpha labeling).compileClosed
        topology.execution)

/-- Derive the decorated presentation without a free whole-diagram field. -/
noncomputable def decorate
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2) :
    DecoratedKirbyPresentation categoryData topology where
  diagram := compiler.compileDiagram topology
  evaluationState := fun alpha => {
    counts := topology.counts
    rawNumerator :=
      categoryData.closedScalar
        (Diagram.eval C (compiler.compileDiagram topology alpha))
  }
  counts_sound := fun _ => rfl
  raw_numerator_sound := fun _ => rfl
  compiledCategorySnapshotHash := categoryData.categorySnapshotHash
  category_snapshot_hash_sound := rfl
  compiledPresentationSnapshotHash := topology.formal.pinnedSourceHash
  presentation_snapshot_hash_sound := rfl
  compiledH2ModelCertificateHash := topology.h2ModelCertificateHash
  h2_model_certificate_hash_sound := rfl
  diagramCertificateHash := compiler.diagramCertificateHash topology
  diagram_certificate_hash_shape :=
    compiler.diagram_certificate_hash_shape topology
  decorationCertificateHash := compiler.decorationCertificateHash topology
  decoration_certificate_hash_shape :=
    compiler.decoration_certificate_hash_shape topology

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
theorem decorate_diagram_is_global_label_expansion
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    (compiler.decorate topology).diagram alpha =
      compiler.compileDiagram topology alpha := by
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
theorem decorate_raw_numerator_is_global_label_scalar
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    ((compiler.decorate topology).evaluationState alpha).rawNumerator =
      categoryData.closedScalar
        (Diagram.eval C (compiler.compileDiagram topology alpha)) := by
  rfl

end FiniteLabelPresentationCompiler

/--
Componentwise data from which the global finite labeling is derived.

Every component has its own finite label fiber.  The component weight may
depend on the presentation and marked class, but the global weight is not a
field: it is the product of all recorded component weights.
-/
structure ComponentLabelExpansion
    (S : Type uS)
    (H2 : Type uH) [AddCommGroup H2] where
  Label : ComponentSpec → Type uS
  labelFintype : (component : ComponentSpec) → Fintype (Label component)
  componentWeight :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (component : ComponentSpec) → Label component → K
  expansionSchema : String
  expansionSnapshotHash : String
  expansion_snapshot_hash_shape :
    RawPresentation.sha256Shape expansionSnapshotHash = true
  sourceRefs : List String
  exactComponentScope : String
  sourceScopeCaveat : String

namespace ComponentLabelExpansion

/-- One label for every component, indexed by its immutable list position. -/
abbrev GlobalLabeling
    {H2 : Type uH} [AddCommGroup H2]
    (expansion : ComponentLabelExpansion (K := K) (S := S) H2)
    (topology : SpecialKirbyPresentation H2) :=
  (index : Fin topology.formal.raw.components.length) →
    expansion.Label (topology.formal.raw.components.get index)

/-- Finiteness is derived component-by-component. -/
@[implicit_reducible]
noncomputable def globalFintype
    {H2 : Type uH} [AddCommGroup H2]
    (expansion : ComponentLabelExpansion (K := K) (S := S) H2)
    (topology : SpecialKirbyPresentation H2) :
    Fintype (expansion.GlobalLabeling topology) := by
  letI (index : Fin topology.formal.raw.components.length) :=
    expansion.labelFintype (topology.formal.raw.components.get index)
  infer_instance

/-- The global Kirby-colour coefficient is the product of component weights. -/
noncomputable def globalWeight
    {H2 : Type uH} [AddCommGroup H2]
    (expansion : ComponentLabelExpansion (K := K) (S := S) H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2)
    (labeling : expansion.GlobalLabeling topology) : K :=
  ∏ index : Fin topology.formal.raw.components.length,
    expansion.componentWeight topology alpha
      (topology.formal.raw.components.get index) (labeling index)

end ComponentLabelExpansion

/--
The intended presentation compiler boundary for a formal Kirby-coloured link.

The caller supplies only component fibers/weights and a trace compiler for one
complete global assignment.  `toFiniteLabel` derives both the assignment type
and the total coefficient; neither can be replaced by an unrelated finite
index set or handwritten whole-link weight.
-/
structure ComponentwiseFiniteLabelPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2] where
  expansion : ComponentLabelExpansion (K := K) (S := S) H2
  eventCompiler :
    (topology : SpecialKirbyPresentation H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling expansion topology) →
      CategoricalEventCompiler C topology.formal.raw
  diagramCertificateHash :
    SpecialKirbyPresentation H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation H2) →
      RawPresentation.sha256Shape
        (decorationCertificateHash topology) = true
  sourceRefs : List String
  exactEventScope : String
  sourceScopeCaveat : String

namespace ComponentwiseFiniteLabelPresentationCompiler

/-- Forget no semantics: derive the generic global-label compiler exactly. -/
noncomputable def toFiniteLabel
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData H2) :
    FiniteLabelPresentationCompiler categoryData H2 where
  Labeling := fun topology _ =>
    compiler.expansion.GlobalLabeling topology
  labelingFintype := fun topology _ =>
    compiler.expansion.globalFintype topology
  weight := fun topology alpha labeling =>
    compiler.expansion.globalWeight topology alpha labeling
  eventCompiler := compiler.eventCompiler
  diagramCertificateHash := compiler.diagramCertificateHash
  diagram_certificate_hash_shape :=
    compiler.diagram_certificate_hash_shape
  decorationCertificateHash := compiler.decorationCertificateHash
  decoration_certificate_hash_shape :=
    compiler.decoration_certificate_hash_shape
  labelExpansionCertificateHash := fun _ =>
    compiler.expansion.expansionSnapshotHash
  label_expansion_certificate_hash_shape := fun _ =>
    compiler.expansion.expansion_snapshot_hash_shape
  sourceRefs := compiler.sourceRefs ++ compiler.expansion.sourceRefs
  exactEventScope := compiler.exactEventScope
  exactLabelScope := compiler.expansion.exactComponentScope
  sourceScopeCaveat :=
    compiler.sourceScopeCaveat ++ " " ++
      compiler.expansion.sourceScopeCaveat

/-- The retained whole-link formal sum for the componentwise expansion. -/
noncomputable def linearDiagram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  compiler.toFiniteLabel.linearDiagram topology alpha

/-- The API diagram is the collapse of the retained componentwise sum. -/
noncomputable def compileDiagram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    Diagram C .unit .unit :=
  compiler.toFiniteLabel.compileDiagram topology alpha

/-- Derive the R11 decoration from the componentwise global expansion. -/
noncomputable def decorate
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2) :
    DecoratedKirbyPresentation categoryData topology :=
  compiler.toFiniteLabel.decorate topology

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The final scalar is visibly the componentwise global weighted sum. -/
theorem compileDiagram_eval_eq_componentwise_sum
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2)
    (alpha : H2) :
    Diagram.eval C (compiler.compileDiagram topology alpha) =
      letI := compiler.expansion.globalFintype topology
      ∑ labeling,
        compiler.expansion.globalWeight topology alpha labeling •
          Diagram.eval C
            ((compiler.eventCompiler topology alpha labeling).compileClosed
              topology.execution) :=
  compiler.toFiniteLabel.compileDiagram_eval_eq_global_weighted_sum
    topology alpha

end ComponentwiseFiniteLabelPresentationCompiler

/--
Closed whitelist of source-bound presentation compiler mechanisms.

The second constructor is the only admitted route for a formal Kirby-colour
sum.  In particular, there is no constructor from an arbitrary
`SpecialKirbyPresentation → H2 → Diagram`.
-/
inductive AdmittedSourceBoundPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2]
  | singleLabel
      (compiler :
        SourceBoundPresentationCompiler categoryData H2) :
      AdmittedSourceBoundPresentationCompiler
        categoryData H2
  | finiteGlobalLabel
      (compiler :
        FiniteLabelPresentationCompiler
          categoryData H2) :
      AdmittedSourceBoundPresentationCompiler
        categoryData H2

namespace AdmittedSourceBoundPresentationCompiler

/-- Evaluate only through one of the two closed source-bound mechanisms. -/
noncomputable def decorate
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      AdmittedSourceBoundPresentationCompiler
        categoryData H2)
    (topology : SpecialKirbyPresentation H2) :
    DecoratedKirbyPresentation categoryData topology :=
  match compiler with
  | .singleLabel compiler =>
      compiler.decorate topology
  | .finiteGlobalLabel compiler =>
      compiler.decorate topology

end AdmittedSourceBoundPresentationCompiler

end TwistedYetter.Kirby.CategoricalPresentationCompiler
