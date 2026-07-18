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
  | birthRight (object : C) [HasRightDual object] :
      PrimitiveEventDiagram C .birth .unit
        (.tensor (.atom object) (.atom objectᘁ))
  | birthLeft (object : C) [HasLeftDual object] :
      PrimitiveEventDiagram C .birth .unit
        (.tensor (.atom (ᘁobject)) (.atom object))
  | deathRight (object : C) [HasRightDual object] :
      PrimitiveEventDiagram C .death
        (.tensor (.atom objectᘁ) (.atom object)) .unit
  | deathLeft (object : C) [HasLeftDual object] :
      PrimitiveEventDiagram C .death
        (.tensor (.atom object) (.atom (ᘁobject))) .unit
  | crossingPositive (left right : Boundary C) :
      PrimitiveEventDiagram C .crossingPositive
        (.tensor left right) (.tensor right left)
  | crossingNegative (left right : Boundary C) :
      PrimitiveEventDiagram C .crossingNegative
        (.tensor left right) (.tensor right left)
  | coupon
      {source target : Boundary C}
      (name : String)
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
  | birthRight object =>
      exact Diagram.cup object
  | birthLeft object =>
      exact Diagram.leftCup object
  | deathRight object =>
      exact Diagram.cap object
  | deathLeft object =>
      exact Diagram.leftCap object
  | crossingPositive left right =>
      exact Diagram.crossing left right
  | crossingNegative left right =>
      exact Diagram.crossingInv left right
  | coupon name morphism =>
      exact Diagram.coupon name morphism
  | twistPositive twist object =>
      exact atomicCoupon
        "positive-framing-twist" (twist.iso.hom.app object)
  | twistNegative twist object =>
      exact atomicCoupon
        "negative-framing-twist" (twist.iso.inv.app object)
  | planarIdentity =>
      exact Diagram.identity _

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
One local categorical compiler for every raw slice-event constructor.

The result boundary is indexed by the exact before/after states accepted by
`RawPresentation.applyEvent`. A caller cannot omit a constructor or compile
an event against unrelated slice states.
-/
structure CategoricalEventCompiler
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C]
    [BraidedCategory C]
    (raw : RawPresentation) where
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
    (strands : List String) →
    {before after : List StrandState} →
    (step_sound :
      raw.applyEvent before
          (.coupon eventId couponId label strands) =
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
      CompiledCategoricalEvent C (twistPrimitiveKind sign)
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
  | .coupon eventId couponId label strands =>
      (compiler.coupon eventId couponId label strands step_sound).diagram
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
A source-bound presentation compiler for one manifold and shared `H2` model.

The two certificate hashes cover the whole `H2`-indexed compiler family for
one presentation. The actual diagram and raw numerator are definitions below,
not fields that a caller may choose independently.
-/
structure SourceBoundPresentationCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  eventCompiler :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
      CategoricalEventCompiler C topology.formal.raw
  diagramCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2) :
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    (compiler.decorate topology).diagram alpha =
      compiler.compileDiagram topology alpha := by
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
theorem decorate_raw_numerator_is_compiled_scalar
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      SourceBoundPresentationCompiler categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  Labeling :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) → Type uS
  labelingFintype :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) → Fintype (Labeling topology alpha)
  weight :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) → Labeling topology alpha → K
  eventCompiler :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
    (labeling : Labeling topology alpha) →
      CategoricalEventCompiler C topology.formal.raw
  diagramCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
      RawPresentation.sha256Shape
        (decorationCertificateHash topology) = true
  labelExpansionCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  label_expansion_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2) :
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    (compiler.decorate topology).diagram alpha =
      compiler.compileDiagram topology alpha := by
  rfl

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
theorem decorate_raw_numerator_is_global_label_scalar
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      FiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  Label : ComponentSpec → Type uS
  labelFintype : (component : ComponentSpec) → Fintype (Label component)
  componentWeight :
    (topology : SpecialKirbyPresentation manifold H2) →
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (expansion : ComponentLabelExpansion (K := K) (S := S) manifold H2)
    (topology : SpecialKirbyPresentation manifold H2) :=
  (index : Fin topology.formal.raw.components.length) →
    expansion.Label (topology.formal.raw.components.get index)

/-- Finiteness is derived component-by-component. -/
@[implicit_reducible]
noncomputable def globalFintype
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (expansion : ComponentLabelExpansion (K := K) (S := S) manifold H2)
    (topology : SpecialKirbyPresentation manifold H2) :
    Fintype (expansion.GlobalLabeling topology) := by
  letI (index : Fin topology.formal.raw.components.length) :=
    expansion.labelFintype (topology.formal.raw.components.get index)
  infer_instance

/-- The global Kirby-colour coefficient is the product of component weights. -/
noncomputable def globalWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (expansion : ComponentLabelExpansion (K := K) (S := S) manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  expansion : ComponentLabelExpansion (K := K) (S := S) manifold H2
  eventCompiler :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
    (labeling :
      ComponentLabelExpansion.GlobalLabeling expansion topology) →
      CategoricalEventCompiler C topology.formal.raw
  diagramCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  decorationCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  decoration_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2) :
    FiniteLabelPresentationCompiler categoryData manifold H2 where
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
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  compiler.toFiniteLabel.linearDiagram topology alpha

/-- The API diagram is the collapse of the retained componentwise sum. -/
noncomputable def compileDiagram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    Diagram C .unit .unit :=
  compiler.toFiniteLabel.compileDiagram topology alpha

/-- Derive the R11 decoration from the componentwise global expansion. -/
noncomputable def decorate
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2) :
    DecoratedKirbyPresentation categoryData topology :=
  compiler.toFiniteLabel.decorate topology

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/-- The final scalar is visibly the componentwise global weighted sum. -/
theorem compileDiagram_eval_eq_componentwise_sum
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
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
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
  | singleLabel
      (compiler :
        SourceBoundPresentationCompiler categoryData manifold H2) :
      AdmittedSourceBoundPresentationCompiler
        categoryData manifold H2
  | finiteGlobalLabel
      (compiler :
        FiniteLabelPresentationCompiler
          categoryData manifold H2) :
      AdmittedSourceBoundPresentationCompiler
        categoryData manifold H2

namespace AdmittedSourceBoundPresentationCompiler

/-- Evaluate only through one of the two closed source-bound mechanisms. -/
noncomputable def decorate
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      AdmittedSourceBoundPresentationCompiler
        categoryData manifold H2)
    (topology : SpecialKirbyPresentation manifold H2) :
    DecoratedKirbyPresentation categoryData topology :=
  match compiler with
  | .singleLabel compiler =>
      compiler.decorate topology
  | .finiteGlobalLabel compiler =>
      compiler.decorate topology

end AdmittedSourceBoundPresentationCompiler

end TwistedYetter.Kirby.CategoricalPresentationCompiler
