import TwistedYetter.Kirby.Final.Semantics.Independent.KirbyDiagram

/-!
# Independent semantics: cut-open graphical presentations

This file contains the graphical state obtained after cutting the dotted
components of a fixed `SpecialKirbyDiagram`.  These intermediate tangles are
not themselves Kirby diagrams.
-/

namespace TwistedYetter.Semantics.Independent

inductive PunctureDirection
  | withDiskOrientation
  | againstDiskOrientation
  deriving DecidableEq, Repr

/--
Which side of the local dotted-handle morphism contains one incidence.

This is domain/codomain variance only.  It does not choose `X` versus `X*`
and it does not create a character exponent.
-/
inductive DottedIncidenceSide
  | inbound
  | outbound
  deriving DecidableEq, Repr

/--
The fixed oriented-boundary convention.  A single positive-incidence model
calibrates `withDiskOrientation` as an outgoing local boundary occurrence.
-/
def PunctureDirection.incidenceSide :
    PunctureDirection → DottedIncidenceSide
  | .withDiskOrientation => .outbound
  | .againstDiskOrientation => .inbound

structure DottedPuncture (trace : CombinatorialLinkTrace) where
  dottedComponent : trace.ComponentId
  twoHandleComponent : trace.ComponentId
  inputStrand : trace.StrandId
  outputStrand : trace.StrandId
  direction : PunctureDirection
  cutPosition : ℕ
  dotted_role :
    (trace.components dottedComponent).role = .dotted
  two_handle_role :
    (trace.components twoHandleComponent).role ≠ .dotted
  input_on_two_handle :
    (trace.strands inputStrand).component = twoHandleComponent
  output_on_two_handle :
    (trace.strands outputStrand).component = twoHandleComponent
  orientation_preserved :
    (trace.strands inputStrand).orientation =
      (trace.strands outputStrand).orientation

/-- Preserve the recorded order while selecting inbound incidences. -/
def dottedInboundPunctures
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace)) :
    List (DottedPuncture trace) :=
  punctures.filter fun puncture =>
    puncture.direction.incidenceSide = .inbound

/-- Preserve the recorded order while selecting outbound incidences. -/
def dottedOutboundPunctures
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace)) :
    List (DottedPuncture trace) :=
  punctures.filter fun puncture =>
    puncture.direction.incidenceSide = .outbound

/-- Exact local source ports for the dotted-handle incidence morphism. -/
def dottedInboundStrandWord
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace)) :
    List trace.StrandId :=
  (dottedInboundPunctures punctures).map DottedPuncture.inputStrand

/-- Exact local target ports for the dotted-handle incidence morphism. -/
def dottedOutboundStrandWord
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace)) :
    List trace.StrandId :=
  (dottedOutboundPunctures punctures).map DottedPuncture.outputStrand

/--
The ordinary-component word underlying the local source.  It deliberately
forgets strand orientation: component labels are assigned before cutting and
are not changed by the dotted disk.
-/
def dottedInboundComponentWord
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace)) :
    List trace.ComponentId :=
  (dottedInboundPunctures punctures).map DottedPuncture.twoHandleComponent

/--
The ordinary-component word underlying the local target.  As on the source,
no `X`/`X*` choice is read from the dotted-disk direction.
-/
def dottedOutboundComponentWord
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace)) :
    List trace.ComponentId :=
  (dottedOutboundPunctures punctures).map DottedPuncture.twoHandleComponent

/--
The category-neutral event language of the tangle obtained after cutting all
dotted spanning disks simultaneously.

A `projectorHole` is not a category morphism.  It marks the all-strand
projector waist inside a larger local movie.  It is not itself the
inbound/outbound boundary used by homology representative independence; that
boundary is defined separately by `dottedInboundStrandWord` and
`dottedOutboundStrandWord`.  This syntax contains neither a Kirby colour nor
an evaluation equality.
-/
inductive CutOpenEvent (trace : CombinatorialLinkTrace)
  | birth (leftOutput rightOutput : trace.StrandId)
  | death (leftInput rightInput : trace.StrandId)
  | crossing
      (overInput underInput overOutput underOutput : trace.StrandId)
      (sign : CrossingSign)
  | framingTwist
      (input output : trace.StrandId)
      (sign : CrossingSign)
  | planarIsotopy
      (continuations : List (trace.StrandId × trace.StrandId))
  | projectorHole
      (dottedComponent : trace.ComponentId)
      (punctures : List (DottedPuncture trace))

def CutOpenEvent.beforeWord
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List trace.StrandId
  | .birth _ _ => []
  | .death left right => [left, right]
  | .crossing overInput underInput _ _ _ => [overInput, underInput]
  | .framingTwist input _ _ => [input]
  | .planarIsotopy continuations => continuations.map Prod.fst
  | .projectorHole _ punctures => punctures.map DottedPuncture.inputStrand

def CutOpenEvent.afterWord
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List trace.StrandId
  | .birth left right => [left, right]
  | .death _ _ => []
  | .crossing _ _ overOutput underOutput _ => [underOutput, overOutput]
  | .framingTwist _ output _ => [output]
  | .planarIsotopy continuations => continuations.map Prod.snd
  | .projectorHole _ punctures => punctures.map DottedPuncture.outputStrand

def CutOpenEvent.continuationPairs
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → List (trace.StrandId × trace.StrandId)
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
  | .projectorHole _ punctures =>
      punctures.map fun puncture =>
        (puncture.inputStrand, puncture.outputStrand)

/--
The category-neutral dual-pairing condition at a cup or cap.

Both strands belong to the same framed component, so every component labeling
assigns them the same simple object.  Their opposite orientations then make
one strand the chosen dual of the other.  This is exactly the information
needed later to interpret a birth or death as coevaluation or evaluation.
-/
def CutOpenEvent.StrandContinuationsAreWellFormed
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
  | .crossing overInput underInput overOutput underOutput _ =>
      (trace.strands overInput).component =
          (trace.strands overOutput).component ∧
        (trace.strands overInput).orientation =
          (trace.strands overOutput).orientation ∧
        (trace.strands underInput).component =
          (trace.strands underOutput).component ∧
        (trace.strands underInput).orientation =
          (trace.strands underOutput).orientation
  | .framingTwist input output _ =>
      (trace.strands input).component =
          (trace.strands output).component ∧
        (trace.strands input).orientation =
          (trace.strands output).orientation
  | .planarIsotopy continuations =>
      ∀ pair ∈ continuations,
        (trace.strands pair.1).component =
            (trace.strands pair.2).component ∧
          (trace.strands pair.1).orientation =
            (trace.strands pair.2).orientation
  | .projectorHole _ punctures =>
      ∀ puncture ∈ punctures,
        (trace.strands puncture.inputStrand).component =
            (trace.strands puncture.outputStrand).component ∧
          (trace.strands puncture.inputStrand).orientation =
            (trace.strands puncture.outputStrand).orientation

def CutOpenEventTransition
    {trace : CombinatorialLinkTrace}
    (event : CutOpenEvent trace)
    (before after : List trace.StrandId) : Prop :=
  ∃ (leftContext rightContext : List trace.StrandId),
    before = leftContext ++ event.beforeWord ++ rightContext ∧
    after = leftContext ++ event.afterWord ++ rightContext

/--
The events allowed while putting a punctured dotted collar into standard
normal form.  The projector itself is deliberately excluded: these events
only bend and transport the original strands to and from the projector waist.
-/
def CutOpenEvent.IsDottedCollarBending
    {trace : CombinatorialLinkTrace} :
    CutOpenEvent trace → Prop
  | .projectorHole _ _ => False
  | _ => True

/--
A finite, category-neutral bending path between two exact strand words.

All correctness fields are transparent combinatorial propositions.  In
particular, this structure contains no category, object label, character,
projector, morphism, or evaluation equality.
-/
structure DottedCollarBendingPath
    (trace : CombinatorialLinkTrace)
    (source target : List trace.StrandId) where
  eventCount : ℕ
  events : Fin eventCount → CutOpenEvent trace
  activeOrder : Fin (eventCount + 1) → List trace.StrandId

/-- All combinatorial correctness conditions for one collar bending path. -/
def DottedCollarBendingPath.FollowsExactBendingTransitions
    {trace : CombinatorialLinkTrace}
    {source target : List trace.StrandId}
    (path : DottedCollarBendingPath trace source target) : Prop :=
  path.activeOrder 0 = source ∧
    path.activeOrder (Fin.last path.eventCount) = target ∧
    (∀ i : Fin path.eventCount,
      CutOpenEventTransition (path.events i)
        (path.activeOrder i.castSucc)
        (path.activeOrder i.succ)) ∧
    (∀ i : Fin path.eventCount,
      (path.events i).StrandContinuationsAreWellFormed) ∧
    (∀ i : Fin path.eventCount,
      (path.events i).IsDottedCollarBending)

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
  strandContinuationsAreWellFormed :
    ∀ i : Fin eventCount,
      (events i).StrandContinuationsAreWellFormed
  eventPortsAreDistinct :
    ∀ i, ((events i).beforeWord ++ (events i).afterWord).Nodup
  everyStrandHasUniqueInputAndOutput :
    ∀ strand,
      (∃! i : Fin eventCount, strand ∈ (events i).beforeWord) ∧
        (∃! i : Fin eventCount, strand ∈ (events i).afterWord)
  activeWordsNoDuplicates :
    ∀ i, (activeOrder i).Nodup
  activeStrandsAreTwoHandles :
    ∀ (i : Fin (eventCount + 1)) (strand : trace.StrandId),
      strand ∈ activeOrder i →
      (trace.components (trace.strands strand).component).role ≠ .dotted

/-
The cut-open trace is the unique source of puncture words.  In particular,
`DottedCutData` does not store a second puncture-word table that could drift
away from the projector events compiled by the evaluator.

The remaining fields are transparent finite correctness conditions on that
single trace.  They certify that every dotted component has one distinguished
projector event, that no extra projector event exists, and that the punctures
inside the distinguished event carry the expected dotted component and list
position.  They contain no topology realization, category, character, or
evaluation equality.
-/
structure DottedCutData (trace : CombinatorialLinkTrace) where
  exterior : CutOpenExteriorTrace trace
  projectorEventIndex :
    (dotted : trace.ComponentId) →
      (trace.components dotted).role = .dotted →
      Fin exterior.eventCount
  projectorEvent_is_for :
    ∀ (dotted : trace.ComponentId)
      (role : (trace.components dotted).role = .dotted),
      ∃ punctures : List (DottedPuncture trace),
        exterior.events (projectorEventIndex dotted role) =
          .projectorHole dotted punctures
  everyProjectorEvent_is_indexed :
    ∀ (i : Fin exterior.eventCount)
      (dotted : trace.ComponentId)
      (punctures : List (DottedPuncture trace)),
      exterior.events i = .projectorHole dotted punctures →
        ∃ role : (trace.components dotted).role = .dotted,
          i = projectorEventIndex dotted role
  projectorPunctures_are_indexed :
    ∀ (dotted : trace.ComponentId)
      (role : (trace.components dotted).role = .dotted)
      (punctures : List (DottedPuncture trace)),
      exterior.events (projectorEventIndex dotted role) =
          .projectorHole dotted punctures →
        ∀ index : Fin punctures.length,
          let puncture := punctures.get index
          puncture.dottedComponent = dotted ∧
            puncture.cutPosition = index.1

/--
The ordered puncture word of a dotted component, read from its distinguished
projector event.  This is a definition from the unique cut-open trace, not a
second caller-supplied table.
-/
noncomputable def DottedCutData.punctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted) :
    List (DottedPuncture trace) :=
  match cut.exterior.events (cut.projectorEventIndex dotted role) with
  | .projectorHole _ punctures => punctures
  | _ => []

/-- The distinguished event contains the puncture word derived from it. -/
theorem DottedCutData.projectorEvent_eq
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted) :
    cut.exterior.events (cut.projectorEventIndex dotted role) =
      .projectorHole dotted (cut.punctureWord dotted role) := by
  obtain ⟨punctures, event_eq⟩ := cut.projectorEvent_is_for dotted role
  simpa [DottedCutData.punctureWord, event_eq] using event_eq

/--
The signed output-minus-input incidence of one ordinary component in one
ordered dotted puncture word.  This is purely combinatorial cut-open data.
-/
noncomputable def dottedCutBoundaryCoefficient
    {trace : CombinatorialLinkTrace}
    (punctures : List (DottedPuncture trace))
    (twoHandle : trace.ComponentId) : ℤ := by
  classical
  exact
    punctures.foldl
      (fun total puncture =>
        if puncture.twoHandleComponent = twoHandle then
          match puncture.direction.incidenceSide with
          | .inbound => total - 1
          | .outbound => total + 1
        else
          total)
      0

/--
The list order is the recorded left-to-right puncture order.  This predicate
checks that every occurrence names the correct dotted component and that its
redundant `cutPosition` agrees with its list index.
-/
def DottedCutData.PunctureWordsRespectRecordedOrder
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  ∀ (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted)
    (index : Fin (cut.punctureWord dotted role).length),
      let puncture := (cut.punctureWord dotted role).get index
      puncture.dottedComponent = dotted ∧
        puncture.cutPosition = index.1

/-- Every literal dotted component has exactly one event using its exact word. -/
def DottedCutData.EveryDottedComponentHasUniqueProjectorEvent
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  ∀ (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted),
      ∃! i : Fin cut.exterior.eventCount,
        cut.exterior.events i =
          .projectorHole dotted (cut.punctureWord dotted role)

/-- Every projector event comes from a dotted component and its exact word. -/
def DottedCutData.EveryProjectorEventUsesExactPunctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  ∀ (i : Fin cut.exterior.eventCount)
    (dotted : trace.ComponentId)
    (punctures : List (DottedPuncture trace)),
      cut.exterior.events i = .projectorHole dotted punctures →
        ∃ role : (trace.components dotted).role = .dotted,
          punctures = cut.punctureWord dotted role

/--
At a projector event, the puncture list occurs in its recorded order as one
contiguous block in the complete left-to-right active order, both before and
after the event.
-/
def DottedCutData.ProjectorPortsOccurInRecordedOrder
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  ∀ (i : Fin cut.exterior.eventCount)
    (dotted : trace.ComponentId)
    (punctures : List (DottedPuncture trace)),
      cut.exterior.events i = .projectorHole dotted punctures →
        ∃ (leftBefore rightBefore leftAfter rightAfter : List trace.StrandId),
          cut.exterior.activeOrder i.castSucc =
              leftBefore ++ punctures.map DottedPuncture.inputStrand ++
                rightBefore ∧
            cut.exterior.activeOrder i.succ =
              leftAfter ++ punctures.map DottedPuncture.outputStrand ++
                rightAfter

/--
At a projector event, the strands outside the ordered puncture block are the
same on both sides.  Only the puncture block changes from input ports to output
ports.
-/
def DottedCutData.ProjectorExteriorContextIsUnchanged
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  ∀ (i : Fin cut.exterior.eventCount)
    (dotted : trace.ComponentId)
    (punctures : List (DottedPuncture trace)),
      cut.exterior.events i = .projectorHole dotted punctures →
        ∃ (leftContext rightContext : List trace.StrandId),
          cut.exterior.activeOrder i.castSucc =
              leftContext ++ punctures.map DottedPuncture.inputStrand ++
                rightContext ∧
            cut.exterior.activeOrder i.succ =
              leftContext ++ punctures.map DottedPuncture.outputStrand ++
                rightContext

/--
Every projector marker in the cut-open trace is exactly the unique marker of
one literal dotted component, and every puncture word follows its recorded
order.  Thus no ordinary component creates a marker and no additional marker
is present.

This is a transparent combinatorial proposition.  It contains no category,
projector morphism, character, or evaluation equality.
-/
def DottedCutData.ProjectorEventsExactlyMatchDottedComponents
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) : Prop :=
  cut.PunctureWordsRespectRecordedOrder ∧
    cut.EveryDottedComponentHasUniqueProjectorEvent ∧
      cut.EveryProjectorEventUsesExactPunctureWord

/-- The derived puncture words carry their intrinsic dotted component and list order. -/
theorem DottedCutData.punctureWordsRespectRecordedOrder
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) :
    cut.PunctureWordsRespectRecordedOrder := by
  intro dotted role index
  obtain ⟨punctures, event_eq⟩ := cut.projectorEvent_is_for dotted role
  simpa [DottedCutData.punctureWord, event_eq] using
    cut.projectorPunctures_are_indexed dotted role punctures event_eq
      (Fin.cast (by simp [DottedCutData.punctureWord, event_eq]) index)

/-- Every dotted component has exactly its distinguished projector event. -/
theorem DottedCutData.everyDottedComponentHasUniqueProjectorEvent
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) :
    cut.EveryDottedComponentHasUniqueProjectorEvent := by
  intro dotted role
  refine ⟨cut.projectorEventIndex dotted role,
    cut.projectorEvent_eq dotted role, ?_⟩
  intro index event_eq
  obtain ⟨otherRole, index_eq⟩ :=
    cut.everyProjectorEvent_is_indexed index dotted
      (cut.punctureWord dotted role) event_eq
  calc
    index = cut.projectorEventIndex dotted otherRole := index_eq
    _ = cut.projectorEventIndex dotted role := by
      rw [Subsingleton.elim otherRole role]

/-- Every projector event is the distinguished event of its dotted component. -/
theorem DottedCutData.everyProjectorEventUsesExactPunctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) :
    cut.EveryProjectorEventUsesExactPunctureWord := by
  intro index dotted punctures event_eq
  obtain ⟨role, index_eq⟩ :=
    cut.everyProjectorEvent_is_indexed index dotted punctures event_eq
  refine ⟨role, ?_⟩
  have canonical := cut.projectorEvent_eq dotted role
  rw [← index_eq] at canonical
  have constructors_eq :
      (.projectorHole dotted punctures : CutOpenEvent trace) =
        .projectorHole dotted (cut.punctureWord dotted role) :=
    event_eq.symm.trans canonical
  injection constructors_eq

/--
Projector completeness is now a theorem of the single-source cut-open data;
no external axiom synchronizes two independently supplied puncture tables.
-/
theorem DottedCutData.projectorEventsExactlyMatchDottedComponents
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) :
    cut.ProjectorEventsExactlyMatchDottedComponents :=
  ⟨cut.punctureWordsRespectRecordedOrder,
    cut.everyDottedComponentHasUniqueProjectorEvent,
    cut.everyProjectorEventUsesExactPunctureWord⟩

/-- The complete active-order transition derives ordered projector ports. -/
theorem DottedCutData.projectorPortsOccurInRecordedOrder
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) :
    cut.ProjectorPortsOccurInRecordedOrder := by
  intro i dotted punctures event_eq
  obtain ⟨leftContext, rightContext, before_eq, after_eq⟩ :=
    cut.exterior.transitionValid i
  rw [event_eq] at before_eq after_eq
  exact ⟨leftContext, rightContext, leftContext, rightContext,
    before_eq, after_eq⟩

/-- The complete active-order transition keeps the exterior context fixed. -/
theorem DottedCutData.projectorExteriorContextIsUnchanged
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace) :
    cut.ProjectorExteriorContextIsUnchanged := by
  intro i dotted punctures event_eq
  obtain ⟨leftContext, rightContext, before_eq, after_eq⟩ :=
    cut.exterior.transitionValid i
  rw [event_eq] at before_eq after_eq
  exact ⟨leftContext, rightContext, before_eq, after_eq⟩

/--
The exact puncture word at any projector marker, derived directly from the
explicit projector-event completeness boundary.
-/
theorem DottedCutData.projectorEvent_hasExactPunctureWord
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (complete : cut.ProjectorEventsExactlyMatchDottedComponents)
    (i : Fin cut.exterior.eventCount)
    (dotted : trace.ComponentId)
    (punctures : List (DottedPuncture trace))
    (event_eq : cut.exterior.events i = .projectorHole dotted punctures) :
    ∃ role : (trace.components dotted).role = .dotted,
      punctures = cut.punctureWord dotted role :=
  complete.2.2 i dotted punctures event_eq

theorem DottedCutData.puncture_dottedComponent_eq
    {trace : CombinatorialLinkTrace}
    (cut : DottedCutData trace)
    (complete : cut.ProjectorEventsExactlyMatchDottedComponents)
    (dotted : trace.ComponentId)
    (role : (trace.components dotted).role = .dotted)
    (puncture : DottedPuncture trace)
    (puncture_mem : puncture ∈ cut.punctureWord dotted role) :
    puncture.dottedComponent = dotted := by
  obtain ⟨index, index_eq⟩ := List.mem_iff_get.mp puncture_mem
  rw [← index_eq]
  exact (complete.1 dotted role index).1

/--
The second semantic layer: a simultaneous cut-open presentation of one fixed
closed special Kirby diagram.  It is not itself another Kirby diagram.
-/
structure DottedCutPresentation (diagram : SpecialKirbyDiagram) where
  cut : DottedCutData diagram.trace
  incidence_agrees_with_handle_boundary :
    ∀ (one : Fin diagram.handles.hOne)
      (two : Fin diagram.handles.hTwo),
      diagram.handles.boundaryTwo
          (fun coordinate => if coordinate = two then 1 else 0) one =
        dottedCutBoundaryCoefficient
          (cut.punctureWord
            (diagram.handles.oneHandleIndex one).1
            (diagram.handles.oneHandleIndex one).2)
          (diagram.handles.twoHandleIndex two).1

/-- Backwards-facing theorem name for the former external completeness axiom. -/
theorem standardDottedProjectorEventCompleteness
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram) :
    presentation.cut.ProjectorEventsExactlyMatchDottedComponents :=
  presentation.cut.projectorEventsExactlyMatchDottedComponents

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 881
