import TwistedYetter.Kirby.CanonicalCancellationRibbonMovies
import TwistedYetter.Kirby.CanonicalMoveGeometry

/-!
# Exact cancellation-script bindings

This module binds the finite event scripts retained by cancellation
`GraphicalEditProgram`s to the exact three-way splits of the admitted
canonical source and target traces.

Every theorem below is an equality/type transport over serialized lists.  No
ambient isotopy, category, evaluator, scalar equality, or topology theorem is
assumed.
-/

namespace TwistedYetter.Kirby.CanonicalCancellationTraceBinding

open TwistedYetter.Kirby.CanonicalKirbyTrace
open TwistedYetter.Kirby.CanonicalMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalTraceLocality
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uH

/-- Exact trace binding for creation of a cancelling one--two pair. -/
structure OneTwoBirthBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology) where
  script :
    OneTwoCancellationScript
      (HandleEdit.oneTwoBirthDottedId metadata.recipe.handleEdit)
      (HandleEdit.oneTwoBirthTwoHandleId metadata.recipe.handleEdit)
  sourceSplit :
    Trace.ThreeWaySplit
      (raw := source.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.identityEvents
      metadata.recipe.window.commonEventSuffix
  targetSplit :
    Trace.ThreeWaySplit
      (raw := target.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.hopfEvents
      metadata.recipe.window.commonEventSuffix

/-- Build the one--two birth binding from executable recipe equalities. -/
def oneTwoBirthBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.topology target.topology) :
    OneTwoBirthBinding source target metadata := by
  let script :=
    GraphicalEditProgram.oneTwoBirthScriptOfEdit
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
  let split :=
    SourceBoundTraceWindow.ofPresentationWindow
      source target metadata.recipe.window
  have events :=
    GraphicalEditProgram.oneTwoBirth_matchesWindow
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
      metadata.recipe.window metadata.recipe.graphical_window_sound
  exact
    { script := script
      sourceSplit := by
        simpa only [events.1] using split.sourceSplit
      targetSplit := by
        simpa only [events.2] using split.targetSplit }

/-- Exact trace binding for removal of a cancelling one--two pair. -/
structure OneTwoDeathBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology) where
  script :
    OneTwoCancellationScript
      (HandleEdit.oneTwoDeathDottedId metadata.recipe.handleEdit)
      (HandleEdit.oneTwoDeathTwoHandleId metadata.recipe.handleEdit)
  sourceSplit :
    Trace.ThreeWaySplit
      (raw := source.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.hopfEvents
      metadata.recipe.window.commonEventSuffix
  targetSplit :
    Trace.ThreeWaySplit
      (raw := target.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.identityEvents
      metadata.recipe.window.commonEventSuffix

/-- Build the one--two death binding from executable recipe equalities. -/
def oneTwoDeathBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology) :
    OneTwoDeathBinding source target metadata := by
  let script :=
    GraphicalEditProgram.oneTwoDeathScriptOfEdit
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
  let split :=
    SourceBoundTraceWindow.ofPresentationWindow
      source target metadata.recipe.window
  have events :=
    GraphicalEditProgram.oneTwoDeath_matchesWindow
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
      metadata.recipe.window metadata.recipe.graphical_window_sound
  exact
    { script := script
      sourceSplit := by
        simpa only [events.1] using split.sourceSplit
      targetSplit := by
        simpa only [events.2] using split.targetSplit }

/-- Exact trace binding for creation of a cancelling two--three pair. -/
structure TwoThreeBirthBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology) where
  script :
    TwoThreeCancellationScript
      (HandleEdit.twoThreeBirthTwoHandleId metadata.recipe.handleEdit)
  sourceSplit :
    Trace.ThreeWaySplit
      (raw := source.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.identityEvents
      metadata.recipe.window.commonEventSuffix
  targetSplit :
    Trace.ThreeWaySplit
      (raw := target.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.zeroFramedEvents
      metadata.recipe.window.commonEventSuffix

/-- Build the two--three birth binding from executable recipe equalities. -/
def twoThreeBirthBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology) :
    TwoThreeBirthBinding source target metadata := by
  let script :=
    GraphicalEditProgram.twoThreeBirthScriptOfEdit
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
  let split :=
    SourceBoundTraceWindow.ofPresentationWindow
      source target metadata.recipe.window
  have events :=
    GraphicalEditProgram.twoThreeBirth_matchesWindow
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
      metadata.recipe.window metadata.recipe.graphical_window_sound
  exact
    { script := script
      sourceSplit := by
        simpa only [events.1] using split.sourceSplit
      targetSplit := by
        simpa only [events.2] using split.targetSplit }

/-- Exact trace binding for removal of a cancelling two--three pair. -/
structure TwoThreeDeathBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology) where
  script :
    TwoThreeCancellationScript
      (HandleEdit.twoThreeDeathTwoHandleId metadata.recipe.handleEdit)
  sourceSplit :
    Trace.ThreeWaySplit
      (raw := source.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.zeroFramedEvents
      metadata.recipe.window.commonEventSuffix
  targetSplit :
    Trace.ThreeWaySplit
      (raw := target.topology.formal.raw)
      (initial := []) (final := [])
      metadata.recipe.window.commonEventPrefix
      script.identityEvents
      metadata.recipe.window.commonEventSuffix

/-- Build the two--three death binding from executable recipe equalities. -/
def twoThreeDeathBinding
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology) :
    TwoThreeDeathBinding source target metadata := by
  let script :=
    GraphicalEditProgram.twoThreeDeathScriptOfEdit
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
  let split :=
    SourceBoundTraceWindow.ofPresentationWindow
      source target metadata.recipe.window
  have events :=
    GraphicalEditProgram.twoThreeDeath_matchesWindow
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
      metadata.recipe.window metadata.recipe.graphical_window_sound
  exact
    { script := script
      sourceSplit := by
        simpa only [events.1] using split.sourceSplit
      targetSplit := by
        simpa only [events.2] using split.targetSplit }

/-- Exact target state of any accepted birth window. -/
theorem birth_window_target_eq
    (eventId componentId positiveId negativeId : String)
    (insertAt : Nat)
    {before after : List StrandState}
    (window :
      EventWindow
        (.birth eventId componentId positiveId negativeId insertAt)
        before after) :
    after =
      before.take insertAt ++
        ([positiveStrand positiveId componentId,
          negativeStrand negativeId componentId] ++
          before.drop insertAt) := by
  cases window
  rw [List.take_left, List.drop_left]

/-- A birth at index zero places its oriented pair at the front. -/
theorem birth_zero_window_target_eq
    (eventId componentId positiveId negativeId : String)
    {before after : List StrandState}
    (window :
      EventWindow
        (.birth eventId componentId positiveId negativeId 0)
        before after) :
    after =
      positiveStrand positiveId componentId ::
        negativeStrand negativeId componentId :: before := by
  simpa using
    birth_window_target_eq
      eventId componentId positiveId negativeId 0 window

/--
Successful death of the explicit front positive/negative pair returns the
untouched suffix.  All lineage and orientation checks are discharged by
reducing the executable validator.
-/
theorem death_front_step_target_eq
    (raw : RawPresentation)
    (eventId componentId positiveId negativeId : String)
    (distinct : positiveId ≠ negativeId)
    (suffix after : List StrandState)
    (step :
      raw.applyEvent
          (positiveStrand positiveId componentId ::
            negativeStrand negativeId componentId :: suffix)
          (.death eventId componentId positiveId negativeId) =
        Except.ok after) :
    after = suffix := by
  simp [RawPresentation.applyEvent, RawPresentation.strand?,
    RawPresentation.removeAdjacentPair?, RawPresentation.requireSome,
    RawPresentation.orientationsOpposite,
    positiveStrand, negativeStrand, distinct,
    Bind.bind, Pure.pure, Except.bind] at step
  change Except.ok suffix = Except.ok after at step
  exact (Except.ok.inj step).symm

/--
The executable six-event one--two cancellation script returns to its initial
boundary.  This is a calculation in the raw slice executor, not a graphical
or evaluator-level assumption.
-/
theorem oneTwoTrace_final_eq
    {raw : RawPresentation}
    {dottedId twoHandleId : String}
    (script : OneTwoCancellationScript dottedId twoHandleId)
    {before after : List StrandState}
    (trace : Trace raw script.hopfEvents before after) :
    after = before := by
  cases trace with
  | cons twoBirthWindow twoBirthStep tail =>
      cases tail with
      | cons dottedBirthWindow dottedBirthStep tail =>
          cases tail with
          | cons firstCrossingWindow firstCrossingStep tail =>
              cases tail with
              | cons secondCrossingWindow secondCrossingStep tail =>
                  cases tail with
                  | cons dottedDeathWindow dottedDeathStep tail =>
                      cases tail with
                      | cons twoDeathWindow twoDeathStep tail =>
                          cases tail
                          have firstBirth :=
                            birth_zero_window_target_eq
                              script.twoBirthId twoHandleId
                              script.twoPositiveId script.twoNegativeId
                              twoBirthWindow
                          rw [firstBirth] at dottedBirthWindow
                          rw [firstBirth] at dottedBirthStep
                          have secondBirth :=
                            birth_zero_window_target_eq
                              script.dottedBirthId dottedId
                              script.dottedPositiveId
                              script.dottedNegativeId
                              dottedBirthWindow
                          rw [secondBirth] at firstCrossingWindow
                          rw [secondBirth] at firstCrossingStep
                          have dottedFresh :=
                            CanonicalTraceLocality.birth_step_fresh
                              raw
                              (positiveStrand script.twoPositiveId
                                  twoHandleId ::
                                negativeStrand script.twoNegativeId
                                  twoHandleId :: before)
                              _
                              script.dottedBirthId dottedId
                              script.dottedPositiveId
                              script.dottedNegativeId 0
                              dottedBirthStep
                          have twoFresh :=
                            CanonicalTraceLocality.birth_step_fresh
                              raw before _
                              script.twoBirthId twoHandleId
                              script.twoPositiveId
                              script.twoNegativeId 0
                              twoBirthStep
                          have dottedPositiveNeTwoPositive :
                              script.dottedPositiveId ≠
                                script.twoPositiveId := by
                            intro equality
                            apply dottedFresh.2.1
                            simp [RawPresentation.activeIds,
                              positiveStrand, equality]
                          by_cases crossingDistinct :
                              script.dottedNegativeId =
                                script.twoPositiveId
                          · simp [RawPresentation.applyEvent,
                              crossingDistinct, Bind.bind,
                              Except.bind] at firstCrossingStep
                          · simp [RawPresentation.applyEvent,
                              RawPresentation.allActive,
                              RawPresentation.strand?,
                              RawPresentation.swapAdjacentPair?,
                              RawPresentation.requireSome,
                              positiveStrand, negativeStrand,
                              crossingDistinct,
                              dottedPositiveNeTwoPositive,
                              Bind.bind, Pure.pure,
                              Except.bind] at firstCrossingStep
                            change
                              Except.ok
                                  (positiveStrand
                                      script.dottedPositiveId dottedId ::
                                    positiveStrand
                                      script.twoPositiveId twoHandleId ::
                                    negativeStrand
                                      script.dottedNegativeId dottedId ::
                                    negativeStrand
                                      script.twoNegativeId twoHandleId ::
                                    before) =
                                Except.ok _ at firstCrossingStep
                            have firstCrossingEq :=
                              Except.ok.inj firstCrossingStep
                            rw [← firstCrossingEq] at secondCrossingWindow
                            rw [← firstCrossingEq] at secondCrossingStep
                            have twoPositiveNeDottedNegative :
                                script.twoPositiveId ≠
                                  script.dottedNegativeId :=
                              Ne.symm crossingDistinct
                            simp [RawPresentation.applyEvent,
                              RawPresentation.allActive,
                              RawPresentation.strand?,
                              RawPresentation.swapAdjacentPair?,
                              RawPresentation.requireSome,
                              positiveStrand, negativeStrand,
                              twoPositiveNeDottedNegative,
                              dottedFresh.1,
                              Bind.bind, Pure.pure,
                              Except.bind, Except.pure] at secondCrossingStep
                            rw [← secondCrossingStep] at dottedDeathWindow
                            rw [← secondCrossingStep] at dottedDeathStep
                            have dottedDeathEq :=
                              death_front_step_target_eq
                                raw script.dottedDeathId dottedId
                                script.dottedPositiveId
                                script.dottedNegativeId
                                dottedFresh.1
                                (positiveStrand script.twoPositiveId
                                    twoHandleId ::
                                  negativeStrand script.twoNegativeId
                                    twoHandleId :: before)
                                _ dottedDeathStep
                            rw [dottedDeathEq] at twoDeathWindow
                            rw [dottedDeathEq] at twoDeathStep
                            exact
                              death_front_step_target_eq
                                raw script.twoDeathId twoHandleId
                                script.twoPositiveId
                                script.twoNegativeId
                                twoFresh.1 before after twoDeathStep

/-- A validated one-marker identity window returns to its initial boundary. -/
theorem identityTrace_final_eq
    {raw : RawPresentation}
    (eventId : String)
    (order : List String)
    {before after : List StrandState}
    (trace :
      Trace raw [.planarIsotopy eventId order] before after) :
    after = before := by
  cases trace with
  | cons window step tail =>
      cases tail
      exact
        (CanonicalTraceLocality.planar_step_order_target
          _ _ _ _ _ step).2

/--
A validated one-marker identity window compiles to the identity diagram up
to the explicit right-identity move of the free graphical grammar.
-/
theorem identityTrace_componentDiagram_isotopy
    {raw : RawPresentation}
    (eventId : String)
    (order : List String)
    {before : List StrandState}
    (trace :
      Trace raw [.planarIsotopy eventId order] before before) :
    GeneratedIsotopy
      (Trace.componentDiagram trace)
      (ComponentDiagram.identity (ComponentBoundary.word before)) := by
  cases trace with
  | cons window step tail =>
      cases tail
      have primitiveEq :
          EventWindow.componentPrimitive window =
            ComponentDiagram.identity
              (ComponentBoundary.word before) :=
        eq_of_heq
          (CanonicalTraceDiagramDeterminism.planar_window_primitive_heq
            eventId order window)
      change
        GeneratedIsotopy
          (EventWindow.componentPrimitive window ≫ᶜ
            ComponentDiagram.identity
              (ComponentBoundary.word before))
          (ComponentDiagram.identity
            (ComponentBoundary.word before))
      rw [primitiveEq]
      exact
        .step
          (.identityAfter
            (ComponentDiagram.identity
              (ComponentBoundary.word before)))

/-- Canonical front birth of a zero-framed component beside an old boundary. -/
def zeroFramedBirthWindowAt
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId)
    (suffix : List StrandState) :
    EventWindow
      (.birth script.birthEventId twoHandleId
        script.positiveId script.negativeId 0)
      suffix
      (positiveStrand script.positiveId twoHandleId ::
        negativeStrand script.negativeId twoHandleId :: suffix) :=
  .birth script.birthEventId twoHandleId
    script.positiveId script.negativeId [] suffix

/-- Canonical front death of that zero-framed component. -/
def zeroFramedDeathWindowAt
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId)
    (suffix : List StrandState) :
    EventWindow
      (.death script.deathEventId twoHandleId
        script.positiveId script.negativeId)
      (positiveStrand script.positiveId twoHandleId ::
        negativeStrand script.negativeId twoHandleId :: suffix)
      suffix :=
  .deathPositiveNegative script.deathEventId twoHandleId
    script.positiveId script.negativeId
    script.positiveId script.negativeId
    (by simp [RawPresentation.sameStringSet])
    [] suffix

/-- Contextual free diagram of the exact two-event zero-framed script. -/
def zeroFramedContextDiagram
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId)
    (suffix : List StrandState) :
    ComponentDiagram
      (ComponentBoundary.word suffix)
      (ComponentBoundary.word suffix) :=
  EventWindow.componentPrimitive
      (zeroFramedBirthWindowAt script suffix) ≫ᶜ
    EventWindow.componentPrimitive
      (zeroFramedDeathWindowAt script suffix)

/-- The exact two-event script returns to its incoming active boundary. -/
theorem zeroFramedTrace_final_eq
    {raw : RawPresentation}
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId)
    {before after : List StrandState}
    (trace :
      Trace raw script.zeroFramedEvents before after) :
    after = before := by
  cases trace with
  | cons birthWindow birthStep tail =>
      cases tail with
      | cons deathWindow deathStep finalTail =>
          cases finalTail
          have middleEq :=
            birth_zero_window_target_eq
              script.birthEventId twoHandleId
              script.positiveId script.negativeId birthWindow
          subst middleEq
          have distinct :=
            (CanonicalTraceLocality.birth_step_fresh
              raw before
              (positiveStrand script.positiveId twoHandleId ::
                negativeStrand script.negativeId twoHandleId :: before)
              script.birthEventId twoHandleId
              script.positiveId script.negativeId 0 birthStep).1
          exact
            death_front_step_target_eq raw
              script.deathEventId twoHandleId
              script.positiveId script.negativeId distinct
              before after deathStep

/--
The exact validated two-event trace compiles to its canonical contextual
zero-framed diagram.
-/
theorem zeroFramedTrace_componentDiagram_isotopy
    {raw : RawPresentation}
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId)
    {boundary : List StrandState}
    (trace :
      Trace raw script.zeroFramedEvents boundary boundary)
    (unique : CanonicalTraceLocality.ActiveIdsUnique boundary) :
    GeneratedIsotopy
      (Trace.componentDiagram trace)
      (zeroFramedContextDiagram script boundary) := by
  cases trace with
  | cons birthWindow birthStep tail =>
      cases tail with
      | cons deathWindow deathStep finalTail =>
          cases finalTail
          have middleEq :=
            birth_zero_window_target_eq
              script.birthEventId twoHandleId
              script.positiveId script.negativeId birthWindow
          subst middleEq
          have birthPrimitiveEq :
              EventWindow.componentPrimitive birthWindow =
                EventWindow.componentPrimitive
                  (zeroFramedBirthWindowAt script boundary) :=
            CanonicalTraceDiagramDeterminism.EventWindow.componentPrimitive_eq
              birthWindow (zeroFramedBirthWindowAt script boundary)
              birthStep unique
          have middleUnique :=
            CanonicalTraceLocality.EventWindow.preserves_activeIdsUnique
              birthWindow birthStep unique
          have deathPrimitiveEq :
              EventWindow.componentPrimitive deathWindow =
                EventWindow.componentPrimitive
                  (zeroFramedDeathWindowAt script boundary) :=
            CanonicalTraceDiagramDeterminism.EventWindow.componentPrimitive_eq
              deathWindow (zeroFramedDeathWindowAt script boundary)
              deathStep middleUnique
          change
            GeneratedIsotopy
              (EventWindow.componentPrimitive birthWindow ≫ᶜ
                (EventWindow.componentPrimitive deathWindow ≫ᶜ
                  ComponentDiagram.identity
                    (ComponentBoundary.word boundary)))
              (EventWindow.componentPrimitive
                  (zeroFramedBirthWindowAt script boundary) ≫ᶜ
                EventWindow.componentPrimitive
                  (zeroFramedDeathWindowAt script boundary))
          rw [birthPrimitiveEq, deathPrimitiveEq]
          exact
            .inContext
              (.compLeft
                (EventWindow.componentPrimitive
                  (zeroFramedBirthWindowAt script boundary)))
              (.step
                (.identityAfter
                  (EventWindow.componentPrimitive
                    (zeroFramedDeathWindowAt script boundary))))

/--
The contextual two-event script is exactly one zero-framed unknot inserted
beside the untouched active boundary.
-/
theorem zeroFramedContextDiagram_isotopy
    {twoHandleId : String}
    (script : TwoThreeCancellationScript twoHandleId)
    (boundary : List StrandState) :
    GeneratedIsotopy
      (zeroFramedContextDiagram script boundary)
      ((ComponentDiagram.Context.surroundBoundaryWord
          [] [] [] boundary).plug
        (ComponentDiagram.zeroFramedUnknot twoHandleId)) := by
  exact
    .step
      (.surroundPairComp
        (positiveStrand script.positiveId twoHandleId)
        (negativeStrand script.negativeId twoHandleId)
        boundary
        (.cupPositiveNegative twoHandleId)
        (.capPositiveNegative twoHandleId))

/--
The exact two--three birth script lifts from its local window to the complete
closed component diagram.
-/
theorem twoThreeBirth_componentTermDiagram_isotopy
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.topology target.topology) :
    GeneratedIsotopy target.componentTermDiagram
      (ComponentDiagram.closedTensor
        (ComponentDiagram.zeroFramedUnknot
          (HandleEdit.twoThreeBirthTwoHandleId
            metadata.recipe.handleEdit))
        source.componentTermDiagram) := by
  let binding := twoThreeBirthBinding source target metadata
  have bindingScriptEq :
      binding.script =
        GraphicalEditProgram.twoThreeBirthScriptOfEdit
          metadata.recipe.handleEdit metadata.recipe.graphicalProgram := by
    rfl
  rcases binding with ⟨script, sourceSplit, targetSplit⟩
  rcases sourceSplit with
    ⟨sourceWhole, sourceAfterPrefix, sourceAfterWindow,
      sourcePrefix, sourceWindow, sourceSuffix, sourceReassembles⟩
  rcases targetSplit with
    ⟨targetWhole, targetAfterPrefix, targetAfterWindow,
      targetPrefix, targetWindow, targetSuffix, targetReassembles⟩
  have scriptEq :
      script =
        GraphicalEditProgram.twoThreeBirthScriptOfEdit
          metadata.recipe.handleEdit metadata.recipe.graphicalProgram :=
    bindingScriptEq
  have windowMatches :=
    GraphicalEditProgram.twoThreeBirth_matchesWindow
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
      metadata.recipe.window metadata.recipe.graphical_window_sound
  have sourceEventsEq :
      source.topology.formal.raw.events =
        metadata.recipe.window.commonEventPrefix ++
          script.identityEvents ++
          metadata.recipe.window.commonEventSuffix := by
    rw [metadata.recipe.window.source_events_sound,
      windowMatches.1, scriptEq]
  have targetEventsEq :
      target.topology.formal.raw.events =
        metadata.recipe.window.commonEventPrefix ++
          script.zeroFramedEvents ++
          metadata.recipe.window.commonEventSuffix := by
    rw [metadata.recipe.window.target_events_sound,
      windowMatches.2, scriptEq]
  have prefixStateEq :
      sourceAfterPrefix = targetAfterPrefix :=
    Trace.final_eq_of_same_events sourcePrefix targetPrefix
  cases prefixStateEq
  have sourceWindowFinalEq :
      sourceAfterWindow = sourceAfterPrefix :=
    identityTrace_final_eq
      script.identityEventId script.identityOrder sourceWindow
  have targetWindowFinalEq :
      targetAfterWindow = sourceAfterPrefix :=
    zeroFramedTrace_final_eq script targetWindow
  cases sourceWindowFinalEq
  cases targetWindowFinalEq
  have prefixUnique :
      ActiveIdsUnique sourceAfterPrefix :=
    Trace.preserves_activeIdsUnique
      sourcePrefix
      (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  have prefixDiagramEq :
      Trace.componentDiagram targetPrefix =
        Trace.componentDiagram sourcePrefix :=
    CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_same_events
      targetPrefix sourcePrefix
      (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  have suffixDiagramEq :
      Trace.componentDiagram targetSuffix =
        Trace.componentDiagram sourceSuffix :=
    CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_same_events
      targetSuffix sourceSuffix prefixUnique
  have sourceWholeDiagramEq :
      source.componentTermDiagram =
        Trace.componentDiagram sourceWhole := by
    unfold CanonicalPresentation.componentTermDiagram
    exact
      CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_events_eq
        sourceEventsEq source.canonicalTrace.trace sourceWhole
        (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  have targetWholeDiagramEq :
      target.componentTermDiagram =
        Trace.componentDiagram targetWhole := by
    unfold CanonicalPresentation.componentTermDiagram
    exact
      CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_events_eq
        targetEventsEq target.canonicalTrace.trace targetWhole
        (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  let sourceSplit' :
      Trace.ThreeWaySplit
        (raw := source.topology.formal.raw)
        (initial := []) (final := [])
        metadata.recipe.window.commonEventPrefix
        script.identityEvents
        metadata.recipe.window.commonEventSuffix :=
    { wholeTrace := sourceWhole
      afterPrefix := sourceAfterPrefix
      afterWindow := sourceAfterPrefix
      prefixTrace := sourcePrefix
      windowTrace := sourceWindow
      suffixTrace := sourceSuffix
      reassembles := sourceReassembles }
  let targetSplit' :
      Trace.ThreeWaySplit
        (raw := target.topology.formal.raw)
        (initial := []) (final := [])
        metadata.recipe.window.commonEventPrefix
        script.zeroFramedEvents
        metadata.recipe.window.commonEventSuffix :=
    { wholeTrace := targetWhole
      afterPrefix := sourceAfterPrefix
      afterWindow := sourceAfterPrefix
      prefixTrace := targetPrefix
      windowTrace := targetWindow
      suffixTrace := targetSuffix
      reassembles := targetReassembles }
  have sourceWindowIsotopy :
      GeneratedIsotopy
        (Trace.componentDiagram sourceWindow)
        (ComponentDiagram.identity
          (ComponentBoundary.word sourceAfterPrefix)) :=
    identityTrace_componentDiagram_isotopy
      script.identityEventId script.identityOrder sourceWindow
  have sourceWholeToRetained :
      GeneratedIsotopy
        (Trace.componentDiagram sourceWhole)
        (Trace.componentDiagram sourcePrefix ≫ᶜ
          Trace.componentDiagram sourceSuffix) := by
    exact
      .trans
        (GeneratedIsotopy.componentDiagram_splitThree
          _ _ _ sourceSplit')
        (.trans
          (GeneratedIsotopy.verticalTriple
            (.refl _) sourceWindowIsotopy (.refl _))
          (.inContext
            (.compRight (Trace.componentDiagram sourceSuffix))
            (.step
              (.identityAfter
                (Trace.componentDiagram sourcePrefix)))))
  have prefixIsotopy :
      GeneratedIsotopy
        (Trace.componentDiagram targetPrefix)
        (Trace.componentDiagram sourcePrefix) := by
    rw [prefixDiagramEq]
    exact .refl _
  have suffixIsotopy :
      GeneratedIsotopy
        (Trace.componentDiagram targetSuffix)
        (Trace.componentDiagram sourceSuffix) := by
    rw [suffixDiagramEq]
    exact .refl _
  have targetWindowIsotopy :
      GeneratedIsotopy
        (Trace.componentDiagram targetWindow)
        (FreeTemplates.closedInsertionAt sourceAfterPrefix
          (ComponentDiagram.zeroFramedUnknot
            (HandleEdit.twoThreeBirthTwoHandleId
              metadata.recipe.handleEdit))) := by
    exact
      .trans
        (zeroFramedTrace_componentDiagram_isotopy
          script targetWindow prefixUnique)
        (.trans
          (zeroFramedContextDiagram_isotopy
            script sourceAfterPrefix)
          (.step
            (.surroundClosedInsertion sourceAfterPrefix
              (ComponentDiagram.zeroFramedUnknot
                (HandleEdit.twoThreeBirthTwoHandleId
                  metadata.recipe.handleEdit)))))
  have targetWholeToClosedRetained :
      GeneratedIsotopy
        (Trace.componentDiagram targetWhole)
        (ComponentDiagram.closedTensor
          (ComponentDiagram.zeroFramedUnknot
            (HandleEdit.twoThreeBirthTwoHandleId
              metadata.recipe.handleEdit))
          (Trace.componentDiagram sourcePrefix ≫ᶜ
            Trace.componentDiagram sourceSuffix)) := by
    exact
      .trans
        (GeneratedIsotopy.componentDiagram_splitThree
          _ _ _ targetSplit')
        (.trans
          (GeneratedIsotopy.verticalTriple
            prefixIsotopy targetWindowIsotopy suffixIsotopy)
          (.step
            (.closedInsertionFactor sourceAfterPrefix
              (ComponentDiagram.zeroFramedUnknot
                (HandleEdit.twoThreeBirthTwoHandleId
                  metadata.recipe.handleEdit))
              (Trace.componentDiagram sourcePrefix)
              (Trace.componentDiagram sourceSuffix))))
  rw [targetWholeDiagramEq, sourceWholeDiagramEq]
  exact
    .trans targetWholeToClosedRetained
      (GeneratedIsotopy.closedTensorRight
        (ComponentDiagram.zeroFramedUnknot
          (HandleEdit.twoThreeBirthTwoHandleId
            metadata.recipe.handleEdit))
        sourceWholeToRetained.symm)

/--
The exact two--three death script lifts from its local window to the complete
closed component diagram.  This is the direction-reversed counterpart of
`twoThreeBirth_componentTermDiagram_isotopy`, proved from the death recipe
rather than postulated as a reverse endpoint equality.
-/
theorem twoThreeDeath_componentTermDiagram_isotopy
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology) :
    GeneratedIsotopy source.componentTermDiagram
      (ComponentDiagram.closedTensor
        (ComponentDiagram.zeroFramedUnknot
          (HandleEdit.twoThreeDeathTwoHandleId
            metadata.recipe.handleEdit))
        target.componentTermDiagram) := by
  let binding := twoThreeDeathBinding source target metadata
  have bindingScriptEq :
      binding.script =
        GraphicalEditProgram.twoThreeDeathScriptOfEdit
          metadata.recipe.handleEdit metadata.recipe.graphicalProgram := by
    rfl
  rcases binding with ⟨script, sourceSplit, targetSplit⟩
  rcases sourceSplit with
    ⟨sourceWhole, sourceAfterPrefix, sourceAfterWindow,
      sourcePrefix, sourceWindow, sourceSuffix, sourceReassembles⟩
  rcases targetSplit with
    ⟨targetWhole, targetAfterPrefix, targetAfterWindow,
      targetPrefix, targetWindow, targetSuffix, targetReassembles⟩
  have scriptEq :
      script =
        GraphicalEditProgram.twoThreeDeathScriptOfEdit
          metadata.recipe.handleEdit metadata.recipe.graphicalProgram :=
    bindingScriptEq
  have windowMatches :=
    GraphicalEditProgram.twoThreeDeath_matchesWindow
      metadata.recipe.handleEdit metadata.recipe.graphicalProgram
      metadata.recipe.window metadata.recipe.graphical_window_sound
  have sourceEventsEq :
      source.topology.formal.raw.events =
        metadata.recipe.window.commonEventPrefix ++
          script.zeroFramedEvents ++
          metadata.recipe.window.commonEventSuffix := by
    rw [metadata.recipe.window.source_events_sound,
      windowMatches.1, scriptEq]
  have targetEventsEq :
      target.topology.formal.raw.events =
        metadata.recipe.window.commonEventPrefix ++
          script.identityEvents ++
          metadata.recipe.window.commonEventSuffix := by
    rw [metadata.recipe.window.target_events_sound,
      windowMatches.2, scriptEq]
  have prefixStateEq :
      sourceAfterPrefix = targetAfterPrefix :=
    Trace.final_eq_of_same_events sourcePrefix targetPrefix
  cases prefixStateEq
  have sourceWindowFinalEq :
      sourceAfterWindow = sourceAfterPrefix :=
    zeroFramedTrace_final_eq script sourceWindow
  have targetWindowFinalEq :
      targetAfterWindow = sourceAfterPrefix :=
    identityTrace_final_eq
      script.identityEventId script.identityOrder targetWindow
  cases sourceWindowFinalEq
  cases targetWindowFinalEq
  have prefixUnique :
      ActiveIdsUnique sourceAfterPrefix :=
    Trace.preserves_activeIdsUnique
      sourcePrefix
      (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  have prefixDiagramEq :
      Trace.componentDiagram targetPrefix =
        Trace.componentDiagram sourcePrefix :=
    CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_same_events
      targetPrefix sourcePrefix
      (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  have suffixDiagramEq :
      Trace.componentDiagram targetSuffix =
        Trace.componentDiagram sourceSuffix :=
    CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_same_events
      targetSuffix sourceSuffix prefixUnique
  have sourceWholeDiagramEq :
      source.componentTermDiagram =
        Trace.componentDiagram sourceWhole := by
    unfold CanonicalPresentation.componentTermDiagram
    exact
      CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_events_eq
        sourceEventsEq source.canonicalTrace.trace sourceWhole
        (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  have targetWholeDiagramEq :
      target.componentTermDiagram =
        Trace.componentDiagram targetWhole := by
    unfold CanonicalPresentation.componentTermDiagram
    exact
      CanonicalTraceDiagramDeterminism.Trace.componentDiagram_eq_of_events_eq
        targetEventsEq target.canonicalTrace.trace targetWhole
        (by simp [ActiveIdsUnique, RawPresentation.activeIds])
  let sourceSplit' :
      Trace.ThreeWaySplit
        (raw := source.topology.formal.raw)
        (initial := []) (final := [])
        metadata.recipe.window.commonEventPrefix
        script.zeroFramedEvents
        metadata.recipe.window.commonEventSuffix :=
    { wholeTrace := sourceWhole
      afterPrefix := sourceAfterPrefix
      afterWindow := sourceAfterPrefix
      prefixTrace := sourcePrefix
      windowTrace := sourceWindow
      suffixTrace := sourceSuffix
      reassembles := sourceReassembles }
  let targetSplit' :
      Trace.ThreeWaySplit
        (raw := target.topology.formal.raw)
        (initial := []) (final := [])
        metadata.recipe.window.commonEventPrefix
        script.identityEvents
        metadata.recipe.window.commonEventSuffix :=
    { wholeTrace := targetWhole
      afterPrefix := sourceAfterPrefix
      afterWindow := sourceAfterPrefix
      prefixTrace := targetPrefix
      windowTrace := targetWindow
      suffixTrace := targetSuffix
      reassembles := targetReassembles }
  have targetWindowIsotopy :
      GeneratedIsotopy
        (Trace.componentDiagram targetWindow)
        (ComponentDiagram.identity
          (ComponentBoundary.word sourceAfterPrefix)) :=
    identityTrace_componentDiagram_isotopy
      script.identityEventId script.identityOrder targetWindow
  have targetWholeToRetained :
      GeneratedIsotopy
        (Trace.componentDiagram targetWhole)
        (Trace.componentDiagram sourcePrefix ≫ᶜ
          Trace.componentDiagram sourceSuffix) := by
    have prefixIsotopy :
        GeneratedIsotopy
          (Trace.componentDiagram targetPrefix)
          (Trace.componentDiagram sourcePrefix) := by
      rw [prefixDiagramEq]
      exact .refl _
    have suffixIsotopy :
        GeneratedIsotopy
          (Trace.componentDiagram targetSuffix)
          (Trace.componentDiagram sourceSuffix) := by
      rw [suffixDiagramEq]
      exact .refl _
    exact
      .trans
        (GeneratedIsotopy.componentDiagram_splitThree
          _ _ _ targetSplit')
        (.trans
          (GeneratedIsotopy.verticalTriple
            prefixIsotopy targetWindowIsotopy suffixIsotopy)
          (.inContext
            (.compRight (Trace.componentDiagram sourceSuffix))
            (.step
              (.identityAfter
                (Trace.componentDiagram sourcePrefix)))))
  have sourceWindowIsotopy :
      GeneratedIsotopy
        (Trace.componentDiagram sourceWindow)
        (FreeTemplates.closedInsertionAt sourceAfterPrefix
          (ComponentDiagram.zeroFramedUnknot
            (HandleEdit.twoThreeDeathTwoHandleId
              metadata.recipe.handleEdit))) := by
    exact
      .trans
        (zeroFramedTrace_componentDiagram_isotopy
          script sourceWindow prefixUnique)
        (.trans
          (zeroFramedContextDiagram_isotopy
            script sourceAfterPrefix)
          (.step
            (.surroundClosedInsertion sourceAfterPrefix
              (ComponentDiagram.zeroFramedUnknot
                (HandleEdit.twoThreeDeathTwoHandleId
                  metadata.recipe.handleEdit)))))
  have sourceWholeToClosedRetained :
      GeneratedIsotopy
        (Trace.componentDiagram sourceWhole)
        (ComponentDiagram.closedTensor
          (ComponentDiagram.zeroFramedUnknot
            (HandleEdit.twoThreeDeathTwoHandleId
              metadata.recipe.handleEdit))
          (Trace.componentDiagram sourcePrefix ≫ᶜ
            Trace.componentDiagram sourceSuffix)) := by
    exact
      .trans
        (GeneratedIsotopy.componentDiagram_splitThree
          _ _ _ sourceSplit')
        (.trans
          (GeneratedIsotopy.verticalTriple
            (.refl _) sourceWindowIsotopy (.refl _))
          (.step
            (.closedInsertionFactor sourceAfterPrefix
              (ComponentDiagram.zeroFramedUnknot
                (HandleEdit.twoThreeDeathTwoHandleId
                  metadata.recipe.handleEdit))
              (Trace.componentDiagram sourcePrefix)
              (Trace.componentDiagram sourceSuffix))))
  rw [sourceWholeDiagramEq, targetWholeDiagramEq]
  exact
    .trans sourceWholeToClosedRetained
      (GeneratedIsotopy.closedTensorRight
        (ComponentDiagram.zeroFramedUnknot
          (HandleEdit.twoThreeDeathTwoHandleId
            metadata.recipe.handleEdit))
        targetWholeToRetained.symm)

end TwistedYetter.Kirby.CanonicalCancellationTraceBinding
