import TwistedYetter.Kirby.Presentation

/-!
# Typed execution traces for admitted sliced presentations

`RawPresentation.validate` is executable, but a downstream compiler should not
have to treat its final `Except.ok` as an opaque promise. This module replays
the same `applyEvent` function into a typed trace. Every node records the exact
event, exact incoming slice, exact outgoing slice, and the equality proving
that the validator computed that transition.

A closed certificate additionally fixes both endpoint boundaries to `[]` and
proves that the trace states are exactly the declared JSON slices.
-/

namespace TwistedYetter.Kirby.PresentationExecutionTrace

open TwistedYetter.Kirby.Presentation

/-- One complete, typed replay of a list of slice events. -/
inductive ExecutionTrace
    (raw : RawPresentation) :
    List SliceEvent → List StrandState → List StrandState → Type
  | nil (state : List StrandState) :
      ExecutionTrace raw [] state state
  | cons
      {event : SliceEvent}
      {rest : List SliceEvent}
      {before after final : List StrandState}
      (step_sound : raw.applyEvent before event = Except.ok after)
      (tail : ExecutionTrace raw rest after final) :
      ExecutionTrace raw (event :: rest) before final

namespace ExecutionTrace

/-- Number of validator transitions represented by the trace. -/
def stepCount
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState} :
    ExecutionTrace raw events before final → Nat
  | .nil _ => 0
  | .cons _ tail => 1 + tail.stepCount

/-- Every slice state, including both endpoints. -/
def states
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState} :
    ExecutionTrace raw events before final → List (List StrandState)
  | .nil state => [state]
  | @cons _ _ _ before _ _ _ tail =>
      before :: tail.states

/-- Stable event IDs in exact execution order. -/
def eventIds
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState} :
    ExecutionTrace raw events before final → List String
  | .nil _ => []
  | @cons _ event _ _ _ _ _ tail =>
      event.eventId :: tail.eventIds

theorem stepCount_eq_event_length
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace : ExecutionTrace raw events before final) :
    trace.stepCount = events.length := by
  induction trace with
  | nil =>
      rfl
  | cons step tail inductionHypothesis =>
      simp only [stepCount, List.length_cons, inductionHypothesis]
      omega

theorem states_length_eq_event_length_add_one
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace : ExecutionTrace raw events before final) :
    trace.states.length = events.length + 1 := by
  induction trace with
  | nil =>
      simp [states]
  | cons step tail inductionHypothesis =>
      simp only [states, List.length_cons, inductionHypothesis]

theorem eventIds_eq
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace : ExecutionTrace raw events before final) :
    trace.eventIds = events.map SliceEvent.eventId := by
  induction trace with
  | nil =>
      simp [eventIds]
  | cons step tail inductionHypothesis =>
      simp only [eventIds, List.map_cons, inductionHypothesis]

end ExecutionTrace

/-- Executably materialize a typed trace or return the first event error. -/
def buildTraceFrom
    (raw : RawPresentation) :
    (events : List SliceEvent) →
    (before : List StrandState) →
      Except String
        (Σ final, ExecutionTrace raw events before final)
  | [], before =>
      return ⟨before, .nil before⟩
  | event :: rest, before =>
      match step : raw.applyEvent before event with
      | .error message => .error message
      | .ok after => do
          let ⟨final, tail⟩ ← buildTraceFrom raw rest after
          return ⟨final, .cons step tail⟩

/--
The downstream compilation certificate for one formal presentation.

The trace is closed by type, not by a Boolean flag. The declared-slice field
then binds every intermediate trace state to the shared JSON artifact.
-/
structure ClosedExecutionCertificate
    (formal : FormalPresentation) where
  trace :
    ExecutionTrace formal.raw formal.raw.events [] []
  declared_slices_sound :
    formal.raw.declaredSlices =
      RawPresentation.declareSlicesFrom 0 trace.states

namespace ClosedExecutionCertificate

/-- A closed trace has exactly one more slice than event. -/
theorem slice_count
    {formal : FormalPresentation}
    (certificate : ClosedExecutionCertificate formal) :
    certificate.trace.states.length =
      formal.raw.events.length + 1 :=
  certificate.trace.states_length_eq_event_length_add_one

/-- A closed trace executes every event exactly once. -/
theorem event_count
    {formal : FormalPresentation}
    (certificate : ClosedExecutionCertificate formal) :
    certificate.trace.stepCount = formal.raw.events.length :=
  certificate.trace.stepCount_eq_event_length

/-- Trace event IDs are exactly the raw artifact event IDs. -/
theorem event_ids
    {formal : FormalPresentation}
    (certificate : ClosedExecutionCertificate formal) :
    certificate.trace.eventIds =
      formal.raw.events.map SliceEvent.eventId :=
  certificate.trace.eventIds_eq

end ClosedExecutionCertificate

/-- Build a closed trace and reject either an open end or stale slices. -/
def buildClosedExecutionCertificate
    (formal : FormalPresentation) :
    Except String (ClosedExecutionCertificate formal) := do
  let ⟨final, trace⟩ ←
    buildTraceFrom formal.raw formal.raw.events []
  if final_sound : final = [] then
    let closedTrace :
        ExecutionTrace formal.raw formal.raw.events [] [] :=
      final_sound ▸ trace
    if slices_sound :
        formal.raw.declaredSlices =
          RawPresentation.declareSlicesFrom 0 closedTrace.states then
      return {
        trace := closedTrace
        declared_slices_sound := slices_sound
      }
    else
      throw "declared Morse slices do not match typed execution trace"
  else
    throw "typed execution trace has a nonempty terminal boundary"

end TwistedYetter.Kirby.PresentationExecutionTrace
