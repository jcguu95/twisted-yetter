import TwistedYetter.Kirby.PresentationExecutionTrace

/-!
# Canonical local windows for serialized Kirby diagrams

`RawPresentation.applyEvent` validates a sliced link combinatorially, but an
evaluator also needs to know the exact contiguous tensor window occupied by
each event.  This module adds that information without adding any category
morphism or scalar value.

The constructors below are deliberately restrictive:

* births and deaths expose the two oppositely oriented strands;
* crossings expose the ordered over/under pair;
* the canonical free-diagram route accepts only explicitly serialized identity
  coupons; general v2 coupons are interpreted by the categorical compiler;
* a framing twist exposes exactly one strand; and
* a planar-isotopy marker covers the complete active boundary.

Arbitrary categorical coupons remain available in
`CategoricalTangle.Diagram` for proofs.  They are not guessed from a serialized
string label in a manifold input.

Every trace step also stores the equality produced by the existing executable
validator.  Thus these windows strengthen, rather than replace, the admitted
JSON execution trace.
-/

namespace TwistedYetter.Kirby.CanonicalKirbyTrace

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationExecutionTrace

/-- The positive strand born for one oriented link component. -/
def positiveStrand (strandId componentId : String) : StrandState where
  strandId := strandId
  componentId := componentId
  orientation := .positive

/-- The negative strand born for one oriented link component. -/
def negativeStrand (strandId componentId : String) : StrandState where
  strandId := strandId
  componentId := componentId
  orientation := .negative

/--
Category-neutral local window for one exact serialized event.

The source and target lists are indices of the type.  Consequently a caller
cannot claim that a crossing occurred in one location while supplying a
different list transformation.
-/
inductive EventWindow :
    SliceEvent → List StrandState → List StrandState → Type
  | birth
      (eventId componentId positiveId negativeId : String)
      (leading suffix : List StrandState) :
      EventWindow
        (.birth eventId componentId positiveId negativeId leading.length)
        (leading ++ suffix)
        (leading ++
          ([positiveStrand positiveId componentId,
            negativeStrand negativeId componentId] ++ suffix))
  | deathPositiveNegative
      (eventId componentId firstId secondId positiveId negativeId : String)
      (listed_ids_sound :
        RawPresentation.sameStringSet
            [positiveId, negativeId] [firstId, secondId] = true)
      (leading suffix : List StrandState) :
      EventWindow
        (.death eventId componentId firstId secondId)
        (leading ++
          ([positiveStrand positiveId componentId,
            negativeStrand negativeId componentId] ++ suffix))
        (leading ++ suffix)
  | deathNegativePositive
      (eventId componentId firstId secondId negativeId positiveId : String)
      (listed_ids_sound :
        RawPresentation.sameStringSet
            [negativeId, positiveId] [firstId, secondId] = true)
      (leading suffix : List StrandState) :
      EventWindow
        (.death eventId componentId firstId secondId)
        (leading ++
          ([negativeStrand negativeId componentId,
            positiveStrand positiveId componentId] ++ suffix))
        (leading ++ suffix)
  | crossing
      (eventId overId underId : String)
      (sign : CrossingSign)
      (overComponent underComponent : String)
      (overOrientation underOrientation : Orientation)
      (leading suffix : List StrandState) :
      EventWindow
        (.crossing eventId overId underId sign)
        (leading ++
          ([
            {
              strandId := overId
              componentId := overComponent
              orientation := overOrientation
            },
            {
              strandId := underId
              componentId := underComponent
              orientation := underOrientation
            }
          ] ++ suffix))
        (leading ++
          ([
            {
              strandId := underId
              componentId := underComponent
              orientation := underOrientation
            },
            {
              strandId := overId
              componentId := overComponent
              orientation := overOrientation
            }
          ] ++ suffix))
  | identityCoupon
      (eventId couponId : String)
      (localWindow leading suffix : List StrandState) :
      EventWindow
        (.coupon eventId couponId "identity"
          (localWindow.map StrandState.strandId)
          localWindow
          leading.length)
        (leading ++ (localWindow ++ suffix))
        (leading ++ (localWindow ++ suffix))
  | framingTwist
      (eventId strandId : String)
      (sign : CrossingSign)
      (strand : StrandState)
      (strand_id_sound : strand.strandId = strandId)
      (leading suffix : List StrandState) :
      EventWindow
        (.framingTwist eventId strandId sign)
        (leading ++ ([strand] ++ suffix))
        (leading ++ ([strand] ++ suffix))
  | planarIdentity
      (eventId : String)
      (state : List StrandState) :
      EventWindow
        (.planarIsotopy eventId (state.map StrandState.strandId))
        state state

/--
A complete typed execution in which every step has a canonical local window
and is accepted by the original `applyEvent` validator.
-/
inductive Trace
    (raw : RawPresentation) :
    List SliceEvent → List StrandState → List StrandState → Type
  | nil (state : List StrandState) :
      Trace raw [] state state
  | cons
      {event : SliceEvent}
      {rest : List SliceEvent}
      {before after final : List StrandState}
      (window : EventWindow event before after)
      (step_sound : raw.applyEvent before event = Except.ok after)
      (tail : Trace raw rest after final) :
      Trace raw (event :: rest) before final

namespace Trace

/-- Forget only the extra local windows, retaining the original typed replay. -/
def toExecutionTrace
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState} :
    Trace raw events before final →
      ExecutionTrace raw events before final
  | .nil state =>
      .nil state
  | .cons _ step_sound tail =>
      .cons step_sound tail.toExecutionTrace

/--
Concatenate two typed canonical traces whose intermediate strand states
agree definitionally.

The intermediate state is an index of both inputs, so this operation cannot
silently splice traces with incompatible open boundaries.
-/
def append
    {raw : RawPresentation}
    {firstEvents secondEvents : List SliceEvent}
    {initial middle final : List StrandState} :
    Trace raw firstEvents initial middle →
    Trace raw secondEvents middle final →
      Trace raw (firstEvents ++ secondEvents) initial final
  | .nil _, second =>
      second
  | .cons window stepSound tail, second =>
      .cons window stepSound (tail.append second)

/--
The state reached after the first part of a three-part replay occurs at the
correct declared-slice index of the left-associated full trace.
-/
theorem boundary_slice_mem_declareSlicesFrom_append_append
    {raw : RawPresentation}
    {firstEvents secondEvents thirdEvents : List SliceEvent}
    {initial firstMiddle secondMiddle final : List StrandState}
    (start : Nat)
    (first : Trace raw firstEvents initial firstMiddle)
    (second : Trace raw secondEvents firstMiddle secondMiddle)
    (third : Trace raw thirdEvents secondMiddle final) :
    ({ index := start + firstEvents.length
       activeStrands := firstMiddle } : DeclaredSlice) ∈
      RawPresentation.declareSlicesFrom start
        ((first.append second).append third).toExecutionTrace.states := by
  induction first generalizing start with
  | nil state =>
      cases second <;> cases third <;>
        simp [append, toExecutionTrace,
          PresentationExecutionTrace.ExecutionTrace.states,
          RawPresentation.declareSlicesFrom]
  | @cons event rest before after final window stepSound tail
      inductionHypothesis =>
      simp only [append, toExecutionTrace,
        PresentationExecutionTrace.ExecutionTrace.states,
        RawPresentation.declareSlicesFrom, List.length_cons,
        List.mem_cons]
      right
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (start := start + 1) second

/-- Transporting only the event-list index preserves every replayed state. -/
theorem toExecutionTrace_states_transport_events
    {raw : RawPresentation}
    {events replacement : List SliceEvent}
    {before final : List StrandState}
    (eventLists : events = replacement)
    (trace : Trace raw events before final) :
    (eventLists ▸ trace).toExecutionTrace.states =
      trace.toExecutionTrace.states := by
  cases eventLists
  rfl

/--
The state reached after an exact prefix appears at the corresponding index in
the declared-slice ledger of the concatenated trace.
-/
theorem boundary_slice_mem_declareSlicesFrom_append
    {raw : RawPresentation}
    {firstEvents secondEvents : List SliceEvent}
    {initial middle final : List StrandState}
    (start : Nat)
    (first : Trace raw firstEvents initial middle)
    (second : Trace raw secondEvents middle final) :
    ({ index := start + firstEvents.length
       activeStrands := middle } : DeclaredSlice) ∈
      RawPresentation.declareSlicesFrom start
        (first.append second).toExecutionTrace.states := by
  induction first generalizing start with
  | nil state =>
      cases second <;>
        simp [append, toExecutionTrace,
          PresentationExecutionTrace.ExecutionTrace.states,
          RawPresentation.declareSlicesFrom]
  | @cons event rest before after final window stepSound tail
      inductionHypothesis =>
      simp only [append, toExecutionTrace,
        PresentationExecutionTrace.ExecutionTrace.states,
        RawPresentation.declareSlicesFrom, List.length_cons,
        List.mem_cons]
      right
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (start := start + 1) second

/--
Split a typed trace at an exact event-list prefix.

The existential middle state is reconstructed from the trace itself.  Both
returned traces retain their original `EventWindow` and `applyEvent`
certificates; no replay evidence is discarded or regenerated.
-/
def splitAppend
    {raw : RawPresentation}
    (firstEvents secondEvents : List SliceEvent)
    {initial final : List StrandState}
    (trace : Trace raw (firstEvents ++ secondEvents) initial final) :
    Σ middle : List StrandState,
      Trace raw firstEvents initial middle ×
        Trace raw secondEvents middle final := by
  induction firstEvents generalizing initial with
  | nil =>
      exact ⟨initial, .nil initial, trace⟩
  | cons event rest inductionHypothesis =>
      cases trace with
      | cons window stepSound tail =>
          obtain ⟨middle, prefixTrace, suffixTrace⟩ :=
            inductionHypothesis tail
          exact
            ⟨middle, .cons window stepSound prefixTrace, suffixTrace⟩

/-- Appending and then splitting recovers an extensionally identical replay. -/
theorem append_splitAppend
    {raw : RawPresentation}
    (firstEvents secondEvents : List SliceEvent)
    {initial final : List StrandState}
    (trace : Trace raw (firstEvents ++ secondEvents) initial final) :
    let split := trace.splitAppend firstEvents secondEvents
    split.2.1.append split.2.2 = trace := by
  induction firstEvents generalizing initial with
  | nil =>
      rfl
  | cons event rest inductionHypothesis =>
      cases trace with
      | cons window stepSound tail =>
          simpa [splitAppend, append] using inductionHypothesis tail

/--
An exact prefix/window/suffix decomposition of one typed canonical trace.

The three traces retain every original replay certificate.  The final field
proves that the pieces reconstruct the supplied trace; callers therefore
cannot replace the selected local window by an unrelated event script.
-/
structure ThreeWaySplit
    {raw : RawPresentation}
    (prefixEvents windowEvents suffixEvents : List SliceEvent)
    {initial final : List StrandState} where
  wholeTrace :
    Trace raw
      (prefixEvents ++ windowEvents ++ suffixEvents)
      initial final
  afterPrefix : List StrandState
  afterWindow : List StrandState
  prefixTrace :
    Trace raw prefixEvents initial afterPrefix
  windowTrace :
    Trace raw windowEvents afterPrefix afterWindow
  suffixTrace :
    Trace raw suffixEvents afterWindow final
  reassembles :
    (prefixTrace.append windowTrace).append suffixTrace = wholeTrace

/-- Compute the exact three-way split from a typed trace. -/
def splitThree
    {raw : RawPresentation}
    (prefixEvents windowEvents suffixEvents : List SliceEvent)
    {initial final : List StrandState}
    (trace :
      Trace raw
        (prefixEvents ++ windowEvents ++ suffixEvents)
        initial final) :
    ThreeWaySplit (raw := raw) (initial := initial) (final := final)
      prefixEvents windowEvents suffixEvents := by
  let outer :=
    trace.splitAppend (prefixEvents ++ windowEvents) suffixEvents
  let inner :=
    outer.2.1.splitAppend prefixEvents windowEvents
  refine
    {
      wholeTrace := trace
      afterPrefix := inner.1
      afterWindow := outer.1
      prefixTrace := inner.2.1
      windowTrace := inner.2.2
      suffixTrace := outer.2.2
      reassembles := ?_
    }
  calc
    (inner.2.1.append inner.2.2).append outer.2.2 =
        outer.2.1.append outer.2.2 := by
      rw [append_splitAppend]
    _ = trace := by
      rw [append_splitAppend]

/-- Number of canonical windows in a trace. -/
def stepCount
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState} :
    Trace raw events before final → Nat
  | .nil _ => 0
  | .cons _ _ tail => 1 + tail.stepCount

theorem stepCount_eq_event_length
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace : Trace raw events before final) :
    trace.stepCount = events.length := by
  induction trace with
  | nil =>
      rfl
  | cons window step tail inductionHypothesis =>
      simp only [stepCount, List.length_cons, inductionHypothesis,
        Nat.add_comm]

end Trace

/--
An admitted formal presentation together with its complete canonical windows.

The endpoint types force the input to be a closed link.  The declared-slice
equation reuses the exact states of the original executable schema.
-/
structure ClosedCertificate (formal : FormalPresentation) where
  trace : Trace formal.raw formal.raw.events [] []
  declared_slices_sound :
    formal.raw.declaredSlices =
      RawPresentation.declareSlicesFrom 0 trace.toExecutionTrace.states

namespace ClosedCertificate

/-- A canonical certificate gives the older execution certificate by erasure. -/
def toClosedExecutionCertificate
    {formal : FormalPresentation}
    (certificate : ClosedCertificate formal) :
    ClosedExecutionCertificate formal where
  trace := certificate.trace.toExecutionTrace
  declared_slices_sound := certificate.declared_slices_sound

/-- Every serialized event occurs in exactly one canonical local window. -/
theorem event_count
    {formal : FormalPresentation}
    (certificate : ClosedCertificate formal) :
    certificate.trace.stepCount = formal.raw.events.length :=
  certificate.trace.stepCount_eq_event_length

end ClosedCertificate

end TwistedYetter.Kirby.CanonicalKirbyTrace
