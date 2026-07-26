import TwistedYetter.Kirby.ComponentRibbonIsotopy
import TwistedYetter.Kirby.CanonicalTraceLocality

/-!
# Diagram determinism for canonical execution traces

This module proves that the free ribbon primitive associated to a validated
event is determined by serialized syntax and the incoming active boundary,
not by an arbitrary choice of `EventWindow` proof.

The theorem is split by event kind so each locality obligation remains small
and auditable.
-/

namespace TwistedYetter.Kirby.CanonicalTraceDiagramDeterminism

open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.CanonicalKirbyTrace
open TwistedYetter.Kirby.ComponentRibbonDiagram

/-- Canonical free primitive for a birth at one exact boundary index. -/
def canonicalBirthPrimitive
    (componentId positiveId negativeId : String)
    (insertAt : Nat)
    (before : List StrandState) :
    ComponentDiagram
      (ComponentBoundary.word
        (before.take insertAt ++ before.drop insertAt))
      (ComponentBoundary.word
        (before.take insertAt ++
          ([positiveStrand positiveId componentId,
            negativeStrand negativeId componentId] ++
              before.drop insertAt))) :=
  (ComponentDiagram.Context.surroundBoundaryWord
    (before.take insertAt) []
    [positiveStrand positiveId componentId,
      negativeStrand negativeId componentId]
    (before.drop insertAt)).plug
      (.cupPositiveNegative componentId)

/--
Every birth window is heterogeneously equal to the primitive reconstructed
from its incoming boundary and serialized insertion index.
-/
theorem birth_window_primitive_heq
    (eventId componentId positiveId negativeId : String)
    (insertAt : Nat)
    {before after : List StrandState}
    (window :
      EventWindow
        (.birth eventId componentId positiveId negativeId insertAt)
        before after) :
    HEq (EventWindow.componentPrimitive window)
      (canonicalBirthPrimitive componentId positiveId negativeId
        insertAt before) := by
  cases window
  unfold canonicalBirthPrimitive
  rw [List.take_left, List.drop_left]
  rfl

/-- Two witnesses for the same birth window compile to the same free diagram. -/
theorem birth_window_primitive_eq
    (eventId componentId positiveId negativeId : String)
    (insertAt : Nat)
    {before after : List StrandState}
    (left :
      EventWindow
        (.birth eventId componentId positiveId negativeId insertAt)
        before after)
    (right :
      EventWindow
        (.birth eventId componentId positiveId negativeId insertAt)
        before after) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  exact eq_of_heq
    ((birth_window_primitive_heq
      eventId componentId positiveId negativeId insertAt left).trans
      (birth_window_primitive_heq
        eventId componentId positiveId negativeId insertAt right).symm)

/-- Every planar marker compiles to the identity of its incoming boundary. -/
theorem planar_window_primitive_heq
    (eventId : String)
    (order : List String)
    {before after : List StrandState}
    (window :
      EventWindow (.planarIsotopy eventId order) before after) :
    HEq (EventWindow.componentPrimitive window)
      (ComponentDiagram.identity (ComponentBoundary.word before)) := by
  cases window
  rfl

/-- Two witnesses for the same planar marker compile to the same diagram. -/
theorem planar_window_primitive_eq
    (eventId : String)
    (order : List String)
    {before after : List StrandState}
    (left :
      EventWindow (.planarIsotopy eventId order) before after)
    (right :
      EventWindow (.planarIsotopy eventId order) before after) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  exact eq_of_heq
    ((planar_window_primitive_heq eventId order left).trans
      (planar_window_primitive_heq eventId order right).symm)

/-- The exact one-strand cut selected by a framing-twist window. -/
structure FramingCut
    (before : List StrandState)
    (strandId : String) where
  leading : List StrandState
  strand : StrandState
  suffix : List StrandState
  state_sound : before = leading ++ ([strand] ++ suffix)
  strand_id_sound : strand.strandId = strandId

/-- Forget the proof term while retaining the concrete framing cut. -/
def framingCut
    (eventId strandId : String)
    (sign : CrossingSign)
    {before after : List StrandState}
    (window :
      EventWindow (.framingTwist eventId strandId sign) before after) :
    FramingCut before strandId :=
  match window with
  | .framingTwist _ _ _ strand strandIdSound leading suffix =>
      ⟨leading, strand, suffix, rfl, strandIdSound⟩

/-- Active-strand uniqueness makes the framing cut unique. -/
theorem framingCut_unique
    {before : List StrandState}
    {strandId : String}
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before)
    (left right : FramingCut before strandId) :
    left = right := by
  cases left with
  | mk leftLeading leftStrand leftSuffix leftState leftId =>
      cases right with
      | mk rightLeading rightStrand rightSuffix rightState rightId =>
          obtain ⟨leadingEq, strandEq, suffixEq⟩ :=
            CanonicalTraceLocality.unique_strand_split strandId
              leftLeading rightLeading leftStrand rightStrand
              leftSuffix rightSuffix
              (leftState ▸ unique)
              (leftState.symm.trans rightState)
              leftId rightId
          subst rightLeading
          subst rightStrand
          subst rightSuffix
          rfl

/-- Free framing primitive reconstructed from the exact one-strand cut. -/
def FramingCut.primitive
    {before : List StrandState}
    {strandId : String}
    (cut : FramingCut before strandId)
    (sign : CrossingSign) :
    ComponentDiagram
      (ComponentBoundary.word
        (cut.leading ++ ([cut.strand] ++ cut.suffix)))
      (ComponentBoundary.word
        (cut.leading ++ ([cut.strand] ++ cut.suffix))) :=
  let localDiagram :=
    match sign with
    | .positive =>
        ComponentDiagram.twistPositive
          (ComponentBoundary.ofStrand cut.strand)
    | .negative =>
        ComponentDiagram.twistNegative
          (ComponentBoundary.ofStrand cut.strand)
  (ComponentDiagram.Context.surroundBoundaryWord
    cut.leading [cut.strand] [cut.strand] cut.suffix).plug
      localDiagram

/-- A framing window compiles to the primitive reconstructed from its cut. -/
theorem framing_window_primitive_cut_heq
    (eventId strandId : String)
    (sign : CrossingSign)
    {before after : List StrandState}
    (window :
      EventWindow (.framingTwist eventId strandId sign) before after) :
    HEq (EventWindow.componentPrimitive window)
      ((framingCut eventId strandId sign window).primitive sign) := by
  cases window
  rfl

/-- Two witnesses for the same framing twist compile to the same diagram. -/
theorem framing_window_primitive_eq
    (eventId strandId : String)
    (sign : CrossingSign)
    {before after : List StrandState}
    (left :
      EventWindow (.framingTwist eventId strandId sign) before after)
    (right :
      EventWindow (.framingTwist eventId strandId sign) before after)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  have cutEq :
      framingCut eventId strandId sign left =
        framingCut eventId strandId sign right :=
    framingCut_unique unique _ _
  have leftHeq :=
    framing_window_primitive_cut_heq eventId strandId sign left
  rw [cutEq] at leftHeq
  exact eq_of_heq
    (leftHeq.trans
      (framing_window_primitive_cut_heq
        eventId strandId sign right).symm)

/-- The exact adjacent ordered pair selected by a crossing window. -/
structure CrossingCut
    (before after : List StrandState)
    (overId underId : String) where
  leading : List StrandState
  over : StrandState
  under : StrandState
  suffix : List StrandState
  before_sound : before = leading ++ ([over, under] ++ suffix)
  after_sound : after = leading ++ ([under, over] ++ suffix)
  over_id_sound : over.strandId = overId
  under_id_sound : under.strandId = underId

/-- Forget the proof term while retaining the concrete crossing cut. -/
def crossingCut
    (eventId overId underId : String)
    (sign : CrossingSign)
    {before after : List StrandState}
    (window :
      EventWindow (.crossing eventId overId underId sign) before after) :
    CrossingCut before after overId underId :=
  match window with
  | .crossing _ _ _ _ overComponent underComponent
      overOrientation underOrientation leading suffix =>
      ⟨leading,
        {
          strandId := overId
          componentId := overComponent
          orientation := overOrientation
        },
        {
          strandId := underId
          componentId := underComponent
          orientation := underOrientation
        },
        suffix, rfl, rfl, rfl, rfl⟩

/-- Active-strand uniqueness makes the crossing cut unique. -/
theorem crossingCut_unique
    {before after : List StrandState}
    {overId underId : String}
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before)
    (left right : CrossingCut before after overId underId) :
    left = right := by
  cases left with
  | mk leftLeading leftOver leftUnder leftSuffix
      leftBefore leftAfter leftOverId leftUnderId =>
      cases right with
      | mk rightLeading rightOver rightUnder rightSuffix
          rightBefore rightAfter rightOverId rightUnderId =>
          obtain ⟨leadingEq, overEq, tailEq⟩ :=
            CanonicalTraceLocality.unique_strand_split overId
              leftLeading rightLeading leftOver rightOver
              (leftUnder :: leftSuffix) (rightUnder :: rightSuffix)
              (leftBefore ▸ unique)
              (leftBefore.symm.trans rightBefore)
              leftOverId rightOverId
          have underEq : leftUnder = rightUnder :=
            List.cons.inj tailEq |>.1
          have suffixEq : leftSuffix = rightSuffix :=
            List.cons.inj tailEq |>.2
          subst rightLeading
          subst rightOver
          subst rightUnder
          subst rightSuffix
          rfl

/-- Free crossing primitive reconstructed from the exact adjacent cut. -/
def CrossingCut.primitive
    {before after : List StrandState}
    {overId underId : String}
    (cut : CrossingCut before after overId underId)
    (sign : CrossingSign) :
    ComponentDiagram
      (ComponentBoundary.word
        (cut.leading ++ ([cut.over, cut.under] ++ cut.suffix)))
      (ComponentBoundary.word
        (cut.leading ++ ([cut.under, cut.over] ++ cut.suffix))) :=
  let localDiagram :=
    match sign with
    | .positive =>
        ComponentDiagram.crossingPositive
          (.atom (ComponentBoundary.ofStrand cut.over))
          (.atom (ComponentBoundary.ofStrand cut.under))
    | .negative =>
        ComponentDiagram.crossingNegative
          (.atom (ComponentBoundary.ofStrand cut.over))
          (.atom (ComponentBoundary.ofStrand cut.under))
  (ComponentDiagram.Context.surroundBoundaryWord
    cut.leading [cut.over, cut.under]
      [cut.under, cut.over] cut.suffix).plug localDiagram

/-- A crossing window compiles to the primitive reconstructed from its cut. -/
theorem crossing_window_primitive_cut_heq
    (eventId overId underId : String)
    (sign : CrossingSign)
    {before after : List StrandState}
    (window :
      EventWindow (.crossing eventId overId underId sign) before after) :
    HEq (EventWindow.componentPrimitive window)
      ((crossingCut eventId overId underId sign window).primitive sign) := by
  cases window
  rfl

/-- Two witnesses for the same crossing compile to the same diagram. -/
theorem crossing_window_primitive_eq
    (eventId overId underId : String)
    (sign : CrossingSign)
    {before after : List StrandState}
    (left :
      EventWindow (.crossing eventId overId underId sign) before after)
    (right :
      EventWindow (.crossing eventId overId underId sign) before after)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  have cutEq :
      crossingCut eventId overId underId sign left =
        crossingCut eventId overId underId sign right :=
    crossingCut_unique unique _ _
  have leftHeq :=
    crossing_window_primitive_cut_heq
      eventId overId underId sign left
  rw [cutEq] at leftHeq
  exact eq_of_heq
    (leftHeq.trans
      (crossing_window_primitive_cut_heq
        eventId overId underId sign right).symm)

/-- The two possible orientation orders of an accepted death pair. -/
inductive OrientedDeathPair (componentId : String) where
  | positiveNegative (positiveId negativeId : String)
  | negativePositive (negativeId positiveId : String)

/-- First strand of an oriented death pair. -/
def OrientedDeathPair.first
    {componentId : String} :
    OrientedDeathPair componentId → StrandState
  | .positiveNegative positiveId _ =>
      positiveStrand positiveId componentId
  | .negativePositive negativeId _ =>
      negativeStrand negativeId componentId

/-- Second strand of an oriented death pair. -/
def OrientedDeathPair.second
    {componentId : String} :
    OrientedDeathPair componentId → StrandState
  | .positiveNegative _ negativeId =>
      negativeStrand negativeId componentId
  | .negativePositive _ positiveId =>
      positiveStrand positiveId componentId

/-- An oriented death pair is determined by its two concrete strands. -/
theorem OrientedDeathPair.eq_of_first_second_eq
    {componentId : String}
    {left right : OrientedDeathPair componentId}
    (firstEq : left.first = right.first)
    (secondEq : left.second = right.second) :
    left = right := by
  cases left <;> cases right
  · simp only [first, positiveStrand, StrandState.mk.injEq] at firstEq
    simp only [second, negativeStrand, StrandState.mk.injEq] at secondEq
    cases firstEq.1
    cases secondEq.1
    rfl
  · simp only [first, positiveStrand, negativeStrand,
      StrandState.mk.injEq] at firstEq
    exact Orientation.noConfusion firstEq.2.2
  · simp only [first, positiveStrand, negativeStrand,
      StrandState.mk.injEq] at firstEq
    exact Orientation.noConfusion firstEq.2.2
  · simp only [first, negativeStrand, StrandState.mk.injEq] at firstEq
    simp only [second, positiveStrand, StrandState.mk.injEq] at secondEq
    cases firstEq.1
    cases secondEq.1
    rfl

/-- The exact adjacent oriented pair deleted by a death event. -/
structure DeathCut
    (before after : List StrandState)
    (componentId firstId secondId : String) where
  leading : List StrandState
  pair : OrientedDeathPair componentId
  suffix : List StrandState
  before_sound :
    before = leading ++ ([pair.first, pair.second] ++ suffix)
  after_sound : after = leading ++ suffix
  listed_ids_sound :
    RawPresentation.sameStringSet
      [pair.first.strandId, pair.second.strandId]
      [firstId, secondId] = true

/-- Forget the proof term while retaining the concrete death cut. -/
def deathCut
    (eventId componentId firstId secondId : String)
    {before after : List StrandState}
    (window :
      EventWindow
        (.death eventId componentId firstId secondId) before after) :
    DeathCut before after componentId firstId secondId :=
  match window with
  | .deathPositiveNegative _ _ _ _ positiveId negativeId
      listed leading suffix =>
      ⟨leading, .positiveNegative positiveId negativeId, suffix,
        rfl, rfl, listed⟩
  | .deathNegativePositive _ _ _ _ negativeId positiveId
      listed leading suffix =>
      ⟨leading, .negativePositive negativeId positiveId, suffix,
        rfl, rfl, listed⟩

/-- Active-strand uniqueness makes the deletion cut and orientation order unique. -/
theorem deathCut_unique
    {before after : List StrandState}
    {componentId firstId secondId : String}
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before)
    (left right :
      DeathCut before after componentId firstId secondId) :
    left = right := by
  cases left with
  | mk leftLeading leftPair leftSuffix leftBefore leftAfter leftListed =>
      cases right with
      | mk rightLeading rightPair rightSuffix
          rightBefore rightAfter rightListed =>
          obtain ⟨leadingEq, firstEq, secondEq, suffixEq⟩ :=
            CanonicalTraceLocality.unique_adjacent_pair_deletion_split
              leftLeading rightLeading
              leftPair.first leftPair.second
              rightPair.first rightPair.second
              leftSuffix rightSuffix
              (List.Nodup.of_map StrandState.strandId
                (leftBefore ▸ unique))
              (leftBefore.symm.trans rightBefore)
              (leftAfter.symm.trans rightAfter)
          have pairEq : leftPair = rightPair :=
            OrientedDeathPair.eq_of_first_second_eq firstEq secondEq
          subst rightLeading
          subst rightPair
          subst rightSuffix
          rfl

/-- The canonical cap for an oriented death pair. -/
def OrientedDeathPair.localPrimitive
    {componentId : String}
    (pair : OrientedDeathPair componentId) :
    ComponentDiagram
      (ComponentBoundary.word [pair.first, pair.second])
      ComponentBoundary.unit :=
  match pair with
  | .positiveNegative _ _ =>
      .capPositiveNegative componentId
  | .negativePositive _ _ =>
      .capNegativePositive componentId

/-- Free death primitive reconstructed from the exact deletion cut. -/
def DeathCut.primitive
    {before after : List StrandState}
    {componentId firstId secondId : String}
    (cut : DeathCut before after componentId firstId secondId) :
    ComponentDiagram
      (ComponentBoundary.word
        (cut.leading ++
          ([cut.pair.first, cut.pair.second] ++ cut.suffix)))
      (ComponentBoundary.word (cut.leading ++ cut.suffix)) :=
  (ComponentDiagram.Context.surroundBoundaryWord
    cut.leading [cut.pair.first, cut.pair.second] [] cut.suffix).plug
      cut.pair.localPrimitive

/-- A death window compiles to the primitive reconstructed from its cut. -/
theorem death_window_primitive_cut_heq
    (eventId componentId firstId secondId : String)
    {before after : List StrandState}
    (window :
      EventWindow
        (.death eventId componentId firstId secondId) before after) :
    HEq (EventWindow.componentPrimitive window)
      (deathCut eventId componentId firstId secondId window).primitive := by
  cases window <;> rfl

/-- Two witnesses for the same accepted death compile to the same diagram. -/
theorem death_window_primitive_eq
    (eventId componentId firstId secondId : String)
    {before after : List StrandState}
    (left :
      EventWindow
        (.death eventId componentId firstId secondId) before after)
    (right :
      EventWindow
        (.death eventId componentId firstId secondId) before after)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  have cutEq :
      deathCut eventId componentId firstId secondId left =
        deathCut eventId componentId firstId secondId right :=
    deathCut_unique unique _ _
  have leftHeq :=
    death_window_primitive_cut_heq
      eventId componentId firstId secondId left
  rw [cutEq] at leftHeq
  exact eq_of_heq
    (leftHeq.trans
      (death_window_primitive_cut_heq
        eventId componentId firstId secondId right).symm)

/-- The exact nonempty strand window selected by an identity-coupon event. -/
structure CouponCut
    (before : List StrandState)
    (strands : List String) where
  leading : List StrandState
  window : List StrandState
  suffix : List StrandState
  state_sound : before = leading ++ (window ++ suffix)
  strand_ids_sound : RawPresentation.activeIds window = strands

/-- Forget the proof term while retaining the concrete coupon cut. -/
def couponCut
    (eventId couponId label : String)
    (strands : List String)
    {before after : List StrandState}
    (window :
      EventWindow (.coupon eventId couponId label strands) before after) :
    CouponCut before strands :=
  match window with
  | .identityCoupon _ _ localWindow leading suffix =>
      ⟨leading, localWindow, suffix, rfl, rfl⟩

/-- A nonempty serialized strand list forces the selected coupon window to be nonempty. -/
theorem couponCut_window_nonempty
    {before : List StrandState}
    {strands : List String}
    (cut : CouponCut before strands)
    (strandsNonempty : strands ≠ []) :
    cut.window ≠ [] := by
  intro windowEmpty
  have idsSound := cut.strand_ids_sound
  rw [windowEmpty] at idsSound
  simp [RawPresentation.activeIds] at idsSound
  exact strandsNonempty idsSound

/-- Active-strand uniqueness makes a nonempty coupon cut unique. -/
theorem couponCut_unique
    {before : List StrandState}
    {strands : List String}
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before)
    (strandsNonempty : strands ≠ [])
    (left right : CouponCut before strands) :
    left = right := by
  cases left with
  | mk leftLeading leftWindow leftSuffix leftState leftIds =>
      cases right with
      | mk rightLeading rightWindow rightSuffix rightState rightIds =>
          obtain ⟨leadingEq, windowEq, suffixEq⟩ :=
            CanonicalTraceLocality.unique_nonempty_window_split
              leftLeading rightLeading leftWindow rightWindow
              leftSuffix rightSuffix
              (leftState ▸ unique)
              (leftState.symm.trans rightState)
              (leftIds.trans rightIds.symm)
              (by
                intro leftEmpty
                rw [leftEmpty] at leftIds
                simp [RawPresentation.activeIds] at leftIds
                exact strandsNonempty leftIds)
          subst rightLeading
          subst rightWindow
          subst rightSuffix
          rfl

/-- Free identity-coupon primitive reconstructed from its exact window. -/
def CouponCut.primitive
    {before : List StrandState}
    {strands : List String}
    (cut : CouponCut before strands)
    (couponId : String) :
    ComponentDiagram
      (ComponentBoundary.word
        (cut.leading ++ (cut.window ++ cut.suffix)))
      (ComponentBoundary.word
        (cut.leading ++ (cut.window ++ cut.suffix))) :=
  (ComponentDiagram.Context.surroundBoundaryWord
    cut.leading cut.window cut.window cut.suffix).plug
      (.identityCoupon couponId
        (ComponentBoundary.word cut.window))

/-- A coupon window compiles to the primitive reconstructed from its cut. -/
theorem coupon_window_primitive_cut_heq
    (eventId couponId label : String)
    (strands : List String)
    {before after : List StrandState}
    (window :
      EventWindow (.coupon eventId couponId label strands) before after) :
    HEq (EventWindow.componentPrimitive window)
      ((couponCut eventId couponId label strands window).primitive
        couponId) := by
  cases window
  rfl

/-- Two witnesses for the same accepted coupon compile to the same diagram. -/
theorem coupon_window_primitive_eq
    (eventId couponId label : String)
    (strands : List String)
    {before after : List StrandState}
    (left :
      EventWindow (.coupon eventId couponId label strands) before after)
    (right :
      EventWindow (.coupon eventId couponId label strands) before after)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before)
    (strandsNonempty : strands ≠ []) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  have cutEq :
      couponCut eventId couponId label strands left =
        couponCut eventId couponId label strands right :=
    couponCut_unique unique strandsNonempty _ _
  have leftHeq :=
    coupon_window_primitive_cut_heq
      eventId couponId label strands left
  rw [cutEq] at leftHeq
  exact eq_of_heq
    (leftHeq.trans
      (coupon_window_primitive_cut_heq
        eventId couponId label strands right).symm)

/--
Every pair of accepted witnesses for one serialized event compiles to the
same free diagram.  The executable step is used only to recover the coupon's
validated nonemptiness condition.
-/
theorem EventWindow.componentPrimitive_eq
    {raw : RawPresentation}
    {event : SliceEvent}
    {before after : List StrandState}
    (left right : EventWindow event before after)
    (step : raw.applyEvent before event = Except.ok after)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before) :
    EventWindow.componentPrimitive left =
      EventWindow.componentPrimitive right := by
  cases event with
  | birth eventId componentId positiveId negativeId insertAt =>
      exact
        birth_window_primitive_eq
          eventId componentId positiveId negativeId insertAt left right
  | death eventId componentId firstId secondId =>
      exact
        death_window_primitive_eq
          eventId componentId firstId secondId left right unique
  | crossing eventId overId underId sign =>
      exact
        crossing_window_primitive_eq
          eventId overId underId sign left right unique
  | coupon eventId couponId label strands =>
      exact
        coupon_window_primitive_eq
          eventId couponId label strands left right unique
          (CanonicalTraceLocality.coupon_step_strands_nonempty
            raw before after eventId couponId label strands step)
  | framingTwist eventId strandId sign =>
      exact
        framing_window_primitive_eq
          eventId strandId sign left right unique
  | planarIsotopy eventId order =>
      exact
        planar_window_primitive_eq eventId order left right

/--
Two validated traces with equal event lists and equal endpoints compile to
the same free component diagram, even when their presentation records differ.
-/
theorem Trace.componentDiagram_eq_of_same_events
    {leftRaw rightRaw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState}
    (left : Trace leftRaw events before final)
    (right : Trace rightRaw events before final)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before) :
    Trace.componentDiagram left = Trace.componentDiagram right := by
  induction left generalizing rightRaw with
  | nil =>
      cases right
      rfl
  | cons leftWindow leftStep leftTail inductionHypothesis =>
      cases right with
      | cons rightWindow rightStep rightTail =>
          have middleEq :=
            CanonicalTraceLocality.applyEvent_ok_target_eq _ _ _ _ _ _
              leftStep rightStep
          subst middleEq
          have primitiveEq :
              EventWindow.componentPrimitive leftWindow =
                EventWindow.componentPrimitive rightWindow :=
            EventWindow.componentPrimitive_eq
              leftWindow rightWindow leftStep unique
          have middleUnique :=
            CanonicalTraceLocality.EventWindow.preserves_activeIdsUnique
              leftWindow leftStep unique
          rw [Trace.componentDiagram, Trace.componentDiagram,
            primitiveEq,
            inductionHypothesis rightTail middleUnique]

/--
Validated traces with propositionally equal serialized event lists compile to
the same free diagram.
-/
theorem Trace.componentDiagram_eq_of_events_eq
    {leftRaw rightRaw : RawPresentation}
    {leftEvents rightEvents : List SliceEvent}
    {before final : List StrandState}
    (eventsEq : leftEvents = rightEvents)
    (left : Trace leftRaw leftEvents before final)
    (right : Trace rightRaw rightEvents before final)
    (unique :
      CanonicalTraceLocality.ActiveIdsUnique before) :
    Trace.componentDiagram left = Trace.componentDiagram right := by
  cases eventsEq
  exact Trace.componentDiagram_eq_of_same_events left right unique

end TwistedYetter.Kirby.CanonicalTraceDiagramDeterminism
