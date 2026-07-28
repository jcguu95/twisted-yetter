import TwistedYetter.Kirby.Final.Semantics.Cancellation
import TwistedYetter.Kirby.Final.Semantics.SlideMoves

/-!
# The four semantic cancellation moves

Exact 1--2 and 2--3 birth/death constructors.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

universe uH

/-- Addition of one literal cancelling dotted-one/ordinary-two Hopf pair. -/
structure OneTwoBirth
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  dottedComponentId : String
  twoHandleComponentId : String
  ids_distinct : dottedComponentId ≠ twoHandleComponentId
  script : OneTwoPairScript dottedComponentId twoHandleComponentId
  source_is_identity_window :
    ∃ eventId order,
      replacement.sourceEventWindow = [.planarIsotopy eventId order]
  target_is_canceling_pair :
    replacement.targetEventWindow = script.events
  count_change : target.counts = source.counts.addOneTwo
  added_components_exact :
    ∃ dotted twoHandle,
      replacement.targetComponentWindow =
        replacement.sourceComponentWindow ++ [dotted, twoHandle] ∧
      dotted.componentId = dottedComponentId ∧
      dotted.role = .dotted ∧
      twoHandle.componentId = twoHandleComponentId ∧
      twoHandle.role ≠ .dotted ∧
      twoHandle.integerFraming = 0

/-- Removal of exactly the cancelling pair specified by `OneTwoBirth`. -/
structure OneTwoDeath
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  dottedComponentId : String
  twoHandleComponentId : String
  ids_distinct : dottedComponentId ≠ twoHandleComponentId
  script : OneTwoPairScript dottedComponentId twoHandleComponentId
  source_is_canceling_pair :
    replacement.sourceEventWindow = script.events
  target_is_identity_window :
    ∃ eventId order,
      replacement.targetEventWindow = [.planarIsotopy eventId order]
  count_change : source.counts = target.counts.addOneTwo
  removed_components_exact :
    ∃ dotted twoHandle,
      replacement.sourceComponentWindow =
        replacement.targetComponentWindow ++ [dotted, twoHandle] ∧
      dotted.componentId = dottedComponentId ∧
      dotted.role = .dotted ∧
      twoHandle.componentId = twoHandleComponentId ∧
      twoHandle.role ≠ .dotted ∧
      twoHandle.integerFraming = 0

/-- Addition of one isolated zero-framed two-handle and one cancelling 3-handle. -/
structure TwoThreeBirth
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  twoHandleComponentId : String
  script : TwoThreePairScript twoHandleComponentId
  source_is_identity_window :
    ∃ eventId order,
      replacement.sourceEventWindow = [.planarIsotopy eventId order]
  target_is_isolated_zero_framed :
    replacement.targetEventWindow = script.events
  count_change : target.counts = source.counts.addTwoThree
  added_component_exact :
    ∃ twoHandle,
      replacement.targetComponentWindow =
        replacement.sourceComponentWindow ++ [twoHandle] ∧
      twoHandle.componentId = twoHandleComponentId ∧
      twoHandle.role ≠ .dotted ∧
      twoHandle.integerFraming = 0

/-- Removal of exactly the isolated zero-framed component in a 2--3 pair. -/
structure TwoThreeDeath
    {H₂ : Type uH} [AddCommGroup H₂]
    (source target : Presentation H₂) where
  replacement : LocalReplacement source target
  twoHandleComponentId : String
  script : TwoThreePairScript twoHandleComponentId
  source_is_isolated_zero_framed :
    replacement.sourceEventWindow = script.events
  target_is_identity_window :
    ∃ eventId order,
      replacement.targetEventWindow = [.planarIsotopy eventId order]
  count_change : source.counts = target.counts.addTwoThree
  removed_component_exact :
    ∃ twoHandle,
      replacement.sourceComponentWindow =
        replacement.targetComponentWindow ++ [twoHandle] ∧
      twoHandle.componentId = twoHandleComponentId ∧
      twoHandle.role ≠ .dotted ∧
      twoHandle.integerFraming = 0


end TwistedYetter.Kirby.Final.SemanticEightMoves

