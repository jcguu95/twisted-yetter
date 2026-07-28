import TwistedYetter.Kirby.Final.Semantics.Presentation

/-!
# Semantic cancellation windows

Exact local event scripts for cancelling 1--2 and 2--3 handle pairs.
-/

namespace TwistedYetter.Kirby.Final.SemanticEightMoves

open TwistedYetter.Kirby.Presentation

/-! ## Independent cancellation local models -/

/-- Exact event identifiers used by a cancelling one--two pair. -/
structure OneTwoPairScript
    (dottedComponentId twoHandleComponentId : String) where
  dottedBirthId : String
  dottedPositiveStrand : String
  dottedNegativeStrand : String
  twoBirthId : String
  twoPositiveStrand : String
  twoNegativeStrand : String
  firstCrossingId : String
  secondCrossingId : String
  dottedDeathId : String
  twoDeathId : String

namespace OneTwoPairScript

/-- The literal isolated cancelling Hopf-pair event window. -/
def events
    {dottedComponentId twoHandleComponentId : String}
    (script : OneTwoPairScript dottedComponentId twoHandleComponentId) :
    List SliceEvent :=
  [
    .birth script.twoBirthId twoHandleComponentId
      script.twoPositiveStrand script.twoNegativeStrand 0,
    .birth script.dottedBirthId dottedComponentId
      script.dottedPositiveStrand script.dottedNegativeStrand 0,
    .crossing script.firstCrossingId
      script.dottedNegativeStrand script.twoPositiveStrand .positive,
    .crossing script.secondCrossingId
      script.twoPositiveStrand script.dottedNegativeStrand .positive,
    .death script.dottedDeathId dottedComponentId
      script.dottedPositiveStrand script.dottedNegativeStrand,
    .death script.twoDeathId twoHandleComponentId
      script.twoPositiveStrand script.twoNegativeStrand
  ]

end OneTwoPairScript

/-- Exact event identifiers for an isolated zero-framed two-handle. -/
structure TwoThreePairScript (twoHandleComponentId : String) where
  birthId : String
  positiveStrand : String
  negativeStrand : String
  deathId : String

namespace TwoThreePairScript

/-- Literal isolated zero-framed component window. -/
def events
    {twoHandleComponentId : String}
    (script : TwoThreePairScript twoHandleComponentId) :
    List SliceEvent :=
  [
    .birth script.birthId twoHandleComponentId
      script.positiveStrand script.negativeStrand 0,
    .death script.deathId twoHandleComponentId
      script.positiveStrand script.negativeStrand
  ]

end TwoThreePairScript


end TwistedYetter.Kirby.Final.SemanticEightMoves

