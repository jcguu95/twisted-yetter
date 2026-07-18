import TwistedYetter.Kirby.KirbyCancellation

namespace TwistedYetter.Mutations.MissingCancellationKillingIdentity

open TwistedYetter.Kirby.KirbyCancellation

universe u

variable {K : Type u} [Field K]

/-- This must fail: the 1--2 local calculation cannot omit killing. -/
def unsafeOneTwo
    (profile : GlobalDimensionProfile (K := K))
    (pairValue cutValue : K)
    (before after : EvaluationState (K := K))
    (counts_sound : before.counts = after.counts.addOneTwo)
    (disjoint :
      before.rawNumerator = pairValue * after.rawNumerator)
    (cutting : pairValue = profile.dDimension * cutValue) :
    OneTwoLocalCalculation profile where
  pairValue := pairValue
  cutValue := cutValue
  before := before
  after := after
  counts_sound := counts_sound
  isolated_from_rest := True
  isolated_from_rest_witness := True.intro
  disjoint_union_sound := disjoint
  cutting_identity := cutting
  transparent_twist_trivial := True
  transparent_twist_witness := True.intro

end TwistedYetter.Mutations.MissingCancellationKillingIdentity
