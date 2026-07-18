import TwistedYetter.Kirby.KirbyCancellation

namespace TwistedYetter.Mutations.MissingTransparentTwistWitness

open TwistedYetter.Kirby.KirbyCancellation

universe u

variable {K : Type u} [Field K]

/-- This must fail: trivial twist on the transparent part is mandatory. -/
def unsafeOneTwo
    (profile : GlobalDimensionProfile (K := K))
    (pairValue cutValue : K)
    (before after : EvaluationState (K := K))
    (counts_sound : before.counts = after.counts.addOneTwo)
    (disjoint :
      True →
      before.rawNumerator = pairValue * after.rawNumerator)
    (cutting :
      True → pairValue = profile.dDimension * cutValue)
    (killing : cutValue = profile.transparentDimension) :
    OneTwoLocalCalculation profile where
  pairValue := pairValue
  cutValue := cutValue
  before := before
  after := after
  counts_sound := counts_sound
  isolated_from_rest := True
  isolated_from_rest_witness := True.intro
  disjoint_union_sound := disjoint
  transparent_twist_trivial := True
  cutting_identity := cutting
  killing_identity := killing

end TwistedYetter.Mutations.MissingTransparentTwistWitness
