import TwistedYetter.Kirby.KirbyCancellation

namespace TwistedYetter.Mutations.MissingPivotalCancellationDimension

open TwistedYetter.Kirby.KirbyCancellation

universe u

variable {K : Type u} [Field K]

/-- This must fail: Remark 3.11's pivotal dimension equation is mandatory. -/
def unsafeTwoThree
    (profile : GlobalDimensionProfile (K := K))
    (unknotValue : K)
    (before after : EvaluationState (K := K))
    (counts_sound : before.counts = after.counts.addTwoThree)
    (disjoint :
      before.rawNumerator = unknotValue * after.rawNumerator) :
    TwoThreeLocalCalculation profile where
  unknotValue := unknotValue
  before := before
  after := after
  counts_sound := counts_sound
  unlinked_unknotted_zero_framed := True
  unlink_witness := True.intro
  disjoint_union_sound := disjoint

end TwistedYetter.Mutations.MissingPivotalCancellationDimension
