import TwistedYetter.Kirby.KirbyCancellation

namespace TwistedYetter.Mutations.ArbitraryNormalizedEqualityAsCancellation

open TwistedYetter.Kirby.KirbyCancellation

universe u

variable {K : Type u} [Field K]

/--
This must fail: a bare equality of normalized values cannot enter the closed
cancellation whitelist.
-/
def unsafeCancellation
    (profile : GlobalDimensionProfile (K := K))
    (before after : EvaluationState (K := K))
    (sound : before.normalized profile = after.normalized profile) :
    AdmittedCancellation profile before after :=
  .fromEquality sound

end TwistedYetter.Mutations.ArbitraryNormalizedEqualityAsCancellation
