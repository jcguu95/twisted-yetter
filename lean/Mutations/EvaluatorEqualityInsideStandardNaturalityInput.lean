import TwistedYetter.Kirby.SourceBackedHandleChainNaturality

namespace TwistedYetter.Mutations.EvaluatorEqualityInsideStandardNaturalityInput

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality

universe uH

/--
This must fail: the homology-domain package has no categorical evaluator
field.
-/
def unsafeInput
    (H2 : Type uH) [AddCommGroup H2]
    (input : StandardHandleChainNaturality H2) :
    StandardHandleChainNaturality H2 where
  compile := input.compile
  evaluatorEquality := True

end TwistedYetter.Mutations.EvaluatorEqualityInsideStandardNaturalityInput
