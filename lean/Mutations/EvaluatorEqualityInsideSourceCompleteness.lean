import TwistedYetter.Kirby.SourceBackedKirbyCompleteness

namespace TwistedYetter.Mutations.EvaluatorEqualityInsideSourceCompleteness

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe u

/-- This must fail: topology completeness cannot contain evaluator equality. -/
def unsafeCompleteness
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type u) [AddCommGroup H2]
    (connected :
      (source target : SpecialKirbyPresentation manifold H2) →
        TopologicalTableTwoMovie source target)
    (evaluatorEquality : True) :
    TopologicalTableTwoCompleteness manifold H2 where
  connected := connected
  evaluatorEquality := evaluatorEquality

end TwistedYetter.Mutations.EvaluatorEqualityInsideSourceCompleteness
