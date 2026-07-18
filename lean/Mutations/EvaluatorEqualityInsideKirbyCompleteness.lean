import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.EvaluatorEqualityInsideKirbyCompleteness

open TwistedYetter.Kirby.KirbyCompleteness

universe u

/--
This must fail: topology completeness cannot contain a pre-written evaluator
equality.
-/
def unsafeCompleteness
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type u)
    (general : GeneralCerfCompleteness manifold)
    (connected :
      (source target : SpecialKirbyPresentation manifold H2) →
        TableTwoMovie source target)
    (evaluatorEquality : True) :
    TableTwoLinkCompleteness manifold H2 where
  generalCerf := general
  tableTwoConnected := connected
  link_calculus_source_refs := ["ref:unsafe"]
  link_calculus_source_locator := "unsafe"
  normal_form_statement := "unsafe"
  exact_move_scope := "unsafe"
  source_scope_caveat := "unsafe"
  evaluatorEquality := evaluatorEquality

end TwistedYetter.Mutations.EvaluatorEqualityInsideKirbyCompleteness
