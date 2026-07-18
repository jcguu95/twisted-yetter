import TwistedYetter.Kirby.KirbyCompleteness

namespace TwistedYetter.Mutations.MissingKirbyCompletenessCaveat

open TwistedYetter.Kirby.KirbyCompleteness

universe u

/-- This must fail: the special link-calculus scope caveat is mandatory. -/
def unsafeCompleteness
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type u)
    [AddCommGroup H2]
    (general : GeneralCerfCompleteness manifold)
    (connected :
      (source target : SpecialKirbyPresentation manifold H2) →
        TableTwoMovie source target) :
    TableTwoLinkCompleteness manifold H2 where
  generalCerf := general
  tableTwoConnected := connected
  link_calculus_source_refs := ["ref:unsafe"]
  link_calculus_source_locator := "unsafe"
  normal_form_statement := "unsafe"
  exact_move_scope := "unsafe"

end TwistedYetter.Mutations.MissingKirbyCompletenessCaveat
