import TwistedYetter.Kirby.Presentation

/-!
This mutation must not compile.  Its death event names an inactive strand, so
the executable validator cannot prove admission.
-/

namespace TwistedYetter.Mutations.InvalidPresentationLineage

open TwistedYetter.Kirby.Presentation

def invalid : RawPresentation where
  roundTripFixture with
  events := [
    .birth "e0" "K0" "K0+" "K0-",
    .death "e1" "K0" "K0+" "not-active"
  ]

theorem rejected : invalid.validate = Except.ok () := by
  rfl

end TwistedYetter.Mutations.InvalidPresentationLineage
