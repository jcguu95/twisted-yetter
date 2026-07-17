import TwistedYetter.Kirby.Presentation

/-!
This mutation must not compile.  Raw JSON-shaped data does not become a
formal presentation unless the executable validator's proof is supplied.
-/

namespace TwistedYetter.Mutations.MissingPresentationAdmission

open TwistedYetter.Kirby.Presentation

def rejected : FormalPresentation where
  raw := roundTripFixture

end TwistedYetter.Mutations.MissingPresentationAdmission
