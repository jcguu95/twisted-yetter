import TwistedYetter.Kirby.PresentationIsotopy

namespace TwistedYetter.Mutations.ArbitraryCertifiedMoveAsIsotopy

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Kirby.PresentationIsotopy

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
This must fail: a generic evaluator equality cannot be injected into the
closed presentation-isotopy whitelist.
-/
def arbitraryStep
    {source target : Boundary C}
    (frame : Diagram C source target) :
    GeneratedIsotopy frame frame :=
  .step (CertifiedMove.refl frame)

end TwistedYetter.Mutations.ArbitraryCertifiedMoveAsIsotopy
