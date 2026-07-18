import TwistedYetter.Kirby.KirbyHandleMoves

namespace TwistedYetter.Mutations.ArbitraryCertifiedMoveAsHandleSlide

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.CategoricalMovie
open TwistedYetter.Kirby.KirbyHandleMoves

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/--
This must fail: the closed Kirby-slide family has no constructor accepting an
arbitrary evaluator-preserving move.
-/
def arbitraryStep
    {source target : Boundary C}
    {before after : Diagram C source target}
    (move : CertifiedMove before after) :
    OrdinaryHandleSlide before after :=
  .step move

end TwistedYetter.Mutations.ArbitraryCertifiedMoveAsHandleSlide
