import TwistedYetter.Kirby.HomologicallyTwistedInvariant

namespace TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.KirbyHandleMoves

universe uC vC

variable {C : Type uC} [Category.{vC} C]
variable [MonoidalCategory C] [BraidedCategory C]

example
    {source target : Boundary C}
    {before after : Diagram C source target}
    (slide : OrdinaryHandleSlide before after)
    (wrong :
      (ordinarySlideMetadata slide).kind = .twoOverOne) :
    (ordinarySlideMetadata slide).kind = .oneOverOne :=
  wrong

end TwistedYetter.Kirby.HomologicallyTwistedInvariant.Mutations
