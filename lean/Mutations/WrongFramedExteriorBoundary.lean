import TwistedYetter.Kirby.FramedEncirclingTransport

/-!
This mutation must not compile.  A visible exterior with boundary `X -> Y`
cannot be inserted into a framed sliding context whose hole expects `X -> X`.
-/

namespace TwistedYetter.Mutations.WrongFramedExteriorBoundary

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramedEncirclingTransport
open TwistedYetter.Kirby.HandleSlide

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

def rejected
    {fixed X Y : C}
    (law : SourcedTensorLeftEncirclingLaw fixed)
    (exterior : Diagram C (.atom X) (.atom Y))
    (context :
      Context C
        (.atom (fixed ⊗ X))
        (.atom (fixed ⊗ X))
        .unit .unit) :=
  exteriorTransportInContext law exterior context

end TwistedYetter.Mutations.WrongFramedExteriorBoundary
