import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.WrongPositiveCrossingEventPrimitive

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/-- This must fail: a positive raw crossing cannot compile to inverse braiding. -/
def wrongPrimitive
    (left right : Boundary C) :
    PrimitiveEventDiagram C .crossingPositive
      (.tensor left right) (.tensor right left) :=
  PrimitiveEventDiagram.crossingNegative left right

end TwistedYetter.Mutations.WrongPositiveCrossingEventPrimitive
