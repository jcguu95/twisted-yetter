import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.ArbitraryFramingTwistPrimitive

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramingNaturality

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/--
This must fail: a fixed-twist framing event has no field accepting a
primitive made from another twist.
-/
def unsafeEvent
    (accepted other : NaturalTwist C)
    (object : C)
    {wholeSource wholeTarget : Boundary C}
    (context :
      StructuralContext C
        (.atom object) (.atom object) wholeSource wholeTarget) :
    CompiledFramingTwistEvent
      C accepted .positive wholeSource wholeTarget where
  object := object
  primitive := PrimitiveEventDiagram.twistPositive other object
  context := context

end TwistedYetter.Mutations.ArbitraryFramingTwistPrimitive
