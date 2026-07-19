import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.WrongRecordedDualInBirthPrimitive

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/--
This must fail: a pairing for `X` and `Y` cannot silently authorize a birth
whose recorded negative strand is the unrelated object `Z`.
-/
def unsafeBirth
    (X Y Z : C)
    (pairing : ExactPairing X Y) :
    PrimitiveEventDiagram C .birth .unit
      (.tensor (.atom X) (.atom Z)) :=
  .birthRight X Y pairing

end TwistedYetter.Mutations.WrongRecordedDualInBirthPrimitive
