import TwistedYetter.Kirby.FramedSliding

/-!
This mutation must not compile.  Lemma 3.4 cannot be constructed from an
external diagram and context alone; it requires the actual Lemma 3.3 law.
-/

namespace TwistedYetter.Mutations.MissingLemma33Law

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramedSliding

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

def rejected
    {fixed X : C}
    (exterior : Diagram C (.atom X) (.atom X)) :=
  exteriorTransportMovie (fixed := fixed) exterior

end TwistedYetter.Mutations.MissingLemma33Law
