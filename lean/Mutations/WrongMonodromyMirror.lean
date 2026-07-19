import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.WrongMonodromyMirror

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]

/-- This must fail: positive monodromy cannot be replaced by mirror monodromy. -/
example (X Y : C) :
    monodromyHom X Y =
      (β_ Y X).inv ≫ (β_ X Y).inv := by
  rfl

end TwistedYetter.Mutations.WrongMonodromyMirror
