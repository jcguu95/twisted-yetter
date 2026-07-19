import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.WrongDrinfeldNaturalityTarget

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
This must fail: naturality lands in the double right dual and therefore uses
`f**`; replacing it by the single dual `f*` is not even a well-typed square.
-/
example {X Y : C} (f : X ⟶ Y) :
    f ≫ drinfeldHom Y =
      drinfeldHom X ≫ (fᘁ : (Yᘁ) ⟶ (Xᘁ)) := by
  exact drinfeldHom_naturality f

end TwistedYetter.Mutations.WrongDrinfeldNaturalityTarget
