import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.WrongDoubleDualOrder

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/--
This must fail: a morphism to the left double dual cannot silently be installed
as a morphism to the chosen right double dual.
-/
def wrongDoubleDualOrder (X : C) (candidate : X ⟶ ᘁ(ᘁX)) :
    X ⟶ (Xᘁ)ᘁ :=
  candidate

end TwistedYetter.Mutations.WrongDoubleDualOrder
