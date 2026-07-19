import TwistedYetter.Fusion.EGNOTraceCyclicity

namespace TwistedYetter.Mutations.ObjectwisePivotalMapsDoNotGiveTraceCyclicity

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/--
This must fail: objectwise arrows have no naturality or monoidality witness and
therefore cannot be used as a pivotal structure in the cyclicity theorem.
-/
example
    (maps : (X : C) → X ⟶ (Xᘁ)ᘁ)
    {X Y : C}
    (f : X ⟶ Y)
    (g : Y ⟶ X) :
    pivotalTrace maps (f ≫ g) = pivotalTrace maps (g ≫ f) :=
  pivotalTrace_cyclic maps f g

end TwistedYetter.Mutations.ObjectwisePivotalMapsDoNotGiveTraceCyclicity
