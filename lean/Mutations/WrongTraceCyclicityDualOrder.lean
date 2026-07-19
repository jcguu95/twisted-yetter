import TwistedYetter.Fusion.EGNOTraceCyclicity

namespace TwistedYetter.Mutations.WrongTraceCyclicityDualOrder

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/--
This must fail: cyclicity moves the cut from `f ≫ g` to `g ≫ f`; it does not
silently dualize the coupons or preserve their original order.
-/
example
    (pivotal : PivotalStructure C)
    {X : C}
    (f g : X ⟶ X) :
    pivotalTrace pivotal (f ≫ g) =
      pivotalTrace pivotal (fᘁ ≫ gᘁ) :=
  pivotalTrace_cyclic pivotal f g

end TwistedYetter.Mutations.WrongTraceCyclicityDualOrder
