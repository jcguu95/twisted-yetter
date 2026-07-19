import TwistedYetter.Fusion.EGNOCanonicalSpherical

namespace TwistedYetter.Mutations.WrongRibbonDualInverseTwist

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
This must fail: the ribbon law identifies the dual of `theta_X` with
`theta_(X*)`, not with its inverse.
-/
example (ribbon : RibbonStructure C) (X : C) :
    (ribbon.toBalancedTwist.iso.hom.app X)ᘁ =
      ribbon.toBalancedTwist.iso.inv.app (Xᘁ) := by
  rfl

end TwistedYetter.Mutations.WrongRibbonDualInverseTwist
