import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.WrongCanonicalInverseTwist

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/-- This must fail: EGNO (8.35) uses `theta`, not `theta⁻¹`. -/
example (ribbon : RibbonStructure C) (X : C) :
    canonicalPivotalHom ribbon X =
      ribbon.toBalancedTwist.iso.inv.app X ≫ drinfeldHom X := by
  rfl

end TwistedYetter.Mutations.WrongCanonicalInverseTwist
