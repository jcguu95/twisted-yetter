import TwistedYetter.Fusion.EGNOCanonicalSpherical

namespace TwistedYetter.Mutations.BalancedTwistIsNotSpherical

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
This must fail: balancing alone has no dual-twist law and therefore does not
authorize the canonical spherical construction.
-/
example (twist : BalancedTwist C) :
    SphericalStructure (C := C) :=
  canonicalSphericalStructure twist

end TwistedYetter.Mutations.BalancedTwistIsNotSpherical
