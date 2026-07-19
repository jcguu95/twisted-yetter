import TwistedYetter.Fusion.EGNORibbon

namespace TwistedYetter.Mutations.MissingBalancingTensor

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/-- This must fail: a natural automorphism need not satisfy balancing. -/
def missingTensorLaw
    (iso : 𝟭 C ≅ 𝟭 C) :
    BalancedTwist C where
  iso := iso

end TwistedYetter.Mutations.MissingBalancingTensor
