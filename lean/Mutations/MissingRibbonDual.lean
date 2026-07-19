import TwistedYetter.Fusion.EGNORibbon

namespace TwistedYetter.Mutations.MissingRibbonDual

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/-- This must fail: a balanced twist is ribbon only after dual compatibility. -/
def missingDualLaw
    (balanced : BalancedTwist C) :
    RibbonStructure C where
  toBalancedTwist := balanced

end TwistedYetter.Mutations.MissingRibbonDual
