import TwistedYetter.Fusion.EGNORibbon

namespace TwistedYetter.Mutations.MissingSphericalDimensionDual

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C]

/-- This must fail: pivotal data alone does not define a spherical structure. -/
def missingDimensionDual
    (pivotal : PivotalStructure C) :
    SphericalStructure (C := C) where
  toPivotalStructure := pivotal

end TwistedYetter.Mutations.MissingSphericalDimensionDual
