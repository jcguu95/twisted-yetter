import TwistedYetter.Fusion.EGNORibbon

namespace TwistedYetter.Mutations.MissingPivotalMonoidality

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C]

/-- This must fail: a natural double-dual isomorphism is not yet pivotal. -/
def missingMonoidality
    (doubleDualMonoidal : (rightDoubleDualFunctor C).Monoidal)
    (iso : 𝟭 C ≅ rightDoubleDualFunctor C) :
    PivotalStructure C where
  doubleDualMonoidal := doubleDualMonoidal
  iso := iso

end TwistedYetter.Mutations.MissingPivotalMonoidality
