import TwistedYetter.Fusion.EGNOCanonicalSpherical

namespace TwistedYetter.Mutations.WrongRibbonLoopMirror

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/-- This must fail: EGNO equation (8.41) uses the positive crossing. -/
example (twist : BalancedTwist C) (X : C) :
    ribbonLoop twist X =
      η_ X (Xᘁ) ≫
        (twist.iso.hom.app X ⊗ₘ 𝟙 (Xᘁ)) ≫
        (β_ (Xᘁ) X).inv ≫
        ε_ X (Xᘁ) := by
  rfl

end TwistedYetter.Mutations.WrongRibbonLoopMirror
