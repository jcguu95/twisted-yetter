import TwistedYetter.Fusion.EGNORibbon

/-!
# Minimal-assumption regression for the right double-dual functor

The functor `(**)` uses only chosen right duals. This module deliberately has
no braiding and no left-rigid assumption, preventing a future refactor from
reintroducing a right/left/right instance diamond.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory

universe u v

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]

/-- The right double-dual functor is available from right rigidity alone. -/
example : C ⥤ C := rightDoubleDualFunctor C

/-- Its morphism action uses the same chosen right dual twice. -/
example {X Y : C} (f : X ⟶ Y) :
    (rightDoubleDualFunctor C).map f = (fᘁ)ᘁ :=
  rfl

end TwistedYetter.Fusion.EGNO
