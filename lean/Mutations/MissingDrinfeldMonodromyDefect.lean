import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.MissingDrinfeldMonodromyDefect

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RightRigidCategory C]

/--
This must fail: the Drinfeld morphism is not monoidal by itself; its defect is
the positive double braiding.
-/
example (X Y : C) :
    (drinfeldHom X ⊗ₘ drinfeldHom Y) ≫
        @Functor.LaxMonoidal.μ C _ _ C _ _
          (rightDoubleDualFunctor C)
          (drinfeldDoubleDualMonoidal (C := C)).toLaxMonoidal X Y =
      drinfeldHom (X ⊗ Y) := by
  rfl

end TwistedYetter.Mutations.MissingDrinfeldMonodromyDefect
