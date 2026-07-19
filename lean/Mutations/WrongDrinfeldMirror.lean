import TwistedYetter.Fusion.EGNOCanonicalPivotal

namespace TwistedYetter.Mutations.WrongDrinfeldMirror

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/-- The mirror crossing has the same type but is not EGNO equation (8.30). -/
def mirrorDrinfeldHom (X : C) : X ⟶ (Xᘁ)ᘁ :=
  (ρ_ X).inv ≫
    X ◁ η_ (Xᘁ) ((Xᘁ)ᘁ) ≫
    (α_ X (Xᘁ) ((Xᘁ)ᘁ)).inv ≫
    (β_ (Xᘁ) X).inv ▷ ((Xᘁ)ᘁ) ≫
    ε_ X (Xᘁ) ▷ ((Xᘁ)ᘁ) ≫
    (λ_ ((Xᘁ)ᘁ)).hom

/-- This must fail: the mirror formula cannot definitionally replace (8.30). -/
example (X : C) : drinfeldHom X = mirrorDrinfeldHom X := by
  rfl

end TwistedYetter.Mutations.WrongDrinfeldMirror
