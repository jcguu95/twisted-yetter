import TwistedYetter.Fusion.EGNORibbon

/-!
# The EGNO canonical pivotal morphism

This module fixes the non-strict form of the Drinfeld morphism from EGNO
equation (8.30), printed page 214. For a ribbon twist `theta`, the candidate
canonical pivotal component is `theta_X` followed by the Drinfeld morphism, as
in EGNO equation (8.35) and Proposition 8.10.12.

Only the objectwise morphisms are defined here. Naturality, invertibility,
monoidality, and sphericality are separate obligations and are not claimed by
this module.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

section Drinfeld

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [RigidCategory C]

/--
The Drinfeld morphism `u_X : X ⟶ X**` from EGNO equation (8.30).

The explicit associator and unitor factors are the non-strict expansion of

`X --id tensor coev_(X*)--> X tensor X* tensor X**
   --c_(X,X*) tensor id--> X* tensor X tensor X**
   --ev_X tensor id--> X**`.
-/
def drinfeldHom (X : C) : X ⟶ (Xᘁ)ᘁ :=
  (ρ_ X).inv ≫
    X ◁ η_ (Xᘁ) ((Xᘁ)ᘁ) ≫
    (α_ X (Xᘁ) ((Xᘁ)ᘁ)).inv ≫
    (β_ X (Xᘁ)).hom ▷ ((Xᘁ)ᘁ) ≫
    ε_ X (Xᘁ) ▷ ((Xᘁ)ᘁ) ≫
    (λ_ ((Xᘁ)ᘁ)).hom

/--
The objectwise canonical pivotal candidate attached to a ribbon twist.

Composition in Lean is left-to-right, so this is the conventional
`u_X ◦ theta_X` written as `theta_X ≫ u_X`.
-/
def canonicalPivotalHom (ribbon : RibbonStructure C) (X : C) :
    X ⟶ (Xᘁ)ᘁ :=
  ribbon.toBalancedTwist.iso.hom.app X ≫ drinfeldHom X

/-- The composition order is fixed and visible to downstream audits. -/
theorem canonicalPivotalHom_eq (ribbon : RibbonStructure C) (X : C) :
    canonicalPivotalHom ribbon X =
      ribbon.toBalancedTwist.iso.hom.app X ≫ drinfeldHom X :=
  rfl

end Drinfeld

end TwistedYetter.Fusion.EGNO
