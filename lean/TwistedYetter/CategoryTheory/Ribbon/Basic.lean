import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Balancing and ribbon structures

These definitions follow EGNO, Definition 8.10.1.  A balancing is a natural
automorphism of the identity satisfying equation (8.32).  It is a ribbon
structure when it is compatible with duality.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  [RigidCategory C] [BraidedCategory C]

/--
A twist, or balancing transformation, in the sense of EGNO, Definition 8.10.1.

Composition is written in diagrammatic order in Lean, so `f ≫ g` denotes the
composite which first applies `f` and then `g`.
-/
structure Balancing where
  /-- The natural automorphism `θ : 𝟭 C ≅ 𝟭 C`. -/
  twist : 𝟭 C ≅ 𝟭 C
  /-- EGNO equation (8.32). -/
  tensor (X Y : C) :
    twist.hom.app (X ⊗ Y) =
      (β_ X Y).hom ≫ (β_ Y X).hom ≫
        (twist.hom.app X ⊗ₘ twist.hom.app Y)

/--
A ribbon structure in the sense of EGNO, Definition 8.10.1: a balancing whose
twist commutes with the chosen right duality.
-/
structure RibbonStructure extends Balancing C where
  duality (X : C) :
    (twist.hom.app X)ᘁ = twist.hom.app (Xᘁ)

/-- A braided rigid monoidal category equipped with a ribbon structure. -/
class RibbonCategory where
  ribbonStructure : RibbonStructure C

end CategoryTheory
