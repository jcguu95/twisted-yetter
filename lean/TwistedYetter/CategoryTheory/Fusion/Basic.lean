import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import TwistedYetter.CategoryTheory.FiniteSemisimple.Basic

/-!
# Fusion categories

This is an upstream-shaped definition built entirely on Mathlib's category,
abelian, linear, monoidal, and rigid structures.
-/

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

universe v uK uC uI

/--
A fusion category over `K` is a finite semisimple `K`-linear rigid monoidal
category with simple tensor unit.

Over an algebraically closed field this is the standard form equivalent to
EGNO, Definition 4.1.1.
-/
class FusionCategory
    (K : Type uK) [Field K]
    (C : Type uC) [Category.{v} C] [Abelian C] [Linear K C]
    [MonoidalCategory C] [RigidCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    : Prop extends FiniteSemisimpleCategory.{v, uK, uC, uI} K C where
  tensorUnit_simple : Simple (𝟙_ C)

end CategoryTheory
