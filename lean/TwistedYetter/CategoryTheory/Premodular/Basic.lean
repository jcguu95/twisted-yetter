import Mathlib.Algebra.CharZero.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TwistedYetter.CategoryTheory.Fusion.Basic
import TwistedYetter.CategoryTheory.Ribbon.Basic

/-!
# Premodular categories

This file follows EGNO, Definition 8.13.1: a premodular category is a ribbon
fusion category.  EGNO works here over an algebraically closed field of
characteristic zero; those hypotheses are therefore explicit in this class.
-/

namespace CategoryTheory

universe v uK uC uI

/--
A premodular category over `K`, following EGNO, Definition 8.13.1.

The inherited `FusionCategory` contains finite semisimplicity and rigidity; the
inherited `RibbonCategory` contains the braiding, twist, balancing equation, and
duality compatibility.
-/
class PremodularCategory
    (K : Type uK) [Field K] [IsAlgClosed K] [CharZero K]
    (C : Type uC) [Category.{v} C] [Abelian C] [Linear K C]
    [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
    [MonoidalPreadditive C] [MonoidalLinear K C]
    extends FusionCategory.{v, uK, uC, uI} K C, RibbonCategory C

end CategoryTheory
