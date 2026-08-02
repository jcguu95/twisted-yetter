import TwistedYetter.CategoryTheory.Premodular.Basic
import TwistedYetter.CategoryTheory.Ribbon.CanonicalSpherical

/-!
# The canonical spherical structure on a premodular category

This is the ribbon-to-spherical direction of EGNO, Proposition 8.10.12,
specialized to the ribbon fusion category in Definition 8.13.1.
-/

namespace CategoryTheory

universe v uK uC uI

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{v} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable [PremodularCategory.{v, uK, uC, uI} K C]

local instance premodularCanonicalRightRigidCategory : RightRigidCategory C :=
  RigidCategory.toRightRigidCategory

local instance premodularCanonicalDoubleDualMonoidal :
    (rightDoubleDualFunctor C).Monoidal :=
  drinfeldDoubleDualMonoidal (C := C)

/-- Every premodular category has the canonical spherical structure. -/
noncomputable def PremodularCategory.canonicalSphericalStructure :
    SphericalStructure (C := C) :=
  CategoryTheory.canonicalSphericalStructure
    (PremodularCategory.toRibbonCategory (K := K) (C := C)).ribbonStructure

end CategoryTheory
