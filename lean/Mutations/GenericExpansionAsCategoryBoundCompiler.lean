import TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler

namespace TwistedYetter.Mutations.GenericExpansionAsCategoryBoundCompiler

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [RightRigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
This must fail: the final route does not accept the older generic expansion
as a category-bound compiler.
-/
def unsafeCompiler
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : Input categoryData}
    (generic :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2) :
    CategoryBoundPresentationCompiler
      categoryData manifold H2 algebra :=
  generic

end TwistedYetter.Mutations.GenericExpansionAsCategoryBoundCompiler
