import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.GenericCategoryBoundAsIntegralCharacterCompiler

open CategoryTheory
open TwistedYetter.Kirby.CategoryBoundKirbyColorCompiler
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
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
This must fail: the final evaluator route may not accept a category-bound
compiler whose nonzero homological coefficient is an arbitrary function.
-/
def unsafeCompiler
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : Input categoryData}
    (compiler :
      CategoryBoundPresentationCompiler
        categoryData H2 algebra) :
    IntegralCharacterBoundPresentationCompiler
      categoryData H2 algebra :=
  compiler

end TwistedYetter.Mutations.GenericCategoryBoundAsIntegralCharacterCompiler
