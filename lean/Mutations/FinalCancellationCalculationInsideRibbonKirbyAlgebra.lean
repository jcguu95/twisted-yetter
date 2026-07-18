import TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

namespace TwistedYetter.Mutations.FinalCancellationCalculationInsideRibbonKirbyAlgebra

open CategoryTheory
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

universe uK uC vC uS uI

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
This must fail: the category algebra cannot contain a completed,
presentation-specific cancellation calculation.
-/
def unsafeFinalCalculation
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    (input : Input categoryData) :=
  input.finalCancellationCalculation

end TwistedYetter.Mutations.FinalCancellationCalculationInsideRibbonKirbyAlgebra
