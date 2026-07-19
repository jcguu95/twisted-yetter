import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.ArbitraryCycleSystemAsCanonicalCompiler

open CategoryTheory
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
This must fail: the final compiler no longer has a caller-replaceable cycle
system field.
-/
def unsafeOverride
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {algebra : Input categoryData}
    (compiler :
      IntegralCharacterBoundPresentationCompiler
        categoryData manifold H2 algebra)
    (replacement : IntegralCycleRepresentativeSystem manifold H2) :
    IntegralCharacterBoundPresentationCompiler
      categoryData manifold H2 algebra :=
  { compiler with cycleSystem := replacement }

end TwistedYetter.Mutations.ArbitraryCycleSystemAsCanonicalCompiler
