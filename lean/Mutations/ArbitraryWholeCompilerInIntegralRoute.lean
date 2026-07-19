import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler

namespace TwistedYetter.Mutations.ArbitraryWholeCompilerInIntegralRoute

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
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
This must fail: the final integral route has no field accepting an arbitrary
whole-event compiler. It accepts only windowed local primitive semantics.
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
    (whole :
      (topology : SpecialKirbyPresentation manifold H2) →
      (alpha : H2) →
      (labeling :
        ComponentLabelExpansion.GlobalLabeling
          (integralCharacterWeights
            (IntegralCycleRepresentativeSystem.canonical manifold H2)
            compiler.selectedGenerator.generator).toComponentExpansion
            topology) →
        CategoricalEventCompiler C topology.formal.raw) :
    IntegralCharacterBoundPresentationCompiler
      categoryData manifold H2 algebra :=
  { compiler with eventCompiler := whole }

end TwistedYetter.Mutations.ArbitraryWholeCompilerInIntegralRoute
