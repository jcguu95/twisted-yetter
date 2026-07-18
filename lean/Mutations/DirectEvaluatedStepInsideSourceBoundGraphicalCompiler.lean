import TwistedYetter.Kirby.SourceBoundGraphicalMoveCompiler

namespace TwistedYetter.Mutations.DirectEvaluatedStepInsideSourceBoundGraphicalCompiler

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
open TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation

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

/-
This must fail: the lower-level compiler has no field accepting a completed
`EvaluatedTableTwoStep`.
-/
def unsafeCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold :
      TwistedYetter.Kirby.KirbyCompleteness.ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (presentationCompiler :
      ComponentwiseFiniteLabelPresentationCompiler
        categoryData manifold H2)
    (algebra :
      TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra.Input categoryData)
    (base :
      SourceBoundGraphicalMoveCompiler
        categoryData manifold H2 presentationCompiler algebra) :
    SourceBoundGraphicalMoveCompiler
      categoryData manifold H2 presentationCompiler algebra :=
  { base with evaluatedStep := True }

end TwistedYetter.Mutations.DirectEvaluatedStepInsideSourceBoundGraphicalCompiler
