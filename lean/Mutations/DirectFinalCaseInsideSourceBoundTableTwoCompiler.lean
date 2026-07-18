import TwistedYetter.Kirby.SourceBoundTableTwoEvaluatorCompiler

namespace TwistedYetter.Mutations.DirectFinalCaseInsideSourceBoundTableTwoCompiler

open CategoryTheory
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.SourceBoundEvaluatorCompilation

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
This must fail: the final source-bound compiler no longer exposes a direct
`framedIsotopy` proof field. All eight cases come from `moveCompiler`.
-/
def unsafeCompiler
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold :
      TwistedYetter.Kirby.KirbyCompleteness.ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (base :
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2) :
    SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2 :=
  { base with framedIsotopy := True }

end TwistedYetter.Mutations.DirectFinalCaseInsideSourceBoundTableTwoCompiler
