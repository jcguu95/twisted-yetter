import TwistedYetter.Kirby.FourManifoldInvariantTarget

namespace TwistedYetter.Mutations.DirectGeometricH2CompilerAsTargetInput

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Kirby.ConcreteMarkedPairAssembly
open TwistedYetter.Kirby.FourManifoldInvariantTarget
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBoundEvaluatorCompilation

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

/--
This must fail: the target no longer accepts a direct final identity law for
marked H2 transport.
-/
def unsafeInputs
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH)
    [AddCommGroup H2]
    (evaluatorCompiler :
      SourceBoundTableTwoEvaluatorCompiler categoryData manifold H2)
    (markedH2Compiler : GeometricMarkedH2Compiler manifold H2)
    (generalCerf : GeneralCerfCompleteness manifold)
    (basePresentation : SpecialKirbyPresentation manifold H2) :
    FourManifoldInvariantInputs categoryData manifold H2 where
  evaluatorCompiler := evaluatorCompiler
  markedH2Compiler := markedH2Compiler
  generalCerf := generalCerf
  basePresentation := basePresentation

end TwistedYetter.Mutations.DirectGeometricH2CompilerAsTargetInput
