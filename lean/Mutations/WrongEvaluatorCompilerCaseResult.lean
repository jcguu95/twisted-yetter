import TwistedYetter.Kirby.TableTwoEvaluatorCompiler

namespace TwistedYetter.Kirby.EvaluatorCompiler.Mutations

open CategoryTheory
open TwistedYetter.Kirby.KirbyColorEncirclingTransport
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uS uI uH

variable {K : Type uK} [Field K]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type uS} [Fintype S] [DecidableEq S]
variable {I : S → S → Type uI}
variable [∀ y z, Fintype (I y z)]
variable [∀ y z, DecidableEq (I y z)]

example
    (categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I))
    (H2 : Type uH) [AddCommGroup H2]
    (compiler :
      TableTwoEvaluatorCompiler categoryData H2)
    {source target : SpecialKirbyPresentation H2}
    (orientation : BandOrientation)
    (metadata : TableTwoMoveMetadata .oneOverOne source target)
    (counts : source.counts = target.counts)
    (transport : MarkedH2Transport source target)
    (alpha : H2) :
    EvaluatedTableTwoStep
      categoryData (compiler.evaluation source)
        (compiler.evaluation target)
        (.oneOverOne orientation metadata counts transport) alpha :=
  compiler.twoOverOne orientation metadata counts transport alpha

end TwistedYetter.Kirby.EvaluatorCompiler.Mutations
