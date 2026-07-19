import TwistedYetter.Kirby.SourceBoundGraphicalMoveCompiler

namespace TwistedYetter.Mutations.FinalNormalizedEqualityInsideOneTwoFactorization

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
open TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation

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

/-
This must fail: a 1--2 factorization program cannot contain a pre-proved final
equality of normalized invariant values.
-/
def unsafeProgram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {profile : GlobalDimensionProfile (K := K)}
    {algebra : CancellationInput profile}
    {beforeDiagram afterDiagram : Diagram C .unit .unit}
    {before after : EvaluationState (K := K)}
    (base :
      OneTwoFactorizationProgram
        (categoryData := categoryData)
        algebra beforeDiagram afterDiagram before after) :
    OneTwoFactorizationProgram
      (categoryData := categoryData)
      algebra beforeDiagram afterDiagram before after :=
  { base with normalizedEquality := True }

end TwistedYetter.Mutations.FinalNormalizedEqualityInsideOneTwoFactorization
