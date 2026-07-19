import TwistedYetter.Kirby.SourceBoundGraphicalMoveCompiler

namespace TwistedYetter.Mutations.HandwrittenRawFactorInsideOneTwoFactorization

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

/--
This must fail: the factorization interface no longer accepts the desired raw
scalar multiplication equality. It requires a typed diagram factorization.
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
  { base with
      disjoint_union_sound := fun _ =>
        by
          rfl }

end TwistedYetter.Mutations.HandwrittenRawFactorInsideOneTwoFactorization
