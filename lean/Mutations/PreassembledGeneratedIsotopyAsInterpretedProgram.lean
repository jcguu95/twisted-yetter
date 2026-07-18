import TwistedYetter.Kirby.SourceBoundGraphicalMoveCompiler

namespace TwistedYetter.Mutations.PreassembledGeneratedIsotopyAsInterpretedProgram

open CategoryTheory
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.PresentationIsotopy
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
open TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

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
This must fail: an interpreted source program has no constructor from an
already assembled `GeneratedIsotopy`.
-/
def unsafeProgram
    {categoryData :
      AdmissibleKirbyCategory
        (K := K) (C := C) (S := S) (I := I)}
    {algebra :
      TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra.Input categoryData}
    {steps : List (String × FramedIsotopyGenerator)}
    {before after : Diagram C .unit .unit}
    (proof : GeneratedIsotopy before after) :
    InterpretedFramedIsotopyProgram algebra steps before after :=
  .fromGeneratedIsotopy proof

end TwistedYetter.Mutations.PreassembledGeneratedIsotopyAsInterpretedProgram
