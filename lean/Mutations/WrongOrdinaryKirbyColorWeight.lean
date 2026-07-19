import TwistedYetter.Kirby.EGNOKirbyColorExpansion

namespace TwistedYetter.Mutations.WrongOrdinaryKirbyColorWeight

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOKirbyColorExpansion

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [BraidedCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

theorem rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (s : S) :
    (ordinary data).weight s = 0 := by
  rfl

end TwistedYetter.Mutations.WrongOrdinaryKirbyColorWeight
