import TwistedYetter.Kirby.EGNOKirbyColorExpansion

namespace TwistedYetter.Mutations.KirbyColorIsNotCategoryObject

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

def rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) :
    C :=
  ordinary data

end TwistedYetter.Mutations.KirbyColorIsNotCategoryObject
