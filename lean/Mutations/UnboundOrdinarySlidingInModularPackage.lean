import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.UnboundOrdinarySlidingInModularPackage

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.HandleSlide

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

def rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (unbound : SourcedSlidingLaw C) :
    Package data :=
  { package with ordinarySliding := unbound }

end TwistedYetter.Mutations.UnboundOrdinarySlidingInModularPackage
