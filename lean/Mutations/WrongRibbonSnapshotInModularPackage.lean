import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.WrongRibbonSnapshotInModularPackage

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOModularKirbyMoves

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

def rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (other : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (wrongRibbon : RibbonFramedKinkLaw other) :
    Package data :=
  { package with framedKink := wrongRibbon }

end TwistedYetter.Mutations.WrongRibbonSnapshotInModularPackage
