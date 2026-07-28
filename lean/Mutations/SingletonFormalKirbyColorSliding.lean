import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.SingletonFormalKirbyColorSliding

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.EGNOKirbyColorEncircling
open TwistedYetter.Kirby.EGNOKirbyColorExpansion

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

#check fun
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertion : SphericalInsertionLaw data)
    (mate : SphericalMateTraceLaw (K := K) data.spherical) =>
  CategoryData.encirclingTransportData data insertion mate (ordinary data)

end TwistedYetter.Mutations.SingletonFormalKirbyColorSliding
