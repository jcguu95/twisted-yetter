import TwistedYetter.Kirby.EGNOModularKirbyMoves

namespace TwistedYetter.Mutations.WrongModularTransparentDimension

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

theorem rejected
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) :
    (dimensionProfile data center certificate).transparentDimension = 0 := by
  rfl

end TwistedYetter.Mutations.WrongModularTransparentDimension
