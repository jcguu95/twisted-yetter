import TwistedYetter.Fusion.EGNOFusionCategory

namespace TwistedYetter.Mutations.FusionDataWithoutRibbonIsNotRibbonData

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable [BraidedCategory C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: finite semisimple fusion data alone does not supply a ribbon
structure, hence cannot authorize pivotal, spherical, or quantum-dimension data.
-/
def promoteWithoutRibbon
    (data : FusionCategoryData (K := K) (C := C) (S := S)) :
    RibbonFusionCategoryData (K := K) (C := C) (S := S) where
  toFusionCategoryData := data

end TwistedYetter.Mutations.FusionDataWithoutRibbonIsNotRibbonData
