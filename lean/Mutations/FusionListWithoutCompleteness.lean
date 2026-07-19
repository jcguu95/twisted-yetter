import TwistedYetter.Fusion.EGNOFusionCategory

namespace TwistedYetter.Mutations.FusionListWithoutCompleteness

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: a finite list is not a complete simple skeleton unless every
simple object is proved to occur.
-/
def eraseCompleteness
    (data : FusionCategoryData (K := K) (C := C) (S := S)) :
    FusionCategoryData (K := K) (C := C) (S := S) where
  simple := data.simple
  simple_isSimple := data.simple_isSimple
  simple_pairwise := data.simple_pairwise
  hom_finite := data.hom_finite
  multiplicity := data.multiplicity
  decomposition := data.decomposition
  unitIndex := data.unitIndex
  unitIso := data.unitIso
  dualIndex := data.dualIndex
  dualIso := data.dualIso

end TwistedYetter.Mutations.FusionListWithoutCompleteness
