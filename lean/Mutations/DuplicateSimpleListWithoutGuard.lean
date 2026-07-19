import TwistedYetter.Fusion.EGNOFusionCategory

namespace TwistedYetter.Mutations.DuplicateSimpleListWithoutGuard

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: simple representatives cannot be admitted without a proof that
isomorphic representatives have the same index.
-/
def erasePairwiseGuard
    (data : FusionCategoryData (K := K) (C := C) (S := S)) :
    FusionCategoryData (K := K) (C := C) (S := S) where
  simple := data.simple
  simple_isSimple := data.simple_isSimple
  simple_complete := data.simple_complete
  hom_finite := data.hom_finite
  multiplicity := data.multiplicity
  decomposition := data.decomposition
  unitIndex := data.unitIndex
  unitIso := data.unitIso
  dualIndex := data.dualIndex
  dualIso := data.dualIso

end TwistedYetter.Mutations.DuplicateSimpleListWithoutGuard
