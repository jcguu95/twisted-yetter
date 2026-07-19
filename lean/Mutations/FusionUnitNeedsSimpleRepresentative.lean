import TwistedYetter.Fusion.EGNOFusionCategory

namespace TwistedYetter.Mutations.FusionUnitNeedsSimpleRepresentative

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: naming a unit index does not prove that its representative is
the tensor unit.
-/
def eraseUnitWitness
    (data : FusionCategoryData (K := K) (C := C) (S := S)) :
    FusionCategoryData (K := K) (C := C) (S := S) where
  simple := data.simple
  simple_isSimple := data.simple_isSimple
  simple_pairwise := data.simple_pairwise
  simple_complete := data.simple_complete
  hom_finite := data.hom_finite
  multiplicity := data.multiplicity
  decomposition := data.decomposition
  unitIndex := data.unitIndex
  dualIndex := data.dualIndex
  dualIso := data.dualIso

end TwistedYetter.Mutations.FusionUnitNeedsSimpleRepresentative
