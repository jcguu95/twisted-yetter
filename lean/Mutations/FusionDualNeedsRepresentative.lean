import TwistedYetter.Fusion.EGNOFusionCategory

namespace TwistedYetter.Mutations.FusionDualNeedsRepresentative

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: a proposed dual-label function needs an actual isomorphism from
the selected categorical right dual.
-/
def eraseDualWitness
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
  unitIso := data.unitIso
  dualIndex := data.dualIndex

end TwistedYetter.Mutations.FusionDualNeedsRepresentative
