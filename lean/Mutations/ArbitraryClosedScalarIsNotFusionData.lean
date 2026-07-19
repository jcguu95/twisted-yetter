import TwistedYetter.Fusion.EGNOFusionCategory

namespace TwistedYetter.Mutations.ArbitraryClosedScalarIsNotFusionData

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
This must fail: closed-diagram scalarization is Schur-derived and is not a
caller-overridable field of the fusion-category package.
-/
def overwriteClosedScalar
    (data : FusionCategoryData (K := K) (C := C) (S := S)) :
    FusionCategoryData (K := K) (C := C) (S := S) :=
  { data with closedScalar := fun _ => 0 }

end TwistedYetter.Mutations.ArbitraryClosedScalarIsNotFusionData
