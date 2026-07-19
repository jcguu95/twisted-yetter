import TwistedYetter.Fusion.EGNOPairingCompatibility

namespace TwistedYetter.Mutations.MissingPivotalFunctorTraceLaw

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC uD vD

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [Linear K C] [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable [Linear K D] [MonoidalCategory D] [RigidCategory D]
variable [MonoidalPreadditive D] [MonoidalLinear K D]
variable {SC SD : Type} [Fintype SC] [DecidableEq SC]
variable [Fintype SD] [DecidableEq SD]
variable (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear K]

/--
This must fail: a linear strong monoidal functor does not silently acquire the
global pivotal trace theorem.
-/
noncomputable def forgedFunctorCompatibility
    (sourceData :
      FusionCategoryData (K := K) (C := C) (S := SC))
    (targetData :
      FusionCategoryData (K := K) (C := D) (S := SD))
    (sourcePivotal : PivotalStructure C)
    (targetPivotal : PivotalStructure D)
    (X Y Z : C) :=
  PivotalFunctorTraceLaw.localCompatibility
    sourceData targetData sourcePivotal targetPivotal X Y Z

end TwistedYetter.Mutations.MissingPivotalFunctorTraceLaw
