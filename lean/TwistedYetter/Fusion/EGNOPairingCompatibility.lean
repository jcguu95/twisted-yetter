import TwistedYetter.Fusion.PivotalMate

/-!
# Category-bound trace and mate compatibility

The older `PivotalMate` module works over a commutative semiring and therefore
keeps its two standard trace-preservation inputs abstract.  This module binds
those inputs to the actual perfect trace pairings derived from finite
semisimple fusion-category data.

Nondegeneracy is a theorem in `EGNOTracePairing`.  The two remaining graphical
facts are each represented by one global, source-labelled law, quantified over
all relevant objects and morphisms.  They cannot be supplied independently for
one basis vector or one Kirby diagram.
-/

namespace TwistedYetter.Fusion.EGNO

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.PivotalMate

universe uK uC vC uD vD

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable [CategoryTheory.Linear K D]
variable [MonoidalCategory D] [RigidCategory D]
variable [MonoidalPreadditive D] [MonoidalLinear K D]
variable {SC SD : Type} [Fintype SC] [DecidableEq SC]
variable [Fintype SD] [DecidableEq SD]
variable (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear K]

/--
One global trace-preservation theorem for a strong monoidal linear functor.

Unlike `PivotalTraceCompatibility`, this is not supplied separately for one
pair of Hom spaces.  It quantifies over every object and endomorphism and is
bound to the actual source and target fusion data and pivotal structures.  It
is the exact consequence of pivotal functoriality stated in
Bärenz--Barrett Lemma 2.23.
-/
structure PivotalFunctorTraceLaw
    (sourceData :
      FusionCategoryData (K := K) (C := C) (S := SC))
    (targetData :
      FusionCategoryData (K := K) (C := D) (S := SD))
    (sourcePivotal : PivotalStructure C)
    (targetPivotal : PivotalStructure D) where
  preserves :
    (X : C) → (f : X ⟶ X) →
      targetData.closedScalar
          (pivotalTrace targetPivotal (F.map f)) =
        sourceData.closedScalar
          (pivotalTrace sourcePivotal f)
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 2.23, equation (2.1.17), journal pages 671-672"

namespace PivotalFunctorTraceLaw

variable {F}
variable (sourceData :
  FusionCategoryData (K := K) (C := C) (S := SC))
variable (targetData :
  FusionCategoryData (K := K) (C := D) (S := SD))
variable (sourcePivotal : PivotalStructure C)
variable (targetPivotal : PivotalStructure D)

/--
The global functor trace law supplies every local pairing map, with both
perfect pairings derived from fusion-category data.
-/
noncomputable def localCompatibility
    (law :
      PivotalFunctorTraceLaw (K := K) F
        sourceData targetData sourcePivotal targetPivotal)
    (X Y' Z : C) :
    PivotalTraceCompatibility (R := K) F
      (sourceData.pivotalTracePerfectPairing
        sourcePivotal Z (X ⊗ Y'))
      (targetData.pivotalTracePerfectPairing
        targetPivotal (F.obj Z) (F.obj X ⊗ F.obj Y')) where
  preserves_trace_pairing f g := by
    rw [sourceData.pivotalTracePerfectPairing_pair,
      targetData.pivotalTracePerfectPairing_pair,
      monoidalImagePrimal_comp_dual]
    exact law.preserves Z (f ≫ g)
  source_ref := law.source_ref
  source_locator := law.source_locator

end PivotalFunctorTraceLaw

end TwistedYetter.Fusion.EGNO
