import TwistedYetter.Fusion.Biorthogonal
import TwistedYetter.Fusion.EGNOTracePairing
import TwistedYetter.Fusion.FrobeniusLinear

/-!
# Pivotal image and spherical mate transport

This module isolates the two standard category-theoretic inputs used in
Bärenz--Barrett (3.1.11):

* a pivotal strong monoidal functor preserves the spherical trace pairing;
* bending both members of a pairing in a spherical category preserves it.

Mathlib does not yet expose pivotal or spherical categories.  These two inputs
are therefore explicit, source-labelled hypotheses.  The monoidal image maps
and both mate maps themselves are concrete linear maps built from Mathlib's
functor coherence, evaluations, and coevaluations.  In particular, the final
transported-dual-family theorem is proved here and is not a hypothesis.
-/

namespace TwistedYetter.Fusion.PivotalMate

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Fusion.FrobeniusLinear

universe uR uC vC uD vD uI

variable {R : Type uR} [CommSemiring R]
variable {C : Type uC} [Category.{vC} C] [Preadditive C]
variable [CategoryTheory.Linear R C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [MonoidalLinear R C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
variable [CategoryTheory.Linear R D]
variable [MonoidalCategory D] [MonoidalPreadditive D]
variable [MonoidalLinear R D]
variable (F : C ⥤ D) [F.Monoidal] [F.Additive] [F.Linear R]

/--
The linear map on the forward Hom space, including the inverse tensorator:

`F(Z ⟶ X ⊗ Y') → (F Z ⟶ F X ⊗ F Y')`.
-/
noncomputable def monoidalImagePrimal
    (X Y' Z : C) :
    (Z ⟶ X ⊗ Y') →ₗ[R]
      (F.obj Z ⟶ F.obj X ⊗ F.obj Y') where
  toFun f := F.map f ≫ (Functor.Monoidal.μIso F X Y').inv
  map_add' f g := by simp
  map_smul' scalar f := by simp

/--
The linear map on the reverse Hom space, including the tensorator:

`F(X ⊗ Y' ⟶ Z) → (F X ⊗ F Y' ⟶ F Z)`.
-/
noncomputable def monoidalImageDual
    (X Y' Z : C) :
    (X ⊗ Y' ⟶ Z) →ₗ[R]
      (F.obj X ⊗ F.obj Y' ⟶ F.obj Z) where
  toFun f := (Functor.Monoidal.μIso F X Y').hom ≫ F.map f
  map_add' f g := by simp
  map_smul' scalar f := by simp

omit [MonoidalPreadditive C] [MonoidalLinear R C]
  [MonoidalPreadditive D] [MonoidalLinear R D] in
/-- The tensorators cancel when the two monoidal image coupons compose. -/
theorem monoidalImagePrimal_comp_dual
    (X Y' Z : C)
    (f : Z ⟶ X ⊗ Y')
    (g : X ⊗ Y' ⟶ Z) :
    monoidalImagePrimal (R := R) F X Y' Z f ≫
        monoidalImageDual (R := R) F X Y' Z g =
      F.map (f ≫ g) := by
  simp [monoidalImagePrimal, monoidalImageDual, Category.assoc]

/--
The precise local consequence of pivotality used by Lemma 3.3.

This is a named trusted input because Mathlib currently has no pivotal-functor
class.  It is Bärenz--Barrett Lemma 2.23, not the sliding conclusion.
-/
structure PivotalTraceCompatibility
    {X Y' Z : C}
    (source :
      PerfectPairing R (Z ⟶ X ⊗ Y') (X ⊗ Y' ⟶ Z))
    (image :
      PerfectPairing R
        (F.obj Z ⟶ F.obj X ⊗ F.obj Y')
        (F.obj X ⊗ F.obj Y' ⟶ F.obj Z)) where
  preserves_trace_pairing :
    (f : Z ⟶ X ⊗ Y') → (g : X ⊗ Y' ⟶ Z) →
      image.pair
          (monoidalImagePrimal (R := R) F X Y' Z f)
          (monoidalImageDual (R := R) F X Y' Z g) =
        source.pair f g
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 2.23, equation (2.1.17), journal pages 671-672"

namespace PivotalTraceCompatibility

variable {F}
variable {X Y' Z : C}
variable {source :
  PerfectPairing R (Z ⟶ X ⊗ Y') (X ⊗ Y' ⟶ Z)}
variable {image :
  PerfectPairing R
    (F.obj Z ⟶ F.obj X ⊗ F.obj Y')
    (F.obj X ⊗ F.obj Y' ⟶ F.obj Z)}

/-- A pivotal trace theorem gives a non-full pairing-preserving Hom map. -/
noncomputable def pairingMap
    (compatibility : PivotalTraceCompatibility (R := R) F source image) :
    PairingMap source image where
  primalMap := monoidalImagePrimal (R := R) F X Y' Z
  dualMap := monoidalImageDual (R := R) F X Y' Z
  preserves_pairing := compatibility.preserves_trace_pairing

end PivotalTraceCompatibility

/--
The precise local spherical-isotopy input for the two concrete mate maps.

The maps in this statement are `mateLinearEquiv` and
`dualMateLinearEquiv`; only their trace-pairing invariance is supplied.
-/
structure SphericalMateCompatibility
    (X Y Y' Z Z' : D)
    [ExactPairing Y Y'] [ExactPairing Y' Y]
    [ExactPairing Z' Z] [ExactPairing Z Z']
    (source :
      PerfectPairing R (Z ⟶ X ⊗ Y') (X ⊗ Y' ⟶ Z))
    (target :
      PerfectPairing R (Y ⟶ Z' ⊗ X) (Z' ⊗ X ⟶ Y)) where
  preserves_trace_pairing :
    (f : Z ⟶ X ⊗ Y') → (g : X ⊗ Y' ⟶ Z) →
      target.pair
          (mateLinearEquiv (R := R) X Y Y' Z Z' f)
          (dualMateLinearEquiv (R := R) X Y Y' Z Z' g) =
        source.pair f g
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 3.3, equations (3.1.9)-(3.1.11), journal pages 683-684"

namespace SphericalMateCompatibility

variable {X Y Y' Z Z' : D}
variable [ExactPairing Y Y'] [ExactPairing Y' Y]
variable [ExactPairing Z' Z] [ExactPairing Z Z']
variable {source :
  PerfectPairing R (Z ⟶ X ⊗ Y') (X ⊗ Y' ⟶ Z)}
variable {target :
  PerfectPairing R (Y ⟶ Z' ⊗ X) (Z' ⊗ X ⟶ Y)}

/-- The concrete pair of mate equivalences preserves the spherical pairing. -/
noncomputable def pairingTransport
    (compatibility :
      SphericalMateCompatibility (R := R)
        X Y Y' Z Z' source target) :
    PairingTransport source target where
  primalEquiv := mateLinearEquiv (R := R) X Y Y' Z Z'
  dualEquiv := dualMateLinearEquiv (R := R) X Y Y' Z Z'
  preserves_pairing := compatibility.preserves_trace_pairing

end SphericalMateCompatibility

section Equation311

variable {X Y Y' Z Z' : C}
variable [ExactPairing (F.obj Y) (F.obj Y')]
variable [ExactPairing (F.obj Y') (F.obj Y)]
variable [ExactPairing (F.obj Z') (F.obj Z)]
variable [ExactPairing (F.obj Z) (F.obj Z')]
variable {source :
  PerfectPairing R (Z ⟶ X ⊗ Y') (X ⊗ Y' ⟶ Z)}
variable {image :
  PerfectPairing R
    (F.obj Z ⟶ F.obj X ⊗ F.obj Y')
    (F.obj X ⊗ F.obj Y' ⟶ F.obj Z)}
variable {target :
  PerfectPairing R
    (F.obj Y ⟶ F.obj Z' ⊗ F.obj X)
    (F.obj Z' ⊗ F.obj X ⟶ F.obj Y)}

/--
Compose pivotal image preservation with spherical mate rotation.
This is the exact pairing map underlying equation (3.1.11).
-/
noncomputable def pivotalMatePairingMap
    (pivotal :
      PivotalTraceCompatibility (R := R) F source image)
    (spherical :
      SphericalMateCompatibility (R := R)
        (F.obj X) (F.obj Y) (F.obj Y') (F.obj Z) (F.obj Z')
        image target) :
    PairingMap source target :=
  (pivotal.pairingMap).comp
    (PairingMap.ofTransport spherical.pairingTransport)

omit [MonoidalPreadditive C] [MonoidalLinear R C] in
/-- Equation (3.1.11): the fully transformed coupons retain their pairing. -/
theorem equation_3_1_11
    (pivotal :
      PivotalTraceCompatibility (R := R) F source image)
    (spherical :
      SphericalMateCompatibility (R := R)
        (F.obj X) (F.obj Y) (F.obj Y') (F.obj Z) (F.obj Z')
        image target)
    (f : Z ⟶ X ⊗ Y')
    (g : X ⊗ Y' ⟶ Z) :
    target.pair
        ((pivotalMatePairingMap F pivotal spherical).primalMap f)
        ((pivotalMatePairingMap F pivotal spherical).dualMap g) =
      source.pair f g :=
  (pivotalMatePairingMap F pivotal spherical).preserves_pairing f g

/--
The conclusion needed in (3.1.6): a source dual basis maps to a finite
biorthogonal family in the target Hom spaces.  No fullness of `F` is used.
-/
noncomputable def transformedDualFamily
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (pivotal :
      PivotalTraceCompatibility (R := R) F source image)
    (spherical :
      SphericalMateCompatibility (R := R)
        (F.obj X) (F.obj Y) (F.obj Y') (F.obj Z) (F.obj Z')
        image target)
    (data : DualBasisData (ι := ι) source) :
    BiorthogonalFamily (ι := ι) target :=
  (pivotalMatePairingMap F pivotal spherical).mapFamily
    (BiorthogonalFamily.ofDualBasisData data)

omit [MonoidalPreadditive C] [MonoidalLinear R C] in
/-- The transformed source basis satisfies the exact Kronecker equations. -/
theorem transformedDualFamily_pair
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (pivotal :
      PivotalTraceCompatibility (R := R) F source image)
    (spherical :
      SphericalMateCompatibility (R := R)
        (F.obj X) (F.obj Y) (F.obj Y') (F.obj Z) (F.obj Z')
        image target)
    (data : DualBasisData (ι := ι) source)
    (i j : ι) :
    target.pair
        ((transformedDualFamily F pivotal spherical data).primal i)
        ((transformedDualFamily F pivotal spherical data).dual j) =
      if i = j then 1 else 0 :=
  (transformedDualFamily F pivotal spherical data).pair_eq i j

end Equation311

end TwistedYetter.Fusion.PivotalMate
