import TwistedYetter.Kirby.EGNOCategoryBoundSliding
import TwistedYetter.Kirby.KirbyCancellation
import TwistedYetter.Kirby.PresentationIsotopy
import TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

/-!
# Category-bound Kirby-move data for a modular ribbon fusion category

This module binds every category-side ingredient of the identity-functor
Kirby route to one `RibbonFusionCategoryData` value.

* the ordinary and generalized slides use the exact formal Kirby colour;
* the global dimension is the sum of squared derived quantum dimensions;
* modularity means that a listed simple is transparent exactly at the unit;
* the transparent dimension is therefore fixed to one;
* framed kinks use the same stored ribbon twist;
* cancellation factors are forced to use the derived dimensions.

The named graphical theorems remain explicit source-backed inputs.  No
presentation evaluator or four-manifold completeness theorem appears here.
-/

namespace TwistedYetter.Kirby.EGNOModularKirbyMoves

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.PresentationIsotopy
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- Double braiding with every object is the categorical transparency condition. -/
def IsTransparent (X : C) : Prop :=
  ∀ Y : C,
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y)

/--
The simple-object form of modularity.

Finite semisimplicity makes the listed simples a complete skeleton, so this
is the exact centre condition consumed by the Kirby normalization.
-/
structure ModularSimpleCenter
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  transparent_iff_unit :
    (s : S) →
      IsTransparent (data.simple s) ↔
        s = data.toFusionCategoryData.unitIndex
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Definition 2.44, journal page 676"

/-- Global dimension derived from the actual ribbon quantum dimensions. -/
noncomputable def globalDimension
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) : K :=
  ∑ s, data.quantumDimension s * data.quantumDimension s

/--
The dimension of the transparent simple sector, formed before modularity is
used to collapse it to the tensor unit.
-/
noncomputable def transparentGlobalDimension
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) : K := by
  classical
  exact
    ∑ s,
      if IsTransparent (data.simple s) then
        data.quantumDimension s * data.quantumDimension s
      else
        0

/--
Nonvanishing needed by the normalization denominator.

Neither dimension value is caller supplied.  This certificate records the
two standard scalar facts not yet derived from the local EGNO interface:
the unit has quantum dimension one, and the derived global sum is nonzero.
The latter is automatic over the usual characteristic-zero modular setting
but not over every algebraically closed field.
-/
structure ModularDimensionCertificate
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (_center : ModularSimpleCenter data) where
  unit_quantum_dimension :
    data.quantumDimension data.toFusionCategoryData.unitIndex = 1
  global_dimension_ne_zero : globalDimension data ≠ 0
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Definitions 2.35 and 2.44, equations (2.2.3) and (2.2.9), "
      ++ "journal pages 675-676"

/--
In the modular case the transparent-simple sum is exactly the tensor-unit
term, hence one.
-/
theorem transparentGlobalDimension_eq_one
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) :
    transparentGlobalDimension data = 1 := by
  classical
  rw [transparentGlobalDimension,
    Finset.sum_eq_single data.toFusionCategoryData.unitIndex]
  · rw [if_pos ((center.transparent_iff_unit
      data.toFusionCategoryData.unitIndex).2 rfl)]
    simp only [certificate.unit_quantum_dimension, mul_one]
  · intro s _ hs
    rw [if_neg]
    exact fun transparent =>
      hs ((center.transparent_iff_unit s).1 transparent)
  · intro missing
    exact (missing (Finset.mem_univ _)).elim

/--
The normalization profile for the identity pivotal functor on a modular
category.  Both ambient dimensions are the same derived global dimension and
the transparent dimension is the actual transparent-simple sum, subsequently
proved to be one.
-/
noncomputable def dimensionProfile
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) :
    GlobalDimensionProfile (K := K) where
  cDimension := globalDimension data
  dDimension := globalDimension data
  transparentDimension := transparentGlobalDimension data
  cDimension_ne_zero := certificate.global_dimension_ne_zero
  dDimension_ne_zero := certificate.global_dimension_ne_zero
  transparentDimension_ne_zero := by
    rw [transparentGlobalDimension_eq_one data center certificate]
    exact one_ne_zero
  source_ref := "ref:baerenz-barrett-dichromatic-2018"
  source_locator :=
    "Definitions 2.35, 2.44, and 3.6; equations (2.2.3), (2.2.9), "
      ++ "and (3.2.1), journal pages 675-676 and 685"

@[simp]
theorem dimensionProfile_cDimension
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) :
    (dimensionProfile data center certificate).cDimension =
      globalDimension data :=
  rfl

@[simp]
theorem dimensionProfile_dDimension
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) :
    (dimensionProfile data center certificate).dDimension =
      globalDimension data :=
  rfl

@[simp]
theorem dimensionProfile_transparentDimension
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) :
    (dimensionProfile data center certificate).transparentDimension = 1 :=
  transparentGlobalDimension_eq_one data center certificate

/--
The three source-backed scalar identities used in the two cancellation
calculations, with every value tied to the derived modular profile.
-/
structure ModularCancellationLaw
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (center : ModularSimpleCenter data)
    (certificate : ModularDimensionCertificate data center) where
  oneTwoPairValue : K
  oneTwoCutValue : K
  cutting_identity :
    oneTwoPairValue =
      globalDimension data * oneTwoCutValue
  killing_identity :
    oneTwoCutValue = transparentGlobalDimension data
  twoThreeUnknotValue : K
  pivotal_dimension_identity :
    twoThreeUnknotValue = globalDimension data
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemmas 2.46-2.47 and Theorem 3.9, equations (2.2.10), "
      ++ "(2.2.11), and (3.3.2), journal pages 677 and 686-687"

namespace ModularCancellationLaw

/-- Export to the older cancellation algebra only after dimensions are fixed. -/
def toCancellationInput
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {center : ModularSimpleCenter data}
    {certificate : ModularDimensionCertificate data center}
    (law : ModularCancellationLaw data center certificate) :
    CancellationInput (dimensionProfile data center certificate) where
  oneTwoPairValue := law.oneTwoPairValue
  oneTwoCutValue := law.oneTwoCutValue
  transparentTwistTrivial := True
  transparent_twist_witness := True.intro
  cutting_identity := fun _ => law.cutting_identity
  killing_identity := law.killing_identity
  twoThreeUnknotValue := law.twoThreeUnknotValue
  pivotal_dimension_preserved := law.pivotal_dimension_identity
  sourceRefs := [law.source_ref]
  exactScope :=
    "Identity-functor modular cancellation with category-derived global "
      ++ "dimension and transparent dimension one."
  sourceScopeCaveat :=
    "The cutting, killing, and isolated-unknot graphical identities are "
      ++ "the explicit standard theorem inputs listed by source locator."

/-- The 1--2 factor is forced to the derived global dimension. -/
theorem one_two_factor
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {center : ModularSimpleCenter data}
    {certificate : ModularDimensionCertificate data center}
    (law : ModularCancellationLaw data center certificate) :
    law.oneTwoPairValue =
      (dimensionProfile data center certificate).oneTwoFactor :=
  law.toCancellationInput.one_two_pair_factor

/-- The 2--3 factor is the same derived global dimension. -/
theorem two_three_factor
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {center : ModularSimpleCenter data}
    {certificate : ModularDimensionCertificate data center}
    (law : ModularCancellationLaw data center certificate) :
    law.twoThreeUnknotValue =
      (dimensionProfile data center certificate).twoThreeFactor :=
  law.toCancellationInput.two_three_unknot_factor

end ModularCancellationLaw

/--
Blackboard-framing conventions bound to the category's exact ribbon
structure.  These are the two explicit graphical equalities already isolated
by `PresentationIsotopy`.
-/
structure RibbonFramedKinkLaw
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  positive_sound :
    (X : C) →
      Diagram.eval C (positiveKink X) =
        (NaturalTwist.ofRibbon data.ribbon).iso.hom.app X
  negative_sound :
    (X : C) →
      Diagram.eval C (negativeKink X) =
        (NaturalTwist.ofRibbon data.ribbon).iso.inv.app X
  source_ref : String := "ref:shum-tortile-1994"
  source_locator : String :=
    "Ribbon graphical coherence identifying blackboard kinks with twist"

namespace RibbonFramedKinkLaw

/-- The old compatibility object is derived with no replaceable ribbon field. -/
def toFramedKinkCompatibility
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (law : RibbonFramedKinkLaw data) :
    FramedKinkCompatibility (C := C) where
  ribbon := data.ribbon
  positive_sound := law.positive_sound
  negative_sound := law.negative_sound
  source_ref := law.source_ref
  source_locator := law.source_locator

end RibbonFramedKinkLaw

/--
Complete category-side denominator for modular identity-functor Kirby moves.

This package has no whole-presentation evaluator and no equality for a Table
2 move.  It supplies only the algebra that a source-bound local compiler may
use.
-/
structure Package
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data
  mateTraceLaw : SphericalMateTraceLaw (K := K) data.spherical
  ordinarySliding : OrdinaryKirbySlidingLaw data
  generalizedSliding :
    LabelIndexedSlidingMovies data insertionLaw mateTraceLaw
  modularCenter : ModularSimpleCenter data
  dimensions : ModularDimensionCertificate data modularCenter
  cancellation :
    ModularCancellationLaw data modularCenter dimensions
  framedKink : RibbonFramedKinkLaw data
  categorySnapshotHash : String
  category_snapshot_hash_shape :
    TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
      categorySnapshotHash = true
  categoryCoherenceCertificateHash : String
  category_coherence_certificate_hash_shape :
    TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
      categoryCoherenceCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace Package

variable {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}

/-- The package normalization profile is definitionally category-derived. -/
noncomputable def profile (package : Package data) :
    GlobalDimensionProfile (K := K) :=
  dimensionProfile data package.modularCenter package.dimensions

/-- The package cancellation input cannot substitute independent dimensions. -/
def cancellationInput (package : Package data) :
    CancellationInput package.profile :=
  package.cancellation.toCancellationInput

/-- Framed isotopy uses the package's exact ribbon twist. -/
def framedKinkCompatibility (package : Package data) :
    FramedKinkCompatibility (C := C) :=
  package.framedKink.toFramedKinkCompatibility

/-- Cut independence is derived from the same canonical ribbon pivotal structure. -/
def sphericalCutTrace (_package : Package data) :
    SphericalCutTrace (C := C) :=
  SphericalCutTrace.ofRibbon data.ribbon

/-- The ordinary slide exported by the package remains formally colour-bound. -/
noncomputable def ordinarySlidingLaw (package : Package data) :
    HandleSlide.SourcedSlidingLaw C :=
  package.ordinarySliding.toSourcedSlidingLaw

end Package

end TwistedYetter.Kirby.EGNOModularKirbyMoves
