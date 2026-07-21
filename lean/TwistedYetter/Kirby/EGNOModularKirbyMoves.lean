import TwistedYetter.Kirby.EGNOCategoryBoundSliding
import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.KirbyCancellation
import TwistedYetter.Kirby.PresentationIsotopy
import TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
import TwistedYetter.Fusion.EGNOPremodularModular

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
open TwistedYetter.Kirby.ComponentRibbonDiagram
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
The exact mathematical laws used by framed-link isotopy proofs.

This structure deliberately contains no content hash or evidence metadata.
Planar coherence, braiding naturality, duality, and coupon naturality are
already theorems of the categorical diagram language; the only selected
structures needed here are the category's ribbon kink and spherical cut.
-/
structure FramedIsotopyLaws
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  framedKinkLaw : RibbonFramedKinkLaw data

namespace FramedIsotopyLaws

/-- The selected kink convention is forced by the category's ribbon twist. -/
def framedKinkCompatibility
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (laws : FramedIsotopyLaws data) :
    FramedKinkCompatibility (C := C) :=
  laws.framedKinkLaw.toFramedKinkCompatibility

/-- Closure-cut invariance uses the spherical trace induced by that ribbon. -/
def sphericalCutTrace
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (_laws : FramedIsotopyLaws data) :
    SphericalCutTrace (C := C) :=
  SphericalCutTrace.ofRibbon data.ribbon

end FramedIsotopyLaws

/--
The three non-derived graphical rule classes required by the modular
identity-functor Kirby argument.

Fixed-label 2-over-2 sliding is now derived from ordinary sliding and
naturality, so it is not a separate assumption class.
-/
inductive GraphicalRuleClass where
  | ordinarySliding
  | cancellation
  | framedKink
  deriving Repr, BEq, DecidableEq

/-- The exact three-rule denominator of the graphical proof. -/
def requiredGraphicalRuleClasses : List GraphicalRuleClass :=
  [
    .ordinarySliding,
    .cancellation,
    .framedKink
  ]

/-- Machine-checked confirmation that the visible denominator has three rules. -/
theorem required_graphical_rule_class_count :
    requiredGraphicalRuleClasses.length = 3 := by
  decide

/--
Low-level environment containing the three non-derived graphical rule classes.

The public modular evaluator does not ask its caller to construct this
environment. `LiteratureBackedModularGraphicalEnvironment.build` fixes its
mathematical fields from explicitly named literature axioms. The remaining
fields bind those laws to one category snapshot and its normalization data.
-/
structure GraphicalInvarianceEnvironment
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  ordinaryKirbySlidingLaw :
    OrdinaryKirbySlidingLaw data
  modularCenter : ModularSimpleCenter data
  dimensions : ModularDimensionCertificate data modularCenter
  cancellationLaw :
    ModularCancellationLaw data modularCenter dimensions
  framedKinkLaw :
    RibbonFramedKinkLaw data
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

namespace GraphicalInvarianceEnvironment

variable {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}

/-- Forget audit metadata and retain exactly the framed-isotopy mathematics. -/
def framedIsotopyLaws
    (graphical : GraphicalInvarianceEnvironment data) :
    FramedIsotopyLaws data where
  framedKinkLaw := graphical.framedKinkLaw

/-- The normalization profile is definitionally category-derived. -/
noncomputable def profile
    (graphical : GraphicalInvarianceEnvironment data) :
    GlobalDimensionProfile (K := K) :=
  dimensionProfile data
    graphical.modularCenter graphical.dimensions

/-- Export the cancellation law with fixed category-derived dimensions. -/
def cancellationInput
    (graphical : GraphicalInvarianceEnvironment data) :
    CancellationInput graphical.profile :=
  graphical.cancellationLaw.toCancellationInput

/-- Export the literature-backed framed-kink law. -/
def framedKinkCompatibility
    (graphical : GraphicalInvarianceEnvironment data) :
    FramedKinkCompatibility (C := C) :=
  graphical.framedKinkLaw.toFramedKinkCompatibility

/-- Cut independence is derived from the same canonical ribbon pivotal structure. -/
def sphericalCutTrace
    (_graphical : GraphicalInvarianceEnvironment data) :
    SphericalCutTrace (C := C) :=
  SphericalCutTrace.ofRibbon data.ribbon

/-- Export the literature-backed ordinary sliding law. -/
noncomputable def ordinarySlidingLaw
    (graphical : GraphicalInvarianceEnvironment data) :
    HandleSlide.SourcedSlidingLaw C :=
  graphical.ordinaryKirbySlidingLaw.toSourcedSlidingLaw

end GraphicalInvarianceEnvironment

namespace LiteratureBackedModularGraphicalEnvironment

variable [CharZero K]

/--
EGNO's unit-dimension theorem for the canonical pivotal structure of a ribbon
fusion category.

This is an explicit textbook axiom boundary, not a caller-supplied field.
-/
axiom egno_quantumDimension_unit
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    𝒞.premodular.quantumDimension
        𝒞.premodular.toFusionCategoryData.unitIndex = 1

/--
Bärenz--Barrett Lemma 3.1, with the exact formal Kirby colour retained by the
diagram-backed interface.
-/
axiom baerenzBarrett_ordinaryKirbySliding
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    OrdinaryKirbySlidingLaw 𝒞.premodular

/--
Bärenz--Barrett's cutting/killing calculation for the exact positive Hopf
pair representing a cancelling 1--2 handle pair.

Only the isolated two-component finite sum occurs in this source-backed
boundary.  The surrounding presentation factorization, homology-exponent
transport, global-label reindexing, and normalization are proved downstream.
-/
axiom baerenzBarrett_oneTwoHopfPairSum
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (dottedId twoHandleId : String)
    (_distinct : dottedId ≠ twoHandleId)
    (labelOf : (Fin 2 → S) → String → S)
    (dotted_label_sound :
      (labels : Fin 2 → S) →
        labelOf labels dottedId = labels 0)
    (two_handle_label_sound :
      (labels : Fin 2 → S) →
        labelOf labels twoHandleId = labels 1) :
    (∑ labels : Fin 2 → S,
      (𝒞.premodular.quantumDimension (labels 0) *
        𝒞.premodular.quantumDimension (labels 1)) *
      𝒞.premodular.toFusionCategoryData.closedScalar
        (Diagram.eval C
          ((ComponentDiagram.oneTwoHopfPair
            dottedId twoHandleId).interpret
              𝒞.premodular (labelOf labels)))) =
      globalDimension 𝒞.premodular

/--
Bärenz--Barrett's killing lemma before summing the label on the strand being
encircled.  A Kirby-coloured dotted meridian kills every nontransparent
simple channel.  In a modular category the only surviving channel is the
tensor unit, where the value is the global dimension.

This label-resolved form is the standard categorical input needed to prove
that a homological tensor-automorphism coupon is invisible after the Tham
`k = 3` vacuum projection.  It still contains no whole-presentation
evaluation and no Kirby-invariance conclusion.
-/
axiom baerenzBarrett_hopfKirbyKillingFiber
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (dottedId twoHandleId : String)
    (_distinct : dottedId ≠ twoHandleId)
    (labelOf : S → S → String → S)
    (dotted_label_sound :
      (dottedLabel twoHandleLabel : S) →
        labelOf dottedLabel twoHandleLabel dottedId = dottedLabel)
    (two_handle_label_sound :
      (dottedLabel twoHandleLabel : S) →
        labelOf dottedLabel twoHandleLabel twoHandleId = twoHandleLabel)
    (twoHandleLabel : S) :
    (∑ dottedLabel : S,
      𝒞.premodular.quantumDimension dottedLabel *
        𝒞.premodular.toFusionCategoryData.closedScalar
          (Diagram.eval C
            ((ComponentDiagram.oneTwoHopfPair
              dottedId twoHandleId).interpret
                𝒞.premodular
                (labelOf dottedLabel twoHandleLabel)))) =
      if twoHandleLabel =
          𝒞.premodular.toFusionCategoryData.unitIndex then
        globalDimension 𝒞.premodular
      else
        0

/--
Shum's coherence theorem for tortile categories, specialized to the positive
and negative blackboard-kink evaluations used by the local compiler.
-/
axiom shum_ribbonFramedKink
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    RibbonFramedKinkLaw 𝒞.premodular

/--
The hash-free framed-isotopy laws canonically selected by a modular category.
-/
noncomputable def framedIsotopyLaws
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    FramedIsotopyLaws 𝒞.premodular where
  framedKinkLaw := shum_ribbonFramedKink 𝒞

/-- The trivial Mueger centre derived from S-matrix nondegeneracy. -/
def modularSimpleCenter
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    ModularSimpleCenter 𝒞.premodular where
  transparent_iff_unit := 𝒞.transparent_iff_unit
  source_ref := "ref:egno-tensor-categories-2015"
  source_locator :=
    "Definition 8.13.4, Remark 8.19.3, and Theorem 8.20.7"

/-- Both normalization facts derived from the named EGNO theorem boundary. -/
def modularDimensionCertificate
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    ModularDimensionCertificate 𝒞.premodular
      (modularSimpleCenter 𝒞) where
  unit_quantum_dimension := egno_quantumDimension_unit 𝒞
  global_dimension_ne_zero := 𝒞.globalDimension_ne_zero
  source_ref := "ref:egno-tensor-categories-2015"
  source_locator := "Proposition 8.14.2 and the unit-dimension identity"

/--
The cancellation scalar law has no independent mathematical field: its three
values are the dimensions required by the normalization formula.

The source-bound local compiler must still prove that the concrete isolated
link factors evaluate to these values.
-/
noncomputable def modularCancellationLaw
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    ModularCancellationLaw 𝒞.premodular
      (modularSimpleCenter 𝒞)
      (modularDimensionCertificate 𝒞) where
  oneTwoPairValue :=
    globalDimension 𝒞.premodular *
      transparentGlobalDimension 𝒞.premodular
  oneTwoCutValue := transparentGlobalDimension 𝒞.premodular
  cutting_identity := rfl
  killing_identity := rfl
  twoThreeUnknotValue := globalDimension 𝒞.premodular
  pivotal_dimension_identity := rfl

/--
Only content-addressed evidence binding remains caller supplied. It contains no
graphical equality.
-/
structure EvidenceBinding where
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

/--
Construct the compiler environment without asking the final theorem caller to
supply any of the three non-derived graphical laws.
-/
noncomputable def build
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (binding : EvidenceBinding) :
    GraphicalInvarianceEnvironment 𝒞.premodular where
  ordinaryKirbySlidingLaw := baerenzBarrett_ordinaryKirbySliding 𝒞
  modularCenter := modularSimpleCenter 𝒞
  dimensions := modularDimensionCertificate 𝒞
  cancellationLaw := modularCancellationLaw 𝒞
  framedKinkLaw := shum_ribbonFramedKink 𝒞
  categorySnapshotHash := binding.categorySnapshotHash
  category_snapshot_hash_shape := binding.category_snapshot_hash_shape
  categoryCoherenceCertificateHash :=
    binding.categoryCoherenceCertificateHash
  category_coherence_certificate_hash_shape :=
    binding.category_coherence_certificate_hash_shape
  sourceRefs := binding.sourceRefs
  exactScope := binding.exactScope
  sourceScopeCaveat := binding.sourceScopeCaveat

end LiteratureBackedModularGraphicalEnvironment

end TwistedYetter.Kirby.EGNOModularKirbyMoves
