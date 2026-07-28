import TwistedYetter.Fusion.EGNOPivotalInsertion
import TwistedYetter.Kirby.EGNOKirbyColorExpansion
import TwistedYetter.Kirby.FramedEncirclingTransport
import TwistedYetter.Kirby.KirbyColorEncirclingTransport
import TwistedYetter.Kirby.LinearContext
import TwistedYetter.Kirby.Presentation

/-!
# Label-indexed Kirby-colour encircling transport

The identity-functor encircling calculation fixes an actual object `X`.
After a Kirby colour is expanded, `X` is one simple label at a time; it is not
a single category object representing the whole formal colour.

This module therefore constructs one `EncirclingTransportData` for every simple
label.  The forward insertion, mate transport, and inverse insertion are
derived from:

* a ribbon fusion category;
* the all-objects pivotal insertion law;
* the all-objects spherical mate trace law.

Only the framed graphical movies remain a separate all-label input.  No field
below states the desired endpoint equality.
-/

namespace TwistedYetter.Kirby.EGNOKirbyColorEncircling

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOKirbyColorExpansion
open TwistedYetter.Kirby.FramedEncirclingTransport
open TwistedYetter.Kirby.KirbyColorEncirclingTransport
open TwistedYetter.Kirby.HandleSlide
open TwistedYetter.Kirby.LinearDiagram

universe uK uC vC uI

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

namespace CategoryData

variable (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))

/--
The channel index for a fixed simple label `x`, the source encircling label
`y`, and the inserted simple channel `z`.
-/
abbrev EncirclingChannelIndex (x y z : S) :=
  data.InsertionIndex
    (data.simple x ⊗ (data.simple y)ᘁ) z

/-- The source trace-dual basis before the mate change. -/
noncomputable def encirclingForwardBasis (x y z : S) :
    DualBasisData (ι := EncirclingChannelIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple x ⊗ (data.simple y)ᘁ)
        (data.simple z)) :=
  data.insertionDualBasis
    (data.simple x ⊗ (data.simple y)ᘁ) z

/-- Cyclicity reverses the insertion pairing before the mate operation. -/
theorem encirclingSourcePairingCyclic
    (x y z : S)
    (projection :
      data.simple x ⊗ (data.simple y)ᘁ ⟶ data.simple z)
    (inclusion :
      data.simple z ⟶ data.simple x ⊗ (data.simple y)ᘁ) :
    (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple z)
        (data.simple x ⊗ (data.simple y)ᘁ)).pair
        inclusion projection =
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple x ⊗ (data.simple y)ᘁ)
        (data.simple z)).pair projection inclusion := by
  rw [data.toFusionCategoryData.pivotalTracePerfectPairing_pair,
    data.toFusionCategoryData.pivotalTracePerfectPairing_pair]
  exact congrArg data.toFusionCategoryData.closedScalar
    (pivotalTrace_cyclic data.pivotal projection inclusion).symm

/-- The insertion basis in the orientation consumed by the mate maps. -/
noncomputable def encirclingMateSourceBasis (x y z : S) :
    DualBasisData (ι := EncirclingChannelIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple z)
        (data.simple x ⊗ (data.simple y)ᘁ)) :=
  (encirclingForwardBasis data x y z).reversed
    (encirclingSourcePairingCyclic data x y z)

/-- The canonical pairing-preserving mate transport for one channel. -/
noncomputable def encirclingMateTransport
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x y z : S) :
    PairingTransport
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple z)
        (data.simple x ⊗ (data.simple y)ᘁ))
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple y)
        ((data.simple z)ᘁ ⊗ data.simple x)) :=
  data.toFusionCategoryData.sphericalMatePairingTransport
    data.spherical mateLaw
    (data.simple x) (data.simple y) (data.simple z)

/-- The full dual basis after the mate change of variables. -/
noncomputable def encirclingMatedBasis
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x y z : S) :
    DualBasisData (ι := EncirclingChannelIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple y)
        ((data.simple z)ᘁ ⊗ data.simple x)) :=
  (encirclingMateTransport data mateLaw x y z).dualBasisData
    (encirclingMateSourceBasis data x y z)

/--
Cyclicity identifies the target pairing with the reversed mated pairing.
-/
theorem encirclingPairingCyclic
    (x y z : S)
    (forward :
      data.simple y ⟶ (data.simple z)ᘁ ⊗ data.simple x)
    (backward :
      (data.simple z)ᘁ ⊗ data.simple x ⟶ data.simple y) :
    (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        ((data.simple z)ᘁ ⊗ data.simple x)
        (data.simple y)).pair backward forward =
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple y)
        ((data.simple z)ᘁ ⊗ data.simple x)).pair forward backward := by
  rw [data.toFusionCategoryData.pivotalTracePerfectPairing_pair,
    data.toFusionCategoryData.pivotalTracePerfectPairing_pair]
  exact congrArg data.toFusionCategoryData.closedScalar
    (pivotalTrace_cyclic data.pivotal forward backward).symm

/-- The mated basis, reversed into insertion orientation on the target object. -/
noncomputable def encirclingBackwardBasis
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x y z : S) :
    DualBasisData (ι := EncirclingChannelIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        ((data.simple z)ᘁ ⊗ data.simple x)
        (data.simple y)) :=
  (encirclingMatedBasis data mateLaw x y z).reversed
    (encirclingPairingCyclic data x y z)

/-- Forward dimension-weighted insertion is an instance of the global law. -/
theorem encirclingForwardSound
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (x y : S) :
    ∑ z, ∑ i : EncirclingChannelIndex data x y z,
      data.quantumDimension z •
        ((encirclingForwardBasis data x y z).primal i ≫
          (encirclingForwardBasis data x y z).dual i) =
      𝟙 (data.simple x ⊗ (data.simple y)ᘁ) :=
  insertionLaw.resolves
    (data.simple x ⊗ (data.simple y)ᘁ)
    (encirclingForwardBasis data x y)

/-- Inverse insertion after the mate change is derived from the same law. -/
theorem encirclingBackwardSound
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x z : S) :
    ∑ y, ∑ i : EncirclingChannelIndex data x y z,
      data.quantumDimension y •
        ((encirclingMatedBasis data mateLaw x y z).dual i ≫
          (encirclingMatedBasis data mateLaw x y z).primal i) =
      𝟙 ((data.simple z)ᘁ ⊗ data.simple x) := by
  have resolved :=
    insertionLaw.resolves
      ((data.simple z)ᘁ ⊗ data.simple x)
      (fun y => encirclingBackwardBasis data mateLaw x y z)
  simpa only [
    encirclingBackwardBasis,
    DualBasisData.reverse_primal,
    DualBasisData.reverse_dual
  ] using resolved

/--
The Kirby-colour encircling algebra for one actual simple label `x`.

Every algebraic equality is now derived from the two global standard laws.
-/
noncomputable def encirclingTransportData
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S) :
    EncirclingTransportData
      (R := K) (D := C) (S := S) (I := EncirclingChannelIndex data x) where
  fixed := data.simple x
  weight := data.quantumDimension
  simple := data.simple
  dualSimple := fun z => (data.simple z)ᘁ
  matedPairing y z :=
    data.toFusionCategoryData.pivotalTracePerfectPairing
      data.pivotal (data.simple y)
      ((data.simple z)ᘁ ⊗ data.simple x)
  matedFamily y z :=
    BiorthogonalFamily.ofDualBasisData
      (encirclingMatedBasis data mateLaw x y z)
  forwardProjection y z i :=
    (encirclingForwardBasis data x y z).primal i
  forwardInclusion y z i :=
    (encirclingForwardBasis data x y z).dual i
  forwardSound y :=
    encirclingForwardSound data insertionLaw x y
  backwardSound z := by
    simpa only [BiorthogonalFamily.ofDualBasisData] using
      encirclingBackwardSound data insertionLaw mateLaw x z
  pivotal_source_ref := "ref:baerenz-barrett-dichromatic-2018"
  pivotal_source_locator :=
    "Lemmas 2.37 and 3.3, equations (2.2.5) and (3.1.3)-(3.1.11)"

end CategoryData

/--
The framed graphical transport, quantified over every simple label that can
occur in the formal Kirby-colour expansion.

`EncirclingTransportFamily` contains contexts and certified local movies. Its
core endpoint equality is derived by `KirbyColorEncirclingTransport`; it is
not a field of this structure.
-/
structure LabelIndexedEncirclingMovies
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical) where
  family :
    (x : S) →
      EncirclingTransportFamily
        (CategoryData.encirclingTransportData data insertionLaw mateLaw x)
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemmas 3.3-3.4, equations (3.1.3)-(3.1.11), journal pages 681-684"

/-
This namespace contains the one remaining literature input.  The mathematical
API is specialized to the identity functor on one ribbon fusion category.
There is no source category, target category, or pivotal functor parameter.

* `kirbyColorEncirclingFiber` is an intentionally unfinished construction for
  one fixed pair `(x, A)`.  Its constructor exposes the precise graphical data
  still to be built.
* `targetEncircling_natural` is the one remaining endpoint-naturality input.
* `sourceEncircling_natural` is derived from the pointwise source-to-target
  equality and target-endpoint naturality.

The insertion and mate/trace equalities inside this calculation are supplied
separately by `PivotalInsertionLaw` and `SphericalMateTraceLaw`.
-/
namespace LiteratureInput

/--
Legacy identity-functor Kirby-colour encircling input.

The role-aware premodular 2/2 proof does not use this declaration.  It remains
an explicit axiom only so archived modular encircling routes continue to
compile while the direct attach--finite-transport--detach route is audited
separately.
-/
axiom kirbyColorEncirclingFiber
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S)
    (strand : C) :
    EncirclingTransportFiber
      (CategoryData.encirclingTransportData data insertionLaw mateLaw x)
      strand

/--
Naturality of the right endpoint in the exposed object `A`.

The target encircling is natural in the exposed strand: an arbitrary morphism
`f : A ⟶ B` can be placed before or after that encircling operator.

Reference: Bärenz--Barrett, Lemma 3.4 and its proof immediately following
equation (3.1.11), journal page 684.
-/
axiom targetEncircling_natural
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S)
    {A B : C}
    (f : A ⟶ B) :
    (tensorLeft (data.simple x)).map f ≫
        LinearDiagram.eval
          (kirbyColorEncirclingFiber data insertionLaw mateLaw x B).targetEncirclingSum =
      LinearDiagram.eval
          (kirbyColorEncirclingFiber data insertionLaw mateLaw x A).targetEncirclingSum ≫
        (tensorLeft (data.simple x)).map f

/--
Naturality of the left endpoint is derived rather than assumed.

The pointwise calculation identifies each source endpoint with its target
endpoint.  Target naturality therefore implies source naturality.
-/
theorem sourceEncircling_natural
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S)
    {A B : C}
    (f : A ⟶ B) :
    (tensorLeft (data.simple x)).map f ≫
        LinearDiagram.eval
          (kirbyColorEncirclingFiber data insertionLaw mateLaw x B).sourceEncirclingSum =
      LinearDiagram.eval
          (kirbyColorEncirclingFiber data insertionLaw mateLaw x A).sourceEncirclingSum ≫
        (tensorLeft (data.simple x)).map f := by
  calc
    _ = (tensorLeft (data.simple x)).map f ≫
        LinearDiagram.eval
          (kirbyColorEncirclingFiber data insertionLaw mateLaw x B).targetEncirclingSum := by
      rw [(kirbyColorEncirclingFiber
        data insertionLaw mateLaw x B).core_sound]
    _ = LinearDiagram.eval
          (kirbyColorEncirclingFiber data insertionLaw mateLaw x A).targetEncirclingSum ≫
        (tensorLeft (data.simple x)).map f :=
      targetEncircling_natural
        data insertionLaw mateLaw x f
    _ = _ := by
      rw [(kirbyColorEncirclingFiber
        data insertionLaw mateLaw x A).core_sound]

end LiteratureInput

/--
Assemble the label-indexed family from the pointwise source-to-target
calculation and the two endpoint naturality statements.

This is a definition, not a literature axiom.  Lean performs the all-simple
indexing and supplies the provenance fields.
-/
noncomputable def labelIndexedEncirclingMovies
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical) :
    LabelIndexedEncirclingMovies data insertionLaw mateLaw where
  family x :=
    { fiber := fun strand =>
        LiteratureInput.kirbyColorEncirclingFiber
          data insertionLaw mateLaw x strand
      source_naturality := fun f =>
        LiteratureInput.sourceEncircling_natural
          data insertionLaw mateLaw x f
      target_naturality := fun f =>
        LiteratureInput.targetEncircling_natural
          data insertionLaw mateLaw x f
      diagram_content_hash :=
        "source:baerenz-barrett-lemma-3.3-3.4-label-indexed" }
  source_ref := "ref:baerenz-barrett-dichromatic-2018"
  source_locator :=
    "Lemmas 3.3-3.4, equations (3.1.2)-(3.1.11), journal pages 681-684"

namespace LabelIndexedEncirclingMovies

variable
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : PivotalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}

/--
One closed encircling-transport window for every possible simple label on the
moving two-handle.
-/
structure ClosedWindow
    (movies : LabelIndexedEncirclingMovies data insertionLaw mateLaw) where
  source : Boundary C
  target : Boundary C
  exterior : Diagram C source target
  context :
    (x : S) →
      Context C
        (.atom (data.simple x ⊗ source.denote))
        (.atom (data.simple x ⊗ target.denote))
        .unit .unit

namespace ClosedWindow

variable
    {movies : LabelIndexedEncirclingMovies data insertionLaw mateLaw}
    (window : ClosedWindow movies)

/-- The complete closed source diagram for one fixed simple label. -/
noncomputable def before (x : S) : Diagram C .unit .unit :=
  Context.plug C (window.context x)
    (beforeExterior
      (movies.family x).sourcedEncirclingLaw
      window.exterior)

/-- The complete closed target diagram for the same fixed simple label. -/
noncomputable def after (x : S) : Diagram C .unit .unit :=
  Context.plug C (window.context x)
    (afterExterior
      (movies.family x).sourcedEncirclingLaw
      window.exterior)

/-- Every fixed-label term follows from framed encircling transport. -/
theorem term_sound (x : S) :
    Diagram.eval C (window.before x) =
      Diagram.eval C (window.after x) :=
  EncirclingTransportFamily.framedEncirclingTransport_sound
    (movies.family x) window.exterior (window.context x)

/-- Formal weighted sum of all fixed-label source diagrams. -/
noncomputable def linearBefore (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum (R := K) coefficient window.before

/-- Formal weighted sum of all fixed-label target diagrams. -/
noncomputable def linearAfter (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum (R := K) coefficient window.after

/--
Termwise encircling transport lifts to any unchanged outer coefficient.

This is the finite-sum theorem needed for ordinary or homologically twisted
Kirby-colour coefficients.  No collapsed sum is treated as one fixed object.
-/
theorem linear_eval_sound (coefficient : S → K) :
    eval (R := K) (window.linearBefore coefficient) =
      eval (R := K) (window.linearAfter coefficient) := by
  simp only [linearBefore, linearAfter, eval_weightedSum]
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg (fun morphism => coefficient x • morphism)
    (window.term_sound x)

/-- Collapse only after the formal weighted-sum equality has been proved. -/
theorem collapsed_eval_sound (coefficient : S → K) :
    Diagram.eval C
        (collapse (R := K) "kirby-encircling-label-sum-source"
          (window.linearBefore coefficient)) =
      Diagram.eval C
        (collapse (R := K) "kirby-encircling-label-sum-target"
          (window.linearAfter coefficient)) :=
  window.linear_eval_sound coefficient

end ClosedWindow

end LabelIndexedEncirclingMovies

/--
The ordinary Kirby-colour slide of Bärenz--Barrett Lemma 3.1, bound to the
actual formal family `sum_s dim(s) s`.

The one global `core_sound` field is the cited sliding theorem.  The two
endpoint diagrams and their evaluations are forced to be the dimension-
weighted expansions of the category's listed simples.

This mathematical structure deliberately contains no evidence hash.  The
current endpoint diagrams are Lean functions rather than serialized syntax,
so pretending that the literature theorem can manufacture a content hash
would give provenance metadata mathematical force that it does not have.
-/
structure OrdinaryKirbySlidingLaw
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S)) where
  beforeSimple :
    (s : S) → (X : C) → Diagram C (.atom X) (.atom X)
  afterSimple :
    (s : S) → (X : C) → Diagram C (.atom X) (.atom X)
  before : 𝟭 C ⟶ 𝟭 C
  after : 𝟭 C ⟶ 𝟭 C
  before_eval :
    (X : C) →
      eval (R := K)
          (diagramExpansion (ordinary data)
            (fun s => beforeSimple s X)) =
        before.app X
  after_eval :
    (X : C) →
      eval (R := K)
          (diagramExpansion (ordinary data)
            (fun s => afterSimple s X)) =
        after.app X
  core_sound : before = after

namespace OrdinaryKirbySlidingLaw

variable {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}

/-- Forget to the old local-move interface only after the formal colour is bound. -/
noncomputable def toSourcedSlidingLaw
    (law : OrdinaryKirbySlidingLaw data) :
    SourcedSlidingLaw C where
  before_diagram X :=
    collapse (R := K) "BB-ordinary-kirby-slide-before"
      (diagramExpansion (ordinary data)
        (fun s => law.beforeSimple s X))
  after_diagram X :=
    collapse (R := K) "BB-ordinary-kirby-slide-after"
      (diagramExpansion (ordinary data)
        (fun s => law.afterSimple s X))
  before := law.before
  after := law.after
  before_eval := law.before_eval
  after_eval := law.after_eval
  core_sound := law.core_sound
  diagram_schema := "twisted-yetter.egno-ordinary-kirby-slide.v1"
  diagram_content_hash :=
    "UNAVAILABLE-NON-SERIALIZED-CATEGORICAL-DIAGRAM"
  source_ref := "ref:baerenz-barrett-dichromatic-2018"
  source_locator :=
    "Lemma 3.1, equation (3.1.1), journal pages 680-681"

/-- The exported ordinary law still evaluates the exact quantum-dimension sum. -/
theorem before_is_dimension_weighted
    (law : OrdinaryKirbySlidingLaw data)
    (X : C) :
    Diagram.eval C (law.toSourcedSlidingLaw.before_diagram X) =
      ∑ s, data.quantumDimension s •
        Diagram.eval C (law.beforeSimple s X) := by
  exact eval_ordinary_expansion data (fun s => law.beforeSimple s X)

/-- The after endpoint retains the same exact formal Kirby-colour weights. -/
theorem after_is_dimension_weighted
    (law : OrdinaryKirbySlidingLaw data)
    (X : C) :
    Diagram.eval C (law.toSourcedSlidingLaw.after_diagram X) =
      ∑ s, data.quantumDimension s •
        Diagram.eval C (law.afterSimple s X) := by
  exact eval_ordinary_expansion data (fun s => law.afterSimple s X)

end OrdinaryKirbySlidingLaw

/--
One closed fixed-label slide window derived from the ordinary Kirby-colour
sliding law.

Because source and target are the same ribbon category, expanding the
possibly twisted colour on the moving component into simple labels reduces
each fixed label `x` to an ordinary Kirby-colour slide with exposed object
`simple x ⊗ exterior`.

No equality is stored in this structure.
-/
structure OrdinaryLabelIndexedSlidingWindow
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (law : OrdinaryKirbySlidingLaw data) where
  source : Boundary C
  target : Boundary C
  exterior : Diagram C source target
  context :
    (x : S) →
      Context C
        (.atom (data.simple x ⊗ source.denote))
        (.atom (data.simple x ⊗ target.denote))
        .unit .unit

namespace OrdinaryLabelIndexedSlidingWindow

variable
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {law : OrdinaryKirbySlidingLaw data}
    (window : OrdinaryLabelIndexedSlidingWindow data law)

/-- The open fixed-label diagram before ordinary Kirby-colour sliding. -/
noncomputable def openBefore (x : S) :
    Diagram C
      (.atom (data.simple x ⊗ window.source.denote))
      (.atom (data.simple x ⊗ window.target.denote)) :=
  law.toSourcedSlidingLaw.before_diagram
      (data.simple x ⊗ window.source.denote) ≫ᵈ
    liftExterior (data.simple x) window.exterior

/-- The open fixed-label diagram after ordinary Kirby-colour sliding. -/
noncomputable def openAfter (x : S) :
    Diagram C
      (.atom (data.simple x ⊗ window.source.denote))
      (.atom (data.simple x ⊗ window.target.denote)) :=
  liftExterior (data.simple x) window.exterior ≫ᵈ
    law.toSourcedSlidingLaw.after_diagram
      (data.simple x ⊗ window.target.denote)

/--
The fixed-label open slide follows from the ordinary sliding theorem and
naturality.  Crossings, extrema, and coupons remain visible in `exterior`.
-/
theorem open_term_sound (x : S) :
    Diagram.eval C (window.openBefore x) =
      Diagram.eval C (window.openAfter x) := by
  let ordinary := law.toSourcedSlidingLaw
  let exteriorMap :=
    (tensorLeft (data.simple x)).map
      (Diagram.eval C window.exterior)
  change
    Diagram.eval C
          (ordinary.before_diagram
            (data.simple x ⊗ window.source.denote)) ≫
        Diagram.eval C
          (liftExterior (data.simple x) window.exterior) =
      Diagram.eval C
          (liftExterior (data.simple x) window.exterior) ≫
        Diagram.eval C
          (ordinary.after_diagram
            (data.simple x ⊗ window.target.denote))
  calc
    _ = ordinary.before.app
          (data.simple x ⊗ window.source.denote) ≫ exteriorMap := by
      rw [ordinary.before_eval,
        liftExterior_eval (data.simple x) window.exterior]
      rfl
    _ = ordinary.after.app
          (data.simple x ⊗ window.source.denote) ≫ exteriorMap := by
      rw [ordinary.core_sound]
    _ = exteriorMap ≫
          ordinary.after.app
            (data.simple x ⊗ window.target.denote) :=
      (ordinary.after.naturality exteriorMap).symm
    _ = _ := by
      rw [liftExterior_eval (data.simple x) window.exterior,
        ordinary.after_eval]
      rfl

/-- Complete closed fixed-label diagram before the slide. -/
noncomputable def before (x : S) : Diagram C .unit .unit :=
  Context.plug C (window.context x) (window.openBefore x)

/-- Complete closed fixed-label diagram after the slide. -/
noncomputable def after (x : S) : Diagram C .unit .unit :=
  Context.plug C (window.context x) (window.openAfter x)

/-- Fully expanded fixed-simple endpoint before the ordinary-colour slide. -/
noncomputable def expandedBeforeTerm (x stationaryLabel : S) :
    Diagram C .unit .unit :=
  Context.plug C (window.context x)
    (law.beforeSimple stationaryLabel
        (data.simple x ⊗ window.source.denote) ≫ᵈ
      liftExterior (data.simple x) window.exterior)

/-- Fully expanded fixed-simple endpoint after the ordinary-colour slide. -/
noncomputable def expandedAfterTerm (x stationaryLabel : S) :
    Diagram C .unit .unit :=
  Context.plug C (window.context x)
    (liftExterior (data.simple x) window.exterior ≫ᵈ
      law.afterSimple stationaryLabel
        (data.simple x ⊗ window.target.denote))

/-- Explicit double sum before the slide; no Kirby colour is collapsed. -/
noncomputable def expandedLinearBefore (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  ∑ x : S, coefficient x •
    ∑ stationaryLabel : S,
      data.quantumDimension stationaryLabel •
        LinearDiagram.atom (R := K)
          (window.expandedBeforeTerm x stationaryLabel)

/-- Explicit double sum after the slide; no Kirby colour is collapsed. -/
noncomputable def expandedLinearAfter (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  ∑ x : S, coefficient x •
    ∑ stationaryLabel : S,
      data.quantumDimension stationaryLabel •
        LinearDiagram.atom (R := K)
          (window.expandedAfterTerm x stationaryLabel)

/-- The expanded before-fiber evaluates to the collapsed ordinary window. -/
theorem expanded_before_fiber_eval (x : S) :
    LinearDiagram.eval
        (∑ stationaryLabel : S,
          data.quantumDimension stationaryLabel •
            LinearDiagram.atom (R := K)
              (window.expandedBeforeTerm x stationaryLabel)) =
      Diagram.eval C (window.before x) := by
  let exterior :=
    liftExterior (data.simple x) window.exterior
  let linearContext :=
    LinearContext.evalContextLinearMap (R := K) (window.context x)
  have openExpansion :
      (∑ stationaryLabel : S,
          data.quantumDimension stationaryLabel •
            Diagram.eval C
              (law.beforeSimple stationaryLabel
                  (data.simple x ⊗ window.source.denote) ≫ᵈ exterior)) =
        Diagram.eval C (window.openBefore x) := by
    calc
      _ =
          (∑ stationaryLabel : S,
              data.quantumDimension stationaryLabel •
                Diagram.eval C
                  (law.beforeSimple stationaryLabel
                    (data.simple x ⊗ window.source.denote))) ≫
            Diagram.eval C exterior := by
        rw [Preadditive.sum_comp]
        simp [Diagram.eval]
      _ =
          Diagram.eval C
              (law.toSourcedSlidingLaw.before_diagram
                (data.simple x ⊗ window.source.denote)) ≫
            Diagram.eval C exterior := by
        rw [law.before_is_dimension_weighted]
      _ = Diagram.eval C (window.openBefore x) := by
        rfl
  calc
    _ = ∑ stationaryLabel : S,
        data.quantumDimension stationaryLabel •
          Diagram.eval C
            (window.expandedBeforeTerm x stationaryLabel) := by
      simp
    _ = linearContext
        (∑ stationaryLabel : S,
          data.quantumDimension stationaryLabel •
            Diagram.eval C
              (law.beforeSimple stationaryLabel
                  (data.simple x ⊗ window.source.denote) ≫ᵈ exterior)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro stationaryLabel _
      rw [map_smul]
      exact congrArg
        (fun value => data.quantumDimension stationaryLabel • value)
        (LinearContext.evalContextLinearMap_diagram
          (window.context x)
          (law.beforeSimple stationaryLabel
              (data.simple x ⊗ window.source.denote) ≫ᵈ exterior)).symm
    _ = linearContext (Diagram.eval C (window.openBefore x)) :=
      congrArg linearContext openExpansion
    _ = Diagram.eval C (window.before x) :=
      LinearContext.evalContextLinearMap_diagram
        (window.context x) (window.openBefore x)

/-- The expanded after-fiber evaluates to the collapsed ordinary window. -/
theorem expanded_after_fiber_eval (x : S) :
    LinearDiagram.eval
        (∑ stationaryLabel : S,
          data.quantumDimension stationaryLabel •
            LinearDiagram.atom (R := K)
              (window.expandedAfterTerm x stationaryLabel)) =
      Diagram.eval C (window.after x) := by
  let exterior :=
    liftExterior (data.simple x) window.exterior
  let linearContext :=
    LinearContext.evalContextLinearMap (R := K) (window.context x)
  have openExpansion :
      (∑ stationaryLabel : S,
          data.quantumDimension stationaryLabel •
            Diagram.eval C
              (exterior ≫ᵈ
                law.afterSimple stationaryLabel
                  (data.simple x ⊗ window.target.denote))) =
        Diagram.eval C (window.openAfter x) := by
    calc
      _ =
          Diagram.eval C exterior ≫
            (∑ stationaryLabel : S,
              data.quantumDimension stationaryLabel •
                Diagram.eval C
                  (law.afterSimple stationaryLabel
                    (data.simple x ⊗ window.target.denote))) := by
        rw [Preadditive.comp_sum]
        simp [Diagram.eval]
      _ =
          Diagram.eval C exterior ≫
            Diagram.eval C
              (law.toSourcedSlidingLaw.after_diagram
                (data.simple x ⊗ window.target.denote)) := by
        rw [law.after_is_dimension_weighted]
      _ = Diagram.eval C (window.openAfter x) := by
        rfl
  calc
    _ = ∑ stationaryLabel : S,
        data.quantumDimension stationaryLabel •
          Diagram.eval C
            (window.expandedAfterTerm x stationaryLabel) := by
      simp
    _ = linearContext
        (∑ stationaryLabel : S,
          data.quantumDimension stationaryLabel •
            Diagram.eval C
              (exterior ≫ᵈ
                law.afterSimple stationaryLabel
                  (data.simple x ⊗ window.target.denote))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro stationaryLabel _
      rw [map_smul]
      exact congrArg
        (fun value => data.quantumDimension stationaryLabel • value)
        (LinearContext.evalContextLinearMap_diagram
          (window.context x)
          (exterior ≫ᵈ
            law.afterSimple stationaryLabel
              (data.simple x ⊗ window.target.denote))).symm
    _ = linearContext (Diagram.eval C (window.openAfter x)) :=
      congrArg linearContext openExpansion
    _ = Diagram.eval C (window.after x) :=
      LinearContext.evalContextLinearMap_diagram
        (window.context x) (window.openAfter x)

/-- Closing in an arbitrary typed context preserves the fixed-label proof. -/
theorem term_sound (x : S) :
    Diagram.eval C (window.before x) =
      Diagram.eval C (window.after x) :=
  Context.eval_plug_congr C (window.context x)
    (window.open_term_sound x)

/-- The explicit double sum is the same evaluator-side slide calculation. -/
theorem expanded_linear_eval_sound (coefficient : S → K) :
    LinearDiagram.eval (window.expandedLinearBefore coefficient) =
      LinearDiagram.eval (window.expandedLinearAfter coefficient) := by
  simp only [expandedLinearBefore, expandedLinearAfter, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg (fun value => coefficient x • value) (by
    simpa only [map_sum, map_smul, LinearDiagram.eval_atom] using
      ((window.expanded_before_fiber_eval x).trans
        ((window.term_sound x).trans
          (window.expanded_after_fiber_eval x).symm)))

/-- Formal coefficient-weighted sum before the fixed-label slides. -/
noncomputable def linearBefore (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum (R := K) coefficient window.before

/-- Formal coefficient-weighted sum after the fixed-label slides. -/
noncomputable def linearAfter (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum (R := K) coefficient window.after

/--
Any finite coefficient system, including a homologically twisted Kirby
colour, slides term by term over the ordinary Kirby colour.
-/
theorem linear_eval_sound (coefficient : S → K) :
    eval (R := K) (window.linearBefore coefficient) =
      eval (R := K) (window.linearAfter coefficient) := by
  simp only [linearBefore, linearAfter, eval_weightedSum]
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg (fun morphism => coefficient x • morphism)
    (window.term_sound x)

end OrdinaryLabelIndexedSlidingWindow

end TwistedYetter.Kirby.EGNOKirbyColorEncircling
