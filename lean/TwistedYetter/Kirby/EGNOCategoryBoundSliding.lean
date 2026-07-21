import TwistedYetter.Fusion.EGNOSphericalInsertion
import TwistedYetter.Kirby.EGNOKirbyColorExpansion
import TwistedYetter.Kirby.FramedSliding
import TwistedYetter.Kirby.GeneralizedSliding
import TwistedYetter.Kirby.Presentation

/-!
# Label-indexed generalized sliding from ribbon fusion data

The generalized slide of Bärenz--Barrett Lemma 3.3 fixes an actual object
`X`.  After a Kirby colour is expanded, `X` is one simple label at a time; it
is not a single category object representing the whole formal colour.

This module therefore constructs one `SlidingCategoryData` for every simple
label.  The forward insertion, mate transport, and inverse insertion are
derived from:

* a ribbon fusion category;
* the all-objects spherical insertion law;
* the all-objects spherical mate trace law.

Only the framed graphical movies remain a separate all-label input.  No field
below states the desired endpoint equality.
-/

namespace TwistedYetter.Kirby.EGNOCategoryBoundSliding

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Fusion.FiniteResolution
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOKirbyColorExpansion
open TwistedYetter.Kirby.FramedSliding
open TwistedYetter.Kirby.GeneralizedSliding
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
The channel index for a fixed sliding label `x`, the Kirby-colour label `y`,
and the inserted simple channel `z`.
-/
abbrev SlidingIndex (x y z : S) :=
  data.InsertionIndex
    (data.simple x ⊗ (data.simple y)ᘁ) z

/-- The source trace-dual basis before the mate change. -/
noncomputable def slidingForwardBasis (x y z : S) :
    DualBasisData (ι := SlidingIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple x ⊗ (data.simple y)ᘁ)
        (data.simple z)) :=
  data.insertionDualBasis
    (data.simple x ⊗ (data.simple y)ᘁ) z

/-- Cyclicity reverses the insertion pairing before the mate operation. -/
theorem slidingSourcePairingCyclic
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
noncomputable def slidingMateSourceBasis (x y z : S) :
    DualBasisData (ι := SlidingIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple z)
        (data.simple x ⊗ (data.simple y)ᘁ)) :=
  (slidingForwardBasis data x y z).reversed
    (slidingSourcePairingCyclic data x y z)

/-- The canonical pairing-preserving mate transport for one channel. -/
noncomputable def slidingMateTransport
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
noncomputable def slidingMatedBasis
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x y z : S) :
    DualBasisData (ι := SlidingIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        (data.simple y)
        ((data.simple z)ᘁ ⊗ data.simple x)) :=
  (slidingMateTransport data mateLaw x y z).dualBasisData
    (slidingMateSourceBasis data x y z)

/--
Cyclicity identifies the target pairing with the reversed mated pairing.
-/
theorem slidingPairingCyclic
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
noncomputable def slidingBackwardBasis
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x y z : S) :
    DualBasisData (ι := SlidingIndex data x y z)
      (data.toFusionCategoryData.pivotalTracePerfectPairing
        data.pivotal
        ((data.simple z)ᘁ ⊗ data.simple x)
        (data.simple y)) :=
  (slidingMatedBasis data mateLaw x y z).reversed
    (slidingPairingCyclic data x y z)

/-- Forward dimension-weighted insertion is an instance of the global law. -/
theorem slidingForwardSound
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (x y : S) :
    ∑ z, ∑ i : SlidingIndex data x y z,
      data.quantumDimension z •
        ((slidingForwardBasis data x y z).primal i ≫
          (slidingForwardBasis data x y z).dual i) =
      𝟙 (data.simple x ⊗ (data.simple y)ᘁ) :=
  insertionLaw.resolves
    (data.simple x ⊗ (data.simple y)ᘁ)
    (slidingForwardBasis data x y)

/-- Inverse insertion after the mate change is derived from the same law. -/
theorem slidingBackwardSound
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x z : S) :
    ∑ y, ∑ i : SlidingIndex data x y z,
      data.quantumDimension y •
        ((slidingMatedBasis data mateLaw x y z).dual i ≫
          (slidingMatedBasis data mateLaw x y z).primal i) =
      𝟙 ((data.simple z)ᘁ ⊗ data.simple x) := by
  have resolved :=
    insertionLaw.resolves
      ((data.simple z)ᘁ ⊗ data.simple x)
      (fun y => slidingBackwardBasis data mateLaw x y z)
  simpa only [
    slidingBackwardBasis,
    DualBasisData.reverse_primal,
    DualBasisData.reverse_dual
  ] using resolved

/--
The generalized-sliding algebra for one actual simple label `x`.

Every algebraic equality is now derived from the two global standard laws.
-/
noncomputable def slidingCategoryData
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical)
    (x : S) :
    SlidingCategoryData
      (R := K) (D := C) (S := S) (I := SlidingIndex data x) where
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
      (slidingMatedBasis data mateLaw x y z)
  forwardProjection y z i :=
    (slidingForwardBasis data x y z).primal i
  forwardInclusion y z i :=
    (slidingForwardBasis data x y z).dual i
  forwardSound y :=
    slidingForwardSound data insertionLaw x y
  backwardSound z := by
    simpa only [BiorthogonalFamily.ofDualBasisData] using
      slidingBackwardSound data insertionLaw mateLaw x z
  pivotal_source_ref := "ref:baerenz-barrett-dichromatic-2018"
  pivotal_source_locator :=
    "Lemmas 2.37 and 3.3, equations (2.2.5) and (3.1.3)-(3.1.11)"

end CategoryData

/--
The framed graphical part of Lemmas 3.3--3.4, quantified over every simple
label that can occur in the formal Kirby-colour expansion.

`SlidingFamily` contains contexts and certified local movies.  Its core
endpoint equality is still derived by `GeneralizedSliding`; it is not a field
of this structure.
-/
structure LabelIndexedSlidingMovies
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data)
    (mateLaw : SphericalMateTraceLaw (K := K) data.spherical) where
  family :
    (x : S) →
      SlidingFamily
        (CategoryData.slidingCategoryData data insertionLaw mateLaw x)
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemmas 3.3-3.4, equations (3.1.3)-(3.1.11), journal pages 681-684"
  graphicalCertificateHash : String
  graphical_certificate_hash_shape :
    TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
      graphicalCertificateHash = true

namespace LabelIndexedSlidingMovies

variable
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} data}
    {mateLaw : SphericalMateTraceLaw (K := K) data.spherical}

/--
One closed generalized-slide window for every possible simple label on the
sliding two-handle.
-/
structure ClosedWindow
    (movies : LabelIndexedSlidingMovies data insertionLaw mateLaw) where
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
    {movies : LabelIndexedSlidingMovies data insertionLaw mateLaw}
    (window : ClosedWindow movies)

/-- The complete closed diagram before sliding one fixed simple label. -/
noncomputable def before (x : S) : Diagram C .unit .unit :=
  Context.plug C (window.context x)
    (beforeExterior
      (movies.family x).sourcedFunctorSlidingLaw
      window.exterior)

/-- The complete closed diagram after sliding the same fixed simple label. -/
noncomputable def after (x : S) : Diagram C .unit .unit :=
  Context.plug C (window.context x)
    (afterExterior
      (movies.family x).sourcedFunctorSlidingLaw
      window.exterior)

/-- Every fixed-label term is proved by the derived Lemma 3.4 movie. -/
theorem term_sound (x : S) :
    Diagram.eval C (window.before x) =
      Diagram.eval C (window.after x) :=
  SlidingFamily.lemma34Movie_sound
    (movies.family x) window.exterior (window.context x)

/-- Formal weighted sum of all fixed-label diagrams before the slide. -/
noncomputable def linearBefore (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum (R := K) coefficient window.before

/-- Formal weighted sum of all fixed-label diagrams after the slide. -/
noncomputable def linearAfter (coefficient : S → K) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum (R := K) coefficient window.after

/--
Termwise generalized sliding lifts to any unchanged outer coefficient.

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
        (collapse (R := K) "BB-label-indexed-slide-before"
          (window.linearBefore coefficient)) =
      Diagram.eval C
        (collapse (R := K) "BB-label-indexed-slide-after"
          (window.linearAfter coefficient)) :=
  window.linear_eval_sound coefficient

end ClosedWindow

end LabelIndexedSlidingMovies

/--
The ordinary Kirby-colour slide of Bärenz--Barrett Lemma 3.1, bound to the
actual formal family `sum_s dim(s) s`.

The one global `core_sound` field is the cited sliding theorem.  The two
endpoint diagrams and their evaluations are forced to be the dimension-
weighted expansions of the category's listed simples.
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
  diagram_schema : String :=
    "twisted-yetter.egno-ordinary-kirby-slide.v1"
  diagram_content_hash : String
  diagram_content_hash_shape :
    TwistedYetter.Kirby.Presentation.RawPresentation.sha256Shape
      diagram_content_hash = true
  source_ref : String := "ref:baerenz-barrett-dichromatic-2018"
  source_locator : String :=
    "Lemma 3.1, equation (3.1.1), journal pages 680-681"

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
  diagram_schema := law.diagram_schema
  diagram_content_hash := law.diagram_content_hash
  source_ref := law.source_ref
  source_locator := law.source_locator

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

For the identity ribbon functor used by the modular invariant, the object
called `F(X)` in Bärenz--Barrett is just the actual object `X`.  Hence, after
expanding the possibly twisted colour on the sliding component into simple
labels, every fixed label `x` is an ordinary Kirby-colour slide with
`X = simple x ⊗ exterior`.  This is the formal content of Remark 3.5.

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

/-- Closing in an arbitrary typed context preserves the fixed-label proof. -/
theorem term_sound (x : S) :
    Diagram.eval C (window.before x) =
      Diagram.eval C (window.after x) :=
  Context.eval_plug_congr C (window.context x)
    (window.open_term_sound x)

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

end TwistedYetter.Kirby.EGNOCategoryBoundSliding
