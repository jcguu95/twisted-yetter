import TwistedYetter.Kirby.Final.Semantics.IndependentAlgebraicInput
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Independent human specification of ribbon graphical calculus

This file is normative.  It was written without importing or inspecting this
repository's graphical calculus, evaluator, Kirby-move proofs, Sage code, or
compatibility bridge.

It pins only the translation

`typed ribbon diagram → morphism in 𝒞 → scalar for a closed diagram`.

It does not contain a Kirby move, dotted handle, homology class,
four-manifold descent, or evaluator equality.

The language has general ordered multi-input, multi-output morphism coupons.
A character coupon is only a unary special case.  Moving a general coupon
across a turn changes it to the appropriate mate; it is never silently
identified with the original morphism.
-/

namespace TwistedYetter.Kirby.Final.IndependentGraphicalCalculusSpecification

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]

/--
The direction of a ribbon strand in the expanded graphical language.

This is not an orientation on a Kirby component.  It is local boundary data
of a typed ribbon graph.
-/
inductive StrandDirection
  | forward
  | backward
  deriving DecidableEq, Repr

/-- One directed, object-labelled ribbon end. -/
structure DirectedObject where
  object : C
  direction : StrandDirection

/-- Reverse direction is interpreted by the selected right dual. -/
def DirectedObject.value : DirectedObject (C := C) → C
  | ⟨X, .forward⟩ => X
  | ⟨X, .backward⟩ => Xᘁ

/--
An ordered boundary tensor word.  The empty word denotes the tensor unit.
The list order is the left-to-right order seen by the graphical reader.
-/
abbrev TensorWord := List (DirectedObject (C := C))

/-- Parenthesization convention: right-associated, with the empty word `𝟙`. -/
def TensorWord.value : TensorWord (C := C) → C
  | [] => 𝟙_ C
  | X :: tail => X.value ⊗ TensorWord.value tail

/--
A completely general coupon.

The ordered input and output words may have any finite lengths.  Fusion
vertices, their duals, unit-cut maps, and character coupons are all special
cases of this one definition.
-/
structure MorphismCoupon
    (input output : TensorWord (C := C)) where
  morphism : input.value ⟶ output.value

/--
The free typed syntax before quotienting by ribbon graphical relations.

Diagrams are read bottom-to-top; tensor factors are read left-to-right.
Associators and unitors needed by the fixed right-associated convention are
inserted by the interpretation, not erased by definitional equality.
-/
inductive RibbonDiagram :
    TensorWord (C := C) →
      TensorWord (C := C) →
      Type (max uC vC)
  | identity (word) :
      RibbonDiagram word word
  | coupon {input output}
      (coupon : MorphismCoupon input output) :
      RibbonDiagram input output
  | compose {source middle target}
      (first : RibbonDiagram source middle)
      (second : RibbonDiagram middle target) :
      RibbonDiagram source target
  | tensor {source₁ target₁ source₂ target₂}
      (left : RibbonDiagram source₁ target₁)
      (right : RibbonDiagram source₂ target₂) :
      RibbonDiagram (source₁ ++ source₂) (target₁ ++ target₂)
  | positiveCrossing (X Y : DirectedObject (C := C)) :
      RibbonDiagram [X, Y] [Y, X]
  | negativeCrossing (X Y : DirectedObject (C := C)) :
      RibbonDiagram [X, Y] [Y, X]
  | leftEvaluation (X : C) :
      RibbonDiagram
        [⟨X, .backward⟩, ⟨X, .forward⟩]
        []
  | leftCoevaluation (X : C) :
      RibbonDiagram
        []
        [⟨X, .forward⟩, ⟨X, .backward⟩]
  | rightEvaluation (X : C) :
      RibbonDiagram
        [⟨X, .forward⟩, ⟨X, .backward⟩]
        []
  | rightCoevaluation (X : C) :
      RibbonDiagram
        []
        [⟨X, .backward⟩, ⟨X, .forward⟩]
  | positiveTwist (X : DirectedObject (C := C)) :
      RibbonDiagram [X] [X]
  | negativeTwist (X : DirectedObject (C := C)) :
      RibbonDiagram [X] [X]

/--
The interpretation of every generator as a category morphism.

This is the only semantic target.  There is no independent arbitrary
function from diagrams to scalars.
-/
structure RibbonDiagramInterpretation where
  interpret :
    {source target : TensorWord (C := C)} →
      RibbonDiagram source target →
      source.value ⟶ target.value

  identity :
    (word : TensorWord (C := C)) →
      interpret (.identity word) = 𝟙 word.value

  coupon :
    {input output : TensorWord (C := C)} →
      (f : MorphismCoupon input output) →
      interpret (.coupon f) = f.morphism

  compose :
    {source middle target : TensorWord (C := C)} →
      (first : RibbonDiagram source middle) →
      (second : RibbonDiagram middle target) →
      interpret (.compose first second) =
        interpret first ≫ interpret second

  positiveCrossing_forward :
    (X Y : C) →
      interpret
        (.positiveCrossing
          ⟨X, .forward⟩
          ⟨Y, .forward⟩) =
        (β_ X Y).hom

  negativeCrossing_forward :
    (X Y : C) →
      interpret
        (.negativeCrossing
          ⟨X, .forward⟩
          ⟨Y, .forward⟩) =
        (β_ X Y).inv

  leftEvaluation :
    (X : C) →
      interpret (.leftEvaluation X) = eval X

  leftCoevaluation :
    (X : C) →
      interpret (.leftCoevaluation X) = coevaluation X

/--
An exact, finite list of the local relations admitted by the graphical
quotient.  The equations themselves are stated in the accompanying human
specification and are realized by `GraphicalRelationSoundness` below.
-/
inductive GraphicalRelationKind
  | categoryIdentity
  | categoryAssociativity
  | tensorIdentity
  | tensorAssociativity
  | tensorInterchange
  | braidingNaturality
  | positiveNegativeCrossingCancellation
  | firstHexagon
  | secondHexagon
  | leftSnake
  | rightSnake
  | twistNaturality
  | balancing
  | twistDualCompatibility
  | couponComposition
  | couponTensor
  | couponAcrossCupAsMate
  | couponAcrossCapAsMate
  | sphericalClosure
  deriving DecidableEq, Repr

/--
One typed instance of one named local relation.

`before` and `after` have exactly the same boundary.  The kind cannot be an
unnamed catch-all relation.
-/
structure GraphicalRelationInstance
    (source target : TensorWord (C := C)) where
  kind : GraphicalRelationKind
  before : RibbonDiagram source target
  after : RibbonDiagram source target

/--
The narrow graphical-coherence boundary.

Every listed local relation has equal categorical interpretations.  This says
nothing about Kirby moves or four-manifolds.
-/
structure GraphicalRelationSoundness
    (semantics : RibbonDiagramInterpretation (C := C)) where
  sound :
    {source target : TensorWord (C := C)} →
      (relation : GraphicalRelationInstance source target) →
      semantics.interpret relation.before =
        semantics.interpret relation.after

/--
A mate operation used when a general coupon passes a cup or cap.

The moved coupon is the corresponding mate; the original morphism is not
silently reused.
-/
structure CouponMateSemantics where
  rightMate :
    {input output : TensorWord (C := C)} →
      MorphismCoupon input output →
      MorphismCoupon
        ([⟨output.value, .backward⟩])
        ([⟨input.value, .backward⟩])

  leftMate :
    {input output : TensorWord (C := C)} →
      MorphismCoupon input output →
      MorphismCoupon
        ([⟨output.value, .backward⟩])
        ([⟨input.value, .backward⟩])

/--
Explicit simple-channel inclusions and projections.

The full completeness relation sums over every simple label and every
multiplicity index.  The tensor-unit projector below keeps only the unit
label.
-/
structure FusionResolutionSemantics
    {S : Type} [Fintype S] [DecidableEq S]
    (fusion :
      IndependentAlgebraicInput.FusionCategorySemantics
        (K := K) (C := C) (S := S)) where
  unitLabel : S
  unitSimpleIso : fusion.simple unitLabel ≅ 𝟙_ C

  inclusion :
    (V : C) →
      (s : S) →
      Fin (fusion.multiplicity V s) →
      fusion.simple s ⟶ V

  projection :
    (V : C) →
      (s : S) →
      Fin (fusion.multiplicity V s) →
      V ⟶ fusion.simple s

  orthogonality :
    (V : C) →
      (s t : S) →
      (μ : Fin (fusion.multiplicity V s)) →
      (ν : Fin (fusion.multiplicity V t)) →
      inclusion V s μ ≫ projection V t ν =
        if h : s = t ∧ μ.val = ν.val
        then eqToHom (by subst h.1; simp_all)
        else 0

  completeness :
    (V : C) →
      ∑ s, ∑ μ,
        projection V s μ ≫ inclusion V s μ =
          𝟙 V

/--
The tensor-unit summand projector derived from the fusion resolution.

It is not a transparent-sector projector.
-/
noncomputable def tensorUnitProjector
    {S : Type} [Fintype S] [DecidableEq S]
    {fusion :
      IndependentAlgebraicInput.FusionCategorySemantics
        (K := K) (C := C) (S := S)}
    (resolution : FusionResolutionSemantics fusion)
    (V : C) : V ⟶ V :=
  ∑ μ,
    resolution.projection V resolution.unitLabel μ ≫
      resolution.inclusion V resolution.unitLabel μ

/--
Closed evaluation is forced to factor through an endomorphism of the tensor
unit and the scalar identification `End(𝟙) = K`.
-/
structure ClosedRibbonScalarSemantics
    {S : Type} [Fintype S] [DecidableEq S]
    (fusion :
      IndependentAlgebraicInput.FusionCategorySemantics
        (K := K) (C := C) (S := S))
    (interpretation : RibbonDiagramInterpretation (C := C)) where
  scalar :
    RibbonDiagram ([] : TensorWord (C := C)) [] → K

  scalar_is_unit_endomorphism_coefficient :
    (diagram : RibbonDiagram ([] : TensorWord (C := C)) []) →
      interpretation.interpret diagram =
        scalar diagram • 𝟙 (𝟙_ C)

end TwistedYetter.Kirby.Final.IndependentGraphicalCalculusSpecification
