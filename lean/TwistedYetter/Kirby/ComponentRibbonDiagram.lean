import TwistedYetter.Fusion.EGNOPremodularModular
import TwistedYetter.Fusion.EGNOTracePairing
import TwistedYetter.Kirby.CanonicalKirbyTrace
import TwistedYetter.Kirby.CategoricalPresentationCompiler
import TwistedYetter.Kirby.CategoricalTangle
import TwistedYetter.Kirby.FramingNaturality
import TwistedYetter.Kirby.Presentation

/-!
# Category-neutral component ribbon diagrams

This file is the topology/category firewall for the canonical Kirby
evaluator.

`ComponentDiagram` is a free, typed ribbon-diagram syntax whose atoms contain
only a component ID and an orientation.  It contains no category object,
morphism, scalar, evaluator value, or equality of evaluator values.

Given a premodular category and a simple label for every component ID,
`ComponentDiagram.interpret` deterministically produces the categorical
diagram.  Thus a topology-side local movie can be recorded once in this free
syntax and interpreted in every admitted category; it need not carry a
category-specific `Diagram` or a polymorphic equality.

The syntax deliberately includes explicit associators and unitors.  We do not
silently strictify the monoidal category.
-/

namespace TwistedYetter.Kirby.ComponentRibbonDiagram

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalKirbyTrace
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.Presentation

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance componentRibbonSelectedRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-- One oriented occurrence of a serialized link component. -/
structure ComponentAtom where
  componentId : String
  orientation : Orientation
  deriving Repr, BEq, DecidableEq

/-- The positively oriented occurrence of one component. -/
def positiveAtom (componentId : String) : ComponentAtom where
  componentId := componentId
  orientation := .positive

/-- The negatively oriented occurrence of one component. -/
def negativeAtom (componentId : String) : ComponentAtom where
  componentId := componentId
  orientation := .negative

/--
Interpret one component occurrence by a supplied simple-label environment.

The environment, rather than a presentation-specific indexing function, is
the input.  This lets the same free diagram be interpreted on both sides of
a component-preserving move after the finite label reindexing is proved.
-/
def ComponentAtom.interpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S) :
    ComponentAtom → C
  | ⟨componentId, .positive⟩ =>
      𝒞.simple (labelOf componentId)
  | ⟨componentId, .negative⟩ =>
      (𝒞.simple (labelOf componentId))ᘁ

/-- Parenthesized component boundary before choosing a category. -/
inductive ComponentBoundary where
  | unit
  | atom (component : ComponentAtom)
  | tensor (left right : ComponentBoundary)
  deriving Repr, BEq, DecidableEq

namespace ComponentBoundary

/-- Forget strand IDs while retaining component lineage and orientation. -/
def ofStrand (strand : StrandState) : ComponentAtom where
  componentId := strand.componentId
  orientation := strand.orientation

/-- Right-associated component boundary used by the canonical trace. -/
def word : List StrandState → ComponentBoundary
  | [] =>
      .unit
  | strand :: [] =>
      .atom (ofStrand strand)
  | strand :: next :: rest =>
      .tensor (.atom (ofStrand strand))
        (word (next :: rest))

/-- Interpret a free component boundary in the selected category. -/
def interpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S) :
    ComponentBoundary → Boundary C
  | .unit =>
      .unit
  | .atom component =>
      .atom (component.interpret 𝒞 labelOf)
  | .tensor left right =>
      .tensor (left.interpret 𝒞 labelOf)
        (right.interpret 𝒞 labelOf)

/-- Every component ID occurring in a free boundary. -/
def componentIds : ComponentBoundary → List String
  | .unit =>
      []
  | .atom component =>
      [component.componentId]
  | .tensor left right =>
      left.componentIds ++ right.componentIds

/-- Boundary interpretation depends only on labels of IDs in that boundary. -/
theorem interpret_eq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    (boundary : ComponentBoundary)
    (agree :
      (componentId : String) →
      componentId ∈ boundary.componentIds →
        leftLabels componentId = rightLabels componentId) :
    boundary.interpret 𝒞 leftLabels =
      boundary.interpret 𝒞 rightLabels := by
  induction boundary with
  | unit =>
      rfl
  | atom component =>
      have labelEq :
          leftLabels component.componentId =
            rightLabels component.componentId :=
        agree component.componentId (by simp [componentIds])
      cases component with
      | mk componentId orientation =>
          cases orientation with
          | positive =>
              exact congrArg Boundary.atom
                (congrArg 𝒞.simple labelEq)
          | negative =>
              exact congrArg Boundary.atom
                (congrArg
                  (fun simpleLabel => (𝒞.simple simpleLabel)ᘁ)
                  labelEq)
  | tensor left right leftIH rightIH =>
      simp only [interpret]
      rw [leftIH (fun componentId membership =>
        agree componentId (by
          simp only [componentIds, List.mem_append]
          exact Or.inl membership))]
      rw [rightIH (fun componentId membership =>
        agree componentId (by
          simp only [componentIds, List.mem_append]
          exact Or.inr membership))]

/-- Interpreting the free word is the ordinary categorical boundary word. -/
theorem interpret_word
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    (strands : List StrandState) :
    (word strands).interpret 𝒞 labelOf =
      TwistedYetter.Kirby.CategoricalPresentationCompiler.boundaryWord
        (fun strand =>
          (ofStrand strand).interpret 𝒞 labelOf)
        strands := by
  induction strands with
  | nil =>
      rfl
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          rfl
      | cons second tail =>
          simpa only [word, interpret,
            TwistedYetter.Kirby.CategoricalPresentationCompiler.boundaryWord]
            using congrArg
              (fun boundary =>
                Boundary.tensor
                  (.atom ((ofStrand first).interpret 𝒞 labelOf))
                  boundary)
              inductionHypothesis

end ComponentBoundary

/--
Typed, category-neutral ribbon-diagram syntax.

The two cap orders are separate constructors.  In a pivotal category they use
different exact pairings; conflating them is a common source of silent mirror
or duality errors.
-/
inductive ComponentDiagram :
    ComponentBoundary → ComponentBoundary → Type
  | identity (boundary : ComponentBoundary) :
      ComponentDiagram boundary boundary
  | comp
      {source middle target : ComponentBoundary} :
      ComponentDiagram source middle →
      ComponentDiagram middle target →
      ComponentDiagram source target
  | tensor
      {leftSource leftTarget rightSource rightTarget :
        ComponentBoundary} :
      ComponentDiagram leftSource leftTarget →
      ComponentDiagram rightSource rightTarget →
      ComponentDiagram
        (.tensor leftSource rightSource)
        (.tensor leftTarget rightTarget)
  | crossingPositive
      (left right : ComponentBoundary) :
      ComponentDiagram
        (.tensor left right) (.tensor right left)
  | crossingNegative
      (left right : ComponentBoundary) :
      ComponentDiagram
        (.tensor left right) (.tensor right left)
  | cupPositiveNegative
      (componentId : String) :
      ComponentDiagram .unit
        (.tensor
          (.atom (positiveAtom componentId))
          (.atom (negativeAtom componentId)))
  | cupNegativePositive
      (componentId : String) :
      ComponentDiagram .unit
        (.tensor
          (.atom (negativeAtom componentId))
          (.atom (positiveAtom componentId)))
  | capNegativePositive
      (componentId : String) :
      ComponentDiagram
        (.tensor
          (.atom (negativeAtom componentId))
          (.atom (positiveAtom componentId)))
        .unit
  | capPositiveNegative
      (componentId : String) :
      ComponentDiagram
        (.tensor
          (.atom (positiveAtom componentId))
          (.atom (negativeAtom componentId)))
        .unit
  | identityCoupon
      (couponId : String)
      (boundary : ComponentBoundary) :
      ComponentDiagram boundary boundary
  | twistPositive
      (component : ComponentAtom) :
      ComponentDiagram (.atom component) (.atom component)
  | twistNegative
      (component : ComponentAtom) :
      ComponentDiagram (.atom component) (.atom component)
  | associatorHom
      (left middle right : ComponentBoundary) :
      ComponentDiagram
        (.tensor (.tensor left middle) right)
        (.tensor left (.tensor middle right))
  | associatorInv
      (left middle right : ComponentBoundary) :
      ComponentDiagram
        (.tensor left (.tensor middle right))
        (.tensor (.tensor left middle) right)
  | leftUnitorHom
      (boundary : ComponentBoundary) :
      ComponentDiagram (.tensor .unit boundary) boundary
  | leftUnitorInv
      (boundary : ComponentBoundary) :
      ComponentDiagram boundary (.tensor .unit boundary)
  | rightUnitorHom
      (boundary : ComponentBoundary) :
      ComponentDiagram (.tensor boundary .unit) boundary
  | rightUnitorInv
      (boundary : ComponentBoundary) :
      ComponentDiagram boundary (.tensor boundary .unit)

namespace ComponentDiagram

infixr:70 " ⊗ᶜ " => ComponentDiagram.tensor
infixr:60 " ≫ᶜ " => ComponentDiagram.comp

/--
Disjoint union of two closed free diagrams, with unitors retained.

This is the category-neutral counterpart of the categorical
`closedTensorDiagram`.  It is used by cancellation geometry so isolation of
the cancelling pair is an equality of free syntax, not an equality of final
scalars.
-/
def closedTensor
    (left right : ComponentDiagram .unit .unit) :
    ComponentDiagram .unit .unit :=
  .leftUnitorInv .unit ≫ᶜ
    (left ⊗ᶜ right) ≫ᶜ
    .leftUnitorHom .unit

/-- Free zero-framed oriented unknot with the selected component ID. -/
def zeroFramedUnknot (componentId : String) :
    ComponentDiagram .unit .unit :=
  .cupPositiveNegative componentId ≫ᶜ
    .capPositiveNegative componentId

/--
The dotted meridian of a cancelling 1--2 pair, cut open along the two-handle
strand.

Writing this open tangle in the free component syntax makes its later pivotal
closure literal rather than an unproved picture-level identification.
-/
def openDottedEncircling
    (dottedId twoHandleId : String) :
    ComponentDiagram
      (.atom (positiveAtom twoHandleId))
      (.atom (positiveAtom twoHandleId)) :=
  let dotted : ComponentBoundary :=
    .atom (positiveAtom dottedId)
  let dottedDual : ComponentBoundary :=
    .atom (negativeAtom dottedId)
  let twoHandle : ComponentBoundary :=
    .atom (positiveAtom twoHandleId)
  .leftUnitorInv twoHandle ≫ᶜ
    (.cupPositiveNegative dottedId ⊗ᶜ .identity twoHandle) ≫ᶜ
    .associatorHom dotted dottedDual twoHandle ≫ᶜ
    (.identity dotted ⊗ᶜ
      (.crossingPositive dottedDual twoHandle ≫ᶜ
        .crossingPositive twoHandle dottedDual)) ≫ᶜ
    .associatorInv dotted dottedDual twoHandle ≫ᶜ
    (.capPositiveNegative dottedId ⊗ᶜ .identity twoHandle) ≫ᶜ
    .leftUnitorHom twoHandle

/--
Free positive Hopf pair used by a cancelling 1--2 handle pair.

The first component is the dotted one-handle circle and the second is its
zero-framed meridian.  This is definitionally the pivotal closure of
`openDottedEncircling`; both positive crossings remain explicit.
-/
def oneTwoHopfPair
    (dottedId twoHandleId : String) :
    ComponentDiagram .unit .unit :=
  let twoHandleDual : ComponentBoundary :=
    .atom (negativeAtom twoHandleId)
  .cupPositiveNegative twoHandleId ≫ᶜ
    (openDottedEncircling dottedId twoHandleId ⊗ᶜ
      .identity twoHandleDual) ≫ᶜ
    .capPositiveNegative twoHandleId

/-- Every component ID inspected by a free diagram. -/
def componentIds :
    {source target : ComponentBoundary} →
      ComponentDiagram source target → List String
  | _, _, .identity boundary =>
      boundary.componentIds
  | _, _, .comp first second =>
      first.componentIds ++ second.componentIds
  | _, _, .tensor left right =>
      left.componentIds ++ right.componentIds
  | _, _, .crossingPositive left right =>
      left.componentIds ++ right.componentIds
  | _, _, .crossingNegative left right =>
      left.componentIds ++ right.componentIds
  | _, _, .cupPositiveNegative componentId =>
      [componentId]
  | _, _, .cupNegativePositive componentId =>
      [componentId]
  | _, _, .capNegativePositive componentId =>
      [componentId]
  | _, _, .capPositiveNegative componentId =>
      [componentId]
  | _, _, .identityCoupon _ boundary =>
      boundary.componentIds
  | _, _, .twistPositive component =>
      [component.componentId]
  | _, _, .twistNegative component =>
      [component.componentId]
  | _, _, .associatorHom left middle right =>
      left.componentIds ++ middle.componentIds ++ right.componentIds
  | _, _, .associatorInv left middle right =>
      left.componentIds ++ middle.componentIds ++ right.componentIds
  | _, _, .leftUnitorHom boundary =>
      boundary.componentIds
  | _, _, .leftUnitorInv boundary =>
      boundary.componentIds
  | _, _, .rightUnitorHom boundary =>
      boundary.componentIds
  | _, _, .rightUnitorInv boundary =>
      boundary.componentIds

/-- Every source-boundary ID is inspected by the whole free diagram. -/
theorem source_componentIds_subset
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target) :
    ∀ {componentId : String},
      componentId ∈ source.componentIds →
        componentId ∈ diagram.componentIds := by
  induction diagram <;>
    simp_all [componentIds, ComponentBoundary.componentIds,
      positiveAtom, negativeAtom] <;>
    aesop

/-- Every target-boundary ID is inspected by the whole free diagram. -/
theorem target_componentIds_subset
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target) :
    ∀ {componentId : String},
      componentId ∈ target.componentIds →
        componentId ∈ diagram.componentIds := by
  induction diagram <;>
    simp_all [componentIds, ComponentBoundary.componentIds,
      positiveAtom, negativeAtom] <;>
    aesop

/-- Interpret every free constructor using only the selected ribbon data. -/
def interpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S) :
    {source target : ComponentBoundary} →
      ComponentDiagram source target →
      Diagram C
        (source.interpret 𝒞 labelOf)
        (target.interpret 𝒞 labelOf)
  | _, _, .identity boundary =>
      Diagram.identity (boundary.interpret 𝒞 labelOf)
  | _, _, .comp first second =>
      first.interpret 𝒞 labelOf ≫ᵈ
        second.interpret 𝒞 labelOf
  | _, _, .tensor left right =>
      left.interpret 𝒞 labelOf ⊗ᵈ
        right.interpret 𝒞 labelOf
  | _, _, .crossingPositive left right =>
      Diagram.crossing
        (left.interpret 𝒞 labelOf)
        (right.interpret 𝒞 labelOf)
  | _, _, .crossingNegative left right =>
      Diagram.crossingInv
        (left.interpret 𝒞 labelOf)
        (right.interpret 𝒞 labelOf)
  | _, _, .cupPositiveNegative componentId =>
      let X := 𝒞.simple (labelOf componentId)
      Diagram.exactCup X Xᘁ inferInstance
  | _, _, .cupNegativePositive componentId =>
      let X := 𝒞.simple (labelOf componentId)
      Diagram.exactCup Xᘁ X
        (pivotalReverseExactPairing 𝒞.pivotal X)
  | _, _, .capNegativePositive componentId =>
      let X := 𝒞.simple (labelOf componentId)
      Diagram.exactCap X Xᘁ inferInstance
  | _, _, .capPositiveNegative componentId =>
      let X := 𝒞.simple (labelOf componentId)
      Diagram.exactCap Xᘁ X
        (pivotalReverseExactPairing 𝒞.pivotal X)
  | _, _, .identityCoupon couponId boundary =>
      Diagram.coupon
        (couponId ++ ":identity")
        (𝟙 (boundary.interpret 𝒞 labelOf).denote)
  | _, _, .twistPositive component =>
      Diagram.coupon "positive-framing-twist"
        ((NaturalTwist.ofRibbon 𝒞.ribbon).iso.hom.app
          (component.interpret 𝒞 labelOf))
  | _, _, .twistNegative component =>
      Diagram.coupon "negative-framing-twist"
        ((NaturalTwist.ofRibbon 𝒞.ribbon).iso.inv.app
          (component.interpret 𝒞 labelOf))
  | _, _, .associatorHom left middle right =>
      Diagram.coupon "component-associator-hom"
        (α_
          (left.interpret 𝒞 labelOf).denote
          (middle.interpret 𝒞 labelOf).denote
          (right.interpret 𝒞 labelOf).denote).hom
  | _, _, .associatorInv left middle right =>
      Diagram.coupon "component-associator-inv"
        (α_
          (left.interpret 𝒞 labelOf).denote
          (middle.interpret 𝒞 labelOf).denote
          (right.interpret 𝒞 labelOf).denote).inv
  | _, _, .leftUnitorHom boundary =>
      Diagram.coupon "component-left-unitor-hom"
        (λ_ (boundary.interpret 𝒞 labelOf).denote).hom
  | _, _, .leftUnitorInv boundary =>
      Diagram.coupon "component-left-unitor-inv"
        (λ_ (boundary.interpret 𝒞 labelOf).denote).inv
  | _, _, .rightUnitorHom boundary =>
      Diagram.coupon "component-right-unitor-hom"
        (ρ_ (boundary.interpret 𝒞 labelOf).denote).hom
  | _, _, .rightUnitorInv boundary =>
      Diagram.coupon "component-right-unitor-inv"
        (ρ_ (boundary.interpret 𝒞 labelOf).denote).inv

/-- Interpreting a free disjoint union is the corresponding closed tensor. -/
theorem interpret_closedTensor
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    (left right : ComponentDiagram .unit .unit) :
    Diagram.eval C ((closedTensor left right).interpret 𝒞 labelOf) =
      (λ_ (𝟙_ C)).inv ≫
        (Diagram.eval C (left.interpret 𝒞 labelOf) ⊗ₘ
          Diagram.eval C (right.interpret 𝒞 labelOf)) ≫
        (λ_ (𝟙_ C)).hom := by
  rfl

/--
The canonical zero-framed unknot evaluates to the pivotal dimension of its
selected simple object.

This is a definitional calculation from the exact right-dual cup and the
reverse exact pairing induced by the ribbon pivotal structure.  It is not a
separate graphical axiom.
-/
theorem zeroFramedUnknot_eval
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    (componentId : String) :
    Diagram.eval C
        ((zeroFramedUnknot componentId).interpret 𝒞 labelOf) =
      𝒞.categoricalDimension (labelOf componentId) := by
  simp only [zeroFramedUnknot, interpret, Diagram.eval,
    RibbonFusionCategoryData.categoricalDimension, pivotalDimension,
    leftCategoricalTrace, pivotalReverseExactPairing,
    CategoryTheory.ExactPairing.coevaluation,
    CategoryTheory.ExactPairing.evaluation,
    CategoryTheory.exactPairingCongrRight]
  monoidal

/-- Scalar form of `zeroFramedUnknot_eval`. -/
theorem zeroFramedUnknot_closedScalar
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    (componentId : String) :
    𝒞.toFusionCategoryData.closedScalar
        (Diagram.eval C
          ((zeroFramedUnknot componentId).interpret 𝒞 labelOf)) =
      𝒞.quantumDimension (labelOf componentId) := by
  simpa only [RibbonFusionCategoryData.quantumDimension] using
    congrArg 𝒞.toFusionCategoryData.closedScalar
      (zeroFramedUnknot_eval 𝒞 labelOf componentId)

/-!
The sigma-packaged proof experiment below is retained temporarily while the
kernel-checked heterogeneous-congruence implementation is established.

/--
Package both interpreted endpoints together with the interpreted diagram.

This sigma type makes label-dependent boundary changes explicit and gives
ordinary equality a fixed ambient type.
-/
def packedInterpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {source target : ComponentBoundary}
    (labelOf : String → S)
    (diagram : ComponentDiagram source target) :
    Σ interpretedSource : Boundary C,
      Σ interpretedTarget : Boundary C,
        Diagram C interpretedSource interpretedTarget :=
  ⟨source.interpret 𝒞 labelOf,
    target.interpret 𝒞 labelOf,
    diagram.interpret 𝒞 labelOf⟩

/--
The complete packed interpretation depends only on the labels of component
IDs actually occurring in the free diagram.
-/
theorem packedInterpret_eq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    packedInterpret 𝒞 leftLabels diagram =
      packedInterpret 𝒞 rightLabels diagram := by
  induction diagram with
  | identity boundary =>
      have boundaryEq :=
        boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
      simp only [packedInterpret, interpret]
      rw [boundaryEq]
  | comp first second firstIH secondIH =>
      simp only [componentIds, List.mem_append] at agree
      have firstEq := firstIH (fun componentId membership =>
        agree componentId (Or.inl membership))
      have secondEq := secondIH (fun componentId membership =>
        agree componentId (Or.inr membership))
      simp only [packedInterpret, interpret] at firstEq secondEq ⊢
      cases firstEq
      cases secondEq
      rfl
  | tensor left right leftIH rightIH =>
      simp only [componentIds, List.mem_append] at agree
      have leftEq := leftIH (fun componentId membership =>
        agree componentId (Or.inl membership))
      have rightEq := rightIH (fun componentId membership =>
        agree componentId (Or.inr membership))
      simp only [packedInterpret, interpret] at leftEq rightEq ⊢
      cases leftEq
      cases rightEq
      rfl
  | crossingPositive left right =>
      have leftBoundary :=
        left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl membership))
      have rightBoundary :=
        right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership))
      simp only [packedInterpret, interpret]
      rw [leftBoundary, rightBoundary]
  | crossingNegative left right =>
      have leftBoundary :=
        left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl membership))
      have rightBoundary :=
        right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership))
      simp only [packedInterpret, interpret]
      rw [leftBoundary, rightBoundary]
  | cupPositiveNegative componentId =>
      have labelEq :=
        agree componentId (by simp [componentIds])
      simp only [packedInterpret, interpret]
      rw [labelEq]
  | cupNegativePositive componentId =>
      have labelEq :=
        agree componentId (by simp [componentIds])
      simp only [packedInterpret, interpret]
      rw [labelEq]
  | capNegativePositive componentId =>
      have labelEq :=
        agree componentId (by simp [componentIds])
      simp only [packedInterpret, interpret]
      rw [labelEq]
  | capPositiveNegative componentId =>
      have labelEq :=
        agree componentId (by simp [componentIds])
      simp only [packedInterpret, interpret]
      rw [labelEq]
  | identityCoupon couponId boundary =>
      have boundaryEq :=
        boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
      simp only [packedInterpret, interpret]
      rw [boundaryEq]
  | twistPositive component =>
      have labelEq :=
        agree component.componentId (by simp [componentIds])
      cases component with
      | mk componentId orientation =>
          cases orientation <;>
            simp only [packedInterpret, interpret,
              ComponentBoundary.interpret, ComponentAtom.interpret] <;>
            rw [labelEq]
  | twistNegative component =>
      have labelEq :=
        agree component.componentId (by simp [componentIds])
      cases component with
      | mk componentId orientation =>
          cases orientation <;>
            simp only [packedInterpret, interpret,
              ComponentBoundary.interpret, ComponentAtom.interpret] <;>
            rw [labelEq]
  | associatorHom left middle right =>
      have leftBoundary :=
        left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inl membership)))
      have middleBoundary :=
        middle.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inr membership)))
      have rightBoundary :=
        right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership))
      simp only [packedInterpret, interpret]
      rw [leftBoundary, middleBoundary, rightBoundary]
  | associatorInv left middle right =>
      have leftBoundary :=
        left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inl membership)))
      have middleBoundary :=
        middle.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inr membership)))
      have rightBoundary :=
        right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership))
      simp only [packedInterpret, interpret]
      rw [leftBoundary, middleBoundary, rightBoundary]
  | leftUnitorHom boundary =>
      have boundaryEq :=
        boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
      simp only [packedInterpret, interpret]
      rw [boundaryEq]
  | leftUnitorInv boundary =>
      have boundaryEq :=
        boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
      simp only [packedInterpret, interpret]
      rw [boundaryEq]
  | rightUnitorHom boundary =>
      have boundaryEq :=
        boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
      simp only [packedInterpret, interpret]
      rw [boundaryEq]
  | rightUnitorInv boundary =>
      have boundaryEq :=
        boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
      simp only [packedInterpret, interpret]
      rw [boundaryEq]

/--
Interpreting a free diagram depends only on the labels of IDs that actually
occur in it.

`HEq` is essential here: for an open diagram, changing a label changes the
Lean type of its interpreted boundary.  The equality of packed
interpretations above proves both the dependent boundary-type equality and
the diagram-value equality.
-/
theorem interpret_heq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    HEq (diagram.interpret 𝒞 leftLabels)
      (diagram.interpret 𝒞 rightLabels) := by
  have packedEq :=
    packedInterpret_eq_of_eq_on_componentIds
      𝒞 leftLabels rightLabels diagram agree
  have projected :
      HEq
        (packedInterpret 𝒞 leftLabels diagram).2.2
        (packedInterpret 𝒞 rightLabels diagram).2.2 := by
    cases packedEq
    rfl
  exact projected

-/

private theorem identity_heq
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq (Diagram.identity left) (Diagram.identity right) := by
  subst right
  rfl

private theorem comp_heq
    {a b c a' b' c' : Boundary C}
    {first : Diagram C a b}
    {first' : Diagram C a' b'}
    {second : Diagram C b c}
    {second' : Diagram C b' c'}
    (aEq : a = a')
    (bEq : b = b')
    (cEq : c = c')
    (firstEq : HEq first first')
    (secondEq : HEq second second') :
    HEq (Diagram.comp first second)
      (Diagram.comp first' second') := by
  subst a'
  subst b'
  subst c'
  exact heq_of_eq
    (congrArg₂ Diagram.comp
      (eq_of_heq firstEq) (eq_of_heq secondEq))

private theorem tensor_heq
    {a b c d a' b' c' d' : Boundary C}
    {left : Diagram C a b}
    {left' : Diagram C a' b'}
    {right : Diagram C c d}
    {right' : Diagram C c' d'}
    (aEq : a = a')
    (bEq : b = b')
    (cEq : c = c')
    (dEq : d = d')
    (leftEq : HEq left left')
    (rightEq : HEq right right') :
    HEq (Diagram.tensor left right)
      (Diagram.tensor left' right') := by
  subst a'
  subst b'
  subst c'
  subst d'
  exact heq_of_eq
    (congrArg₂ Diagram.tensor
      (eq_of_heq leftEq) (eq_of_heq rightEq))

private theorem crossing_heq
    {left right left' right' : Boundary C}
    (leftEq : left = left')
    (rightEq : right = right') :
    HEq (Diagram.crossing left right)
      (Diagram.crossing left' right') := by
  subst left'
  subst right'
  rfl

private theorem crossingInv_heq
    {left right left' right' : Boundary C}
    (leftEq : left = left')
    (rightEq : right = right') :
    HEq (Diagram.crossingInv left right)
      (Diagram.crossingInv left' right') := by
  subst left'
  subst right'
  rfl

private theorem positiveCup_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {left right : S}
    (labelEq : left = right) :
    HEq
      (Diagram.exactCup
        (𝒞.simple left) (𝒞.simple left)ᘁ inferInstance)
      (Diagram.exactCup
        (𝒞.simple right) (𝒞.simple right)ᘁ inferInstance) := by
  subst right
  rfl

private theorem negativeCup_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {left right : S}
    (labelEq : left = right) :
    HEq
      (Diagram.exactCup
        (𝒞.simple left)ᘁ (𝒞.simple left)
        (pivotalReverseExactPairing 𝒞.pivotal (𝒞.simple left)))
      (Diagram.exactCup
        (𝒞.simple right)ᘁ (𝒞.simple right)
        (pivotalReverseExactPairing 𝒞.pivotal (𝒞.simple right))) := by
  subst right
  rfl

private theorem negativePositiveCap_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {left right : S}
    (labelEq : left = right) :
    HEq
      (Diagram.exactCap
        (𝒞.simple left) (𝒞.simple left)ᘁ inferInstance)
      (Diagram.exactCap
        (𝒞.simple right) (𝒞.simple right)ᘁ inferInstance) := by
  subst right
  rfl

private theorem positiveNegativeCap_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {left right : S}
    (labelEq : left = right) :
    HEq
      (Diagram.exactCap
        (𝒞.simple left)ᘁ (𝒞.simple left)
        (pivotalReverseExactPairing 𝒞.pivotal (𝒞.simple left)))
      (Diagram.exactCap
        (𝒞.simple right)ᘁ (𝒞.simple right)
        (pivotalReverseExactPairing 𝒞.pivotal (𝒞.simple right))) := by
  subst right
  rfl

private theorem identityCoupon_heq
    (couponId : String)
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      (Diagram.coupon (couponId ++ ":identity") (𝟙 left.denote))
      (Diagram.coupon (couponId ++ ":identity") (𝟙 right.denote)) := by
  subst right
  rfl

private theorem positiveTwist_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {left right : C}
    (objectEq : left = right) :
    HEq
      ((Diagram.coupon "positive-framing-twist"
          ((NaturalTwist.ofRibbon 𝒞.ribbon).iso.hom.app left)) :
        Diagram C (.atom left) (.atom left))
      ((Diagram.coupon "positive-framing-twist"
          ((NaturalTwist.ofRibbon 𝒞.ribbon).iso.hom.app right)) :
        Diagram C (.atom right) (.atom right)) := by
  subst right
  rfl

private theorem negativeTwist_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    {left right : C}
    (objectEq : left = right) :
    HEq
      ((Diagram.coupon "negative-framing-twist"
          ((NaturalTwist.ofRibbon 𝒞.ribbon).iso.inv.app left)) :
        Diagram C (.atom left) (.atom left))
      ((Diagram.coupon "negative-framing-twist"
          ((NaturalTwist.ofRibbon 𝒞.ribbon).iso.inv.app right)) :
        Diagram C (.atom right) (.atom right)) := by
  subst right
  rfl

private theorem associatorHom_heq
    {left middle right left' middle' right' : Boundary C}
    (leftEq : left = left')
    (middleEq : middle = middle')
    (rightEq : right = right') :
    HEq
      ((Diagram.coupon "component-associator-hom"
          (α_ left.denote middle.denote right.denote).hom) :
        Diagram C
          (.tensor (.tensor left middle) right)
          (.tensor left (.tensor middle right)))
      ((Diagram.coupon "component-associator-hom"
          (α_ left'.denote middle'.denote right'.denote).hom) :
        Diagram C
          (.tensor (.tensor left' middle') right')
          (.tensor left' (.tensor middle' right'))) := by
  subst left'
  subst middle'
  subst right'
  rfl

private theorem associatorInv_heq
    {left middle right left' middle' right' : Boundary C}
    (leftEq : left = left')
    (middleEq : middle = middle')
    (rightEq : right = right') :
    HEq
      ((Diagram.coupon "component-associator-inv"
          (α_ left.denote middle.denote right.denote).inv) :
        Diagram C
          (.tensor left (.tensor middle right))
          (.tensor (.tensor left middle) right))
      ((Diagram.coupon "component-associator-inv"
          (α_ left'.denote middle'.denote right'.denote).inv) :
        Diagram C
          (.tensor left' (.tensor middle' right'))
          (.tensor (.tensor left' middle') right')) := by
  subst left'
  subst middle'
  subst right'
  rfl

private theorem leftUnitorHom_heq
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      ((Diagram.coupon "component-left-unitor-hom"
          (λ_ left.denote).hom) :
        Diagram C (.tensor .unit left) left)
      ((Diagram.coupon "component-left-unitor-hom"
          (λ_ right.denote).hom) :
        Diagram C (.tensor .unit right) right) := by
  subst right
  rfl

private theorem leftUnitorInv_heq
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      ((Diagram.coupon "component-left-unitor-inv"
          (λ_ left.denote).inv) :
        Diagram C left (.tensor .unit left))
      ((Diagram.coupon "component-left-unitor-inv"
          (λ_ right.denote).inv) :
        Diagram C right (.tensor .unit right)) := by
  subst right
  rfl

private theorem rightUnitorHom_heq
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      ((Diagram.coupon "component-right-unitor-hom"
          (ρ_ left.denote).hom) :
        Diagram C (.tensor left .unit) left)
      ((Diagram.coupon "component-right-unitor-hom"
          (ρ_ right.denote).hom) :
        Diagram C (.tensor right .unit) right) := by
  subst right
  rfl

private theorem rightUnitorInv_heq
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      ((Diagram.coupon "component-right-unitor-inv"
          (ρ_ left.denote).inv) :
        Diagram C left (.tensor left .unit))
      ((Diagram.coupon "component-right-unitor-inv"
          (ρ_ right.denote).inv) :
        Diagram C right (.tensor right .unit)) := by
  subst right
  rfl

private theorem sourceBoundary_interpret_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    source.interpret 𝒞 leftLabels =
      source.interpret 𝒞 rightLabels :=
  source.interpret_eq_of_eq_on_componentIds
    𝒞 leftLabels rightLabels
    (fun _ membership =>
      agree _ (diagram.source_componentIds_subset membership))

private theorem targetBoundary_interpret_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    target.interpret 𝒞 leftLabels =
      target.interpret 𝒞 rightLabels :=
  target.interpret_eq_of_eq_on_componentIds
    𝒞 leftLabels rightLabels
    (fun _ membership =>
      agree _ (diagram.target_componentIds_subset membership))

/--
Interpreting a free diagram depends only on the labels of IDs that actually
occur in it.

The result is heterogeneous because an open diagram's Lean type contains its
interpreted source and target objects.  Every dependent constructor is
transported with its source and target equalities; no boundary cast is
silently discarded.
-/
theorem interpret_heq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    HEq (diagram.interpret 𝒞 leftLabels)
      (diagram.interpret 𝒞 rightLabels) := by
  induction diagram with
  | identity boundary =>
      exact identity_heq
        (boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)
  | comp first second firstIH secondIH =>
      let agreeFirst :
          (componentId : String) →
          componentId ∈ first.componentIds →
            leftLabels componentId = rightLabels componentId :=
        fun componentId membership =>
          agree componentId (by
            simp only [componentIds, List.mem_append]
            exact Or.inl membership)
      let agreeSecond :
          (componentId : String) →
          componentId ∈ second.componentIds →
            leftLabels componentId = rightLabels componentId :=
        fun componentId membership =>
          agree componentId (by
            simp only [componentIds, List.mem_append]
            exact Or.inr membership)
      exact comp_heq
        (sourceBoundary_interpret_eq
          𝒞 leftLabels rightLabels first agreeFirst)
        (targetBoundary_interpret_eq
          𝒞 leftLabels rightLabels first agreeFirst)
        (targetBoundary_interpret_eq
          𝒞 leftLabels rightLabels second agreeSecond)
        (firstIH agreeFirst)
        (secondIH agreeSecond)
  | tensor left right leftIH rightIH =>
      let agreeLeft :
          (componentId : String) →
          componentId ∈ left.componentIds →
            leftLabels componentId = rightLabels componentId :=
        fun componentId membership =>
          agree componentId (by
            simp only [componentIds, List.mem_append]
            exact Or.inl membership)
      let agreeRight :
          (componentId : String) →
          componentId ∈ right.componentIds →
            leftLabels componentId = rightLabels componentId :=
        fun componentId membership =>
          agree componentId (by
            simp only [componentIds, List.mem_append]
            exact Or.inr membership)
      exact tensor_heq
        (sourceBoundary_interpret_eq
          𝒞 leftLabels rightLabels left agreeLeft)
        (targetBoundary_interpret_eq
          𝒞 leftLabels rightLabels left agreeLeft)
        (sourceBoundary_interpret_eq
          𝒞 leftLabels rightLabels right agreeRight)
        (targetBoundary_interpret_eq
          𝒞 leftLabels rightLabels right agreeRight)
        (leftIH agreeLeft)
        (rightIH agreeRight)
  | crossingPositive left right =>
      exact crossing_heq
        (left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl membership)))
        (right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership)))
  | crossingNegative left right =>
      exact crossingInv_heq
        (left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl membership)))
        (right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership)))
  | cupPositiveNegative componentId =>
      exact positiveCup_heq 𝒞
        (agree componentId (by simp [componentIds]))
  | cupNegativePositive componentId =>
      exact negativeCup_heq 𝒞
        (agree componentId (by simp [componentIds]))
  | capNegativePositive componentId =>
      exact negativePositiveCap_heq 𝒞
        (agree componentId (by simp [componentIds]))
  | capPositiveNegative componentId =>
      exact positiveNegativeCap_heq 𝒞
        (agree componentId (by simp [componentIds]))
  | identityCoupon couponId boundary =>
      exact identityCoupon_heq couponId
        (boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)
  | twistPositive component =>
      have labelEq :=
        agree component.componentId (by simp [componentIds])
      cases component with
      | mk componentId orientation =>
          cases orientation with
          | positive =>
              exact positiveTwist_heq 𝒞
                (congrArg 𝒞.simple labelEq)
          | negative =>
              exact positiveTwist_heq 𝒞
                (congrArg
                  (fun simpleLabel => (𝒞.simple simpleLabel)ᘁ)
                  labelEq)
  | twistNegative component =>
      have labelEq :=
        agree component.componentId (by simp [componentIds])
      cases component with
      | mk componentId orientation =>
          cases orientation with
          | positive =>
              exact negativeTwist_heq 𝒞
                (congrArg 𝒞.simple labelEq)
          | negative =>
              exact negativeTwist_heq 𝒞
                (congrArg
                  (fun simpleLabel => (𝒞.simple simpleLabel)ᘁ)
                  labelEq)
  | associatorHom left middle right =>
      exact associatorHom_heq
        (left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inl membership))))
        (middle.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inr membership))))
        (right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership)))
  | associatorInv left middle right =>
      exact associatorInv_heq
        (left.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inl membership))))
        (middle.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inl (Or.inr membership))))
        (right.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            agree componentId (by
              simp only [componentIds, List.mem_append]
              exact Or.inr membership)))
  | leftUnitorHom boundary =>
      exact leftUnitorHom_heq
        (boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)
  | leftUnitorInv boundary =>
      exact leftUnitorInv_heq
        (boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)
  | rightUnitorHom boundary =>
      exact rightUnitorHom_heq
        (boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)
  | rightUnitorInv boundary =>
      exact rightUnitorInv_heq
        (boundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)

/--
Closed-diagram evaluation is therefore independent of labels outside the
diagram's finite component support.
-/
theorem eval_interpret_eq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    (diagram : ComponentDiagram .unit .unit)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    Diagram.eval C (diagram.interpret 𝒞 leftLabels) =
      Diagram.eval C (diagram.interpret 𝒞 rightLabels) := by
  have diagramEq :
      diagram.interpret 𝒞 leftLabels =
        diagram.interpret 𝒞 rightLabels :=
    eq_of_heq
      (interpret_heq_of_eq_on_componentIds
        𝒞 leftLabels rightLabels diagram agree)
  exact congrArg (Diagram.eval C) diagramEq

/--
Interpret a free diagram whose endpoints are canonical strand words.

This is the sole typed transport between the free component-boundary syntax
and the older categorical `boundaryWord` syntax.  Its two transports are
proved by `ComponentBoundary.interpret_word`; no arbitrary endpoint equality
is accepted.
-/
def interpretStrandWord
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    {before after : List StrandState}
    (diagram :
      ComponentDiagram
        (ComponentBoundary.word before)
        (ComponentBoundary.word after)) :
    Diagram C
      (TwistedYetter.Kirby.CategoricalPresentationCompiler.boundaryWord
        (fun strand =>
          (ComponentBoundary.ofStrand strand).interpret 𝒞 labelOf)
        before)
      (TwistedYetter.Kirby.CategoricalPresentationCompiler.boundaryWord
        (fun strand =>
          (ComponentBoundary.ofStrand strand).interpret 𝒞 labelOf)
        after) := by
  simpa only [ComponentBoundary.interpret_word] using
    diagram.interpret 𝒞 labelOf

/--
The free syntax has a category-independent one-hole context language.

The context stores only other free diagrams; it contains no interpreted
morphism.
-/
inductive Context :
    ComponentBoundary → ComponentBoundary →
      ComponentBoundary → ComponentBoundary → Type
  | hole (source target : ComponentBoundary) :
      Context source target source target
  | compLeft
      {holeSource holeTarget wholeSource : ComponentBoundary}
      (before : ComponentDiagram wholeSource holeSource) :
      Context holeSource holeTarget wholeSource holeTarget
  | compRight
      {holeSource holeTarget wholeTarget : ComponentBoundary}
      (after : ComponentDiagram holeTarget wholeTarget) :
      Context holeSource holeTarget holeSource wholeTarget
  | tensorLeft
      {holeSource holeTarget rightSource rightTarget :
        ComponentBoundary}
      (right : ComponentDiagram rightSource rightTarget) :
      Context holeSource holeTarget
        (.tensor holeSource rightSource)
        (.tensor holeTarget rightTarget)
  | tensorRight
      {leftSource leftTarget holeSource holeTarget :
        ComponentBoundary}
      (left : ComponentDiagram leftSource leftTarget) :
      Context holeSource holeTarget
        (.tensor leftSource holeSource)
        (.tensor leftTarget holeTarget)
  | compose
      {holeSource holeTarget middleSource middleTarget wholeSource wholeTarget :
        ComponentBoundary} :
      Context holeSource holeTarget middleSource middleTarget →
      Context middleSource middleTarget wholeSource wholeTarget →
      Context holeSource holeTarget wholeSource wholeTarget

namespace Context

/--
Component IDs stored in the exterior of the unique hole.

The hole boundaries are deliberately omitted: their IDs belong to the piece
being inserted.  This lets a compiler certify that a selected dotted label is
absent from the exterior without falsely rejecting the dotted encircling
window itself.
-/
def componentIds :
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary} →
    Context holeSource holeTarget wholeSource wholeTarget → List String
  | _, _, _, _, .hole _ _ =>
      []
  | _, _, _, _, .compLeft before =>
      before.componentIds
  | _, _, _, _, .compRight after =>
      after.componentIds
  | _, _, _, _, .tensorLeft right =>
      right.componentIds
  | _, _, _, _, .tensorRight left =>
      left.componentIds
  | _, _, _, _, .compose inner outer =>
      inner.componentIds ++ outer.componentIds

/-- Every whole-source ID comes from the hole source or the stored exterior. -/
theorem wholeSource_componentIds_subset
    {holeSource holeTarget wholeSource wholeTarget : ComponentBoundary}
    (context : Context holeSource holeTarget wholeSource wholeTarget) :
    ∀ {componentId : String},
      componentId ∈ wholeSource.componentIds →
        componentId ∈ holeSource.componentIds ∨
          componentId ∈ context.componentIds := by
  induction context with
  | hole =>
      intro componentId membership
      exact Or.inl membership
  | compLeft before =>
      intro componentId membership
      exact Or.inr (before.source_componentIds_subset membership)
  | compRight after =>
      intro componentId membership
      exact Or.inl membership
  | tensorLeft right =>
      intro componentId membership
      simp only [ComponentBoundary.componentIds, List.mem_append] at membership
      cases membership with
      | inl inHole => exact Or.inl inHole
      | inr inRight =>
          exact Or.inr (right.source_componentIds_subset inRight)
  | tensorRight left =>
      intro componentId membership
      simp only [ComponentBoundary.componentIds, List.mem_append] at membership
      cases membership with
      | inl inLeft =>
          exact Or.inr (left.source_componentIds_subset inLeft)
      | inr inHole => exact Or.inl inHole
  | compose inner outer innerIH outerIH =>
      intro componentId membership
      cases outerIH membership with
      | inl inMiddle =>
          cases innerIH inMiddle with
          | inl inHole => exact Or.inl inHole
          | inr inInner =>
              exact Or.inr (by
                simp only [componentIds, List.mem_append]
                exact Or.inl inInner)
      | inr inOuter =>
          exact Or.inr (by
            simp only [componentIds, List.mem_append]
            exact Or.inr inOuter)

/-- Every whole-target ID comes from the hole target or the stored exterior. -/
theorem wholeTarget_componentIds_subset
    {holeSource holeTarget wholeSource wholeTarget : ComponentBoundary}
    (context : Context holeSource holeTarget wholeSource wholeTarget) :
    ∀ {componentId : String},
      componentId ∈ wholeTarget.componentIds →
        componentId ∈ holeTarget.componentIds ∨
          componentId ∈ context.componentIds := by
  induction context with
  | hole =>
      intro componentId membership
      exact Or.inl membership
  | compLeft before =>
      intro componentId membership
      exact Or.inl membership
  | compRight after =>
      intro componentId membership
      exact Or.inr (after.target_componentIds_subset membership)
  | tensorLeft right =>
      intro componentId membership
      simp only [ComponentBoundary.componentIds, List.mem_append] at membership
      cases membership with
      | inl inHole => exact Or.inl inHole
      | inr inRight =>
          exact Or.inr (right.target_componentIds_subset inRight)
  | tensorRight left =>
      intro componentId membership
      simp only [ComponentBoundary.componentIds, List.mem_append] at membership
      cases membership with
      | inl inLeft =>
          exact Or.inr (left.target_componentIds_subset inLeft)
      | inr inHole => exact Or.inl inHole
  | compose inner outer innerIH outerIH =>
      intro componentId membership
      cases outerIH membership with
      | inl inMiddle =>
          cases innerIH inMiddle with
          | inl inHole => exact Or.inl inHole
          | inr inInner =>
              exact Or.inr (by
                simp only [componentIds, List.mem_append]
                exact Or.inl inInner)
      | inr inOuter =>
          exact Or.inr (by
            simp only [componentIds, List.mem_append]
            exact Or.inr inOuter)

/-- Fill the unique free hole. -/
def plug
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary} :
    Context holeSource holeTarget wholeSource wholeTarget →
    ComponentDiagram holeSource holeTarget →
      ComponentDiagram wholeSource wholeTarget
  | .hole _ _, piece =>
      piece
  | .compLeft before, piece =>
      before ≫ᶜ piece
  | .compRight after, piece =>
      piece ≫ᶜ after
  | .tensorLeft right, piece =>
      piece ⊗ᶜ right
  | .tensorRight left, piece =>
      left ⊗ᶜ piece
  | .compose inner outer, piece =>
      outer.plug (inner.plug piece)

/-- Deterministically interpret a free context as a categorical context. -/
def interpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S) :
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary} →
    Context holeSource holeTarget wholeSource wholeTarget →
      CategoricalTangle.Context C
        (holeSource.interpret 𝒞 labelOf)
        (holeTarget.interpret 𝒞 labelOf)
        (wholeSource.interpret 𝒞 labelOf)
        (wholeTarget.interpret 𝒞 labelOf)
  | _, _, _, _, .hole source target =>
      .hole
        (source.interpret 𝒞 labelOf)
        (target.interpret 𝒞 labelOf)
  | _, _, _, _, .compLeft before =>
      .compLeft (before.interpret 𝒞 labelOf)
  | _, _, _, _, .compRight after =>
      .compRight (after.interpret 𝒞 labelOf)
  | _, _, _, _, .tensorLeft right =>
      .tensorLeft (right.interpret 𝒞 labelOf)
  | _, _, _, _, .tensorRight left =>
      .tensorRight (left.interpret 𝒞 labelOf)
  | _, _, _, _, .compose inner outer =>
      .compose
        (inner.interpret 𝒞 labelOf)
        (outer.interpret 𝒞 labelOf)

private theorem categoricalHole_heq
    {holeSource holeTarget holeSource' holeTarget' : Boundary C}
    (sourceEq : holeSource = holeSource')
    (targetEq : holeTarget = holeTarget') :
    HEq
      (CategoricalTangle.Context.hole holeSource holeTarget)
      (CategoricalTangle.Context.hole holeSource' holeTarget') := by
  subst holeSource'
  subst holeTarget'
  rfl

private theorem categoricalCompLeft_heq
    {holeSource holeTarget wholeSource
      holeSource' holeTarget' wholeSource' : Boundary C}
    {before : Diagram C wholeSource holeSource}
    {before' : Diagram C wholeSource' holeSource'}
    (holeSourceEq : holeSource = holeSource')
    (holeTargetEq : holeTarget = holeTarget')
    (wholeSourceEq : wholeSource = wholeSource')
    (beforeEq : HEq before before') :
    HEq
      (CategoricalTangle.Context.compLeft
        (holeTarget := holeTarget) before)
      (CategoricalTangle.Context.compLeft
        (holeTarget := holeTarget') before') := by
  subst holeSource'
  subst holeTarget'
  subst wholeSource'
  cases beforeEq
  rfl

private theorem categoricalCompRight_heq
    {holeSource holeTarget wholeTarget
      holeSource' holeTarget' wholeTarget' : Boundary C}
    {after : Diagram C holeTarget wholeTarget}
    {after' : Diagram C holeTarget' wholeTarget'}
    (holeSourceEq : holeSource = holeSource')
    (holeTargetEq : holeTarget = holeTarget')
    (wholeTargetEq : wholeTarget = wholeTarget')
    (afterEq : HEq after after') :
    HEq
      (CategoricalTangle.Context.compRight
        (holeSource := holeSource) after)
      (CategoricalTangle.Context.compRight
        (holeSource := holeSource') after') := by
  subst holeSource'
  subst holeTarget'
  subst wholeTarget'
  cases afterEq
  rfl

private theorem categoricalTensorLeft_heq
    {holeSource holeTarget rightSource rightTarget
      holeSource' holeTarget' rightSource' rightTarget' : Boundary C}
    {right : Diagram C rightSource rightTarget}
    {right' : Diagram C rightSource' rightTarget'}
    (holeSourceEq : holeSource = holeSource')
    (holeTargetEq : holeTarget = holeTarget')
    (rightSourceEq : rightSource = rightSource')
    (rightTargetEq : rightTarget = rightTarget')
    (rightEq : HEq right right') :
    HEq
      (CategoricalTangle.Context.tensorLeft
        (holeSource := holeSource) (holeTarget := holeTarget) right)
      (CategoricalTangle.Context.tensorLeft
        (holeSource := holeSource') (holeTarget := holeTarget') right') := by
  subst holeSource'
  subst holeTarget'
  subst rightSource'
  subst rightTarget'
  cases rightEq
  rfl

private theorem categoricalTensorRight_heq
    {leftSource leftTarget holeSource holeTarget
      leftSource' leftTarget' holeSource' holeTarget' : Boundary C}
    {left : Diagram C leftSource leftTarget}
    {left' : Diagram C leftSource' leftTarget'}
    (leftSourceEq : leftSource = leftSource')
    (leftTargetEq : leftTarget = leftTarget')
    (holeSourceEq : holeSource = holeSource')
    (holeTargetEq : holeTarget = holeTarget')
    (leftEq : HEq left left') :
    HEq
      (CategoricalTangle.Context.tensorRight
        (holeSource := holeSource) (holeTarget := holeTarget) left)
      (CategoricalTangle.Context.tensorRight
        (holeSource := holeSource') (holeTarget := holeTarget') left') := by
  subst leftSource'
  subst leftTarget'
  subst holeSource'
  subst holeTarget'
  cases leftEq
  rfl

private theorem categoricalCompose_heq
    {holeSource holeTarget middleSource middleTarget wholeSource wholeTarget
      holeSource' holeTarget' middleSource' middleTarget' wholeSource' wholeTarget' :
      Boundary C}
    {inner : CategoricalTangle.Context C
      holeSource holeTarget middleSource middleTarget}
    {inner' : CategoricalTangle.Context C
      holeSource' holeTarget' middleSource' middleTarget'}
    {outer : CategoricalTangle.Context C
      middleSource middleTarget wholeSource wholeTarget}
    {outer' : CategoricalTangle.Context C
      middleSource' middleTarget' wholeSource' wholeTarget'}
    (holeSourceEq : holeSource = holeSource')
    (holeTargetEq : holeTarget = holeTarget')
    (middleSourceEq : middleSource = middleSource')
    (middleTargetEq : middleTarget = middleTarget')
    (wholeSourceEq : wholeSource = wholeSource')
    (wholeTargetEq : wholeTarget = wholeTarget')
    (innerEq : HEq inner inner')
    (outerEq : HEq outer outer') :
    HEq
      (CategoricalTangle.Context.compose inner outer)
      (CategoricalTangle.Context.compose inner' outer') := by
  subst holeSource'
  subst holeTarget'
  subst middleSource'
  subst middleTarget'
  subst wholeSource'
  subst wholeTarget'
  cases innerEq
  cases outerEq
  rfl

/--
Interpreting a free one-hole context depends only on labels at the hole
boundaries and component IDs stored in the exterior.  The result is
heterogeneous because changing a label can change all four boundary types.
-/
theorem interpret_heq_of_eq_on_hole_and_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {holeSource holeTarget wholeSource wholeTarget : ComponentBoundary}
    (context : Context holeSource holeTarget wholeSource wholeTarget)
    (holeSourceAgree :
      (componentId : String) → componentId ∈ holeSource.componentIds →
        leftLabels componentId = rightLabels componentId)
    (holeTargetAgree :
      (componentId : String) → componentId ∈ holeTarget.componentIds →
        leftLabels componentId = rightLabels componentId)
    (exteriorAgree :
      (componentId : String) → componentId ∈ context.componentIds →
        leftLabels componentId = rightLabels componentId) :
    HEq (context.interpret 𝒞 leftLabels)
      (context.interpret 𝒞 rightLabels) := by
  induction context generalizing leftLabels rightLabels with
  | @hole source target =>
      exact categoricalHole_heq
        (source.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeSourceAgree)
        (target.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeTargetAgree)
  | @compLeft holeSource holeTarget wholeSource before =>
      have beforeEq :=
        before.interpret_heq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels exteriorAgree
      exact categoricalCompLeft_heq
        (holeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeSourceAgree)
        (holeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeTargetAgree)
        (wholeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            exteriorAgree componentId
              (before.source_componentIds_subset membership)))
        beforeEq
  | @compRight holeSource holeTarget wholeTarget after =>
      have afterEq :=
        after.interpret_heq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels exteriorAgree
      exact categoricalCompRight_heq
        (holeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeSourceAgree)
        (holeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeTargetAgree)
        (wholeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            exteriorAgree componentId
              (after.target_componentIds_subset membership)))
        afterEq
  | @tensorLeft holeSource holeTarget rightSource rightTarget right =>
      have rightEq :=
        right.interpret_heq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels exteriorAgree
      exact categoricalTensorLeft_heq
        (holeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeSourceAgree)
        (holeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeTargetAgree)
        (rightSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            exteriorAgree componentId
              (right.source_componentIds_subset membership)))
        (rightTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            exteriorAgree componentId
              (right.target_componentIds_subset membership)))
        rightEq
  | @tensorRight leftSource leftTarget holeSource holeTarget left =>
      have leftEq :=
        left.interpret_heq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels exteriorAgree
      exact categoricalTensorRight_heq
        (leftSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            exteriorAgree componentId
              (left.source_componentIds_subset membership)))
        (leftTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            exteriorAgree componentId
              (left.target_componentIds_subset membership)))
        (holeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeSourceAgree)
        (holeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeTargetAgree)
        leftEq
  | @compose holeSource holeTarget middleSource middleTarget
      wholeSource wholeTarget inner outer innerIH outerIH =>
      let agreeInner := fun componentId membership =>
        exteriorAgree componentId (by
          simp only [componentIds, List.mem_append]
          exact Or.inl membership)
      let agreeOuter := fun componentId membership =>
        exteriorAgree componentId (by
          simp only [componentIds, List.mem_append]
          exact Or.inr membership)
      let middleSourceAgree := fun componentId membership =>
        match wholeSource_componentIds_subset inner membership with
        | Or.inl inHole => holeSourceAgree componentId inHole
        | Or.inr inInner => agreeInner componentId inInner
      let middleTargetAgree := fun componentId membership =>
        match wholeTarget_componentIds_subset inner membership with
        | Or.inl inHole => holeTargetAgree componentId inHole
        | Or.inr inInner => agreeInner componentId inInner
      have innerEq := innerIH leftLabels rightLabels
        holeSourceAgree holeTargetAgree agreeInner
      have outerEq := outerIH leftLabels rightLabels
        middleSourceAgree middleTargetAgree agreeOuter
      exact categoricalCompose_heq
        (holeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeSourceAgree)
        (holeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels holeTargetAgree)
        (middleSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels middleSourceAgree)
        (middleTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels middleTargetAgree)
        (wholeSource.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            match wholeSource_componentIds_subset
              (Context.compose inner outer) membership with
            | Or.inl inHole => holeSourceAgree componentId inHole
            | Or.inr inExterior => exteriorAgree componentId inExterior))
        (wholeTarget.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels
          (fun componentId membership =>
            match wholeTarget_componentIds_subset
              (Context.compose inner outer) membership with
            | Or.inl inHole => holeTargetAgree componentId inHole
            | Or.inr inExterior => exteriorAgree componentId inExterior))
        innerEq outerEq

/-- Expose one list concatenation using only free associators and unitors. -/
def splitBoundaryWord :
    (left right : List StrandState) →
      ComponentDiagram
        (ComponentBoundary.word (left ++ right))
        (.tensor
          (ComponentBoundary.word left)
          (ComponentBoundary.word right))
  | [], right =>
      .leftUnitorInv (ComponentBoundary.word right)
  | [strand], [] =>
      .rightUnitorInv (.atom (ComponentBoundary.ofStrand strand))
  | [_strand], _ :: _ =>
      .identity _
  | strand :: next :: rest, right =>
      (.identity (.atom (ComponentBoundary.ofStrand strand)) ⊗ᶜ
          splitBoundaryWord (next :: rest) right) ≫ᶜ
        .associatorInv
          (.atom (ComponentBoundary.ofStrand strand))
          (ComponentBoundary.word (next :: rest))
          (ComponentBoundary.word right)

/-- Reassemble one exposed list concatenation. -/
def joinBoundaryWord :
    (left right : List StrandState) →
      ComponentDiagram
        (.tensor
          (ComponentBoundary.word left)
          (ComponentBoundary.word right))
        (ComponentBoundary.word (left ++ right))
  | [], right =>
      .leftUnitorHom (ComponentBoundary.word right)
  | [strand], [] =>
      .rightUnitorHom (.atom (ComponentBoundary.ofStrand strand))
  | [_strand], _ :: _ =>
      .identity _
  | strand :: next :: rest, right =>
      .associatorHom
          (.atom (ComponentBoundary.ofStrand strand))
          (ComponentBoundary.word (next :: rest))
          (ComponentBoundary.word right) ≫ᶜ
        (.identity (.atom (ComponentBoundary.ofStrand strand)) ⊗ᶜ
          joinBoundaryWord (next :: rest) right)

/--
Place one local component diagram inside exact prefix and suffix tensor words.
-/
def surroundBoundaryWord
    (leading localSource localTarget suffix : List StrandState) :
    Context
      (ComponentBoundary.word localSource)
      (ComponentBoundary.word localTarget)
      (ComponentBoundary.word (leading ++ (localSource ++ suffix)))
      (ComponentBoundary.word (leading ++ (localTarget ++ suffix))) := by
  let suffixContext :
      Context
        (ComponentBoundary.word localSource)
        (ComponentBoundary.word localTarget)
        (ComponentBoundary.word (localSource ++ suffix))
        (ComponentBoundary.word (localTarget ++ suffix)) :=
    .compose
      (.compose
        (.tensorLeft
          (.identity (ComponentBoundary.word suffix)))
        (.compLeft
          (splitBoundaryWord localSource suffix)))
      (.compRight
        (joinBoundaryWord localTarget suffix))
  exact
    .compose
      (.compose
        suffixContext
        (.tensorRight
          (.identity (ComponentBoundary.word leading))))
      (.compose
        (.compLeft
          (splitBoundaryWord leading (localSource ++ suffix)))
        (.compRight
          (joinBoundaryWord leading (localTarget ++ suffix))))

/-- Interpretation commutes definitionally with filling the free hole. -/
theorem interpret_plug
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary}
    (context :
      Context holeSource holeTarget wholeSource wholeTarget)
    (piece : ComponentDiagram holeSource holeTarget) :
    (context.plug piece).interpret 𝒞 labelOf =
      CategoricalTangle.Context.plug C
        (context.interpret 𝒞 labelOf)
        (piece.interpret 𝒞 labelOf) := by
  induction context with
  | hole =>
      rfl
  | compLeft =>
      rfl
  | compRight =>
      rfl
  | tensorLeft =>
      rfl
  | tensorRight =>
      rfl
  | compose inner outer innerIH outerIH =>
      change
        (outer.plug (inner.plug piece)).interpret 𝒞 labelOf =
          CategoricalTangle.Context.plug C
            (outer.interpret 𝒞 labelOf)
            (CategoricalTangle.Context.plug C
              (inner.interpret 𝒞 labelOf)
              (piece.interpret 𝒞 labelOf))
      rw [outerIH (inner.plug piece), innerIH piece]

end Context

end ComponentDiagram

namespace EventWindow

/-- The free local primitive selected by one exact canonical event window. -/
def componentPrimitive :
    {event : SliceEvent} →
    {before after : List StrandState} →
      EventWindow event before after →
      ComponentDiagram
        (ComponentBoundary.word before)
        (ComponentBoundary.word after)
  | _, _, _, .birth eventId componentId positiveId negativeId
      leading suffix =>
      (ComponentDiagram.Context.surroundBoundaryWord
        leading []
        [
          positiveStrand positiveId componentId,
          negativeStrand negativeId componentId
        ]
        suffix).plug
          (.cupPositiveNegative componentId)
  | _, _, _, .deathPositiveNegative eventId componentId firstId secondId
      positiveId negativeId listedIds leading suffix =>
      (ComponentDiagram.Context.surroundBoundaryWord
        leading
        [
          positiveStrand positiveId componentId,
          negativeStrand negativeId componentId
        ]
        [] suffix).plug
          (.capPositiveNegative componentId)
  | _, _, _, .deathNegativePositive eventId componentId firstId secondId
      negativeId positiveId listedIds leading suffix =>
      (ComponentDiagram.Context.surroundBoundaryWord
        leading
        [
          negativeStrand negativeId componentId,
          positiveStrand positiveId componentId
        ]
        [] suffix).plug
          (.capNegativePositive componentId)
  | _, _, _, .crossing eventId overId underId sign
      overComponent underComponent overOrientation underOrientation
      leading suffix => by
      let over : StrandState := {
        strandId := overId
        componentId := overComponent
        orientation := overOrientation
      }
      let under : StrandState := {
        strandId := underId
        componentId := underComponent
        orientation := underOrientation
      }
      let localDiagram :=
        match sign with
        | .positive =>
            ComponentDiagram.crossingPositive
              (.atom (ComponentBoundary.ofStrand over))
              (.atom (ComponentBoundary.ofStrand under))
        | .negative =>
            ComponentDiagram.crossingNegative
              (.atom (ComponentBoundary.ofStrand over))
              (.atom (ComponentBoundary.ofStrand under))
      exact
        (ComponentDiagram.Context.surroundBoundaryWord
          leading [over, under] [under, over] suffix).plug localDiagram
  | _, _, _, .identityCoupon eventId couponId localWindow
      leading suffix =>
      (ComponentDiagram.Context.surroundBoundaryWord
        leading localWindow localWindow suffix).plug
          (.identityCoupon couponId
            (ComponentBoundary.word localWindow))
  | _, _, _, .framingTwist eventId strandId sign strand strandIdSound
      leading suffix => by
      let localDiagram :=
        match sign with
        | .positive =>
            ComponentDiagram.twistPositive
              (ComponentBoundary.ofStrand strand)
        | .negative =>
            ComponentDiagram.twistNegative
              (ComponentBoundary.ofStrand strand)
      exact
        (ComponentDiagram.Context.surroundBoundaryWord
          leading [strand] [strand] suffix).plug localDiagram
  | _, _, _, .planarIdentity eventId state =>
      .identity (ComponentBoundary.word state)

end EventWindow

namespace Trace

/-- Compose free component primitives along one exact canonical trace. -/
def componentDiagram
    {raw : RawPresentation}
    {events : List SliceEvent}
    {before final : List StrandState} :
    Trace raw events before final →
      ComponentDiagram
        (ComponentBoundary.word before)
        (ComponentBoundary.word final)
  | .nil state =>
      .identity (ComponentBoundary.word state)
  | .cons window _ tail =>
      EventWindow.componentPrimitive window ≫ᶜ componentDiagram tail

/--
Changing only the event-list index of a typed trace does not change the free
diagram it compiles.  The proof eliminates the index equality before any
diagram reasoning.
-/
theorem componentDiagram_transport_events
    {raw : RawPresentation}
    {events replacement : List SliceEvent}
    {before final : List StrandState}
    (eventLists : events = replacement)
    (trace : Trace raw events before final) :
    componentDiagram (eventLists ▸ trace) =
      componentDiagram trace := by
  cases eventLists
  rfl

end Trace

end TwistedYetter.Kirby.ComponentRibbonDiagram
