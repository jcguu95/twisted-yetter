import TwistedYetter.Kirby.ComponentDottedEncircling
import TwistedYetter.Kirby.ComponentRibbonIsotopy
import TwistedYetter.Kirby.PremodularDottedCutting

/-!
# Component-role-aware free ribbon diagrams

`ComponentDiagram` treats every component as an ordinary labelled ribbon.
That is correct for ordinary two-handles but not for a special dotted
one-handle in a premodular category.  This file adds one free primitive,
`specialDottedCut`, without changing the existing diagram syntax.

The primitive contains only a dotted component ID and a category-neutral
puncture boundary.  Its categorical interpretation is the normalized
tensor-unit projector.  Erasing the role distinction restores the ordinary
open dotted encircling used for modular calibration.
-/

namespace TwistedYetter.Kirby.RoleAwareComponentDiagram

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.ModularVacuumProjector
open TwistedYetter.Kirby.PremodularDottedCutting

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Free diagrams with one additional role-aware dotted-cut primitive. -/
inductive RoleAwareDiagram :
    ComponentBoundary → ComponentBoundary → Type
  | ordinary
      {source target : ComponentBoundary}
      (diagram : ComponentDiagram source target) :
      RoleAwareDiagram source target
  | specialDottedCut
      (dottedId : String)
      (punctureBoundary : ComponentBoundary) :
      RoleAwareDiagram punctureBoundary punctureBoundary
  | characterPower
      (boundary : ComponentBoundary)
      (exponent : ℤ) :
      RoleAwareDiagram boundary boundary
  | comp
      {source middle target : ComponentBoundary} :
      RoleAwareDiagram source middle →
      RoleAwareDiagram middle target →
      RoleAwareDiagram source target
  | tensor
      {leftSource leftTarget rightSource rightTarget :
        ComponentBoundary} :
      RoleAwareDiagram leftSource leftTarget →
      RoleAwareDiagram rightSource rightTarget →
      RoleAwareDiagram
        (.tensor leftSource rightSource)
        (.tensor leftTarget rightTarget)

namespace RoleAwareDiagram

/-- Disjoint union of two closed role-aware diagrams. -/
def closedTensor
    (left right : RoleAwareDiagram .unit .unit) :
    RoleAwareDiagram .unit .unit :=
  .comp
    (.ordinary (.leftUnitorInv .unit))
    (.comp
      (.tensor left right)
      (.ordinary (.leftUnitorHom .unit)))

/--
The role-aware local diagram of a cancelling 1--2 pair.

The ordinary meridian is closed around one special dotted cut.  No ordinary
Kirby-colour node is introduced for the dotted component.
-/
def oneTwoCutPair
    (dottedId twoHandleId : String) :
    RoleAwareDiagram .unit .unit :=
  let meridian : ComponentBoundary :=
    .atom (positiveAtom twoHandleId)
  let meridianDual : ComponentBoundary :=
    .atom (negativeAtom twoHandleId)
  .comp
    (.ordinary (.cupPositiveNegative twoHandleId))
    (.comp
      (.tensor
        (.specialDottedCut dottedId meridian)
        (.ordinary (.identity meridianDual)))
      (.ordinary (.capPositiveNegative twoHandleId)))

/-- Forget component roles by restoring every dotted cut as an encircling. -/
def erase :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target →
        ComponentDiagram source target
  | _, _, .ordinary diagram =>
      diagram
  | _, _, .specialDottedCut dottedId punctureBoundary =>
      TwistedYetter.Kirby.ComponentDottedEncircling.ComponentDiagram.openDottedEncircling
        dottedId punctureBoundary
  | _, _, .characterPower boundary _ =>
      .identityCoupon "tensor-automorphism-power" boundary
  | _, _, .comp first second =>
      first.erase ≫ᶜ second.erase
  | _, _, .tensor left right =>
      left.erase ⊗ᶜ right.erase

/-- Dotted component IDs represented by special-cut nodes. -/
def specialDottedIds :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target → List String
  | _, _, .ordinary _ =>
      []
  | _, _, .specialDottedCut dottedId _ =>
      [dottedId]
  | _, _, .characterPower _ _ =>
      []
  | _, _, .comp first second =>
      first.specialDottedIds ++ second.specialDottedIds
  | _, _, .tensor left right =>
      left.specialDottedIds ++ right.specialDottedIds

/-- Component IDs crossing the selected dotted disks. -/
def punctureIds :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target → List String
  | _, _, .ordinary _ =>
      []
  | _, _, .specialDottedCut _ punctureBoundary =>
      punctureBoundary.componentIds
  | _, _, .characterPower boundary _ =>
      boundary.componentIds
  | _, _, .comp first second =>
      first.punctureIds ++ second.punctureIds
  | _, _, .tensor left right =>
      left.punctureIds ++ right.punctureIds

/-- Component IDs still interpreted by ordinary ribbon-diagram semantics. -/
def ordinaryComponentIds :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target → List String
  | _, _, .ordinary diagram =>
      diagram.componentIds
  | _, _, .specialDottedCut _ _ =>
      []
  | _, _, .characterPower boundary _ =>
      boundary.componentIds
  | _, _, .comp first second =>
      first.ordinaryComponentIds ++ second.ordinaryComponentIds
  | _, _, .tensor left right =>
      left.ordinaryComponentIds ++ right.ordinaryComponentIds

/-- Every component ID whose label can affect role-aware interpretation. -/
def componentIds :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target → List String
  | _, _, .ordinary diagram =>
      diagram.componentIds
  | _, _, .specialDottedCut _ punctureBoundary =>
      punctureBoundary.componentIds
  | _, _, .characterPower boundary _ =>
      boundary.componentIds
  | _, _, .comp first second =>
      first.componentIds ++ second.componentIds
  | _, _, .tensor left right =>
      left.componentIds ++ right.componentIds

/-- Interpret a special cut as the normalized tensor-unit projector. -/
noncomputable def interpretSpecialDottedCut
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    (dottedId : String)
    (punctureBoundary : ComponentBoundary) :
    Diagram C
      (punctureBoundary.interpret 𝒞 labelOf)
      (punctureBoundary.interpret 𝒞 labelOf) :=
  Diagram.coupon
    ("special-dotted-unit-cut:" ++ dottedId)
    (specialDottedCutOperator 𝒞
      (punctureBoundary.interpret 𝒞 labelOf).denote)

/-- Deterministic categorical interpretation of the role-aware free syntax. -/
noncomputable def interpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S) :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target →
        Diagram C
          (source.interpret 𝒞 labelOf)
          (target.interpret 𝒞 labelOf)
  | _, _, .ordinary diagram =>
      diagram.interpret 𝒞 labelOf
  | _, _, .specialDottedCut dottedId punctureBoundary =>
      interpretSpecialDottedCut 𝒞 labelOf dottedId punctureBoundary
  | _, _, .characterPower boundary exponent =>
      Diagram.coupon "tensor-automorphism-power"
        (automorphismObjectPower η
          (boundary.interpret 𝒞 labelOf).denote exponent)
  | _, _, .comp first second =>
      first.interpret 𝒞 η labelOf ≫ᵈ second.interpret 𝒞 η labelOf
  | _, _, .tensor left right =>
      left.interpret 𝒞 η labelOf ⊗ᵈ right.interpret 𝒞 η labelOf

/-- Source-boundary IDs occur in the role-aware support. -/
theorem source_componentIds_subset
    {source target : ComponentBoundary}
    (diagram : RoleAwareDiagram source target) :
    ∀ {componentId : String},
      componentId ∈ source.componentIds →
        componentId ∈ diagram.componentIds := by
  induction diagram with
  | ordinary diagram =>
      exact diagram.source_componentIds_subset
  | specialDottedCut =>
      exact fun membership => membership
  | characterPower =>
      exact fun membership => membership
  | comp first second firstIH secondIH =>
      exact fun membership =>
        by
          simp only [componentIds, List.mem_append]
          exact Or.inl (firstIH membership)
  | tensor left right leftIH rightIH =>
      intro componentId membership
      simp only [ComponentBoundary.componentIds,
        RoleAwareDiagram.componentIds,
        List.mem_append] at membership ⊢
      cases membership with
      | inl leftMembership =>
          exact Or.inl (leftIH leftMembership)
      | inr rightMembership =>
          exact Or.inr (rightIH rightMembership)

/-- Target-boundary IDs occur in the role-aware support. -/
theorem target_componentIds_subset
    {source target : ComponentBoundary}
    (diagram : RoleAwareDiagram source target) :
    ∀ {componentId : String},
      componentId ∈ target.componentIds →
        componentId ∈ diagram.componentIds := by
  induction diagram with
  | ordinary diagram =>
      exact diagram.target_componentIds_subset
  | specialDottedCut =>
      exact fun membership => membership
  | characterPower =>
      exact fun membership => membership
  | comp first second firstIH secondIH =>
      exact fun membership =>
        by
          simp only [componentIds, List.mem_append]
          exact Or.inr (secondIH membership)
  | tensor left right leftIH rightIH =>
      intro componentId membership
      simp only [ComponentBoundary.componentIds,
        RoleAwareDiagram.componentIds,
        List.mem_append] at membership ⊢
      cases membership with
      | inl leftMembership =>
          exact Or.inl (leftIH leftMembership)
      | inr rightMembership =>
          exact Or.inr (rightIH rightMembership)

private theorem sourceBoundary_interpret_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : RoleAwareDiagram source target)
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
    (diagram : RoleAwareDiagram source target)
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

private theorem comp_interpret_heq
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

private theorem tensor_interpret_heq
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

private theorem specialCut_interpret_heq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (dottedId : String)
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      (Diagram.coupon
        ("special-dotted-unit-cut:" ++ dottedId)
        (specialDottedCutOperator 𝒞 left.denote))
      (Diagram.coupon
        ("special-dotted-unit-cut:" ++ dottedId)
        (specialDottedCutOperator 𝒞 right.denote)) := by
  subst right
  rfl

private theorem characterPower_interpret_heq
    (η : TensorIdentityAutomorphism C)
    (exponent : ℤ)
    {left right : Boundary C}
    (boundaryEq : left = right) :
    HEq
      (Diagram.coupon "tensor-automorphism-power"
        (automorphismObjectPower η left.denote exponent))
      (Diagram.coupon "tensor-automorphism-power"
        (automorphismObjectPower η right.denote exponent)) := by
  subst right
  rfl

/--
Role-aware interpretation depends only on labels of IDs in its finite
support.  The result is heterogeneous because open boundary types can change.
-/
theorem interpret_heq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (leftLabels rightLabels : String → S)
    {source target : ComponentBoundary}
    (diagram : RoleAwareDiagram source target)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    HEq (diagram.interpret 𝒞 η leftLabels)
      (diagram.interpret 𝒞 η rightLabels) := by
  induction diagram with
  | ordinary diagram =>
      exact
        diagram.interpret_heq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree
  | specialDottedCut dottedId punctureBoundary =>
      exact specialCut_interpret_heq 𝒞 dottedId
        (punctureBoundary.interpret_eq_of_eq_on_componentIds
          𝒞 leftLabels rightLabels agree)
  | characterPower boundary exponent =>
      exact characterPower_interpret_heq η exponent
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
      exact comp_interpret_heq
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
      exact tensor_interpret_heq
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

/-- Closed role-aware evaluation ignores labels outside finite support. -/
theorem eval_interpret_eq_of_eq_on_componentIds
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (leftLabels rightLabels : String → S)
    (diagram : RoleAwareDiagram .unit .unit)
    (agree :
      (componentId : String) →
      componentId ∈ diagram.componentIds →
        leftLabels componentId = rightLabels componentId) :
    Diagram.eval C (diagram.interpret 𝒞 η leftLabels) =
      Diagram.eval C (diagram.interpret 𝒞 η rightLabels) := by
  exact congrArg (Diagram.eval C)
    (eq_of_heq
      (interpret_heq_of_eq_on_componentIds
        𝒞 η leftLabels rightLabels diagram agree))

/-- The local role-aware 1--2 pair is the pivotal closure of the special cut. -/
theorem oneTwoCutPair_eval_eq_pivotalClosure
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (labelOf : String → S) :
    Diagram.eval C
        ((oneTwoCutPair dottedId twoHandleId).interpret 𝒞 η labelOf) =
      TwistedYetter.Kirby.ModularOpenKilling.pivotalClosure
        𝒞 (𝒞.simple (labelOf twoHandleId))
        (specialDottedCutOperator 𝒞
          (𝒞.simple (labelOf twoHandleId))) := by
  simp only [oneTwoCutPair, interpret, ordinary,
    ComponentDiagram.interpret, interpretSpecialDottedCut,
    Diagram.eval, ComponentBoundary.interpret, Boundary.denote,
    TwistedYetter.Kirby.ModularOpenKilling.pivotalClosure,
    pivotalTrace, leftCategoricalTrace,
    pivotalReverseExactPairing,
    CategoryTheory.ExactPairing.evaluation,
    CategoryTheory.exactPairingCongrRight]
  monoidal

/--
Category-neutral isotopy grammar for role-aware diagrams.

Special dotted cuts cannot be created, removed, or replaced by ordinary
Kirby-coloured components in this grammar.  They can only be carried through
composition and tensor contexts while ordinary subdiagrams undergo an
already checked generated ribbon isotopy.
-/
inductive GeneratedIsotopy :
    {source target : ComponentBoundary} →
      RoleAwareDiagram source target →
      RoleAwareDiagram source target → Prop
  | refl
      {source target : ComponentBoundary}
      (diagram : RoleAwareDiagram source target) :
      GeneratedIsotopy diagram diagram
  | ordinary
      {source target : ComponentBoundary}
      {before after : ComponentDiagram source target}
      (isotopy :
        ComponentRibbonIsotopy.GeneratedIsotopy before after) :
      GeneratedIsotopy (.ordinary before) (.ordinary after)
  | comp
      {source middle target : ComponentBoundary}
      {firstBefore firstAfter : RoleAwareDiagram source middle}
      {secondBefore secondAfter : RoleAwareDiagram middle target}
      (first : GeneratedIsotopy firstBefore firstAfter)
      (second : GeneratedIsotopy secondBefore secondAfter) :
      GeneratedIsotopy
        (.comp firstBefore secondBefore)
        (.comp firstAfter secondAfter)
  | tensor
      {leftSource leftTarget rightSource rightTarget :
        ComponentBoundary}
      {leftBefore leftAfter :
        RoleAwareDiagram leftSource leftTarget}
      {rightBefore rightAfter :
        RoleAwareDiagram rightSource rightTarget}
      (left : GeneratedIsotopy leftBefore leftAfter)
      (right : GeneratedIsotopy rightBefore rightAfter) :
      GeneratedIsotopy
        (.tensor leftBefore rightBefore)
        (.tensor leftAfter rightAfter)
  | symm
      {source target : ComponentBoundary}
      {before after : RoleAwareDiagram source target}
      (isotopy : GeneratedIsotopy before after) :
      GeneratedIsotopy after before
  | trans
      {source target : ComponentBoundary}
      {first second third : RoleAwareDiagram source target}
      (firstIsotopy : GeneratedIsotopy first second)
      (secondIsotopy : GeneratedIsotopy second third) :
      GeneratedIsotopy first third

namespace GeneratedIsotopy

/--
Every role-aware free isotopy evaluates equally in every premodular category.

This theorem is recursive over the visible grammar above; there is no
arbitrary graph-equivalence or evaluator-equality constructor.
-/
theorem eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    {source target : ComponentBoundary}
    {before after : RoleAwareDiagram source target}
    (isotopy : GeneratedIsotopy before after) :
    Diagram.eval C (before.interpret 𝒞 η labelOf) =
      Diagram.eval C (after.interpret 𝒞 η labelOf) := by
  induction isotopy with
  | refl =>
      rfl
  | ordinary isotopy =>
      exact
        ComponentRibbonIsotopy.GeneratedIsotopy.eval_eq
          𝒞.premodular labelOf isotopy
  | comp _ _ firstSound secondSound =>
      simp only [RoleAwareDiagram.interpret, Diagram.eval]
      rw [firstSound, secondSound]
  | tensor _ _ leftSound rightSound =>
      simp only [RoleAwareDiagram.interpret, Diagram.eval]
      rw [leftSound, rightSound]
  | symm _ sound =>
      exact sound.symm
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end GeneratedIsotopy

/--
A category-independent one-hole context for role-aware diagrams.

It stores only free syntax around the hole.  In particular, it contains no
interpreted morphism and no claim that two evaluations are equal.
-/
inductive Context :
    ComponentBoundary → ComponentBoundary →
      ComponentBoundary → ComponentBoundary → Type
  | hole (source target : ComponentBoundary) :
      Context source target source target
  | compLeft
      {holeSource holeTarget wholeSource : ComponentBoundary}
      (before : RoleAwareDiagram wholeSource holeSource) :
      Context holeSource holeTarget wholeSource holeTarget
  | compRight
      {holeSource holeTarget wholeTarget : ComponentBoundary}
      (after : RoleAwareDiagram holeTarget wholeTarget) :
      Context holeSource holeTarget holeSource wholeTarget
  | tensorLeft
      {holeSource holeTarget rightSource rightTarget :
        ComponentBoundary}
      (right : RoleAwareDiagram rightSource rightTarget) :
      Context holeSource holeTarget
        (.tensor holeSource rightSource)
        (.tensor holeTarget rightTarget)
  | tensorRight
      {leftSource leftTarget holeSource holeTarget :
        ComponentBoundary}
      (left : RoleAwareDiagram leftSource leftTarget) :
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
Embed an ordinary free-diagram context into the role-aware language.

Every stored piece is wrapped by `RoleAwareDiagram.ordinary`; consequently
the resulting context contains no special dotted cut and no character
coupon.  This is the type-level boundary used by the ordinary 2/2 band core.
-/
def ordinary :
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary} →
    ComponentRibbonDiagram.ComponentDiagram.Context
        holeSource holeTarget wholeSource wholeTarget →
      Context holeSource holeTarget wholeSource wholeTarget
  | _, _, _, _, .hole source target =>
      .hole source target
  | _, _, _, _, .compLeft before =>
      .compLeft (.ordinary before)
  | _, _, _, _, .compRight after =>
      .compRight (.ordinary after)
  | _, _, _, _, .tensorLeft right =>
      .tensorLeft (.ordinary right)
  | _, _, _, _, .tensorRight left =>
      .tensorRight (.ordinary left)
  | _, _, _, _, .compose inner outer =>
      .compose (ordinary inner) (ordinary outer)

/-- Fill the unique free hole with a role-aware diagram. -/
def plug
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary} :
    Context holeSource holeTarget wholeSource wholeTarget →
    RoleAwareDiagram holeSource holeTarget →
      RoleAwareDiagram wholeSource wholeTarget
  | .hole _ _, piece =>
      piece
  | .compLeft before, piece =>
      .comp before piece
  | .compRight after, piece =>
      .comp piece after
  | .tensorLeft right, piece =>
      .tensor piece right
  | .tensorRight left, piece =>
      .tensor left piece
  | .compose inner outer, piece =>
      outer.plug (inner.plug piece)

/-- Interpret a free role-aware context as a categorical one-hole context. -/
noncomputable def interpret
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
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
      .compLeft (before.interpret 𝒞 η labelOf)
  | _, _, _, _, .compRight after =>
      .compRight (after.interpret 𝒞 η labelOf)
  | _, _, _, _, .tensorLeft right =>
      .tensorLeft (right.interpret 𝒞 η labelOf)
  | _, _, _, _, .tensorRight left =>
      .tensorRight (left.interpret 𝒞 η labelOf)
  | _, _, _, _, .compose inner outer =>
      .compose
        (inner.interpret 𝒞 η labelOf)
        (outer.interpret 𝒞 η labelOf)

/--
Interpreting an embedded ordinary context recovers its ordinary
interpretation.  Thus the embedding adds no dotted-cut or character
semantics.
-/
theorem interpret_ordinary
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary}
    (context :
      ComponentRibbonDiagram.ComponentDiagram.Context
        holeSource holeTarget wholeSource wholeTarget) :
    (ordinary context).interpret 𝒞 η labelOf =
      context.interpret 𝒞 labelOf := by
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
      simp only [ordinary, interpret,
        ComponentRibbonDiagram.ComponentDiagram.Context.interpret,
        innerIH, outerIH]

/-- Interpretation commutes with filling the role-aware free hole. -/
theorem interpret_plug
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labelOf : String → S)
    {holeSource holeTarget wholeSource wholeTarget :
      ComponentBoundary}
    (context :
      Context holeSource holeTarget wholeSource wholeTarget)
    (piece : RoleAwareDiagram holeSource holeTarget) :
    (context.plug piece).interpret 𝒞 η labelOf =
      CategoricalTangle.Context.plug C
        (context.interpret 𝒞 η labelOf)
        (piece.interpret 𝒞 η labelOf) := by
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
        (outer.plug (inner.plug piece)).interpret 𝒞 η labelOf =
          CategoricalTangle.Context.plug C
            (outer.interpret 𝒞 η labelOf)
            (CategoricalTangle.Context.plug C
              (inner.interpret 𝒞 η labelOf)
              (piece.interpret 𝒞 η labelOf))
      rw [outerIH (inner.plug piece), innerIH piece]

end Context

/-- Machine-visible statement of the new syntax's exact semantic boundary. -/
def currentStatus : String :=
  "PASS_ROLE_AWARE_FREE_DIAGRAM_SPECIAL_DOTTED_INTERPRETER"

end RoleAwareDiagram

end TwistedYetter.Kirby.RoleAwareComponentDiagram
