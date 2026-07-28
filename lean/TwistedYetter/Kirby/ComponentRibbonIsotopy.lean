import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.PremodularFramedKink
import TwistedYetter.Kirby.PresentationIsotopy

/-!
# Generated isotopy for category-neutral component ribbon diagrams

This module turns the free component syntax into a proof-relevant framed
isotopy calculus.  A proof contains only typed component diagrams and typed
component contexts.  It contains no category object, morphism, scalar,
evaluator value, or equality of evaluator values.

Interpretation in any admitted modular category sends every primitive move
to a theorem of monoidal, braided, rigid, or ribbon graphical calculus.  The
soundness theorem is proved by recursion over the free proof term.

This file does not assert that an arbitrary pair of serialized presentations
is connected by the grammar.  Such a connection must be stored as an exact
category-neutral proof term and checked against the canonical endpoint
diagrams.
-/

namespace TwistedYetter.Kirby.ComponentRibbonIsotopy

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

namespace FreeTemplates

open ComponentDiagram

/--
Insert a closed local diagram beside an active boundary using explicit
left-unitors.
-/
def closedInsertionAt
    (boundary : List Presentation.StrandState)
    (localDiagram : ComponentDiagram .unit .unit) :
    ComponentDiagram
      (ComponentBoundary.word boundary)
      (ComponentBoundary.word boundary) :=
  .leftUnitorInv (ComponentBoundary.word boundary) ≫ᶜ
    (localDiagram ⊗ᶜ
      .identity (ComponentBoundary.word boundary)) ≫ᶜ
    .leftUnitorHom (ComponentBoundary.word boundary)

/-- A vertical identity inserted before a free diagram. -/
def identityBefore
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target) :
    ComponentDiagram source target :=
  .identity source ≫ᶜ diagram

/-- A vertical identity inserted after a free diagram. -/
def identityAfter
    {source target : ComponentBoundary}
    (diagram : ComponentDiagram source target) :
    ComponentDiagram source target :=
  diagram ≫ᶜ .identity target

/-- Two parenthesizations of a three-stage vertical composition. -/
def compAssocBefore
    {a b c d : ComponentBoundary}
    (first : ComponentDiagram a b)
    (second : ComponentDiagram b c)
    (third : ComponentDiagram c d) :
    ComponentDiagram a d :=
  (first ≫ᶜ second) ≫ᶜ third

def compAssocAfter
    {a b c d : ComponentBoundary}
    (first : ComponentDiagram a b)
    (second : ComponentDiagram b c)
    (third : ComponentDiagram c d) :
    ComponentDiagram a d :=
  first ≫ᶜ (second ≫ᶜ third)

/-- Interchange two disjoint critical events. -/
def interchangeBefore
    {a b c e f g : ComponentBoundary}
    (leftFirst : ComponentDiagram a b)
    (leftSecond : ComponentDiagram b c)
    (rightFirst : ComponentDiagram e f)
    (rightSecond : ComponentDiagram f g) :
    ComponentDiagram (.tensor a e) (.tensor c g) :=
  (leftFirst ⊗ᶜ rightFirst) ≫ᶜ
    (leftSecond ⊗ᶜ rightSecond)

def interchangeAfter
    {a b c e f g : ComponentBoundary}
    (leftFirst : ComponentDiagram a b)
    (leftSecond : ComponentDiagram b c)
    (rightFirst : ComponentDiagram e f)
    (rightSecond : ComponentDiagram f g) :
    ComponentDiagram (.tensor a e) (.tensor c g) :=
  (leftFirst ≫ᶜ leftSecond) ⊗ᶜ
    (rightFirst ≫ᶜ rightSecond)

/-- Positive/negative and negative/positive Reidemeister-II pairs. -/
def reidemeisterIIPositiveBefore
    (left right : ComponentBoundary) :
    ComponentDiagram (.tensor left right) (.tensor left right) :=
  .crossingPositive left right ≫ᶜ
    .crossingNegative right left

def reidemeisterIINegativeBefore
    (left right : ComponentBoundary) :
    ComponentDiagram (.tensor left right) (.tensor left right) :=
  .crossingNegative left right ≫ᶜ
    .crossingPositive right left

def reidemeisterIIAfter
    (left right : ComponentBoundary) :
    ComponentDiagram (.tensor left right) (.tensor left right) :=
  .identity _

/-- Left side of Reidemeister III with associators retained explicitly. -/
def reidemeisterIIIBefore
    (left middle right : ComponentBoundary) :
    ComponentDiagram
      (.tensor left (.tensor middle right))
      (.tensor right (.tensor middle left)) :=
  .associatorInv left middle right ≫ᶜ
    (.crossingPositive left middle ⊗ᶜ .identity right) ≫ᶜ
    .associatorHom middle left right ≫ᶜ
    (.identity middle ⊗ᶜ .crossingPositive left right) ≫ᶜ
    .associatorInv middle right left ≫ᶜ
    (.crossingPositive middle right ⊗ᶜ .identity left) ≫ᶜ
    .associatorHom right middle left

/-- Right side of Reidemeister III with associators retained explicitly. -/
def reidemeisterIIIAfter
    (left middle right : ComponentBoundary) :
    ComponentDiagram
      (.tensor left (.tensor middle right))
      (.tensor right (.tensor middle left)) :=
  (.identity left ⊗ᶜ .crossingPositive middle right) ≫ᶜ
    .associatorInv left right middle ≫ᶜ
    (.crossingPositive left right ⊗ᶜ .identity middle) ≫ᶜ
    .associatorHom right left middle ≫ᶜ
    (.identity right ⊗ᶜ .crossingPositive left middle)

/-- Snake on a positively oriented component and its selected right dual. -/
def rightPrimalSnakeBefore (componentId : String) :
    ComponentDiagram
      (.atom (positiveAtom componentId))
      (.atom (positiveAtom componentId)) :=
  .leftUnitorInv (.atom (positiveAtom componentId)) ≫ᶜ
    (.cupPositiveNegative componentId ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    .associatorHom
      (.atom (positiveAtom componentId))
      (.atom (negativeAtom componentId))
      (.atom (positiveAtom componentId)) ≫ᶜ
    (.identity (.atom (positiveAtom componentId)) ⊗ᶜ
      .capNegativePositive componentId) ≫ᶜ
    .rightUnitorHom (.atom (positiveAtom componentId))

/-- The opposite snake on the selected right-dual occurrence. -/
def rightDualSnakeBefore (componentId : String) :
    ComponentDiagram
      (.atom (negativeAtom componentId))
      (.atom (negativeAtom componentId)) :=
  .rightUnitorInv (.atom (negativeAtom componentId)) ≫ᶜ
    (.identity (.atom (negativeAtom componentId)) ⊗ᶜ
      .cupPositiveNegative componentId) ≫ᶜ
    .associatorInv
      (.atom (negativeAtom componentId))
      (.atom (positiveAtom componentId))
      (.atom (negativeAtom componentId)) ≫ᶜ
    (.capNegativePositive componentId ⊗ᶜ
      .identity (.atom (negativeAtom componentId))) ≫ᶜ
    .leftUnitorHom (.atom (negativeAtom componentId))

/-- Positive blackboard kink on a positively oriented component. -/
def positiveKink (componentId : String) :
    ComponentDiagram
      (.atom (positiveAtom componentId))
      (.atom (positiveAtom componentId)) :=
  .leftUnitorInv (.atom (positiveAtom componentId)) ≫ᶜ
    (.cupPositiveNegative componentId ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    .associatorHom
      (.atom (positiveAtom componentId))
      (.atom (negativeAtom componentId))
      (.atom (positiveAtom componentId)) ≫ᶜ
    (.identity (.atom (positiveAtom componentId)) ⊗ᶜ
      .crossingPositive
        (.atom (negativeAtom componentId))
        (.atom (positiveAtom componentId))) ≫ᶜ
    (.identity (.atom (positiveAtom componentId)) ⊗ᶜ
      .capPositiveNegative componentId) ≫ᶜ
    .rightUnitorHom (.atom (positiveAtom componentId))

/-- Negative blackboard kink on a positively oriented component. -/
def negativeKink (componentId : String) :
    ComponentDiagram
      (.atom (positiveAtom componentId))
      (.atom (positiveAtom componentId)) :=
  .leftUnitorInv (.atom (positiveAtom componentId)) ≫ᶜ
    (.cupPositiveNegative componentId ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    .associatorHom
      (.atom (positiveAtom componentId))
      (.atom (negativeAtom componentId))
      (.atom (positiveAtom componentId)) ≫ᶜ
    (.identity (.atom (positiveAtom componentId)) ⊗ᶜ
      .crossingNegative
        (.atom (negativeAtom componentId))
        (.atom (positiveAtom componentId))) ≫ᶜ
    (.identity (.atom (positiveAtom componentId)) ⊗ᶜ
      .capPositiveNegative componentId) ≫ᶜ
    .rightUnitorHom (.atom (positiveAtom componentId))

/-- Canonical isolated birth window for one oriented component. -/
def zeroFramedBirthWindow
    (birthEventId componentId positiveId negativeId : String) :
    CanonicalKirbyTrace.EventWindow
      (.birth birthEventId componentId positiveId negativeId 0)
      []
      [CanonicalKirbyTrace.positiveStrand positiveId componentId,
        CanonicalKirbyTrace.negativeStrand negativeId componentId] :=
  .birth birthEventId componentId positiveId negativeId [] []

/-- Canonical isolated death window for the same oriented component. -/
def zeroFramedDeathWindow
    (deathEventId componentId positiveId negativeId : String) :
    CanonicalKirbyTrace.EventWindow
      (.death deathEventId componentId positiveId negativeId)
      [CanonicalKirbyTrace.positiveStrand positiveId componentId,
        CanonicalKirbyTrace.negativeStrand negativeId componentId]
      [] :=
  .deathPositiveNegative deathEventId componentId
    positiveId negativeId positiveId negativeId
    (by simp [Presentation.RawPresentation.sameStringSet]) [] []

/-- Free diagram generated by the exact isolated birth/death event script. -/
def zeroFramedEventDiagram
    (birthEventId deathEventId componentId positiveId negativeId : String) :
    ComponentDiagram .unit .unit :=
  ComponentRibbonDiagram.EventWindow.componentPrimitive
      (zeroFramedBirthWindow
        birthEventId componentId positiveId negativeId) ≫ᶜ
    ComponentRibbonDiagram.EventWindow.componentPrimitive
      (zeroFramedDeathWindow
        deathEventId componentId positiveId negativeId)

/--
Free diagram generated by the exact isolated six-event movie for a positive
Hopf pair: birth the meridian, birth the dotted circle, cross twice, then
remove the dotted circle and the meridian.
-/
def oneTwoHopfEventDiagram
    (twoBirthId dottedBirthId firstCrossingId secondCrossingId
      dottedDeathId twoDeathId dottedId twoHandleId
      dottedPositiveId dottedNegativeId twoPositiveId twoNegativeId :
      String) :
    ComponentDiagram .unit .unit :=
  let dottedPositive :=
    CanonicalKirbyTrace.positiveStrand dottedPositiveId dottedId
  let dottedNegative :=
    CanonicalKirbyTrace.negativeStrand dottedNegativeId dottedId
  let twoPositive :=
    CanonicalKirbyTrace.positiveStrand twoPositiveId twoHandleId
  let twoNegative :=
    CanonicalKirbyTrace.negativeStrand twoNegativeId twoHandleId
  let twoBirth :
      CanonicalKirbyTrace.EventWindow
        (.birth twoBirthId twoHandleId twoPositiveId twoNegativeId 0)
        [] [twoPositive, twoNegative] :=
    .birth twoBirthId twoHandleId twoPositiveId twoNegativeId [] []
  let dottedBirth :
      CanonicalKirbyTrace.EventWindow
        (.birth dottedBirthId dottedId
          dottedPositiveId dottedNegativeId 0)
        [twoPositive, twoNegative]
        [dottedPositive, dottedNegative, twoPositive, twoNegative] :=
    .birth dottedBirthId dottedId dottedPositiveId dottedNegativeId
      [] [twoPositive, twoNegative]
  let firstCrossing :
      CanonicalKirbyTrace.EventWindow
        (.crossing firstCrossingId dottedNegativeId twoPositiveId .positive)
        [dottedPositive, dottedNegative, twoPositive, twoNegative]
        [dottedPositive, twoPositive, dottedNegative, twoNegative] :=
    .crossing firstCrossingId dottedNegativeId twoPositiveId .positive
      dottedId twoHandleId .negative .positive
      [dottedPositive] [twoNegative]
  let secondCrossing :
      CanonicalKirbyTrace.EventWindow
        (.crossing secondCrossingId twoPositiveId dottedNegativeId .positive)
        [dottedPositive, twoPositive, dottedNegative, twoNegative]
        [dottedPositive, dottedNegative, twoPositive, twoNegative] :=
    .crossing secondCrossingId twoPositiveId dottedNegativeId .positive
      twoHandleId dottedId .positive .negative
      [dottedPositive] [twoNegative]
  let dottedDeath :
      CanonicalKirbyTrace.EventWindow
        (.death dottedDeathId dottedId dottedPositiveId dottedNegativeId)
        [dottedPositive, dottedNegative, twoPositive, twoNegative]
        [twoPositive, twoNegative] :=
    .deathPositiveNegative dottedDeathId dottedId
      dottedPositiveId dottedNegativeId
      dottedPositiveId dottedNegativeId
      (by simp [Presentation.RawPresentation.sameStringSet])
      [] [twoPositive, twoNegative]
  let twoDeath :
      CanonicalKirbyTrace.EventWindow
        (.death twoDeathId twoHandleId twoPositiveId twoNegativeId)
        [twoPositive, twoNegative] [] :=
    .deathPositiveNegative twoDeathId twoHandleId
      twoPositiveId twoNegativeId twoPositiveId twoNegativeId
      (by simp [Presentation.RawPresentation.sameStringSet]) [] []
  ComponentRibbonDiagram.EventWindow.componentPrimitive twoBirth ≫ᶜ
    ComponentRibbonDiagram.EventWindow.componentPrimitive dottedBirth ≫ᶜ
    ComponentRibbonDiagram.EventWindow.componentPrimitive firstCrossing ≫ᶜ
    ComponentRibbonDiagram.EventWindow.componentPrimitive secondCrossing ≫ᶜ
    ComponentRibbonDiagram.EventWindow.componentPrimitive dottedDeath ≫ᶜ
    ComponentRibbonDiagram.EventWindow.componentPrimitive twoDeath

end FreeTemplates

/--
Primitive evaluator-preserving moves in the category-neutral syntax.

There is no constructor accepting an arbitrary proposition or equality.
-/
inductive TaggedMove :
    {source target : ComponentBoundary} →
      ComponentDiagram source target →
      ComponentDiagram source target → Type
  | identityBefore
      {source target : ComponentBoundary}
      (diagram : ComponentDiagram source target) :
      TaggedMove (FreeTemplates.identityBefore diagram) diagram
  | identityAfter
      {source target : ComponentBoundary}
      (diagram : ComponentDiagram source target) :
      TaggedMove (FreeTemplates.identityAfter diagram) diagram
  | compAssoc
      {a b c d : ComponentBoundary}
      (first : ComponentDiagram a b)
      (second : ComponentDiagram b c)
      (third : ComponentDiagram c d) :
      TaggedMove
        (FreeTemplates.compAssocBefore first second third)
        (FreeTemplates.compAssocAfter first second third)
  | interchange
      {a b c e f g : ComponentBoundary}
      (leftFirst : ComponentDiagram a b)
      (leftSecond : ComponentDiagram b c)
      (rightFirst : ComponentDiagram e f)
      (rightSecond : ComponentDiagram f g) :
      TaggedMove
        (FreeTemplates.interchangeBefore
          leftFirst leftSecond rightFirst rightSecond)
        (FreeTemplates.interchangeAfter
          leftFirst leftSecond rightFirst rightSecond)
  | reidemeisterIIPositive
      (left right : ComponentBoundary) :
      TaggedMove
        (FreeTemplates.reidemeisterIIPositiveBefore left right)
        (FreeTemplates.reidemeisterIIAfter left right)
  | reidemeisterIINegative
      (left right : ComponentBoundary) :
      TaggedMove
        (FreeTemplates.reidemeisterIINegativeBefore left right)
        (FreeTemplates.reidemeisterIIAfter left right)
  | reidemeisterIII
      (left middle right : ComponentBoundary) :
      TaggedMove
        (FreeTemplates.reidemeisterIIIBefore left middle right)
        (FreeTemplates.reidemeisterIIIAfter left middle right)
  | rightPrimalSnake (componentId : String) :
      TaggedMove
        (FreeTemplates.rightPrimalSnakeBefore componentId)
        (.identity (.atom (positiveAtom componentId)))
  | rightDualSnake (componentId : String) :
      TaggedMove
        (FreeTemplates.rightDualSnakeBefore componentId)
        (.identity (.atom (negativeAtom componentId)))
  | framedPositive (componentId : String) :
      TaggedMove
        (FreeTemplates.positiveKink componentId)
        (.twistPositive (positiveAtom componentId))
  | framedNegative (componentId : String) :
      TaggedMove
        (FreeTemplates.negativeKink componentId)
        (.twistNegative (positiveAtom componentId))
  | eraseIdentityCoupon
      (couponId : String)
      (boundary : ComponentBoundary) :
      TaggedMove
        (.identityCoupon couponId boundary)
        (.identity boundary)
  | surroundPairComp
      (firstStrand secondStrand : Presentation.StrandState)
      (suffix : List Presentation.StrandState)
      (first :
        ComponentDiagram .unit
          (ComponentBoundary.word [firstStrand, secondStrand]))
      (second :
        ComponentDiagram
          (ComponentBoundary.word [firstStrand, secondStrand]) .unit) :
      TaggedMove
        ((ComponentDiagram.Context.surroundBoundaryWord
            [] [] [firstStrand, secondStrand] suffix).plug first ≫ᶜ
          (ComponentDiagram.Context.surroundBoundaryWord
            [] [firstStrand, secondStrand] [] suffix).plug second)
        ((ComponentDiagram.Context.surroundBoundaryWord
            [] [] [] suffix).plug
          (first ≫ᶜ second))
  | closedInsertionFactor
      (boundary : List Presentation.StrandState)
      (localDiagram : ComponentDiagram .unit .unit)
      (prefixDiagram :
        ComponentDiagram .unit (ComponentBoundary.word boundary))
      (suffixDiagram :
        ComponentDiagram (ComponentBoundary.word boundary) .unit) :
      TaggedMove
        ((prefixDiagram ≫ᶜ
          FreeTemplates.closedInsertionAt boundary localDiagram) ≫ᶜ
          suffixDiagram)
        (ComponentDiagram.closedTensor localDiagram
          (prefixDiagram ≫ᶜ suffixDiagram))
  | surroundClosedInsertion
      (boundary : List Presentation.StrandState)
      (localDiagram : ComponentDiagram .unit .unit) :
      TaggedMove
        ((ComponentDiagram.Context.surroundBoundaryWord
          [] [] [] boundary).plug localDiagram)
        (FreeTemplates.closedInsertionAt boundary localDiagram)
  | zeroFramedEventNormalization
      (birthEventId deathEventId componentId positiveId negativeId :
        String) :
      TaggedMove
        (FreeTemplates.zeroFramedEventDiagram
          birthEventId deathEventId componentId positiveId negativeId)
        (ComponentDiagram.zeroFramedUnknot componentId)
  | oneTwoHopfEventNormalization
      (twoBirthId dottedBirthId firstCrossingId secondCrossingId
        dottedDeathId twoDeathId dottedId twoHandleId
        dottedPositiveId dottedNegativeId twoPositiveId twoNegativeId :
        String) :
      TaggedMove
        (FreeTemplates.oneTwoHopfEventDiagram
          twoBirthId dottedBirthId firstCrossingId secondCrossingId
          dottedDeathId twoDeathId dottedId twoHandleId
          dottedPositiveId dottedNegativeId twoPositiveId twoNegativeId)
        (ComponentDiagram.oneTwoHopfPair dottedId twoHandleId)

/-- Reflexive, symmetric, transitive, and typed-context closure. -/
inductive GeneratedIsotopy :
    {source target : ComponentBoundary} →
      ComponentDiagram source target →
      ComponentDiagram source target → Prop
  | refl
      {source target : ComponentBoundary}
      (diagram : ComponentDiagram source target) :
      GeneratedIsotopy diagram diagram
  | step
      {source target : ComponentBoundary}
      {before after : ComponentDiagram source target}
      (move : TaggedMove before after) :
      GeneratedIsotopy before after
  | symm
      {source target : ComponentBoundary}
      {before after : ComponentDiagram source target} :
      GeneratedIsotopy before after →
        GeneratedIsotopy after before
  | trans
      {source target : ComponentBoundary}
      {first middle last : ComponentDiagram source target} :
      GeneratedIsotopy first middle →
      GeneratedIsotopy middle last →
        GeneratedIsotopy first last
  | inContext
      {holeSource holeTarget wholeSource wholeTarget :
        ComponentBoundary}
      {before after : ComponentDiagram holeSource holeTarget}
      (context :
        ComponentDiagram.Context
          holeSource holeTarget wholeSource wholeTarget) :
      GeneratedIsotopy before after →
        GeneratedIsotopy
          (context.plug before) (context.plug after)

namespace TaggedMove

/--
Inserting a tensor-unit endomorphism at an intermediate boundary factors as
the closed tensor product of that endomorphism with the retained closed
morphism.

This is the Eckmann--Hilton centrality calculation for `End(𝟙)`, expressed
before scalarization.  It uses only monoidal coherence and naturality.
-/
theorem closedInsertionFactor_monoidal
    (B : C)
    (localMorphism : 𝟙_ C ⟶ 𝟙_ C)
    (prefixMorphism : 𝟙_ C ⟶ B)
    (suffixMorphism : B ⟶ 𝟙_ C) :
    (prefixMorphism ≫
        (λ_ B).inv ≫
        (localMorphism ⊗ₘ 𝟙 B) ≫
        (λ_ B).hom) ≫
      suffixMorphism =
    (λ_ (𝟙_ C)).inv ≫
      (localMorphism ⊗ₘ
        (prefixMorphism ≫ suffixMorphism)) ≫
      (λ_ (𝟙_ C)).hom := by
  simp only [MonoidalCategory.tensorHom_def',
    MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Category.assoc, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.id_whiskerLeft, Iso.inv_hom_id_assoc,
    MonoidalCategory.whiskerRight_id, ← MonoidalCategory.unitors_equal,
    ← MonoidalCategory.unitors_inv_equal, Iso.inv_hom_id,
    Category.comp_id]
  rw [← MonoidalCategory.leftUnitor_naturality suffixMorphism]
  rw [← Category.assoc (localMorphism ▷ B)]
  rw [← MonoidalCategory.whisker_exchange
    localMorphism suffixMorphism]
  have naturality :
      (λ_ B).inv ≫ (𝟙_ C ◁ suffixMorphism) ≫
          (localMorphism ▷ 𝟙_ C) =
        suffixMorphism ≫ (λ_ (𝟙_ C)).inv ≫
          (localMorphism ▷ 𝟙_ C) := by
    exact
      (MonoidalCategory.leftUnitor_inv_naturality_assoc
        suffixMorphism (localMorphism ▷ 𝟙_ C)).symm
  slice_lhs 2 4 => rw [naturality]
  simp [← MonoidalCategory.unitors_equal,
    ← MonoidalCategory.unitors_inv_equal]

/-- Every free primitive preserves categorical evaluation after interpretation. -/
theorem eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    {source target : ComponentBoundary}
    {before after : ComponentDiagram source target}
    (move : TaggedMove before after) :
    Diagram.eval C (before.interpret 𝒞.premodular labelOf) =
      Diagram.eval C (after.interpret 𝒞.premodular labelOf) := by
  cases move with
  | identityBefore diagram =>
      simp [FreeTemplates.identityBefore, ComponentDiagram.interpret,
        Diagram.eval]
  | identityAfter diagram =>
      simp [FreeTemplates.identityAfter, ComponentDiagram.interpret,
        Diagram.eval]
  | compAssoc first second third =>
      simp [FreeTemplates.compAssocBefore, FreeTemplates.compAssocAfter,
        ComponentDiagram.interpret, Diagram.eval, Category.assoc]
  | interchange leftFirst leftSecond rightFirst rightSecond =>
      exact MonoidalCategory.tensorHom_comp_tensorHom
        (Diagram.eval C (leftFirst.interpret 𝒞.premodular labelOf))
        (Diagram.eval C (rightFirst.interpret 𝒞.premodular labelOf))
        (Diagram.eval C (leftSecond.interpret 𝒞.premodular labelOf))
        (Diagram.eval C (rightSecond.interpret 𝒞.premodular labelOf))
  | reidemeisterIIPositive left right =>
      simp [FreeTemplates.reidemeisterIIPositiveBefore,
        FreeTemplates.reidemeisterIIAfter,
        ComponentDiagram.interpret, Diagram.eval]
  | reidemeisterIINegative left right =>
      simp [FreeTemplates.reidemeisterIINegativeBefore,
        FreeTemplates.reidemeisterIIAfter,
        ComponentDiagram.interpret, Diagram.eval]
  | reidemeisterIII left middle right =>
      simpa [FreeTemplates.reidemeisterIIIBefore,
        FreeTemplates.reidemeisterIIIAfter,
        ComponentDiagram.interpret, Diagram.eval, Boundary.denote] using
        BraidedCategory.yang_baxter
          (left.interpret 𝒞.premodular labelOf).denote
          (middle.interpret 𝒞.premodular labelOf).denote
          (right.interpret 𝒞.premodular labelOf).denote
  | rightPrimalSnake componentId =>
      let X := 𝒞.premodular.simple (labelOf componentId)
      simpa [FreeTemplates.rightPrimalSnakeBefore,
        ComponentDiagram.interpret, ComponentBoundary.interpret,
        ComponentAtom.interpret, positiveAtom, negativeAtom,
        Diagram.eval, Boundary.denote] using
        TwistedYetter.Kirby.PresentationIsotopy.rightPrimalSnake_sound X
  | rightDualSnake componentId =>
      let X := 𝒞.premodular.simple (labelOf componentId)
      simpa [FreeTemplates.rightDualSnakeBefore,
        ComponentDiagram.interpret, ComponentBoundary.interpret,
        ComponentAtom.interpret, positiveAtom, negativeAtom,
        Diagram.eval, Boundary.denote] using
        TwistedYetter.Kirby.PresentationIsotopy.rightDualSnake_sound X
  | framedPositive componentId =>
      let X := 𝒞.premodular.simple (labelOf componentId)
      simpa [FreeTemplates.positiveKink, ComponentDiagram.interpret,
        TwistedYetter.Kirby.PresentationIsotopy.positiveKink,
        TwistedYetter.Kirby.PresentationIsotopy.leftUnitorInvDiagram,
        TwistedYetter.Kirby.PresentationIsotopy.associatorHomDiagram,
        TwistedYetter.Kirby.PresentationIsotopy.rightUnitorHomDiagram,
        Diagram.eval, Boundary.denote] using
        (ribbonFramedKinkEvaluation 𝒞).positive_sound X
  | framedNegative componentId =>
      let X := 𝒞.premodular.simple (labelOf componentId)
      simpa [FreeTemplates.negativeKink, ComponentDiagram.interpret,
        TwistedYetter.Kirby.PresentationIsotopy.negativeKink,
        TwistedYetter.Kirby.PresentationIsotopy.leftUnitorInvDiagram,
        TwistedYetter.Kirby.PresentationIsotopy.associatorHomDiagram,
        TwistedYetter.Kirby.PresentationIsotopy.rightUnitorHomDiagram,
        Diagram.eval, Boundary.denote] using
        (ribbonFramedKinkEvaluation 𝒞).negative_sound X
  | eraseIdentityCoupon couponId boundary =>
      simp [ComponentDiagram.interpret, Diagram.eval]
  | surroundPairComp firstStrand secondStrand suffix first second =>
      cases suffix with
      | nil =>
          simp [ComponentDiagram.Context.surroundBoundaryWord,
            ComponentDiagram.Context.plug,
            ComponentDiagram.Context.splitBoundaryWord,
            ComponentDiagram.Context.joinBoundaryWord,
            ComponentDiagram.interpret, Diagram.eval]
          monoidal
      | cons suffixHead suffixTail =>
          simp [ComponentDiagram.Context.surroundBoundaryWord,
            ComponentDiagram.Context.plug,
            ComponentDiagram.Context.splitBoundaryWord,
            ComponentDiagram.Context.joinBoundaryWord,
            ComponentDiagram.interpret, Diagram.eval]
          monoidal
  | closedInsertionFactor boundary localDiagram prefixDiagram suffixDiagram =>
      rw [ComponentDiagram.interpret_closedTensor]
      change
        (Diagram.eval C
              (prefixDiagram.interpret 𝒞.premodular labelOf) ≫
            (λ_
              ((ComponentBoundary.word boundary).interpret
                𝒞.premodular labelOf).denote).inv ≫
            (Diagram.eval C
                (localDiagram.interpret 𝒞.premodular labelOf) ⊗ₘ
              𝟙
                ((ComponentBoundary.word boundary).interpret
                  𝒞.premodular labelOf).denote) ≫
            (λ_
              ((ComponentBoundary.word boundary).interpret
                𝒞.premodular labelOf).denote).hom) ≫
          Diagram.eval C
            (suffixDiagram.interpret 𝒞.premodular labelOf) =
        (λ_ (𝟙_ C)).inv ≫
          (Diagram.eval C
                (localDiagram.interpret 𝒞.premodular labelOf) ⊗ₘ
              (Diagram.eval C
                  (prefixDiagram.interpret 𝒞.premodular labelOf) ≫
                Diagram.eval C
                  (suffixDiagram.interpret
                    𝒞.premodular labelOf))) ≫
            (λ_ (𝟙_ C)).hom
      exact
        closedInsertionFactor_monoidal
          ((ComponentBoundary.word boundary).interpret
            𝒞.premodular labelOf).denote
          (Diagram.eval C
            (localDiagram.interpret 𝒞.premodular labelOf))
          (Diagram.eval C
            (prefixDiagram.interpret 𝒞.premodular labelOf))
          (Diagram.eval C
            (suffixDiagram.interpret 𝒞.premodular labelOf))
  | surroundClosedInsertion boundary localDiagram =>
      cases boundary with
      | nil =>
          simp [ComponentDiagram.Context.surroundBoundaryWord,
            ComponentDiagram.Context.plug,
            ComponentDiagram.Context.splitBoundaryWord,
            ComponentDiagram.Context.joinBoundaryWord,
            FreeTemplates.closedInsertionAt,
            ComponentBoundary.word, ComponentBoundary.interpret,
            Boundary.denote, ComponentDiagram.interpret, Diagram.eval]
          monoidal
      | cons boundaryHead boundaryTail =>
          simp [ComponentDiagram.Context.surroundBoundaryWord,
            ComponentDiagram.Context.plug,
            ComponentDiagram.Context.splitBoundaryWord,
            ComponentDiagram.Context.joinBoundaryWord,
            FreeTemplates.closedInsertionAt,
            ComponentBoundary.word, ComponentBoundary.interpret,
            Boundary.denote, ComponentDiagram.interpret, Diagram.eval]
  | zeroFramedEventNormalization birthEventId deathEventId componentId
      positiveId negativeId =>
      simp [FreeTemplates.zeroFramedEventDiagram,
        FreeTemplates.zeroFramedBirthWindow,
        FreeTemplates.zeroFramedDeathWindow,
        ComponentRibbonDiagram.EventWindow.componentPrimitive,
        ComponentDiagram.Context.surroundBoundaryWord,
        ComponentDiagram.Context.plug,
        ComponentDiagram.Context.splitBoundaryWord,
        ComponentDiagram.Context.joinBoundaryWord,
        ComponentDiagram.zeroFramedUnknot,
        ComponentDiagram.interpret, Diagram.eval]
      monoidal
  | oneTwoHopfEventNormalization
      twoBirthId dottedBirthId firstCrossingId secondCrossingId
      dottedDeathId twoDeathId dottedId twoHandleId
      dottedPositiveId dottedNegativeId twoPositiveId twoNegativeId =>
      simp [FreeTemplates.oneTwoHopfEventDiagram,
        ComponentRibbonDiagram.EventWindow.componentPrimitive,
        ComponentDiagram.Context.surroundBoundaryWord,
        ComponentDiagram.Context.plug,
        ComponentDiagram.Context.splitBoundaryWord,
        ComponentDiagram.Context.joinBoundaryWord,
        ComponentDiagram.oneTwoHopfPair,
        ComponentDiagram.openDottedEncircling,
        ComponentDiagram.interpret, Diagram.eval]
      monoidal
end TaggedMove

namespace GeneratedIsotopy

/--
Appending typed canonical traces agrees with vertically composing their free
component diagrams, up to the explicit identity and associativity moves of the
free graphical grammar.

This is intentionally an isotopy proof rather than an equality of syntax
trees: the two sides generally have different parenthesizations.
-/
theorem componentDiagram_append
    {raw : Presentation.RawPresentation}
    {firstEvents secondEvents : List Presentation.SliceEvent}
    {initial middle final : List Presentation.StrandState}
    (first :
      CanonicalKirbyTrace.Trace raw firstEvents initial middle)
    (second :
      CanonicalKirbyTrace.Trace raw secondEvents middle final) :
    GeneratedIsotopy
      (ComponentRibbonDiagram.Trace.componentDiagram
        (first.append second))
      (ComponentRibbonDiagram.Trace.componentDiagram first ≫ᶜ
        ComponentRibbonDiagram.Trace.componentDiagram second) := by
  induction first with
  | nil =>
      exact
        .symm (.step
          (.identityBefore
            (ComponentRibbonDiagram.Trace.componentDiagram second)))
  | cons window stepSound tail inductionHypothesis =>
      exact
        .trans
          (.inContext
            (.compLeft
              (ComponentRibbonDiagram.EventWindow.componentPrimitive window))
            (inductionHypothesis second))
          (.symm (.step
            (.compAssoc
              (ComponentRibbonDiagram.EventWindow.componentPrimitive window)
              (ComponentRibbonDiagram.Trace.componentDiagram tail)
              (ComponentRibbonDiagram.Trace.componentDiagram second))))

/--
The complete free diagram of an exact three-way trace split is isotopic to
the visible composition of its prefix, local window, and suffix.
-/
theorem componentDiagram_splitThree
    {raw : Presentation.RawPresentation}
    (prefixEvents windowEvents suffixEvents :
      List Presentation.SliceEvent)
    {initial final : List Presentation.StrandState}
    (split :
      CanonicalKirbyTrace.Trace.ThreeWaySplit
        (raw := raw) (initial := initial) (final := final)
        prefixEvents windowEvents suffixEvents) :
    GeneratedIsotopy
      (ComponentRibbonDiagram.Trace.componentDiagram split.wholeTrace)
      ((ComponentRibbonDiagram.Trace.componentDiagram split.prefixTrace ≫ᶜ
          ComponentRibbonDiagram.Trace.componentDiagram split.windowTrace) ≫ᶜ
        ComponentRibbonDiagram.Trace.componentDiagram split.suffixTrace) := by
  rw [← split.reassembles]
  exact
    .trans
      (componentDiagram_append
        (split.prefixTrace.append split.windowTrace)
        split.suffixTrace)
      (.inContext
        (.compRight
          (ComponentRibbonDiagram.Trace.componentDiagram split.suffixTrace))
        (componentDiagram_append split.prefixTrace split.windowTrace))

/--
Replace all three pieces of a vertically composed diagram by generated
isotopies.  This is the category-neutral congruence needed when a local
Kirby window is reinserted between a common prefix and suffix.
-/
theorem verticalTriple
    {a b c d : ComponentBoundary}
    {prefixBefore prefixAfter : ComponentDiagram a b}
    {windowBefore windowAfter : ComponentDiagram b c}
    {suffixBefore suffixAfter : ComponentDiagram c d}
    (prefixIsotopy : GeneratedIsotopy prefixBefore prefixAfter)
    (windowIsotopy : GeneratedIsotopy windowBefore windowAfter)
    (suffixIsotopy : GeneratedIsotopy suffixBefore suffixAfter) :
    GeneratedIsotopy
      ((prefixBefore ≫ᶜ windowBefore) ≫ᶜ suffixBefore)
      ((prefixAfter ≫ᶜ windowAfter) ≫ᶜ suffixAfter) := by
  exact
    .trans
      (.inContext
        (.compose (.compRight windowBefore) (.compRight suffixBefore))
        prefixIsotopy)
      (.trans
        (.inContext
          (.compose (.compLeft prefixAfter) (.compRight suffixBefore))
          windowIsotopy)
        (.inContext
          (.compLeft (prefixAfter ≫ᶜ windowAfter))
          suffixIsotopy))

/-- Tensor a closed generated isotopy on the right of a fixed closed diagram. -/
theorem closedTensorRight
    (left : ComponentDiagram .unit .unit)
    {before after : ComponentDiagram .unit .unit}
    (isotopy : GeneratedIsotopy before after) :
    GeneratedIsotopy
      (ComponentDiagram.closedTensor left before)
      (ComponentDiagram.closedTensor left after) := by
  exact
    .trans
      (.symm
        (.step
          (.compAssoc
            (.leftUnitorInv .unit)
            (left ⊗ᶜ before)
            (.leftUnitorHom .unit))))
      (.trans
        (.inContext
          (.compRight (.leftUnitorHom .unit))
          (.inContext
            (.compLeft (.leftUnitorInv .unit))
            (.inContext (.tensorRight left) isotopy)))
        (.step
          (.compAssoc
            (.leftUnitorInv .unit)
            (left ⊗ᶜ after)
            (.leftUnitorHom .unit))))

/--
Lift a local trace-window replacement through independently typed source and
target prefixes and suffixes.

The shared intermediate strand-state indices are explicit in the type.  No
raw event-list equality can silently stand in for the three required free
diagram isotopies.
-/
theorem traceTripleReplacement
    {sourceRaw targetRaw : Presentation.RawPresentation}
    {sourcePrefixEvents sourceWindowEvents sourceSuffixEvents
      targetPrefixEvents targetWindowEvents targetSuffixEvents :
      List Presentation.SliceEvent}
    {initial afterPrefix afterWindow final :
      List Presentation.StrandState}
    (sourcePrefix :
      CanonicalKirbyTrace.Trace sourceRaw sourcePrefixEvents
        initial afterPrefix)
    (sourceWindow :
      CanonicalKirbyTrace.Trace sourceRaw sourceWindowEvents
        afterPrefix afterWindow)
    (sourceSuffix :
      CanonicalKirbyTrace.Trace sourceRaw sourceSuffixEvents
        afterWindow final)
    (targetPrefix :
      CanonicalKirbyTrace.Trace targetRaw targetPrefixEvents
        initial afterPrefix)
    (targetWindow :
      CanonicalKirbyTrace.Trace targetRaw targetWindowEvents
        afterPrefix afterWindow)
    (targetSuffix :
      CanonicalKirbyTrace.Trace targetRaw targetSuffixEvents
        afterWindow final)
    (prefixIsotopy :
      GeneratedIsotopy
        (ComponentRibbonDiagram.Trace.componentDiagram sourcePrefix)
        (ComponentRibbonDiagram.Trace.componentDiagram targetPrefix))
    (windowIsotopy :
      GeneratedIsotopy
        (ComponentRibbonDiagram.Trace.componentDiagram sourceWindow)
        (ComponentRibbonDiagram.Trace.componentDiagram targetWindow))
    (suffixIsotopy :
      GeneratedIsotopy
        (ComponentRibbonDiagram.Trace.componentDiagram sourceSuffix)
        (ComponentRibbonDiagram.Trace.componentDiagram targetSuffix)) :
    GeneratedIsotopy
      (ComponentRibbonDiagram.Trace.componentDiagram
        ((sourcePrefix.append sourceWindow).append sourceSuffix))
      (ComponentRibbonDiagram.Trace.componentDiagram
        ((targetPrefix.append targetWindow).append targetSuffix)) := by
  exact
    .trans
      (componentDiagram_append
        (sourcePrefix.append sourceWindow) sourceSuffix)
      (.trans
        (.inContext
          (.compRight
            (ComponentRibbonDiagram.Trace.componentDiagram sourceSuffix))
          (componentDiagram_append sourcePrefix sourceWindow))
        (.trans
          (verticalTriple prefixIsotopy windowIsotopy suffixIsotopy)
          (.trans
            (.inContext
              (.compRight
                (ComponentRibbonDiagram.Trace.componentDiagram targetSuffix))
              (componentDiagram_append targetPrefix targetWindow).symm)
            (componentDiagram_append
              (targetPrefix.append targetWindow) targetSuffix).symm)))

/-- Soundness of the complete category-neutral framed-isotopy proof term. -/
theorem eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (labelOf : String → S)
    {source target : ComponentBoundary}
    {before after : ComponentDiagram source target}
    (isotopy : GeneratedIsotopy before after) :
    Diagram.eval C (before.interpret 𝒞.premodular labelOf) =
      Diagram.eval C (after.interpret 𝒞.premodular labelOf) := by
  induction isotopy with
  | refl =>
      rfl
  | step move =>
      exact move.eval_eq 𝒞 labelOf
  | symm _ inductionHypothesis =>
      exact inductionHypothesis.symm
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound
  | inContext context isotopy inductionHypothesis =>
      rw [ComponentDiagram.Context.interpret_plug,
        ComponentDiagram.Context.interpret_plug]
      exact CategoricalTangle.Context.eval_plug_congr C
        (context.interpret 𝒞.premodular labelOf)
        inductionHypothesis

end GeneratedIsotopy

end TwistedYetter.Kirby.ComponentRibbonIsotopy
