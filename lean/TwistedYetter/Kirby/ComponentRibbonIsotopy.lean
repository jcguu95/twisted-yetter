import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.EGNOModularKirbyMoves
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
    (.crossingPositive
        (.atom (positiveAtom componentId))
        (.atom (negativeAtom componentId)) ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    (.capNegativePositive componentId ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    .leftUnitorHom (.atom (positiveAtom componentId))

/-- Negative blackboard kink on a positively oriented component. -/
def negativeKink (componentId : String) :
    ComponentDiagram
      (.atom (positiveAtom componentId))
      (.atom (positiveAtom componentId)) :=
  .leftUnitorInv (.atom (positiveAtom componentId)) ≫ᶜ
    (.cupPositiveNegative componentId ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    (.crossingNegative
        (.atom (positiveAtom componentId))
        (.atom (negativeAtom componentId)) ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    (.capNegativePositive componentId ⊗ᶜ
      .identity (.atom (positiveAtom componentId))) ≫ᶜ
    .leftUnitorHom (.atom (positiveAtom componentId))

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

/-- Every free primitive preserves categorical evaluation after interpretation. -/
theorem eval_eq
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
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
        TwistedYetter.Kirby.PresentationIsotopy.leftUnitorHomDiagram,
        Diagram.eval, Boundary.denote] using
        (shum_ribbonFramedKink 𝒞).positive_sound X
  | framedNegative componentId =>
      let X := 𝒞.premodular.simple (labelOf componentId)
      simpa [FreeTemplates.negativeKink, ComponentDiagram.interpret,
        TwistedYetter.Kirby.PresentationIsotopy.negativeKink,
        TwistedYetter.Kirby.PresentationIsotopy.leftUnitorInvDiagram,
        TwistedYetter.Kirby.PresentationIsotopy.leftUnitorHomDiagram,
        Diagram.eval, Boundary.denote] using
        (shum_ribbonFramedKink 𝒞).negative_sound X
  | eraseIdentityCoupon couponId boundary =>
      simp [ComponentDiagram.interpret, Diagram.eval]

end TaggedMove

namespace GeneratedIsotopy

/-- Soundness of the complete category-neutral framed-isotopy proof term. -/
theorem eval_eq
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
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
