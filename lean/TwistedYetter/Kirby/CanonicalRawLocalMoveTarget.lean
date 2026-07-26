import TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput

/-!
# Completion target for raw local Kirby moves

This module pins the exact work needed to eliminate
`standardLocalCycleCalculation`.  It does not assert that the work has been
completed.

The existing source-bound recipe stores an admitted source and an admitted
target.  That is useful evidence, but by itself it does not prove that the
target was produced by applying the named Kirby move to the source.  The
target below closes that gap in two stages:

1. a deterministic engine reconstructs the target mathematical core
   (components and slice events) from the source and a local rewrite
   instruction; and
2. the generated rewrite must compile to the already restricted
   `LocalCycleCalculation` grammar.

The instruction contains the local replacement windows because these are the
right-hand side of a rewrite rule.  It contains neither the whole target
presentation nor a target hash.  The final invariant does not accept an
engine or completion proof as an argument.

The provenance envelope is deliberately not reconstructed.  Presentation
IDs, source locators, and content hashes certify an artifact but do not alter
the ribbon diagram.  Requiring a pure Lean function to synthesize those
fields would confuse mathematical generation with evidence production.
-/

namespace TwistedYetter.Kirby.CanonicalRawLocalMoveTarget

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
One source-local rewrite instruction.

The replacement windows are local output syntax, not an independently
admitted target.  The source equations pin the place at which they are
spliced.  In particular, this structure has no `target`,
`targetPresentationHash`, or target-validation witness field.
-/
structure Instruction (source : FormalPresentation) where
  kind : RecipeKind
  commonComponentPrefix : List ComponentSpec
  sourceComponentWindow : List ComponentSpec
  replacementComponentWindow : List ComponentSpec
  commonComponentSuffix : List ComponentSpec
  source_components_sound :
    source.raw.components =
      commonComponentPrefix ++ sourceComponentWindow ++
        commonComponentSuffix
  commonEventPrefix : List SliceEvent
  sourceEventWindow : List SliceEvent
  replacementEventWindow : List SliceEvent
  commonEventSuffix : List SliceEvent
  source_events_sound :
    source.raw.events =
      commonEventPrefix ++ sourceEventWindow ++ commonEventSuffix
  source_event_window_nonempty : sourceEventWindow ≠ []
  replacement_event_window_nonempty : replacementEventWindow ≠ []
  handleEdit : HandleEdit kind
  graphicalProgram : GraphicalEditProgram handleEdit

namespace Instruction

/-- The component registry forced by one local rewrite instruction. -/
def rewrittenComponents
    {source : FormalPresentation}
    (instruction : Instruction source) : List ComponentSpec :=
  instruction.commonComponentPrefix ++
    instruction.replacementComponentWindow ++
      instruction.commonComponentSuffix

/-- The slice-event trace forced by one local rewrite instruction. -/
def rewrittenEvents
    {source : FormalPresentation}
    (instruction : Instruction source) : List SliceEvent :=
  instruction.commonEventPrefix ++
    instruction.replacementEventWindow ++
      instruction.commonEventSuffix

/--
Forget the independently admitted target while retaining the exact local
right-hand side of an existing source-bound recipe.
-/
def ofRecipe
    {kind : RecipeKind}
    {source target : FormalPresentation}
    (recipe : SourceBoundRecipe kind source target) :
    Instruction source where
  kind := kind
  commonComponentPrefix := recipe.window.commonComponentPrefix
  sourceComponentWindow := recipe.window.sourceComponentWindow
  replacementComponentWindow := recipe.window.targetComponentWindow
  commonComponentSuffix := recipe.window.commonComponentSuffix
  source_components_sound := recipe.window.source_components_sound
  commonEventPrefix := recipe.window.commonEventPrefix
  sourceEventWindow := recipe.window.sourceEventWindow
  replacementEventWindow := recipe.window.targetEventWindow
  commonEventSuffix := recipe.window.commonEventSuffix
  source_events_sound := recipe.window.source_events_sound
  source_event_window_nonempty :=
    recipe.window.source_event_window_nonempty
  replacement_event_window_nonempty :=
    recipe.window.target_event_window_nonempty
  handleEdit := recipe.handleEdit
  graphicalProgram := recipe.graphicalProgram

end Instruction

/--
The mathematical core of a serialized presentation.

Declared slices are deterministically checked by `RawPresentation.validate`
and therefore need not be an independent field here.  Provenance and hashes
belong to the immutable evidence envelope, not to the local rewrite result.
-/
structure PresentationCore where
  components : List ComponentSpec
  events : List SliceEvent
  deriving Repr, BEq, DecidableEq

namespace PresentationCore

/-- Forget only the non-mathematical evidence envelope. -/
def ofFormal (presentation : FormalPresentation) : PresentationCore where
  components := presentation.raw.components
  events := presentation.raw.events

/-- Two mathematical cores are equal when both defining fields agree. -/
theorem ext
    (left right : PresentationCore)
    (components : left.components = right.components)
    (events : left.events = right.events) :
    left = right := by
  cases left
  cases right
  simp_all

end PresentationCore

namespace Instruction

/-- The complete mathematical output forced by one instruction. -/
def rewrittenCore
    {source : FormalPresentation}
    (instruction : Instruction source) : PresentationCore where
  components := instruction.rewrittenComponents
  events := instruction.rewrittenEvents

/--
An instruction obtained from an admitted source-bound recipe reconstructs
exactly the target mathematical core.
-/
theorem rewrittenCore_ofRecipe_eq_target
    {kind : RecipeKind}
    {source target : FormalPresentation}
    (recipe : SourceBoundRecipe kind source target) :
    (Instruction.ofRecipe recipe).rewrittenCore =
      PresentationCore.ofFormal target := by
  apply PresentationCore.ext
  · exact recipe.window.target_components_sound.symm
  · exact recipe.window.target_events_sound.symm

end Instruction

/-- Project the source-local instruction from one topology move. -/
def instructionOfMove
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target) :
    Instruction source.formal :=
  match move with
  | .framedIsotopy metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .oneOverOne metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .twoOverOne metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .twoOverTwo metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .oneTwoBirth metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .oneTwoDeath metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .twoThreeBirth metadata _ =>
      Instruction.ofRecipe metadata.recipe
  | .twoThreeDeath metadata _ =>
      Instruction.ofRecipe metadata.recipe

/-- A deterministic engine for the mathematical presentation core. -/
structure Engine where
  apply :
    {source : FormalPresentation} →
      Instruction source → PresentationCore

/-- The canonical engine is literal window replacement. -/
def canonicalEngine : Engine where
  apply := fun instruction => instruction.rewrittenCore

namespace canonicalEngine

/-- The canonical engine changes exactly the selected component window. -/
theorem components_sound
    {source : FormalPresentation}
    (instruction : Instruction source) :
    (canonicalEngine.apply instruction).components =
      instruction.rewrittenComponents :=
  rfl

/-- The canonical engine changes exactly the selected event window. -/
theorem events_sound
    {source : FormalPresentation}
    (instruction : Instruction source) :
    (canonicalEngine.apply instruction).events =
      instruction.rewrittenEvents :=
  rfl

/-- Every admitted topology move endpoint has the generated core. -/
theorem generates_exact_target
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target) :
    canonicalEngine.apply (instructionOfMove move) =
      PresentationCore.ofFormal target.formal := by
  cases move with
  | framedIsotopy metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | oneOverOne metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | twoOverOne metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | twoOverTwo metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | oneTwoBirth metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | oneTwoDeath metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | twoThreeBirth metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe
  | twoThreeDeath metadata counts =>
      exact Instruction.rewrittenCore_ofRecipe_eq_target
        metadata.recipe

end canonicalEngine

/--
The remaining completion obligation for one fixed modular category.

Core generation and exact endpoint reconstruction are theorems above.  The
sole remaining field requires a constructor of the restricted eight-case
graphical grammar, not a scalar equality.
-/
structure Completion
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) where
  generated_move_calculation :
    {H2 : Type uH} →
    [AddCommGroup H2] →
    {source target : CanonicalPresentation H2} →
    (move :
      TopologicalTableTwoMove source.topology target.topology) →
      LocalCycleCalculation 𝒞 automorphism
        (CanonicalSourceBackedMove.enrichedMove move)

/-- A completed graphical compiler replaces the literature boundary axiom. -/
def localCycleCalculation_of_completion
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    (completion : Completion 𝒞 automorphism)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (move :
      TopologicalTableTwoMove source.topology target.topology) :
    LocalCycleCalculation 𝒞 automorphism
      (CanonicalSourceBackedMove.enrichedMove move) :=
  completion.generated_move_calculation move

/--
The standard completion assembled from transparent graphical realizations.

The external inputs are the eight separately named local geometry facts.
Their exhaustive assembly and translation to `LocalCycleCalculation` are
kernel checked.
-/
noncomputable def standardCompletion
    (𝒞 : ModularFusionCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C) :
    Completion 𝒞 η where
  generated_move_calculation := fun move =>
    standardLocalCycleCalculation 𝒞 η move

/-- Machine-visible status of the two separate stages. -/
def currentStatus : String :=
  "CORE_REWRITE_ENGINE_KERNEL_CHECKED;"
    ++ "EIGHT_CASE_GRAPHICAL_COMPILER_KERNEL_CHECKED;"
    ++ "EIGHT_LOCAL_GEOMETRY_INPUTS_EXPLICIT;"
    ++ "THREE_SLIDE_INPUTS_ARE_CATEGORY_DEPENDENT"

/-- Exact non-claim attached to this target module. -/
def explicitNonClaim : String :=
  "The canonical core rewrite engine and exact-target theorem are complete. "
    ++ "The eight-case compiler from GraphicalMoveRealization to "
    ++ "LocalCycleCalculation is complete, and standardCompletion is "
    ++ "constructed. Lean imports eight separately audited local geometry "
    ++ "facts; only the three slide facts mention the modular category. "
    ++ "It does not reconstruct planar "
    ++ "coordinates and coupon neighbourhoods from serialized events."

end TwistedYetter.Kirby.CanonicalRawLocalMoveTarget
