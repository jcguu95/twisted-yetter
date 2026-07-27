import TwistedYetter.Kirby.RoleAwareSameComponentTransport
import TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
import TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints
import TwistedYetter.Kirby.SelectedCoordinateFiniteSum
import TwistedYetter.Kirby.TwoOverTwoFusionChannel

/-!
# A role-aware exterior for the premodular 2/2 band movie

The only literature input in this file is the open Bärenz--Barrett band
movie for an arbitrary endomorphism of the exposed two-strand object.  The
input does not mention a tensor-identity automorphism, component exponents,
Kirby weights, or a closed evaluator value.
-/

namespace TwistedYetter.Kirby.RoleAwareTwoOverTwoBandMovie

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonIsotopy
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.LinearContext
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareSameComponentTransport
open TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.TwoOverTwoFusionChannel

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance roleAwareTwoOverTwoRightRigid : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/-
The two exposed ordinary strands of the role-aware 2/2 band movie.

Unlike the legacy boundary, this definition reads the component IDs and
orientation from the same structural binding that supplies the ordinary-role
proofs and finite-sum coordinates below.
-/
def roleAwareLocalBoundary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (_countsSound : source.topology.counts = target.topology.counts) :
    ComponentBoundary :=
  let binding := metadata.recipe.twoOverTwoStructuralBinding
  .tensor
    (.atom (positiveAtom binding.slidingTwoHandleId))
    (.atom
      (match binding.orientation with
      | .positive => negativeAtom binding.stationaryTwoHandleId
      | .negative => positiveAtom binding.stationaryTwoHandleId))

/--
One shared role-aware exterior exposing the two ordinary strands of a 2/2
slide.  This is free diagram syntax only.
-/
structure Window
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) where
  sourceGeometry : Geometry source
  targetGeometry : Geometry target
  exterior :
    RoleAwareDiagram.Context
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
      .unit .unit
  sourceLocal :
    ComponentRibbonDiagram.ComponentDiagram.Context
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
  targetLocal :
    ComponentRibbonDiagram.ComponentDiagram.Context
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
      (roleAwareLocalBoundary metadata countsSound)
  source_factorization :
    sourceGeometry.cutDiagram =
      exterior.plug
        ((RoleAwareDiagram.Context.ordinary sourceLocal).plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (roleAwareLocalBoundary metadata countsSound))))
  target_factorization :
    targetGeometry.cutDiagram =
      exterior.plug
        ((RoleAwareDiagram.Context.ordinary targetLocal).plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (roleAwareLocalBoundary metadata countsSound))))

namespace Window

/-- Interpret only the shared role-aware exterior with a source labeling. -/
noncomputable def sourceExteriorContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labeling : CanonicalPresentation.OrdinaryLabeling (S := S) source) :=
  window.exterior.interpret 𝒞 η
    (CanonicalPresentation.roleAwareLabelOf 𝒞 source labeling)

/-- Interpret the same exterior with a transported target labeling. -/
noncomputable def targetExteriorContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labeling : CanonicalPresentation.OrdinaryLabeling (S := S) target) :=
  window.exterior.interpret 𝒞 η
    (CanonicalPresentation.roleAwareLabelOf 𝒞 target labeling)

/--
The exact categorical source context obtained by interpreting the shared
role-aware exterior and the source local band context.

The hole is the interpreted two-strand local boundary.  Dotted cuts and all
other exterior character coupons remain in the outer context.
-/
noncomputable def sourceTermContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labeling : CanonicalPresentation.OrdinaryLabeling (S := S) source) :=
  let labelOf :=
    CanonicalPresentation.roleAwareLabelOf 𝒞 source labeling
  CategoricalTangle.Context.compose
    ((RoleAwareDiagram.Context.ordinary window.sourceLocal).interpret
      𝒞 η labelOf)
    (window.sourceExteriorContext 𝒞 η labeling)

/--
The exact categorical target context obtained from the same role-aware
exterior and the target local band context.
-/
noncomputable def targetTermContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labeling : CanonicalPresentation.OrdinaryLabeling (S := S) target) :=
  let labelOf :=
    CanonicalPresentation.roleAwareLabelOf 𝒞 target labeling
  CategoricalTangle.Context.compose
    ((RoleAwareDiagram.Context.ordinary window.targetLocal).interpret
      𝒞 η labelOf)
    (window.targetExteriorContext 𝒞 η labeling)

/--
The source evaluator term is definitionally bound to the exact source band
context selected by the role-aware topology window.
-/
theorem sourceTermDiagram_eq_plug_identity
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labeling : CanonicalPresentation.OrdinaryLabeling (S := S) source) :
    CanonicalPresentation.roleAwareTermDiagram
        𝒞 η source window.sourceGeometry labeling =
      CategoricalTangle.Context.plug C
        (window.sourceTermContext 𝒞 η labeling)
        (CategoricalTangle.Diagram.identity
          ((roleAwareLocalBoundary metadata countsSound).interpret 𝒞
            (CanonicalPresentation.roleAwareLabelOf
              𝒞 source labeling))) := by
  unfold CanonicalPresentation.roleAwareTermDiagram sourceTermContext
  rw [window.source_factorization]
  rw [RoleAwareDiagram.Context.interpret_plug]
  rw [RoleAwareDiagram.Context.interpret_plug]
  rfl

/--
The target evaluator term is bound to the exact target band context selected
by the same source-bound move recipe.
-/
theorem targetTermDiagram_eq_plug_identity
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (labeling : CanonicalPresentation.OrdinaryLabeling (S := S) target) :
    CanonicalPresentation.roleAwareTermDiagram
        𝒞 η target window.targetGeometry labeling =
      CategoricalTangle.Context.plug C
        (window.targetTermContext 𝒞 η labeling)
        (CategoricalTangle.Diagram.identity
          ((roleAwareLocalBoundary metadata countsSound).interpret 𝒞
            (CanonicalPresentation.roleAwareLabelOf
              𝒞 target labeling))) := by
  unfold CanonicalPresentation.roleAwareTermDiagram targetTermContext
  rw [window.target_factorization]
  rw [RoleAwareDiagram.Context.interpret_plug]
  rw [RoleAwareDiagram.Context.interpret_plug]
  rfl

end Window

/--
A role-aware 2/2 window whose source and target are pinned to the clean
attach--transport--detach script stored by the admitted recipe.

This wrapper is still category-neutral.  It records no labels, character,
fusion channels, evaluator values, or scalar equalities.  In particular, it
does not solve the separate categorical endpoint-interpretation obligation.
-/
structure CleanWindow
    {H2 : Type uH} [AddCommGroup H2]
    (source target : CanonicalPresentation H2)
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts) where
  window : Window source target metadata countsSound
  source_events_sound :
    metadata.recipe.window.sourceEventWindow =
      metadata.recipe.twoOverTwoCleanScript.sourceEvents
  target_events_sound :
    metadata.recipe.window.targetEventWindow =
      metadata.recipe.twoOverTwoCleanScript.targetEvents
  endpoints_match_window :
    metadata.recipe.twoOverTwoCleanScript.EndpointsMatchWindow
      metadata.recipe.window
  attach_source_declared :
    metadata.recipe.twoOverTwoCleanScript.attach.sourceSlice ∈
      source.topology.formal.raw.declaredSlices
  attach_target_declared :
    metadata.recipe.twoOverTwoCleanScript.attach.targetSlice ∈
      target.topology.formal.raw.declaredSlices
  detach_source_declared :
    metadata.recipe.twoOverTwoCleanScript.detach.sourceSlice ∈
      source.topology.formal.raw.declaredSlices
  detach_target_declared :
    metadata.recipe.twoOverTwoCleanScript.detach.targetSlice ∈
      target.topology.formal.raw.declaredSlices

namespace CleanWindow

/--
Compile the clean-window certificate already checked by the source recipe.
No caller may substitute a second script or a second source/target window.
-/
def ofWindow
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound) :
    CleanWindow source target metadata countsSound := by
  let sound := metadata.recipe.twoOverTwoCleanScript_matchesWindow
  have facts :
      metadata.recipe.window.sourceEventWindow =
          metadata.recipe.twoOverTwoCleanScript.sourceEvents ∧
        metadata.recipe.window.targetEventWindow =
          metadata.recipe.twoOverTwoCleanScript.targetEvents ∧
        metadata.recipe.twoOverTwoCleanScript.EndpointsMatchWindow
            metadata.recipe.window ∧
        metadata.recipe.twoOverTwoCleanScript.attach.sourceSlice ∈
          source.topology.formal.raw.declaredSlices ∧
        metadata.recipe.twoOverTwoCleanScript.attach.targetSlice ∈
          target.topology.formal.raw.declaredSlices ∧
        metadata.recipe.twoOverTwoCleanScript.detach.sourceSlice ∈
          source.topology.formal.raw.declaredSlices ∧
        metadata.recipe.twoOverTwoCleanScript.detach.targetSlice ∈
          target.topology.formal.raw.declaredSlices := by
    simpa [SourceBoundRecipe.twoOverTwoCleanScript] using
      GraphicalEditProgram.twoOverTwo_matchesWindow
        metadata.recipe.handleEdit metadata.recipe.graphicalProgram
        metadata.recipe.window sound
  exact
    { window := window
      source_events_sound := facts.1
      target_events_sound := facts.2.1
      endpoints_match_window := facts.2.2.1
      attach_source_declared := facts.2.2.2.1
      attach_target_declared := facts.2.2.2.2.1
      detach_source_declared := facts.2.2.2.2.2.1
      detach_target_declared := facts.2.2.2.2.2.2 }

/-- The exact clean script selected by this window's source-bound recipe. -/
def script
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (_clean : CleanWindow source target metadata countsSound) :=
  metadata.recipe.twoOverTwoCleanScript

/--
The source replacement window is exactly the script's transport region.
Clean attach and detach collars contain no serialized events.
-/
theorem sourceEventWindow_eq_transportEvents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    metadata.recipe.window.sourceEventWindow =
      clean.script.sourceTransportEvents := by
  rw [clean.source_events_sound]
  unfold CleanBandSlideScript.sourceEvents
  have attachClean :
      metadata.recipe.twoOverTwoCleanScript.attach.sourceCollarEvents = [] := by
    simpa only [script] using
      clean.script.attach.source_collar_clean
  have detachClean :
      metadata.recipe.twoOverTwoCleanScript.detach.sourceCollarEvents = [] := by
    simpa only [script] using
      clean.script.detach.source_collar_clean
  rw [attachClean, detachClean]
  simpa only [List.nil_append, List.append_nil, script]

/--
The target replacement window is exactly the script's transport region.
Clean attach and detach collars contain no serialized events.
-/
theorem targetEventWindow_eq_transportEvents
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    metadata.recipe.window.targetEventWindow =
      clean.script.targetTransportEvents := by
  rw [clean.target_events_sound]
  unfold CleanBandSlideScript.targetEvents
  have attachClean :
      metadata.recipe.twoOverTwoCleanScript.attach.targetCollarEvents = [] := by
    simpa only [script] using
      clean.script.attach.target_collar_clean
  have detachClean :
      metadata.recipe.twoOverTwoCleanScript.detach.targetCollarEvents = [] := by
    simpa only [script] using
      clean.script.detach.target_collar_clean
  rw [attachClean, detachClean]
  simpa only [List.nil_append, List.append_nil, script]

/--
Compute the unique typed prefix/window/suffix split from the admitted source
and target traces and the recipe-owned event window.  A caller cannot provide
a second replay.
-/
def traceWindow
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (_clean : CleanWindow source target metadata countsSound) :
    CanonicalMoveGeometry.SourceBoundTraceWindow
      source target metadata.recipe.window :=
  CanonicalMoveGeometry.SourceBoundTraceWindow.ofPresentationWindow
    source target metadata.recipe.window

/-- The source attach slice is the actual state at the local window entrance. -/
theorem attach_source_activeStrands
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    clean.script.attach.sourceSlice.activeStrands =
      clean.traceWindow.sourceSplit.afterPrefix := by
  let expected : Presentation.DeclaredSlice :=
    { index := metadata.recipe.window.commonEventPrefix.length
      activeStrands := clean.traceWindow.sourceSplit.afterPrefix }
  have generatedMember :
      expected ∈
        Presentation.RawPresentation.declareSlicesFrom 0
          clean.traceWindow.sourceSplit.wholeTrace.toExecutionTrace.states := by
    rw [← clean.traceWindow.sourceSplit.reassembles]
    simpa [expected] using
      CanonicalKirbyTrace.Trace.boundary_slice_mem_declareSlicesFrom_append_append
          0
          clean.traceWindow.sourceSplit.prefixTrace
          clean.traceWindow.sourceSplit.windowTrace
          clean.traceWindow.sourceSplit.suffixTrace
  have attachGenerated := clean.attach_source_declared
  rw [clean.traceWindow.source_declared_slices_sound] at attachGenerated
  have sameSlice :
      clean.script.attach.sourceSlice = expected := by
    apply
      Presentation.RawPresentation.eq_of_mem_declareSlicesFrom_of_index_eq
        attachGenerated generatedMember
    simpa [expected] using clean.endpoints_match_window.1
  exact congrArg Presentation.DeclaredSlice.activeStrands sameSlice

/-- The target attach slice is the actual state at the local window entrance. -/
theorem attach_target_activeStrands
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    clean.script.attach.targetSlice.activeStrands =
      clean.traceWindow.targetSplit.afterPrefix := by
  let expected : Presentation.DeclaredSlice :=
    { index := metadata.recipe.window.commonEventPrefix.length
      activeStrands := clean.traceWindow.targetSplit.afterPrefix }
  have generatedMember :
      expected ∈
        Presentation.RawPresentation.declareSlicesFrom 0
          clean.traceWindow.targetSplit.wholeTrace.toExecutionTrace.states := by
    rw [← clean.traceWindow.targetSplit.reassembles]
    simpa [expected] using
      CanonicalKirbyTrace.Trace.boundary_slice_mem_declareSlicesFrom_append_append
          0
          clean.traceWindow.targetSplit.prefixTrace
          clean.traceWindow.targetSplit.windowTrace
          clean.traceWindow.targetSplit.suffixTrace
  have attachGenerated := clean.attach_target_declared
  rw [clean.traceWindow.target_declared_slices_sound] at attachGenerated
  have sameSlice :
      clean.script.attach.targetSlice = expected := by
    apply
      Presentation.RawPresentation.eq_of_mem_declareSlicesFrom_of_index_eq
        attachGenerated generatedMember
    simpa [expected] using clean.endpoints_match_window.2.1
  exact congrArg Presentation.DeclaredSlice.activeStrands sameSlice

/-- The source detach slice is the actual state at the local window exit. -/
theorem detach_source_activeStrands
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    clean.script.detach.sourceSlice.activeStrands =
      clean.traceWindow.sourceSplit.afterWindow := by
  let expected : Presentation.DeclaredSlice :=
    { index :=
        (metadata.recipe.window.commonEventPrefix ++
          metadata.recipe.window.sourceEventWindow).length
      activeStrands := clean.traceWindow.sourceSplit.afterWindow }
  have generatedMember :
      expected ∈
        Presentation.RawPresentation.declareSlicesFrom 0
          clean.traceWindow.sourceSplit.wholeTrace.toExecutionTrace.states := by
    rw [← clean.traceWindow.sourceSplit.reassembles]
    simpa [expected] using
      CanonicalKirbyTrace.Trace.boundary_slice_mem_declareSlicesFrom_append
        0
        (clean.traceWindow.sourceSplit.prefixTrace.append
          clean.traceWindow.sourceSplit.windowTrace)
        clean.traceWindow.sourceSplit.suffixTrace
  have detachGenerated := clean.detach_source_declared
  rw [clean.traceWindow.source_declared_slices_sound] at detachGenerated
  have sameSlice :
      clean.script.detach.sourceSlice = expected := by
    apply
      Presentation.RawPresentation.eq_of_mem_declareSlicesFrom_of_index_eq
        detachGenerated generatedMember
    simpa [expected] using clean.endpoints_match_window.2.2.1
  exact congrArg Presentation.DeclaredSlice.activeStrands sameSlice

/-- The target detach slice is the actual state at the local window exit. -/
theorem detach_target_activeStrands
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    clean.script.detach.targetSlice.activeStrands =
      clean.traceWindow.targetSplit.afterWindow := by
  let expected : Presentation.DeclaredSlice :=
    { index :=
        (metadata.recipe.window.commonEventPrefix ++
          metadata.recipe.window.targetEventWindow).length
      activeStrands := clean.traceWindow.targetSplit.afterWindow }
  have generatedMember :
      expected ∈
        Presentation.RawPresentation.declareSlicesFrom 0
          clean.traceWindow.targetSplit.wholeTrace.toExecutionTrace.states := by
    rw [← clean.traceWindow.targetSplit.reassembles]
    simpa [expected] using
      CanonicalKirbyTrace.Trace.boundary_slice_mem_declareSlicesFrom_append
        0
        (clean.traceWindow.targetSplit.prefixTrace.append
          clean.traceWindow.targetSplit.windowTrace)
        clean.traceWindow.targetSplit.suffixTrace
  have detachGenerated := clean.detach_target_declared
  rw [clean.traceWindow.target_declared_slices_sound] at detachGenerated
  have sameSlice :
      clean.script.detach.targetSlice = expected := by
    apply
      Presentation.RawPresentation.eq_of_mem_declareSlicesFrom_of_index_eq
        detachGenerated generatedMember
    simpa [expected] using clean.endpoints_match_window.2.2.2
  exact congrArg Presentation.DeclaredSlice.activeStrands sameSlice

/--
The admitted source diagram is generated-isotopic to the exact typed
prefix--clean-window--suffix split selected by the source-bound recipe.
-/
theorem source_componentTermDiagram_split
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    GeneratedIsotopy
      source.componentTermDiagram
      ((ComponentRibbonDiagram.Trace.componentDiagram
            clean.traceWindow.sourceSplit.prefixTrace ≫ᶜ
          ComponentRibbonDiagram.Trace.componentDiagram
            clean.traceWindow.sourceSplit.windowTrace) ≫ᶜ
        ComponentRibbonDiagram.Trace.componentDiagram
          clean.traceWindow.sourceSplit.suffixTrace) := by
  rw [← clean.traceWindow.source_whole_diagram_sound]
  exact
    GeneratedIsotopy.componentDiagram_splitThree
      metadata.recipe.window.commonEventPrefix
      metadata.recipe.window.sourceEventWindow
      metadata.recipe.window.commonEventSuffix
      clean.traceWindow.sourceSplit

/--
The admitted target diagram has the corresponding exact typed
prefix--clean-window--suffix split, with the same recipe-owned exterior event
lists.
-/
theorem target_componentTermDiagram_split
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound) :
    GeneratedIsotopy
      target.componentTermDiagram
      ((ComponentRibbonDiagram.Trace.componentDiagram
            clean.traceWindow.targetSplit.prefixTrace ≫ᶜ
          ComponentRibbonDiagram.Trace.componentDiagram
            clean.traceWindow.targetSplit.windowTrace) ≫ᶜ
        ComponentRibbonDiagram.Trace.componentDiagram
          clean.traceWindow.targetSplit.suffixTrace) := by
  rw [← clean.traceWindow.target_whole_diagram_sound]
  exact
    GeneratedIsotopy.componentDiagram_splitThree
      metadata.recipe.window.commonEventPrefix
      metadata.recipe.window.targetEventWindow
      metadata.recipe.window.commonEventSuffix
      clean.traceWindow.targetSplit

end CleanWindow

namespace Window

/--
The exact category-neutral source-recipe binding underlying this interpreted
2-over-2 window.

This is computed from `metadata.recipe`; callers do not supply a second
binding certificate.  Its orientation, moving/stationary components,
ordinary roles, and literal source/target windows therefore cannot drift
away from the move being evaluated.
-/
def recipeStructuralBinding
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (_window : Window source target metadata countsSound) :
    SourceBoundRecipe.TwoOverTwoStructuralBinding metadata.recipe :=
  metadata.recipe.twoOverTwoStructuralBinding

/-!
The complete role-aware label denominator is split here, before any
categorical band calculation.  Dotted components are absent by construction;
the two visible coordinates are the ordinary moving and stationary
two-handles selected by the source recipe.
-/
namespace RoleAwareFiniteSumBlocks

/-- The moving two-handle as an index of the role-aware label denominator. -/
def movingSourceIndex
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound) :
    CanonicalPresentation.OrdinaryComponentIndex source :=
  ⟨window.recipeStructuralBinding.components.slidingSourceIndex,
    window.recipeStructuralBinding.sliding_role_sound⟩

/-- The stationary two-handle as an index of the role-aware label denominator. -/
def stationarySourceIndex
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound) :
    CanonicalPresentation.OrdinaryComponentIndex source :=
  ⟨window.recipeStructuralBinding.components.stationarySourceIndex,
    window.recipeStructuralBinding.stationary_role_sound⟩

/-- The recipe proves that the two selected ordinary coordinates are distinct. -/
theorem sourceIndicesDistinct
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound) :
    movingSourceIndex window ≠ stationarySourceIndex window := by
  intro equal
  apply window.recipeStructuralBinding.components.source_indices_distinct
  exact congrArg Subtype.val equal

/-- Labels on every ordinary component except the moving/stationary pair. -/
abbrev Block
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound) :=
  RemainingIndex
      (remainingSelected
        (stationarySourceIndex window)
        (movingSourceIndex window)
        (sourceIndicesDistinct window)) →
    S

/-- Reinsert the moving and stationary labels into one source block. -/
def sourceLabeling
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.OrdinaryLabeling (S := S) source :=
  combineAtTwo
    (stationarySourceIndex window)
    (movingSourceIndex window)
    (sourceIndicesDistinct window)
    stationaryLabel movingLabel remaining

/-- Transport one source block through the exact same-component correspondence. -/
def targetLabeling
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.OrdinaryLabeling (S := S) target :=
  OrdinaryTransport.ordinaryLabelingEquiv
    (Request.twoOverTwo metadata countsSound).sameComponentChange
    (sourceLabeling window remaining movingLabel stationaryLabel)

/-- The source moving component receives exactly the selected moving label. -/
theorem sourceLabelOf_movingComponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.roleAwareLabelOf 𝒞 source
        (sourceLabeling window remaining movingLabel stationaryLabel)
        window.recipeStructuralBinding.slidingTwoHandleId =
      movingLabel := by
  rw [← window.recipeStructuralBinding.components.sliding_source_id_sound]
  unfold componentAt
  change
    CanonicalPresentation.roleAwareLabelOf 𝒞 source
        (sourceLabeling window remaining movingLabel stationaryLabel)
        (source.topology.formal.raw.components.get
          (movingSourceIndex window).1).componentId =
      movingLabel
  rw [CanonicalPresentation.roleAwareLabelOf_ordinary
    𝒞 source
    (sourceLabeling window remaining movingLabel stationaryLabel)
    (movingSourceIndex window)]
  exact combineAtTwo_second
    (stationarySourceIndex window)
    (movingSourceIndex window)
    (sourceIndicesDistinct window)
    stationaryLabel movingLabel remaining

/--
The source stationary component receives exactly the selected stationary
label.
-/
theorem sourceLabelOf_stationaryComponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.roleAwareLabelOf 𝒞 source
        (sourceLabeling window remaining movingLabel stationaryLabel)
        window.recipeStructuralBinding.stationaryTwoHandleId =
      stationaryLabel := by
  rw [← window.recipeStructuralBinding.components.stationary_source_id_sound]
  unfold componentAt
  change
    CanonicalPresentation.roleAwareLabelOf 𝒞 source
        (sourceLabeling window remaining movingLabel stationaryLabel)
        (source.topology.formal.raw.components.get
          (stationarySourceIndex window).1).componentId =
      stationaryLabel
  rw [CanonicalPresentation.roleAwareLabelOf_ordinary
    𝒞 source
    (sourceLabeling window remaining movingLabel stationaryLabel)
    (stationarySourceIndex window)]
  exact combineAtTwo_first
    (stationarySourceIndex window)
    (movingSourceIndex window)
    (sourceIndicesDistinct window)
    stationaryLabel movingLabel remaining

/--
The transported target labeling selects exactly the same role-aware simple
object at every stable component ID.  Dotted IDs remain forced to the tensor
unit on both sides.
-/
theorem targetLabelOf_eq_sourceLabelOf
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S)
    (componentId : String) :
    CanonicalPresentation.roleAwareLabelOf 𝒞 target
        (targetLabeling window remaining movingLabel stationaryLabel)
        componentId =
      CanonicalPresentation.roleAwareLabelOf 𝒞 source
        (sourceLabeling window remaining movingLabel stationaryLabel)
        componentId := by
  exact RoleAwareSameComponentTransport.roleAwareLabelOf_transport
    𝒞 source target
    (Request.twoOverTwo metadata countsSound).sameComponentChange
    (sourceLabeling window remaining movingLabel stationaryLabel)
    componentId

/-- The transported target moving component retains the moving label. -/
theorem targetLabelOf_movingComponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.roleAwareLabelOf 𝒞 target
        (targetLabeling window remaining movingLabel stationaryLabel)
        window.recipeStructuralBinding.slidingTwoHandleId =
      movingLabel := by
  rw [targetLabelOf_eq_sourceLabelOf
    window 𝒞 remaining movingLabel stationaryLabel]
  exact sourceLabelOf_movingComponent
    window 𝒞 remaining movingLabel stationaryLabel

/-- The transported target stationary component retains the stationary label. -/
theorem targetLabelOf_stationaryComponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.roleAwareLabelOf 𝒞 target
        (targetLabeling window remaining movingLabel stationaryLabel)
        window.recipeStructuralBinding.stationaryTwoHandleId =
      stationaryLabel := by
  rw [targetLabelOf_eq_sourceLabelOf
    window 𝒞 remaining movingLabel stationaryLabel]
  exact sourceLabelOf_stationaryComponent
    window 𝒞 remaining movingLabel stationaryLabel

/-- In positive orientation the exact source hole is `x tensor y-dual`. -/
theorem sourceLocalBoundary_interpret_positive
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (orientationSound :
      window.recipeStructuralBinding.orientation = .positive)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    (roleAwareLocalBoundary metadata countsSound).interpret 𝒞
        (CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom ((𝒞.simple stationaryLabel)ᘁ)) := by
  change
    metadata.recipe.twoOverTwoStructuralBinding.orientation = .positive
      at orientationSound
  have movingSound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.slidingTwoHandleId =
        movingLabel := by
    simpa [Window.recipeStructuralBinding] using
      sourceLabelOf_movingComponent
        window 𝒞 remaining movingLabel stationaryLabel
  have stationarySound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.stationaryTwoHandleId =
        stationaryLabel := by
    simpa [Window.recipeStructuralBinding] using
      sourceLabelOf_stationaryComponent
        window 𝒞 remaining movingLabel stationaryLabel
  simp only [roleAwareLocalBoundary, orientationSound,
    ComponentBoundary.interpret, ComponentAtom.interpret,
    positiveAtom, negativeAtom]
  rw [movingSound, stationarySound]

/-- In negative orientation the exact source hole is `x tensor y`. -/
theorem sourceLocalBoundary_interpret_negative
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (orientationSound :
      window.recipeStructuralBinding.orientation = .negative)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    (roleAwareLocalBoundary metadata countsSound).interpret 𝒞
        (CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom (𝒞.simple stationaryLabel)) := by
  change
    metadata.recipe.twoOverTwoStructuralBinding.orientation = .negative
      at orientationSound
  have movingSound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.slidingTwoHandleId =
        movingLabel := by
    simpa [Window.recipeStructuralBinding] using
      sourceLabelOf_movingComponent
        window 𝒞 remaining movingLabel stationaryLabel
  have stationarySound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.stationaryTwoHandleId =
        stationaryLabel := by
    simpa [Window.recipeStructuralBinding] using
      sourceLabelOf_stationaryComponent
        window 𝒞 remaining movingLabel stationaryLabel
  simp only [roleAwareLocalBoundary, orientationSound,
    ComponentBoundary.interpret, ComponentAtom.interpret, positiveAtom]
  rw [movingSound, stationarySound]

/-- In positive orientation the transported target hole is also `x tensor y-dual`. -/
theorem targetLocalBoundary_interpret_positive
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (orientationSound :
      window.recipeStructuralBinding.orientation = .positive)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    (roleAwareLocalBoundary metadata countsSound).interpret 𝒞
        (CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom ((𝒞.simple stationaryLabel)ᘁ)) := by
  change
    metadata.recipe.twoOverTwoStructuralBinding.orientation = .positive
      at orientationSound
  have movingSound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.slidingTwoHandleId =
        movingLabel := by
    simpa [Window.recipeStructuralBinding] using
      targetLabelOf_movingComponent
        window 𝒞 remaining movingLabel stationaryLabel
  have stationarySound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.stationaryTwoHandleId =
        stationaryLabel := by
    simpa [Window.recipeStructuralBinding] using
      targetLabelOf_stationaryComponent
        window 𝒞 remaining movingLabel stationaryLabel
  simp only [roleAwareLocalBoundary, orientationSound,
    ComponentBoundary.interpret, ComponentAtom.interpret,
    positiveAtom, negativeAtom]
  rw [movingSound, stationarySound]

/-- In negative orientation the transported target hole is also `x tensor y`. -/
theorem targetLocalBoundary_interpret_negative
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (orientationSound :
      window.recipeStructuralBinding.orientation = .negative)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    (roleAwareLocalBoundary metadata countsSound).interpret 𝒞
        (CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel)) =
      .tensor
        (.atom (𝒞.simple movingLabel))
        (.atom (𝒞.simple stationaryLabel)) := by
  change
    metadata.recipe.twoOverTwoStructuralBinding.orientation = .negative
      at orientationSound
  have movingSound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.slidingTwoHandleId =
        movingLabel := by
    simpa [Window.recipeStructuralBinding] using
      targetLabelOf_movingComponent
        window 𝒞 remaining movingLabel stationaryLabel
  have stationarySound :
      CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel)
          metadata.recipe.twoOverTwoStructuralBinding.stationaryTwoHandleId =
        stationaryLabel := by
    simpa [Window.recipeStructuralBinding] using
      targetLabelOf_stationaryComponent
        window 𝒞 remaining movingLabel stationaryLabel
  simp only [roleAwareLocalBoundary, orientationSound,
    ComponentBoundary.interpret, ComponentAtom.interpret, positiveAtom]
  rw [movingSound, stationarySound]

/--
Consequently the role-aware exterior is literally common after transport.
`HEq` is used because its typed hole boundary is indexed by the label
function that has just been proved equal.
-/
theorem sourceExteriorContext_heq_targetExteriorContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    HEq
      (window.sourceExteriorContext 𝒞 η
        (sourceLabeling window remaining movingLabel stationaryLabel))
      (window.targetExteriorContext 𝒞 η
        (targetLabeling window remaining movingLabel stationaryLabel)) := by
  have labels :
      CanonicalPresentation.roleAwareLabelOf 𝒞 target
          (targetLabeling window remaining movingLabel stationaryLabel) =
        CanonicalPresentation.roleAwareLabelOf 𝒞 source
          (sourceLabeling window remaining movingLabel stationaryLabel) := by
    funext componentId
    exact targetLabelOf_eq_sourceLabelOf
      window 𝒞 remaining movingLabel stationaryLabel componentId
  unfold Window.sourceExteriorContext Window.targetExteriorContext
  generalize
    CanonicalPresentation.roleAwareLabelOf 𝒞 source
        (sourceLabeling window remaining movingLabel stationaryLabel) =
      sourceLabels at labels ⊢
  generalize
    CanonicalPresentation.roleAwareLabelOf 𝒞 target
        (targetLabeling window remaining movingLabel stationaryLabel) =
      targetLabels at labels ⊢
  cases labels
  rfl

/-- One exact source block, retaining both selected finite label sums. -/
noncomputable def endpointCoefficient
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) : K :=
  CanonicalPresentation.roleAwareGlobalWeight
    𝒞 η source sourceCycle
    (sourceLabeling window remaining movingLabel stationaryLabel)

/--
The target evaluator uses exactly the same coefficient in every
`(movingLabel, stationaryLabel)` sector.

This is the complete character bookkeeping theorem for the role-aware 2/2
move.  It includes both selected component exponents and every unchanged
ordinary component.  No graphical sliding statement is used.
-/
theorem targetWeight_eq_endpointCoefficient
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    CanonicalPresentation.roleAwareGlobalWeight
        𝒞 η target
        ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle)
        (targetLabeling window remaining movingLabel stationaryLabel) =
      endpointCoefficient
        window 𝒞 η sourceCycle remaining movingLabel stationaryLabel := by
  unfold endpointCoefficient targetLabeling
  symm
  exact RoleAwareSameComponentTransport.roleAwareGlobalWeight_transport
    𝒞 η
    (Request.twoOverTwo metadata countsSound).sameComponentChange
    (CanonicalSourceBoundSlideMovie.premodularTwoOverTwoExponentTransport
      metadata countsSound sourceCycle)
    (sourceLabeling window remaining movingLabel stationaryLabel)

/-- The moving-component factor splits from the exact role-aware weight. -/
theorem endpointCoefficient_factor_moving
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    endpointCoefficient
        window 𝒞 η sourceCycle remaining movingLabel stationaryLabel =
      source.cycleComponentWeight 𝒞 η sourceCycle
          (componentAt source.topology.formal
            (movingSourceIndex window).1) movingLabel *
        endpointCoefficient window 𝒞 η sourceCycle remaining
          𝒞.toFusionCategoryData.unitIndex stationaryLabel := by
  classical
  unfold endpointCoefficient
    CanonicalPresentation.roleAwareGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 η sourceCycle
        (source.topology.formal.raw.components.get index.1)
        (sourceLabeling
          window remaining movingLabel stationaryLabel index))
    (movingSourceIndex window)]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 η sourceCycle
        (source.topology.formal.raw.components.get index.1)
        (sourceLabeling window remaining
          𝒞.toFusionCategoryData.unitIndex stationaryLabel index))
    (movingSourceIndex window)]
  simp only [sourceLabeling]
  rw [combineAtTwo_second, combineAtTwo_second]
  have unitWeight :
      source.cycleComponentWeight 𝒞 η sourceCycle
          (source.topology.formal.raw.components.get
            (movingSourceIndex window).1)
          𝒞.toFusionCategoryData.unitIndex = 1 := by
    unfold CanonicalPresentation.cycleComponentWeight
    rw [𝒞.quantumDimension_unit]
    rw [ThamThreeHandleVacuum.automorphismScalarPower_unitIndex]
    simp
  rw [unitWeight]
  simp only [one_mul, componentAt]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg
    (fun label =>
      source.cycleComponentWeight 𝒞 η sourceCycle
        (source.topology.formal.raw.components.get index.1) label)
    (combineAtTwo_eq_of_ne_second
      (stationarySourceIndex window)
      (movingSourceIndex window)
      (sourceIndicesDistinct window)
      stationaryLabel movingLabel
      𝒞.toFusionCategoryData.unitIndex remaining index.property)

/-- The stationary-component factor also splits from the exact weight. -/
theorem endpointCoefficient_factor_stationary
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    endpointCoefficient
        window 𝒞 η sourceCycle remaining movingLabel stationaryLabel =
      source.cycleComponentWeight 𝒞 η sourceCycle
          (componentAt source.topology.formal
            (stationarySourceIndex window).1) stationaryLabel *
        endpointCoefficient window 𝒞 η sourceCycle remaining
          movingLabel 𝒞.toFusionCategoryData.unitIndex := by
  classical
  unfold endpointCoefficient
    CanonicalPresentation.roleAwareGlobalWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 η sourceCycle
        (source.topology.formal.raw.components.get index.1)
        (sourceLabeling
          window remaining movingLabel stationaryLabel index))
    (stationarySourceIndex window)]
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun index =>
      source.cycleComponentWeight 𝒞 η sourceCycle
        (source.topology.formal.raw.components.get index.1)
        (sourceLabeling window remaining movingLabel
          𝒞.toFusionCategoryData.unitIndex index))
    (stationarySourceIndex window)]
  simp only [sourceLabeling]
  rw [combineAtTwo_first, combineAtTwo_first]
  have unitWeight :
      source.cycleComponentWeight 𝒞 η sourceCycle
          (source.topology.formal.raw.components.get
            (stationarySourceIndex window).1)
          𝒞.toFusionCategoryData.unitIndex = 1 := by
    unfold CanonicalPresentation.cycleComponentWeight
    rw [𝒞.quantumDimension_unit]
    rw [ThamThreeHandleVacuum.automorphismScalarPower_unitIndex]
    simp
  rw [unitWeight]
  simp only [one_mul, componentAt]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg
    (fun label =>
      source.cycleComponentWeight 𝒞 η sourceCycle
        (source.topology.formal.raw.components.get index.1) label)
    (combineAtTwo_eq_of_ne_first
      (stationarySourceIndex window)
      (movingSourceIndex window)
      (sourceIndicesDistinct window)
      stationaryLabel 𝒞.toFusionCategoryData.unitIndex movingLabel
      remaining index.property)

/-- Both selected factors split, leaving the literal unit/unit complement. -/
theorem endpointCoefficient_factor_both
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    endpointCoefficient
        window 𝒞 η sourceCycle remaining movingLabel stationaryLabel =
      source.cycleComponentWeight 𝒞 η sourceCycle
          (componentAt source.topology.formal
            (movingSourceIndex window).1) movingLabel *
        source.cycleComponentWeight 𝒞 η sourceCycle
          (componentAt source.topology.formal
            (stationarySourceIndex window).1) stationaryLabel *
        endpointCoefficient window 𝒞 η sourceCycle remaining
          𝒞.toFusionCategoryData.unitIndex
          𝒞.toFusionCategoryData.unitIndex := by
  rw [endpointCoefficient_factor_moving]
  rw [endpointCoefficient_factor_stationary]
  simp only [mul_assoc]

/-- Source-cycle exponent on the moving ordinary component. -/
noncomputable def movingExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  source.cycleComponentExponent sourceCycle
    (componentAt source.topology.formal (movingSourceIndex window).1)

/-- Source-cycle exponent on the stationary ordinary component. -/
noncomputable def stationaryExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  source.cycleComponentExponent sourceCycle
    (componentAt source.topology.formal (stationarySourceIndex window).1)

/--
The exponent carried by the internal fusion channel.

For the positive endpoint the stationary strand is dual, so its exponent
changes sign.  For the negative endpoint both exposed strands are positive.
-/
noncomputable def internalChannelExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  match window.recipeStructuralBinding.orientation with
  | .positive => -(stationaryExponent window sourceCycle)
  | .negative => stationaryExponent window sourceCycle

/-- The actual character scalar attached to an internal simple channel `z`. -/
noncomputable def internalChannelWeight
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (z : S) : K :=
  TwoOverTwoFusionChannel.internalCharacterWeight
    𝒞.premodular η (internalChannelExponent window sourceCycle) z

/--
The residual character exponent carried by the exposed moving strand.

For the positive endpoint the stationary occurrence is dual, so extracting
the common channel coupon changes `a - (-b)` to `a + b`.  For the negative
endpoint it is the ordinary tensor product and the residual is `a - b`.
-/
noncomputable def residualMovingExponent
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle) : ℤ :=
  match window.recipeStructuralBinding.orientation with
  | .positive =>
      movingExponent window sourceCycle + stationaryExponent window sourceCycle
  | .negative =>
      movingExponent window sourceCycle - stationaryExponent window sourceCycle

/--
The common character coupon carried through the internal fusion channel.

At a positive endpoint the stationary strand is dual, hence exponent `-b`
acts by `χ_x^{-b} χ_y^b`.  At a negative endpoint both strands are positive,
hence exponent `b` acts by `χ_x^b χ_y^b`.
-/
noncomputable def channelCharacterScalar
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (movingLabel stationaryLabel : S) : K :=
  let b := stationaryExponent window sourceCycle
  match window.recipeStructuralBinding.orientation with
  | .positive =>
      𝒞.toFusionCategoryData.automorphismScalarPower
          η movingLabel (-b) *
        𝒞.toFusionCategoryData.automorphismScalarPower
          η stationaryLabel b
  | .negative =>
      𝒞.toFusionCategoryData.automorphismScalarPower
          η movingLabel b *
        𝒞.toFusionCategoryData.automorphismScalarPower
          η stationaryLabel b

/--
The outer coefficient after the stationary character coupon has been moved
inside the generalized-sliding channel calculation.

The unit/unit sector is exactly the product of all unchanged component
weights.  The remaining factors are the moving quantum dimension and its
orientation-correct residual character.
-/
noncomputable def movingCoefficient
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel : S) : K :=
  endpointCoefficient window 𝒞 η sourceCycle remaining
      𝒞.toFusionCategoryData.unitIndex
      𝒞.toFusionCategoryData.unitIndex *
    𝒞.quantumDimension movingLabel *
    𝒞.toFusionCategoryData.automorphismScalarPower
      η movingLabel (residualMovingExponent window sourceCycle)

/--
The derived residual coefficient and the visible channel coupon reconstruct
the exact original `(x,y)` coefficient.

This is the scalar heart of the twisted 2/2 bookkeeping.  No band-movie or
graphical equality is used.
-/
theorem endpointCoefficient_eq_movingCoefficient_mul_channel
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    endpointCoefficient
        window 𝒞 η sourceCycle remaining movingLabel stationaryLabel =
      movingCoefficient window 𝒞 η sourceCycle remaining movingLabel *
        𝒞.quantumDimension stationaryLabel *
        channelCharacterScalar
          window 𝒞 η sourceCycle movingLabel stationaryLabel := by
  rw [endpointCoefficient_factor_both]
  unfold CanonicalPresentation.cycleComponentWeight movingCoefficient
    channelCharacterScalar residualMovingExponent movingExponent
    stationaryExponent
  cases orientation :
      window.recipeStructuralBinding.orientation with
  | positive =>
      simp only
      have movingPowers :
          𝒞.premodular.toFusionCategoryData.automorphismScalarPower
                η movingLabel
                  (source.cycleComponentExponent sourceCycle
                      (componentAt source.topology.formal
                        ↑(movingSourceIndex window)) +
                    source.cycleComponentExponent sourceCycle
                      (componentAt source.topology.formal
                        ↑(stationarySourceIndex window))) *
              𝒞.premodular.toFusionCategoryData.automorphismScalarPower
                η movingLabel
                  (-source.cycleComponentExponent sourceCycle
                    (componentAt source.topology.formal
                      ↑(stationarySourceIndex window))) =
            𝒞.premodular.toFusionCategoryData.automorphismScalarPower
              η movingLabel
                (source.cycleComponentExponent sourceCycle
                  (componentAt source.topology.formal
                    ↑(movingSourceIndex window))) := by
        rw [← 𝒞.toFusionCategoryData.automorphismScalarPower_add]
        congr 1
        omega
      rw [← movingPowers]
      ring
  | negative =>
      simp only
      have movingPowers :
          𝒞.premodular.toFusionCategoryData.automorphismScalarPower
                η movingLabel
                  (source.cycleComponentExponent sourceCycle
                      (componentAt source.topology.formal
                        ↑(movingSourceIndex window)) -
                    source.cycleComponentExponent sourceCycle
                      (componentAt source.topology.formal
                        ↑(stationarySourceIndex window))) *
              𝒞.premodular.toFusionCategoryData.automorphismScalarPower
                η movingLabel
                  (source.cycleComponentExponent sourceCycle
                    (componentAt source.topology.formal
                      ↑(stationarySourceIndex window))) =
            𝒞.premodular.toFusionCategoryData.automorphismScalarPower
              η movingLabel
                (source.cycleComponentExponent sourceCycle
                  (componentAt source.topology.formal
                    ↑(movingSourceIndex window))) := by
        rw [← 𝒞.toFusionCategoryData.automorphismScalarPower_add]
        congr 1
        omega
      rw [← movingPowers]
      ring

/--
For a positive clean endpoint, the complete character-bearing fusion-channel
sum is valid inside the exact source presentation context.
-/
theorem positiveChannelSum_in_sourceTermContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw :
      SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (orientationSound :
      window.recipeStructuralBinding.orientation = .positive)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    let labeling :=
      sourceLabeling window remaining movingLabel stationaryLabel
    let objectSound :
        ((roleAwareLocalBoundary metadata countsSound).interpret 𝒞
          (CanonicalPresentation.roleAwareLabelOf
            𝒞 source labeling)).denote =
          OrientedTensorObject 𝒞.premodular movingLabel stationaryLabel :=
      by
        simpa [OrientedTensorObject] using
          congrArg (fun boundary : Boundary C => boundary.denote)
            (sourceLocalBoundary_interpret_positive
              window 𝒞 orientationSound remaining movingLabel stationaryLabel)
    ∑ channel : OrientedChannel
        𝒞.premodular movingLabel stationaryLabel,
      evalContextLinearMap (R := K)
        (window.sourceTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (unequalExponentChannelMorphism
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (-(stationaryExponent window sourceCycle)) channel)) =
      evalContextLinearMap (R := K)
        (window.sourceTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (globalPositiveEndpointCoupon
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (stationaryExponent window sourceCycle))) := by
  dsimp only
  exact sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞.premodular insertionLaw η movingLabel stationaryLabel
    (movingExponent window sourceCycle)
    (-(stationaryExponent window sourceCycle))
    _ (window.sourceTermContext 𝒞 η
      (sourceLabeling window remaining movingLabel stationaryLabel))

/--
For a negative clean endpoint, the independently proved negative
fusion-channel sum is valid inside the exact source presentation context.
-/
theorem negativeChannelSum_in_sourceTermContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw :
      SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (orientationSound :
      window.recipeStructuralBinding.orientation = .negative)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    let labeling :=
      sourceLabeling window remaining movingLabel stationaryLabel
    let objectSound :
        ((roleAwareLocalBoundary metadata countsSound).interpret 𝒞
          (CanonicalPresentation.roleAwareLabelOf
            𝒞 source labeling)).denote =
          NegativeTensorObject 𝒞.premodular movingLabel stationaryLabel :=
      by
        simpa [NegativeTensorObject] using
          congrArg (fun boundary : Boundary C => boundary.denote)
            (sourceLocalBoundary_interpret_negative
              window 𝒞 orientationSound remaining movingLabel stationaryLabel)
    ∑ channel : NegativeChannel
        𝒞.premodular movingLabel stationaryLabel,
      evalContextLinearMap (R := K)
        (window.sourceTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (unequalNegativeChannelMorphism
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (stationaryExponent window sourceCycle) channel)) =
      evalContextLinearMap (R := K)
        (window.sourceTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (negativeCharacterCoupon
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (stationaryExponent window sourceCycle))) := by
  dsimp only
  exact sum_unequalNegativeChannelMorphism_inBoundaryContext
    𝒞.premodular insertionLaw η movingLabel stationaryLabel
    (movingExponent window sourceCycle)
    (stationaryExponent window sourceCycle)
    _ (window.sourceTermContext 𝒞 η
      (sourceLabeling window remaining movingLabel stationaryLabel))

/--
The positive fusion-channel identity also holds in the exact transported
target presentation context.
-/
theorem positiveChannelSum_in_targetTermContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw :
      SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (orientationSound :
      window.recipeStructuralBinding.orientation = .positive)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    let labeling :=
      targetLabeling window remaining movingLabel stationaryLabel
    let objectSound :
        ((roleAwareLocalBoundary metadata countsSound).interpret 𝒞
          (CanonicalPresentation.roleAwareLabelOf
            𝒞 target labeling)).denote =
          OrientedTensorObject 𝒞.premodular movingLabel stationaryLabel :=
      by
        simpa [OrientedTensorObject] using
          congrArg (fun boundary : Boundary C => boundary.denote)
            (targetLocalBoundary_interpret_positive
              window 𝒞 orientationSound remaining movingLabel stationaryLabel)
    ∑ channel : OrientedChannel
        𝒞.premodular movingLabel stationaryLabel,
      evalContextLinearMap (R := K)
        (window.targetTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (unequalExponentChannelMorphism
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (-(stationaryExponent window sourceCycle)) channel)) =
      evalContextLinearMap (R := K)
        (window.targetTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (globalPositiveEndpointCoupon
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (stationaryExponent window sourceCycle))) := by
  dsimp only
  exact sum_unequalExponentChannelMorphism_inBoundaryContext
    𝒞.premodular insertionLaw η movingLabel stationaryLabel
    (movingExponent window sourceCycle)
    (-(stationaryExponent window sourceCycle))
    _ (window.targetTermContext 𝒞 η
      (targetLabeling window remaining movingLabel stationaryLabel))

/--
The negative fusion-channel identity also holds in the exact transported
target presentation context.
-/
theorem negativeChannelSum_in_targetTermContext
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (insertionLaw :
      SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞)
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (orientationSound :
      window.recipeStructuralBinding.orientation = .negative)
    (remaining : Block (S := S) window)
    (movingLabel stationaryLabel : S) :
    let labeling :=
      targetLabeling window remaining movingLabel stationaryLabel
    let objectSound :
        ((roleAwareLocalBoundary metadata countsSound).interpret 𝒞
          (CanonicalPresentation.roleAwareLabelOf
            𝒞 target labeling)).denote =
          NegativeTensorObject 𝒞.premodular movingLabel stationaryLabel :=
      by
        simpa [NegativeTensorObject] using
          congrArg (fun boundary : Boundary C => boundary.denote)
            (targetLocalBoundary_interpret_negative
              window 𝒞 orientationSound remaining movingLabel stationaryLabel)
    ∑ channel : NegativeChannel
        𝒞.premodular movingLabel stationaryLabel,
      evalContextLinearMap (R := K)
        (window.targetTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (unequalNegativeChannelMorphism
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (stationaryExponent window sourceCycle) channel)) =
      evalContextLinearMap (R := K)
        (window.targetTermContext 𝒞 η labeling)
        (transportEndomorphism objectSound
          (negativeCharacterCoupon
            𝒞.premodular η movingLabel stationaryLabel
            (movingExponent window sourceCycle)
            (stationaryExponent window sourceCycle))) := by
  dsimp only
  exact sum_unequalNegativeChannelMorphism_inBoundaryContext
    𝒞.premodular insertionLaw η movingLabel stationaryLabel
    (movingExponent window sourceCycle)
    (stationaryExponent window sourceCycle)
    _ (window.targetTermContext 𝒞 η
      (targetLabeling window remaining movingLabel stationaryLabel))

/-- One exact source block, retaining both selected finite label sums. -/
noncomputable def sourceBlock
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  ∑ movingLabel : S, ∑ stationaryLabel : S,
    endpointCoefficient
        window 𝒞 η sourceCycle remaining movingLabel stationaryLabel •
      LinearDiagram.atom (R := K)
        (CanonicalPresentation.roleAwareTermDiagram
          𝒞 η source window.sourceGeometry
          (sourceLabeling window remaining movingLabel stationaryLabel))

/-- One exact target block indexed by the same source remaining labels. -/
noncomputable def targetBlock
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  let targetCycle :=
    (Request.twoOverTwo metadata countsSound).targetCycle sourceCycle
  ∑ movingLabel : S, ∑ stationaryLabel : S,
    CanonicalPresentation.roleAwareGlobalWeight
        𝒞 η target targetCycle
        (targetLabeling window remaining movingLabel stationaryLabel) •
      LinearDiagram.atom (R := K)
        (CanonicalPresentation.roleAwareTermDiagram
          𝒞 η target window.targetGeometry
          (targetLabeling window remaining movingLabel stationaryLabel))

/--
After the proved handle-chain transport, the target block can be written
with the literal source-indexed coefficient.  The remaining difference
between the two blocks is therefore entirely graphical.
-/
theorem targetBlock_eq_commonCoefficient
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (remaining : Block (S := S) window) :
    targetBlock window 𝒞 η sourceCycle remaining =
      ∑ movingLabel : S, ∑ stationaryLabel : S,
        endpointCoefficient
            window 𝒞 η sourceCycle remaining movingLabel stationaryLabel •
          LinearDiagram.atom (R := K)
            (CanonicalPresentation.roleAwareTermDiagram
              𝒞 η target window.targetGeometry
              (targetLabeling
                window remaining movingLabel stationaryLabel)) := by
  classical
  unfold targetBlock
  apply Finset.sum_congr rfl
  intro movingLabel _
  apply Finset.sum_congr rfl
  intro stationaryLabel _
  rw [targetWeight_eq_endpointCoefficient
    window 𝒞 η sourceCycle remaining movingLabel stationaryLabel]

/-- The source role-aware evaluator is exactly the sum of canonical blocks. -/
theorem sourceDecomposition
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalPresentation.roleAwareLinearDiagram
        𝒞 η source window.sourceGeometry sourceCycle =
      ∑ remaining : Block (S := S) window,
        sourceBlock window 𝒞 η sourceCycle remaining := by
  classical
  unfold CanonicalPresentation.roleAwareLinearDiagram
    LinearDiagram.weightedSum sourceBlock sourceLabeling
  rw [sum_splitAtTwo
    (stationarySourceIndex window)
    (movingSourceIndex window)
    (sourceIndicesDistinct window)]
  rfl

/-- The target role-aware evaluator is the same source-indexed block sum. -/
theorem targetDecomposition
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalPresentation.roleAwareLinearDiagram
        𝒞 η target window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle) =
      ∑ remaining : Block (S := S) window,
        targetBlock window 𝒞 η sourceCycle remaining := by
  classical
  unfold CanonicalPresentation.roleAwareLinearDiagram
    LinearDiagram.weightedSum targetBlock targetLabeling
  rw [← Equiv.sum_comp
    (OrdinaryTransport.ordinaryLabelingEquiv
      (Request.twoOverTwo metadata countsSound).sameComponentChange)
    (fun targetLabeling =>
      CanonicalPresentation.roleAwareGlobalWeight
          𝒞 η target
          ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle)
          targetLabeling •
        LinearDiagram.atom (R := K)
          (CanonicalPresentation.roleAwareTermDiagram
            𝒞 η target window.targetGeometry targetLabeling))]
  rw [sum_splitAtTwo
    (stationarySourceIndex window)
    (movingSourceIndex window)
    (sourceIndicesDistinct window)]
  rfl

end RoleAwareFiniteSumBlocks

/-
These three inputs are category-level literature boundaries.  They do not
mention a Kirby presentation, a clean band script, a homology class, a
character exponent, or an evaluator endpoint.
-/
namespace StandardPremodularBandLaws

/--
Spherical insertion of a complete dual basis.

Reference boundary: Bärenz--Barrett, Lemma 2.37 and equation (2.2.5).
-/
axiom sphericalInsertion
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞

/--
Compatibility of the pivotal trace pairing with the mate operation.

Reference boundary: Bärenz--Barrett, Lemma 3.3, equations
(3.1.3)--(3.1.8).
-/
axiom sphericalMateTrace
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    SphericalMateTraceLaw (K := K) 𝒞.spherical

/--
The label-indexed graphical movie of Bärenz--Barrett Lemmas 3.3--3.4.

This law is quantified over the arbitrary exposed strand used by
`SlidingFamily`.  It does not know the role-aware exterior into which that
movie will later be plugged.
-/
axiom labelIndexedMovies
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S)) :
    LabelIndexedSlidingMovies 𝒞
      (sphericalInsertion 𝒞) (sphericalMateTrace 𝒞)

end StandardPremodularBandLaws

/--
The common role-aware exterior canonically closes the channel-weighted
Bärenz--Barrett calculation.

The stationary label is set to the tensor unit in the exterior because the
stationary Kirby-colour sum is generated inside the weighted sliding fiber.
Positive orientation exposes the dual of the unit; negative orientation
exposes the unit itself.
-/
noncomputable def RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (remaining : RoleAwareFiniteSumBlocks.Block (S := S) window) :
    ChannelWeightedClosedWindow
      (StandardPremodularBandLaws.labelIndexedMovies 𝒞) where
  strand :=
    match window.recipeStructuralBinding.orientation with
    | .positive =>
        (𝒞.simple 𝒞.toFusionCategoryData.unitIndex)ᘁ
    | .negative =>
        𝒞.simple 𝒞.toFusionCategoryData.unitIndex
  closure movingLabel := by
    cases orientation :
        window.recipeStructuralBinding.orientation with
    | positive =>
        let labeling :=
          RoleAwareFiniteSumBlocks.sourceLabeling
            window remaining movingLabel
              𝒞.toFusionCategoryData.unitIndex
        let context := window.sourceExteriorContext 𝒞 η labeling
        have boundarySound :=
          RoleAwareFiniteSumBlocks.sourceLocalBoundary_interpret_positive
            window 𝒞 orientation remaining movingLabel
              𝒞.toFusionCategoryData.unitIndex
        rw [boundarySound] at context
        change
          Context C
            (.tensor (.atom (𝒞.simple movingLabel))
              (.atom ((𝒞.simple 𝒞.toFusionCategoryData.unitIndex)ᘁ)))
            (.tensor (.atom (𝒞.simple movingLabel))
              (.atom ((𝒞.simple 𝒞.toFusionCategoryData.unitIndex)ᘁ)))
            .unit .unit at context
        exact evalContextLinearMap (R := K) context
    | negative =>
        let labeling :=
          RoleAwareFiniteSumBlocks.sourceLabeling
            window remaining movingLabel
              𝒞.toFusionCategoryData.unitIndex
        let context := window.sourceExteriorContext 𝒞 η labeling
        have boundarySound :=
          RoleAwareFiniteSumBlocks.sourceLocalBoundary_interpret_negative
            window 𝒞 orientation remaining movingLabel
              𝒞.toFusionCategoryData.unitIndex
        rw [boundarySound] at context
        change
          Context C
            (.tensor (.atom (𝒞.simple movingLabel))
              (.atom (𝒞.simple 𝒞.toFusionCategoryData.unitIndex)))
            (.tensor (.atom (𝒞.simple movingLabel))
              (.atom (𝒞.simple 𝒞.toFusionCategoryData.unitIndex)))
            .unit .unit at context
        exact evalContextLinearMap (R := K) context

/--
The internal character weight, with the orientation sign fixed by the
role-aware window, survives the full generalized-sliding calculation.

This closes the character-bearing categorical movie.  It does not assert
that the source or target presentation syntax is already one of these two
stages.
-/
theorem RoleAwareFiniteSumBlocks.internalChannelWeight_transport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (movingLabel : S)
    (strand : C) :
    LinearDiagram.eval
        (((StandardPremodularBandLaws.labelIndexedMovies 𝒞).family
            movingLabel).fiber strand
          |>.channelWeightedStage314
            (RoleAwareFiniteSumBlocks.internalChannelWeight
              window 𝒞 η sourceCycle)) =
      LinearDiagram.eval
        (((StandardPremodularBandLaws.labelIndexedMovies 𝒞).family
            movingLabel).fiber strand
          |>.channelWeightedStage318
            (RoleAwareFiniteSumBlocks.internalChannelWeight
              window 𝒞 η sourceCycle)) :=
  TwoOverTwoFusionChannel.internalCharacterWeight_transport
    𝒞.premodular
    (StandardPremodularBandLaws.sphericalInsertion 𝒞)
    (StandardPremodularBandLaws.sphericalMateTrace 𝒞)
    (StandardPremodularBandLaws.labelIndexedMovies 𝒞)
    η movingLabel strand
    (RoleAwareFiniteSumBlocks.internalChannelExponent window sourceCycle)

/--
Exact structural binding of a role-aware 2/2 move to its explicit
finite-sum attach and detach stages.

The two compatibility fields are equalities of retained `LinearDiagram`
syntax.
There is deliberately no field asserting equality after evaluation.
-/
structure FiniteSumBinding
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) where
  Block : Type
  blockFintype : Fintype Block
  sourceBlock :
    Block → LinearDiagram (R := K) (C := C) .unit .unit
  targetBlock :
    Block → LinearDiagram (R := K) (C := C) .unit .unit
  source_decomposition :
    CanonicalPresentation.roleAwareLinearDiagram
        𝒞 η source window.sourceGeometry sourceCycle =
      ∑ block, sourceBlock block
  target_decomposition :
    CanonicalPresentation.roleAwareLinearDiagram
        𝒞 η target window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle) =
      ∑ block, targetBlock block
  weightedWindow :
    Block →
      ChannelWeightedClosedWindow
        (StandardPremodularBandLaws.labelIndexedMovies 𝒞)
  movingCoefficient : Block → S → K
  attach_preserves_evaluation :
    (block : Block) →
      LinearDiagram.eval (sourceBlock block) =
        (weightedWindow block).linearBeforeEval
          (movingCoefficient block)
          (RoleAwareFiniteSumBlocks.internalChannelWeight
            window 𝒞 η sourceCycle)
  detach_preserves_evaluation :
    (block : Block) →
      LinearDiagram.eval (targetBlock block) =
        (weightedWindow block).linearAfterEval
          (movingCoefficient block)
          (RoleAwareFiniteSumBlocks.internalChannelWeight
            window 𝒞 η sourceCycle)

namespace FiniteSumBinding

/--
Every interpreted finite-sum binding exposes the exact source recipe that
selected its local move.  This certificate is computed, not supplied.
-/
def recipeBinding
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    {window : Window source target metadata countsSound}
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {sourceCycle : source.DegreeTwoCycle}
    (_binding : FiniteSumBinding window 𝒞 η sourceCycle) :
    SourceBoundRecipe.TwoOverTwoStructuralBinding metadata.recipe :=
  window.recipeStructuralBinding

/--
The explicit endpoint binding and generalized sliding prove equality of the
two complete role-aware finite sums.
-/
theorem linear_eval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    {window : Window source target metadata countsSound}
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {sourceCycle : source.DegreeTwoCycle}
    (binding : FiniteSumBinding window 𝒞 η sourceCycle) :
    LinearDiagram.eval
        (CanonicalPresentation.roleAwareLinearDiagram
          𝒞 η source window.sourceGeometry sourceCycle) =
    LinearDiagram.eval
        (CanonicalPresentation.roleAwareLinearDiagram
          𝒞 η target window.targetGeometry
            ((Request.twoOverTwo metadata countsSound).targetCycle
              sourceCycle)) := by
  letI := binding.blockFintype
  rw [binding.source_decomposition, binding.target_decomposition]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro block _
  rw [binding.attach_preserves_evaluation block,
    binding.detach_preserves_evaluation block]
  exact (binding.weightedWindow block).linear_eval_eq
    (binding.movingCoefficient block)
    (RoleAwareFiniteSumBlocks.internalChannelWeight
      window 𝒞 η sourceCycle)

/-- The complete finite-sum proof descends to the normalized evaluator. -/
theorem roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    {window : Window source target metadata countsSound}
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {sourceCycle : source.DegreeTwoCycle}
    (binding : FiniteSumBinding window 𝒞 η sourceCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source window.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle) :=
  RoleAwareSameComponentTransport.roleAwareCycleEval_eq_of_linearDiagram_eval_eq
    𝒞 η window.sourceGeometry window.targetGeometry countsSound
    sourceCycle
    ((Request.twoOverTwo metadata countsSound).targetCycle sourceCycle)
    binding.linear_eval_eq

end FiniteSumBinding

/--
The one remaining literature/graphical input for a 2-over-2 block.

It identifies the two exact free-syntax blocks produced above with
Bärenz--Barrett stages (3.1.3) and (3.1.8).  It does not assert equality of
their evaluations.  In particular, the stationary Kirby-colour label and all
fusion channels remain inside `closedWindow`.
-/
structure AttachDetachInterpretation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) where
  attach_preserves_evaluation :
    (block : RoleAwareFiniteSumBlocks.Block (S := S) window) →
      LinearDiagram.eval
          (RoleAwareFiniteSumBlocks.sourceBlock
            window 𝒞 η sourceCycle block) =
        (RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
          window 𝒞 η block).linearBeforeEval
          (RoleAwareFiniteSumBlocks.movingCoefficient
            window 𝒞 η sourceCycle block)
          (RoleAwareFiniteSumBlocks.internalChannelWeight
            window 𝒞 η sourceCycle)
  detach_preserves_evaluation :
    (block : RoleAwareFiniteSumBlocks.Block (S := S) window) →
      LinearDiagram.eval
          (RoleAwareFiniteSumBlocks.targetBlock
            window 𝒞 η sourceCycle block) =
        (RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
          window 𝒞 η block).linearAfterEval
          (RoleAwareFiniteSumBlocks.movingCoefficient
            window 𝒞 η sourceCycle block)
          (RoleAwareFiniteSumBlocks.internalChannelWeight
            window 𝒞 η sourceCycle)

namespace AttachDetachInterpretation

/-- Assemble the exact whole-sum binding from the recipe-derived blocks. -/
noncomputable def toFiniteSumBinding
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    {window : Window source target metadata countsSound}
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {sourceCycle : source.DegreeTwoCycle}
    (interpretation :
      AttachDetachInterpretation window 𝒞 η sourceCycle) :
    FiniteSumBinding window 𝒞 η sourceCycle where
  Block := RoleAwareFiniteSumBlocks.Block (S := S) window
  blockFintype := inferInstance
  sourceBlock :=
    RoleAwareFiniteSumBlocks.sourceBlock window 𝒞 η sourceCycle
  targetBlock :=
    RoleAwareFiniteSumBlocks.targetBlock window 𝒞 η sourceCycle
  source_decomposition :=
    RoleAwareFiniteSumBlocks.sourceDecomposition window 𝒞 η sourceCycle
  target_decomposition :=
    RoleAwareFiniteSumBlocks.targetDecomposition window 𝒞 η sourceCycle
  weightedWindow :=
    RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow window 𝒞 η
  movingCoefficient :=
    RoleAwareFiniteSumBlocks.movingCoefficient window 𝒞 η sourceCycle
  attach_preserves_evaluation := interpretation.attach_preserves_evaluation
  detach_preserves_evaluation := interpretation.detach_preserves_evaluation

/--
The standard endpoint interpretation and the kernel-checked generalized
sliding calculation prove the complete normalized role-aware equality.
-/
theorem roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    {window : Window source target metadata countsSound}
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {sourceCycle : source.DegreeTwoCycle}
    (interpretation :
      AttachDetachInterpretation window 𝒞 η sourceCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source window.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle) :=
  interpretation.toFiniteSumBinding.roleAwareCycleEval_eq

end AttachDetachInterpretation

end Window

/--
The one intentionally unfilled proof obligation left after deleting the broad
endpoint axiom.

A value must be constructed from the clean source/target syntax and the
listed categorical sliding laws.  Merely possessing a clean topology window
does not manufacture this value.
-/
abbrev StandardAttachDetachObligation
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology}
    {countsSound : source.topology.counts = target.topology.counts}
    (clean : CleanWindow source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :=
  Window.AttachDetachInterpretation clean.window 𝒞 η sourceCycle

/-
The two still-unproved attach and detach obligations, exposed as separate
fields.

This is deliberately not a single
`resolve : ... → AttachDetachInterpretation`
black box.  A future construction must visibly:

1. prove that attaching the standard fusion resolution preserves the source
   evaluation; and
2. prove that detaching the transported fusion resolution preserves the target
   evaluation.

The weighted window itself is constructed from the exact common exterior.
The two endpoint interpretation boundaries and their derived evaluation
theorems are declared immediately below.  The axioms are pointwise
topology-to-category translations; the evaluation equalities are theorems.
-/
namespace TwoOverTwoAttachDetach

/-
These are the two narrow topology-to-category interpretation boundaries.

They are deliberately pointwise in the moving simple label.  Neither axiom
states that source and target evaluations are equal, and neither mentions the
sliding theorem or the normalized four-manifold invariant.  Each only says
that interpreting the corresponding clean Kirby collar produces the standard
categorical attach/detach stage already constructed above.
-/
namespace CleanEndpointInterpretation

/--
For one fixed moving simple label, interpreting the clean Kirby attaching
collar gives the standard channel-resolved categorical attach stage.

This is an interpreter boundary, not an invariance statement: it identifies
one endpoint with one categorical expression and says nothing about the
target endpoint.
-/
axiom attach_fixedMovingLabel
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (clean : CleanWindow source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle)
    (block : Window.RoleAwareFiniteSumBlocks.Block (S := S) clean.window)
    (movingLabel : S) :
    (∑ stationaryLabel : S,
      Window.RoleAwareFiniteSumBlocks.endpointCoefficient
          clean.window 𝒞 η sourceCycle block movingLabel stationaryLabel •
        Diagram.eval C
          (CanonicalPresentation.roleAwareTermDiagram
            𝒞 η source clean.window.sourceGeometry
            (Window.RoleAwareFiniteSumBlocks.sourceLabeling
              clean.window block movingLabel stationaryLabel))) =
      Window.RoleAwareFiniteSumBlocks.movingCoefficient
          clean.window 𝒞 η sourceCycle block movingLabel •
        (Window.RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
          clean.window 𝒞 η block).beforeEval
          (Window.RoleAwareFiniteSumBlocks.internalChannelWeight
            clean.window 𝒞 η sourceCycle) movingLabel

/--
For one fixed moving simple label, interpreting the clean Kirby detaching
collar gives the standard transported categorical detach stage.

This is again only an endpoint interpretation.  The equality between the
attach and detach stages is the separately proved weighted sliding theorem.
-/
axiom detach_fixedMovingLabel
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (clean : CleanWindow source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle)
    (block : Window.RoleAwareFiniteSumBlocks.Block (S := S) clean.window)
    (movingLabel : S) :
    (∑ stationaryLabel : S,
      Window.RoleAwareFiniteSumBlocks.endpointCoefficient
          clean.window 𝒞 η sourceCycle block movingLabel stationaryLabel •
        Diagram.eval C
          (CanonicalPresentation.roleAwareTermDiagram
            𝒞 η target clean.window.targetGeometry
            (Window.RoleAwareFiniteSumBlocks.targetLabeling
              clean.window block movingLabel stationaryLabel))) =
      Window.RoleAwareFiniteSumBlocks.movingCoefficient
          clean.window 𝒞 η sourceCycle block movingLabel •
        (Window.RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
          clean.window 𝒞 η block).afterEval
          (Window.RoleAwareFiniteSumBlocks.internalChannelWeight
            clean.window 𝒞 η sourceCycle) movingLabel

end CleanEndpointInterpretation

/--
Attaching the standard complete fusion resolution to a clean role-aware
two-over-two source window preserves its evaluation.

The proof expands the complete source block, then applies the pointwise clean
attach interpretation under the outer finite sum.
-/
theorem attach_preserves_evaluation
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2] :
    {source target : CanonicalPresentation H2} →
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology) →
    (countsSound : source.topology.counts = target.topology.counts) →
    (clean : CleanWindow source target metadata countsSound) →
    (sourceCycle : source.DegreeTwoCycle) →
    (block : Window.RoleAwareFiniteSumBlocks.Block (S := S) clean.window) →
      LinearDiagram.eval
          (Window.RoleAwareFiniteSumBlocks.sourceBlock
            clean.window 𝒞 η sourceCycle block) =
        (Window.RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
          clean.window 𝒞 η block).linearBeforeEval
          (Window.RoleAwareFiniteSumBlocks.movingCoefficient
            clean.window 𝒞 η sourceCycle block)
          (Window.RoleAwareFiniteSumBlocks.internalChannelWeight
            clean.window 𝒞 η sourceCycle) := by
  classical
  intro source target metadata countsSound clean sourceCycle block
  unfold Window.RoleAwareFiniteSumBlocks.sourceBlock
  unfold ChannelWeightedClosedWindow.linearBeforeEval
  simp only [map_sum, map_smul, LinearDiagram.eval_atom]
  apply Finset.sum_congr rfl
  intro movingLabel _
  exact CleanEndpointInterpretation.attach_fixedMovingLabel
    𝒞 η metadata countsSound clean sourceCycle block movingLabel

/--
Detaching the transported complete fusion resolution from a clean
role-aware two-over-two target window preserves its evaluation.

The proof first rewrites the transported target coefficient to the exact
source-indexed coefficient, then applies the pointwise clean detach
interpretation under the outer finite sum.
-/
theorem detach_preserves_evaluation
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2] :
    {source target : CanonicalPresentation H2} →
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology) →
    (countsSound : source.topology.counts = target.topology.counts) →
    (clean : CleanWindow source target metadata countsSound) →
    (sourceCycle : source.DegreeTwoCycle) →
    (block : Window.RoleAwareFiniteSumBlocks.Block (S := S) clean.window) →
      LinearDiagram.eval
          (Window.RoleAwareFiniteSumBlocks.targetBlock
            clean.window 𝒞 η sourceCycle block) =
        (Window.RoleAwareFiniteSumBlocks.canonicalChannelWeightedWindow
          clean.window 𝒞 η block).linearAfterEval
          (Window.RoleAwareFiniteSumBlocks.movingCoefficient
            clean.window 𝒞 η sourceCycle block)
          (Window.RoleAwareFiniteSumBlocks.internalChannelWeight
            clean.window 𝒞 η sourceCycle) := by
  classical
  intro source target metadata countsSound clean sourceCycle block
  unfold Window.RoleAwareFiniteSumBlocks.targetBlock
  unfold ChannelWeightedClosedWindow.linearAfterEval
  simp only [map_sum, map_smul, LinearDiagram.eval_atom]
  simp_rw
    [Window.RoleAwareFiniteSumBlocks.targetWeight_eq_endpointCoefficient
      clean.window 𝒞 η sourceCycle]
  apply Finset.sum_congr rfl
  intro movingLabel _
  exact CleanEndpointInterpretation.detach_fixedMovingLabel
    𝒞 η metadata countsSound clean sourceCycle block movingLabel

/--
Assemble the per-window record from the two explicit attach/detach theorems.
This definition adds no further assumption.
-/
noncomputable def resolve
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : PremodularCategory (K := K) (C := C) (S := S)}
    {η : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (clean : CleanWindow source target metadata countsSound)
    (sourceCycle : source.DegreeTwoCycle) :
    StandardAttachDetachObligation clean 𝒞 η sourceCycle where
  attach_preserves_evaluation :=
    attach_preserves_evaluation 𝒞 η
      metadata countsSound clean sourceCycle
  detach_preserves_evaluation :=
    detach_preserves_evaluation 𝒞 η
      metadata countsSound clean sourceCycle

end TwoOverTwoAttachDetach

/--
Once the standard-normal-form endpoint interpretation is supplied, every
remaining step is the kernel-checked finite-sum proof.  This theorem remains
deliberately conditional; there is no global axiom producing the categorical
compiler.
-/
theorem CleanWindow.roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (clean : CleanWindow source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle)
    (endpoint :
      StandardAttachDetachObligation clean 𝒞 η sourceCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source clean.window.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target clean.window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle) :=
  endpoint.roleAwareCycleEval_eq

end TwistedYetter.Kirby.RoleAwareTwoOverTwoBandMovie
