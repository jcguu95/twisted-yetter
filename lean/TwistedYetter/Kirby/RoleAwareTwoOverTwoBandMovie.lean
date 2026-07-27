import TwistedYetter.Kirby.RoleAwareSameComponentTransport
import TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints
import TwistedYetter.Kirby.SelectedCoordinateFiniteSum
import TwistedYetter.Kirby.TwoOverTwoFusionChannel
import TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

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
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.RoleAwareComponentDiagram
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareSameComponentTransport
open TwistedYetter.Kirby.PremodularTwoOverTwoBandEndpoints
open TwistedYetter.Kirby.SelectedCoordinateFiniteSum
open TwistedYetter.Kirby.SimultaneousDottedCutGeometry
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe
open TwistedYetter.Kirby.TwoOverTwoFusionChannel
open TwistedYetter.Kirby.TwoOverTwoSourceFreeFactorization

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

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
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      .unit .unit
  sourceLocal :
    ComponentRibbonDiagram.ComponentDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  targetLocal :
    ComponentRibbonDiagram.ComponentDiagram.Context
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
      (localBoundary metadata countsSound)
  source_factorization :
    sourceGeometry.cutDiagram =
      exterior.plug
        ((RoleAwareDiagram.Context.ordinary sourceLocal).plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (localBoundary metadata countsSound))))
  target_factorization :
    targetGeometry.cutDiagram =
      exterior.plug
        ((RoleAwareDiagram.Context.ordinary targetLocal).plug
          (.ordinary
            (ComponentRibbonDiagram.ComponentDiagram.identity
              (localBoundary metadata countsSound))))

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
    CanonicalPresentation.roleAwareGlobalWeight
        𝒞 η source sourceCycle
        (sourceLabeling window remaining movingLabel stationaryLabel) •
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

/--
Exact structural binding of a role-aware 2/2 move to the explicit
Bärenz--Barrett finite-sum endpoints.

The two endpoint fields are equalities of retained `LinearDiagram` syntax.
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
  insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞
  mateLaw : SphericalMateTraceLaw (K := K) 𝒞.spherical
  movies : LabelIndexedSlidingMovies 𝒞 insertionLaw mateLaw
  closedWindow :
    Block → LabelIndexedSlidingMovies.ClosedWindow movies
  movingCoefficient : Block → S → K
  source_endpoint :
    (block : Block) →
      sourceBlock block =
        linearEndpoint Side.before
          (closedWindow block) (movingCoefficient block)
  target_endpoint :
    (block : Block) →
      targetBlock block =
        linearEndpoint Side.after
          (closedWindow block) (movingCoefficient block)

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
  rw [binding.source_endpoint block, binding.target_endpoint block]
  exact PremodularTwoOverTwoBandEndpoints.linearEndpoint_eval_eq
    (binding.closedWindow block) (binding.movingCoefficient block)

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
structure BandEndpointInterpretation
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
  insertionLaw : SphericalInsertionLaw.{uK, uC, vC, vC} 𝒞
  mateLaw : SphericalMateTraceLaw (K := K) 𝒞.spherical
  movies : LabelIndexedSlidingMovies 𝒞 insertionLaw mateLaw
  closedWindow :
    RoleAwareFiniteSumBlocks.Block (S := S) window →
      LabelIndexedSlidingMovies.ClosedWindow movies
  movingCoefficient :
    RoleAwareFiniteSumBlocks.Block (S := S) window → S → K
  source_endpoint :
    (block : RoleAwareFiniteSumBlocks.Block (S := S) window) →
      RoleAwareFiniteSumBlocks.sourceBlock
          window 𝒞 η sourceCycle block =
        linearEndpoint Side.before
          (closedWindow block) (movingCoefficient block)
  target_endpoint :
    (block : RoleAwareFiniteSumBlocks.Block (S := S) window) →
      RoleAwareFiniteSumBlocks.targetBlock
          window 𝒞 η sourceCycle block =
        linearEndpoint Side.after
          (closedWindow block) (movingCoefficient block)

/--
Bärenz--Barrett Lemmas 3.3--3.4 identify a standard oriented 2-over-2 band
window with the explicit finite-sum endpoints above.

This boundary is intentionally structural: its result is retained diagram
syntax, never an evaluator equality or scalar equality.
-/
axiom standardBandEndpointInterpretation
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
    BandEndpointInterpretation window 𝒞 η sourceCycle

namespace BandEndpointInterpretation

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
      BandEndpointInterpretation window 𝒞 η sourceCycle) :
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
  insertionLaw := interpretation.insertionLaw
  mateLaw := interpretation.mateLaw
  movies := interpretation.movies
  closedWindow := interpretation.closedWindow
  movingCoefficient := interpretation.movingCoefficient
  source_endpoint := interpretation.source_endpoint
  target_endpoint := interpretation.target_endpoint

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
      BandEndpointInterpretation window 𝒞 η sourceCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source window.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle) :=
  interpretation.toFiniteSumBinding.roleAwareCycleEval_eq

end BandEndpointInterpretation

/-- Complete normalized role-aware 2/2 invariance. -/
theorem roleAwareCycleEval_eq
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      KirbyCompleteness.TableTwoMoveMetadata
        .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (window : Window source target metadata countsSound)
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    (sourceCycle : source.DegreeTwoCycle) :
    CanonicalPresentation.roleAwareCycleEval
        𝒞 η source window.sourceGeometry sourceCycle =
      CanonicalPresentation.roleAwareCycleEval
        𝒞 η target window.targetGeometry
          ((Request.twoOverTwo metadata countsSound).targetCycle
            sourceCycle) :=
  (standardBandEndpointInterpretation
    window 𝒞 η sourceCycle).roleAwareCycleEval_eq

end Window

end TwistedYetter.Kirby.RoleAwareTwoOverTwoBandMovie
