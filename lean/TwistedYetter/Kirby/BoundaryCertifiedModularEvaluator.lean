import TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation
import TwistedYetter.Kirby.EGNOModularFinalTheoremRefactor
import TwistedYetter.Kirby.SourceBackedHandleChainNaturality

/-!
# The modular evaluator on boundary-certified presentations

This module closes the concrete evaluator bridge without identifying two
independently supplied handle complexes.

* a presentation carries a boundary standardization certificate;
* its Mathlib handle chain is definitionally built from the transposes of the
  primal derived `d2` and `d3`;
* a move is an exact existing Table 2 move between the converted certified
  presentations; and
* the public marking type is the second homology of that derived chain.

The primal handle counts remain available for link normalization and move
names; only the homology chain is turned over.  The fixed ambient `H2` type is
used only as the marked coordinate understood
by the existing event compiler.  Each presentation's visible
`h2ModelEquiv` identifies its derived handle homology with that coordinate.
-/

namespace TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.BoundaryCertifiedKirbyPresentation
open TwistedYetter.Kirby.BoundaryDerivedHandleChain
open TwistedYetter.Kirby.BoundaryDerivedHandleChainModel
open TwistedYetter.Kirby.BoundaryStandardization
open TwistedYetter.Kirby.EGNOModularFinalTheoremRefactor
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uD uIso uSlide uP uSphere uH uK uC vC

/--
An exact topology-only Table 2 move whose endpoints are certified
presentations.

The move carries no caller-supplied homology transport.  Its chain
equivalence is compiled below from the one visible standard handle-chain
naturality axiom.
-/
structure BoundaryCertifiedMove
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    (source target :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2) where
  underlying :
    TopologicalTableTwoMove
      (source.toSpecialKirbyPresentation semantics)
      (target.toSpecialKirbyPresentation semantics)

namespace BoundaryCertifiedMove

/--
Enrich a topology-only move with its source-bound handle-chain equivalence.
-/
noncomputable def enriched
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    {semantics : LowerKirbyDiagramSemantics lowerTheory}
    {lowerBoundary : LowerHandleBoundaryData lowerTheory}
    {sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus}
    {intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport}
    {H2 : Type uH} [AddCommGroup H2]
    {source target :
      BoundaryCertifiedPresentation lowerBoundary sphereTransport
        intersection H2}
    (move : BoundaryCertifiedMove semantics source target) :
    TableTwoMove
      (source.toSpecialKirbyPresentation semantics)
      (target.toSpecialKirbyPresentation semantics) :=
  enrichMove
    (sourceBackedGeometricH2Compiler H2).localCompiler
    move.underlying

end BoundaryCertifiedMove

/--
The marked-presentation calculus whose markings are derived handle homology.
-/
noncomputable def boundaryCertifiedCalculus
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (H2 : Type uH) [AddCommGroup H2] :
    HandlePresentationTheory where
  Presentation :=
    BoundaryCertifiedPresentation lowerBoundary sphereTransport
      intersection H2
  Marking := fun presentation =>
    presentation.handleChain.SecondHomology
  ElementaryMove := fun source target =>
    BoundaryCertifiedMove semantics source target
  transport := fun move =>
    move.enriched.homologyTransport.chainEquivalence.secondHomologyAddEquiv

section ModularEvaluation

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
The existing event-by-event modular evaluator, restricted to certified
presentations and their boundary-derived handle homology.
-/
noncomputable def boundaryCertifiedEvaluation
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (H2 : Type) [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (inputs : CompiledEvaluatorEvidence 𝒞 H2) :
    PresentationEvaluation
      (boundaryCertifiedCalculus semantics lowerBoundary sphereTransport
        intersection H2) K where
  value := fun presentation alpha =>
    inputs.presentationCompiler.value
      (presentation.toSpecialKirbyPresentation semantics)
      (presentation.h2ModelEquiv alpha)

/--
The certified evaluation preserves every exact certified Table 2 move.

The proof uses only the existing move compiler and the chain-induced homology
transport.  No equality of final evaluator values is accepted as input.
-/
theorem boundaryCertifiedEvaluation_localInvariant
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (H2 : Type) [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    (inputs : CompiledEvaluatorEvidence 𝒞 H2) :
    IsInvariantUnderElementaryMoves
      (boundaryCertifiedEvaluation semantics lowerBoundary sphereTransport
        intersection H2 𝒞 inputs) := by
  intro source target move alpha
  simpa only [boundaryCertifiedEvaluation, boundaryCertifiedCalculus] using
    (inputs.evalC_local_move_invariant
      (source := source.toSpecialKirbyPresentation semantics)
      (target := target.toSpecialKirbyPresentation semantics)
      move.enriched alpha)

/-- The boundary-certified evaluation on its generated Kirby quotient. -/
noncomputable def boundaryCertifiedEvaluationOnKirbyClass
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (H2 : Type) [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    (inputs : CompiledEvaluatorEvidence 𝒞 H2) :
    (boundaryCertifiedCalculus semantics lowerBoundary sphereTransport
      intersection H2).KirbyClass → K :=
  (boundaryCertifiedEvaluation semantics lowerBoundary sphereTransport
    intersection H2 𝒞 inputs).descendToKirbyClass
      (boundaryCertifiedEvaluation_localInvariant semantics lowerBoundary
        sphereTransport intersection H2 inputs)

/-- Quotient evaluation agrees with the certified presentation formula. -/
theorem boundaryCertifiedEvaluationOnKirbyClass_mk
    {calculus : FramedSurgeryDiagramTheory.{uD, uIso, uSlide}}
    {lowerTheory :
      LowerHandlebodyTheory.{uD, uIso, uSlide, uP} calculus}
    (semantics : LowerKirbyDiagramSemantics lowerTheory)
    (lowerBoundary : LowerHandleBoundaryData lowerTheory)
    (sphereTransport :
      SphereSystemTransport.{uD, uIso, uSlide, uSphere} calculus)
    (intersection :
      AttachingSphereIntersectionTheory
        lowerTheory lowerBoundary sphereTransport)
    (H2 : Type) [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    (inputs : CompiledEvaluatorEvidence 𝒞 H2)
    (marked :
      (boundaryCertifiedCalculus semantics lowerBoundary sphereTransport
        intersection H2).MarkedPresentation) :
    boundaryCertifiedEvaluationOnKirbyClass semantics lowerBoundary
        sphereTransport intersection H2 inputs (Quotient.mk _ marked) =
      (boundaryCertifiedEvaluation semantics lowerBoundary sphereTransport
        intersection H2 𝒞 inputs).markedValue marked :=
  rfl

end ModularEvaluation

end TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator
