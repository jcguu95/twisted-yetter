import TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput
import TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
import TwistedYetter.Kirby.LiteratureBackedFourManifoldInputs
import TwistedYetter.Kirby.DottedBoundaryGeneratorInvariance

/-!
# Closed four-manifold invariance relative to explicit literature inputs

This is the final descent module for the modular route relative to the
external statements named below.  It is not an axiom-free reconstruction of
smooth topology or planar Kirby-diagram geometry.

The public evaluator `EvalC` is constructed from a canonical component trace,
the category's exact simple objects, tensor-automorphism weights, finite
Kirby-colour sums, scalarization, and category-derived normalization.  It is
not a caller-supplied function.

The proof has three visible layers:

1. standard smooth four-manifold/Kirby--Cerf correspondence and handle-chain
   naturality are imported at the explicit literature boundary;
2. exact local endpoint realizations are imported only as values of
   restricted graphical proof grammars; and
3. standard dotted-disk geometry is imported as an explicit, category-neutral
   topology fact and compiled through the modular vacuum identity into
   independence from the chosen degree-two cycle; and
4. Lean proves all eight local evaluator equalities, finite-movie descent,
   and oriented-diffeomorphism invariance.

No theorem below accepts a caller-selected dotted geometry, local-move
realization, graphical compiler, arbitrary evaluator, scalar equality, or
evidence hash as a parameter. Standard dotted geometry is part of the final
presentation domain; its existence and Kirby--Cerf completeness therefore
remain visible in the four smooth-topology assumptions. The fixed local-move
realization axiom and handle-chain naturality axiom remain visible in
`#print axioms`. The categorical dotted-label calculation and descent to
`H₂` are proved, not assumed.
-/

namespace TwistedYetter.Kirby.CanonicalModularKirbyInvariance

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.DottedBoundaryGeometry
open TwistedYetter.Kirby.HandleChainHomology
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.LiteratureBackedFourManifoldTopology
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Machine-visible denominator of the directed local move proof. -/
inductive LocalCalculationClass where
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
  deriving Repr, BEq, DecidableEq

def requiredLocalCalculationClasses : List LocalCalculationClass :=
  [
    .framedIsotopy,
    .oneOverOne,
    .twoOverOne,
    .twoOverTwo,
    .oneTwoBirth,
    .oneTwoDeath,
    .twoThreeBirth,
    .twoThreeDeath
  ]

theorem required_local_calculation_class_count :
    requiredLocalCalculationClasses.length = 8 := by
  rfl

theorem required_local_calculation_classes_unique :
    requiredLocalCalculationClasses.Nodup := by
  decide

/-- Public alias for the canonical chain enrichment used throughout this file. -/
noncomputable def enrichedMove
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation manifold H2}
    (move : TopologicalTableTwoMove source.topology target.topology) :
    TableTwoMove source.topology target.topology :=
  CanonicalSourceBackedMove.enrichedMove move

/--
The category-neutral marked handle-presentation theory.

Its markings are the actual second homology groups of the handle chain
complexes.  Its elementary relation is exactly the eight source-bound
topology moves.
-/
noncomputable def handlePresentationTheory
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] :
    HandlePresentationTheory where
  Presentation := StandardDottedCanonicalPresentation manifold H2
  Marking := fun presentation =>
    presentation.canonicalPresentation.topology.handleChain.SecondHomology
  ElementaryMove := fun source target =>
    TopologicalTableTwoMove
      source.canonicalPresentation.topology
      target.canonicalPresentation.topology
  transport := fun move =>
    (enrichedMove move).homologyTransport.chainEquivalence
      |>.secondHomologyAddEquiv

/--
The canonical modular presentation evaluation in each presentation's own
handle-chain coordinates.
-/
noncomputable def presentationEvaluation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] :
    PresentationEvaluation
      (handlePresentationTheory manifold H2) K where
  value := fun presentation alpha =>
    presentation.canonicalPresentation.EvalC 𝒞 automorphism alpha

/--
Compile one certified standard dotted presentation into independence from the
selected cycle representative. The proof invokes the finite dotted-label
calculation and integral handle-chain generator reduction established in
`DottedBoundaryGeneratorInvariance`.
-/
theorem representativeIndependenceOfStandardDottedPresentation
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : StandardDottedCanonicalPresentation manifold H2) :
    CanonicalPresentation.CycleRepresentativeIndependence
      𝒞 automorphism presentation.canonicalPresentation := by
  intro left right sameClass
  exact presentation.dottedGeometry.respects_homology_class
    𝒞 automorphism presentation.canonicalPresentation
    left right sameClass

/--
The canonical evaluator is invariant under every elementary marked move.

The two literature-backed graphical inputs return only restricted proof
terms. `LocalCycleCalculation.soundOfEndpoints` performs the actual category
calculation, representative-independence bridge, and normalization proof.
-/
theorem evalC_local_move_invariant
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C) :
    IsInvariantUnderElementaryMoves
      (presentationEvaluation 𝒞 automorphism manifold H2) := by
  intro source target move alpha
  change
    source.canonicalPresentation.EvalC 𝒞 automorphism alpha =
      target.canonicalPresentation.EvalC 𝒞 automorphism
        ((enrichedMove move).homologyTransport.chainEquivalence
          |>.secondHomologyAddEquiv alpha)
  exact LocalCycleCalculation.soundOfEndpoints
    (representativeIndependenceOfStandardDottedPresentation
      𝒞 automorphism source)
    (representativeIndependenceOfStandardDottedPresentation
      𝒞 automorphism target)
    (standardLocalCycleCalculation 𝒞 automorphism move)
    alpha

/--
The canonical modular invariant of marked closed oriented smooth
four-manifolds, relative to the explicitly named topology, handle-chain, and
diagrammatic literature inputs.

The only explicit theorem argument beyond the category and tensor
automorphism is the four-part smooth-topology literature boundary.  The
separately named handle-chain and diagrammatic literature inputs remain
visible in the theorem's axiom audit.
-/
noncomputable def EvalCOnClosedFourManifolds
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (topology :
      Assumptions
        (handlePresentationTheory manifold H2)) :
    topology.realization.MarkedClosedOrientedSmoothFourManifold → K :=
  topology.fourManifoldInvariant
    (presentationEvaluation 𝒞 automorphism manifold H2)
    (evalC_local_move_invariant 𝒞 automorphism)

/-- The resulting function is invariant under oriented diffeomorphism. -/
theorem EvalCOnClosedFourManifolds_diffeomorphism_invariant
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (topology :
      Assumptions
        (handlePresentationTheory manifold H2))
    {left right :
      topology.realization.MarkedClosedOrientedSmoothFourManifold}
    (diffeomorphism :
      topology.realization.orientedDiffeomorphism.Hom left right) :
    EvalCOnClosedFourManifolds
        𝒞 automorphism topology left =
      EvalCOnClosedFourManifolds
        𝒞 automorphism topology right :=
  topology.fourManifoldInvariant_diffeomorphism_invariant
    (presentationEvaluation 𝒞 automorphism manifold H2)
    (evalC_local_move_invariant 𝒞 automorphism)
    diffeomorphism

/-- Pullback along geometric realization recovers the canonical `EvalC`. -/
theorem EvalCOnClosedFourManifolds_on_presentation
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (topology :
      Assumptions
        (handlePresentationTheory manifold H2))
    (presentation : StandardDottedCanonicalPresentation manifold H2)
    (alpha :
      presentation.canonicalPresentation.topology.handleChain.SecondHomology) :
    EvalCOnClosedFourManifolds
        𝒞 automorphism topology
        (topology.realization.realize ⟨presentation, alpha⟩) =
      presentation.canonicalPresentation.EvalC
        𝒞 automorphism alpha :=
  topology.fourManifoldInvariant_on_presentation
    (presentationEvaluation 𝒞 automorphism manifold H2)
    (evalC_local_move_invariant 𝒞 automorphism)
    ⟨presentation, alpha⟩

end TwistedYetter.Kirby.CanonicalModularKirbyInvariance
