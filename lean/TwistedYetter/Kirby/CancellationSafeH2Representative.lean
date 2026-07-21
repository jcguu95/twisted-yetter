import TwistedYetter.Kirby.CanonicalCycleLocalInvariance

/-!
# Cancellation-safe representatives of second-homology classes

The naive cycle-colour evaluator is not constant on every fiber of
`cycles -> H2`.  The correct surgery statement therefore keeps a geometric
representative of the requested `H2` class and transports that representative
through each Kirby move.

For births, slides, and framed isotopies, the move geometry determines the
target cycle.  For a cancellation death, one extra condition is essential:
the source cycle must be recovered after transporting to the target and then
back through the reverse birth.  This is the chain-level form of Yetter's
rule that a cancellable two-handle is not part of the selected homology basis
and hence has exponent zero.

No field below contains an equality of evaluator values.
-/

namespace TwistedYetter.Kirby.CancellationSafeH2Representative

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
The marked handle-chain transport retained by one local calculation.
-/
noncomputable def markedTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move) :
    MarkedH2Transport source.topology target.topology :=
  match calculation with
  | .framedIsotopy _ _ transport _ => transport
  | .oneOverOne _ _ _ transport _ => transport
  | .twoOverOne _ _ _ transport _ => transport
  | .twoOverTwo _ _ _ transport _ => transport
  | .oneTwoBirth _ _ transport _ => transport
  | .oneTwoDeath _ _ transport _ =>
      transport
  | .twoThreeBirth _ _ transport _ => transport
  | .twoThreeDeath _ _ transport _ =>
      transport

/-- The chain-level cycle transport selected by the same calculation. -/
noncomputable def cycleTransport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move) :
    CycleTransport source target
      (markedTransport calculation).targetClass :=
  match calculation with
  | .framedIsotopy _ _ _ geometry =>
      geometry.cycleTransport
  | .oneOverOne _ _ _ transport _ =>
      CycleTransport.ofMarkedH2Transport source target transport
  | .twoOverOne _ _ _ transport _ =>
      CycleTransport.ofMarkedH2Transport source target transport
  | .twoOverTwo _ _ _ transport _ =>
      CycleTransport.ofMarkedH2Transport source target transport
  | .oneTwoBirth _ _ _ geometry =>
      geometry.added.cycleTransport
  | .oneTwoDeath _ _ transport _ =>
      CycleTransport.ofMarkedH2Transport source target transport
  | .twoThreeBirth _ _ _ geometry =>
      geometry.added.cycleTransport
  | .twoThreeDeath _ _ transport _ =>
      CycleTransport.ofMarkedH2Transport source target transport

/-- The target cycle forced by the calculation and source cycle. -/
noncomputable def targetCycle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (sourceCycle : source.DegreeTwoCycle) :
    target.DegreeTwoCycle :=
  (cycleTransport calculation).targetCycle sourceCycle

/--
The forced target cycle represents exactly the class induced by the retained
handle-chain equivalence.
-/
theorem targetCycle_class
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (sourceCycle : source.DegreeTwoCycle) :
    target.topology.handleChain.complex.homologyπ 2
        (targetCycle calculation sourceCycle) =
      (markedTransport calculation).chainEquivalence.secondHomologyAddEquiv
          (source.topology.handleChain.complex.homologyπ 2 sourceCycle) := by
  apply target.topology.h2ModelEquiv.injective
  simp only [targetCycle]
  rw [(cycleTransport calculation).class_sound]
  simp [MarkedH2Transport.targetClass,
    MarkedH2Transport.homologyEquiv,
    MarkedH2Transport.homologyAddEquiv]

/--
After a death move, transport the proposed target cycle back through the
reverse birth.  Other move types leave the source cycle unchanged here.
-/
noncomputable def returnedSourceCycle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (sourceCycle : source.DegreeTwoCycle) :
    source.DegreeTwoCycle :=
  match calculation with
  | .oneTwoDeath _ _ _ geometry =>
      geometry.reverseBirth.added.cycleTransport.targetCycle
        (targetCycle calculation sourceCycle)
  | .twoThreeDeath _ _ _ geometry =>
      geometry.reverseBirth.added.cycleTransport.targetCycle
        (targetCycle calculation sourceCycle)
  | _ => sourceCycle

/--
The exact no-hidden-boundary condition needed by a cancellation.

For non-death moves this is definitionally reflexive.  For a death it says
that deleting and then re-inserting the cancelling pair returns the original
cycle, so no nonzero homology coefficient was hidden on the deleted
two-handle.
-/
def IsCancellationSafe
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (sourceCycle : source.DegreeTwoCycle) : Prop :=
  returnedSourceCycle calculation sourceCycle = sourceCycle

/--
Every local calculation preserves the explicit-cycle value on a
cancellation-safe source cycle.
-/
theorem cycleEvalC_sound
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    (sourceCycle : source.DegreeTwoCycle)
    (safe : IsCancellationSafe calculation sourceCycle) :
    source.cycleEvalC 𝒞 automorphism sourceCycle =
      target.cycleEvalC 𝒞 automorphism
        (targetCycle calculation sourceCycle) := by
  cases calculation with
  | framedIsotopy metadata counts transport geometry =>
      exact cycleEvalC_eq_of_counts_and_linear_eval
        𝒞 automorphism sourceCycle
        (geometry.cycleTransport.targetCycle sourceCycle)
        counts
        (geometry.cycleLinearDiagram_eval_transport
          𝒞 automorphism sourceCycle)
  | oneOverOne orientation metadata counts transport geometry =>
      exact cycleEvalC_eq_of_counts_and_linear_eval
        𝒞 automorphism sourceCycle
        ((CycleTransport.ofMarkedH2Transport
          source target transport).targetCycle sourceCycle)
        counts
        (geometry.cycleLinearDiagram_eval_transport
          𝒞 automorphism sourceCycle)
  | twoOverOne orientation metadata counts transport geometry =>
      exact cycleEvalC_eq_of_counts_and_linear_eval
        𝒞 automorphism sourceCycle
        ((CycleTransport.ofMarkedH2Transport
          source target transport).targetCycle sourceCycle)
        counts
        (geometry.cycleLinearDiagram_eval_transport
          𝒞 automorphism sourceCycle)
  | twoOverTwo orientation metadata counts transport geometry =>
      exact cycleEvalC_eq_of_counts_and_linear_eval
        𝒞 automorphism sourceCycle
        ((CycleTransport.ofMarkedH2Transport
          source target transport).targetCycle sourceCycle)
        counts
        (geometry.cycleLinearDiagram_eval_transport
          𝒞 automorphism sourceCycle)
  | oneTwoBirth metadata counts transport geometry =>
      exact oneTwoBirth_cycleEvalC
        𝒞 automorphism counts geometry sourceCycle
  | oneTwoDeath metadata counts transport geometry =>
      let forward :=
        CycleTransport.ofMarkedH2Transport source target transport
      have birthSound :=
        oneTwoBirth_cycleEvalC
          𝒞 automorphism counts geometry.reverseBirth
          (forward.targetCycle sourceCycle)
      change
        geometry.reverseBirth.added.cycleTransport.targetCycle
            (forward.targetCycle sourceCycle) =
          sourceCycle at safe
      rw [safe] at birthSound
      exact birthSound.symm
  | twoThreeBirth metadata counts transport geometry =>
      exact twoThreeBirth_cycleEvalC
        𝒞 automorphism counts geometry sourceCycle
  | twoThreeDeath metadata counts transport geometry =>
      let forward :=
        CycleTransport.ofMarkedH2Transport source target transport
      have birthSound :=
        twoThreeBirth_cycleEvalC
          𝒞 automorphism counts geometry.reverseBirth
          (forward.targetCycle sourceCycle)
      change
        geometry.reverseBirth.added.cycleTransport.targetCycle
            (forward.targetCycle sourceCycle) =
          sourceCycle at safe
      rw [safe] at birthSound
      exact birthSound.symm

/--
A geometric representative of an actual second-homology class.

The public index is `alpha : H2`; the cycle is internal evidence and must be
proved to represent that class.
-/
structure GeometricRepresentative
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) where
  cycle : presentation.DegreeTwoCycle
  represents :
    presentation.topology.handleChain.complex.homologyπ 2 cycle = alpha

/-- Evaluate an `H2` class through its explicit geometric representative. -/
noncomputable def eval
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (representative : GeometricRepresentative presentation alpha) : K :=
  presentation.cycleEvalC 𝒞 automorphism representative.cycle

/--
Compatibility data for two geometric representatives across one move.

No scalar equality is stored.  The target cycle must literally be the cycle
produced by the move geometry, and the source must pass the visible
cancellation-safety predicate.
-/
structure CancellationSafeStep
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    {sourceAlpha :
      source.topology.handleChain.SecondHomology}
    {targetAlpha :
      target.topology.handleChain.SecondHomology}
    (sourceRepresentative :
      GeometricRepresentative source sourceAlpha)
    (targetRepresentative :
      GeometricRepresentative target targetAlpha) where
  source_safe :
    IsCancellationSafe calculation sourceRepresentative.cycle
  target_cycle :
    targetRepresentative.cycle =
      targetCycle calculation sourceRepresentative.cycle

namespace CancellationSafeStep

/--
Compatibility forces the public target `H2` class to be the actual
chain-equivalence transport of the public source class.
-/
theorem alpha_transport
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    {sourceAlpha :
      source.topology.handleChain.SecondHomology}
    {targetAlpha :
      target.topology.handleChain.SecondHomology}
    (sourceRepresentative :
      GeometricRepresentative source sourceAlpha)
    (targetRepresentative :
      GeometricRepresentative target targetAlpha)
    (compatible :
      CancellationSafeStep calculation
        sourceRepresentative targetRepresentative) :
    targetAlpha =
      (markedTransport calculation).chainEquivalence.secondHomologyAddEquiv
        sourceAlpha := by
  rw [← targetRepresentative.represents,
    compatible.target_cycle,
    targetCycle_class,
    sourceRepresentative.represents]

end CancellationSafeStep

/--
The corrected local `H2` theorem: compatible cancellation-safe geometric
representatives give equal evaluations.
-/
theorem eval_sound
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation :
      LocalCycleCalculation 𝒞 automorphism move)
    {sourceAlpha :
      source.topology.handleChain.SecondHomology}
    {targetAlpha :
      target.topology.handleChain.SecondHomology}
    (sourceRepresentative :
      GeometricRepresentative source sourceAlpha)
    (targetRepresentative :
      GeometricRepresentative target targetAlpha)
    (compatible :
      CancellationSafeStep calculation
        sourceRepresentative targetRepresentative) :
    eval 𝒞 automorphism source sourceAlpha sourceRepresentative =
      eval 𝒞 automorphism target targetAlpha targetRepresentative := by
  rw [eval, eval, compatible.target_cycle]
  exact cycleEvalC_sound calculation sourceRepresentative.cycle
    compatible.source_safe

/--
One presentation together with an actual `H2` class and a certified geometric
representative of that class.
-/
structure GeometricH2State
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  presentation : CanonicalPresentation manifold H2
  alpha : presentation.topology.handleChain.SecondHomology
  representative : GeometricRepresentative presentation alpha

namespace GeometricH2State

/-- Evaluation of a geometrically represented `H2` state. -/
noncomputable def value
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (state : GeometricH2State manifold H2) : K :=
  eval 𝒞 automorphism state.presentation state.alpha
    state.representative

end GeometricH2State

/--
An internal admissible handle presentation of one public class
`alpha : H2`.

The public class is expressed in the fixed geometric `H2` coordinates.
The handle-chain class and its degree-two cycle are proof witnesses hidden
inside `state`.  In particular, callers of the eventual manifold invariant
will not supply a cycle.
-/
structure AdmissiblePresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (alpha : H2) where
  state : GeometricH2State manifold H2
  representsPublicClass :
    state.presentation.topology.h2ModelEquiv state.alpha = alpha

namespace AdmissiblePresentation

/--
Every canonical presentation produces an admissible representative of every
public `H2` class.  This is only representative existence for a fixed
presentation; it does not assert that two such choices are connected by a
cancellation-safe movie.
-/
noncomputable def ofCanonicalPresentation
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2)
    (alpha : H2) :
    AdmissiblePresentation manifold H2 alpha where
  state :=
    {
      presentation := presentation
      alpha := presentation.topology.h2ModelEquiv.symm alpha
      representative :=
        {
          cycle :=
            presentation.chosenCycle
              (presentation.topology.h2ModelEquiv.symm alpha)
          represents :=
            presentation.chosenCycle_class
              (presentation.topology.h2ModelEquiv.symm alpha)
        }
    }
  representsPublicClass :=
    presentation.topology.h2ModelEquiv.apply_symm_apply alpha

/-- Evaluate an admissible presentation using its internal cycle witness. -/
noncomputable def value
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {alpha : H2}
    (presentation : AdmissiblePresentation manifold H2 alpha) : K :=
  presentation.state.value 𝒞 automorphism

end AdmissiblePresentation

/--
A finite Kirby movie whose `H2` representatives are visibly transported and
cancellation-safe at every step.

The step constructor stores no equality in `K`.
-/
inductive CancellationSafeMovie
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2] :
    GeometricH2State manifold H2 →
      GeometricH2State manifold H2 →
        Type (max 2 (max uK (max uC (max vC (uH + 1)))))
  | refl (state : GeometricH2State manifold H2) :
      CancellationSafeMovie 𝒞 automorphism state state
  | step
      {source target : GeometricH2State manifold H2}
      {move :
        TableTwoMove
          source.presentation.topology
          target.presentation.topology}
      (calculation :
        LocalCycleCalculation 𝒞 automorphism move)
      (compatible :
        CancellationSafeStep calculation
          source.representative target.representative) :
      CancellationSafeMovie 𝒞 automorphism source target
  | trans
      {source middle target : GeometricH2State manifold H2} :
      CancellationSafeMovie 𝒞 automorphism source middle →
      CancellationSafeMovie 𝒞 automorphism middle target →
      CancellationSafeMovie 𝒞 automorphism source target

namespace CancellationSafeMovie

/--
The corrected movie-level `H2` theorem: a finite sequence of visibly
compatible, cancellation-safe moves preserves the evaluation.
-/
theorem value_sound
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : GeometricH2State manifold H2}
    (movie : CancellationSafeMovie 𝒞 automorphism source target) :
    source.value 𝒞 automorphism =
      target.value 𝒞 automorphism := by
  induction movie with
  | refl =>
      rfl
  | step calculation compatible =>
      exact eval_sound calculation _ _ compatible
  | trans _ _ firstSound secondSound =>
      exact firstSound.trans secondSound

end CancellationSafeMovie

/--
The existing local calculation proves equality for any two internal
admissible presentations joined by a cancellation-safe movie.

This is the categorical half of representative independence.  The remaining
global input is existence of such a movie between any two admissible
presentations of the same public pair `(X, alpha)`.
-/
theorem AdmissiblePresentation.value_eq_of_movie
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {alpha : H2}
    {source target : AdmissiblePresentation manifold H2 alpha}
    (movie :
      CancellationSafeMovie 𝒞 automorphism source.state target.state) :
    source.value 𝒞 automorphism =
      target.value 𝒞 automorphism :=
  movie.value_sound

end TwistedYetter.Kirby.CancellationSafeH2Representative
