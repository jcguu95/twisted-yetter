import TwistedYetter.Kirby.CancellationSafeH2Representative
import TwistedYetter.Kirby.H2BasisMarkedEvaluator
import TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

/-!
# Kirby invariance of the H2-basis-marked evaluator

This module connects the corrected `H₂`-level presentation formula to the
existing explicit-cycle Kirby calculations.

The bridge is deliberately geometric.  Across one move, it requires proof
that:

* the target basis-marked cycle is literally the cycle produced by the
  retained handle-chain map; and
* the source basis-marked cycle passes the visible cancellation-safety
  predicate.

Neither requirement contains a scalar, category evaluation, or equality of
invariant values.  Lean then derives local equality from the existing
coupon-calculus calculation, and derives finite-movie and quotient
invariance by induction.

What is not proved here is the global topology theorem constructing such
basis-compatible data for every Kirby--Cerf move.  That remaining obligation
is exposed by `BasisMarkedMove`, rather than hidden in an arbitrary
representative-independence axiom.
-/

namespace TwistedYetter.Kirby.H2BasisMarkedKirbyInvariance

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CancellationSafeH2Representative
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.H2BasisMarkedEvaluator
open TwistedYetter.Kirby.H2BasisMarkedEvaluator.CanonicalPresentation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.ModularFourManifoldInvariantFinalTarget

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Topology-only compatibility of two certified sphere bases across one local
Kirby calculation.

The target equality is at the level of actual degree-two cycles.  The second
field is the explicit no-hidden-coefficient condition for cancellation
deaths.  There is no field in `K`.
-/
structure BasisMarkedMoveCompatibility
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move)
    (sourceBasis : H2BasisRealization source)
    (targetBasis : H2BasisRealization target) where
  marked_cycle_transport :
    (alpha : source.topology.handleChain.SecondHomology) →
      targetBasis.markedCycle
          ((markedTransport calculation).chainEquivalence
            |>.secondHomologyAddEquiv alpha) =
        targetCycle calculation (sourceBasis.markedCycle alpha)
  cancellation_safe :
    (alpha : source.topology.handleChain.SecondHomology) →
      IsCancellationSafe calculation (sourceBasis.markedCycle alpha)

namespace BasisMarkedMoveCompatibility

/--
One basis-compatible local Kirby calculation preserves the corrected
`H₂`-level presentation value.
-/
theorem presentationValue_eq
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move)
    (sourceBasis : H2BasisRealization source)
    (targetBasis : H2BasisRealization target)
    (compatibility :
      BasisMarkedMoveCompatibility calculation sourceBasis targetBasis)
    (alpha : source.topology.handleChain.SecondHomology) :
    basisMarkedPresentationValue
        𝒞 automorphism source sourceBasis alpha =
      basisMarkedPresentationValue
        𝒞 automorphism target targetBasis
          ((markedTransport calculation).chainEquivalence
            |>.secondHomologyAddEquiv alpha) := by
  rw [basisMarkedPresentationValue_eq_rawCycleColourEval]
  rw [basisMarkedPresentationValue_eq_rawCycleColourEval]
  rw [compatibility.marked_cycle_transport]
  exact cycleEvalC_sound calculation
    (sourceBasis.markedCycle alpha)
    (compatibility.cancellation_safe alpha)

end BasisMarkedMoveCompatibility

/-- One canonical presentation equipped with a certified sphere basis. -/
structure BasisMarkedPresentation
    (H2 : Type uH) [AddCommGroup H2] where
  presentation : CanonicalPresentation H2
  basis : H2BasisRealization presentation

/--
One elementary move with an actual local graphical calculation and an actual
topological basis-transport proof.

There is no constructor from a scalar equality.
-/
structure BasisMarkedMove
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    (source target : BasisMarkedPresentation H2) where
  move :
    TableTwoMove
      source.presentation.topology target.presentation.topology
  calculation :
    LocalCycleCalculation 𝒞 automorphism move
  compatibility :
    BasisMarkedMoveCompatibility calculation source.basis target.basis

/--
The marked-presentation theory generated only by basis-compatible Kirby
moves.
-/
noncomputable def basisMarkedPresentationTheory
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2] :
    HandlePresentationTheory where
  Presentation := BasisMarkedPresentation H2
  Marking := fun marked =>
    marked.presentation.topology.handleChain.SecondHomology
  ElementaryMove := fun source target =>
    BasisMarkedMove 𝒞 automorphism source target
  transport := fun move =>
    (markedTransport move.calculation).chainEquivalence
      |>.secondHomologyAddEquiv

/-- The corrected scalar formula on one basis-certified presentation. -/
noncomputable def basisMarkedEvaluation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2] :
    PresentationEvaluation
      (basisMarkedPresentationTheory 𝒞 automorphism H2) K where
  value := fun marked alpha =>
    basisMarkedPresentationValue
      𝒞 automorphism marked.presentation marked.basis alpha

/--
The corrected evaluator preserves every admitted elementary move.

This theorem derives the equality; `BasisMarkedMove` itself cannot store it.
-/
theorem basisMarkedEvaluation_localInvariant
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2] :
    IsInvariantUnderElementaryMoves
      (basisMarkedEvaluation 𝒞 automorphism H2) := by
  intro source target move alpha
  exact move.compatibility.presentationValue_eq
    𝒞 automorphism move.calculation source.basis target.basis alpha

/--
The basis-marked formula therefore defines a scalar on the generated marked
Kirby quotient.
-/
noncomputable def basisMarkedEvaluationOnKirbyClass
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2] :
    (basisMarkedPresentationTheory
      𝒞 automorphism H2).KirbyClass → K :=
  (basisMarkedEvaluation 𝒞 automorphism H2).descendToKirbyClass
    (basisMarkedEvaluation_localInvariant
      𝒞 automorphism H2)

/-- Quotient evaluation agrees with the explicit presentation formula. -/
theorem basisMarkedEvaluationOnKirbyClass_mk
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (H2 : Type uH) [AddCommGroup H2]
    (marked :
      (basisMarkedPresentationTheory
        𝒞 automorphism H2).MarkedPresentation) :
    basisMarkedEvaluationOnKirbyClass
        𝒞 automorphism H2 (Quotient.mk _ marked) =
      (basisMarkedEvaluation
        𝒞 automorphism H2).markedValue marked :=
  rfl

end TwistedYetter.Kirby.H2BasisMarkedKirbyInvariance
