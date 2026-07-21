import TwistedYetter.Kirby.CancellationSafeH2Representative

/-!
# Constructing cancellation-safe representatives over arbitrary H2

This module isolates the exact chain-level fact needed to transport an
arbitrary integral second-homology class through a cancellation death.

For every non-death calculation, the source representative transports
forward directly.  For a death, the topology compiler must exhibit a strict
cycle retraction: every target cycle has a source lift, forward transport
returns the target cycle, and delete-then-reinsert returns the source lift.

The retraction contains no category scalar and no evaluator equality.  Lean
derives from it that the lifted source cycle represents the inverse-transported
`H2` class, is cancellation-safe, and has the same evaluation as the target.
No freeness, finite generation, torsion-free, or simply-connected hypothesis
is used.
-/

namespace TwistedYetter.Kirby.CancellationSafeH2Transport

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CancellationSafeH2Representative
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
The representative obtained by applying the calculation's actual forward
chain map to a source representative.
-/
noncomputable def transportedRepresentative
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move)
    {sourceAlpha : source.topology.handleChain.SecondHomology}
    (sourceRepresentative : GeometricRepresentative source sourceAlpha) :
    GeometricRepresentative target
      ((markedTransport calculation).chainEquivalence
        |>.secondHomologyAddEquiv sourceAlpha) where
  cycle := targetCycle calculation sourceRepresentative.cycle
  represents := by
    rw [targetCycle_class, sourceRepresentative.represents]

/--
Once the source cycle is known to be cancellation-safe, forward transport
constructs the complete compatible representative step.
-/
def transportedStep
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move)
    {sourceAlpha : source.topology.handleChain.SecondHomology}
    (sourceRepresentative : GeometricRepresentative source sourceAlpha)
    (safe : IsCancellationSafe calculation sourceRepresentative.cycle) :
    CancellationSafeStep calculation sourceRepresentative
      (transportedRepresentative calculation sourceRepresentative) where
  source_safe := safe
  target_cycle := rfl

/-- Exactly the two directed death constructors require an extra check. -/
def AutomaticallySafe
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move) : Prop :=
  match calculation with
  | .oneTwoDeath _ _ _ _ => False
  | .twoThreeDeath _ _ _ _ => False
  | _ => True

/-- Every non-death constructor is cancellation-safe by definition. -/
theorem isCancellationSafe_of_automaticallySafe
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move)
    (sourceCycle : source.DegreeTwoCycle)
    (automatic : AutomaticallySafe calculation) :
    IsCancellationSafe calculation sourceCycle := by
  cases calculation <;>
    simp_all [AutomaticallySafe, IsCancellationSafe, returnedSourceCycle]

/--
Strict cycle data for a cancellation death.

`forward_lift` says that adding the missing pair and then applying the death
returns the chosen target cycle.  `returned_lift` says that applying the
death and then its retained reverse birth returns the source lift literally.
-/
structure StrictCycleRetraction
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move) where
  lift : target.DegreeTwoCycle → source.DegreeTwoCycle
  forward_lift :
    (targetCycleValue : target.DegreeTwoCycle) →
      targetCycle calculation (lift targetCycleValue) = targetCycleValue
  returned_lift :
    (targetCycleValue : target.DegreeTwoCycle) →
      returnedSourceCycle calculation (lift targetCycleValue) =
        lift targetCycleValue

namespace StrictCycleRetraction

/--
The strict retraction carried by every 1--2 death calculation.

This constructor extracts only chain-level cycle data already required by
`OneTwoDeathCycleGeometry`; no evaluator equality is assumed.
-/
noncomputable def ofOneTwoDeath
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addOneTwo)
    (transport : MarkedH2Transport source.topology target.topology)
    (geometry : OneTwoDeathCycleGeometry source target transport) :
    StrictCycleRetraction
      (LocalCycleCalculation.oneTwoDeath
        (𝒞 := 𝒞) (automorphism := automorphism)
        metadata countsSound transport geometry) where
  lift := geometry.reverseBirth.added.cycleTransport.targetCycle
  forward_lift := geometry.forward_reverse_cycle
  returned_lift := by
    intro targetCycleValue
    change
      geometry.reverseBirth.added.cycleTransport.targetCycle
          ((CycleTransport.ofMarkedH2Transport source target transport).targetCycle
            (geometry.reverseBirth.added.cycleTransport.targetCycle
              targetCycleValue)) =
        geometry.reverseBirth.added.cycleTransport.targetCycle targetCycleValue
    rw [geometry.forward_reverse_cycle]

/--
The strict retraction carried by every 2--3 death calculation.
-/
noncomputable def ofTwoThreeDeath
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.topology target.topology)
    (countsSound :
      source.topology.counts = target.topology.counts.addTwoThree)
    (transport : MarkedH2Transport source.topology target.topology)
    (geometry : TwoThreeDeathCycleGeometry source target transport) :
    StrictCycleRetraction
      (LocalCycleCalculation.twoThreeDeath
        (𝒞 := 𝒞) (automorphism := automorphism)
        metadata countsSound transport geometry) where
  lift := geometry.reverseBirth.added.cycleTransport.targetCycle
  forward_lift := geometry.forward_reverse_cycle
  returned_lift := by
    intro targetCycleValue
    change
      geometry.reverseBirth.added.cycleTransport.targetCycle
          ((CycleTransport.ofMarkedH2Transport source target transport).targetCycle
            (geometry.reverseBirth.added.cycleTransport.targetCycle
              targetCycleValue)) =
        geometry.reverseBirth.added.cycleTransport.targetCycle targetCycleValue
    rw [geometry.forward_reverse_cycle]

/-- The source class forced by inverse transport of a target class. -/
noncomputable def sourceClass
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    {calculation : LocalCycleCalculation 𝒞 automorphism move}
    (_retraction : StrictCycleRetraction calculation)
    (targetAlpha : target.topology.handleChain.SecondHomology) :
    source.topology.handleChain.SecondHomology :=
  (markedTransport calculation).chainEquivalence
    |>.secondHomologyAddEquiv.symm targetAlpha

/--
Lift a target representative through a strict cancellation retraction.

The proof that the result represents the inverse-transported class is
derived from homology naturality; it is not a field of the retraction.
-/
noncomputable def liftRepresentative
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    {calculation : LocalCycleCalculation 𝒞 automorphism move}
    (retraction : StrictCycleRetraction calculation)
    {targetAlpha : target.topology.handleChain.SecondHomology}
    (targetRepresentative : GeometricRepresentative target targetAlpha) :
    GeometricRepresentative source (retraction.sourceClass targetAlpha) where
  cycle := retraction.lift targetRepresentative.cycle
  represents := by
    unfold sourceClass
    apply (markedTransport calculation).chainEquivalence
      |>.secondHomologyAddEquiv.injective
    rw [AddEquiv.apply_symm_apply]
    rw [← targetCycle_class calculation]
    rw [retraction.forward_lift]
    exact targetRepresentative.represents

/-- The lifted representative is visibly safe for the death. -/
theorem liftRepresentative_safe
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    {calculation : LocalCycleCalculation 𝒞 automorphism move}
    (retraction : StrictCycleRetraction calculation)
    {targetAlpha : target.topology.handleChain.SecondHomology}
    (targetRepresentative : GeometricRepresentative target targetAlpha) :
    IsCancellationSafe calculation
      (retraction.liftRepresentative targetRepresentative).cycle :=
  retraction.returned_lift targetRepresentative.cycle

/-- The retraction constructs the complete compatible death step. -/
def liftedStep
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    {calculation : LocalCycleCalculation 𝒞 automorphism move}
    (retraction : StrictCycleRetraction calculation)
    {targetAlpha : target.topology.handleChain.SecondHomology}
    (targetRepresentative : GeometricRepresentative target targetAlpha) :
    CancellationSafeStep calculation
      (retraction.liftRepresentative targetRepresentative)
      targetRepresentative where
  source_safe := retraction.liftRepresentative_safe targetRepresentative
  target_cycle := (retraction.forward_lift targetRepresentative.cycle).symm

/--
The scalar equality across a cancellation death is a theorem derived from
the strict topology-only retraction and the categorical local calculation.
-/
theorem eval_lift_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {source target : CanonicalPresentation manifold H2}
    {move : TableTwoMove source.topology target.topology}
    {calculation : LocalCycleCalculation 𝒞 automorphism move}
    (retraction : StrictCycleRetraction calculation)
    {targetAlpha : target.topology.handleChain.SecondHomology}
    (targetRepresentative : GeometricRepresentative target targetAlpha) :
    eval 𝒞 automorphism source (retraction.sourceClass targetAlpha)
        (retraction.liftRepresentative targetRepresentative) =
      eval 𝒞 automorphism target targetAlpha targetRepresentative :=
  eval_sound calculation
    (retraction.liftRepresentative targetRepresentative)
    targetRepresentative
    (retraction.liftedStep targetRepresentative)

end StrictCycleRetraction

end TwistedYetter.Kirby.CancellationSafeH2Transport
