import TwistedYetter.Kirby.CancellationSafeH2Transport
import TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler

/-!
# Representative transport and the extra strict-death boundary

Forward transport is total for framed isotopy, all three slides, and both
births.  A directed cancellation death is not forward-total on arbitrary
source cycles: the disappearing coefficient must be zero.  Reverse totality
at the raw-cycle level therefore requires a separately supplied strict cycle
retraction; it does not follow from chain homotopy equivalence alone.

This file proves that dichotomy for all eight checked constructors.  It is a
chain-level theorem and contains no scalar evaluation field.
-/

namespace TwistedYetter.Kirby.CertifiedH2RepresentativeTransport

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CancellationSafeH2Representative
open TwistedYetter.Kirby.CancellationSafeH2Transport
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.KernelCheckedLocalMoveCompiler
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Every source representative admits a compatible forward representative. -/
def ForwardTotal
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move) : Prop :=
  ∀ {sourceAlpha : source.topology.handleChain.SecondHomology},
    (sourceRepresentative : GeometricRepresentative source sourceAlpha) →
      ∃ targetRepresentative :
          GeometricRepresentative target
            ((markedTransport calculation).chainEquivalence
              |>.secondHomologyAddEquiv sourceAlpha),
        CancellationSafeStep calculation
          sourceRepresentative targetRepresentative

/-- Every target representative admits a compatible source lift. -/
def BackwardTotal
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move) : Prop :=
  ∀ {targetAlpha : target.topology.handleChain.SecondHomology},
    (targetRepresentative : GeometricRepresentative target targetAlpha) →
      ∃ sourceRepresentative :
          GeometricRepresentative source
            ((markedTransport calculation).chainEquivalence
              |>.secondHomologyAddEquiv.symm targetAlpha),
        CancellationSafeStep calculation
          sourceRepresentative targetRepresentative

/-- Every automatically safe constructor is forward-total. -/
theorem forwardTotal_of_automaticallySafe
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    {move : TableTwoMove source.topology target.topology}
    (calculation : LocalCycleCalculation 𝒞 automorphism move)
    (automatic : AutomaticallySafe calculation) :
    ForwardTotal calculation := by
  intro sourceAlpha sourceRepresentative
  let targetRepresentative :=
    transportedRepresentative calculation sourceRepresentative
  exact ⟨targetRepresentative,
    transportedStep calculation sourceRepresentative
      (isCancellationSafe_of_automaticallySafe
        calculation sourceRepresentative.cycle automatic)⟩

/-- A 1--2 death is total in the reverse direction. -/
theorem oneTwoDeath_backwardTotal
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
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
        metadata countsSound transport geometry) →
    BackwardTotal
      (LocalCycleCalculation.oneTwoDeath
        (𝒞 := 𝒞) (automorphism := automorphism)
        metadata countsSound transport geometry) := by
  intro retraction
  intro targetAlpha targetRepresentative
  exact ⟨retraction.liftRepresentative targetRepresentative,
    retraction.liftedStep targetRepresentative⟩

/-- A 2--3 death is total in the reverse direction. -/
theorem twoThreeDeath_backwardTotal
    {𝒞 : ModularCategory (K := K) (C := C) (S := S)}
    {automorphism : TensorIdentityAutomorphism C}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
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
        metadata countsSound transport geometry) →
    BackwardTotal
      (LocalCycleCalculation.twoThreeDeath
        (𝒞 := 𝒞) (automorphism := automorphism)
        metadata countsSound transport geometry) := by
  intro retraction
  intro targetAlpha targetRepresentative
  exact ⟨retraction.liftRepresentative targetRepresentative,
    retraction.liftedStep targetRepresentative⟩

end TwistedYetter.Kirby.CertifiedH2RepresentativeTransport
