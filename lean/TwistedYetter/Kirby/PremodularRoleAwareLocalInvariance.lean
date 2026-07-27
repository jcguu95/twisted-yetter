import TwistedYetter.Kirby.RoleAwarePresentationEvaluation
import TwistedYetter.Kirby.RoleAwareTableTwoMove

/-!
# Exhaustive local invariance of the role-aware premodular evaluator

The theorem in this file performs exactly eight constructor cases.  It
contains no fallback constructor and accepts no evaluator equality as data.
-/

namespace TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.RoleAwarePresentationEvaluation
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.RoleAwareTableTwoMove
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- The forward chain map sends the chosen source cycle to the target class. -/
private theorem forwardCycleClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (transport : MarkedH2Transport source.topology target.topology)
    (alpha : source.topology.handleChain.SecondHomology) :
    target.topology.handleChain.complex.homologyπ 2
        ((CycleTransport.ofMarkedH2Transport source target transport)
          |>.targetCycle (source.chosenCycle alpha)) =
      transport.chainEquivalence.secondHomologyAddEquiv alpha := by
  apply target.topology.h2ModelEquiv.injective
  rw [(CycleTransport.ofMarkedH2Transport source target transport).class_sound]
  rw [source.chosenCycle_class]
  simp [MarkedH2Transport.targetClass,
    MarkedH2Transport.homologyEquiv,
    MarkedH2Transport.homologyAddEquiv]

/--
Transporting the chosen target representative backwards represents the
original source class.
-/
private theorem inverseChosenCycleClass
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (transport : MarkedH2Transport source.topology target.topology)
    (alpha : source.topology.handleChain.SecondHomology) :
    source.topology.handleChain.complex.homologyπ 2
        ((CycleTransport.ofMarkedH2TransportInverse source target transport)
          |>.targetCycle
            (target.chosenCycle
              (transport.chainEquivalence.secondHomologyAddEquiv alpha))) =
      alpha := by
  apply source.topology.h2ModelEquiv.injective
  rw [(CycleTransport.ofMarkedH2TransportInverse source target transport)
    |>.class_sound]
  rw [target.chosenCycle_class]
  simp [MarkedH2Transport.homologyEquiv,
    MarkedH2Transport.homologyAddEquiv]

/--
Every one of the eight role-aware elementary events preserves the
homology-level premodular evaluation.
-/
theorem elementaryMove_invariant
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {source target : Presentation H2}
    (move : ElementaryMove source target)
    (alpha :
      source.canonicalPresentation.topology.handleChain.SecondHomology) :
    roleAwareEvalH2 𝒞 η source alpha =
      roleAwareEvalH2 𝒞 η target
        (ElementaryMove.transport move alpha) := by
  cases move with
  | framedIsotopy metadata countsSound geometry componentChangeSound
      sourceGeometry targetGeometry =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .framedIsotopy metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let sourceCycle := source.canonicalPresentation.chosenCycle alpha
      let targetCycle :=
        (CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle sourceCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry sourceCycle := rfl
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              simpa [sourceGeometry, targetGeometry, topologyMove, transport,
                sourceCycle, targetCycle] using
                geometry.roleAwareCycleEval_eq transport
                  (framedIsotopyExponentTransport metadata countsSound
                    geometry componentChangeSound)
                  countsSound 𝒞 η sourceCycle
        _ = _ := by
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              simpa [ElementaryMove.transport, ElementaryMove.forget,
                topologyMove, transport, targetCycle] using
                forwardCycleClass transport alpha
  | oneOverOne metadata countsSound compiled sourceGeometry targetGeometry =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .oneOverOne metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let sourceCycle := source.canonicalPresentation.chosenCycle alpha
      let targetCycle :=
        (CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle sourceCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry sourceCycle := rfl
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              change compiled.movie.sourceGeometry =
                source.simultaneousGeometry at sourceGeometry
              change compiled.movie.targetGeometry =
                target.simultaneousGeometry at targetGeometry
              rw [← sourceGeometry, ← targetGeometry]
              simpa [topologyMove, transport, sourceCycle, targetCycle,
                CanonicalSourceBoundSlideMovie.Request.targetCycle] using
                SourceBoundUnitCutGeometry.oneOverOne_roleAwareCycleEval_eq
                  metadata countsSound compiled.movie 𝒞 η sourceCycle
        _ = _ := by
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              simpa [ElementaryMove.transport, ElementaryMove.forget,
                topologyMove, transport, targetCycle] using
                forwardCycleClass transport alpha
  | twoOverOne metadata countsSound compiled sourceGeometry targetGeometry =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .twoOverOne metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let sourceCycle := source.canonicalPresentation.chosenCycle alpha
      let targetCycle :=
        (CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle sourceCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry sourceCycle := rfl
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              change compiled.movie.sourceGeometry =
                source.simultaneousGeometry at sourceGeometry
              change compiled.movie.targetGeometry =
                target.simultaneousGeometry at targetGeometry
              rw [← sourceGeometry, ← targetGeometry]
              simpa [topologyMove, transport, sourceCycle, targetCycle,
                CanonicalSourceBoundSlideMovie.Request.targetCycle] using
                SourceBoundUnitCutGeometry.twoOverOne_roleAwareCycleEval_eq
                  metadata countsSound compiled.movie 𝒞 η sourceCycle
        _ = _ := by
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              simpa [ElementaryMove.transport, ElementaryMove.forget,
                topologyMove, transport, targetCycle] using
                forwardCycleClass transport alpha
  | twoOverTwo metadata countsSound clean sourceGeometry targetGeometry =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .twoOverTwo metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let sourceCycle := source.canonicalPresentation.chosenCycle alpha
      let targetCycle :=
        (CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle sourceCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry sourceCycle := rfl
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              change clean.window.sourceGeometry =
                source.simultaneousGeometry at sourceGeometry
              change clean.window.targetGeometry =
                target.simultaneousGeometry at targetGeometry
              rw [← sourceGeometry, ← targetGeometry]
              simpa [topologyMove, transport, sourceCycle, targetCycle,
                CanonicalSourceBoundSlideMovie.Request.targetCycle] using
                clean.roleAwareCycleEval_eq
                  metadata countsSound 𝒞 η sourceCycle
                    (RoleAwareTwoOverTwoBandMovie.TwoOverTwoAttachDetach.resolve
                      metadata countsSound clean sourceCycle)
        _ = _ := by
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              simpa [ElementaryMove.transport, ElementaryMove.forget,
                topologyMove, transport, targetCycle] using
                forwardCycleClass transport alpha
  | oneTwoBirth metadata countsSound data =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .oneTwoBirth metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let sourceCycle := source.canonicalPresentation.chosenCycle alpha
      let targetCycle :=
        (CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle sourceCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry sourceCycle := rfl
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              simpa [data.source_geometry, data.target_geometry, topologyMove,
                transport, sourceCycle, targetCycle] using
                (data.topology.roleAwareCycleEval_birth countsSound
                  𝒞 η sourceCycle targetCycle
                  (data.exponentTransport sourceCycle)
                  (data.exponentTransport_addedExponent_zero sourceCycle)).symm
        _ = _ := by
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              simpa [ElementaryMove.transport, ElementaryMove.forget,
                topologyMove, transport, targetCycle] using
                forwardCycleClass transport alpha
  | oneTwoDeath metadata countsSound data =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .oneTwoDeath metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let targetAlpha := transport.chainEquivalence.secondHomologyAddEquiv alpha
      let targetCycle := target.canonicalPresentation.chosenCycle targetAlpha
      let returnedSourceCycle :=
        (CycleTransport.ofMarkedH2TransportInverse
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle targetCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry returnedSourceCycle := by
              symm
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              exact inverseChosenCycleClass transport alpha
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              simpa [data.source_geometry, data.target_geometry,
                returnedSourceCycle] using
                data.reverseBirth.roleAwareCycleEval_death countsSound
                  𝒞 η targetCycle returnedSourceCycle
                  (data.exponentTransport targetCycle)
                  (data.exponentTransport_addedExponent_zero targetCycle)
        _ = _ := by
              rfl
  | twoThreeBirth metadata countsSound data =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .twoThreeBirth metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let sourceCycle := source.canonicalPresentation.chosenCycle alpha
      let targetCycle :=
        (CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle sourceCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry sourceCycle := rfl
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              simpa [data.source_geometry, data.target_geometry, topologyMove,
                transport, sourceCycle, targetCycle] using
                (data.topology.roleAwareCycleEval_birth countsSound
                  𝒞 η sourceCycle targetCycle
                  (data.exponentTransport sourceCycle)
                  (data.exponentTransport_addedExponent_zero sourceCycle)).symm
        _ = _ := by
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              simpa [ElementaryMove.transport, ElementaryMove.forget,
                topologyMove, transport, targetCycle] using
                forwardCycleClass transport alpha
  | twoThreeDeath metadata countsSound data =>
      let topologyMove : TopologicalTableTwoMove
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology :=
        .twoThreeDeath metadata countsSound
      let transport := (enrichedMove topologyMove).homologyTransport
      let targetAlpha := transport.chainEquivalence.secondHomologyAddEquiv alpha
      let targetCycle := target.canonicalPresentation.chosenCycle targetAlpha
      let returnedSourceCycle :=
        (CycleTransport.ofMarkedH2TransportInverse
          source.canonicalPresentation target.canonicalPresentation
          transport).targetCycle targetCycle
      calc
        roleAwareEvalH2 𝒞 η source alpha =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η source.canonicalPresentation
              source.simultaneousGeometry returnedSourceCycle := by
              symm
              apply roleAwareCycleEval_eq_roleAwareEvalH2
              exact inverseChosenCycleClass transport alpha
        _ =
            RoleAwarePremodularEvaluator.CanonicalPresentation.roleAwareCycleEval
              𝒞 η target.canonicalPresentation
              target.simultaneousGeometry targetCycle := by
              simpa [data.source_geometry, data.target_geometry,
                returnedSourceCycle] using
                data.reverseBirth.roleAwareCycleEval_death countsSound
                  𝒞 η targetCycle returnedSourceCycle
                  (data.exponentTransport targetCycle)
                  (data.exponentTransport_addedExponent_zero targetCycle)
        _ = _ := by
              rfl

end TwistedYetter.Kirby.PremodularRoleAwareLocalInvariance
