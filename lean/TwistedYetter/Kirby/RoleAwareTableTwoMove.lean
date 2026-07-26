import TwistedYetter.Kirby.CanonicalSourceBackedMove
import TwistedYetter.Kirby.RoleAwareFramedIsotopy
import TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
import TwistedYetter.Kirby.RoleAwareTwoOverTwoBandMovie
import TwistedYetter.Kirby.SourceBoundRoleAwareOneTwo
import TwistedYetter.Kirby.SourceBoundRoleAwareTwoThree
import TwistedYetter.Kirby.SourceBoundUnitCutGeometry

/-!
# The eight role-aware special Kirby events

This file is the topology-only input language of the premodular main line.
Every constructor binds its local geometry to the simultaneous dotted-cut
geometry stored by its exact source and target presentations.  No field
mentions a category, character, scalar, or evaluator equality.
-/

namespace TwistedYetter.Kirby.RoleAwareTableTwoMove

open TwistedYetter.Kirby.CanonicalCycleMoveGeometry
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.RoleAwareAddedOrdinaryTransport
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uH

private noncomputable def moveTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) :
    MarkedH2Transport
      source.canonicalPresentation.topology
      target.canonicalPresentation.topology :=
  (enrichedMove move).homologyTransport

/-- Extra topology data for a role-aware 1--2 birth. -/
structure OneTwoBirthData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) where
  topology :
    SourceBoundRoleAwareOneTwo.BirthTopology
      source.canonicalPresentation target.canonicalPresentation
  source_geometry :
    topology.sourceGeometry = source.simultaneousGeometry
  target_geometry :
    topology.targetGeometry = target.simultaneousGeometry
  exponentTransport :
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) →
      topology.ordinaryChange.ExponentTransport sourceCycle
        ((CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          (moveTransport move)).targetCycle sourceCycle)
  addedExponentZero :
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) →
      (exponentTransport sourceCycle).addedExponent 0 = 0

/-- Extra topology data for a role-aware 1--2 death, read as a reverse birth. -/
structure OneTwoDeathData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) where
  reverseBirth :
    SourceBoundRoleAwareOneTwo.BirthTopology
      target.canonicalPresentation source.canonicalPresentation
  source_geometry :
    reverseBirth.targetGeometry = source.simultaneousGeometry
  target_geometry :
    reverseBirth.sourceGeometry = target.simultaneousGeometry
  exponentTransport :
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) →
      reverseBirth.ordinaryChange.ExponentTransport targetCycle
        ((CycleTransport.ofMarkedH2TransportInverse
          source.canonicalPresentation target.canonicalPresentation
          (moveTransport move)).targetCycle targetCycle)
  addedExponentZero :
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) →
      (exponentTransport targetCycle).addedExponent 0 = 0

/-- Extra topology data for a role-aware 2--3 birth. -/
structure TwoThreeBirthData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) where
  topology :
    SourceBoundRoleAwareTwoThree.BirthTopology
      source.canonicalPresentation target.canonicalPresentation
  source_geometry :
    topology.sourceGeometry = source.simultaneousGeometry
  target_geometry :
    topology.targetGeometry = target.simultaneousGeometry
  exponentTransport :
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) →
      topology.ordinaryChange.ExponentTransport sourceCycle
        ((CycleTransport.ofMarkedH2Transport
          source.canonicalPresentation target.canonicalPresentation
          (moveTransport move)).targetCycle sourceCycle)
  addedExponentZero :
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) →
      (exponentTransport sourceCycle).addedExponent 0 = 0

/-- Extra topology data for a role-aware 2--3 death, read as a reverse birth. -/
structure TwoThreeDeathData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) where
  reverseBirth :
    SourceBoundRoleAwareTwoThree.BirthTopology
      target.canonicalPresentation source.canonicalPresentation
  source_geometry :
    reverseBirth.targetGeometry = source.simultaneousGeometry
  target_geometry :
    reverseBirth.sourceGeometry = target.simultaneousGeometry
  exponentTransport :
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) →
      reverseBirth.ordinaryChange.ExponentTransport targetCycle
        ((CycleTransport.ofMarkedH2TransportInverse
          source.canonicalPresentation target.canonicalPresentation
          (moveTransport move)).targetCycle targetCycle)
  addedExponentZero :
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) →
      (exponentTransport targetCycle).addedExponent 0 = 0

/--
The exact eight-event role-aware move language.

All categorical equalities are deliberately absent.  The equality fields bind
the local topology certificate to the evaluator geometry already stored at
the two endpoints.
-/
inductive ElementaryMove
    {H2 : Type uH} [AddCommGroup H2] :
    Presentation H2 → Presentation H2 → Type (uH + 1)
  | framedIsotopy
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .framedIsotopy
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (geometry :
        RoleAwareFramedIsotopy.Geometry
          source.canonicalPresentation target.canonicalPresentation
          (moveTransport
            (.framedIsotopy metadata countsSound)))
      (sourceGeometry :
        geometry.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        geometry.targetGeometry = target.simultaneousGeometry) :
      ElementaryMove source target
  | oneOverOne
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .oneOverOne
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (movie :
        SourceBoundUnitCutGeometry.OneOverOneMovie
          source.canonicalPresentation target.canonicalPresentation metadata)
      (sourceGeometry :
        movie.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        movie.targetGeometry = target.simultaneousGeometry) :
      ElementaryMove source target
  | twoOverOne
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .twoOverOne
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (movie :
        SourceBoundUnitCutGeometry.TwoOverOneMovie
          source.canonicalPresentation target.canonicalPresentation metadata)
      (sourceGeometry :
        movie.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        movie.targetGeometry = target.simultaneousGeometry) :
      ElementaryMove source target
  | twoOverTwo
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .twoOverTwo
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (window :
        RoleAwareTwoOverTwoBandMovie.Window
          source.canonicalPresentation target.canonicalPresentation
          metadata countsSound)
      (sourceGeometry :
        window.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        window.targetGeometry = target.simultaneousGeometry) :
      ElementaryMove source target
  | oneTwoBirth
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .oneTwoBirth
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        target.canonicalPresentation.topology.counts =
          source.canonicalPresentation.topology.counts.addOneTwo)
      (data :
        OneTwoBirthData source target
          (.oneTwoBirth metadata countsSound)) :
      ElementaryMove source target
  | oneTwoDeath
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .oneTwoDeath
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts.addOneTwo)
      (data :
        OneTwoDeathData source target
          (.oneTwoDeath metadata countsSound)) :
      ElementaryMove source target
  | twoThreeBirth
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .twoThreeBirth
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        target.canonicalPresentation.topology.counts =
          source.canonicalPresentation.topology.counts.addTwoThree)
      (data :
        TwoThreeBirthData source target
          (.twoThreeBirth metadata countsSound)) :
      ElementaryMove source target
  | twoThreeDeath
      {source target : Presentation H2}
      (metadata :
        TableTwoMoveMetadata .twoThreeDeath
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts.addTwoThree)
      (data :
        TwoThreeDeathData source target
          (.twoThreeDeath metadata countsSound)) :
      ElementaryMove source target

namespace ElementaryMove

/-- Forget the role-aware geometry but retain the exact standard topology move. -/
def forget
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2} :
    ElementaryMove source target →
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology
  | .framedIsotopy metadata countsSound _ _ _ =>
      .framedIsotopy metadata countsSound
  | .oneOverOne metadata countsSound _ _ _ =>
      .oneOverOne metadata countsSound
  | .twoOverOne metadata countsSound _ _ _ =>
      .twoOverOne metadata countsSound
  | .twoOverTwo metadata countsSound _ _ _ =>
      .twoOverTwo metadata countsSound
  | .oneTwoBirth metadata countsSound _ =>
      .oneTwoBirth metadata countsSound
  | .oneTwoDeath metadata countsSound _ =>
      .oneTwoDeath metadata countsSound
  | .twoThreeBirth metadata countsSound _ =>
      .twoThreeBirth metadata countsSound
  | .twoThreeDeath metadata countsSound _ =>
      .twoThreeDeath metadata countsSound

/-- The chain-derived map on handle-chain second homology. -/
noncomputable def transport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    (move : ElementaryMove source target) :
    source.canonicalPresentation.topology.handleChain.SecondHomology ≃+
      target.canonicalPresentation.topology.handleChain.SecondHomology :=
  (enrichedMove move.forget).homologyTransport.chainEquivalence
    |>.secondHomologyAddEquiv

end ElementaryMove

/--
T4: standard local topology realizes each ordinary Table 2 move by one exact
role-aware certificate.  This boundary is category-neutral and contains no
evaluation statement.
-/
structure LocalGeometryRealization
    (H2 : Type uH) [AddCommGroup H2] where
  realize :
    {source target : Presentation H2} →
    TopologicalTableTwoMove
      source.canonicalPresentation.topology
      target.canonicalPresentation.topology →
      ElementaryMove source target
  forget_realize :
    {source target : Presentation H2} →
    (move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology) →
      (realize move).forget = move

end TwistedYetter.Kirby.RoleAwareTableTwoMove
