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
open TwistedYetter.Kirby.RoleAwarePremodularEvaluator
open TwistedYetter.Kirby.RoleAwareSpecialKirbyPresentation
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness
open TwistedYetter.Kirby.SourceBoundLocalMoveRecipe

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
    (metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology)
    (countsSound :
      target.canonicalPresentation.topology.counts =
        source.canonicalPresentation.topology.counts.addOneTwo) where
  topology :
    SourceBoundRoleAwareOneTwo.BirthTopology
      source.canonicalPresentation target.canonicalPresentation
  source_geometry :
    topology.sourceGeometry = source.simultaneousGeometry
  target_geometry :
    topology.targetGeometry = target.simultaneousGeometry
  common_component_alignment :
    (sourceIndex :
      CanonicalPresentation.OrdinaryComponentIndex
        source.canonicalPresentation) →
      (componentAt target.canonicalPresentation.topology.formal
          (topology.ordinaryChange.targetDecomposition.symm
            (Sum.inl sourceIndex)).1).componentId =
        (componentAt target.canonicalPresentation.topology.formal
          ((oneTwoBirthAddedChange
            metadata).targetDecomposition.symm
            (Sum.inl sourceIndex.1))).componentId
  added_component_alignment :
    (componentAt target.canonicalPresentation.topology.formal
        (topology.ordinaryChange.targetDecomposition.symm
          (Sum.inr (0 : Fin 1))).1).componentId =
      (componentAt target.canonicalPresentation.topology.formal
        ((oneTwoBirthAddedChange
          metadata).targetDecomposition.symm
          (Sum.inr secondOfTwo))).componentId

/-- Extra topology data for a role-aware 1--2 death, read as a reverse birth. -/
structure OneTwoDeathData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology)
    (countsSound :
      source.canonicalPresentation.topology.counts =
        target.canonicalPresentation.topology.counts.addOneTwo) where
  reverseBirth :
    SourceBoundRoleAwareOneTwo.BirthTopology
      target.canonicalPresentation source.canonicalPresentation
  source_geometry :
    reverseBirth.targetGeometry = source.simultaneousGeometry
  target_geometry :
    reverseBirth.sourceGeometry = target.simultaneousGeometry
  common_component_alignment :
    (targetIndex :
      CanonicalPresentation.OrdinaryComponentIndex
        target.canonicalPresentation) →
      (componentAt source.canonicalPresentation.topology.formal
          (reverseBirth.ordinaryChange.targetDecomposition.symm
            (Sum.inl targetIndex)).1).componentId =
        (componentAt source.canonicalPresentation.topology.formal
          ((oneTwoDeathRemovedChange
            metadata).sourceDecomposition.symm
            (Sum.inl targetIndex.1))).componentId
  added_component_alignment :
    (componentAt source.canonicalPresentation.topology.formal
        (reverseBirth.ordinaryChange.targetDecomposition.symm
          (Sum.inr (0 : Fin 1))).1).componentId =
      (componentAt source.canonicalPresentation.topology.formal
        ((oneTwoDeathRemovedChange
          metadata).sourceDecomposition.symm
          (Sum.inr secondOfTwo))).componentId

/-- Extra topology data for a role-aware 2--3 birth. -/
structure TwoThreeBirthData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology)
    (countsSound :
      target.canonicalPresentation.topology.counts =
        source.canonicalPresentation.topology.counts.addTwoThree) where
  topology :
    SourceBoundRoleAwareTwoThree.BirthTopology
      source.canonicalPresentation target.canonicalPresentation
  source_geometry :
    topology.sourceGeometry = source.simultaneousGeometry
  target_geometry :
    topology.targetGeometry = target.simultaneousGeometry
  common_component_alignment :
    (sourceIndex :
      CanonicalPresentation.OrdinaryComponentIndex
        source.canonicalPresentation) →
      (componentAt target.canonicalPresentation.topology.formal
          (topology.ordinaryChange.targetDecomposition.symm
            (Sum.inl sourceIndex)).1).componentId =
        (componentAt target.canonicalPresentation.topology.formal
          ((twoThreeBirthAddedChange
            metadata).targetDecomposition.symm
            (Sum.inl sourceIndex.1))).componentId
  added_component_alignment :
    (componentAt target.canonicalPresentation.topology.formal
        (topology.ordinaryChange.targetDecomposition.symm
          (Sum.inr (0 : Fin 1))).1).componentId =
      (componentAt target.canonicalPresentation.topology.formal
        ((twoThreeBirthAddedChange
          metadata).targetDecomposition.symm
          (Sum.inr onlyOne))).componentId

/-- Extra topology data for a role-aware 2--3 death, read as a reverse birth. -/
structure TwoThreeDeathData
    {H2 : Type uH} [AddCommGroup H2]
    (source target : Presentation H2)
    (metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology)
    (countsSound :
      source.canonicalPresentation.topology.counts =
        target.canonicalPresentation.topology.counts.addTwoThree) where
  reverseBirth :
    SourceBoundRoleAwareTwoThree.BirthTopology
      target.canonicalPresentation source.canonicalPresentation
  source_geometry :
    reverseBirth.targetGeometry = source.simultaneousGeometry
  target_geometry :
    reverseBirth.sourceGeometry = target.simultaneousGeometry
  common_component_alignment :
    (targetIndex :
      CanonicalPresentation.OrdinaryComponentIndex
        target.canonicalPresentation) →
      (componentAt source.canonicalPresentation.topology.formal
          (reverseBirth.ordinaryChange.targetDecomposition.symm
            (Sum.inl targetIndex)).1).componentId =
        (componentAt source.canonicalPresentation.topology.formal
          ((twoThreeDeathRemovedChange
            metadata).sourceDecomposition.symm
            (Sum.inl targetIndex.1))).componentId
  added_component_alignment :
    (componentAt source.canonicalPresentation.topology.formal
        (reverseBirth.ordinaryChange.targetDecomposition.symm
          (Sum.inr (0 : Fin 1))).1).componentId =
      (componentAt source.canonicalPresentation.topology.formal
        ((twoThreeDeathRemovedChange
          metadata).sourceDecomposition.symm
          (Sum.inr onlyOne))).componentId

private theorem cycleComponentExponent_eq_of_componentId_eq
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation H2)
    (cycle : presentation.DegreeTwoCycle)
    (left right : Presentation.ComponentSpec)
    (componentId_eq : left.componentId = right.componentId) :
    presentation.cycleComponentExponent cycle left =
      presentation.cycleComponentExponent cycle right := by
  unfold CanonicalPresentation.cycleComponentExponent
  unfold SpecialKirbyPresentation.cycleComponentExponent
  rw [componentId_eq]

namespace OneTwoBirthData

/--
The role-filtered exponent transport is derived from handle-chain naturality
and the topology-only component alignment.  It is not part of the local
factorization axiom.
-/
noncomputable def exponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      target.canonicalPresentation.topology.counts =
        source.canonicalPresentation.topology.counts.addOneTwo}
    (data : OneTwoBirthData source target metadata countsSound)
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) :
    data.topology.ordinaryChange.ExponentTransport sourceCycle
      ((CycleTransport.ofMarkedH2Transport
        source.canonicalPresentation target.canonicalPresentation
        (moveTransport (.oneTwoBirth metadata countsSound))).targetCycle
          sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).oneTwoBirthCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      addedExponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro sourceIndex
    calc
      target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            (data.topology.ordinaryChange.targetDecomposition.symm
              (Sum.inl sourceIndex)).1) =
        target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            ((oneTwoBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inl sourceIndex.1))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          (data.common_component_alignment sourceIndex)
      _ = source.canonicalPresentation.cycleComponentExponent sourceCycle
          (componentAt source.canonicalPresentation.topology.formal
            sourceIndex.1) := by
        exact coordinateLaw.common_exponent_sound sourceCycle sourceIndex.1
  · intro addedIndex
    have addedIndex_eq : addedIndex = (0 : Fin 1) := Subsingleton.elim _ _
    subst addedIndex
    calc
      target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            (data.topology.ordinaryChange.targetDecomposition.symm
              (Sum.inr (0 : Fin 1))).1) =
        target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            ((oneTwoBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inr secondOfTwo))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          data.added_component_alignment
      _ = 0 :=
        coordinateLaw.added_exponent_zero sourceCycle secondOfTwo

@[simp]
theorem exponentTransport_addedExponent_zero
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .oneTwoBirth
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      target.canonicalPresentation.topology.counts =
        source.canonicalPresentation.topology.counts.addOneTwo}
    (data : OneTwoBirthData source target metadata countsSound)
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) :
    (data.exponentTransport sourceCycle).addedExponent 0 = 0 :=
  rfl

end OneTwoBirthData

namespace OneTwoDeathData

/-- Reverse 1--2 exponent transport, derived from handle-chain naturality. -/
noncomputable def exponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      source.canonicalPresentation.topology.counts =
        target.canonicalPresentation.topology.counts.addOneTwo}
    (data : OneTwoDeathData source target metadata countsSound)
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) :
    data.reverseBirth.ordinaryChange.ExponentTransport targetCycle
      ((CycleTransport.ofMarkedH2TransportInverse
        source.canonicalPresentation target.canonicalPresentation
        (moveTransport (.oneTwoDeath metadata countsSound))).targetCycle
          targetCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).oneTwoDeathCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      addedExponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro targetIndex
    calc
      source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            (data.reverseBirth.ordinaryChange.targetDecomposition.symm
              (Sum.inl targetIndex)).1) =
        source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            ((oneTwoDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inl targetIndex.1))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          (data.common_component_alignment targetIndex)
      _ = target.canonicalPresentation.cycleComponentExponent targetCycle
          (componentAt target.canonicalPresentation.topology.formal
            targetIndex.1) :=
        coordinateLaw.common_exponent_sound targetCycle targetIndex.1
  · intro addedIndex
    have addedIndex_eq : addedIndex = (0 : Fin 1) := Subsingleton.elim _ _
    subst addedIndex
    calc
      source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            (data.reverseBirth.ordinaryChange.targetDecomposition.symm
              (Sum.inr (0 : Fin 1))).1) =
        source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.oneTwoDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            ((oneTwoDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inr secondOfTwo))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          data.added_component_alignment
      _ = 0 :=
        coordinateLaw.removed_exponent_zero targetCycle secondOfTwo

@[simp]
theorem exponentTransport_addedExponent_zero
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .oneTwoDeath
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      source.canonicalPresentation.topology.counts =
        target.canonicalPresentation.topology.counts.addOneTwo}
    (data : OneTwoDeathData source target metadata countsSound)
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) :
    (data.exponentTransport targetCycle).addedExponent 0 = 0 :=
  rfl

end OneTwoDeathData

namespace TwoThreeBirthData

/-- Forward 2--3 exponent transport, derived from handle-chain naturality. -/
noncomputable def exponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      target.canonicalPresentation.topology.counts =
        source.canonicalPresentation.topology.counts.addTwoThree}
    (data : TwoThreeBirthData source target metadata countsSound)
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) :
    data.topology.ordinaryChange.ExponentTransport sourceCycle
      ((CycleTransport.ofMarkedH2Transport
        source.canonicalPresentation target.canonicalPresentation
        (moveTransport (.twoThreeBirth metadata countsSound))).targetCycle
          sourceCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).twoThreeBirthCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      addedExponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro sourceIndex
    calc
      target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            (data.topology.ordinaryChange.targetDecomposition.symm
              (Sum.inl sourceIndex)).1) =
        target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            ((twoThreeBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inl sourceIndex.1))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          (data.common_component_alignment sourceIndex)
      _ = source.canonicalPresentation.cycleComponentExponent sourceCycle
          (componentAt source.canonicalPresentation.topology.formal
            sourceIndex.1) :=
        coordinateLaw.common_exponent_sound sourceCycle sourceIndex.1
  · intro addedIndex
    have addedIndex_eq : addedIndex = (0 : Fin 1) := Subsingleton.elim _ _
    subst addedIndex
    calc
      target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            (data.topology.ordinaryChange.targetDecomposition.symm
              (Sum.inr (0 : Fin 1))).1) =
        target.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2Transport
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeBirth metadata countsSound))).targetCycle
              sourceCycle)
          (componentAt target.canonicalPresentation.topology.formal
            ((twoThreeBirthAddedChange metadata).targetDecomposition.symm
              (Sum.inr onlyOne))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          data.added_component_alignment
      _ = 0 :=
        coordinateLaw.added_exponent_zero sourceCycle onlyOne

@[simp]
theorem exponentTransport_addedExponent_zero
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .twoThreeBirth
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      target.canonicalPresentation.topology.counts =
        source.canonicalPresentation.topology.counts.addTwoThree}
    (data : TwoThreeBirthData source target metadata countsSound)
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) :
    (data.exponentTransport sourceCycle).addedExponent 0 = 0 :=
  rfl

end TwoThreeBirthData

namespace TwoThreeDeathData

/-- Reverse 2--3 exponent transport, derived from handle-chain naturality. -/
noncomputable def exponentTransport
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      source.canonicalPresentation.topology.counts =
        target.canonicalPresentation.topology.counts.addTwoThree}
    (data : TwoThreeDeathData source target metadata countsSound)
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) :
    data.reverseBirth.ordinaryChange.ExponentTransport targetCycle
      ((CycleTransport.ofMarkedH2TransportInverse
        source.canonicalPresentation target.canonicalPresentation
        (moveTransport (.twoThreeDeath metadata countsSound))).targetCycle
          targetCycle) := by
  let coordinateLaw :=
    (standardHandleChainNaturality H2).twoThreeDeathCoordinates
      metadata countsSound
  refine
    { common_exponent_sound := ?_
      addedExponent := fun _ => 0
      added_exponent_sound := ?_ }
  · intro targetIndex
    calc
      source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            (data.reverseBirth.ordinaryChange.targetDecomposition.symm
              (Sum.inl targetIndex)).1) =
        source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            ((twoThreeDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inl targetIndex.1))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          (data.common_component_alignment targetIndex)
      _ = target.canonicalPresentation.cycleComponentExponent targetCycle
          (componentAt target.canonicalPresentation.topology.formal
            targetIndex.1) :=
        coordinateLaw.common_exponent_sound targetCycle targetIndex.1
  · intro addedIndex
    have addedIndex_eq : addedIndex = (0 : Fin 1) := Subsingleton.elim _ _
    subst addedIndex
    calc
      source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            (data.reverseBirth.ordinaryChange.targetDecomposition.symm
              (Sum.inr (0 : Fin 1))).1) =
        source.canonicalPresentation.cycleComponentExponent
          ((CycleTransport.ofMarkedH2TransportInverse
            source.canonicalPresentation target.canonicalPresentation
            (moveTransport (.twoThreeDeath metadata countsSound))).targetCycle
              targetCycle)
          (componentAt source.canonicalPresentation.topology.formal
            ((twoThreeDeathRemovedChange metadata).sourceDecomposition.symm
              (Sum.inr onlyOne))) :=
        cycleComponentExponent_eq_of_componentId_eq _ _ _ _
          data.added_component_alignment
      _ = 0 :=
        coordinateLaw.removed_exponent_zero targetCycle onlyOne

@[simp]
theorem exponentTransport_addedExponent_zero
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {metadata :
      TableTwoMoveMetadata .twoThreeDeath
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    {countsSound :
      source.canonicalPresentation.topology.counts =
        target.canonicalPresentation.topology.counts.addTwoThree}
    (data : TwoThreeDeathData source target metadata countsSound)
    (targetCycle : target.canonicalPresentation.DegreeTwoCycle) :
    (data.exponentTransport targetCycle).addedExponent 0 = 0 :=
  rfl

end TwoThreeDeathData

/--
Framed-isotopy exponent transport is derived from the handle-chain theorem
after the local factorization identifies the same component correspondence.
-/
noncomputable def framedIsotopyExponentTransport
    {H2 : Type uH} [AddCommGroup H2]
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
        source.canonicalPresentation target.canonicalPresentation)
    (componentChangeSound :
      geometry.componentChange = framedIsotopySameChange metadata)
    (sourceCycle : source.canonicalPresentation.DegreeTwoCycle) :
    SameComponentCycleExponentTransport
      source.canonicalPresentation target.canonicalPresentation
      geometry.componentChange sourceCycle
      ((CycleTransport.ofMarkedH2Transport
        source.canonicalPresentation target.canonicalPresentation
        (moveTransport (.framedIsotopy metadata countsSound))).targetCycle
          sourceCycle) := by
  rw [componentChangeSound]
  let coordinateLaw :=
    (standardHandleChainNaturality H2).framedIsotopyCoordinates
      metadata countsSound
  exact
    { exponent_sound := fun targetIndex =>
        coordinateLaw.exponent_sound sourceCycle targetIndex }

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
          source.canonicalPresentation target.canonicalPresentation)
      (componentChangeSound :
        geometry.componentChange = framedIsotopySameChange metadata)
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
      (compiled :
        SourceBoundUnitCutGeometry.CleanOneOverOneMovie
          source.canonicalPresentation target.canonicalPresentation metadata)
      (sourceGeometry :
        compiled.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        compiled.targetGeometry = target.simultaneousGeometry) :
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
      (compiled :
        SourceBoundUnitCutGeometry.CleanTwoOverOneMovie
          source.canonicalPresentation target.canonicalPresentation metadata)
      (sourceGeometry :
        compiled.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        compiled.targetGeometry = target.simultaneousGeometry) :
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
      (clean :
        RoleAwareTwoOverTwoBandMovie.CleanWindow
          source.canonicalPresentation target.canonicalPresentation
          metadata countsSound)
      (sourceGeometry :
        clean.window.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        clean.window.targetGeometry = target.simultaneousGeometry) :
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
        OneTwoBirthData source target metadata countsSound) :
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
        OneTwoDeathData source target metadata countsSound) :
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
        TwoThreeBirthData source target metadata countsSound) :
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
        TwoThreeDeathData source target metadata countsSound) :
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
  | .framedIsotopy metadata countsSound _ _ _ _ =>
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
The purely topological local factorization attached to one standard Table 2
move.

The eight constructors make the event kind, orientation-bearing metadata,
source/target geometry, and local movie data mechanically visible.  No
constructor mentions a category, character, scalar, or evaluator equality.
-/
inductive StandardMoveLocalFactorization
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2} :
    TopologicalTableTwoMove
      source.canonicalPresentation.topology
      target.canonicalPresentation.topology →
      Type (uH + 1)
  | framedIsotopy
      (metadata :
        TableTwoMoveMetadata .framedIsotopy
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (geometry :
        RoleAwareFramedIsotopy.Geometry
          source.canonicalPresentation target.canonicalPresentation)
      (componentChangeSound :
        geometry.componentChange = framedIsotopySameChange metadata)
      (sourceGeometry :
        geometry.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        geometry.targetGeometry = target.simultaneousGeometry) :
      StandardMoveLocalFactorization
        (.framedIsotopy metadata countsSound)
  | oneOverOne
      (metadata :
        TableTwoMoveMetadata .oneOverOne
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (compiled :
        SourceBoundUnitCutGeometry.CleanOneOverOneMovie
          source.canonicalPresentation target.canonicalPresentation metadata)
      (sourceGeometry :
        compiled.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        compiled.targetGeometry = target.simultaneousGeometry) :
      StandardMoveLocalFactorization
        (.oneOverOne metadata countsSound)
  | twoOverOne
      (metadata :
        TableTwoMoveMetadata .twoOverOne
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (compiled :
        SourceBoundUnitCutGeometry.CleanTwoOverOneMovie
          source.canonicalPresentation target.canonicalPresentation metadata)
      (sourceGeometry :
        compiled.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        compiled.targetGeometry = target.simultaneousGeometry) :
      StandardMoveLocalFactorization
        (.twoOverOne metadata countsSound)
  | twoOverTwo
      (metadata :
        TableTwoMoveMetadata .twoOverTwo
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts)
      (clean :
        RoleAwareTwoOverTwoBandMovie.CleanWindow
          source.canonicalPresentation target.canonicalPresentation
          metadata countsSound)
      (sourceGeometry :
        clean.window.sourceGeometry = source.simultaneousGeometry)
      (targetGeometry :
        clean.window.targetGeometry = target.simultaneousGeometry) :
      StandardMoveLocalFactorization
        (.twoOverTwo metadata countsSound)
  | oneTwoBirth
      (metadata :
        TableTwoMoveMetadata .oneTwoBirth
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        target.canonicalPresentation.topology.counts =
          source.canonicalPresentation.topology.counts.addOneTwo)
      (data :
        OneTwoBirthData source target metadata countsSound) :
      StandardMoveLocalFactorization
        (.oneTwoBirth metadata countsSound)
  | oneTwoDeath
      (metadata :
        TableTwoMoveMetadata .oneTwoDeath
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts.addOneTwo)
      (data :
        OneTwoDeathData source target metadata countsSound) :
      StandardMoveLocalFactorization
        (.oneTwoDeath metadata countsSound)
  | twoThreeBirth
      (metadata :
        TableTwoMoveMetadata .twoThreeBirth
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        target.canonicalPresentation.topology.counts =
          source.canonicalPresentation.topology.counts.addTwoThree)
      (data :
        TwoThreeBirthData source target metadata countsSound) :
      StandardMoveLocalFactorization
        (.twoThreeBirth metadata countsSound)
  | twoThreeDeath
      (metadata :
        TableTwoMoveMetadata .twoThreeDeath
          source.canonicalPresentation.topology
          target.canonicalPresentation.topology)
      (countsSound :
        source.canonicalPresentation.topology.counts =
          target.canonicalPresentation.topology.counts.addTwoThree)
      (data :
        TwoThreeDeathData source target metadata countsSound) :
      StandardMoveLocalFactorization
        (.twoThreeDeath metadata countsSound)

namespace StandardMoveLocalFactorization

/-- Compile a topology-only local factorization into the exact role-aware move. -/
def compile
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology} :
    StandardMoveLocalFactorization move →
      ElementaryMove source target
  | .framedIsotopy metadata countsSound geometry componentChangeSound
      sourceGeometry targetGeometry =>
      .framedIsotopy metadata countsSound geometry componentChangeSound
        sourceGeometry targetGeometry
  | .oneOverOne metadata countsSound compiled sourceGeometry targetGeometry =>
      .oneOverOne metadata countsSound compiled sourceGeometry targetGeometry
  | .twoOverOne metadata countsSound compiled sourceGeometry targetGeometry =>
      .twoOverOne metadata countsSound compiled sourceGeometry targetGeometry
  | .twoOverTwo metadata countsSound clean sourceGeometry targetGeometry =>
      .twoOverTwo metadata countsSound clean sourceGeometry targetGeometry
  | .oneTwoBirth metadata countsSound data =>
      .oneTwoBirth metadata countsSound data
  | .oneTwoDeath metadata countsSound data =>
      .oneTwoDeath metadata countsSound data
  | .twoThreeBirth metadata countsSound data =>
      .twoThreeBirth metadata countsSound data
  | .twoThreeDeath metadata countsSound data =>
      .twoThreeDeath metadata countsSound data

/-- The explicit compiler cannot change the underlying standard Kirby move. -/
theorem forget_compile
    {H2 : Type uH} [AddCommGroup H2]
    {source target : Presentation H2}
    {move :
      TopologicalTableTwoMove
        source.canonicalPresentation.topology
        target.canonicalPresentation.topology}
    (factorization : StandardMoveLocalFactorization move) :
    factorization.compile.forget = move := by
  cases factorization <;> rfl

end StandardMoveLocalFactorization

/--
The derived local-geometry compiler consumed by the evaluator proof.

Values of this structure should be assembled from explicit local
factorizations; the public topology boundary no longer assumes one wholesale.
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
