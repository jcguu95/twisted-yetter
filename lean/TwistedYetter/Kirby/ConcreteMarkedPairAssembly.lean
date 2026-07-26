import TwistedYetter.Kirby.HomologicallyTwistedInvariant
import TwistedYetter.Kirby.SourceBackedKirbyCompleteness

/-!
# Marked-pair assembly from local chain data

Every special presentation already identifies the second homology of its
handle chain complex with one fixed geometric model `H2`.  A local Kirby move
is correctly marked only when its chain-induced map becomes the identity in
those shared geometric coordinates.

This module records that local condition once, proves by induction that every
source-backed Table 2 movie acts as the identity on the geometric model, and
constructs `MarkedPairPresentationSystem` with no handwritten
`marked_transport_sound` field.

The local chain equivalences and their identity-in-geometric-coordinates laws
remain explicit inputs.  This is the intended interface to standard
functoriality of handle homology, not a claim that the current raw diagram
schema computes those chain maps automatically.
-/

namespace TwistedYetter.Kirby.ConcreteMarkedPairAssembly

open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uH

/--
Local handle-chain compiler with the exact geometric-coordinate law.

The map on `H2` is still derived from `transport.chainEquivalence`; the
identity law only certifies that the source and target coordinate
identifications both refer to the same geometric `H2(X)`.
-/
structure GeometricMarkedH2Compiler
    (H2 : Type uH) [AddCommGroup H2] where
  localCompiler : LocalMarkedH2Compiler H2
  transport_is_identity :
    {source target : SpecialKirbyPresentation H2} →
    (move : TopologicalTableTwoMove source target) →
      (localCompiler.transport move).homologyAddEquiv =
        AddEquiv.refl H2

namespace GeometricMarkedH2Compiler

/-- Every locally compiled transport fixes each geometric marked class. -/
theorem local_targetClass_eq
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : GeometricMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target)
    (alpha : H2) :
    (compiler.localCompiler.transport move).targetClass alpha = alpha := by
  change (compiler.localCompiler.transport move).homologyAddEquiv alpha =
    alpha
  rw [compiler.transport_is_identity move]
  rfl

/-- Enriching one bare topology move preserves its geometric class. -/
theorem enrichMove_targetClass_eq
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : GeometricMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (move : TopologicalTableTwoMove source target)
    (alpha : H2) :
    (enrichMove compiler.localCompiler move).homologyTransport.targetClass
        alpha =
      alpha := by
  cases move with
  | framedIsotopy metadata counts =>
      exact compiler.local_targetClass_eq
        (.framedIsotopy metadata counts) alpha
  | oneOverOne metadata counts =>
      exact compiler.local_targetClass_eq
        (.oneOverOne metadata counts) alpha
  | twoOverOne metadata counts =>
      exact compiler.local_targetClass_eq
        (.twoOverOne metadata counts) alpha
  | twoOverTwo metadata counts =>
      exact compiler.local_targetClass_eq
        (.twoOverTwo metadata counts) alpha
  | oneTwoBirth metadata counts =>
      exact compiler.local_targetClass_eq
        (.oneTwoBirth metadata counts) alpha
  | oneTwoDeath metadata counts =>
      exact compiler.local_targetClass_eq
        (.oneTwoDeath metadata counts) alpha
  | twoThreeBirth metadata counts =>
      exact compiler.local_targetClass_eq
        (.twoThreeBirth metadata counts) alpha
  | twoThreeDeath metadata counts =>
      exact compiler.local_targetClass_eq
        (.twoThreeDeath metadata counts) alpha

/-- Every enriched source-backed movie fixes the geometric marked class. -/
theorem enrichMovie_targetClass_eq
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : GeometricMarkedH2Compiler H2)
    {source target : SpecialKirbyPresentation H2}
    (movie : TopologicalTableTwoMovie source target)
    (alpha : H2) :
    (enrichMovie compiler.localCompiler movie).targetClass alpha =
      alpha := by
  induction movie generalizing alpha with
  | refl presentation =>
      rfl
  | step move =>
      exact compiler.enrichMove_targetClass_eq move alpha
  | trans first second firstIH secondIH =>
      change
        (enrichMovie compiler.localCompiler second).targetClass
            ((enrichMovie compiler.localCompiler first).targetClass alpha) =
          alpha
      rw [secondIH, firstIH]

/-- Source-backed completeness enriched with the supplied local chain maps. -/
noncomputable def tableTwoCompleteness
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : GeometricMarkedH2Compiler H2)
    (generalCerf : GeneralCerfCompleteness) :
    TableTwoLinkCompleteness H2 :=
  buildTableTwoLinkCompleteness generalCerf
    (movieEnrichmentOfLocalCompiler compiler.localCompiler)

/-- The exact completeness movie used by the assembly fixes geometric `H2`. -/
theorem completeness_targetClass_eq
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : GeometricMarkedH2Compiler H2)
    (generalCerf : GeneralCerfCompleteness)
    (source target : SpecialKirbyPresentation H2)
    (alpha : H2) :
    ((compiler.tableTwoCompleteness generalCerf).tableTwoConnected
        source target).targetClass alpha =
      alpha := by
  exact compiler.enrichMovie_targetClass_eq
    (standardSpecialKirbyPresentationsConnected source target) alpha

/--
Canonical marked-pair system.

The presentation coordinate is the shared geometric class itself.  The
transport law is derived from the local chain compiler rather than supplied
as an independent proposition.
-/
noncomputable def markedPairSystem
    {H2 : Type uH} [AddCommGroup H2]
    (compiler : GeometricMarkedH2Compiler H2)
    (generalCerf : GeneralCerfCompleteness)
    (basePresentation : SpecialKirbyPresentation H2) :
    MarkedPairPresentationSystem H2 where
  completeness := compiler.tableTwoCompleteness generalCerf
  represents := fun _ coordinate geometricClass =>
    coordinate = geometricClass
  chosenPresentation := fun _ => basePresentation
  chosenCoordinate := fun alpha => alpha
  chosen_represents := fun _ => rfl
  marked_transport_sound := by
    intro source target sourceCoordinate targetCoordinate geometricClass
      sourceRepresents targetRepresents
    rw [sourceRepresents, targetRepresents]
    exact compiler.completeness_targetClass_eq
      generalCerf source target geometricClass

end GeometricMarkedH2Compiler

end TwistedYetter.Kirby.ConcreteMarkedPairAssembly
