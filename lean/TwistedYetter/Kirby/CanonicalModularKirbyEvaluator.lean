import TwistedYetter.Kirby.CanonicalKirbyTrace
import TwistedYetter.Kirby.ComponentRibbonDiagram
import TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
import TwistedYetter.Kirby.HandleChainGeneratorReduction
import TwistedYetter.Kirby.HandleHomologyBoundaryReduction
import TwistedYetter.Kirby.ModularDottedBoundaryCalculation
import TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

/-!
# The canonical modular Kirby evaluator

This module defines the presentation value `Eval_C(P, alpha)` without a
caller-supplied presentation compiler.

The input `CanonicalPresentation` contains only mathematical/combinatorial
presentation data:

* an admitted special Kirby presentation;
* a deterministic index for every serialized link component; and
* the category-neutral canonical local windows from `CanonicalKirbyTrace`.

It contains no category morphism, graphical equality, evaluator function, or
scalar result.  Given a modular category and a tensor automorphism, Lean
constructs all cups, caps, crossings, identity coupons, framing twists,
component weights, finite sums, scalarization, and normalization.

Arbitrary coupons used inside graphical proofs remain genuine morphisms in
`CategoricalTangle.Diagram`.  Ordinary manifold inputs admit only the
`identityCoupon` constructor, so a string label can never select an arbitrary
endomorphism.
-/

namespace TwistedYetter.Kirby.CanonicalModularKirbyEvaluator

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalKirbyTrace
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.HandleChainGeneratorReduction
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.HandleHomologyBoundaryReduction
open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.ModularDottedBoundaryCalculation
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance canonicalSelectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

/--
Deterministic indexing of every component in the serialized registry.

The two equations force `indexOf` to be the inverse of the exact component
list.  It is presentation data, not an evaluator choice.
-/
structure ComponentIndexing (formal : FormalPresentation) where
  indexOf : String → Option (Fin formal.raw.components.length)
  index_roundtrip :
    (index : Fin formal.raw.components.length) →
      indexOf (formal.raw.components.get index).componentId = some index
  index_sound :
    (componentId : String) →
    (index : Fin formal.raw.components.length) →
      indexOf componentId = some index →
        componentId =
          (formal.raw.components.get index).componentId

/--
The exact presentation domain of the canonical evaluator.

No field below can specify the value of a diagram or of the invariant.
-/
structure CanonicalPresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  topology : SpecialKirbyPresentation manifold H2
  componentIndexing : ComponentIndexing topology.formal
  canonicalTrace : ClosedCertificate topology.formal

namespace CanonicalPresentation

/-- One complete assignment of simple labels to serialized components. -/
abbrev GlobalLabeling
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2) :=
  Fin presentation.topology.formal.raw.components.length → S

/-- Resolve a component ID by the presentation's proved finite index. -/
def labelOf
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S))
    (componentId : String) : S :=
  match presentation.componentIndexing.indexOf componentId with
  | some index => labeling index
  | none => 𝒞.premodular.toFusionCategoryData.unitIndex

theorem labelOf_component
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S))
    (index : Fin presentation.topology.formal.raw.components.length) :
    presentation.labelOf 𝒞 labeling
        (presentation.topology.formal.raw.components.get index).componentId =
      labeling index := by
  simp only [labelOf,
    presentation.componentIndexing.index_roundtrip index]

/-- Interpret orientation by the selected simple or its selected right dual. -/
def strandObject
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S))
    (strand : StrandState) : C :=
  (ComponentBoundary.ofStrand strand).interpret
    𝒞.premodular (presentation.labelOf 𝒞 labeling)

end CanonicalPresentation

namespace EventWindow

/--
Canonical categorical interpretation of one category-neutral event window.

There is no morphism argument.  Every primitive is selected by the event
constructor and every exterior is generated by associators, unitors, and
identities through `WindowedCategoricalEvent.toCompiled`.
-/
def compile
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S))
    {event : SliceEvent}
    {before after : List StrandState}
    (window : EventWindow event before after) :
    Diagram C
      (boundaryWord (presentation.strandObject 𝒞 labeling) before)
      (boundaryWord (presentation.strandObject 𝒞 labeling) after) := by
  simpa only [CanonicalPresentation.strandObject] using
    ComponentDiagram.interpretStrandWord
      𝒞.premodular (presentation.labelOf 𝒞 labeling)
      (ComponentRibbonDiagram.EventWindow.componentPrimitive window)

end EventWindow

namespace Trace

/-- Compose canonical local interpretations along a complete typed trace. -/
def compile
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S))
    {events : List SliceEvent}
    {before final : List StrandState} :
    Trace presentation.topology.formal.raw events before final →
      Diagram C
        (boundaryWord (presentation.strandObject 𝒞 labeling) before)
        (boundaryWord (presentation.strandObject 𝒞 labeling) final)
  | trace => by
      simpa only [CanonicalPresentation.strandObject] using
        ComponentDiagram.interpretStrandWord
          𝒞.premodular (presentation.labelOf 𝒞 labeling)
          (ComponentRibbonDiagram.Trace.componentDiagram trace)

/--
The categorical trace compiler is exactly the interpretation of the
category-neutral component diagram.  This prevents the public evaluator and
the topology-side move certificates from using parallel diagram semantics.
-/
theorem compile_eq_componentDiagram_interpret
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S))
    {events : List SliceEvent}
    {before final : List StrandState}
    (trace :
      Trace presentation.topology.formal.raw events before final) :
    Trace.compile 𝒞 presentation labeling trace =
      ComponentDiagram.interpretStrandWord
        𝒞.premodular (presentation.labelOf 𝒞 labeling)
        (ComponentRibbonDiagram.Trace.componentDiagram trace) := by
  rfl

end Trace

namespace CanonicalPresentation

/-- Complete closed component diagram before choosing category labels. -/
def componentTermDiagram
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2) :
    ComponentDiagram .unit .unit :=
  ComponentRibbonDiagram.Trace.componentDiagram
    presentation.canonicalTrace.trace

/-- The complete closed categorical term for one global simple labeling. -/
def termDiagram
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S)) :
    Diagram C .unit .unit :=
  ComponentDiagram.interpretStrandWord
    𝒞.premodular (presentation.labelOf 𝒞 labeling)
    (before := []) (after := [])
    presentation.componentTermDiagram

/-- The public term remains propositionally equal to the recursive compiler. -/
theorem termDiagram_eq_trace_compile
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (presentation : CanonicalPresentation manifold H2)
    (labeling : presentation.GlobalLabeling (S := S)) :
    presentation.termDiagram 𝒞 labeling =
      Trace.compile 𝒞 presentation labeling
        presentation.canonicalTrace.trace :=
  by
    simpa only [termDiagram, componentTermDiagram] using
      (Trace.compile_eq_componentDiagram_interpret
        𝒞 presentation labeling presentation.canonicalTrace.trace).symm

/-- Category-derived normalization profile; no metadata binding is required. -/
noncomputable def normalizationProfile
    (𝒞 : ModularCategory (K := K) (C := C) (S := S)) :
    GlobalDimensionProfile (K := K) :=
  dimensionProfile 𝒞.premodular
    (modularSimpleCenter 𝒞)
    (modularDimensionCertificate 𝒞)

/-- Degree-two cycles of the presentation's actual handle chain. -/
noncomputable abbrev DegreeTwoCycle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2) :=
  presentation.topology.handleChain.complex.cycles 2

/-- Coordinates of an explicit cycle in the two-handle basis. -/
noncomputable def cycleHandleCoefficients
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) :
    Fin presentation.topology.counts.h2 → ℤ :=
  presentation.topology.handleChain.degreeTwoBasis.hom
    (presentation.topology.handleChain.complex.iCycles 2 cycle)

/-- Exponent on one component, read directly from an explicit cycle. -/
noncomputable def cycleComponentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle)
    (component : ComponentSpec) : ℤ :=
  match presentation.topology.twoHandleIndex? component.componentId with
  | none => 0
  | some index => presentation.cycleHandleCoefficients cycle index

/-- Component coefficient before passing from cycles to homology. -/
noncomputable def cycleComponentWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle)
    (component : ComponentSpec)
    (simple : S) : K :=
  𝒞.premodular.quantumDimension simple *
    𝒞.premodular.toFusionCategoryData.automorphismScalarPower
      automorphism simple
      (presentation.cycleComponentExponent cycle component)

/-- Product coefficient for one global labeling of an explicit cycle. -/
noncomputable def cycleGlobalWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle)
    (labeling : presentation.GlobalLabeling (S := S)) : K :=
  ∏ index,
    presentation.cycleComponentWeight 𝒞 automorphism cycle
      (presentation.topology.formal.raw.components.get index)
      (labeling index)

/-- Formal Kirby-colour sum attached to one explicit degree-two cycle. -/
noncomputable def cycleLinearDiagram
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum
    (presentation.cycleGlobalWeight 𝒞 automorphism cycle)
    (presentation.termDiagram 𝒞)

/-- Raw scalar of the explicit-cycle evaluation. -/
noncomputable def cycleRawNumerator
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) : K :=
  𝒞.premodular.toFusionCategoryData.closedScalar
    (LinearDiagram.eval
      (presentation.cycleLinearDiagram 𝒞 automorphism cycle))

/-- The explicit-cycle formal sum evaluates term by term. -/
theorem cycleLinearDiagram_eval
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) :
    LinearDiagram.eval
        (presentation.cycleLinearDiagram 𝒞 automorphism cycle) =
      ∑ labeling,
        presentation.cycleGlobalWeight 𝒞 automorphism cycle labeling •
          Diagram.eval C (presentation.termDiagram 𝒞 labeling) := by
  exact eval_weightedSum _ _

/--
The raw numerator of an explicit cycle is the complete finite sum of its
component coefficient times the closed scalar of each globally labelled
term.
-/
theorem cycleRawNumerator_eq_sum
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) :
    presentation.cycleRawNumerator 𝒞 automorphism cycle =
      ∑ labeling,
        presentation.cycleGlobalWeight 𝒞 automorphism cycle labeling *
          𝒞.premodular.toFusionCategoryData.closedScalar
            (Diagram.eval C
              (presentation.termDiagram 𝒞 labeling)) := by
  classical
  unfold cycleRawNumerator
  rw [presentation.cycleLinearDiagram_eval 𝒞 automorphism cycle]
  change
    𝒞.premodular.toFusionCategoryData.unitEndLinearEquiv.symm
        (∑ labeling,
          presentation.cycleGlobalWeight 𝒞 automorphism cycle labeling •
            Diagram.eval C
              (presentation.termDiagram 𝒞 labeling)) =
      _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro labeling _
  exact
    𝒞.premodular.toFusionCategoryData.closedScalar_smul
      (presentation.cycleGlobalWeight 𝒞 automorphism cycle labeling)
      (Diagram.eval C (presentation.termDiagram 𝒞 labeling))

/-- Evaluation state before quotienting cycles by degree-three boundaries. -/
noncomputable def cycleEvaluationState
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) :
    EvaluationState (K := K) where
  counts := presentation.topology.counts
  rawNumerator :=
    presentation.cycleRawNumerator 𝒞 automorphism cycle

/--
Normalized cycle-colour value on a concrete evaluator-side dual two-cycle.

Descent to `H₂` is not automatic here: it follows only after the boundary
graphical realization below has been constructed.
-/
noncomputable def rawCycleColourEval
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) : K :=
  (presentation.cycleEvaluationState 𝒞 automorphism cycle).normalized
    (normalizationProfile 𝒞)

/--
Compatibility name for `rawCycleColourEval`.
-/
noncomputable abbrev cycleEvalC
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (cycle : presentation.DegreeTwoCycle) : K :=
  presentation.rawCycleColourEval 𝒞 automorphism cycle

/--
Finite local graphical obligations for descending the dual-cycle expression
to `H₂`.

An inhabitant may prove only the movie for one integral multiple of one
stored degree-three generator in front of one existing cycle.  In the
upside-down evaluator these generators are precisely the primal dotted
one-handles.  The caller can no longer postulate the desired equality for an
arbitrary pair of homologous cycles; `HandleChainGeneratorReduction` derives
that global statement from these finite local checks.
-/
structure CycleBoundaryGraphicalRealization
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2) where
  calculateGenerator :
    (cycle : presentation.DegreeTwoCycle) →
    (index : Fin presentation.topology.counts.turnedOver.h3) →
    (coefficient : ℤ) →
    DottedBoundaryLinearCalculation 𝒞 automorphism
      (presentation.cycleLinearDiagram 𝒞 automorphism
        (addBoundary presentation.topology.handleChain cycle
          (coordinateChain presentation.topology.handleChain
            index coefficient)))
      (presentation.cycleLinearDiagram 𝒞 automorphism cycle)

/-- Each required graphical movie gives the corresponding scalar law. -/
theorem CycleBoundaryGraphicalRealization.generatorInvariant
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization :
      CycleBoundaryGraphicalRealization
        𝒞 automorphism presentation) :
    IntegralGeneratorBoundaryInvariant
      presentation.topology.handleChain
      (presentation.cycleEvalC 𝒞 automorphism) := by
  intro cycle index coefficient
  have linearEvaluation :=
    (realization.calculateGenerator cycle index coefficient).eval_eq
  have rawNumerator :=
    congrArg
      𝒞.premodular.toFusionCategoryData.closedScalar
      linearEvaluation
  simp only [cycleEvalC, rawCycleColourEval, cycleEvaluationState,
    cycleRawNumerator, EvaluationState.normalized]
  rw [rawNumerator]

/--
The finite dotted-handle generator movies imply equality on actual `H₂`.

The reduction from an arbitrary degree-three chain to basis generators is a
proved theorem over the presentation's integral handle-chain model; it is not
an evaluator assumption.
-/
theorem CycleBoundaryGraphicalRealization.respects_homology_class
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization :
      CycleBoundaryGraphicalRealization
        𝒞 automorphism presentation)
    (left right : presentation.DegreeTwoCycle)
    (sameClass :
      presentation.topology.handleChain.complex.homologyπ 2 left =
        presentation.topology.handleChain.complex.homologyπ 2 right) :
    presentation.cycleEvalC 𝒞 automorphism left =
      presentation.cycleEvalC 𝒞 automorphism right := by
  exact
    HandleChainGeneratorReduction.respects_homology_class
      presentation.topology.handleChain
      (presentation.cycleEvalC 𝒞 automorphism)
      realization.generatorInvariant left right sameClass

/--
The exact proposition needed for an evaluator to descend from degree-two
cycles to the presentation's actual handle-chain second homology.

This proposition is intentionally separated from any particular graphical
proof language.  A caller may use it only after deriving it from a concrete
certificate such as `DottedBoundaryGeometry.GeometrySystem`.
-/
abbrev CycleRepresentativeIndependence
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2) :=
  ∀ (left right : presentation.DegreeTwoCycle),
    presentation.topology.handleChain.complex.homologyπ 2 left =
        presentation.topology.handleChain.complex.homologyπ 2 right →
      presentation.cycleEvalC 𝒞 automorphism left =
        presentation.cycleEvalC 𝒞 automorphism right

/-- The former graphical realization proves the clean descent proposition. -/
theorem CycleBoundaryGraphicalRealization.representativeIndependence
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization :
      CycleBoundaryGraphicalRealization
        𝒞 automorphism presentation) :
    CycleRepresentativeIndependence 𝒞 automorphism presentation := by
  intro left right sameClass
  exact realization.respects_homology_class
    𝒞 automorphism presentation left right sameClass

/--
Global dual-cycle descent interface.
-/
abbrev CycleBoundaryGraphicalRealizationSystem
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] :=
  (presentation : CanonicalPresentation manifold H2) →
    CycleBoundaryGraphicalRealization 𝒞 automorphism presentation

/--
Clean global descent interface, with no graphical grammar hidden in its name.
The final four-manifold theorem derives this interface from dotted-boundary
geometry rather than accepting it as an independent hypothesis.
-/
abbrev CycleRepresentativeIndependenceSystem
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] :=
  (presentation : CanonicalPresentation manifold H2) →
    CycleRepresentativeIndependence 𝒞 automorphism presentation

/--
A normalized choice of cycle over an actual handle-chain homology class.

This is a section of the quotient map, not a geometrically canonical
representative.  Its value becomes independent of the section only after a
`CycleBoundaryGraphicalRealization` has been proved for the evaluator-side
dual complex.
-/
noncomputable def chosenCycle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.DegreeTwoCycle :=
  (IntegralTwoHandleCycleModel.canonical presentation.topology)
    |>.cycleRepresentative (presentation.topology.h2ModelEquiv alpha)

/-- The chosen cycle represents the requested handle-homology class. -/
theorem chosenCycle_class
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.topology.handleChain.complex.homologyπ 2
        (presentation.chosenCycle alpha) =
      alpha := by
  apply presentation.topology.h2ModelEquiv.injective
  exact
    (IntegralTwoHandleCycleModel.canonical presentation.topology)
      |>.cycle_class_sound (presentation.topology.h2ModelEquiv alpha)

/-- Formal finite Kirby-colour sum after selecting a representative. -/
noncomputable def linearDiagram
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  presentation.cycleLinearDiagram 𝒞 automorphism
    (presentation.chosenCycle alpha)

/-- Raw closed scalar before handle normalization. -/
noncomputable def rawNumerator
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) : K :=
  𝒞.premodular.toFusionCategoryData.closedScalar
    (LinearDiagram.eval
      (presentation.linearDiagram 𝒞 automorphism alpha))

/-- Evaluation state forced by the presentation counts and canonical sum. -/
noncomputable def evaluationState
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    EvaluationState (K := K) where
  counts := presentation.topology.counts
  rawNumerator := presentation.rawNumerator 𝒞 automorphism alpha

/--
The normalized value at one noncomputably chosen dual-cycle section.

Independence from the section is a theorem only in the presence of the
graphical realization above.
-/
noncomputable def chosenCycleSectionValue
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) : K :=
  (presentation.evaluationState 𝒞 automorphism alpha).normalized
    (normalizationProfile 𝒞)

/--
Compatibility name for `chosenCycleSectionValue`.
-/
noncomputable abbrev EvalC
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) : K :=
  presentation.chosenCycleSectionValue 𝒞 automorphism alpha

/--
Conditional comparison with another representative.

The premise is deliberately explicit.  The corrected route must derive it
from dual-chain boundary geometry and the modular dotted-vacuum theorem.
-/
theorem EvalC_eq_cycleEvalC
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (representativeIndependence :
      CycleRepresentativeIndependence
        𝒞 automorphism presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (cycle : presentation.DegreeTwoCycle)
    (cycle_class :
      presentation.topology.handleChain.complex.homologyπ 2 cycle =
      alpha) :
    presentation.EvalC 𝒞 automorphism alpha =
      presentation.cycleEvalC 𝒞 automorphism cycle := by
  apply representativeIndependence
  exact (presentation.chosenCycle_class alpha).trans cycle_class.symm

/-- Compatibility wrapper for the superseded graphical-realization route. -/
theorem EvalC_eq_cycleEvalC_of_graphical_realization
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization :
      CycleBoundaryGraphicalRealization
        𝒞 automorphism presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (cycle : presentation.DegreeTwoCycle)
    (cycle_class :
      presentation.topology.handleChain.complex.homologyπ 2 cycle =
        alpha) :
    presentation.EvalC 𝒞 automorphism alpha =
      presentation.cycleEvalC 𝒞 automorphism cycle := by
  exact presentation.EvalC_eq_cycleEvalC
    𝒞 automorphism
    (realization.representativeIndependence 𝒞 automorphism presentation)
    alpha cycle cycle_class

/-- The formal sum evaluates term by term over all global labelings. -/
theorem linearDiagram_eval
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    LinearDiagram.eval
        (presentation.linearDiagram 𝒞 automorphism alpha) =
      ∑ labeling,
        presentation.cycleGlobalWeight 𝒞 automorphism
            (presentation.chosenCycle alpha) labeling •
          Diagram.eval C (presentation.termDiagram 𝒞 labeling) := by
  exact eval_weightedSum _ _

/--
The raw numerator is the explicit finite sum of coefficient times closed
scalar for every global simple labeling.

This is a linearity theorem for the category-derived scalarization, not an
additional evaluator assumption.
-/
theorem rawNumerator_eq_sum
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.rawNumerator 𝒞 automorphism alpha =
      ∑ labeling,
        presentation.cycleGlobalWeight 𝒞 automorphism
            (presentation.chosenCycle alpha) labeling *
          𝒞.premodular.toFusionCategoryData.closedScalar
            (Diagram.eval C
              (presentation.termDiagram 𝒞 labeling)) := by
  classical
  unfold rawNumerator
  rw [presentation.linearDiagram_eval 𝒞 automorphism alpha]
  change
    𝒞.premodular.toFusionCategoryData.unitEndLinearEquiv.symm
        (∑ labeling,
          presentation.cycleGlobalWeight 𝒞 automorphism
              (presentation.chosenCycle alpha) labeling •
            Diagram.eval C
              (presentation.termDiagram 𝒞 labeling)) =
      _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro labeling _
  exact
    𝒞.premodular.toFusionCategoryData.closedScalar_smul
      (presentation.cycleGlobalWeight 𝒞 automorphism
        (presentation.chosenCycle alpha) labeling)
      (Diagram.eval C (presentation.termDiagram 𝒞 labeling))

/--
The legacy chosen-section value unfolds to its normalized evaluation state.
-/
theorem EvalC_eq_normalized
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.EvalC 𝒞 automorphism alpha =
      (presentation.evaluationState 𝒞 automorphism alpha).normalized
        (normalizationProfile 𝒞) :=
  rfl

end CanonicalPresentation

end TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
