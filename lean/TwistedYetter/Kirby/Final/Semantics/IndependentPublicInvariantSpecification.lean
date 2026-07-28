import TwistedYetter.Kirby.Final.Semantics.IndependentEvaluatorSpecification
import TwistedYetter.Kirby.Final.Semantics.IndependentMoveHomologyTransportSpecification

/-!
# Independent human specification of the public invariant

This file is normative.  It was written without importing or inspecting this
repository's topological input, descent, public invariant, final theorem,
compatibility bridge, evaluator implementation, or computation code.

It separates three logically different statements:

1. the explicit cycle-level formula is independent of all auxiliary choices,
   and hence defines a value on `(D, α)`;
2. the value on `(D, α)` is invariant under each of the eight elementary
   marked Kirby moves, and hence under a finite Kirby movie;
3. classical marked Kirby--Cerf topology identifies presentations of the
   same marked closed four-manifold, so the diagram-level value descends to
   `(X, α)`.

No topology boundary in this file contains a category, character, ribbon
diagram, evaluator, or scalar equality.
-/

namespace TwistedYetter.Kirby.Final.IndependentPublicInvariantSpecification

open CategoryTheory
open IndependentAlgebraicInput
open IndependentPresentationSpecification
open IndependentHomologyMarkingSpecification
open IndependentMoveHomologyTransportSpecification
open IndependentGraphicalCalculusSpecification
open IndependentEvaluatorSpecification

universe
  uK uC vC
  uKnot uFramed uDisk uPoint uBunching uThreeManifold
  uManifold uH uDiffeomorphism

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

variable
  {geometry : KirbyGeometrySemantics}

/--
The classical manifold-level objects deliberately not reconstructed here.

`H₂ X` is a bundled integral module, so it may have arbitrary rank and
torsion.  An oriented diffeomorphism carries an explicit induced isomorphism
on H₂.  Identity, composition, and inverse laws are part of this topology
boundary.
-/
structure ClosedOrientedSmoothFourManifoldSemantics where
  Manifold : Type uManifold
  H₂ : Manifold → ModuleCat.{uH} ℤ

  OrientedDiffeomorphism :
    Manifold → Manifold → Type uDiffeomorphism
  identity :
    (X : Manifold) → OrientedDiffeomorphism X X
  compose :
    {X Y Z : Manifold} →
      OrientedDiffeomorphism X Y →
      OrientedDiffeomorphism Y Z →
      OrientedDiffeomorphism X Z
  inverse :
    {X Y : Manifold} →
      OrientedDiffeomorphism X Y →
      OrientedDiffeomorphism Y X

  inducedH₂ :
    {X Y : Manifold} →
      OrientedDiffeomorphism X Y →
      (H₂ X ≅ H₂ Y)
  inducedH₂_identity :
    (X : Manifold) →
      inducedH₂ (identity X) = Iso.refl (H₂ X)
  inducedH₂_compose :
    {X Y Z : Manifold} →
    (f : OrientedDiffeomorphism X Y) →
    (g : OrientedDiffeomorphism Y Z) →
      inducedH₂ (compose f g) =
        inducedH₂ f ≪≫ inducedH₂ g
  inducedH₂_inverse :
    {X Y : Manifold} →
    (f : OrientedDiffeomorphism X Y) →
      inducedH₂ (inverse f) =
        (inducedH₂ f).symm

/--
Topology boundary R: the special Kirby diagram closes to the named smooth,
closed, connected, oriented four-manifold.

This proposition mentions no category, character, evaluator, or scalar.
-/
axiom DiagramRealizesClosedFourManifold
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (diagram : SpecialKirbyDiagram geometry)
    (X : topology.Manifold) :
    Prop

/--
One certified realization of a closed four-manifold by a special Kirby
diagram.

The H₂ comparison is an additive isomorphism, not a definitional
identification and not an abbreviation to `ℤ`.
-/
structure SpecialKirbyRealization
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (geometry : KirbyGeometrySemantics)
    (X : topology.Manifold) where
  diagram : SpecialKirbyDiagram geometry
  realizes :
    DiagramRealizesClosedFourManifold topology diagram X
  h₂Comparison :
    KirbyH₂ diagram ≃+ topology.H₂ X

/--
A realization of the marked pair `(X, α)`.

`diagramMarking` is the unique diagram-side input used by the evaluator.
The displayed equation is the only legal bridge to the manifold class
`α`.
-/
structure MarkedSpecialKirbyRealization
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (geometry : KirbyGeometrySemantics)
    (X : topology.Manifold)
    (α : topology.H₂ X) where
  realization : SpecialKirbyRealization topology geometry X
  diagramMarking : KirbyH₂ realization.diagram
  marking_matches :
    realization.h₂Comparison diagramMarking = α

/--
Topology boundary E: every marked pair `(X, α)` has at least one certified
special Kirby realization.

This is existence only.  It does not choose a preferred diagram and does not
state evaluator equality.
-/
structure MarkedSpecialKirbyExistence
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (geometry : KirbyGeometrySemantics) where
  realization_exists :
    (X : topology.Manifold) →
      (α : topology.H₂ X) →
      Nonempty (MarkedSpecialKirbyRealization topology geometry X α)

/--
The complete diagram-level evaluation theory.

For every special Kirby diagram it supplies the literal topology-to-graph
assembler and the theorem that the explicit cycle formula is independent of
all auxiliary choices.  It therefore produces a function on the actual
quotient `KirbyH₂ diagram`.
-/
structure DiagramEvaluationTheory
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (geometry : KirbyGeometrySemantics) where
  assembly :
    (diagram : SpecialKirbyDiagram geometry) →
      RoleAwareClosedDiagramAssembly 𝒞η graphical diagram
  diagramEvaluator :
    (diagram : SpecialKirbyDiagram geometry) →
      DiagramLevelTwistedYetter
        𝒞η graphical diagram (assembly diagram)

/-- Evaluate the marked special Kirby diagram `(D, α)`. -/
noncomputable def DiagramEvaluationTheory.evaluate
    {𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S)}
    {graphical : EvaluatorGraphicalData 𝒞η.1}
    (theory : DiagramEvaluationTheory 𝒞η graphical geometry)
    (diagram : SpecialKirbyDiagram geometry)
    (α : KirbyH₂ diagram) : K :=
  (theory.diagramEvaluator diagram).evaluate α

/--
The algebraic/topological theorem obligation for the eight elementary moves.

The target marking is not separately supplied: it is exactly the marking
induced by the explicit chain map carried by `move`.
-/
def ElementaryMoveEvaluationInvariant
    {𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S)}
    {graphical : EvaluatorGraphicalData 𝒞η.1}
    (theory : DiagramEvaluationTheory 𝒞η graphical geometry) :
    Prop :=
  ∀ {source target : SpecialKirbyDiagram geometry}
    (move : ElementaryMoveTransport source target)
    (α : KirbyH₂ source),
    theory.evaluate source α =
      theory.evaluate target (move.transportH₂ α)

/--
Finite-movie invariance is a theorem by induction, not a new topology axiom.
-/
theorem kirbyMovie_preserves_evaluation
    {𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S)}
    {graphical : EvaluatorGraphicalData 𝒞η.1}
    (theory : DiagramEvaluationTheory 𝒞η graphical geometry)
    (localInvariant : ElementaryMoveEvaluationInvariant theory) :
    ∀ {source target : SpecialKirbyDiagram geometry}
      (movie : KirbyMovieTransport source target)
      (α : KirbyH₂ source),
      theory.evaluate source α =
        theory.evaluate target (movie.transportH₂ α)
  | _, _, .identity _, _ => rfl
  | _, _, .then first rest, α =>
      (localInvariant first α).trans
        (kirbyMovie_preserves_evaluation
          theory
          localInvariant
          rest
          (first.transportH₂ α))

/--
Topology boundary KC: marked Kirby--Cerf completeness.

Suppose `P` realizes `(X, α)`, `Q` realizes `(Y, β)`, and an oriented
diffeomorphism `f : X → Y` sends `α` to `β`.  Then there is a finite movie
from the exact diagram of `P` to the exact diagram of `Q`, and its chain-map
transport sends the exact diagram marking of `P` to that of `Q`.

This statement contains no category, character, evaluator, or scalar
equality.
-/
structure MarkedKirbyCerfCompleteness
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (geometry : KirbyGeometrySemantics) where
  movie :
    {X Y : topology.Manifold} →
      {α : topology.H₂ X} →
      {β : topology.H₂ Y} →
      (P : MarkedSpecialKirbyRealization topology geometry X α) →
      (Q : MarkedSpecialKirbyRealization topology geometry Y β) →
      (f : topology.OrientedDiffeomorphism X Y) →
      (topology.inducedH₂ f).hom α = β →
      KirbyMovieTransport
        P.realization.diagram
        Q.realization.diagram

  movie_transports_marking :
    {X Y : topology.Manifold} →
      {α : topology.H₂ X} →
      {β : topology.H₂ Y} →
      (P : MarkedSpecialKirbyRealization topology geometry X α) →
      (Q : MarkedSpecialKirbyRealization topology geometry Y β) →
      (f : topology.OrientedDiffeomorphism X Y) →
      (h : (topology.inducedH₂ f).hom α = β) →
      (movie P Q f h).transportH₂ P.diagramMarking =
        Q.diagramMarking

/--
Noncomputably choose one certified special Kirby realization of each marked
pair.  The next theorem proves that the resulting scalar does not depend on
this choice.
-/
noncomputable def chosenMarkedRealization
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (existence : MarkedSpecialKirbyExistence topology geometry)
    (X : topology.Manifold)
    (α : topology.H₂ X) :
    MarkedSpecialKirbyRealization topology geometry X α :=
  Classical.choice (existence.realization_exists X α)

/--
The public invariant has exactly the mathematical input
`((𝒞, η), (X, α))`.

No diagram, cycle, chart, puncture direction, assembler, or presentation
choice is a public argument.
-/
noncomputable def TwistedYetter
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (theory : DiagramEvaluationTheory 𝒞η graphical geometry)
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (existence : MarkedSpecialKirbyExistence topology geometry)
    (Xα : Σ X : topology.Manifold, topology.H₂ X) : K :=
  let presentation :=
    chosenMarkedRealization
      topology existence Xα.1 Xα.2
  theory.evaluate
    presentation.realization.diagram
    presentation.diagramMarking

/--
The final target theorem.

Its only non-foundational proof inputs are:

1. auxiliary-choice independence, already contained in
   `DiagramEvaluationTheory`;
2. the eight source-bound elementary-move evaluation theorems;
3. marked Kirby--Cerf completeness.
-/
theorem TwistedYetter_diffeomorphism_invariant
    (𝒞η : TwistedPremodularCategorySemantics
      (K := K) (C := C) (S := S))
    (graphical : EvaluatorGraphicalData 𝒞η.1)
    (theory : DiagramEvaluationTheory 𝒞η graphical geometry)
    (localInvariant : ElementaryMoveEvaluationInvariant theory)
    (topology : ClosedOrientedSmoothFourManifoldSemantics)
    (existence : MarkedSpecialKirbyExistence topology geometry)
    (completeness : MarkedKirbyCerfCompleteness topology geometry)
    {X Y : topology.Manifold}
    (f : topology.OrientedDiffeomorphism X Y)
    (α : topology.H₂ X) :
    TwistedYetter
        𝒞η graphical theory topology existence ⟨X, α⟩ =
      TwistedYetter
        𝒞η graphical theory topology existence
        ⟨Y, (topology.inducedH₂ f).hom α⟩ := by
  let P :=
    chosenMarkedRealization topology existence X α
  let β :=
    (topology.inducedH₂ f).hom α
  let Q :=
    chosenMarkedRealization topology existence Y β
  let movie :=
    completeness.movie P Q f rfl
  change
    theory.evaluate P.realization.diagram P.diagramMarking =
      theory.evaluate Q.realization.diagram Q.diagramMarking
  calc
    theory.evaluate P.realization.diagram P.diagramMarking =
        theory.evaluate
          Q.realization.diagram
          (movie.transportH₂ P.diagramMarking) :=
      kirbyMovie_preserves_evaluation
        theory localInvariant movie P.diagramMarking
    _ = theory.evaluate
          Q.realization.diagram
          Q.diagramMarking := by
      rw [completeness.movie_transports_marking P Q f rfl]

end TwistedYetter.Kirby.Final.IndependentPublicInvariantSpecification
