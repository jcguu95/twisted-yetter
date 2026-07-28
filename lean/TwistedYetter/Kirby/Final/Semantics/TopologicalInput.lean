import TwistedYetter.Kirby.Final.Semantics.MoveAssembly

/-!
# Four-manifold, presentation, H₂, and Kirby--Cerf semantics

This layer contains no category or evaluator.
-/

namespace TwistedYetter.Kirby.Final.SemanticSpecification

universe uX uH uD uP

/-- The externally supplied manifold and integral-homology semantics. -/
structure ClosedFourManifoldSemantics where
  Manifold : Type uX
  H₂ : Manifold → Type uH
  h₂AddCommGroup : (X : Manifold) → AddCommGroup (H₂ X)
  OrientedDiffeomorphism : Manifold → Manifold → Type uD
  inducedH₂ :
    {X Y : Manifold} →
      OrientedDiffeomorphism X Y →
        H₂ X ≃+ H₂ Y

attribute [instance] ClosedFourManifoldSemantics.h₂AddCommGroup

/-- The intended public topological input is exactly a dependent pair `(X, α)`. -/
abbrev HomologicalFourManifold
    (topology : ClosedFourManifoldSemantics) :=
  Σ X : topology.Manifold, topology.H₂ X

/-- A presentation family is indexed by the manifold it presents. -/
abbrev PresentationFamily
    (topology : ClosedFourManifoldSemantics) :=
  topology.Manifold → Type uP

/--
The human meaning of presentation realization.

Every presentation has its own handle-chain second homology.  That group is
identified with `H₂ X` for the manifold indexing the presentation.  No single
auxiliary group is shared by all manifolds.
-/
structure PresentationRealization
    (topology : ClosedFourManifoldSemantics)
    (Presentation : PresentationFamily.{uX, uP} topology) where
  Realizes :
    {X : topology.Manifold} →
      Presentation X → topology.Manifold → Prop
  realizedManifold :
    {X : topology.Manifold} → Presentation X → topology.Manifold
  realizationDiffeomorphism :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        topology.OrientedDiffeomorphism
          (realizedManifold presentation) X
  realizes_realizedManifold :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        Realizes presentation (realizedManifold presentation)
  HandleH₂ :
    {X : topology.Manifold} → Presentation X → Type uH
  handleH₂AddCommGroup :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        AddCommGroup (HandleH₂ presentation)
  handleH₂EquivRealized :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        HandleH₂ presentation ≃+
          topology.H₂ (realizedManifold presentation)

attribute [instance] PresentationRealization.handleH₂AddCommGroup

namespace PresentationRealization

/-- The induced identification from handle homology to the displayed `H₂ X`. -/
def handleH₂Equiv
    {topology : ClosedFourManifoldSemantics}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (realization : PresentationRealization topology Presentation)
    {X : topology.Manifold}
    (presentation : Presentation X) :
    realization.HandleH₂ presentation ≃+ topology.H₂ X :=
  (realization.handleH₂EquivRealized presentation).trans
    (topology.inducedH₂
      (realization.realizationDiffeomorphism presentation))

end PresentationRealization

/--
Expose the exact admitted presentation atoms used by the independent move
specification.

The outer presentation may carry realization certificates, but its Kirby
data cannot be replaced by an arbitrary relation or a move tag.
-/
structure ExactPresentationView
    {topology : ClosedFourManifoldSemantics}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (realization : PresentationRealization topology Presentation) where
  exact :
    {X : topology.Manifold} →
      Presentation X →
        SemanticEightMoves.Presentation (topology.H₂ X)
  realizationHandleH₂Equiv :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        realization.HandleH₂ presentation ≃+
          (exact presentation).handleChain.SecondHomology
  realization_square :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        (realizationHandleH₂Equiv presentation).trans
            (exact presentation).handleH₂Equiv =
          realization.handleH₂Equiv presentation

/--
An elementary semantic move is now exactly one of the eight independent
constructors in `SemanticEightMoves`.  There is no user-supplied move
relation, predicate, tag dispatch, or evaluator equality.
-/
abbrev ElementaryMove
    {topology : ClosedFourManifoldSemantics}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (view : ExactPresentationView realization)
    {X : topology.Manifold}
    (source target : Presentation X) :=
  SemanticEightMoves.ElementaryMove
    (view.exact source) (view.exact target)

/-- A Kirby movie is a finite composite of the eight elementary moves. -/
inductive KirbyMovie
    {topology : ClosedFourManifoldSemantics}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (view : ExactPresentationView realization)
    {X : topology.Manifold} :
    Presentation X → Presentation X → Type _
  | refl (presentation) :
      KirbyMovie view presentation presentation
  | elementary {source target} :
      ElementaryMove view source target →
        KirbyMovie view source target
  | symm {source target} :
      KirbyMovie view source target →
        KirbyMovie view target source
  | trans {source middle target} :
      KirbyMovie view source middle →
      KirbyMovie view middle target →
        KirbyMovie view source target

/--
A marked movie is a finite Kirby movie together with the single actual class
`α ∈ H₂(X)` that remains fixed throughout its elementary steps.
-/
structure MarkedKirbyMovie
    {topology : ClosedFourManifoldSemantics}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (view : ExactPresentationView realization)
    {X : topology.Manifold}
    (source target : Presentation X)
    (alpha : topology.H₂ X) where
  movie : KirbyMovie view source target

/--
Presentation existence: every closed oriented smooth four-manifold has at
least one admissible special Kirby presentation.
-/
def PresentationExistence
    {topology : ClosedFourManifoldSemantics}
    (Presentation : PresentationFamily.{uX, uP} topology) :
    Prop :=
  ∀ X : topology.Manifold, Nonempty (Presentation X)

/--
Reindexing changes only which diffeomorphic manifold a presentation is
declared to present; it does not insert a Kirby move or evaluator equality.
-/
structure PresentationReindexing
    {topology : ClosedFourManifoldSemantics}
    (Presentation : PresentationFamily.{uX, uP} topology) where
  reindex :
    {X Y : topology.Manifold} →
      topology.OrientedDiffeomorphism X Y →
        Presentation X → Presentation Y

/--
Marked Kirby--Cerf completeness.

After reindexing a source presentation along an oriented diffeomorphism
`X → Y`, every source and target presentation is connected by a finite movie
made only from the eight declared elementary relations.
-/
def KirbyCerfComplete
    {topology : ClosedFourManifoldSemantics}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (view : ExactPresentationView realization)
    (reindexing : PresentationReindexing Presentation) :
    Prop :=
  ∀ {X Y : topology.Manifold}
    (f : topology.OrientedDiffeomorphism X Y)
    (source : Presentation X)
    (target : Presentation Y)
    (α : topology.H₂ X),
      Nonempty
        (MarkedKirbyMovie view
          (reindexing.reindex f source)
          target
          (topology.inducedH₂ f α))

end TwistedYetter.Kirby.Final.SemanticSpecification

