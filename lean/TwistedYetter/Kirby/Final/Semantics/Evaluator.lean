import TwistedYetter.Kirby.Final.Semantics.AlgebraicInput
import TwistedYetter.Kirby.Final.Semantics.TopologicalInput

/-!
# Exact role-aware evaluator semantics

Ordinary labels, dotted cuts, finite sums, normalization, and the explicit
obligations for representatives, elementary moves, and reindexing.
-/

namespace TwistedYetter.Kirby.Final.SemanticSpecification

open scoped BigOperators

universe uX uH uD uP uK uM

variable {K : Type uK} [Field K]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
The exact role-aware finite-sum evaluator data.

Ordinary and dotted components have disjoint index types.  Only ordinary
components receive simple labels.  Dotted components enter the diagram only
through the special normalized tensor-unit cut implemented by
`specialCutDiagramEvaluation`.
-/
structure RoleAwareEvaluator
    {topology : ClosedFourManifoldSemantics}
    (AlgebraicInput : Type uM)
    (Presentation : PresentationFamily.{uX, uP} topology)
    (realization : PresentationRealization topology Presentation) where
  OrdinaryComponent :
    {X : topology.Manifold} → Presentation X → Type
  ordinaryComponentFintype :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        Fintype (OrdinaryComponent presentation)
  DottedComponent :
    {X : topology.Manifold} →
      Presentation X → Type
  dottedComponentFintype :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        Fintype (DottedComponent presentation)
  ordinaryLabelingFintype :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        Fintype (OrdinaryComponent presentation → S)
  HandleCycle :
    {X : topology.Manifold} →
      Presentation X → Type uH
  cycleClass :
    {X : topology.Manifold} →
      {presentation : Presentation X} →
        HandleCycle presentation → realization.HandleH₂ presentation
  cycleRepresentative :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
        realization.HandleH₂ presentation → HandleCycle presentation
  cycleRepresentative_class :
    {X : topology.Manifold} →
      (presentation : Presentation X) →
      (homologyClass : realization.HandleH₂ presentation) →
        cycleClass (cycleRepresentative presentation homologyClass) =
          homologyClass
  ordinaryExponent :
    {X : topology.Manifold} →
      {presentation : Presentation X} →
        HandleCycle presentation → OrdinaryComponent presentation → ℤ
  ordinaryCoefficient :
    AlgebraicInput →
    {X : topology.Manifold} →
      (presentation : Presentation X) →
      HandleCycle presentation →
      (OrdinaryComponent presentation → S) →
        K
  specialCutDiagramEvaluation :
    AlgebraicInput →
    {X : topology.Manifold} →
      (presentation : Presentation X) →
      (OrdinaryComponent presentation → S) →
        K
  globalDimension : AlgebraicInput → K
  globalDimension_ne_zero :
    (algebra : AlgebraicInput) → globalDimension algebra ≠ 0
  oneHandleCount :
    {X : topology.Manifold} → Presentation X → ℕ
  twoHandleCount :
    {X : topology.Manifold} → Presentation X → ℕ

attribute [instance] RoleAwareEvaluator.ordinaryComponentFintype
attribute [instance] RoleAwareEvaluator.dottedComponentFintype
attribute [instance] RoleAwareEvaluator.ordinaryLabelingFintype

namespace RoleAwareEvaluator

/-- Simple labels are assigned exactly to ordinary 2-handle components. -/
abbrev OrdinaryLabeling
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    {X : topology.Manifold}
    (presentation : Presentation X) :=
  evaluator.OrdinaryComponent presentation → S

/-- The literal finite sum specified above. -/
noncomputable def rawNumerator
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    (algebra : AlgebraicInput)
    {X : topology.Manifold}
    (presentation : Presentation X)
    (cycle : evaluator.HandleCycle presentation) :
    K :=
  ∑ labeling : evaluator.OrdinaryLabeling presentation,
    evaluator.ordinaryCoefficient algebra presentation cycle labeling *
      evaluator.specialCutDiagramEvaluation algebra presentation labeling

/--
The role-aware normalization:
`D^(h₂-h₁) D^h₁`.  The second factor is the normalized dotted-cut factor;
it is not the dimension of the transparent sector.
-/
noncomputable def denominator
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    (algebra : AlgebraicInput)
    {X : topology.Manifold}
    (presentation : Presentation X) :
    K :=
  evaluator.globalDimension algebra ^
      (Int.ofNat (evaluator.twoHandleCount presentation) -
        Int.ofNat (evaluator.oneHandleCount presentation)) *
    evaluator.globalDimension algebra ^
      Int.ofNat (evaluator.oneHandleCount presentation)

/-- The intended presentation evaluator, with no hidden alternative route. -/
noncomputable def value
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    {realization : PresentationRealization topology Presentation}
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization)
    (algebra : AlgebraicInput)
    {X : topology.Manifold}
    (presentation : Presentation X)
    (α : topology.H₂ X) :
    K :=
  let handleClass := (realization.handleH₂Equiv presentation).symm α
  let cycle := evaluator.cycleRepresentative presentation handleClass
  evaluator.rawNumerator algebra presentation cycle /
    evaluator.denominator algebra presentation

end RoleAwareEvaluator

/--
The raw cycle expression must depend only on the represented handle-homology
class.  This is the explicit descent obligation that was previously hidden by
an arbitrary direct map from `H₂ X` to exponent tables.
-/
def RepresentativeIndependent
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (realization : PresentationRealization topology Presentation)
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization) :
    Prop :=
  ∀ (algebra : AlgebraicInput)
    {X : topology.Manifold}
    (presentation : Presentation X)
    (left right : evaluator.HandleCycle presentation),
      evaluator.cycleClass left = evaluator.cycleClass right →
        evaluator.rawNumerator algebra presentation left =
          evaluator.rawNumerator algebra presentation right

/-- The evaluator equality required for each of the eight move constructors. -/
def PreservesElementaryMoves
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (realization : PresentationRealization topology Presentation)
    (view : ExactPresentationView realization)
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization) :
    Prop :=
  ∀ (algebra : AlgebraicInput)
    {X : topology.Manifold}
    {source target : Presentation X},
      ElementaryMove view source target →
      (α : topology.H₂ X) →
        evaluator.value algebra source α =
          evaluator.value algebra target α

/--
Changing only the manifold index along a diffeomorphism transports the
displayed `H₂` class and does not change the evaluator.
-/
def PreservesReindexing
    {topology : ClosedFourManifoldSemantics}
    {AlgebraicInput : Type uM}
    {Presentation : PresentationFamily.{uX, uP} topology}
    (realization : PresentationRealization topology Presentation)
    (reindexing : PresentationReindexing Presentation)
    (evaluator :
      RoleAwareEvaluator
        (K := K) (S := S) AlgebraicInput Presentation realization) :
    Prop :=
  ∀ (algebra : AlgebraicInput)
    {X Y : topology.Manifold}
    (f : topology.OrientedDiffeomorphism X Y)
    (presentation : Presentation X)
    (α : topology.H₂ X),
      evaluator.value algebra presentation α =
        evaluator.value algebra
          (reindexing.reindex f presentation)
          (topology.inducedH₂ f α)

/-- The mathematical condition required of the final intrinsic invariant. -/
def DiffeomorphismInvariant
    (topology : ClosedFourManifoldSemantics)
    (AlgebraicInput : Type uM)
    (K : Type uK)
    (value : AlgebraicInput → HomologicalFourManifold topology → K) :
    Prop :=
  ∀ (algebra : AlgebraicInput)
    {X Y : topology.Manifold}
    (f : topology.OrientedDiffeomorphism X Y)
    (α : topology.H₂ X),
      value algebra ⟨X, α⟩ =
        value algebra ⟨Y, topology.inducedH₂ f α⟩


end TwistedYetter.Kirby.Final.SemanticSpecification

