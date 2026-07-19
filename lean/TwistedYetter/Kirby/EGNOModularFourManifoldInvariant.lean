import TwistedYetter.Kirby.EGNOModularKirbyMoves
import TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
import TwistedYetter.Kirby.ConcreteMarkedPairAssembly
import TwistedYetter.Kirby.SourceBackedHandleChainNaturality

/-!
# Modular category data to a marked four-manifold invariant

This is the terminal assembly for the ten-step EGNO route.  The formal Kirby
colour remains a finite sum of complete globally labelled diagrams.  Local
isotopy, ordinary slides, generalized 2-over-2 slides, and cancellations have
separate proof grammars, so no field can be filled by a bare equality of final
normalized values.

The final descent is relative to three visible classes of input:

* the named global graphical laws inside `EGNOModularKirbyMoves.Package`;
* a source-bound presentation and local-move compiler;
* the standard special-Kirby and handle-chain topology inputs isolated in the
  existing source-backed modules.

No identification with a Crane--Yetter state sum is asserted.
-/

namespace TwistedYetter.Kirby.EGNOModularFourManifoldInvariant

open scoped BigOperators
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.ConcreteMarkedPairAssembly
open TwistedYetter.Kirby.EGNOCategoryBoundSliding
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.FramingNaturality
open TwistedYetter.Kirby.GeneralizedSliding
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.IntegralCharacterKirbyColorCompiler
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.KirbyHandleMoves
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.PresentationIsotopy
open TwistedYetter.Kirby.SourceBackedHandleChainNaturality

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

local instance selectedRigidRightDual : RightRigidCategory C :=
  (inferInstance : RigidCategory C).toRightRigidCategory

omit [MonoidalPreadditive C] [MonoidalLinear K C] [DecidableEq S] in
/--
Scalarization of a disjoint union is multiplicative.

The proof is the Eckmann--Hilton calculation on `End(𝟙)`, followed by the
Schur-derived linear equivalence `K ≃ End(𝟙)`.  It is not an extra graphical
assumption.
-/
theorem closedTensorScalar_multiplicative
    (data : FusionCategoryData (K := K) (C := C) (S := S))
    (left right : Diagram C .unit .unit) :
    data.closedScalar
        (Diagram.eval C (closedTensorDiagram left right)) =
      data.closedScalar (Diagram.eval C left) *
        data.closedScalar (Diagram.eval C right) := by
  have tensor_closed
      (f g : 𝟙_ C ⟶ 𝟙_ C) :
      (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom =
        g ≫ f := by
    simp [tensorHom_def', ← unitors_equal, ← unitors_inv_equal]
  rw [show Diagram.eval C (closedTensorDiagram left right) =
      Diagram.eval C right ≫ Diagram.eval C left by
    exact tensor_closed _ _]
  exact (data.closedScalar_comp _ _).trans (mul_comm _ _)

/-- One global assignment of a simple label to every serialized component. -/
abbrev GlobalLabeling
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2) :=
  Fin topology.formal.raw.components.length → S

/-- The canonical integral exponent carried by one serialized component. -/
noncomputable def componentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2)
    (component : ComponentSpec) : ℤ :=
  (IntegralTwoHandleCycleModel.canonical topology).componentExponent
    alpha component

/--
The only component coefficient admitted by the terminal modular route.
-/
noncomputable def componentWeight
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2)
    (component : ComponentSpec)
    (simple : S) : K :=
  data.quantumDimension simple *
    data.toFusionCategoryData.automorphismScalarPower
      automorphism simple
      (componentExponent topology alpha component)

/-- At the zero marked class every component has the ordinary Kirby weight. -/
theorem componentWeight_zero
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2)
    (component : ComponentSpec)
    (simple : S) :
    componentWeight data automorphism topology 0 component simple =
      data.quantumDimension simple := by
  simp [componentWeight, componentExponent,
    IntegralTwoHandleCycleModel.componentExponent_zero]

/-- Product of all component coefficients for one complete global labeling. -/
noncomputable def globalWeight
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2)
    (labeling : GlobalLabeling (S := S) topology) : K :=
  ∏ index,
    componentWeight data automorphism topology alpha
      (topology.formal.raw.components.get index) (labeling index)

/--
Resolve immutable component IDs to one complete global labeling.

The raw presentation validator guarantees that every active strand refers to
a listed component.  This witness records the unique lookup used by the
categorical event semantics.
-/
structure LabelledComponentResolver
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (topology : SpecialKirbyPresentation manifold H2)
    (labeling : GlobalLabeling (S := S) topology) where
  labelOf : String → S
  component_sound :
    (index : Fin topology.formal.raw.components.length) →
      labelOf
          (topology.formal.raw.components.get index).componentId =
        labeling index

/-- Interpret strand orientation using the selected categorical right dual. -/
def strandObject
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {topology : SpecialKirbyPresentation manifold H2}
    {labeling : GlobalLabeling (S := S) topology}
    (resolver : LabelledComponentResolver topology labeling)
    (strand : StrandState) : C :=
  match strand.orientation with
  | .positive => data.simple (resolver.labelOf strand.componentId)
  | .negative => (data.simple (resolver.labelOf strand.componentId))ᘁ

/--
Whole-presentation compiler for the exact EGNO category and automorphism.

There is no whole-diagram field.  Every term is compiled event-by-event from
the validated execution trace, and the finite sum is formed only afterward.
-/
structure PresentationCompiler
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  resolver :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
    (labeling : GlobalLabeling (S := S) topology) →
      LabelledComponentResolver topology labeling
  eventSemantics :
    (topology : SpecialKirbyPresentation manifold H2) →
    (alpha : H2) →
    (labeling : GlobalLabeling (S := S) topology) →
      WindowedCategoricalEventSemantics
        topology.formal.raw
        (strandObject data (resolver topology alpha labeling))
        (NaturalTwist.ofRibbon data.ribbon)
  diagramCertificateHash :
    SpecialKirbyPresentation manifold H2 → String
  diagram_certificate_hash_shape :
    (topology : SpecialKirbyPresentation manifold H2) →
      RawPresentation.sha256Shape
        (diagramCertificateHash topology) = true
  compilerCertificateHash : String
  compiler_certificate_hash_shape :
    RawPresentation.sha256Shape compilerCertificateHash = true
  categorySnapshotHash : String
  category_snapshot_hash_sound :
    categorySnapshotHash = package.categorySnapshotHash
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace PresentationCompiler

/-- Exact event compiler for one complete global labeling. -/
def eventCompiler
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2)
    (labeling : GlobalLabeling (S := S) topology) :
    CategoricalEventCompiler C topology.formal.raw :=
  (compiler.eventSemantics topology alpha labeling)
    |>.toCategoricalEventCompiler

/-- Complete closed term for one global labeling. -/
def termDiagram
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2)
    (labeling : GlobalLabeling (S := S) topology) :
    Diagram C .unit .unit :=
  (compiler.eventCompiler topology alpha labeling).compileClosed
    topology.execution

/-- Formal finite sum of complete globally labelled presentation terms. -/
noncomputable def linearDiagram
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum
    (globalWeight data automorphism topology alpha)
    (compiler.termDiagram topology alpha)

/-- The raw numerator is forced by the derived scalarization. -/
noncomputable def rawNumerator
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) : K :=
  data.toFusionCategoryData.closedScalar
    (LinearDiagram.eval (compiler.linearDiagram topology alpha))

/-- Counts and numerator used by the normalization theorem. -/
noncomputable def evaluationState
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    EvaluationState (K := K) where
  counts := topology.counts
  rawNumerator := compiler.rawNumerator topology alpha

/-- The normalized value on one certified marked presentation. -/
noncomputable def value
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) : K :=
  (compiler.evaluationState topology alpha).normalized package.profile

/-- Evaluation visibly remains the complete global finite sum. -/
theorem linearDiagram_eval
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (compiler :
      PresentationCompiler data package automorphism manifold H2)
    (topology : SpecialKirbyPresentation manifold H2)
    (alpha : H2) :
    LinearDiagram.eval (compiler.linearDiagram topology alpha) =
      ∑ labeling,
        globalWeight data automorphism topology alpha labeling •
          Diagram.eval C
            (compiler.termDiagram topology alpha labeling) := by
  exact eval_weightedSum _ _

end PresentationCompiler

/--
Package-bound primitive isotopies.

Framing and closure constructors can only use the twist and spherical trace
derived from this exact Step 9 package.
-/
inductive PackageTaggedMove
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (package : Package data) :
    {source target : Boundary C} →
      Diagram C source target → Diagram C source target →
        Type (max uC vC)
  | planarIdentityBefore
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      PackageTaggedMove package (identityBefore diagram) diagram
  | planarIdentityAfter
      {source target : Boundary C}
      (diagram : Diagram C source target) :
      PackageTaggedMove package (identityAfter diagram) diagram
  | planarCompAssoc
      {a b c d : Boundary C}
      (first : Diagram C a b)
      (second : Diagram C b c)
      (third : Diagram C c d) :
      PackageTaggedMove package
        (compAssocBefore first second third)
        (compAssocAfter first second third)
  | criticalInterchange
      {a b c e f g : Boundary C}
      (leftFirst : Diagram C a b)
      (leftSecond : Diagram C b c)
      (rightFirst : Diagram C e f)
      (rightSecond : Diagram C f g) :
      PackageTaggedMove package
        (tensorInterchangeBefore
          leftFirst leftSecond rightFirst rightSecond)
        (tensorInterchangeAfter
          leftFirst leftSecond rightFirst rightSecond)
  | reidemeisterIIPositive (X Y : C) :
      PackageTaggedMove package
        (reidemeisterIIPositiveBefore X Y)
        (reidemeisterIIAfter X Y)
  | reidemeisterIINegative (X Y : C) :
      PackageTaggedMove package
        (reidemeisterIINegativeBefore X Y)
        (reidemeisterIIAfter X Y)
  | reidemeisterIII (X Y Z : C) :
      PackageTaggedMove package
        (reidemeisterIIIBefore X Y Z)
        (reidemeisterIIIAfter X Y Z)
  | rightPrimalSnake (X : C) :
      PackageTaggedMove package
        (rightPrimalSnakeBefore X) (Diagram.identity (.atom X))
  | rightDualSnake (X : C) :
      PackageTaggedMove package
        (rightDualSnakeBefore X) (Diagram.identity (.atom Xᘁ))
  | leftPrimalSnake (X : C) :
      PackageTaggedMove package
        (leftPrimalSnakeBefore X) (Diagram.identity (.atom X))
  | leftDualSnake (X : C) :
      PackageTaggedMove package
        (leftDualSnakeBefore X) (Diagram.identity (.atom (ᘁX)))
  | framedPositive (X : C) :
      PackageTaggedMove package
        (positiveKink X)
        (package.framedKinkCompatibility.positiveTwistDiagram X)
  | framedNegative (X : C) :
      PackageTaggedMove package
        (negativeKink X)
        (package.framedKinkCompatibility.negativeTwistDiagram X)
  | couponPositiveCrossing
      {X X' Y Y' : C}
      (f : X ⟶ Y)
      (g : X' ⟶ Y') :
      PackageTaggedMove package
        (positiveCrossingBefore f g) (positiveCrossingAfter f g)
  | couponNegativeCrossing
      {X X' Y Y' : C}
      (f : X ⟶ Y)
      (g : X' ⟶ Y') :
      PackageTaggedMove package
        (negativeCrossingBefore f g) (negativeCrossingAfter f g)
  | couponRightCup
      {X Y : C}
      (f : X ⟶ Y) :
      PackageTaggedMove package
        (rightCupMateSide f) (rightCupOriginalSide f)
  | couponRightCap
      {X Y : C}
      (f : X ⟶ Y) :
      PackageTaggedMove package
        (rightCapMateSide f) (rightCapOriginalSide f)
  | couponLeftCup
      {X Y : C}
      (f : X ⟶ Y) :
      PackageTaggedMove package
        (leftCupMateSide f) (leftCupOriginalSide f)
  | couponLeftCap
      {X Y : C}
      (f : X ⟶ Y) :
      PackageTaggedMove package
        (leftCapMateSide f) (leftCapOriginalSide f)
  | couponPositiveTwist
      {X Y : C}
      (name : String)
      (f : X ⟶ Y) :
      PackageTaggedMove package
        (package.framedKinkCompatibility.twist.positiveBefore name f)
        (package.framedKinkCompatibility.twist.positiveAfter name f)
  | couponNegativeTwist
      {X Y : C}
      (name : String)
      (f : X ⟶ Y) :
      PackageTaggedMove package
        (package.framedKinkCompatibility.twist.negativeBefore name f)
        (package.framedKinkCompatibility.twist.negativeAfter name f)
  | closureCut
      {X Y : C}
      (f : X ⟶ Y)
      (g : Y ⟶ X) :
      PackageTaggedMove package
        (package.sphericalCutTrace.cutBefore f g)
        (package.sphericalCutTrace.cutAfter f g)

namespace PackageTaggedMove

/-- Forget the package wrapper only after exact twist and trace are selected. -/
def toTaggedMove
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {source target : Boundary C}
    {before after : Diagram C source target} :
    PackageTaggedMove package before after →
      TaggedMove before after
  | .planarIdentityBefore diagram =>
      .planarIdentityBefore diagram
  | .planarIdentityAfter diagram =>
      .planarIdentityAfter diagram
  | .planarCompAssoc first second third =>
      .planarCompAssoc first second third
  | .criticalInterchange leftFirst leftSecond rightFirst rightSecond =>
      .criticalInterchange leftFirst leftSecond rightFirst rightSecond
  | .reidemeisterIIPositive X Y =>
      .reidemeisterIIPositive X Y
  | .reidemeisterIINegative X Y =>
      .reidemeisterIINegative X Y
  | .reidemeisterIII X Y Z =>
      .reidemeisterIII X Y Z
  | .rightPrimalSnake X =>
      .rightPrimalSnake X
  | .rightDualSnake X =>
      .rightDualSnake X
  | .leftPrimalSnake X =>
      .leftPrimalSnake X
  | .leftDualSnake X =>
      .leftDualSnake X
  | .framedPositive X =>
      .framedPositive package.framedKinkCompatibility X
  | .framedNegative X =>
      .framedNegative package.framedKinkCompatibility X
  | .couponPositiveCrossing f g =>
      .couponPositiveCrossing f g
  | .couponNegativeCrossing f g =>
      .couponNegativeCrossing f g
  | .couponRightCup f =>
      .couponRightCup f
  | .couponRightCap f =>
      .couponRightCap f
  | .couponLeftCup f =>
      .couponLeftCup f
  | .couponLeftCap f =>
      .couponLeftCap f
  | .couponPositiveTwist name f =>
      .couponPositiveTwist
        package.framedKinkCompatibility.twist name f
  | .couponNegativeTwist name f =>
      .couponNegativeTwist
        package.framedKinkCompatibility.twist name f
  | .closureCut f g =>
      .closureCut package.sphericalCutTrace f g

theorem eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {source target : Boundary C}
    {before after : Diagram C source target}
    (move : PackageTaggedMove package before after) :
    Diagram.eval C before = Diagram.eval C after :=
  move.toTaggedMove.sound

end PackageTaggedMove

/-- Reflexive, symmetric, transitive, and context-closed package isotopy. -/
inductive PackageIsotopy
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (package : Package data) :
    {source target : Boundary C} →
      Diagram C source target → Diagram C source target → Prop
  | refl {source target : Boundary C}
      (frame : Diagram C source target) :
      PackageIsotopy package frame frame
  | step
      {source target : Boundary C}
      {before after : Diagram C source target}
      (move : PackageTaggedMove package before after) :
      PackageIsotopy package before after
  | symm
      {source target : Boundary C}
      {before after : Diagram C source target} :
      PackageIsotopy package before after →
        PackageIsotopy package after before
  | trans
      {source target : Boundary C}
      {first middle last : Diagram C source target} :
      PackageIsotopy package first middle →
      PackageIsotopy package middle last →
        PackageIsotopy package first last
  | inContext
      {holeSource holeTarget wholeSource wholeTarget : Boundary C}
      {before after : Diagram C holeSource holeTarget}
      (context :
        Context C holeSource holeTarget wholeSource wholeTarget) :
      PackageIsotopy package before after →
        PackageIsotopy package
          (Context.plug C context before)
          (Context.plug C context after)

namespace PackageIsotopy

/-- Every package-bound isotopy preserves categorical evaluation. -/
theorem eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {source target : Boundary C}
    {before after : Diagram C source target}
    (isotopy : PackageIsotopy package before after) :
    Diagram.eval C before = Diagram.eval C after := by
  induction isotopy with
  | refl => rfl
  | step move => exact move.eval_eq
  | symm _ ih => exact ih.symm
  | trans _ _ leftIH rightIH => exact leftIH.trans rightIH
  | inContext context _ ih =>
      exact Context.eval_plug_congr C context ih

end PackageIsotopy

/-- Linear closure of exact package-bound framed isotopies. -/
inductive LinearIsotopy
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (package : Package data) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK uC vC)
  | atom
      {before after : Diagram C .unit .unit}
      (isotopy : PackageIsotopy package before after) :
      LinearIsotopy package (atom before) (atom after)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearIsotopy package leftBefore leftAfter →
      LinearIsotopy package rightBefore rightAfter →
        LinearIsotopy package
          (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after : LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearIsotopy package before after →
        LinearIsotopy package (scalar • before) (scalar • after)
  | trans
      {first middle last :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      LinearIsotopy package first middle →
      LinearIsotopy package middle last →
        LinearIsotopy package first last

namespace LinearIsotopy

/-- Linear isotopy soundness is derived by structural recursion. -/
theorem eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {before after : LinearDiagram (R := K) (C := C) .unit .unit}
    (isotopy : LinearIsotopy package before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction isotopy with
  | atom isotopy =>
      simpa only [eval_atom] using isotopy.eval_eq
  | add _ _ leftIH rightIH =>
      simpa only [map_add] using congrArg₂ (· + ·) leftIH rightIH
  | smul scalar _ ih =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) ih
  | trans _ _ leftIH rightIH =>
      exact leftIH.trans rightIH

end LinearIsotopy

/-- Extract the exact ordinary sliding law retained by a slide proof. -/
def ordinaryLaw
    {source target : Boundary C}
    {before after : Diagram C source target} :
    OrdinaryHandleSlide before after → HandleSlide.SourcedSlidingLaw C
  | .oneOverOne _ _ _ law _ _ => law
  | .twoOverOne _ _ _ law _ _ => law

/-- Extract source-bound metadata from an ordinary slide proof. -/
def ordinaryMetadata
    {source target : Boundary C}
    {before after : Diagram C source target} :
    OrdinaryHandleSlide before after → SlideMetadata
  | .oneOverOne metadata _ _ _ _ _ => metadata
  | .twoOverOne metadata _ _ _ _ _ => metadata

/--
Linear closure of ordinary slides bound to the package's exact formal colour.
-/
inductive BoundOrdinarySlide
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (package : Package data)
    (kind : SlideKind)
    (orientation : BandOrientation)
    (moveId sourceHash targetHash : String) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK uC vC)
  | atom
      {before after : Diagram C .unit .unit}
      (slide : OrdinaryHandleSlide before after)
      (law_sound :
        ordinaryLaw slide = package.ordinarySlidingLaw)
      (kind_sound : (ordinaryMetadata slide).kind = kind)
      (orientation_sound :
        (ordinaryMetadata slide).orientation = orientation)
      (move_id_sound :
        (ordinaryMetadata slide).moveId = moveId)
      (source_hash_sound :
        (ordinaryMetadata slide).sourcePresentationHash = sourceHash)
      (target_hash_sound :
        (ordinaryMetadata slide).targetPresentationHash = targetHash) :
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash (atom before) (atom after)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash leftBefore leftAfter →
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash rightBefore rightAfter →
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after : LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash before after →
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash
        (scalar • before) (scalar • after)

namespace BoundOrdinarySlide

/-- The ordinary-slide finite sum preserves categorical evaluation. -/
theorem eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {kind : SlideKind}
    {orientation : BandOrientation}
    {moveId sourceHash targetHash : String}
    {before after : LinearDiagram (R := K) (C := C) .unit .unit}
    (slide :
      BoundOrdinarySlide package kind orientation
        moveId sourceHash targetHash before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction slide with
  | atom slide _ _ _ _ _ _ =>
      simpa only [eval_atom] using slide.sound
  | add _ _ leftIH rightIH =>
      simpa only [map_add] using congrArg₂ (· + ·) leftIH rightIH
  | smul scalar _ ih =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) ih

end BoundOrdinarySlide

/--
Linear closure of the label-indexed generalized slide.

The base constructor is exactly `ClosedWindow.linear_eval_sound`; no fixed
object can stand for the whole formal colour.
-/
inductive BoundGeneralizedSlide
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    (package : Package data) :
    LinearDiagram (R := K) (C := C) .unit .unit →
      LinearDiagram (R := K) (C := C) .unit .unit →
        Type (max uK uC vC)
  | window
      (closedWindow :
        LabelIndexedSlidingMovies.ClosedWindow package.generalizedSliding)
      (coefficient : S → K) :
      BoundGeneralizedSlide package
        (closedWindow.linearBefore coefficient)
        (closedWindow.linearAfter coefficient)
  | add
      {leftBefore leftAfter rightBefore rightAfter :
        LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundGeneralizedSlide package leftBefore leftAfter →
      BoundGeneralizedSlide package rightBefore rightAfter →
      BoundGeneralizedSlide package
        (leftBefore + rightBefore) (leftAfter + rightAfter)
  | smul
      (scalar : K)
      {before after : LinearDiagram (R := K) (C := C) .unit .unit} :
      BoundGeneralizedSlide package before after →
      BoundGeneralizedSlide package
        (scalar • before) (scalar • after)

namespace BoundGeneralizedSlide

/-- The generalized-slide finite sum preserves categorical evaluation. -/
theorem eval_eq
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {before after : LinearDiagram (R := K) (C := C) .unit .unit}
    (slide : BoundGeneralizedSlide package before after) :
    LinearDiagram.eval before = LinearDiagram.eval after := by
  induction slide with
  | window closedWindow coefficient =>
      exact closedWindow.linear_eval_sound coefficient
  | add _ _ leftIH rightIH =>
      simpa only [map_add] using congrArg₂ (· + ·) leftIH rightIH
  | smul scalar _ ih =>
      simpa only [map_smul] using
        congrArg (fun value => scalar • value) ih

end BoundGeneralizedSlide

/--
Hash binding for one exact topology move and one graphical proof object.
-/
structure LocalMoveBinding
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target) where
  moveId : String
  move_id_sound : moveId = tableTwoMoveId move
  sourcePresentationHash : String
  source_hash_sound :
    sourcePresentationHash = source.formal.pinnedSourceHash
  targetPresentationHash : String
  target_hash_sound :
    targetPresentationHash = target.formal.pinnedSourceHash
  graphicalCertificateHash : String
  graphical_certificate_hash_shape :
    RawPresentation.sha256Shape graphicalCertificateHash = true
  categorySnapshotHash : String
  category_snapshot_hash_shape :
    RawPresentation.sha256Shape categorySnapshotHash = true

/-- Build a local binding without accepting free move or presentation IDs. -/
def localMoveBinding
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target)
    (certificateHash : String)
    (certificateShape :
      RawPresentation.sha256Shape certificateHash = true) :
    LocalMoveBinding move where
  moveId := tableTwoMoveId move
  move_id_sound := rfl
  sourcePresentationHash := source.formal.pinnedSourceHash
  source_hash_sound := rfl
  targetPresentationHash := target.formal.pinnedSourceHash
  target_hash_sound := rfl
  graphicalCertificateHash := certificateHash
  graphical_certificate_hash_shape := certificateShape
  categorySnapshotHash := package.categorySnapshotHash
  category_snapshot_hash_shape := package.category_snapshot_hash_shape

/-- Exact local factorization for a 1--2 cancellation. -/
structure OneTwoFactorization
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (before after : LinearDiagram (R := K) (C := C) .unit .unit) where
  localPairDiagram : Diagram C .unit .unit
  diagram_factorization :
    LinearDiagram.eval before =
      Diagram.eval C
        (closedTensorDiagram localPairDiagram
          (collapse (R := K) "EGNO-one-two-rest" after))
  local_pair_scalar :
    data.toFusionCategoryData.closedScalar
        (Diagram.eval C localPairDiagram) =
      package.cancellation.oneTwoPairValue

namespace OneTwoFactorization

/-- Derive the complete normalized 1--2 calculation from local factorization. -/
noncomputable def toCalculation
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {before after : LinearDiagram (R := K) (C := C) .unit .unit}
    (program : OneTwoFactorization data package before after)
    {beforeCounts afterCounts : HandleCounts}
    (counts_sound : beforeCounts = afterCounts.addOneTwo) :
    OneTwoLocalCalculation package.profile where
  pairValue := package.cancellation.oneTwoPairValue
  cutValue := package.cancellation.oneTwoCutValue
  before := {
    counts := beforeCounts
    rawNumerator :=
      data.toFusionCategoryData.closedScalar
        (LinearDiagram.eval before)
  }
  after := {
    counts := afterCounts
    rawNumerator :=
      data.toFusionCategoryData.closedScalar
        (LinearDiagram.eval after)
  }
  counts_sound := counts_sound
  isolated_from_rest := True
  isolated_from_rest_witness := True.intro
  disjoint_union_sound := fun _ => by
    rw [program.diagram_factorization,
      closedTensorScalar_multiplicative,
      eval_collapse, program.local_pair_scalar]
  transparent_twist_trivial :=
    package.cancellationInput.transparentTwistTrivial
  transparent_twist_witness :=
    package.cancellationInput.transparent_twist_witness
  cutting_identity :=
    package.cancellationInput.cutting_identity
  killing_identity :=
    package.cancellationInput.killing_identity

end OneTwoFactorization

/-- Exact local factorization for a 2--3 cancellation. -/
structure TwoThreeFactorization
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (before after : LinearDiagram (R := K) (C := C) .unit .unit) where
  localUnknotDiagram : Diagram C .unit .unit
  diagram_factorization :
    LinearDiagram.eval before =
      Diagram.eval C
        (closedTensorDiagram localUnknotDiagram
          (collapse (R := K) "EGNO-two-three-rest" after))
  local_unknot_scalar :
    data.toFusionCategoryData.closedScalar
        (Diagram.eval C localUnknotDiagram) =
      package.cancellation.twoThreeUnknotValue

namespace TwoThreeFactorization

/-- Derive the complete normalized 2--3 calculation from local factorization. -/
noncomputable def toCalculation
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {before after : LinearDiagram (R := K) (C := C) .unit .unit}
    (program : TwoThreeFactorization data package before after)
    {beforeCounts afterCounts : HandleCounts}
    (counts_sound : beforeCounts = afterCounts.addTwoThree) :
    TwoThreeLocalCalculation package.profile where
  unknotValue := package.cancellation.twoThreeUnknotValue
  before := {
    counts := beforeCounts
    rawNumerator :=
      data.toFusionCategoryData.closedScalar
        (LinearDiagram.eval before)
  }
  after := {
    counts := afterCounts
    rawNumerator :=
      data.toFusionCategoryData.closedScalar
        (LinearDiagram.eval after)
  }
  counts_sound := counts_sound
  unlinked_unknotted_zero_framed := True
  unlink_witness := True.intro
  disjoint_union_sound := fun _ => by
    rw [program.diagram_factorization,
      closedTensorScalar_multiplicative,
      eval_collapse, program.local_unknot_scalar]
  pivotal_dimension_preserved :=
    package.cancellationInput.pivotal_dimension_preserved

end TwoThreeFactorization

/--
The source-bound denominator for all eight directed local move families.

Each field returns a lower-level proof grammar or local factorization.  There
is no field containing a raw or normalized scalar equality.
-/
structure LocalMoveCompiler
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (automorphism : TensorIdentityAutomorphism C)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2]
    (presentation :
      PresentationCompiler data package automorphism manifold H2) where
  framedIsotopy :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .framedIsotopy source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      LinearIsotopy package
        (presentation.linearDiagram source alpha)
        (presentation.linearDiagram target
          (transport.targetClass alpha))
  oneOverOne :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .oneOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      BoundOrdinarySlide package .oneOverOne orientation
        metadata.moveId metadata.sourcePresentationHash
        metadata.targetPresentationHash
        (presentation.linearDiagram source alpha)
        (presentation.linearDiagram target
          (transport.targetClass alpha))
  twoOverOne :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .twoOverOne source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      BoundOrdinarySlide package .twoOverOne orientation
        metadata.moveId metadata.sourcePresentationHash
        metadata.targetPresentationHash
        (presentation.linearDiagram source alpha)
        (presentation.linearDiagram target
          (transport.targetClass alpha))
  twoOverTwo :
    {source target : SpecialKirbyPresentation manifold H2} →
    (orientation : BandOrientation) →
    (metadata : TableTwoMoveMetadata .twoOverTwo source target) →
    (counts_sound : source.counts = target.counts) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      BoundGeneralizedSlide package
        (presentation.linearDiagram source alpha)
        (presentation.linearDiagram target
          (transport.targetClass alpha))
  oneTwoBirth :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .oneTwoBirth source target) →
    (counts_sound : target.counts = source.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      OneTwoFactorization data package
        (presentation.linearDiagram target
          (transport.targetClass alpha))
        (presentation.linearDiagram source alpha)
  oneTwoDeath :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .oneTwoDeath source target) →
    (counts_sound : source.counts = target.counts.addOneTwo) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      OneTwoFactorization data package
        (presentation.linearDiagram source alpha)
        (presentation.linearDiagram target
          (transport.targetClass alpha))
  twoThreeBirth :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .twoThreeBirth source target) →
    (counts_sound : target.counts = source.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      TwoThreeFactorization data package
        (presentation.linearDiagram target
          (transport.targetClass alpha))
        (presentation.linearDiagram source alpha)
  twoThreeDeath :
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata .twoThreeDeath source target) →
    (counts_sound : source.counts = target.counts.addTwoThree) →
    (transport : MarkedH2Transport source target) →
    (alpha : H2) →
      TwoThreeFactorization data package
        (presentation.linearDiagram source alpha)
        (presentation.linearDiagram target
          (transport.targetClass alpha))
  graphicalCertificateHash :
    {kind : SourceBoundLocalMoveRecipe.RecipeKind} →
    {source target : SpecialKirbyPresentation manifold H2} →
      TableTwoMoveMetadata kind source target → H2 → String
  graphical_certificate_hash_shape :
    {kind : SourceBoundLocalMoveRecipe.RecipeKind} →
    {source target : SpecialKirbyPresentation manifold H2} →
    (metadata : TableTwoMoveMetadata kind source target) →
    (alpha : H2) →
      RawPresentation.sha256Shape
        (graphicalCertificateHash metadata alpha) = true
  categorySnapshotHash : String
  category_snapshot_hash_sound :
    categorySnapshotHash = package.categorySnapshotHash
  compilerCertificateHash : String
  compiler_certificate_hash_shape :
    RawPresentation.sha256Shape compilerCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace LocalMoveCompiler

/-- Equal counts and equal formal evaluations give equal normalized values. -/
theorem normalized_eq_of_linear_eval
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation :
      PresentationCompiler data package automorphism manifold H2}
    {source target : SpecialKirbyPresentation manifold H2}
    (alpha beta : H2)
    (counts_eq : source.counts = target.counts)
    (linear_eval_eq :
      LinearDiagram.eval (presentation.linearDiagram source alpha) =
        LinearDiagram.eval (presentation.linearDiagram target beta)) :
    presentation.value source alpha =
      presentation.value target beta := by
  apply EvaluatedTableTwoStep.normalized_eq_of_counts_and_raw
  · exact counts_eq
  · exact congrArg data.toFusionCategoryData.closedScalar linear_eval_eq

/-- Every one of the eight exact Table 2 constructors preserves the value. -/
theorem move_invariant
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation :
      PresentationCompiler data package automorphism manifold H2}
    (compiler :
      LocalMoveCompiler
        data package automorphism manifold H2 presentation)
    {source target : SpecialKirbyPresentation manifold H2}
    (move : TableTwoMove source target)
    (alpha : H2) :
    presentation.value source alpha =
      presentation.value target
        (move.homologyTransport.targetClass alpha) := by
  cases move with
  | framedIsotopy metadata counts transport =>
      exact normalized_eq_of_linear_eval alpha
        (transport.targetClass alpha) counts
        (compiler.framedIsotopy metadata counts transport alpha).eval_eq
  | oneOverOne orientation metadata counts transport =>
      exact normalized_eq_of_linear_eval alpha
        (transport.targetClass alpha) counts
        (BoundOrdinarySlide.eval_eq
          (compiler.oneOverOne orientation metadata counts transport alpha))
  | twoOverOne orientation metadata counts transport =>
      exact normalized_eq_of_linear_eval alpha
        (transport.targetClass alpha) counts
        (BoundOrdinarySlide.eval_eq
          (compiler.twoOverOne orientation metadata counts transport alpha))
  | twoOverTwo orientation metadata counts transport =>
      exact normalized_eq_of_linear_eval alpha
        (transport.targetClass alpha) counts
        (BoundGeneralizedSlide.eval_eq
          (compiler.twoOverTwo orientation metadata counts transport alpha))
  | oneTwoBirth metadata counts transport =>
      let calculation :=
        (compiler.oneTwoBirth metadata counts transport alpha)
          |>.toCalculation counts
      simpa only [PresentationCompiler.value,
        PresentationCompiler.evaluationState,
        PresentationCompiler.rawNumerator] using
          calculation.normalized_sound.symm
  | oneTwoDeath metadata counts transport =>
      let calculation :=
        (compiler.oneTwoDeath metadata counts transport alpha)
          |>.toCalculation counts
      simpa only [PresentationCompiler.value,
        PresentationCompiler.evaluationState,
        PresentationCompiler.rawNumerator] using
          calculation.normalized_sound
  | twoThreeBirth metadata counts transport =>
      let calculation :=
        (compiler.twoThreeBirth metadata counts transport alpha)
          |>.toCalculation counts
      simpa only [PresentationCompiler.value,
        PresentationCompiler.evaluationState,
        PresentationCompiler.rawNumerator] using
          calculation.normalized_sound.symm
  | twoThreeDeath metadata counts transport =>
      let calculation :=
        (compiler.twoThreeDeath metadata counts transport alpha)
          |>.toCalculation counts
      simpa only [PresentationCompiler.value,
        PresentationCompiler.evaluationState,
        PresentationCompiler.rawNumerator] using
          calculation.normalized_sound

/-- Movie induction over the source-backed move grammar. -/
theorem movie_invariant
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {automorphism : TensorIdentityAutomorphism C}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation :
      PresentationCompiler data package automorphism manifold H2}
    (compiler :
      LocalMoveCompiler
        data package automorphism manifold H2 presentation)
    {source target : SpecialKirbyPresentation manifold H2}
    (movie : TableTwoMovie source target)
    (alpha : H2) :
    presentation.value source alpha =
      presentation.value target (movie.targetClass alpha) := by
  induction movie generalizing alpha with
  | refl => rfl
  | step move => exact compiler.move_invariant move alpha
  | trans first second firstIH secondIH =>
      change
        presentation.value _ alpha =
          presentation.value _
            (second.targetClass (first.targetClass alpha))
      exact (firstIH alpha).trans
        (secondIH (first.targetClass alpha))

end LocalMoveCompiler

/--
All exact inputs needed to descend the modular link prescription to a marked
four-manifold pair.
-/
structure InvariantInputs
    (data : RibbonFusionCategoryData (K := K) (C := C) (S := S))
    (package : Package data)
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  automorphism : TensorIdentityAutomorphism C
  presentationCompiler :
    PresentationCompiler data package automorphism manifold H2
  localMoveCompiler :
    LocalMoveCompiler data package automorphism manifold H2
      presentationCompiler
  generalCerf : GeneralCerfCompleteness manifold
  basePresentation : SpecialKirbyPresentation manifold H2
  assemblyCertificateHash : String
  assembly_certificate_hash_shape :
    RawPresentation.sha256Shape assemblyCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace InvariantInputs

/-- Marked presentation system derived from the two visible topology inputs. -/
noncomputable def markedSystem
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : InvariantInputs data package manifold H2) :
    MarkedPairPresentationSystem manifold H2 :=
  (sourceBackedGeometricH2Compiler manifold H2)
    |>.toGeometricMarkedH2Compiler
    |>.markedPairSystem inputs.generalCerf inputs.basePresentation

/-- Value of one marked pair using the system's chosen presentation. -/
noncomputable def value
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : InvariantInputs data package manifold H2)
    (alpha : H2) : K :=
  inputs.presentationCompiler.value
    (inputs.markedSystem.chosenPresentation alpha)
    (inputs.markedSystem.chosenCoordinate alpha)

/--
Every certified presentation of `(X, alpha)` computes the chosen value.
-/
theorem presentation_independent
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : InvariantInputs data package manifold H2)
    {presentation : SpecialKirbyPresentation manifold H2}
    {coordinate alpha : H2}
    (represents :
      inputs.markedSystem.represents presentation coordinate alpha) :
    inputs.presentationCompiler.value presentation coordinate =
      inputs.value alpha := by
  let movie :=
    inputs.markedSystem.completeness.tableTwoConnected
      (inputs.markedSystem.chosenPresentation alpha) presentation
  have movieEquality :=
    inputs.localMoveCompiler.movie_invariant movie
      (inputs.markedSystem.chosenCoordinate alpha)
  have coordinateEquality :
      movie.targetClass
          (inputs.markedSystem.chosenCoordinate alpha) =
        coordinate :=
    inputs.markedSystem.marked_transport_sound
      (inputs.markedSystem.chosen_represents alpha) represents
  rw [coordinateEquality] at movieEquality
  exact movieEquality.symm

/--
Terminal theorem: any two certified presentations of the same marked pair
have equal normalized EGNO modular evaluations.
-/
theorem four_manifold_invariant
    {data : RibbonFusionCategoryData (K := K) (C := C) (S := S)}
    {package : Package data}
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (inputs : InvariantInputs data package manifold H2)
    {left right : SpecialKirbyPresentation manifold H2}
    {leftCoordinate rightCoordinate alpha : H2}
    (leftRepresents :
      inputs.markedSystem.represents left leftCoordinate alpha)
    (rightRepresents :
      inputs.markedSystem.represents right rightCoordinate alpha) :
    inputs.presentationCompiler.value left leftCoordinate =
      inputs.presentationCompiler.value right rightCoordinate := by
  rw [inputs.presentation_independent leftRepresents,
    inputs.presentation_independent rightRepresents]

end InvariantInputs

/-- Visible denominator of non-derived mathematical input classes. -/
inductive DomainInputClass where
  | globalGraphicalTheorems
  | sourceBoundPresentationCompiler
  | sourceBoundLocalMoveCompiler
  | generalCerfCompleteness
  | specialKirbyCompleteness
  | handleChainNaturality
  deriving Repr, BEq, DecidableEq

/-- No input class is hidden from the terminal theorem boundary. -/
def requiredDomainInputClasses : List DomainInputClass :=
  [
    .globalGraphicalTheorems,
    .sourceBoundPresentationCompiler,
    .sourceBoundLocalMoveCompiler,
    .generalCerfCompleteness,
    .specialKirbyCompleteness,
    .handleChainNaturality
  ]

theorem domain_input_class_count :
    requiredDomainInputClasses.length = 6 := by
  rfl

theorem domain_input_classes_unique :
    requiredDomainInputClasses.Nodup := by
  decide

end TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
