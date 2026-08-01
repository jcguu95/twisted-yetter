import TwistedYetter.Kirby.Final.Semantics.Independent.Invariant
import TwistedYetter.Kirby.Final.Semantics.Independent.OneTwoLocalReplacement
import TwistedYetter.Kirby.Final.Semantics.Independent.TwoThreeLocalReplacement
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Independent semantics: explicit entrance axioms

This is the unique trust boundary above the frozen mathematical definitions.
Every declaration below is individually named.  No axiom states an evaluator
equality, representative independence, local-move invariance, or the final
four-manifold theorem.

The abstract witness types make the unformalized topology visible without
pretending that a string, hash, or opaque proposition is a proof.  Composite
certificates are assembled below as theorems from individually named inputs.
-/

namespace TwistedYetter.Semantics.Independent

open CategoryTheory

universe uK

/-! ## Clean band-slide topology

There is no separate clean-band existence axiom here.  A band-slide
`ElementaryMove` carries its exact `CleanBandSlide` data.  The marked
Kirby--Cerf completeness axiom must produce a movie whose slide constructors
contain that data.
-/

/-! ## Elementary-move topology

Framed-isotopy, band-slide, and cancellation data belong to the corresponding
`ElementaryMove` constructors.  This file does not postulate separate
witness/existence axioms for their internal fields.  The single marked
Kirby--Cerf completeness axiom below must return a finite movie built from
those exact constructors.
-/

/-! ## Ribbon graphical coherence -/

axiom FramedRibbonIsotopyWitness
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    {X Y : 𝒞.C} :
    RibbonExpression 𝒞 X Y → RibbonExpression 𝒞 X Y → Type

abbrev FramedRibbonIsotopic
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    {X Y : 𝒞.C}
    (left right : RibbonExpression 𝒞 X Y) : Prop :=
  Nonempty (FramedRibbonIsotopyWitness left right)

/--
Shum 1994, Theorem 2.6: a framed-ribbon isotopy witness identifies the
interpreted morphisms.  This is a category-literature input, not a
Twisted-Yetter evaluation equality.
-/
axiom shum_framedRibbonCoherence
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : PremodularFusionCategory K}
    {X Y : 𝒞.C}
    {left right : RibbonExpression 𝒞 X Y} :
    FramedRibbonIsotopic left right →
    left.interpret = right.interpret

/--
EGNO, canonical pivotal structure of a ribbon category: the tensor unit has
quantum dimension one.

This is a basic category-literature input.  It mentions no Kirby diagram,
character, evaluator, or manifold.
-/
axiom egno_tensorUnitQuantumDimension
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    𝒞.simples.quantumDimension 𝒞.simples.tensorUnit = 1

/--
EGNO, nonvanishing of the global dimension of a fusion category over an
algebraically closed field of characteristic zero.
-/
axiom egno_globalDimension_ne_zero
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : PremodularFusionCategory K) :
    𝒞.globalDimension ≠ 0

/-! ## Clean band-slide graphical interpretation -/

/--
The explicit standard local normal form at one endpoint of a clean band slide.

The hole object is the tensor product of the displayed moving and stationary
simple labels.  `identityStage` and `resolvedStage` below are therefore
definitions, not arbitrary expressions supplied by an axiom.
-/
structure CleanBandEndpointNormalForm
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (_slide : CleanBandSlide source.diagram target.diagram)
    (_sourceCycle : ThamTwoCycles source.primalBoundary) where
  movingLabel : 𝒞η.category.simples.Simple
  stationaryLabel : 𝒞η.category.simples.Simple
  context :
    RibbonExpressionContext 𝒞η.category
      (fusionPairObject 𝒞η.category movingLabel stationaryLabel)
      (fusionPairObject 𝒞η.category movingLabel stationaryLabel)
      (categoryUnitObject 𝒞η.category)
      (categoryUnitObject 𝒞η.category)

def CleanBandEndpointNormalForm.identityStage
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞η : TwistedPremodularCategory K}
    {source target : HomologicallyMarkedDiagram}
    {slide : CleanBandSlide source.diagram target.diagram}
    {sourceCycle : ThamTwoCycles source.primalBoundary}
    (normalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCycle) :
    ClosedRibbonExpression 𝒞η.category :=
  normalForm.context.plug
    (identityExpression 𝒞η.category
      (fusionPairObject 𝒞η.category
        normalForm.movingLabel normalForm.stationaryLabel))

def CleanBandEndpointNormalForm.resolvedStage
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞η : TwistedPremodularCategory K}
    {source target : HomologicallyMarkedDiagram}
    {slide : CleanBandSlide source.diagram target.diagram}
    {sourceCycle : ThamTwoCycles source.primalBoundary}
    (normalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCycle) :
    ClosedRibbonExpression 𝒞η.category :=
  normalForm.context.plug
    (fusionResolutionExpression 𝒞η.category
      normalForm.movingLabel normalForm.stationaryLabel)

/--
The exact normalized closed graphical expression compiled from one marked
diagram and one THAM-side cycle.

Unlike `evaluateCycle`, this retains the endomorphism of the tensor unit.  It
therefore permits attach, transport, and detach to be compared at the
graphical-morphism level before scalarization.
-/
noncomputable def normalizedCycleExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (marked : HomologicallyMarkedDiagram)
    (cycle : ThamTwoCycles marked.primalBoundary) :
    ClosedRibbonExpression 𝒞η.category :=
  .morphism
    (thamDefinition511Normalization
          𝒞η.category.globalDimension
          marked.diagram.handles.hThree
          marked.diagram.handles.hTwo
          marked.diagram.handles.hOne •
      ∑ labeling : TwoHandleLabeling 𝒞η.category marked.diagram,
        (ordinaryKirbyWeight 𝒞η.category labeling *
            characterWeight 𝒞η labeling cycle) •
          (canonicalRoleAwareGraphCompiler
            𝒞η marked.diagram marked.primalBoundary labeling cycle).graph.interpret)

/--
Clean attachment has the standard typed graphical interpretation.

The axiom supplies the two intermediate expressions as visible data and says
only that the exact normalized source expression is framed-ribbon isotopic to
the attached expression.  It does not assert scalar evaluation equality or
the final slide result.
-/
axiom cleanAttach_hasStandardGraphicalInterpretation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (slide : CleanBandSlide source.diagram target.diagram)
    (slideRealizes :
      CleanBandSlideRealizesStandardKirbySlide slide)
    (sourceCycle : ThamTwoCycles source.primalBoundary) :
    ∃ normalForm : CleanBandEndpointNormalForm 𝒞η slide sourceCycle,
      FramedRibbonIsotopic
        (normalizedCycleExpression 𝒞η source sourceCycle)
        normalForm.identityStage

/--
Clean detachment has the standard typed graphical interpretation.

The target cycle is forced to be the cycle transported by the move's exact
THAM chain map.  No caller may provide an unrelated target marking.
-/
axiom cleanDetach_hasStandardGraphicalInterpretation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (slide : CleanBandSlide source.diagram target.diagram)
    (slideRealizes :
      CleanBandSlideRealizesStandardKirbySlide slide)
    (transport : ThamHandleChainTransport source target)
    (sourceCycle : ThamTwoCycles source.primalBoundary)
    :
    ∃ normalForm : CleanBandEndpointNormalForm 𝒞η slide sourceCycle,
      FramedRibbonIsotopic
        normalForm.identityStage
        (normalizedCycleExpression 𝒞η target
          (transport.mapCycle sourceCycle))

/--
The finite coupon route gives a typed naturality derivation between the exact
fusion-resolved attach and detach normal forms.

This is the formal stopping point for the compactness/generic-position
argument.  The returned object is proof-relevant graphical transport, not an
evaluation equality.
-/
axiom finiteCouponTransport_hasTypedGraphicalDerivation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (slide : CleanBandSlide source.diagram target.diagram)
    (slideRealizes :
      CleanBandSlideRealizesStandardKirbySlide slide)
    (transportComplete :
      FiniteCouponTransportRealizesCompletePath
        slide.decomposition.transport)
    (sourceCycle : ThamTwoCycles source.primalBoundary)
    (attachNormalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCycle)
    (detachNormalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCycle) :
    CharacterCouponTransport 𝒞η.character
      attachNormalForm.resolvedStage detachNormalForm.resolvedStage

/-! ## Framed-isotopy graphical interpretation -/

/--
An exact certified framed isotopy compiles to a framed-ribbon isotopy between
the frozen source expression and the expression at the uniquely transported
THAM-side cycle.

This is the narrow topology-to-graphical boundary used by the framed-isotopy
case.  It returns an isotopy witness, not an evaluator equality.  In
particular, neither the target cycle nor a scalar result can be chosen by the
caller.
-/
axiom framedIsotopy_hasTypedGraphicalInterpretation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (script : FramedIsotopyScript source.diagram target.diagram)
    (scriptRealizes :
      FramedIsotopyScriptRealizesFramedIsotopy script)
    (transport : ThamHandleChainTransport source target)
    (sourceCycle : ThamTwoCycles source.primalBoundary) :
    FramedRibbonIsotopic
      (normalizedCycleExpression 𝒞η source sourceCycle)
      (normalizedCycleExpression 𝒞η target
        (transport.mapCycle sourceCycle))

/-! ## Cancellation local graphical normal forms

The former one--two birth/death graphical axioms were removed. Their exact
graphical conclusions are theorem obligations in `Proofs/CancellationMoves`.
The former two--three graphical axioms have now also been removed.
Its exact transparent normal form is carried explicitly by the move
constructor; no two--three local-normal-form axiom remains.  The one--two
normal form is still the external category-neutral input specified in
`OneTwoLocalReplacement`.
-/

/-! ## Smooth four-manifold and Kirby--Cerf topology

The following three declarations are the explicit foundational vocabulary.
They are counted in the entrance-axiom ledger so that the public final theorem
can remain the human statement in `𝒞η`, `f`, and `α` without hiding ambient
parameters.
-/

axiom ClosedOrientedSmoothFourManifold : Type

/-- The underlying topological space of a smooth oriented four-manifold. -/
axiom underlyingTopologicalSpace :
  ClosedOrientedSmoothFourManifold → TopCat

axiom OrientedDiffeomorphism :
  ClosedOrientedSmoothFourManifold →
  ClosedOrientedSmoothFourManifold →
  Type

/-- An oriented diffeomorphism supplies its underlying homeomorphism. -/
axiom underlyingHomeomorphism
    {X Y : ClosedOrientedSmoothFourManifold} :
    OrientedDiffeomorphism X Y →
    (underlyingTopologicalSpace X ≅ underlyingTopologicalSpace Y)

/-- Integral singular homology in degree two. -/
noncomputable def integralSingularH₂Functor :
    TopCat ⥤ AddCommGrpCat :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat 2).obj
    (AddCommGrpCat.of ℤ)

/-- The second integral singular homology group of a four-manifold. -/
noncomputable def ManifoldH₂
    (X : ClosedOrientedSmoothFourManifold) : AddCommGrpCat :=
  integralSingularH₂Functor.obj (underlyingTopologicalSpace X)

/-- Functoriality of integral singular homology under an oriented diffeomorphism. -/
noncomputable def inducedH₂
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : OrientedDiffeomorphism X Y) :
    ManifoldH₂ X ≃+ ManifoldH₂ Y :=
  CategoryTheory.Iso.addCommGroupIsoToAddEquiv
    (integralSingularH₂Functor.mapIso (underlyingHomeomorphism f))

/--
The closed oriented smooth four-manifold obtained from a combinatorial special
Kirby diagram by the usual handle-attachment construction.  The diagram type
already records one zero-handle, one four-handle, dotted one-handles, framed
two-handles, and the closing three-handle data.
-/
axiom realizeSpecialKirbyDiagram :
  CombinatorialSpecialKirbyDiagram → ClosedOrientedSmoothFourManifold

/--
The Poincare-duality identification obtained by turning the handle
decomposition upside down.  The codomain is the homology of the canonical
transposed THAM complex; callers cannot supply an arbitrary group equivalence.
-/
axiom turnoverPoincareDualityEquiv
    (diagram : CombinatorialSpecialKirbyDiagram)
    (primal : PrimalDegreeThreeBoundaryData diagram)
    (homologyComparison :
      PrimalKirbyH₂ primal ≃+ ManifoldH₂ (realizeSpecialKirbyDiagram diagram)) :
    PrimalKirbyH₂ primal ≃+ ThamKirbyH₂ primal

/-! ## Explicit classical topology axioms -/

/--
T1. Every closed oriented smooth four-manifold admits at least one special
Kirby diagram in the stated sense.
-/
axiom specialKirbyDiagram_exists
    (X : ClosedOrientedSmoothFourManifold) :
    Σ diagram : CombinatorialSpecialKirbyDiagram,
      OrientedDiffeomorphism (realizeSpecialKirbyDiagram diagram) X

/--
T2. The integral handle chain complex of a presenting diagram computes the
manifold's second homology.
-/
axiom specialKirbyDiagram_computesH₂
    (diagram : CombinatorialSpecialKirbyDiagram) :
    Σ primal : PrimalDegreeThreeBoundaryData diagram,
      PrimalKirbyH₂ primal ≃+ ManifoldH₂ (realizeSpecialKirbyDiagram diagram)

structure SpecialKirbyRepresentativeOf
    (X : ClosedOrientedSmoothFourManifold) where
  diagram : CombinatorialSpecialKirbyDiagram
  primalBoundary : PrimalDegreeThreeBoundaryData diagram
  realizationDiffeomorphism :
    OrientedDiffeomorphism (realizeSpecialKirbyDiagram diagram) X
  diagramHomologyComparison :
    PrimalKirbyH₂ primalBoundary ≃+
      ManifoldH₂ (realizeSpecialKirbyDiagram diagram)
  alpha : PrimalKirbyH₂ primalBoundary

noncomputable def SpecialKirbyRepresentativeOf.thamHomologyIdentification
    {X : ClosedOrientedSmoothFourManifold}
    (representative : SpecialKirbyRepresentativeOf X) :
    TurnoverH₂Identification representative.primalBoundary :=
  { equiv := turnoverPoincareDualityEquiv
      representative.diagram
      representative.primalBoundary
      representative.diagramHomologyComparison }

noncomputable def SpecialKirbyRepresentativeOf.toHomologicallyMarkedDiagram
    {X : ClosedOrientedSmoothFourManifold}
    (representative : SpecialKirbyRepresentativeOf X) :
    HomologicallyMarkedDiagram :=
  { diagram := representative.diagram
    primalBoundary := representative.primalBoundary
    turnover := representative.thamHomologyIdentification
    alpha := representative.alpha }

noncomputable def SpecialKirbyRepresentativeOf.diagramH₂EquivManifoldH₂
    {X : ClosedOrientedSmoothFourManifold}
    (representative : SpecialKirbyRepresentativeOf X) :
    PrimalKirbyH₂ representative.primalBoundary ≃+ ManifoldH₂ X :=
  representative.diagramHomologyComparison.trans
    (inducedH₂ representative.realizationDiffeomorphism)

def SpecialKirbyRepresentativeOf.representsHomologyClass
    {X : ClosedOrientedSmoothFourManifold}
    (alpha : ManifoldH₂ X)
    (representative : SpecialKirbyRepresentativeOf X) : Prop :=
  representative.diagramH₂EquivManifoldH₂ representative.alpha = alpha

/--
The special Kirby representative used by the evaluator is assembled from the explicit
topology axioms above.  The selected combinatorial diagram already carries the
cut-and-reglue plans required at all dotted components; no separate puncture
word realization axiom is needed.
-/
theorem specialKirbyRepresentative_exists
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) :
    ∃ representative : SpecialKirbyRepresentativeOf X,
      representative.representsHomologyClass alpha := by
  obtain ⟨diagram, realizationDiffeomorphism⟩ := specialKirbyDiagram_exists X
  obtain ⟨primal, diagramHomologyComparison⟩ :=
    specialKirbyDiagram_computesH₂ diagram
  let homologyComparison : PrimalKirbyH₂ primal ≃+ ManifoldH₂ X :=
    diagramHomologyComparison.trans (inducedH₂ realizationDiffeomorphism)
  let representative : SpecialKirbyRepresentativeOf X :=
    { diagram := diagram
      primalBoundary := primal
      realizationDiffeomorphism := realizationDiffeomorphism
      diagramHomologyComparison := diagramHomologyComparison
      alpha := homologyComparison.symm alpha }
  refine ⟨representative, ?_⟩
  exact homologyComparison.apply_symm_apply alpha

axiom markedKirbyCerf_complete
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : OrientedDiffeomorphism X Y)
    (alpha : ManifoldH₂ X)
    (left : SpecialKirbyRepresentativeOf X)
    (leftCorrect : left.representsHomologyClass alpha)
    (right : SpecialKirbyRepresentativeOf Y)
    (rightCorrect :
      right.representsHomologyClass (inducedH₂ f alpha)) :
    Nonempty (KirbyMovie left.toHomologicallyMarkedDiagram
      right.toHomologicallyMarkedDiagram)

/--
The clean final target after all algebraic and local-move obligations have
been proved.  The target is a definition, not an entrance axiom.
-/
def TwistedYetterDiffeomorphismInvarianceTarget
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K) : Prop :=
  ∀ (X Y : ClosedOrientedSmoothFourManifold)
    (f : OrientedDiffeomorphism X Y)
    (alpha : ManifoldH₂ X)
    (left : SpecialKirbyRepresentativeOf X)
    (leftCorrect : left.representsHomologyClass alpha)
    (right : SpecialKirbyRepresentativeOf Y)
    (rightCorrect :
      right.representsHomologyClass (inducedH₂ f alpha)),
    evaluateMarking 𝒞η left.toHomologicallyMarkedDiagram =
      evaluateMarking 𝒞η right.toHomologicallyMarkedDiagram

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 2216
