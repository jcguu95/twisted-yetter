import TwistedYetter.Kirby.Final.Semantics.Independent.Invariant

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

universe uK

/-! ## Dotted-disk topology -/

/--
External topology witness that the ordered puncture words are realized by
pairwise compatible spanning disks and that cutting and regluing recovers the
specified combinatorial trace.
-/
axiom DottedCutTopologyWitness :
  CombinatorialSpecialKirbyDiagram → Type

axiom dottedCutWords_topologicallyRealizable
    (diagram : CombinatorialSpecialKirbyDiagram) :
    Nonempty (DottedCutTopologyWitness diagram)

/-! ## Turned-over handle topology -/

/--
External topology witness that the stored additive equivalence is the
Poincaré-duality identification induced by turning over this handle
decomposition.
-/
axiom TurnoverPoincareDualityWitness
    (marked : HomologicallyMarkedDiagram) :
    Type

axiom turnoverH₂Identification_realizesPoincareDuality
    (marked : HomologicallyMarkedDiagram) :
    Nonempty (TurnoverPoincareDualityWitness marked)

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

/-! ## Clean band-slide graphical interpretation -/

/--
The two typed graphical stages between clean attachment and clean detachment.

This structure is data-only.  In particular, it contains no proof that either
stage is the interpretation of a Kirby diagram and no evaluation equality.
Those three external responsibilities are stated separately below.
-/
structure CleanBandGraphicalStages
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    {source target : HomologicallyMarkedDiagram}
    (_slide : CleanBandSlide source.diagram target.diagram)
    (_sourceCycle : ThamTwoCycles source.turnedOver) where
  attached : ClosedRibbonExpression 𝒞η.category
  detachable : ClosedRibbonExpression 𝒞η.category

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
    (cycle : ThamTwoCycles marked.turnedOver) :
    ClosedRibbonExpression 𝒞η.category :=
  .morphism
    (thamDefinition511Normalization
          𝒞η.category.globalDimension
          marked.diagram.handles.hThree
          marked.diagram.handles.hTwo
          marked.diagram.handles.hOne •
      ∑ labeling : TwoHandleLabeling 𝒞η.category marked.diagram,
        (ordinaryKirbyWeight 𝒞η.category labeling *
            characterWeight 𝒞η marked.turnedOver labeling cycle) •
          (canonicalRoleAwareGraphCompiler
            𝒞η marked.diagram marked.primalBoundary marked.turnedOver
              labeling cycle).graph.interpret)

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
    (sourceCycle : ThamTwoCycles source.turnedOver) :
    ∃ stages : CleanBandGraphicalStages 𝒞η slide sourceCycle,
      FramedRibbonIsotopic
        (normalizedCycleExpression 𝒞η source sourceCycle)
        stages.attached

/--
The finite coupon route gives a typed naturality derivation between the exact
attached and detachable expressions selected by the clean-attach boundary.

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
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (stages : CleanBandGraphicalStages 𝒞η slide sourceCycle) :
    CharacterCouponTransport 𝒞η.character
      stages.attached stages.detachable

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
    (sourceCycle : ThamTwoCycles source.turnedOver)
    (stages : CleanBandGraphicalStages 𝒞η slide sourceCycle) :
    FramedRibbonIsotopic
      stages.detachable
      (normalizedCycleExpression 𝒞η target
        (transport.mapCycle sourceCycle))

/-! ## Smooth four-manifold and Kirby--Cerf topology

The following three declarations are the explicit foundational vocabulary.
They are counted in the entrance-axiom ledger so that the public final theorem
can remain the human statement in `𝒞η`, `f`, and `α` without hiding ambient
parameters.
-/

axiom ClosedOrientedSmoothFourManifold : Type

axiom ManifoldH₂ :
  ClosedOrientedSmoothFourManifold → Type

axiom OrientedDiffeomorphism :
  ClosedOrientedSmoothFourManifold →
  ClosedOrientedSmoothFourManifold →
  Type

axiom manifoldH₂_addCommGroup
    (X : ClosedOrientedSmoothFourManifold) :
    AddCommGroup (ManifoldH₂ X)

attribute [instance] manifoldH₂_addCommGroup

axiom DiagramRealizationWitness :
  CombinatorialSpecialKirbyDiagram →
  ClosedOrientedSmoothFourManifold →
  Type

abbrev DiagramRealizes
    (diagram : CombinatorialSpecialKirbyDiagram)
    (X : ClosedOrientedSmoothFourManifold) : Prop :=
  Nonempty (DiagramRealizationWitness diagram X)

structure MarkedRealizationData
    (X : ClosedOrientedSmoothFourManifold) where
  markedDiagram : HomologicallyMarkedDiagram
  homologyComparison :
    PrimalKirbyH₂ markedDiagram.primalBoundary ≃+ ManifoldH₂ X

def MarkedRealizationIsCorrect
    {X : ClosedOrientedSmoothFourManifold}
    (alpha : ManifoldH₂ X)
    (realization : MarkedRealizationData X) : Prop :=
  DiagramRealizes realization.markedDiagram.diagram X ∧
    realization.homologyComparison
        realization.markedDiagram.alpha =
      alpha

axiom markedRealization_exists
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) :
    ∃ realization : MarkedRealizationData X,
      MarkedRealizationIsCorrect alpha realization

axiom inducedH₂
    {X Y : ClosedOrientedSmoothFourManifold} :
    OrientedDiffeomorphism X Y →
    ManifoldH₂ X ≃+ ManifoldH₂ Y

axiom markedKirbyCerf_complete
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : OrientedDiffeomorphism X Y)
    (alpha : ManifoldH₂ X)
    (left : MarkedRealizationData X)
    (leftCorrect : MarkedRealizationIsCorrect alpha left)
    (right : MarkedRealizationData Y)
    (rightCorrect :
      MarkedRealizationIsCorrect (inducedH₂ f alpha) right) :
    Nonempty (KirbyMovie left.markedDiagram right.markedDiagram)

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
    (left : MarkedRealizationData X)
    (leftCorrect : MarkedRealizationIsCorrect alpha left)
    (right : MarkedRealizationData Y)
    (rightCorrect :
      MarkedRealizationIsCorrect (inducedH₂ f alpha) right),
    evaluateMarking 𝒞η left.markedDiagram =
      evaluateMarking 𝒞η right.markedDiagram

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 289
