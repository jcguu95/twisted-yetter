import TwistedYetter.Kirby.Final.Semantics.Independent.Invariant
import TwistedYetter.Kirby.Final.Semantics.Independent.IntrinsicDottedCutGraphical
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

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory

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
    {𝒞 : BundledPremodularCategory K}
    {X Y : 𝒞.C} :
    RibbonExpression 𝒞 X Y → RibbonExpression 𝒞 X Y → Type

abbrev FramedRibbonIsotopic
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    {𝒞 : BundledPremodularCategory K}
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
    {𝒞 : BundledPremodularCategory K}
    {X Y : 𝒞.C}
    {left right : RibbonExpression 𝒞 X Y} :
    FramedRibbonIsotopic left right →
    left.interpret = right.interpret

/-! ## Intrinsic dotted-cut graphical interpretation -/

/--
Regluing one topologically realized intrinsic dotted cut gives the exact
compiled closed ribbon graph inside a linear one-hole exterior context.

This is the narrow topology-to-graphical boundary for the intrinsic route.
It mentions a category only in order to type and interpret the ribbon graph.
It contains no twisting character, homology exponent, scalar evaluation, or
representative-independence conclusion.  In particular, dotted direction
does not choose `X` versus `X*` and does not create a character exponent.
-/
axiom intrinsicDottedCutRegluing_hasTypedGraphicalInterpretation
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (labeling : TwoHandleLabeling 𝒞 diagram)
    (dotted : diagram.trace.ComponentId)
    (role : (diagram.trace.components dotted).role = .dotted)
    (cut : IntrinsicDottedCutTangle diagram
      (presentation.cut.punctureWord dotted role))
    (_regluing :
      IntrinsicDottedCutRegluesToDiagram
        diagram presentation dotted role cut) :
    ∃ context : LinearRibbonExpressionContext 𝒞
        (simpleLabelWordObject 𝒞
          (dottedInboundLabelWord 𝒞 diagram labeling
            (presentation.cut.punctureWord dotted role)))
        (simpleLabelWordObject 𝒞
          (dottedOutboundLabelWord 𝒞 diagram labeling
            (presentation.cut.punctureWord dotted role)))
        (𝟙_ 𝒞.C) (𝟙_ 𝒞.C),
      FramedRibbonIsotopic
        (context.plug (.morphism
          (intrinsicDottedCutMorphism 𝒞 diagram labeling cut)))
        (.morphism
          (compileCutOpenExteriorMorphism
            𝒞 diagram presentation labeling))

/--
Standard pivotal-trace normalization: the tensor unit has quantum dimension
one.  This is derived from pivotal-trace cyclicity, canonical comparison of
right duals, and the unit coherence laws.
-/
theorem standard_tensorUnitQuantumDimension
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
    𝒞.simples.quantumDimension 𝒞.simples.tensorUnit = 1 :=
  𝒞.simples.tensorUnit_quantumDimension

/--
Etingof--Nikshych--Ostrik, *On fusion categories*, Theorem 2.3:
the global dimension of a fusion category over an algebraically closed field
of characteristic zero is nonzero.
-/
axiom eno_globalDimension_ne_zero
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞 : BundledPremodularCategory K) :
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
    (_sourceCoefficients : ThamTwoHandleCoefficients source.diagram) where
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
    {sourceCoefficients : ThamTwoHandleCoefficients source.diagram}
    (normalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCoefficients) :
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
    {sourceCoefficients : ThamTwoHandleCoefficients source.diagram}
    (normalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCoefficients) :
    ClosedRibbonExpression 𝒞η.category :=
  normalForm.context.plug
    (fusionResolutionExpression 𝒞η.category
      normalForm.movingLabel normalForm.stationaryLabel)

/--
The exact normalized closed graphical expression compiled from one marked
diagram and one THAM-side cycle.

Unlike `evaluateCoefficients`, this retains the endomorphism of the tensor unit.  It
therefore permits attach, transport, and detach to be compared at the
graphical-morphism level before scalarization.
-/
noncomputable def normalizedCycleExpression
    {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
    (𝒞η : TwistedPremodularCategory K)
    (marked : HomologicallyMarkedDiagram)
    (coefficients : ThamTwoHandleCoefficients marked.diagram) :
    ClosedRibbonExpression 𝒞η.category :=
  .morphism
    (thamDefinition511Normalization
          𝒞η.category.globalDimension
          marked.diagram.handles.hThree
          marked.diagram.handles.hTwo
          marked.diagram.handles.hOne •
      ∑ labeling : TwoHandleLabeling 𝒞η.category marked.diagram,
        (ordinaryKirbyWeight 𝒞η.category labeling *
            characterWeight 𝒞η labeling coefficients) •
          (canonicalRoleAwareGraphCompiler
            𝒞η marked.diagram marked.cut
              labeling coefficients).interpret)

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
    (sourceCoefficients : ThamTwoHandleCoefficients source.diagram) :
    ∃ normalForm :
        CleanBandEndpointNormalForm 𝒞η slide sourceCoefficients,
      FramedRibbonIsotopic
        (normalizedCycleExpression 𝒞η source sourceCoefficients)
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
    (sourceCoefficients : ThamTwoHandleCoefficients source.diagram)
    :
    ∃ normalForm :
        CleanBandEndpointNormalForm 𝒞η slide sourceCoefficients,
      FramedRibbonIsotopic
        normalForm.identityStage
        (normalizedCycleExpression 𝒞η target
          (transport.mapCoefficients sourceCoefficients))

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
    (sourceCoefficients : ThamTwoHandleCoefficients source.diagram)
    (attachNormalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCoefficients)
    (detachNormalForm :
      CleanBandEndpointNormalForm 𝒞η slide sourceCoefficients) :
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
    (sourceCoefficients : ThamTwoHandleCoefficients source.diagram) :
    FramedRibbonIsotopic
      (normalizedCycleExpression 𝒞η source sourceCoefficients)
      (normalizedCycleExpression 𝒞η target
        (transport.mapCoefficients sourceCoefficients))

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

/-! ## Explicit classical topology relations -/

/--
`PresentsClosedFourManifold D X` means that the displayed zero-, one-, and
two-handle data of `D` can be completed by exactly `D.handles.hThree`
unrecorded three-handles and the unique four-handle to a closed oriented
smooth four-manifold oriented-diffeomorphic to `X`.

This is deliberately a relation, not a realization algorithm and not a
certificate containing attaching spheres.  It mentions no category,
character, evaluator, scalar, homology comparison, or invariance conclusion.
-/
axiom PresentsClosedFourManifold :
  SpecialKirbyDiagram → ClosedOrientedSmoothFourManifold → Prop

/--
`RepresentsPoincareDualClass presentation beta alpha` means that the ambient
THAM marking `beta`, represented by integral primal-two-handle coefficients
modulo the visible coboundaries `im(∂₂ᵀ)`, is the coordinate class of
`PD(alpha)` in the turned-over handle decomposition underlying
`presentation`.

The relation does not expose or reconstruct the unrecorded three-handle
attaching spheres.  In particular, it does not assert that every element of
`ThamMarkingClass D` is a genuine cohomology class; it selects only the classes
which arise from the stated manifold homology class.
-/
axiom RepresentsPoincareDualClass
    {diagram : SpecialKirbyDiagram}
    {X : ClosedOrientedSmoothFourManifold}
    (_presentation : PresentsClosedFourManifold diagram X) :
    ThamMarkingClass diagram → ManifoldH₂ X → Prop

structure SpecialKirbyRepresentativeOf
    (X : ClosedOrientedSmoothFourManifold) where
  diagram : SpecialKirbyDiagram
  cut : DottedCutPresentation diagram
  presents : PresentsClosedFourManifold diagram X
  thamAlpha : ThamMarkingClass diagram

noncomputable def SpecialKirbyRepresentativeOf.toHomologicallyMarkedDiagram
    {X : ClosedOrientedSmoothFourManifold}
    (representative : SpecialKirbyRepresentativeOf X) :
    HomologicallyMarkedDiagram :=
  { diagram := representative.diagram
    cut := representative.cut
    thamAlpha := representative.thamAlpha }

def SpecialKirbyRepresentativeOf.representsHomologyClass
    {X : ClosedOrientedSmoothFourManifold}
    (alpha : ManifoldH₂ X)
    (representative : SpecialKirbyRepresentativeOf X) : Prop :=
  RepresentsPoincareDualClass
    representative.presents representative.thamAlpha alpha

/--
T1/T2. Every marked closed oriented smooth four-manifold `(X, alpha)` admits
at least one special Kirby representative with a cut-open presentation and an
ambient THAM marking representing `PD(alpha)`.

This is an external handle-topology existence statement.  It does not compute
a diagram, a three-handle attachment, or a coefficient vector, and it does not
assert an evaluator equality.
-/
axiom specialKirbyRepresentative_exists
    (X : ClosedOrientedSmoothFourManifold)
    (alpha : ManifoldH₂ X) :
    ∃ representative : SpecialKirbyRepresentativeOf X,
      representative.representsHomologyClass alpha

/--
T3. Marked Kirby--Cerf completeness for the two explicit topology relations.

If two representatives describe classes related by an oriented
diffeomorphism, there is a finite Kirby movie between their exact ambient
THAM markings.  The endpoints are constrained by
`RepresentsPoincareDualClass`; no caller may choose unrelated markings.
-/
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

end

end TwistedYetter.Semantics.Independent

-- semantic-freeze-padding: 50
