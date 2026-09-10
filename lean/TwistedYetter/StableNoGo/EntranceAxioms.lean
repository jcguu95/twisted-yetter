import TwistedYetter.StableNoGo.ConnectedSum
import TwistedYetter.Kirby.Final.Semantics.Independent.LocalReplacementSyntax

/-!
# Explicit entrance axioms for the stable no-go theorem

This file fixes the external trust boundary of the new stable no-go argument.
It was drafted on 2026-08-03 after comparing the Lean statement with the
revised prose proof and the cited primary sources.

The declarations below are deliberately separated from project obligations.
In particular, this file does **not** assume any connected-sum formula for
`TwistedYetter`, any evaluator equality, any stabilization scalar, or the final
marked-intersection-form theorem.

External topology inputs:

* naturality of the intersection pairing under oriented diffeomorphism;
* composition and connected sum of oriented diffeomorphisms, together with
  their exact action on integral second homology;
* Wall's stable classification theorem;
* Ruberman--Strle's one-stable realization theorem.

External category input:

* the premodular Kirby-colour killing identity.

The nonvanishing of fusion-category global dimension is already the separately
named literature input `eno_globalDimension_ne_zero` in the frozen frontend.

The split-special-Kirby-presentation boundary below is exposed through exact
serialized component, strand, event, active-order, handle-index, and marking
bindings.  It is not an opaque `isSplit` predicate and contains no category or
evaluator equality.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped BigOperators
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/-! ## Transparent split-presentation syntax -/

def shiftSerializedStrand (componentOffset : ℕ) :
    SerializedStrand → SerializedStrand
  | strand =>
      { component := componentOffset + strand.component
        orientation := strand.orientation }

def shiftSerializedPuncture
    (componentOffset strandOffset : ℕ) :
    SerializedPuncture → SerializedPuncture
  | puncture =>
      { dottedComponent := componentOffset + puncture.dottedComponent
        twoHandleComponent := componentOffset + puncture.twoHandleComponent
        inputStrand := strandOffset + puncture.inputStrand
        outputStrand := strandOffset + puncture.outputStrand
        direction := puncture.direction
        cutPosition := puncture.cutPosition }

def shiftSerializedCutOpenEvent
    (componentOffset strandOffset : ℕ) :
    SerializedCutOpenEvent → SerializedCutOpenEvent
  | .birth left right =>
      .birth (strandOffset + left) (strandOffset + right)
  | .death left right =>
      .death (strandOffset + left) (strandOffset + right)
  | .crossing overInput underInput overOutput underOutput sign =>
      .crossing
        (strandOffset + overInput) (strandOffset + underInput)
        (strandOffset + overOutput) (strandOffset + underOutput) sign
  | .framingTwist input output sign =>
      .framingTwist (strandOffset + input) (strandOffset + output) sign
  | .planarIsotopy continuations =>
      .planarIsotopy
        (continuations.map fun pair =>
          (strandOffset + pair.1, strandOffset + pair.2))
  | .projectorHole dotted punctures =>
      .projectorHole (componentOffset + dotted)
        (punctures.map
          (shiftSerializedPuncture componentOffset strandOffset))

def shiftSerializedActiveOrder (strandOffset : ℕ) :
    List ℕ → List ℕ :=
  List.map (strandOffset + ·)

/--
The exact category-neutral syntax saying that one certified presentation is the
split union of two others in disjoint three-balls.
-/
structure SplitSpecialKirbyPresentation
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (left : SpecialKirbyRepresentativeOf X)
    (right : SpecialKirbyRepresentativeOf Y) where
  target : SpecialKirbyRepresentativeOf (connectedSum X Y)
  twoHandleEquiv :
    Fin target.diagram.handles.hTwo ≃
      Fin left.diagram.handles.hTwo ⊕ Fin right.diagram.handles.hTwo
  hOne_additive :
    target.diagram.handles.hOne =
      left.diagram.handles.hOne + right.diagram.handles.hOne
  hThree_additive :
    target.diagram.handles.hThree =
      left.diagram.handles.hThree + right.diagram.handles.hThree
  components_split :
    serializedComponents target.diagram =
      serializedComponents left.diagram ++
        serializedComponents right.diagram
  strands_split :
    serializedStrands target.diagram =
      serializedStrands left.diagram ++
        (serializedStrands right.diagram).map
          (shiftSerializedStrand left.diagram.trace.componentCount)
  events_split :
    serializedExteriorEvents target.cut =
      serializedExteriorEvents left.cut ++
        (serializedExteriorEvents right.cut).map
          (shiftSerializedCutOpenEvent
            left.diagram.trace.componentCount
            left.diagram.trace.strandCount)
  activeOrders_split :
    serializedActiveOrders target.cut =
      serializedActiveOrders left.cut ++
        ((serializedActiveOrders right.cut).map
          (shiftSerializedActiveOrder left.diagram.trace.strandCount)).tail
  leftTwoHandleComponent :
    ∀ handle : Fin left.diagram.handles.hTwo,
      (target.diagram.handles.twoHandleIndex
          (twoHandleEquiv.symm (Sum.inl handle))).1.1 =
        (left.diagram.handles.twoHandleIndex handle).1.1
  rightTwoHandleComponent :
    ∀ handle : Fin right.diagram.handles.hTwo,
      (target.diagram.handles.twoHandleIndex
          (twoHandleEquiv.symm (Sum.inr handle))).1.1 =
        left.diagram.trace.componentCount +
          (right.diagram.handles.twoHandleIndex handle).1.1

/--
The chain-level form of connected-sum naturality needed by the character
exponents.  Every coordinate equation is stated independently of any category.
-/
structure SplitMarkingNaturality
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (alpha : ManifoldH₂ X)
    (beta : ManifoldH₂ Y)
    (_leftRepresents : left.representsHomologyClass alpha)
    (_rightRepresents : right.representsHomologyClass beta)
    (split : SplitSpecialKirbyPresentation left right) where
  leftCoefficients : ThamTwoHandleCoefficients left.diagram
  rightCoefficients : ThamTwoHandleCoefficients right.diagram
  targetCoefficients : ThamTwoHandleCoefficients split.target.diagram
  leftCoefficients_class :
    thamMarkingClass leftCoefficients = left.thamAlpha
  rightCoefficients_class :
    thamMarkingClass rightCoefficients = right.thamAlpha
  targetCoefficients_class :
    thamMarkingClass targetCoefficients = split.target.thamAlpha
  target_represents_connectedSum :
    split.target.representsHomologyClass
      (connectedSumMarking alpha beta)
  left_coordinates :
    ∀ handle : Fin left.diagram.handles.hTwo,
      targetCoefficients (split.twoHandleEquiv.symm (Sum.inl handle)) =
        leftCoefficients handle
  right_coordinates :
    ∀ handle : Fin right.diagram.handles.hTwo,
      targetCoefficients (split.twoHandleEquiv.symm (Sum.inr handle)) =
        rightCoefficients handle

/--
Standard split-union realization: two certified special presentations placed in
disjoint three-balls give a certified presentation of the manifold connected
sum, with the exact transparent syntax recorded above.
-/
axiom splitSpecialKirbyPresentation_exists
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (left : SpecialKirbyRepresentativeOf X)
    (right : SpecialKirbyRepresentativeOf Y) :
    Nonempty (SplitSpecialKirbyPresentation left right)

/--
For the standard split presentation, the two Poincare-dual marking relations
admit coefficient representatives whose restrictions are the two original
representatives and whose target class represents the connected-sum marking.
-/
axiom splitSpecialKirbyPresentation_marking_natural
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    {left : SpecialKirbyRepresentativeOf X}
    {right : SpecialKirbyRepresentativeOf Y}
    (alpha : ManifoldH₂ X)
    (beta : ManifoldH₂ Y)
    (leftRepresents : left.representsHomologyClass alpha)
    (rightRepresents : right.representsHomologyClass beta)
    (split : SplitSpecialKirbyPresentation left right) :
    Nonempty
      (SplitMarkingNaturality
        alpha beta leftRepresents rightRepresents split)

/-! ## Transparent connected-sum homology notation -/

/--
The direct-sum map on second homology, transported through the fixed
Mayer--Vietoris identifications for connected sums.
-/
def connectedSumH₂Map
    {X X' Y Y' : ClosedConnectedOrientedSmoothFourManifold}
    (f : ManifoldH₂ X ≃+ ManifoldH₂ X')
    (g : ManifoldH₂ Y ≃+ ManifoldH₂ Y') :
    ManifoldH₂ (connectedSum X Y) ≃+
      ManifoldH₂ (connectedSum X' Y') :=
  (connectedSumH₂ X Y).trans
    ((f.prodCongr g).trans (connectedSumH₂ X' Y').symm)

@[simp]
theorem connectedSumH₂Map_apply
    {X X' Y Y' : ClosedConnectedOrientedSmoothFourManifold}
    (f : ManifoldH₂ X ≃+ ManifoldH₂ X')
    (g : ManifoldH₂ Y ≃+ ManifoldH₂ Y')
    (alpha : ManifoldH₂ X) (beta : ManifoldH₂ Y) :
    connectedSumH₂Map f g (connectedSumMarking alpha beta) =
      connectedSumMarking (f alpha) (g beta) := by
  simp [connectedSumH₂Map, connectedSumMarking]
  rfl

/-! ## Standard functorial topology boundaries -/

/-! ### Standard simply connected four-manifolds -/

/-- The standard oriented complex projective plane. -/
axiom complexProjectivePlane : ClosedConnectedOrientedSmoothFourManifold

/-- The complex projective plane with reversed orientation. -/
axiom reversedComplexProjectivePlane : ClosedConnectedOrientedSmoothFourManifold

/-- The oriented four-sphere. -/
axiom fourSphere : ClosedConnectedOrientedSmoothFourManifold

/-- The standard oriented `K3` surface. -/
axiom k3Surface : ClosedConnectedOrientedSmoothFourManifold

/-- The `K3` surface with reversed orientation. -/
axiom reversedK3Surface : ClosedConnectedOrientedSmoothFourManifold

/-- `CP²` is simply connected. -/
axiom complexProjectivePlane_simplyConnected :
    IsSimplyConnected complexProjectivePlane

/-- Reversing the orientation of `CP²` does not change its fundamental group. -/
axiom reversedComplexProjectivePlane_simplyConnected :
    IsSimplyConnected reversedComplexProjectivePlane

/-- `S⁴` is simply connected. -/
axiom fourSphere_simplyConnected : IsSimplyConnected fourSphere

/-- `K3` is simply connected. -/
axiom k3Surface_simplyConnected : IsSimplyConnected k3Surface

/-- Reversing the orientation of `K3` does not change its fundamental group. -/
axiom reversedK3Surface_simplyConnected :
    IsSimplyConnected reversedK3Surface

/-! ### Standard rank-one and zero intersection forms -/

/-- The standard generator coordinate on `H₂(CP²; Z)`. -/
axiom complexProjectivePlaneH₂ :
    ManifoldH₂ complexProjectivePlane ≃+ ℤ

/-- In the standard coordinate, the intersection form of `CP²` is `⟨1⟩`. -/
axiom complexProjectivePlane_intersectionForm
    (a b : ManifoldH₂ complexProjectivePlane) :
    integralIntersectionPairing complexProjectivePlane a b =
      complexProjectivePlaneH₂ a * complexProjectivePlaneH₂ b

/-- The positive generator of `H₂(CP²; Z)`. -/
def positiveProjectivePlaneGenerator :
    ManifoldH₂ complexProjectivePlane :=
  complexProjectivePlaneH₂.symm 1

/-- The standard generator coordinate on `H₂(CPbar²; Z)`. -/
axiom reversedComplexProjectivePlaneH₂ :
    ManifoldH₂ reversedComplexProjectivePlane ≃+ ℤ

/-- In the standard coordinate, the intersection form of `CPbar²` is `⟨-1⟩`. -/
axiom reversedComplexProjectivePlane_intersectionForm
    (a b : ManifoldH₂ reversedComplexProjectivePlane) :
    integralIntersectionPairing reversedComplexProjectivePlane a b =
      -(reversedComplexProjectivePlaneH₂ a *
        reversedComplexProjectivePlaneH₂ b)

/-- The negative generator of `H₂(CPbar²; Z)`. -/
def negativeProjectivePlaneGenerator :
    ManifoldH₂ reversedComplexProjectivePlane :=
  reversedComplexProjectivePlaneH₂.symm 1

/-- Integral second homology of `S⁴` is trivial. -/
axiom fourSphere_H₂_eq_zero (alpha : ManifoldH₂ fourSphere) : alpha = 0

/-- The integral intersection form of `S⁴` is zero. -/
theorem fourSphere_intersectionForm_eq_zero
    (alpha beta : ManifoldH₂ fourSphere) :
    integralIntersectionPairing fourSphere alpha beta = 0 := by
  rw [fourSphere_H₂_eq_zero alpha, fourSphere_H₂_eq_zero beta]
  simp

/--
An oriented diffeomorphism preserves the integral intersection pairing.
-/
axiom orientedDiffeomorphism_preservesIntersectionPairing
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (g : OrientedDiffeomorphism X Y)
    (a b : ManifoldH₂ X) :
    integralIntersectionPairing Y (inducedH₂ g a) (inducedH₂ g b) =
      integralIntersectionPairing X a b

/-- `S² × S²` is simply connected. -/
axiom sphereTwoProduct_simplyConnected :
    IsSimplyConnected sphereTwoProduct

/-- Connected sum preserves simple connectivity. -/
axiom connectedSum_simplyConnected
    {X Y : ClosedConnectedOrientedSmoothFourManifold} :
    IsSimplyConnected X →
      IsSimplyConnected Y →
        IsSimplyConnected (connectedSum X Y)

/--
The Mayer--Vietoris splitting identifies the connected-sum intersection form
with the orthogonal direct sum of the two original intersection forms.
-/
axiom connectedSumH₂_preservesIntersectionPairing
    (X Y : ClosedConnectedOrientedSmoothFourManifold)
    (a a' : ManifoldH₂ X) (b b' : ManifoldH₂ Y) :
    integralIntersectionPairing (connectedSum X Y)
        (connectedSumMarking a b) (connectedSumMarking a' b') =
      integralIntersectionPairing X a a' +
        integralIntersectionPairing Y b b'

/-- Identity orientation-preserving diffeomorphism. -/
axiom identityOrientedDiffeomorphism
    (X : ClosedConnectedOrientedSmoothFourManifold) :
    OrientedDiffeomorphism X X

/-- The identity diffeomorphism induces the identity on integral `H₂`. -/
axiom inducedH₂_identityOrientedDiffeomorphism
    (X : ClosedConnectedOrientedSmoothFourManifold) :
    inducedH₂ (identityOrientedDiffeomorphism X) =
      AddEquiv.refl (ManifoldH₂ X)

/-- The intersection-form isometry induced by an oriented diffeomorphism. -/
def intersectionFormIsometryOfDiffeomorphism
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (g : OrientedDiffeomorphism X Y) :
    IntegralIntersectionFormIsometry X Y where
  toAddEquiv := inducedH₂ g
  preservesPairing :=
    orientedDiffeomorphism_preservesIntersectionPairing g

/-- Composition of orientation-preserving diffeomorphisms. -/
axiom composeOrientedDiffeomorphism
    {X Y Z : ClosedConnectedOrientedSmoothFourManifold}
    (g : OrientedDiffeomorphism X Y)
    (h : OrientedDiffeomorphism Y Z) :
    OrientedDiffeomorphism X Z

/-- The homology action of a composite is the composite homology action. -/
axiom inducedH₂_composeOrientedDiffeomorphism
    {X Y Z : ClosedConnectedOrientedSmoothFourManifold}
    (g : OrientedDiffeomorphism X Y)
    (h : OrientedDiffeomorphism Y Z) :
    inducedH₂ (composeOrientedDiffeomorphism g h) =
      (inducedH₂ g).trans (inducedH₂ h)

/-- Connected sum of orientation-preserving diffeomorphisms. -/
axiom connectedSumOrientedDiffeomorphism
    {X X' Y Y' : ClosedConnectedOrientedSmoothFourManifold}
    (g : OrientedDiffeomorphism X X')
    (h : OrientedDiffeomorphism Y Y') :
    OrientedDiffeomorphism (connectedSum X Y) (connectedSum X' Y')

/--
Under the fixed Mayer--Vietoris splittings, the homology action of `g # h` is
exactly `g_* ⊕ h_*`.
-/
axiom inducedH₂_connectedSumOrientedDiffeomorphism
    {X X' Y Y' : ClosedConnectedOrientedSmoothFourManifold}
    (g : OrientedDiffeomorphism X X')
    (h : OrientedDiffeomorphism Y Y') :
    inducedH₂ (connectedSumOrientedDiffeomorphism g h) =
      connectedSumH₂Map (inducedH₂ g) (inducedH₂ h)

/-! ## Wall and Ruberman--Strle -/

/--
Wall stable classification (Wall 1964, *On simply-connected 4-manifolds*,
Theorems 2--3): intersection-form-isometric closed simply connected oriented
smooth four-manifolds become orientation-preservingly diffeomorphic after the
same finite number of `S² × S²` stabilizations.

No claim is made here about the induced homology action of the resulting
diffeomorphism.
-/
axiom wall_stableClassification
    {X Y : ClosedConnectedOrientedSmoothFourManifold}
    (simplyConnectedX : IsSimplyConnected X)
    (simplyConnectedY : IsSimplyConnected Y)
    (f : IntegralIntersectionFormIsometry X Y) :
    Σ n : Nat, OrientedDiffeomorphism (stabilize X n) (stabilize Y n)

/--
Ruberman--Strle, Theorem 2.1 (arXiv:2210.16260v2, PDF p. 2): for every
intersection-form automorphism `A` of a closed simply connected smooth
four-manifold `Z`, the extension `A ⊕ id_H` is realized by an
orientation-preserving self-diffeomorphism of `Z # (S² × S²)`.

The displayed equality is the complete homology action under the fixed
Mayer--Vietoris splitting, not merely its restriction to the old summand.
-/
axiom rubermanStrle_oneStableRealization
    {Z : ClosedConnectedOrientedSmoothFourManifold}
    (simplyConnectedZ : IsSimplyConnected Z)
    (A : IntegralIntersectionFormIsometry Z Z) :
    ∃ h : OrientedDiffeomorphism
        (connectedSum Z sphereTwoProduct)
        (connectedSum Z sphereTwoProduct),
      inducedH₂ h =
        connectedSumH₂Map A.toAddEquiv
          (AddEquiv.refl (ManifoldH₂ sphereTwoProduct))

/-! ## Premodular Kirby-colour killing -/

/-- A simple object is transparent when its monodromy with every object is identity. -/
def IsTransparentSimple
    (𝒞 : CategoryTheory.BundledPremodularCategory K)
    (j : 𝒞.Simple) : Prop :=
  ∀ X : 𝒞.C,
    monodromyHom (𝒞.simpleObject j) X =
      𝟙 (𝒞.simpleObject j ⊗ X)

/-- The scalar evaluation of the positively oriented Hopf link labelled `i,j`. -/
noncomputable def positiveHopfLinkScalar
    (𝒞 : CategoryTheory.BundledPremodularCategory K)
    (i j : 𝒞.Simple) : K :=
  𝒞.closedScalar
    (𝒞.canonicalRibbonTrace
      (monodromyHom (𝒞.simpleObject i) (𝒞.simpleObject j)))

/--
Premodular Kirby-colour killing (Bärenz--Barrett, Lemma 2.46; originally
Bruguières, Lemma 1.4.2), in the positive Hopf-link convention fixed above.

This is a local ribbon-fusion identity.  It does not mention a four-manifold,
the Twisted Yetter evaluator, or an invariance conclusion.
-/
axiom premodularKirbyColourKilling
    (𝒞 : CategoryTheory.BundledPremodularCategory K)
    (j : 𝒞.Simple) :
    (IsTransparentSimple 𝒞 j →
      (∑ i : 𝒞.Simple,
          𝒞.quantumDimension i * positiveHopfLinkScalar 𝒞 i j) =
        𝒞.globalDimension * 𝒞.quantumDimension j) ∧
    (¬IsTransparentSimple 𝒞 j →
      (∑ i : 𝒞.Simple,
          𝒞.quantumDimension i * positiveHopfLinkScalar 𝒞 i j) = 0)

end

end TwistedYetter.StableNoGo
