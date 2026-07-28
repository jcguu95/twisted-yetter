import TwistedYetter.Kirby.Final.Semantics.IndependentHomologyMarkingSpecification

/-!
# Independent human specification of Kirby-move H₂ transport

This file is normative.  It was written from the human handle-chain meaning
of the eight Kirby moves without importing or inspecting this repository's
move compiler, move transport, evaluator, descent, Sage, or bridge code.

The direction of every map in this file is source to target.

There are two deliberately separate layers:

1. a chain map, which mechanically induces a map on
   `ker(∂₂) / im(∂₃)`;
2. a move-specific handle formula saying what that chain map does to the
   individually indexed handle orientation lines.

No category, character, graphical evaluation, scalar, or invariant equality
occurs here.
-/

namespace TwistedYetter.Kirby.Final.IndependentMoveHomologyTransportSpecification

open CategoryTheory
open IndependentPresentationSpecification
open IndependentHomologyMarkingSpecification

universe uKnot uFramed uDisk uPoint uBunching uThreeManifold

variable
  {geometry :
    KirbyGeometrySemantics
      (uKnot := uKnot)
      (uFramed := uFramed)
      (uDisk := uDisk)
      (uPoint := uPoint)
      (uBunching := uBunching)
      (uThreeManifold := uThreeManifold)}

/-- The local sign fixed by the oriented band or canceling pair. -/
inductive LocalSign where
  | positive
  | negative
deriving DecidableEq

/-- The integer represented by a local sign after compatible generators are chosen. -/
def LocalSign.integer : LocalSign → ℤ
  | .positive => 1
  | .negative => -1

/--
A source-to-target chain map in degrees three, two, and one.

The two displayed equations are exactly the chain-map equations.  They are
what make cycles map to cycles and boundaries map to boundaries.
-/
structure HandleChainMap
    (source target : SpecialKirbyDiagram geometry) where
  mapOne :
    source.handleBoundary.oneChains.carrier ⟶
      target.handleBoundary.oneChains.carrier
  mapTwo :
    source.handleBoundary.twoChains.carrier ⟶
      target.handleBoundary.twoChains.carrier
  mapThree :
    source.handleBoundary.threeChains.carrier ⟶
      target.handleBoundary.threeChains.carrier

  commutes_boundaryTwo :
    mapTwo ≫ target.handleBoundary.boundaryTwo =
      source.handleBoundary.boundaryTwo ≫ mapOne
  commutes_boundaryThree :
    mapThree ≫ target.handleBoundary.boundaryThree =
      source.handleBoundary.boundaryThree ≫ mapTwo

  mapCycle :
    TwoCycle source → TwoCycle target
  mapCycle_chain :
    ∀ cycle,
      (mapCycle cycle).chain = mapTwo cycle.chain
  respects_homology :
    ∀ a b,
      Homologous a b →
        Homologous (mapCycle a) (mapCycle b)

/--
The induced map on the actual marking quotient.

There is no separately supplied "correct α transport": it is the quotient
map mechanically induced by `mapCycle`.
-/
def HandleChainMap.inducedH₂
    {source target : SpecialKirbyDiagram geometry}
    (transport : HandleChainMap source target) :
    KirbyH₂ source → KirbyH₂ target :=
  Quotient.map transport.mapCycle transport.respects_homology

/--
A chain-level transport that is an equivalence on H₂.

Birth/death need not be isomorphisms of chain groups: they add or remove an
acyclic adjacent-degree pair.  Therefore the exact requirement is that the
explicit forward and backward chain maps induce mutually inverse maps on the
H₂ quotient.
-/
structure HandleHomologyEquivalence
    (source target : SpecialKirbyDiagram geometry) where
  forward : HandleChainMap source target
  backward : HandleChainMap target source
  backward_forward :
    ∀ α,
      backward.inducedH₂ (forward.inducedH₂ α) = α
  forward_backward :
    ∀ β,
      forward.inducedH₂ (backward.inducedH₂ β) = β

/-- The source-to-target transport of an H₂ marking. -/
def HandleHomologyEquivalence.transport
    {source target : SpecialKirbyDiagram geometry}
    (equivalence : HandleHomologyEquivalence source target) :
    KirbyH₂ source → KirbyH₂ target :=
  equivalence.forward.inducedH₂

/--
The complete and deliberately small grammar of permitted maps on
handle-indexed orientation lines.

* `signedReindex` sends each source handle line to exactly one target handle
  line, with coefficient `+1` or `-1`.
* `identity` is the index-preserving special case.
* `shear` sends the named moving generator to itself plus or minus the named
  stationary generator and fixes every other generator.
* `includeLast` includes all old generators and creates no coefficient on the
  new last generator.
* `projectLast` fixes all old generators and kills the new last generator.

The equalities on handle counts are explicit arguments, so none of these
constructors can silently change rank.
-/
inductive DegreeFormula (sourceCount targetCount : ℕ) where
  | signedReindex
      (forward : Fin sourceCount → Fin targetCount)
      (backward : Fin targetCount → Fin sourceCount)
      (forward_backward : ∀ j, forward (backward j) = j)
      (backward_forward : ∀ i, backward (forward i) = i)
      (sign : Fin sourceCount → LocalSign)
  | identity
      (sameCount : sourceCount = targetCount)
  | shear
      (sameCount : sourceCount = targetCount)
      (moving stationary : Fin sourceCount)
      (distinct : moving ≠ stationary)
      (sign : LocalSign)
  | includeLast
      (targetAddsOne : targetCount = sourceCount + 1)
  | projectLast
      (sourceAddsOne : sourceCount = targetCount + 1)

/--
The topology/algebra interface for reading a coordinate-free handle map in
temporary compatible orientation charts.

This relation means literally that `map` has the displayed integer matrix
specified by `formula` with respect to the individual handle-line
generators.  It contains no category or evaluator statement.
-/
axiom HandleMapHasFormula
    {sourceCount targetCount : ℕ}
    (source : HandleIndexedOrientationModule sourceCount)
    (target : HandleIndexedOrientationModule targetCount)
    (map : source.carrier ⟶ target.carrier)
    (formula : DegreeFormula sourceCount targetCount) :
    Prop

/--
The exact handle-chain formula carried by one elementary move.

The formula is deliberately separated by degree.  The fields below say
which handles are geometrically involved; the matrices say exactly how every
handle generator is transported.
-/
structure MoveChainFormula
    (source target : SpecialKirbyDiagram geometry) where
  degreeOne :
    DegreeFormula
      source.geometric.hOne
      target.geometric.hOne
  degreeTwo :
    DegreeFormula
      source.geometric.hTwo
      target.geometric.hTwo
  degreeThree :
    DegreeFormula
      source.geometric.hThree
      target.geometric.hThree

/-- The explicit chain map realizes all three displayed handle formulas. -/
def RealizesMoveChainFormula
    {source target : SpecialKirbyDiagram geometry}
    (transport : HandleChainMap source target)
    (formula : MoveChainFormula source target) : Prop :=
  HandleMapHasFormula
      source.handleBoundary.oneChains
      target.handleBoundary.oneChains
      transport.mapOne
      formula.degreeOne ∧
    HandleMapHasFormula
      source.handleBoundary.twoChains
      target.handleBoundary.twoChains
      transport.mapTwo
      formula.degreeTwo ∧
    HandleMapHasFormula
      source.handleBoundary.threeChains
      target.handleBoundary.threeChains
      transport.mapThree
      formula.degreeThree

/--
The eight directed move kinds.  Birth and death remain distinct because
their source-to-target chain maps point in opposite directions.
-/
inductive MoveKind where
  | framedIsotopy
  | oneOverOne
  | twoOverOne
  | twoOverTwo
  | oneTwoBirth
  | oneTwoDeath
  | twoThreeBirth
  | twoThreeDeath
deriving DecidableEq

/-- A move formula consists only of signed reindexings. -/
def MoveChainFormula.IsSignedReindexing
    {source target : SpecialKirbyDiagram geometry}
    (formula : MoveChainFormula source target) : Prop :=
  (∃ f g h₁ h₂ sign,
      formula.degreeOne =
        .signedReindex f g h₁ h₂ sign) ∧
    (∃ f g h₁ h₂ sign,
      formula.degreeTwo =
        .signedReindex f g h₁ h₂ sign) ∧
    (∃ f g h₁ h₂ sign,
      formula.degreeThree =
        .signedReindex f g h₁ h₂ sign)

/--
The exact coordinate-free topology boundary for a clean cancellation pair.

For `oneTwo`, the new last degree-two handle has boundary `±` the new last
degree-one handle and has no old degree-one term.

For `twoThree`, the new last degree-three handle has boundary `±` the new
last degree-two handle, the new degree-two handle has zero degree-two
boundary, and neither equation contains an old-handle term.
-/
inductive CancellationBlockKind where
  | oneTwo
  | twoThree

axiom HasIsolatedAcyclicCancellationBlock
    (kind : CancellationBlockKind)
    (source target : SpecialKirbyDiagram geometry)
    (sign : LocalSign) :
    Prop

/--
Framed isotopy only reindexes the same handles, possibly changing temporary
orientation generators by signs.  It neither creates a handle nor performs
an elementary handle-basis shear.
-/
structure FramedIsotopyTransport
    (source target : SpecialKirbyDiagram geometry) where
  equivalence : HandleHomologyEquivalence source target
  formula : MoveChainFormula source target
  realizes_formula :
    RealizesMoveChainFormula equivalence.forward formula
  formula_is_signed_reindexing :
    formula.IsSignedReindexing

/--
A 1/1 slide performs one elementary shear in degree one.

The moving and stationary dotted components are distinct.  Degree two and
degree three are transported by their unchanged component correspondences;
the chain-map equations force the changed incidence data to match the
degree-one shear.
-/
structure OneOverOneTransport
    (source target : SpecialKirbyDiagram geometry) where
  moving : Fin source.geometric.hOne
  stationary : Fin source.geometric.hOne
  distinct : moving ≠ stationary
  sign : LocalSign
  same_handle_counts :
    source.geometric.hOne = target.geometric.hOne ∧
      source.geometric.hTwo = target.geometric.hTwo ∧
      source.geometric.hThree = target.geometric.hThree
  equivalence : HandleHomologyEquivalence source target
  formula : MoveChainFormula source target
  degree_one_is_elementary_shear :
    formula.degreeOne =
      .shear
        same_handle_counts.1
        moving
        stationary
        distinct
        sign
  degree_two_is_identity :
    formula.degreeTwo =
      .identity same_handle_counts.2.1
  degree_three_is_identity :
    formula.degreeThree =
      .identity same_handle_counts.2.2
  realizes_formula :
    RealizesMoveChainFormula equivalence.forward formula

/--
A 2/1 passage changes the attaching geometry but creates no handle and does
not rename a handle generator.

Its chain transport is the identity correspondence in all three degrees.
The nontrivial obligation is geometric: the source and target incidence maps
must still satisfy the chain-map equations for this identity transport.
-/
structure TwoOverOneTransport
    (source target : SpecialKirbyDiagram geometry) where
  movingTwoHandle : Fin source.geometric.hTwo
  stationaryOneHandle : Fin source.geometric.hOne
  sign : LocalSign
  same_handle_counts :
    source.geometric.hOne = target.geometric.hOne ∧
      source.geometric.hTwo = target.geometric.hTwo ∧
      source.geometric.hThree = target.geometric.hThree
  equivalence : HandleHomologyEquivalence source target
  formula : MoveChainFormula source target
  degree_one_is_identity :
    formula.degreeOne =
      .identity same_handle_counts.1
  degree_two_is_identity :
    formula.degreeTwo =
      .identity same_handle_counts.2.1
  degree_three_is_identity :
    formula.degreeThree =
      .identity same_handle_counts.2.2
  realizes_formula :
    RealizesMoveChainFormula equivalence.forward formula

/--
A 2/2 slide performs one elementary shear in degree two.

The moving and stationary ordinary framed components are distinct.  Degree
one and degree three follow their component correspondences; the chain-map
equations encode the corresponding changes of `∂₂` and `∂₃`.
-/
structure TwoOverTwoTransport
    (source target : SpecialKirbyDiagram geometry) where
  moving : Fin source.geometric.hTwo
  stationary : Fin source.geometric.hTwo
  distinct : moving ≠ stationary
  sign : LocalSign
  same_handle_counts :
    source.geometric.hOne = target.geometric.hOne ∧
      source.geometric.hTwo = target.geometric.hTwo ∧
      source.geometric.hThree = target.geometric.hThree
  equivalence : HandleHomologyEquivalence source target
  formula : MoveChainFormula source target
  degree_one_is_identity :
    formula.degreeOne =
      .identity same_handle_counts.1
  degree_two_is_elementary_shear :
    formula.degreeTwo =
      .shear
        same_handle_counts.2.1
        moving
        stationary
        distinct
        sign
  degree_three_is_identity :
    formula.degreeThree =
      .identity same_handle_counts.2.2
  realizes_formula :
    RealizesMoveChainFormula equivalence.forward formula

/--
An explicit 1--2 birth adds one new degree-one generator and one new
degree-two generator forming an acyclic block:

`∂₂(new two-handle) = ± new one-handle`,

with no old-handle term.  Old generators include unchanged.  Projection
deletes the new pair.  The supplied chain homology equivalence proves that
these maps induce the canonical H₂ identification.
-/
structure OneTwoBirthTransport
    (source target : SpecialKirbyDiagram geometry) where
  sign : LocalSign
  handle_counts :
    target.geometric.hOne = source.geometric.hOne + 1 ∧
      target.geometric.hTwo = source.geometric.hTwo + 1 ∧
      target.geometric.hThree = source.geometric.hThree
  equivalence : HandleHomologyEquivalence source target
  forwardFormula : MoveChainFormula source target
  backwardFormula : MoveChainFormula target source
  forward_degree_one_includes_old :
    forwardFormula.degreeOne =
      .includeLast handle_counts.1
  forward_degree_two_includes_old :
    forwardFormula.degreeTwo =
      .includeLast handle_counts.2.1
  forward_degree_three_is_identity :
    forwardFormula.degreeThree =
      .identity handle_counts.2.2.symm
  backward_degree_one_deletes_new :
    backwardFormula.degreeOne =
      .projectLast handle_counts.1
  backward_degree_two_deletes_new :
    backwardFormula.degreeTwo =
      .projectLast handle_counts.2.1
  backward_degree_three_is_identity :
    backwardFormula.degreeThree =
      .identity handle_counts.2.2
  forward_realizes_formula :
    RealizesMoveChainFormula equivalence.forward forwardFormula
  backward_realizes_formula :
    RealizesMoveChainFormula equivalence.backward backwardFormula
  isolated_acyclic_block :
    HasIsolatedAcyclicCancellationBlock .oneTwo source target sign

/-- A 1--2 death is exactly the reverse of a specified 1--2 birth. -/
structure OneTwoDeathTransport
    (source target : SpecialKirbyDiagram geometry) where
  reverseBirth : OneTwoBirthTransport target source
  equivalence :
    HandleHomologyEquivalence source target
  forward_is_reverse_birth_backward :
    equivalence.forward = reverseBirth.equivalence.backward
  backward_is_reverse_birth_forward :
    equivalence.backward = reverseBirth.equivalence.forward

/--
An explicit 2--3 birth adds one new degree-two generator and one new
degree-three generator forming an acyclic block:

`∂₃(new three-handle) = ± new two-handle`,

and `∂₂(new two-handle) = 0`, with no old-handle term.  Old generators
include unchanged and projection deletes the new pair.
-/
structure TwoThreeBirthTransport
    (source target : SpecialKirbyDiagram geometry) where
  sign : LocalSign
  handle_counts :
    target.geometric.hOne = source.geometric.hOne ∧
      target.geometric.hTwo = source.geometric.hTwo + 1 ∧
      target.geometric.hThree = source.geometric.hThree + 1
  equivalence : HandleHomologyEquivalence source target
  forwardFormula : MoveChainFormula source target
  backwardFormula : MoveChainFormula target source
  forward_degree_one_is_identity :
    forwardFormula.degreeOne =
      .identity handle_counts.1.symm
  forward_degree_two_includes_old :
    forwardFormula.degreeTwo =
      .includeLast handle_counts.2.1
  forward_degree_three_includes_old :
    forwardFormula.degreeThree =
      .includeLast handle_counts.2.2
  backward_degree_one_is_identity :
    backwardFormula.degreeOne =
      .identity handle_counts.1
  backward_degree_two_deletes_new :
    backwardFormula.degreeTwo =
      .projectLast handle_counts.2.1
  backward_degree_three_deletes_new :
    backwardFormula.degreeThree =
      .projectLast handle_counts.2.2
  forward_realizes_formula :
    RealizesMoveChainFormula equivalence.forward forwardFormula
  backward_realizes_formula :
    RealizesMoveChainFormula equivalence.backward backwardFormula
  isolated_acyclic_block :
    HasIsolatedAcyclicCancellationBlock .twoThree source target sign

/-- A 2--3 death is exactly the reverse of a specified 2--3 birth. -/
structure TwoThreeDeathTransport
    (source target : SpecialKirbyDiagram geometry) where
  reverseBirth : TwoThreeBirthTransport target source
  equivalence :
    HandleHomologyEquivalence source target
  forward_is_reverse_birth_backward :
    equivalence.forward = reverseBirth.equivalence.backward
  backward_is_reverse_birth_forward :
    equivalence.backward = reverseBirth.equivalence.forward

/--
The exhaustive independent H₂-transport semantics for one elementary move.

Every constructor contains an explicit source-to-target chain equivalence.
Consequently its action on `α` is derived, never independently asserted.
-/
inductive ElementaryMoveTransport
    (source target : SpecialKirbyDiagram geometry) where
  | framedIsotopy :
      FramedIsotopyTransport source target →
        ElementaryMoveTransport source target
  | oneOverOne :
      OneOverOneTransport source target →
        ElementaryMoveTransport source target
  | twoOverOne :
      TwoOverOneTransport source target →
        ElementaryMoveTransport source target
  | twoOverTwo :
      TwoOverTwoTransport source target →
        ElementaryMoveTransport source target
  | oneTwoBirth :
      OneTwoBirthTransport source target →
        ElementaryMoveTransport source target
  | oneTwoDeath :
      OneTwoDeathTransport source target →
        ElementaryMoveTransport source target
  | twoThreeBirth :
      TwoThreeBirthTransport source target →
        ElementaryMoveTransport source target
  | twoThreeDeath :
      TwoThreeDeathTransport source target →
        ElementaryMoveTransport source target

/-- Extract the explicit homology equivalence carried by any move. -/
def ElementaryMoveTransport.homologyEquivalence
    {source target : SpecialKirbyDiagram geometry} :
    ElementaryMoveTransport source target →
      HandleHomologyEquivalence source target
  | .framedIsotopy move => move.equivalence
  | .oneOverOne move => move.equivalence
  | .twoOverOne move => move.equivalence
  | .twoOverTwo move => move.equivalence
  | .oneTwoBirth move => move.equivalence
  | .oneTwoDeath move => move.equivalence
  | .twoThreeBirth move => move.equivalence
  | .twoThreeDeath move => move.equivalence

/--
The only legal transport of a marking through one elementary Kirby move.
-/
def ElementaryMoveTransport.transportH₂
    {source target : SpecialKirbyDiagram geometry}
    (move : ElementaryMoveTransport source target) :
    KirbyH₂ source → KirbyH₂ target :=
  move.homologyEquivalence.transport

/--
A finite Kirby movie transports an H₂ class by composing the induced maps of
its elementary moves in order.  No new transport choice is made here.
-/
inductive KirbyMovieTransport :
    SpecialKirbyDiagram geometry →
      SpecialKirbyDiagram geometry →
      Type _ where
  | identity (diagram) :
      KirbyMovieTransport diagram diagram
  | then
      {source middle target}
      (first : ElementaryMoveTransport source middle)
      (rest : KirbyMovieTransport middle target) :
      KirbyMovieTransport source target

def KirbyMovieTransport.transportH₂
    {source target : SpecialKirbyDiagram geometry} :
    KirbyMovieTransport source target →
      KirbyH₂ source →
      KirbyH₂ target
  | .identity _, α => α
  | .then first rest, α =>
      rest.transportH₂ (first.transportH₂ α)

end TwistedYetter.Kirby.Final.IndependentMoveHomologyTransportSpecification
