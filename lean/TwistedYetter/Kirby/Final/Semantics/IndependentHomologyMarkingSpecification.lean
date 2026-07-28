import TwistedYetter.Kirby.Final.Semantics.IndependentPresentationSpecification

/-!
# Independent human specification of H₂ marking

This file is normative.  It was written without importing or inspecting this
repository's H₂, handle-chain, evaluator, move-transport, Sage, or bridge
implementations.

For a `SpecialKirbyDiagram D`, the marking type is exactly

`ker(∂₂) / im(∂₃)`.

A marking is a class in this quotient, not a selected 2-cycle.  A cycle and a
handle-coordinate chart are auxiliary witnesses used only by a computation.
No assumption of rank one, torsion-freeness, or simple connectivity occurs.
-/

namespace TwistedYetter.Kirby.Final.IndependentHomologyMarkingSpecification

open CategoryTheory
open IndependentPresentationSpecification

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

/-- A handle 2-chain whose `∂₂` is zero. -/
structure TwoCycle (diagram : SpecialKirbyDiagram geometry) where
  chain : diagram.handleBoundary.twoChains.carrier
  boundaryTwo_zero :
    diagram.handleBoundary.boundaryTwo chain = 0

/--
Two cycles represent the same class exactly when their difference is the
`∂₃` of a handle 3-chain.
-/
def Homologous
    {diagram : SpecialKirbyDiagram geometry}
    (a b : TwoCycle diagram) : Prop :=
  ∃ c : diagram.handleBoundary.threeChains.carrier,
    b.chain - a.chain =
      diagram.handleBoundary.boundaryThree c

/-- The handle-homology relation is an equivalence relation. -/
def homologousSetoid
    (diagram : SpecialKirbyDiagram geometry) :
    Setoid (TwoCycle diagram) where
  r := Homologous
  iseqv := {
    refl := by
      intro a
      refine ⟨0, ?_⟩
      simp
    symm := by
      intro a b hab
      rcases hab with ⟨c, hc⟩
      refine ⟨-c, ?_⟩
      simpa using congrArg Neg.neg hc
    trans := by
      intro a b c hab hbc
      rcases hab with ⟨x, hx⟩
      rcases hbc with ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      simpa [map_add] using congrArg₂ (· + ·) hx hy
  }

/--
The marking group at diagram level.

This type is not abbreviated to `ℤ` and retains arbitrary rank and torsion.
-/
def KirbyH₂ (diagram : SpecialKirbyDiagram geometry) :=
  Quotient (homologousSetoid diagram)

/-- The quotient class of a handle 2-cycle. -/
def classOfCycle
    {diagram : SpecialKirbyDiagram geometry}
    (cycle : TwoCycle diagram) :
    KirbyH₂ diagram :=
  Quotient.mk _ cycle

/--
A temporary representative used to run a cycle-level formula.

The public mathematical input is `α`; this witness must disappear after
representative independence is proved.
-/
structure CycleRepresentative
    {diagram : SpecialKirbyDiagram geometry}
    (α : KirbyH₂ diagram) where
  cycle : TwoCycle diagram
  represents :
    classOfCycle cycle = α

/--
A generator choice on one rank-one handle orientation line.

Choosing this is choosing a sign/orientation for that handle.  It is not part
of the `SpecialKirbyDiagram`.
-/
structure OrientationLineCoordinate
    (line : ModuleCat ℤ) where
  coordinate : line ≅ ModuleCat.of ℤ ℤ

/--
An auxiliary coordinate chart for a computation.

Each handle line receives its own generator.  The chart cannot mix different
handle components by an arbitrary `GL(n, ℤ)` transformation.
-/
structure HandleCoordinateChart
    (diagram : SpecialKirbyDiagram geometry) where
  oneHandleCoordinate :
    (i : Fin diagram.geometric.hOne) →
      OrientationLineCoordinate
        (diagram.handleBoundary.oneChains.line i)
  twoHandleCoordinate :
    (j : Fin diagram.geometric.hTwo) →
      OrientationLineCoordinate
        (diagram.handleBoundary.twoChains.line j)
  threeHandleCoordinate :
    (k : Fin diagram.geometric.hThree) →
      OrientationLineCoordinate
        (diagram.handleBoundary.threeChains.line k)

/--
The exact public marking input at diagram level is the dependent pair
`(D, α)`.
-/
abbrev MarkedSpecialKirbyDiagram :=
  Σ diagram : SpecialKirbyDiagram geometry, KirbyH₂ diagram

/--
The representative-independence obligation, stated without an evaluator.

Any future cycle-level quantity descends to `KirbyH₂` only after proving this
predicate for that particular quantity.
-/
def RepresentativeIndependent
    {Value : Type}
    {diagram : SpecialKirbyDiagram geometry}
    (cycleQuantity : TwoCycle diagram → Value) :
    Prop :=
  ∀ a b, Homologous a b → cycleQuantity a = cycleQuantity b

end TwistedYetter.Kirby.Final.IndependentHomologyMarkingSpecification
