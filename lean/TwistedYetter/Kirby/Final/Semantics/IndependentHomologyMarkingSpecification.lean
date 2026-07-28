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
  {geometry : KirbyGeometrySemantics}

/-- A handle 2-chain whose `∂₂` is zero. -/
structure TwoCycle (diagram : SpecialKirbyDiagram geometry) where
  chain : diagram.handleBoundary.twoChains.carrier
  boundaryTwo_zero :
    diagram.handleBoundary.boundaryTwo chain = 0

@[ext]
theorem TwoCycle.ext
    {diagram : SpecialKirbyDiagram geometry}
    {a b : TwoCycle diagram}
    (h : a.chain = b.chain) :
    a = b := by
  cases a
  cases b
  simp_all

instance {diagram : SpecialKirbyDiagram geometry} :
    Zero (TwoCycle diagram) where
  zero :=
    { chain := 0
      boundaryTwo_zero := by simp }

instance {diagram : SpecialKirbyDiagram geometry} :
    Add (TwoCycle diagram) where
  add a b :=
    { chain := a.chain + b.chain
      boundaryTwo_zero := by
        rw [map_add, a.boundaryTwo_zero, b.boundaryTwo_zero]
        simp }

instance {diagram : SpecialKirbyDiagram geometry} :
    Neg (TwoCycle diagram) where
  neg a :=
    { chain := -a.chain
      boundaryTwo_zero := by
        rw [map_neg, a.boundaryTwo_zero]
        simp }

instance {diagram : SpecialKirbyDiagram geometry} :
    Sub (TwoCycle diagram) where
  sub a b :=
    { chain := a.chain - b.chain
      boundaryTwo_zero := by
        rw [map_sub, a.boundaryTwo_zero, b.boundaryTwo_zero]
        simp }

instance {diagram : SpecialKirbyDiagram geometry} :
    SMul ℕ (TwoCycle diagram) where
  smul n a :=
    { chain := n • a.chain
      boundaryTwo_zero := by
        rw [map_nsmul, a.boundaryTwo_zero]
        simp }

instance {diagram : SpecialKirbyDiagram geometry} :
    SMul ℤ (TwoCycle diagram) where
  smul n a :=
    { chain := n • a.chain
      boundaryTwo_zero := by
        rw [map_zsmul, a.boundaryTwo_zero]
        change
          n • (0 : diagram.handleBoundary.oneChains.carrier) = 0
        exact zsmul_zero n }

instance {diagram : SpecialKirbyDiagram geometry} :
    AddCommGroup (TwoCycle diagram) :=
  Function.Injective.addCommGroup
    TwoCycle.chain
    (fun _ _ h => TwoCycle.ext h)
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)

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

/-- The handle-homology relation respects addition of cycles. -/
def homologousAddCon
    (diagram : SpecialKirbyDiagram geometry) :
    AddCon (TwoCycle diagram) where
  toSetoid :=
    { r := Homologous
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
      } }
  add' := by
    intro w x y z hw hy
    rcases hw with ⟨a, ha⟩
    rcases hy with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    change
      (x.chain + z.chain) - (w.chain + y.chain) =
        diagram.handleBoundary.boundaryThree (a + b)
    calc
      (x.chain + z.chain) - (w.chain + y.chain) =
          (x.chain - w.chain) + (z.chain - y.chain) := by
            abel
      _ = diagram.handleBoundary.boundaryThree a +
          diagram.handleBoundary.boundaryThree b := by
            rw [ha, hb]
      _ = diagram.handleBoundary.boundaryThree (a + b) := by
            rw [map_add]

/--
The marking group at diagram level.

This type is not abbreviated to `ℤ` and retains arbitrary rank and torsion.
-/
def KirbyH₂ (diagram : SpecialKirbyDiagram geometry) :=
  (homologousAddCon diagram).Quotient

instance {diagram : SpecialKirbyDiagram geometry} :
    AddCommGroup (KirbyH₂ diagram) :=
  inferInstanceAs
    (AddCommGroup ((homologousAddCon diagram).Quotient))

/-- The quotient class of a handle 2-cycle. -/
def classOfCycle
    {diagram : SpecialKirbyDiagram geometry}
    (cycle : TwoCycle diagram) :
    KirbyH₂ diagram :=
  (cycle : (homologousAddCon diagram).Quotient)

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
