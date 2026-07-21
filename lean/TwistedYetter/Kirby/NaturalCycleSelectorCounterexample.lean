import Mathlib.Data.Int.Basic

/-!
# Obstruction to a strictly natural cycle selector

This file isolates a small integral-chain obstruction that matters for the
global marked Kirby problem.

Model the degree-two cycles by `Z^2`.  The first coordinate records the
homology class, while the second coordinate is a degree-three boundary.  The
boundary shear

`(x, y) |-> (x, x + y)`

therefore induces the identity on `H2 = Z`.

There is no selector of one cycle over every homology class which both
represents that class and is fixed strictly by this shear.  Thus a global
solution cannot be obtained by demanding a cycle section natural under every
homology-trivial chain automorphism.

This is only an algebraic strategy obstruction.  It does not assert that the
displayed shear is already realized by a loop in the repository's concrete
Kirby-move engine, and it does not rule out a stable normal form or a
distinguished admissible orbit of representatives.
-/

namespace TwistedYetter.Kirby.NaturalCycleSelectorCounterexample

/-- Degree-two cycles in the two-generator test complex. -/
abbrev DegreeTwoCycle := Fin 2 → ℤ

/-- The quotient class after the second coordinate is declared a boundary. -/
def homologyClass (cycle : DegreeTwoCycle) : ℤ :=
  cycle 0

/-- A chain shear which changes a cycle only by the boundary coordinate. -/
def boundaryShear (cycle : DegreeTwoCycle) : DegreeTwoCycle :=
  fun coordinate =>
    if coordinate = 0 then cycle 0 else cycle 0 + cycle 1

/-- The boundary shear induces the identity on the displayed homology. -/
theorem boundaryShear_homologyClass (cycle : DegreeTwoCycle) :
    homologyClass (boundaryShear cycle) = homologyClass cycle := by
  simp [homologyClass, boundaryShear]

/--
A hypothetical strictly natural representative selector.

`class_sound` says the selected cycle represents the requested class.
`shear_natural` demands literal equality of cycles, not merely equality in
homology.
-/
structure StrictNaturalSelector where
  cycle : ℤ → DegreeTwoCycle
  class_sound :
    (alpha : ℤ) → homologyClass (cycle alpha) = alpha
  shear_natural :
    (alpha : ℤ) → boundaryShear (cycle alpha) = cycle alpha

/--
No strictly boundary-shear-natural selector exists, even though the shear is
the identity on homology.
-/
theorem no_strictNaturalSelector :
    IsEmpty StrictNaturalSelector := by
  refine ⟨?_⟩
  intro selector
  have classAtOne := selector.class_sound 1
  have shearAtOne :=
    congrFun (selector.shear_natural 1) (1 : Fin 2)
  simp [homologyClass] at classAtOne
  simp [boundaryShear, classAtOne] at shearAtOne
  omega

end TwistedYetter.Kirby.NaturalCycleSelectorCounterexample
