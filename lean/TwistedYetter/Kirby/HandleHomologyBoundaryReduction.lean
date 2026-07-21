import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TwistedYetter.Kirby.HandleChainHomology

/-!
# Reducing equality in handle homology to a degree-three boundary

For a chain complex of integral modules, Mathlib defines homology as the
quotient of cycles by the image of the incoming differential.  This file
exposes the corresponding elementwise statement at degree two.

The result is deliberately independent of every category, link evaluator,
and Kirby move.  It turns an equality in `H₂` into an actual element of the
degree-three side of the short complex, together with the exact equation
whose image is the difference of the two cycles.
-/

namespace TwistedYetter.Kirby.HandleHomologyBoundaryReduction

open CategoryTheory
open TwistedYetter.Kirby.HandleChainHomology

universe u

/--
Two degree-two cycles determine the same Mathlib homology class exactly when
their difference lies in the image of the incoming degree-three map.

The witness lives in `(complex.sc 2).X₁`, which is definitionally the
degree-three chain object for a downward chain complex.  The equation is
stated in Mathlib's concrete kernel model of degree-two cycles so that no
choice of quotient representative is hidden.
-/
theorem homologyπ_eq_iff_exists_boundary
    {R : Type u} [Ring R]
    (complex : ChainComplex (ModuleCat R) ℕ)
    (left right : complex.cycles 2) :
    complex.homologyπ 2 left = complex.homologyπ 2 right ↔
      ∃ chain : (complex.sc 2).X₁,
        (complex.sc 2).moduleCatToCycles chain =
          (complex.sc 2).moduleCatCyclesIso.hom left -
            (complex.sc 2).moduleCatCyclesIso.hom right := by
  let S := complex.sc 2
  change
    S.homologyπ left = S.homologyπ right ↔
      ∃ chain : S.X₁,
        S.moduleCatToCycles chain =
          S.moduleCatCyclesIso.hom left -
            S.moduleCatCyclesIso.hom right
  rw [show
    (∃ chain : S.X₁,
        S.moduleCatToCycles chain =
          S.moduleCatCyclesIso.hom left -
            S.moduleCatCyclesIso.hom right) ↔
      S.moduleCatCyclesIso.hom left -
          S.moduleCatCyclesIso.hom right ∈
        LinearMap.range S.moduleCatToCycles by
      constructor
      · rintro ⟨chain, equation⟩
        exact ⟨chain, equation⟩
      · rintro ⟨chain, equation⟩
        exact ⟨chain, equation⟩]
  exact
    Iff.trans
      ⟨fun equality => by
          simpa only [← ConcreteCategory.comp_apply,
            ShortComplex.π_moduleCatCyclesIso_hom] using
            congr(S.moduleCatHomologyIso.hom $equality),
        fun membership =>
          (ModuleCat.mono_iff_injective
            S.moduleCatHomologyIso.hom).1 inferInstance (by
              simpa only [← ConcreteCategory.comp_apply,
                ShortComplex.π_moduleCatCyclesIso_hom] using membership)⟩
      (Submodule.Quotient.eq _)

end TwistedYetter.Kirby.HandleHomologyBoundaryReduction
