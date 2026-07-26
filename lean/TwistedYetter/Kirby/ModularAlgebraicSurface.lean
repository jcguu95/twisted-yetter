import TwistedYetter.Kirby.CanonicalModularKirbyInvariance

/-!
# Natural algebraic surface for the modular Kirby evaluation

This module exposes the algebraic statement in the variables used by a
mathematician:

* a modular category `𝒞`;
* a tensor automorphism `η` of its identity functor;
* a special Kirby diagram `P`; and
* a class `a` in the handle-chain `H₂` of `P`.

The evaluator is canonical.  No arbitrary evaluator, graphical-rule package,
compiler, or local-invariance proof occurs in the public interface.
-/

namespace TwistedYetter.Fusion.EGNO.ModularCategory

open CategoryTheory
open TwistedYetter.Fusion.EGNO

universe uK uC vC

/--
Tensor automorphisms of the identity functor, displayed as depending on the
chosen modular category.
-/
abbrev TensorIdentityAutomorphism
    {K : Type uK} [Field K] [IsAlgClosed K]
    {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
    [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
    {S : Type} [Fintype S] [DecidableEq S]
    (_𝒞 : ModularCategory (K := K) (C := C) (S := S)) :=
  TwistedYetter.Fusion.EGNO.TensorIdentityAutomorphism C

end TwistedYetter.Fusion.EGNO.ModularCategory

namespace TwistedYetter.Kirby.ModularAlgebraicSurface

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalModularKirbyInvariance
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

noncomputable section

/--
A category-neutral special Kirby diagram in the admitted canonical syntax.

The mathematical diagram carries no repository scope or artifact identity.
-/
abbrev SpecialKirbyDiagram :=
  StandardDottedCanonicalPresentation ℤ

namespace SpecialKirbyDiagram

/-- The second homology computed directly from the diagram's handle complex. -/
abbrev HandleH₂
    (P : SpecialKirbyDiagram) :=
  P.canonicalPresentation.topology.handleChain.SecondHomology

end SpecialKirbyDiagram

/-- One elementary Kirby move between two special diagrams. -/
abbrev ElementaryKirbyMove
    (P Q : SpecialKirbyDiagram) :=
  TopologicalTableTwoMove
    P.canonicalPresentation.topology
    Q.canonicalPresentation.topology

namespace ElementaryKirbyMove

/--
The map on handle-chain `H₂` computed by the elementary move.

For a two-handle slide this performs the corresponding basis change; it does
not leave the coordinate vector artificially fixed.
-/
noncomputable def transportH₂
    {P Q : SpecialKirbyDiagram}
    (m : ElementaryKirbyMove P Q) :
    P.HandleH₂ ≃+ Q.HandleH₂ :=
  (enrichedMove m).homologyTransport.chainEquivalence
    |>.secondHomologyAddEquiv

end ElementaryKirbyMove

/--
The canonical homologically twisted modular evaluation of one special Kirby
diagram and one class in its handle-chain `H₂`.
-/
noncomputable def TwistedKirbyEvaluation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (η : 𝒞.TensorIdentityAutomorphism)
    (P : SpecialKirbyDiagram)
    (a : P.HandleH₂) : K :=
  P.canonicalPresentation.EvalC 𝒞 η a

/--
The canonical modular evaluation is natural under every elementary Kirby
move, with the handle-chain class transported by the move itself.

No graphical law or local-invariance proof is accepted as an argument.
-/
theorem TwistedKirbyEvaluation_elementaryMove_invariant
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (η : 𝒞.TensorIdentityAutomorphism)
    {P Q : SpecialKirbyDiagram}
    (m : ElementaryKirbyMove P Q)
    (a : P.HandleH₂) :
    TwistedKirbyEvaluation 𝒞 η P a =
      TwistedKirbyEvaluation 𝒞 η Q (m.transportH₂ a) := by
  exact
    evalC_local_move_invariant
      (H2 := ℤ) 𝒞 η m a

end

end TwistedYetter.Kirby.ModularAlgebraicSurface
