import TwistedYetter.Kirby.CanonicalCycleLocalInvariance
import TwistedYetter.Kirby.CanonicalSourceBackedMove

/-!
# Literature boundary for canonical graphical endpoint realization

This module isolates the remaining diagrammatic input not reconstructed from
serialized planar embeddings:

1. an exact special-Kirby local recipe compiles to one of the restricted
   eight cycle-safe graphical proof grammars.

This diagrammatic/topological realization statement does not state that an
evaluator is invariant and cannot return an equality in the ground field.
All categorical soundness, finite Kirby-colour sums, normalization, and
reverse-move bookkeeping are proved after this boundary.

Selected sources:

* Bärenz--Barrett, Lemmas 3.1, 3.3--3.4, Table 2, and Theorem 3.9,
  journal pages 680--687;
* Shum's coherence theorem for tortile categories for the framed ribbon
  graphical calculus.

Lean does not reconstruct ambient planar isotopies, attaching-band
neighbourhoods, or the placement of every coupon cut from the raw serialized
event list in this module.  That exact limitation is intentionally visible
in the single axiom below.

There is deliberately no unproved global dual-boundary movie axiom hidden in
this file.  The former apparent counterexample used the primal handle chain
where Tham's evaluator uses the upside-down dual chain; it remains only a
regression test for that convention error.  The actual remaining obligation
is to compile every dual `d3` boundary change through the primal dotted
one-handle and its Tham `k = 3` vacuum projector.
-/

namespace TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalCycleLocalInvariance
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CanonicalSourceBackedMove
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Exact denominator of the imported diagrammatic statements. -/
inductive AssumptionClass where
  | tableTwoEndpointRealization
  deriving Repr, BEq, DecidableEq

def requiredAssumptionClasses : List AssumptionClass :=
  [
    .tableTwoEndpointRealization
  ]

theorem required_assumption_class_count :
    requiredAssumptionClasses.length = 1 := by
  rfl

theorem required_assumption_classes_unique :
    requiredAssumptionClasses.Nodup := by
  decide

/-- Stable repository references for the two imported statements. -/
def sourceRefs : List String :=
  [
    "ref:baerenz-barrett-dichromatic-2018",
    "ref:shum-tortile-1994"
  ]

/-- Exact imported meaning of the first diagrammatic statement. -/
def tableTwoEndpointExactScope : String :=
  "Each source-bound special-Kirby Table 2 recipe, interpreted by the "
    ++ "canonical component trace and the chain-transported explicit cycle, "
    ++ "has a proof in exactly one restricted framed-isotopy, whole-sum "
    ++ "slide, or isolated-cancellation grammar."

/-- Machine-visible scope of the still-open global dual-boundary bridge. -/
def dualBoundaryIntegrationScope : String :=
  "The wrong-primal-chain counterexample is retracted. Lean now compiles a "
    ++ "complete dotted-boundary GeometrySystem through the Tham k=3 vacuum "
    ++ "identity and proves H2 representative independence. The final "
    ++ "presentation domain now carries this geometry certification, so no "
    ++ "global geometry axiom is asserted for malformed raw syntax."

/-- What the remaining diagrammatic axiom is not allowed to say. -/
def sourceScopeCaveat : String :=
  "The axiom supplies no scalar equality, final EvalC equality, "
    ++ "arbitrary evaluator, a homology map, or a Kirby-completeness theorem. "
    ++ "Lean does not compile raw planar coordinates and attaching-band "
    ++ "neighbourhoods into these proof terms."

/--
The standard exact-endpoint realization of one source-bound Table 2 move.

The returned value is one of eight restricted geometry constructors.  The
axiom cannot return the equality proved by `LocalCycleCalculation.sound`.
-/
axiom standardLocalCycleCalculation
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation manifold H2}
    (move :
      TopologicalTableTwoMove source.topology target.topology) :
    LocalCycleCalculation 𝒞 automorphism (enrichedMove move)

end TwistedYetter.Kirby.LiteratureBackedCanonicalGraphicalInput
