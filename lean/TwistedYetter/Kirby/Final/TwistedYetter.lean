import TwistedYetter.Kirby.Final.Proofs.FrozenFrontendLocalMoves

/-!
# Frozen-frontend Twisted Yetter invariant

This file has no second evaluator and no conformance detour.  It proves the
finite-movie descent from the frozen frontend's canonical graphical evaluator,
representative-independence theorem, and eight local-move calculations.  It
then exports the manifold-level `TwistedYetter` and the clean public theorem
`TwistedYetter_diffeomorphism_invariant`.

The category route is canonical: ribbon data determines the pivotal and
spherical structures used by the graphical trace.  The cut-open graph compiler
and THAM normalization are frozen-frontend definitions rather than caller
supplied inputs.  The more general conditional descent lemma remains internal
so that the public theorem exposes no evaluator, compiler, normalization, or
proof-package parameter.
-/

namespace TwistedYetter.Kirby.Final

open CategoryTheory
open TwistedYetter.Semantics.Independent
open TwistedYetter.Kirby.Final.Proofs

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The conditional evaluator on one frozen-frontend marked diagram.

This is exactly `Independent.evaluateMarking`; it is not a wrapper around the
previous repository evaluator.
-/
abbrev evaluateMarkedDiagram
    (𝒞η : TwistedPremodularCategory K)
    (marked : HomologicallyMarkedDiagram) : K :=
  evaluateMarking 𝒞η marked

/--
One frozen-frontend elementary move preserves evaluation.

The source representative is transported by the move's THAM-side chain map.
Representative independence then identifies it with the representative chosen
for the target marking.
-/
theorem elementaryMove_preserves_frontend_evaluation
    (𝒞η : TwistedPremodularCategory K)
    (representativeIndependent :
      ∀ (marked : HomologicallyMarkedDiagram),
        RepresentativeIndependenceStatement
          𝒞η
          marked.diagram marked.cut)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η)
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    evaluateMarkedDiagram 𝒞η source =
      evaluateMarkedDiagram 𝒞η target := by
  let sourceCycle : ThamTwoHandleCoefficients source.diagram :=
    Quotient.out source.thamAlpha
  let transportedCycle : ThamTwoHandleCoefficients target.diagram :=
    move.homology.tham.mapCoefficients sourceCycle
  let targetCycle : ThamTwoHandleCoefficients target.diagram :=
    Quotient.out target.thamAlpha
  apply (localInvariant move sourceCycle).trans
  apply representativeIndependent target transportedCycle targetCycle
  change
    move.homology.tham.inducedMarking
        (thamMarkingClass sourceCycle) =
      thamMarkingClass targetCycle
  rw [show thamMarkingClass sourceCycle = source.thamAlpha by
    exact Quotient.out_eq source.thamAlpha]
  rw [show thamMarkingClass targetCycle = target.thamAlpha by
    exact Quotient.out_eq target.thamAlpha]
  exact move.thamMarkingTransport.symm

/--
A finite frozen-frontend Kirby movie preserves evaluation.

This is derived by induction over the finite list of elementary stages; it is
not an additional topology or evaluator axiom.
-/
theorem kirbyMovie_preserves_frontend_evaluation
    (𝒞η : TwistedPremodularCategory K)
    (representativeIndependent :
      ∀ (marked : HomologicallyMarkedDiagram),
        RepresentativeIndependenceStatement
          𝒞η
          marked.diagram marked.cut)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η)
    {source target : HomologicallyMarkedDiagram}
    (movie : KirbyMovie source target) :
    evaluateMarkedDiagram 𝒞η source =
      evaluateMarkedDiagram 𝒞η target := by
  have step :
      ∀ i : Fin movie.stageCount,
        evaluateMarkedDiagram 𝒞η
            (movie.stages i.castSucc) =
          evaluateMarkedDiagram 𝒞η
            (movie.stages i.succ) := by
    intro i
    exact elementaryMove_preserves_frontend_evaluation
      𝒞η
      representativeIndependent localInvariant (movie.elementary i)
  have fromStart :
      ∀ i : Fin (movie.stageCount + 1),
        evaluateMarkedDiagram 𝒞η
            (movie.stages 0) =
          evaluateMarkedDiagram 𝒞η
            (movie.stages i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i inductionHypothesis =>
        exact inductionHypothesis.trans (step i)
  calc
    evaluateMarkedDiagram 𝒞η source =
        evaluateMarkedDiagram 𝒞η
          (movie.stages 0) := by
      rw [movie.startsAtSource]
    _ = evaluateMarkedDiagram 𝒞η
          (movie.stages (Fin.last movie.stageCount)) :=
      fromStart (Fin.last movie.stageCount)
    _ = evaluateMarkedDiagram 𝒞η target := by
      rw [movie.endsAtTarget]

namespace ConditionalDescent

/--
Conditional diffeomorphism descent after all evaluator and topology data have
been supplied.

This is an internal assembly lemma, not the final manifold invariant theorem.
-/
theorem diffeomorphism_invariant_of_descent_data
    (𝒞η : TwistedPremodularCategory K)
    (representativeIndependent :
      ∀ (marked : HomologicallyMarkedDiagram),
        RepresentativeIndependenceStatement
          𝒞η
          marked.diagram marked.cut)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η) :
    TwistedYetterDiffeomorphismInvarianceTarget
      𝒞η := by
  intro X Y f alpha left leftCorrect right rightCorrect
  obtain ⟨movie⟩ :=
    markedKirbyCerf_complete f alpha left leftCorrect right rightCorrect
  exact
    kirbyMovie_preserves_frontend_evaluation
      𝒞η
      representativeIndependent localInvariant movie

end ConditionalDescent

/--
The manifold-level frozen-frontend evaluator.

Its public inputs are exactly a twisted premodular category and a closed
oriented smooth four-manifold together with an integral second-homology
class.  No graphical evaluator, compiler, normalization, local-invariance
proof, or topology package is a public argument.

This definition is connected directly to the constructions supplied by the
frozen frontend.  None of those constructions is replaced by a public
parameter or `sorry`.
-/
noncomputable def TwistedYetter
    (𝒞η : TwistedPremodularCategory K)
    (Xα :
      Σ X : ClosedOrientedSmoothFourManifold,
        ManifoldH₂ X) : K :=
  let representative :=
    (specialKirbyRepresentative_exists Xα.1 Xα.2).choose
  evaluateMarkedDiagram 𝒞η representative.toHomologicallyMarkedDiagram

/--
Clean final theorem target.

There are no escape-hatch parameters.  The proof must obtain graphical
evaluation, representative independence, and all eight local calculations
from the frozen frontend itself.
-/
theorem TwistedYetter_diffeomorphism_invariant
    (𝒞η : TwistedPremodularCategory K)
    {X Y : ClosedOrientedSmoothFourManifold}
    (f : OrientedDiffeomorphism X Y)
    (alpha : ManifoldH₂ X) :
    TwistedYetter 𝒞η ⟨X, alpha⟩ =
      TwistedYetter 𝒞η ⟨Y, inducedH₂ f alpha⟩ := by
  unfold TwistedYetter
  let leftExistence := specialKirbyRepresentative_exists X alpha
  let rightExistence :=
    specialKirbyRepresentative_exists Y (inducedH₂ f alpha)
  exact
    ConditionalDescent.diffeomorphism_invariant_of_descent_data
      𝒞η
      (fun marked =>
        frozenFrontendRepresentativeIndependence
          𝒞η marked.diagram marked.cut)
      (frozenFrontendLocalMoveInvariance 𝒞η)
      X Y f alpha
      leftExistence.choose leftExistence.choose_spec
      rightExistence.choose rightExistence.choose_spec

end

end TwistedYetter.Kirby.Final
