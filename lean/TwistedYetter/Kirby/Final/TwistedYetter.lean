import TwistedYetter.Kirby.Final.Semantics.Independent.Entry

/-!
# Frozen-frontend conditional descent

This file has no second evaluator and no conformance detour.  It proves the
finite-movie descent that follows once the frozen frontend's evaluator data
and local calculations have been supplied.

It deliberately does not export a manifold-level `TwistedYetter` or a theorem
named `TwistedYetter_diffeomorphism_invariant`.  The frozen frontend currently
does not yet construct a typed categorical graphical interpretation or prove
representative independence and the eight local moves from
`TwistedPremodularCategory`.  The cut-open graph compiler and THAM
normalization are now canonical frozen-frontend definitions.  Calling the
conditional result a final theorem would still hide the remaining
mathematical obligations.
-/

namespace TwistedYetter.Kirby.Final

open TwistedYetter.Semantics.Independent

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
          marked.diagram marked.primalBoundary marked.turnedOver)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η)
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    evaluateMarkedDiagram 𝒞η source =
      evaluateMarkedDiagram 𝒞η target := by
  let sourceCycle : ThamTwoCycles source.turnedOver :=
    Quotient.out source.thamAlpha
  let transportedCycle : ThamTwoCycles target.turnedOver :=
    move.homology.tham.mapCycle sourceCycle
  let targetCycle : ThamTwoCycles target.turnedOver :=
    Quotient.out target.thamAlpha
  apply (localInvariant move sourceCycle).trans
  apply representativeIndependent target transportedCycle targetCycle
  change
    move.homology.tham.inducedH₂
        (thamCycleClass source.turnedOver sourceCycle) =
      thamCycleClass target.turnedOver targetCycle
  rw [show thamCycleClass source.turnedOver sourceCycle = source.thamAlpha by
    exact Quotient.out_eq source.thamAlpha]
  rw [show thamCycleClass target.turnedOver targetCycle = target.thamAlpha by
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
          marked.diagram marked.primalBoundary marked.turnedOver)
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
          marked.diagram marked.primalBoundary marked.turnedOver)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η) :
    TwistedYetterDiffeomorphismInvarianceTarget
      𝒞η := by
  intro X Y f alpha left right
  obtain ⟨movie⟩ :=
    markedKirbyCerf_complete f alpha left right
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

This definition is intentionally connected to the three constructions that
the frozen frontend must supply.  During the red-first phase those names are
left unresolved rather than replaced by parameters or `sorry`.
-/
noncomputable def TwistedYetter
    (𝒞η : TwistedPremodularCategory K)
    (Xα :
      Σ X : ClosedOrientedSmoothFourManifold,
        ManifoldH₂ X) : K :=
  let realization :=
    Classical.choice (markedRealization_exists Xα.1 Xα.2)
  evaluateMarkedDiagram 𝒞η realization.markedDiagram

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
  exact
    ConditionalDescent.diffeomorphism_invariant_of_descent_data
      𝒞η
      (frozenFrontendRepresentativeIndependence 𝒞η)
      (frozenFrontendLocalMoveInvariance 𝒞η)
      X Y f alpha
      (Classical.choice (markedRealization_exists X alpha))
      (Classical.choice
        (markedRealization_exists Y (inducedH₂ f alpha)))

end

end TwistedYetter.Kirby.Final
