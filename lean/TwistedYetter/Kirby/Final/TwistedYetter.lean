import TwistedYetter.Kirby.Final.Semantics.Independent.Entry

/-!
# Frozen-frontend conditional descent

This file has no second evaluator and no conformance detour.  It proves the
finite-movie descent that follows once the frozen frontend's evaluator data
and local calculations have been supplied.

It deliberately does not export a manifold-level `TwistedYetter` or a theorem
named `TwistedYetter_diffeomorphism_invariant`.  The frozen frontend currently
does not construct its graphical evaluation, graph compiler, normalization,
representative-independence proof, or eight local-move proofs from
`TwistedPremodularCategory`.  Calling the conditional result a final theorem
would hide exactly those missing obligations.
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
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (marked : HomologicallyMarkedDiagram) : K :=
  evaluateMarking 𝒞η graphical compiler normalization marked

/--
One frozen-frontend elementary move preserves evaluation.

The source representative is transported by the move's THAM-side chain map.
Representative independence then identifies it with the representative chosen
for the target marking.
-/
theorem elementaryMove_preserves_frontend_evaluation
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (representativeIndependent :
      ∀ (marked : HomologicallyMarkedDiagram),
        RepresentativeIndependenceStatement
          𝒞η graphical compiler normalization
          marked.diagram marked.primalBoundary marked.turnedOver)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η graphical compiler normalization)
    {source target : HomologicallyMarkedDiagram}
    (move : ElementaryMove source target) :
    evaluateMarkedDiagram 𝒞η graphical compiler normalization source =
      evaluateMarkedDiagram 𝒞η graphical compiler normalization target := by
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
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (representativeIndependent :
      ∀ (marked : HomologicallyMarkedDiagram),
        RepresentativeIndependenceStatement
          𝒞η graphical compiler normalization
          marked.diagram marked.primalBoundary marked.turnedOver)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η graphical compiler normalization)
    {source target : HomologicallyMarkedDiagram}
    (movie : KirbyMovie source target) :
    evaluateMarkedDiagram 𝒞η graphical compiler normalization source =
      evaluateMarkedDiagram 𝒞η graphical compiler normalization target := by
  have step :
      ∀ i : Fin movie.stageCount,
        evaluateMarkedDiagram 𝒞η graphical compiler normalization
            (movie.stages i.castSucc) =
          evaluateMarkedDiagram 𝒞η graphical compiler normalization
            (movie.stages i.succ) := by
    intro i
    exact elementaryMove_preserves_frontend_evaluation
      𝒞η graphical compiler normalization
      representativeIndependent localInvariant (movie.elementary i)
  have fromStart :
      ∀ i : Fin (movie.stageCount + 1),
        evaluateMarkedDiagram 𝒞η graphical compiler normalization
            (movie.stages 0) =
          evaluateMarkedDiagram 𝒞η graphical compiler normalization
            (movie.stages i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i inductionHypothesis =>
        exact inductionHypothesis.trans (step i)
  calc
    evaluateMarkedDiagram 𝒞η graphical compiler normalization source =
        evaluateMarkedDiagram 𝒞η graphical compiler normalization
          (movie.stages 0) := by
      rw [movie.startsAtSource]
    _ = evaluateMarkedDiagram 𝒞η graphical compiler normalization
          (movie.stages (Fin.last movie.stageCount)) :=
      fromStart (Fin.last movie.stageCount)
    _ = evaluateMarkedDiagram 𝒞η graphical compiler normalization target := by
      rw [movie.endsAtTarget]

namespace ConditionalDescent

/--
Conditional diffeomorphism descent after all evaluator and topology data have
been supplied.

This is an internal assembly lemma, not the final manifold invariant theorem.
-/
theorem diffeomorphism_invariant_of_descent_data
    (𝒞η : TwistedPremodularCategory K)
    (graphical : RibbonGraphicalEvaluation 𝒞η.category)
    (compiler : RoleAwareGraphCompiler 𝒞η)
    (normalization : ThamDefinition511Normalization K)
    (representativeIndependent :
      ∀ (marked : HomologicallyMarkedDiagram),
        RepresentativeIndependenceStatement
          𝒞η graphical compiler normalization
          marked.diagram marked.primalBoundary marked.turnedOver)
    (localInvariant :
      LocalMoveInvarianceStatement 𝒞η graphical compiler normalization)
    (topology : ClassicalKirbyTopologyBoundary) :
    TwistedYetterDiffeomorphismInvarianceTarget
      𝒞η graphical compiler normalization topology := by
  intro X Y f alpha left right
  obtain ⟨movie⟩ :=
    ClassicalKirbyTopologyBoundary.markedKirbyCerfCompleteness
      topology f alpha left right
  exact
    kirbyMovie_preserves_frontend_evaluation
      𝒞η graphical compiler normalization
      representativeIndependent localInvariant movie

end ConditionalDescent

end

end TwistedYetter.Kirby.Final
