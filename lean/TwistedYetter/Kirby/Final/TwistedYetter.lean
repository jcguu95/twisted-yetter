import TwistedYetter.Kirby.Final.Semantics.Independent.Entry

/-!
# Public homologically twisted Yetter invariant

This public file has no second evaluator and no conformance detour.  Its final
theorem speaks directly about the frozen independent frontend semantics.
-/

namespace TwistedYetter.Kirby.Final

open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The public evaluator on one frozen-frontend marked diagram.

This is exactly `Independent.evaluateMarking`; it is not a wrapper around the
previous repository evaluator.
-/
abbrev TwistedYetter
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
    TwistedYetter 𝒞η graphical compiler normalization source =
      TwistedYetter 𝒞η graphical compiler normalization target := by
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
    TwistedYetter 𝒞η graphical compiler normalization source =
      TwistedYetter 𝒞η graphical compiler normalization target := by
  have step :
      ∀ i : Fin movie.stageCount,
        TwistedYetter 𝒞η graphical compiler normalization
            (movie.stages i.castSucc) =
          TwistedYetter 𝒞η graphical compiler normalization
            (movie.stages i.succ) := by
    intro i
    exact elementaryMove_preserves_frontend_evaluation
      𝒞η graphical compiler normalization
      representativeIndependent localInvariant (movie.elementary i)
  have fromStart :
      ∀ i : Fin (movie.stageCount + 1),
        TwistedYetter 𝒞η graphical compiler normalization
            (movie.stages 0) =
          TwistedYetter 𝒞η graphical compiler normalization
            (movie.stages i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i inductionHypothesis =>
        exact inductionHypothesis.trans (step i)
  calc
    TwistedYetter 𝒞η graphical compiler normalization source =
        TwistedYetter 𝒞η graphical compiler normalization
          (movie.stages 0) := by
      rw [movie.startsAtSource]
    _ = TwistedYetter 𝒞η graphical compiler normalization
          (movie.stages (Fin.last movie.stageCount)) :=
      fromStart (Fin.last movie.stageCount)
    _ = TwistedYetter 𝒞η graphical compiler normalization target := by
      rw [movie.endsAtTarget]

/--
The final theorem is exactly the diffeomorphism-invariance target stated by the
frozen frontend.

There is deliberately no current-evaluator certificate in either the statement
or the proof.
-/
theorem TwistedYetter_diffeomorphism_invariant
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

end

end TwistedYetter.Kirby.Final
