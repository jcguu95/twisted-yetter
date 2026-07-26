import TwistedYetter.Kirby.TwoOverTwoNegativeBandMovie

/-!
# Orientation-complete premodular 2/2 slide

The positive and negative local boundaries are handled by separate typed
proofs.  This file performs the exhaustive orientation dispatch and exposes
the one theorem used by the final evaluator route.
-/

namespace TwistedYetter.Kirby.TwoOverTwoOrientationComplete

open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.KirbyCompleteness

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/--
Every orientation of the exact source-bound 2/2 slide preserves the complete
unnormalised premodular evaluator.
-/
theorem cycleLinearDiagram_eval_eq
    (𝒞 : PremodularCategory (K := K) (C := C) (S := S))
    (η : TensorIdentityAutomorphism C)
    {H2 : Type uH} [AddCommGroup H2]
    {source target : CanonicalPresentation H2}
    (metadata :
      TableTwoMoveMetadata .twoOverTwo source.topology target.topology)
    (countsSound : source.topology.counts = target.topology.counts)
    (sourceCycle : source.DegreeTwoCycle) :
    LinearDiagram.eval
        (source.cycleLinearDiagram 𝒞 η sourceCycle) =
      LinearDiagram.eval
        (target.cycleLinearDiagram 𝒞 η
          ((CanonicalSourceBoundSlideMovie.Request.twoOverTwo
            metadata countsSound).targetCycle sourceCycle)) := by
  cases orientationSound :
      (CanonicalSourceBoundSlideMovie.Request.twoOverTwo
        metadata countsSound).orientation with
  | positive =>
      exact
        TwoOverTwoBandMovie.positiveBandMovie_cycleLinearDiagram_eval_eq
          𝒞 η metadata countsSound orientationSound
          sourceCycle
  | negative =>
      exact
        TwoOverTwoNegativeBandMovie.negativeBandMovie_cycleLinearDiagram_eval_eq
          𝒞 η metadata countsSound orientationSound sourceCycle

end TwistedYetter.Kirby.TwoOverTwoOrientationComplete
