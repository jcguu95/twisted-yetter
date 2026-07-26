import TwistedYetter.Kirby.TwoOverTwoOrientationComplete

/-!
# Axiom audit for the source-bound slide movie

The final line is the public orientation-complete premodular 2-over-2
statement.  Its dependency list must expose the positive and negative
Bärenz--Barrett band-movie inputs and must not contain any of the deleted
attach/detach endpoint-equality axioms.
-/

#print axioms TwistedYetter.Kirby.CanonicalSourceBoundSlideMovie.premodularTwoOverTwoExponentTransport
#print axioms TwistedYetter.Kirby.TwoOverTwoBandMovie.positiveBandMovie_cycleLinearDiagram_eval_eq
#print axioms TwistedYetter.Kirby.TwoOverTwoNegativeBandMovie.negativeBandMovie_cycleLinearDiagram_eval_eq
#print axioms TwistedYetter.Kirby.TwoOverTwoOrientationComplete.cycleLinearDiagram_eval_eq
