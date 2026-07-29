import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Axiom audit for frozen-frontend conditional descent

The route imports the independent semantic entry directly.  The clean
manifold-level invariant is intentionally absent until the canonical
evaluator data and local proofs can be derived without new blanket axioms.
-/

#print axioms TwistedYetter.Kirby.Final.evaluateMarkedDiagram
#print axioms
  TwistedYetter.Kirby.Final.elementaryMove_preserves_frontend_evaluation
#print axioms
  TwistedYetter.Kirby.Final.kirbyMovie_preserves_frontend_evaluation
#print axioms
  TwistedYetter.Kirby.Final.ConditionalDescent.diffeomorphism_invariant_of_descent_data
