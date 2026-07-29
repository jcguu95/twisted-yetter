import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Axiom audit for the frozen-frontend conditional line

This audit no longer calls the conditional descent lemma a final theorem.
The frozen frontend still lacks canonical evaluator data and the derived
representative-independence and local-move proofs.
-/

#print axioms
  TwistedYetter.Kirby.Final.elementaryMove_preserves_frontend_evaluation

#print axioms
  TwistedYetter.Kirby.Final.kirbyMovie_preserves_frontend_evaluation

#print axioms
  TwistedYetter.Kirby.Final.ConditionalDescent.diffeomorphism_invariant_of_descent_data
