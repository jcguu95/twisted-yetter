import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Axiom audit for the frozen-frontend public invariant

The public route imports the independent semantic entry directly.  This audit
therefore prints only the frontend evaluator and the three derived invariance
theorems; no legacy evaluator or conformance certificate is in scope.
-/

#print axioms TwistedYetter.Kirby.Final.TwistedYetter
#print axioms
  TwistedYetter.Kirby.Final.elementaryMove_preserves_frontend_evaluation
#print axioms
  TwistedYetter.Kirby.Final.kirbyMovie_preserves_frontend_evaluation
#print axioms
  TwistedYetter.Kirby.Final.TwistedYetter_diffeomorphism_invariant
