import TwistedYetter.Kirby.Final.TwistedYetter

/-!
# Axiom audit for the frozen-frontend premodular main line

The final theorem now speaks directly about the frozen premodular evaluator.
The former implementation-side local calculations are intentionally outside
this public audit until a separate backend-correctness theorem is established.
-/

#print axioms
  TwistedYetter.Kirby.Final.elementaryMove_preserves_frontend_evaluation

#print axioms
  TwistedYetter.Kirby.Final.kirbyMovie_preserves_frontend_evaluation

#print axioms
  TwistedYetter.Kirby.Final.TwistedYetter_diffeomorphism_invariant
