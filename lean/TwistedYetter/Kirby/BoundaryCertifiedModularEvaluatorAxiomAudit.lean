import TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator

/-!
# Axiom audit for the boundary-certified modular evaluator

The bridge may use the already-visible modular graphical axioms and the one
named handle-chain naturality axiom.  It must not introduce any other topology
axiom or a proof oracle.
-/

#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator.BoundaryCertifiedMove.enriched
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator.boundaryCertifiedCalculus
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator.boundaryCertifiedEvaluation
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator.boundaryCertifiedEvaluation_localInvariant
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator.boundaryCertifiedEvaluationOnKirbyClass
#print axioms
  TwistedYetter.Kirby.BoundaryCertifiedModularEvaluator.boundaryCertifiedEvaluationOnKirbyClass_mk
