import TwistedYetter.Kirby.CanonicalModularKirbyEvaluator

/-!
# Axiom audit for the canonical modular presentation value

The event and finite-sum compiler must not use a project axiom.  The final
normalization uses only the named EGNO modular dimension theorem boundary.
-/

#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.EventWindow.compile
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.Trace.compile
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.termDiagram
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.linearDiagram_eval
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.rawCycleColourEval
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.chosenCycleSectionValue
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.CycleBoundaryGraphicalRealization.representativeIndependence
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.EvalC_eq_cycleEvalC
#print axioms TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.EvalC_eq_normalized
