import TwistedYetter.Kirby.ModularOpenKilling

/-!
# Axiom audit for the open modular killing proof

The diagram-to-partial-trace bridge, finite-sum scalarization, S-column
reduction, Schur reconstruction, and closed Hopf consequence are local
theorems.  The only mathematical inputs are the explicitly named EGNO
partial-trace, weighted S-column, and nonzero-dimension facts.
-/

#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.openEncirclingDiagram_eval
#print axioms
  TwistedYetter.Fusion.EGNO.PremodularCategory.quantumDimension_unit
#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.egno_partialTraceCharacter
#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.egno_weightedSColumn
#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.egno_simpleQuantumDimension_ne_zero
#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.openKirbyEncirclingOperator_eq_scalar_smul
#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.baerenzBarrett_tham_openKirbyKilling_simpleScalar
#print axioms
  TwistedYetter.Kirby.ModularOpenKilling.baerenzBarrett_tham_openKirbyKilling_simple
