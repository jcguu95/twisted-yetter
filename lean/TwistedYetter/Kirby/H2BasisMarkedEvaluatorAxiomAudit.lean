import TwistedYetter.Kirby.H2BasisMarkedEvaluator

/-!
# Axiom audit for the H2-basis-marked evaluator

The representative theorem must be a kernel-checked consequence of defining
the evaluator on `H₂`.  Basis independence remains visible through graphical
calculation proof terms.
-/

open
  TwistedYetter.Kirby.H2BasisMarkedEvaluator.CanonicalPresentation

#print axioms H2BasisRealization.basisHandle_injective
#print axioms H2BasisRealization.markedCycle_class
#print axioms H2BasisRealization.nonbasis_componentExponent
#print axioms basisMarkedPresentationValue_eq_rawCycleColourEval
#print axioms BasisReindexing.presentationValue_eq
#print axioms BasisChangeGraphicalRealization.presentationValue_eq
#print axioms
  BasisIndependenceProof.EvalC_eq_basisMarkedPresentationValue
#print axioms BasisIndependenceProof.EvalC_congr
