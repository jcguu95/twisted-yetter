import TwistedYetter.Kirby.Final.Semantics.CompleteSemanticConformance

/-!
# Axiom audit for the frozen-semantics conformance gate

The lifting theorem may use only the standard quotient/classical axioms
already required by the finite categorical construction.  In particular it
must not contain `sorryAx` or a project axiom asserting evaluator equality.
-/

open TwistedYetter.Kirby.Final.CompleteSemanticConformance

#print axioms
  MarkingBinding.currentAlpha_is_exact_turnedOver_marking

#print axioms
  EvaluatorBinding.weightConformance_of_primitive_bindings

#print axioms
  EvaluatorBinding.roleAwareCycleEval_eq_frozenEvaluateCycle

#print axioms
  FrozenConformanceCertificate.formalAdmission

#print axioms
  FrozenConformanceCertificate.sound
