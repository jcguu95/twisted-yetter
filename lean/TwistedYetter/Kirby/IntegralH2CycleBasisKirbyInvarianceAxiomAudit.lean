import TwistedYetter.Kirby.IntegralH2CycleBasisKirbyInvariance

/-!
# Axiom audit for generalized integral cycle-basis Kirby invariance

The local and quotient theorems may depend on the disclosed category
graphical inputs.  They must not depend on an arbitrary representative-
descent axiom.
-/

open TwistedYetter.Kirby.IntegralH2CycleBasisKirbyInvariance

#print axioms
  integralCycleBasisPresentationValue_eq_of_strictComparison
#print axioms integralCycleBasisPresentationValue_rebase
#print axioms
  IntegralCycleBasisMoveCompatibility.presentationValue_eq
#print axioms integralCycleBasisEvaluation_localInvariant
#print axioms integralCycleBasisEvaluationOnKirbyClass
#print axioms integralCycleBasisEvaluationOnKirbyClass_mk
