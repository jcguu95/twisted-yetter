import TwistedYetter.Kirby.H2BasisMarkedKirbyInvariance

/-!
# Axiom audit for H2-basis-marked Kirby invariance

The local equality, finite-movie descent, and quotient construction must be
kernel-checked consequences of explicit cycle transport and graphical proof
objects.  The audit keeps all remaining literature-backed category axioms
visible.
-/

open TwistedYetter.Kirby.H2BasisMarkedKirbyInvariance

#print axioms BasisMarkedMoveCompatibility.presentationValue_eq
#print axioms basisMarkedEvaluation_localInvariant
#print axioms basisMarkedEvaluationOnKirbyClass
#print axioms basisMarkedEvaluationOnKirbyClass_mk
