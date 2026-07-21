import TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance

/-!
# Axiom audit for arbitrary-H2 marked Kirby invariance

These commands make the dependency boundary visible in build logs.  The
local theorem is derived from the supplied modular-category structure and
certified local move; it introduces no project axiom and assumes no
finite-free structure on `H2`.
-/

#print axioms TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance.markedEvaluation_localInvariant
#print axioms TwistedYetter.Kirby.GeneralH2MarkedKirbyInvariance.evaluationOnKirbyClass_mk
