import TwistedYetter.Kirby.CancellationSafeH2Representative

/-!
# Axiom audit for cancellation-safe second-homology representatives

The naive assertion that the cycle-colour evaluation descends through every
fiber of `cycles -> H2` is false.  This audit instead exposes the dependencies
of the corrected theorem: the public input is an actual `H2` class, its
geometric cycle represents that class, and cancellation deaths must satisfy
the visible no-hidden-boundary condition.
-/

#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.targetCycle_class
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.CancellationSafeStep.alpha_transport
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.cycleEvalC_sound
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.eval_sound
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.CancellationSafeMovie.value_sound
