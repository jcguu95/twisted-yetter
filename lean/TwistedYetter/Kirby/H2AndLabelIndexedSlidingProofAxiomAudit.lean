import TwistedYetter.Kirby.CancellationSafeH2Representative
import TwistedYetter.Kirby.CycleRepresentativeCounterexample

/-!
# Axiom audit for the H2 and label-indexed sliding corrections

This audit keeps the two requested proof obligations adjacent:

* an actual handle-chain `H2` class is represented and transported through
  cancellation-safe moves; and
* in the modular identity-functor case, fixed-label and coefficient-weighted
  slides are derived from ordinary Kirby-colour sliding.

The old numerical counterexample is printed only as a regression test for
the wrong primal-chain adapter.  It does not refute descent in the intended
upside-down dual complex.
-/

#print axioms TwistedYetter.Kirby.CycleRepresentativeCounterexample.no_naive_representative_descent

#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.targetCycle_class
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.CancellationSafeStep.alpha_transport
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.eval_sound
#print axioms TwistedYetter.Kirby.CancellationSafeH2Representative.CancellationSafeMovie.value_sound

#print axioms TwistedYetter.Kirby.EGNOCategoryBoundSliding.OrdinaryLabelIndexedSlidingWindow.open_term_sound
#print axioms TwistedYetter.Kirby.EGNOCategoryBoundSliding.OrdinaryLabelIndexedSlidingWindow.term_sound
#print axioms TwistedYetter.Kirby.EGNOCategoryBoundSliding.OrdinaryLabelIndexedSlidingWindow.linear_eval_sound
#print axioms TwistedYetter.Kirby.CanonicalCycleSlideGeometry.BoundGeneralizedLinearSlide.eval_eq
