import TwistedYetter

/-!
# Kernel axiom audit for the Kirby coupon bootstrap

This file is compiled by `scripts/lean_axiom_audit.sh`. The script fails if
Lean reports `sorryAx`.
-/

#print axioms TwistedYetter.Kirby.CouponNaturality.slide_through_positive_crossing
#print axioms TwistedYetter.Kirby.CouponNaturality.slide_through_negative_crossing
#print axioms TwistedYetter.Kirby.CouponNaturality.slide_through_left_cup
#print axioms TwistedYetter.Kirby.CouponNaturality.slide_through_left_cap
#print axioms TwistedYetter.Kirby.CouponNaturality.slide_through_right_cup
#print axioms TwistedYetter.Kirby.CouponNaturality.slide_through_right_cap
#print axioms TwistedYetter.Kirby.CategoricalTangle.Context.eval_plug_congr
#print axioms TwistedYetter.Kirby.CategoricalTangle.positiveCrossingMove_sound
#print axioms TwistedYetter.Kirby.CategoricalTangle.negativeCrossingMove_sound
#print axioms TwistedYetter.Kirby.CategoricalTangle.leftCupMove_sound
#print axioms TwistedYetter.Kirby.CategoricalTangle.leftCapMove_sound
#print axioms TwistedYetter.Kirby.CategoricalTangle.rightCupMove_sound
#print axioms TwistedYetter.Kirby.CategoricalTangle.rightCapMove_sound
#print axioms TwistedYetter.Kirby.CategoricalMovie.Movie.sound
#print axioms TwistedYetter.Kirby.FramingNaturality.NaturalTwist.positive_transport_sound
#print axioms TwistedYetter.Kirby.FramingNaturality.NaturalTwist.negative_transport_sound
#print axioms TwistedYetter.Kirby.HandleSlide.SourcedSlidingLaw.coupon_transport_sound
#print axioms TwistedYetter.Kirby.HandleSlide.SourcedSlidingLaw.coupon_transport_in_context_sound
