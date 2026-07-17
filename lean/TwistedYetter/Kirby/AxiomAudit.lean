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
#print axioms TwistedYetter.Kirby.HandleSlide.SourcedFunctorSlidingLaw.coupon_transport_sound
#print axioms TwistedYetter.Kirby.LinearDiagram.eval_weightedSum
#print axioms TwistedYetter.Kirby.LinearDiagram.eval_collapse
#print axioms TwistedYetter.Kirby.LinearContext.evalContextLinearMap_apply
#print axioms TwistedYetter.Kirby.LinearContext.insertIdentity
#print axioms TwistedYetter.Kirby.MateDiagram.mateExpanded_sound
#print axioms TwistedYetter.Kirby.MateDiagram.dualMateExpanded_sound
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingCategoryData.equation_3_1_9_to_3_1_11
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingFiber.equation_3_1_4
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingFiber.equation_3_1_5
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingFiber.equation_3_1_6
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingFiber.equation_3_1_7_to_3_1_8
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingFiber.core_sound
#print axioms TwistedYetter.Kirby.GeneralizedSliding.SlidingFamily.equation_3_1_2
#print axioms TwistedYetter.Kirby.FramedSliding.liftExterior_eval
#print axioms TwistedYetter.Kirby.FramedSliding.exterior_transport_sound
#print axioms TwistedYetter.Kirby.FramedSliding.exterior_transport_in_context_sound
#print axioms TwistedYetter.Kirby.FramedSliding.ClosedFramedContext.lemma_3_4
#print axioms TwistedYetter.Kirby.FramedSliding.SlidingFamily.lemma34Movie_sound
#print axioms TwistedYetter.Kirby.Presentation.FormalPresentation.validation_witness
#print axioms TwistedYetter.Kirby.Presentation.FormalPresentation.pinned_source_hash_eq
