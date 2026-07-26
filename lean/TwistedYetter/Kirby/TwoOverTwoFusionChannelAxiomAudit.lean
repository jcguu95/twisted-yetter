import TwistedYetter.Kirby.TwoOverTwoFusionChannel

/-!
# Kernel axiom audit for the explicit twisted 2/2 fusion channels

These commands keep the two mathematically important facts visible:

* the `d_z`-weighted `(z, μ)` resolution reconstructs the two oriented
  character coupons; and
* a character coupon placed on every internal `z` channel transports through
  the trivalent vertex by naturality.
-/

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.sum_orientedChannelMorphism

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.automorphismObjectPower_naturality

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.sum_orientedChannelCouponMorphism

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.automorphismObjectPower_oriented_eq_smul_identity

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.sum_orientedChannelMorphism_eq_sum_orientedChannelCouponMorphism

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.sum_orientedChannelCouponMorphism_inContext

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.sum_unequalExponentChannelMorphism

#print axioms
  TwistedYetter.Kirby.TwoOverTwoFusionChannel.sum_globalPositiveEndpointChannelMorphism
