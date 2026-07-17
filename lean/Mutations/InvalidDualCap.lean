import TwistedYetter.Kirby.CouponKernel

namespace TwistedYetter.Mutations.InvalidDualCap

open TwistedYetter.Kirby

inductive Wire
  | red
  | blue

instance : WireDuality Wire where
  dual
    | .red => .blue
    | .blue => .red
  dual_dual wire := by cases wire <;> rfl

instance : CouponSignature Wire where
  Coupon _ _ := Unit

-- Expected failure: cap red consumes [blue, red], not [red, red].
def invalidDualCap : Tangle Wire [.red, .red] [] :=
  Tangle.cap Wire.red

end TwistedYetter.Mutations.InvalidDualCap
