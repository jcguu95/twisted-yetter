import TwistedYetter.Kirby.CouponKernel

namespace TwistedYetter.Mutations.InvalidComposition

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

def redToBlue : Tangle Wire [.red] [.blue] :=
  .coupon ()

def redToRed : Tangle Wire [.red] [.red] :=
  .coupon ()

-- Expected failure: the first output is blue but the second input is red.
def invalidComposition : Tangle Wire [.red] [.red] :=
  redToBlue ≫ₜ redToRed

end TwistedYetter.Mutations.InvalidComposition
