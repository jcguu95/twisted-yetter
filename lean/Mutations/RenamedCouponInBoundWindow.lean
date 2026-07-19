import TwistedYetter.Kirby.CategoricalPresentationCompiler

namespace TwistedYetter.Mutations.RenamedCouponInBoundWindow

open CategoryTheory
open TwistedYetter.Kirby.CategoricalPresentationCompiler
open TwistedYetter.Kirby.Presentation

universe u v

variable {C : Type u} [Category.{v} C]
variable [MonoidalCategory C] [BraidedCategory C]

/--
This must fail: a coupon primitive certified under one ID cannot be admitted
as a different serialized coupon ID.
-/
def unsafeRename
    (objectOf : StrandState → C)
    (expectedId wrongId label : String)
    (strands : List String)
    (before after localWindow : List StrandState)
    (window :
      WindowedCategoricalEvent objectOf .coupon before after)
    (sourceSound : window.localSource = localWindow)
    (targetSound : window.localTarget = localWindow)
    (idsSound :
      localWindow.map (fun strand => strand.strandId) = strands)
    (wrongIdSound : window.primitive.couponId? = some wrongId)
    (labelSound : window.primitive.couponLabel? = some label) :
    BoundCouponEvent objectOf expectedId label strands before after where
  window := window
  localWindow := localWindow
  local_source_sound := sourceSound
  local_target_sound := targetSound
  ordered_ids_sound := idsSound
  coupon_id_sound := wrongIdSound
  coupon_label_sound := labelSound

end TwistedYetter.Mutations.RenamedCouponInBoundWindow
