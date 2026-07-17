import TwistedYetter.Kirby.Presentation

/-!
This mutation must not compile.  The formal raw schema has no mutable alias
field; only a pinned source content hash is representable.
-/

namespace TwistedYetter.Mutations.MutableAliasPresentation

open TwistedYetter.Kirby.Presentation

def rejected : RawPresentation :=
  { roundTripFixture with alias := "current" }

end TwistedYetter.Mutations.MutableAliasPresentation
