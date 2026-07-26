import TwistedYetter.Kirby.ConcreteMarkedPairAssembly

namespace TwistedYetter.Kirby.ConcreteMarkedPairAssembly.Mutations

open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.SourceBackedKirbyCompleteness

universe uH

example
    (H2 : Type uH) [AddCommGroup H2]
    (localCompiler : LocalMarkedH2Compiler H2) :
    {source target : SpecialKirbyPresentation H2} →
    (move : TopologicalTableTwoMove source target) →
      (localCompiler.transport move).homologyAddEquiv =
        AddEquiv.refl H2 := by
  intro source target move
  rfl

end TwistedYetter.Kirby.ConcreteMarkedPairAssembly.Mutations
