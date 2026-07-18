import TwistedYetter.Kirby.SourceBoundGraphicalMoveCompiler

namespace TwistedYetter.Mutations.FinalNormalizedEqualityInsideOneTwoFactorization

open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.RibbonKirbyGraphicalAlgebra
open TwistedYetter.Kirby.SourceBoundGraphicalMoveCompilation

universe u

variable {K : Type u} [Field K]

/-
This must fail: a 1--2 factorization program cannot contain a pre-proved final
equality of normalized invariant values.
-/
def unsafeProgram
    {profile : GlobalDimensionProfile (K := K)}
    {algebra : CancellationInput profile}
    {before after : EvaluationState (K := K)}
    (base : OneTwoFactorizationProgram algebra before after) :
    OneTwoFactorizationProgram algebra before after :=
  { base with normalizedEquality := True }

end TwistedYetter.Mutations.FinalNormalizedEqualityInsideOneTwoFactorization
