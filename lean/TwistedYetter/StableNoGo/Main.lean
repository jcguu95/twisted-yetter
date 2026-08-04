import TwistedYetter.StableNoGo.ConnectedSum
import TwistedYetter.StableNoGo.ConditionalMain
import TwistedYetter.StableNoGo.EntranceAxioms
import TwistedYetter.StableNoGo.MarkedStableRealization
import TwistedYetter.StableNoGo.SplitEvaluation

/-!
# Current terminal assembly point for the stable no-go proof

The theorem in this file is still conditional.  Compared with the generic
assembly lemma, however, finite stabilization has been constructed and proved.
Only the three substantive obligations listed in its arguments remain.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

/--
The marked-intersection-form theorem follows from the marked connected-sum
formula, nonvanishing of the resulting stabilization multiplier, and marked
stable realization of lattice isometries.
-/
theorem premodularMarkedIntersectionFormInvariance_of_core_obligations
    (𝒞η : TwistedPremodularCategory K)
    (globalDimension : K)
    (connectedSumFormula :
      MarkedConnectedSumFormula 𝒞η globalDimension)
    (stabilizationMultiplier_ne_zero :
      stabilizationMultiplier 𝒞η globalDimension ≠ 0)
    (markedStableRealization :
      ∀ (X Y : ClosedOrientedSmoothFourManifold),
        IsSimplyConnected X →
        IsSimplyConnected Y →
        ∀ (f : IntegralIntersectionFormIsometry X Y)
          (alpha : ManifoldH₂ X),
          MarkedStableRealization
            stabilize stabilizedMarking alpha (f alpha)) :
    PremodularMarkedIntersectionFormInvariance 𝒞η :=
  premodularMarkedIntersectionFormInvariance_of_stable_inputs
    𝒞η stabilize stabilizedMarking
    (stabilizationMultiplier 𝒞η globalDimension)
    stabilizationMultiplier_ne_zero
    (markedStabilizationFormula_of_connectedSum
      𝒞η globalDimension connectedSumFormula)
    markedStableRealization

end


end TwistedYetter.StableNoGo
