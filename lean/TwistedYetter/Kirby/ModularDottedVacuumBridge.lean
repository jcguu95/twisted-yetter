import TwistedYetter.Kirby.ThamThreeHandleVacuum

/-!
# Exact modular dotted-component vacuum bridge target

Under the dual/upside-down convention, a primal dotted one-handle is Tham's
`k = 3` handle.  The remaining local theorem is therefore not a mysterious
map for primal three-handles.  It is the following concrete statement:

the positive Hopf pair formed by the specially dotted component and its
cancelling primal two-handle has the same finite label sum for every integral
homological exponent on the two-handle.

This file defines that exact finite sum.  Lean proves the exponent-zero case
from the ordinary cancellation input and the all-exponent case from the
label-resolved Bärenz--Barrett killing lemma.  The bridge is a theorem, not a
caller-supplied field of the final invariant.
-/

namespace TwistedYetter.Kirby.ModularDottedVacuumBridge

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.ComponentRibbonDiagram
open TwistedYetter.Kirby.EGNOModularKirbyMoves
open TwistedYetter.Kirby.EGNOModularKirbyMoves.LiteratureBackedModularGraphicalEnvironment
open TwistedYetter.Kirby.ThamThreeHandleVacuum

universe uK uC vC

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

/-- Canonical labels for the two components of the local Hopf pair. -/
def pairLabel
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (dottedId twoHandleId : String)
    (labels : Fin 2 → S)
    (componentId : String) : S :=
  if componentId = dottedId then labels 0
  else if componentId = twoHandleId then labels 1
  else 𝒞.premodular.toFusionCategoryData.unitIndex

@[simp] theorem pairLabel_dotted
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (dottedId twoHandleId : String)
    (labels : Fin 2 → S) :
    pairLabel 𝒞 dottedId twoHandleId labels dottedId = labels 0 := by
  simp [pairLabel]

@[simp] theorem pairLabel_twoHandle
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (dottedId twoHandleId : String)
    (distinct : dottedId ≠ twoHandleId)
    (labels : Fin 2 → S) :
    pairLabel 𝒞 dottedId twoHandleId labels twoHandleId = labels 1 := by
  simp [pairLabel, Ne.symm distinct]

/--
The actual serialized local sum with exponent `n` on the ordinary
two-handle.  The dotted component has ordinary Kirby-colour weight; it is not
mistaken for a primal degree-two component.
-/
noncomputable def twistedHopfPairSum
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (exponent : ℤ) : K :=
  ∑ labels : Fin 2 → S,
    ((𝒞.premodular.quantumDimension (labels 0) *
        𝒞.premodular.quantumDimension (labels 1)) *
      𝒞.premodular.toFusionCategoryData.automorphismScalarPower
        automorphism (labels 1) exponent) *
      𝒞.premodular.toFusionCategoryData.closedScalar
        (CategoricalTangle.Diagram.eval C
          ((ComponentDiagram.oneTwoHopfPair dottedId twoHandleId).interpret
            𝒞.premodular
            (pairLabel 𝒞 dottedId twoHandleId labels)))

/-- The already-established ordinary cancellation is the exponent-zero case. -/
theorem twistedHopfPairSum_zero
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (distinct : dottedId ≠ twoHandleId) :
    twistedHopfPairSum 𝒞 automorphism dottedId twoHandleId 0 =
      globalDimension 𝒞.premodular := by
  classical
  simp only [twistedHopfPairSum,
    FusionCategoryData.automorphismScalarPower_zero, mul_one]
  exact baerenzBarrett_oneTwoHopfPairSum
    𝒞 dottedId twoHandleId distinct
    (pairLabel 𝒞 dottedId twoHandleId)
    (pairLabel_dotted 𝒞 dottedId twoHandleId)
    (pairLabel_twoHandle 𝒞 dottedId twoHandleId distinct)

/--
The label-resolved Bärenz--Barrett killing lemma proves the complete vacuum
bridge for every integral exponent.  Lean performs the finite-sum reindexing,
uses modularity to retain only the unit label, and then uses monoidality of
the automorphism on that unit.
-/
theorem twistedHopfPairSum_eq_globalDimension
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (distinct : dottedId ≠ twoHandleId)
    (exponent : ℤ) :
    twistedHopfPairSum 𝒞 automorphism dottedId twoHandleId exponent =
      globalDimension 𝒞.premodular := by
  classical
  let pairEquiv : (Fin 2 → S) ≃ S × S :=
    piFinTwoEquiv (fun _ : Fin 2 => S)
  let summand : (Fin 2 → S) → K := fun labels =>
    ((𝒞.premodular.quantumDimension (labels 0) *
        𝒞.premodular.quantumDimension (labels 1)) *
      𝒞.premodular.toFusionCategoryData.automorphismScalarPower
        automorphism (labels 1) exponent) *
      𝒞.premodular.toFusionCategoryData.closedScalar
        (CategoricalTangle.Diagram.eval C
          ((ComponentDiagram.oneTwoHopfPair dottedId twoHandleId).interpret
            𝒞.premodular
            (pairLabel 𝒞 dottedId twoHandleId labels)))
  have reindex :
      (∑ labels : Fin 2 → S, summand labels) =
        ∑ labels : S × S, summand (pairEquiv.symm labels) :=
    (Equiv.sum_comp pairEquiv.symm summand).symm
  rw [twistedHopfPairSum]
  change (∑ labels : Fin 2 → S, summand labels) = _
  rw [reindex, Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ twoHandleLabel : S, ∑ dottedLabel : S,
        summand (pairEquiv.symm (dottedLabel, twoHandleLabel))) =
        ∑ twoHandleLabel : S,
          (𝒞.premodular.quantumDimension twoHandleLabel *
            𝒞.premodular.toFusionCategoryData.automorphismScalarPower
              automorphism twoHandleLabel exponent) *
            (∑ dottedLabel : S,
              𝒞.premodular.quantumDimension dottedLabel *
                𝒞.premodular.toFusionCategoryData.closedScalar
                  (CategoricalTangle.Diagram.eval C
                    ((ComponentDiagram.oneTwoHopfPair
                      dottedId twoHandleId).interpret
                        𝒞.premodular
                        (pairLabel 𝒞 dottedId twoHandleId
                          (pairEquiv.symm
                            (dottedLabel, twoHandleLabel)))))) := by
      apply Finset.sum_congr rfl
      intro twoHandleLabel _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro dottedLabel _
      simp only [summand, pairEquiv, piFinTwoEquiv,
        Equiv.coe_fn_symm_mk, Fin.cons_zero, Fin.cons_one]
      ring
    _ = ∑ twoHandleLabel : S,
          (𝒞.premodular.quantumDimension twoHandleLabel *
            𝒞.premodular.toFusionCategoryData.automorphismScalarPower
              automorphism twoHandleLabel exponent) *
            (if twoHandleLabel =
                𝒞.premodular.toFusionCategoryData.unitIndex then
              globalDimension 𝒞.premodular
            else
              0) := by
      apply Finset.sum_congr rfl
      intro twoHandleLabel _
      apply congrArg
      exact baerenzBarrett_hopfKirbyKillingFiber
        𝒞 dottedId twoHandleId distinct
        (fun dottedLabel twoLabel =>
          pairLabel 𝒞 dottedId twoHandleId
            (pairEquiv.symm (dottedLabel, twoLabel)))
        (by
          intro dottedLabel twoLabel
          simp [pairEquiv, piFinTwoEquiv])
        (by
          intro dottedLabel twoLabel
          simpa only [pairEquiv, piFinTwoEquiv,
            Equiv.coe_fn_symm_mk, Fin.cons_one, Fin.cons_zero] using
            pairLabel_twoHandle 𝒞 dottedId twoHandleId distinct
              (pairEquiv.symm (dottedLabel, twoLabel)))
        twoHandleLabel
    _ = globalDimension 𝒞.premodular := by
      rw [Finset.sum_eq_single
        𝒞.premodular.toFusionCategoryData.unitIndex]
      · simp [egno_quantumDimension_unit 𝒞,
          automorphismScalarPower_unitIndex
            𝒞.premodular.toFusionCategoryData automorphism exponent]
      · intro simple _ notUnit
        simp [notUnit]
      · intro unitMissing
        exact (unitMissing (Finset.mem_univ _)).elim

/--
Exact missing categorical theorem: the dotted component realizes the vacuum
projector for every integral boundary exponent.
-/
def RealizesThamK3Vacuum
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String) : Prop :=
  ∀ exponent : ℤ,
    twistedHopfPairSum 𝒞 automorphism dottedId twoHandleId exponent =
      globalDimension 𝒞.premodular

/-- The standard modular killing lemma constructs the bridge. -/
theorem realizesThamK3Vacuum
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (distinct : dottedId ≠ twoHandleId) :
    RealizesThamK3Vacuum 𝒞 automorphism dottedId twoHandleId :=
  twistedHopfPairSum_eq_globalDimension
    𝒞 automorphism dottedId twoHandleId distinct

namespace RealizesThamK3Vacuum

/-- Once the bridge is proved, boundary-related exponents evaluate equally. -/
theorem exponent_independent
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (bridge : RealizesThamK3Vacuum 𝒞 automorphism dottedId twoHandleId)
    (left right : ℤ) :
    twistedHopfPairSum 𝒞 automorphism dottedId twoHandleId left =
      twistedHopfPairSum 𝒞 automorphism dottedId twoHandleId right := by
  rw [bridge left, bridge right]

/-- The bridge agrees with the separately proved unit-sector shadow. -/
theorem agrees_with_unitSector
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (dottedId twoHandleId : String)
    (bridge : RealizesThamK3Vacuum 𝒞 automorphism dottedId twoHandleId)
    (exponent : ℤ) :
    twistedHopfPairSum 𝒞 automorphism dottedId twoHandleId exponent =
      globalDimension 𝒞.premodular *
        vacuumProjectedRegularWeight 𝒞.premodular automorphism exponent := by
  rw [bridge exponent, vacuumProjectedRegularWeight_eq_one, mul_one]

end RealizesThamK3Vacuum

/-- The exact current result: every integral exponent is proved. -/
def currentStatus : String :=
  "PASS_ALL_EXPONENT_MODULAR_DOTTED_THAM_K3_VACUUM_BRIDGE"

end TwistedYetter.Kirby.ModularDottedVacuumBridge
