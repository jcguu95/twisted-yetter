import Mathlib.Data.Fintype.BigOperators
import TwistedYetter.Kirby.CanonicalModularKirbyEvaluator

/-!
# An optional H2-basis-marked modular Kirby evaluator

This module implements the sphere-basis prescription used in Yetter's
restricted surgery argument:

* topology supplies actual degree-two cycles supported on selected
  two-handles;
* their two-handle coordinates and homology classes are certified to form an
  integral basis;
* the marked input is `alpha : H₂`, not a degree-two cycle;
* only the selected basis components receive the coordinates of `alpha`;
* every other component, including a newly cancellable two-handle, receives
  exponent zero.

The construction is useful independently of the general dual-chain route.
It must not be presented as a repair forced by the old primal cancelling-pair
"counterexample": that diagnosis used the wrong handle convention.

Independence of the selected sphere basis is a separate graphical obligation.
It is represented below by `BasisChangeGraphicalRealization`, whose field
returns a proof term in the existing closed coupon calculus rather than a bare
scalar equality.

Reference: `ref:yetter-homologically-twisted-1993`, Definition 10 and
Theorem 11, PDF pages 4--5.  The source theorem itself is in the
simply-connected, mod-two Broda setting.  The integral-coordinate
generalization formalized here still requires the displayed basis-change
graphical realizations.
-/

namespace TwistedYetter.Kirby.H2BasisMarkedEvaluator

open scoped BigOperators
open CategoryTheory
open TwistedYetter.Fusion.EGNO
open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.CategoricalTangle
open TwistedYetter.Kirby.EGNOModularFourManifoldInvariant
open TwistedYetter.Kirby.HomologicallyTwistedInvariant
open TwistedYetter.Kirby.KirbyCancellation
open TwistedYetter.Kirby.KirbyCompleteness
open TwistedYetter.Kirby.LinearDiagram
open TwistedYetter.Kirby.Presentation
open TwistedYetter.Kirby.TensorAutomorphismCouponCalculus

universe uK uC vC uH

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [CategoryTheory.Linear K C]
variable [MonoidalCategory C] [RigidCategory C] [BraidedCategory C]
variable [MonoidalPreadditive C] [MonoidalLinear K C]
variable {S : Type} [Fintype S] [DecidableEq S]

namespace CanonicalPresentation

/-- The integral unit vector corresponding to one basis index. -/
def coordinateUnit (rank : Nat) (index coordinate : Fin rank) : ℤ :=
  if coordinate = index then 1 else 0

/--
A family of actual degree-two cycles, each supported on one selected
two-handle, certified to be an integral basis of the presentation's
handle-chain `H₂`.

`coordinates` proves freeness and supplies all coordinates.  The final field
pins the cycle both to the selected two-handle unit vector and to the
corresponding homology basis vector.  A caller therefore cannot choose
unrelated handles, cycles, and abstract basis data.
-/
structure H2BasisRealization
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (presentation : CanonicalPresentation manifold H2) where
  rank : Nat
  coordinates :
    presentation.topology.handleChain.SecondHomology ≃+
      (Fin rank → ℤ)
  basisHandle :
    Fin rank → Fin presentation.topology.counts.h2
  basisIndex? :
    Fin presentation.topology.counts.h2 → Option (Fin rank)
  basis_index_roundtrip :
    (index : Fin rank) →
      basisIndex? (basisHandle index) = some index
  basis_index_sound :
    (handle : Fin presentation.topology.counts.h2) →
    (index : Fin rank) →
      basisIndex? handle = some index →
        handle = basisHandle index
  basisCycle :
    Fin rank → presentation.DegreeTwoCycle
  basis_cycle_handle_coordinates :
    (index : Fin rank) →
    (handle : Fin presentation.topology.counts.h2) →
      presentation.cycleHandleCoefficients
          (basisCycle index) handle =
        coordinateUnit presentation.topology.counts.h2
          (basisHandle index) handle
  basis_homology_coordinates :
    (index coordinate : Fin rank) →
      coordinates
          (presentation.topology.handleChain.complex.homologyπ 2
            (basisCycle index))
          coordinate =
        coordinateUnit rank index coordinate
  basisCertificateHash : String
  basis_certificate_hash_shape :
    RawPresentation.sha256Shape basisCertificateHash = true
  sourceRefs : List String
  exactScope : String
  sourceScopeCaveat : String

namespace H2BasisRealization

/-- The selected handle map is injective, derived from its proved inverse. -/
theorem basisHandle_injective
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation) :
    Function.Injective realization.basisHandle := by
  intro left right equality
  have inverseEquality :=
    congrArg realization.basisIndex? equality
  simpa [realization.basis_index_roundtrip] using inverseEquality

/--
The canonical degree-two cycle selected by the certified sphere basis.

This is a linear combination of actual cycles, not a choice of an arbitrary
representative from the homology quotient.
-/
noncomputable def markedCycle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.DegreeTwoCycle :=
  ∑ index,
    (realization.coordinates alpha index) •
      realization.basisCycle index

/-- The canonical marked cycle represents exactly the requested `H₂` class. -/
theorem markedCycle_class
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    presentation.topology.handleChain.complex.homologyπ 2
        (realization.markedCycle alpha) =
      alpha := by
  classical
  apply realization.coordinates.injective
  funext coordinate
  simp [markedCycle, realization.basis_homology_coordinates,
    coordinateUnit]

/-- Coordinate expansion of the canonical marked cycle in the handle basis. -/
theorem markedCycle_coefficient_eq_sum
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2) :
    presentation.cycleHandleCoefficients
        (realization.markedCycle alpha) handle =
      ∑ index,
        realization.coordinates alpha index *
          coordinateUnit presentation.topology.counts.h2
            (realization.basisHandle index) handle := by
  classical
  calc
    presentation.cycleHandleCoefficients
        (realization.markedCycle alpha) handle =
      ∑ index,
        realization.coordinates alpha index *
          presentation.cycleHandleCoefficients
            (realization.basisCycle index) handle := by
      unfold markedCycle
      unfold CanonicalPresentation.cycleHandleCoefficients
      rw [map_sum, map_sum]
      simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro index _
      rw [map_zsmul, map_zsmul]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [realization.basis_cycle_handle_coordinates]

/--
On a selected basis handle, the marked cycle has exactly the corresponding
coordinate of `alpha`.
-/
theorem markedCycle_coefficient_basisHandle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (index : Fin realization.rank) :
    presentation.cycleHandleCoefficients
        (realization.markedCycle alpha)
        (realization.basisHandle index) =
      realization.coordinates alpha index := by
  classical
  rw [realization.markedCycle_coefficient_eq_sum]
  simp only [coordinateUnit]
  simp_rw [realization.basisHandle_injective.eq_iff]
  simp

/--
On every handle outside the selected basis, the canonical marked cycle has
coefficient zero.
-/
theorem markedCycle_coefficient_of_not_selected
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2)
    (notSelected : realization.basisIndex? handle = none) :
      presentation.cycleHandleCoefficients
        (realization.markedCycle alpha) handle = 0 := by
  classical
  have handle_ne :
      (index : Fin realization.rank) →
        handle ≠ realization.basisHandle index := by
    intro index equality
    have roundtrip := realization.basis_index_roundtrip index
    rw [← equality, notSelected] at roundtrip
    contradiction
  rw [realization.markedCycle_coefficient_eq_sum]
  simp [coordinateUnit, handle_ne]

/--
Integral exponent on one two-handle.

Only handles in the certified sphere basis read a coordinate of `alpha`.
Every non-basis handle receives zero.
-/
noncomputable def handleExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2) : ℤ :=
  match realization.basisIndex? handle with
  | none => 0
  | some index => realization.coordinates alpha index

/-- A selected basis handle reads exactly the matching coordinate of `alpha`. -/
theorem handleExponent_basisHandle
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (index : Fin realization.rank) :
    realization.handleExponent alpha (realization.basisHandle index) =
      realization.coordinates alpha index := by
  simp [handleExponent, realization.basis_index_roundtrip]

/-- A certified non-basis handle has exponent zero. -/
theorem handleExponent_of_not_selected
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2)
    (notSelected : realization.basisIndex? handle = none) :
    realization.handleExponent alpha handle = 0 := by
  simp [handleExponent, notSelected]

/--
The basis-marked handle exponent is exactly the corresponding coefficient of
the canonical marked cycle.
-/
theorem markedCycle_coefficient_eq_handleExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2) :
    presentation.cycleHandleCoefficients
        (realization.markedCycle alpha) handle =
      realization.handleExponent alpha handle := by
  cases lookup : realization.basisIndex? handle with
  | none =>
      rw [realization.markedCycle_coefficient_of_not_selected
        alpha handle lookup]
      exact (realization.handleExponent_of_not_selected
        alpha handle lookup).symm
  | some index =>
      have handle_eq :
          handle = realization.basisHandle index :=
        realization.basis_index_sound handle index lookup
      subst handle
      rw [realization.markedCycle_coefficient_basisHandle]
      exact (realization.handleExponent_basisHandle alpha index).symm

/-- Read the basis exponent of one serialized link component. -/
noncomputable def componentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (component : ComponentSpec) : ℤ :=
  match presentation.topology.twoHandleIndex? component.componentId with
  | none => 0
  | some handle => realization.handleExponent alpha handle

/--
The component exponent used by the basis-marked evaluator is exactly the raw
cycle exponent of its canonical marked cycle.
-/
theorem componentExponent_eq_cycleComponentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (component : ComponentSpec) :
    realization.componentExponent alpha component =
      presentation.cycleComponentExponent
        (realization.markedCycle alpha) component := by
  unfold componentExponent
  unfold CanonicalPresentation.cycleComponentExponent
  cases lookup :
      presentation.topology.twoHandleIndex? component.componentId with
  | none =>
      rfl
  | some handle =>
      exact
        (realization.markedCycle_coefficient_eq_handleExponent
          alpha handle).symm

/-- Dotted one-handle components always receive exponent zero. -/
theorem dotted_componentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (component : ComponentSpec)
    (dotted : component.role = .dotted) :
    realization.componentExponent alpha component = 0 := by
  simp [componentExponent,
    presentation.topology.dotted_component_unindexed component dotted]

/-- A selected basis component reads its matching `H₂` coordinate. -/
theorem basis_componentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (index : Fin realization.rank) :
    realization.componentExponent alpha
        (presentation.topology.twoHandleComponent
          (realization.basisHandle index)) =
      realization.coordinates alpha index := by
  simp [componentExponent,
    presentation.topology.two_handle_index_roundtrip,
    handleExponent_basisHandle]

/--
A non-basis two-handle component receives exponent zero.

This is the formal cancellation-safety fact: a newly introduced cancellable
two-handle is harmless once the topology proof certifies that it is absent
from the selected homology basis.
-/
theorem nonbasis_componentExponent
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2)
    (notSelected : realization.basisIndex? handle = none) :
    realization.componentExponent alpha
        (presentation.topology.twoHandleComponent handle) = 0 := by
  simp [componentExponent,
    presentation.topology.two_handle_index_roundtrip,
    handleExponent, notSelected]

/-- The zero `H₂` class gives exponent zero on every component. -/
theorem componentExponent_zero
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (realization : H2BasisRealization presentation)
    (component : ComponentSpec) :
    realization.componentExponent 0 component = 0 := by
  unfold componentExponent handleExponent
  split
  · rfl
  · split <;> simp

end H2BasisRealization

/-- Component coefficient forced by one marked `H₂` class and sphere basis. -/
noncomputable def basisMarkedComponentWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (component : ComponentSpec)
    (simple : S) : K :=
  𝒞.premodular.quantumDimension simple *
    𝒞.premodular.toFusionCategoryData.automorphismScalarPower
      automorphism simple
      (realization.componentExponent alpha component)

/-- The basis-marked component weight is the canonical marked-cycle weight. -/
theorem basisMarkedComponentWeight_eq_cycleComponentWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (component : ComponentSpec)
    (simple : S) :
    basisMarkedComponentWeight
        𝒞 automorphism presentation realization alpha component simple =
      presentation.cycleComponentWeight
        𝒞 automorphism (realization.markedCycle alpha) component simple := by
  unfold basisMarkedComponentWeight
  unfold CanonicalPresentation.cycleComponentWeight
  rw [realization.componentExponent_eq_cycleComponentExponent]

/-- Product coefficient for one global simple labeling. -/
noncomputable def basisMarkedGlobalWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (labeling : presentation.GlobalLabeling (S := S)) : K :=
  ∏ index,
    basisMarkedComponentWeight 𝒞 automorphism presentation realization alpha
      (presentation.topology.formal.raw.components.get index)
      (labeling index)

/-- Every complete-label coefficient agrees with the canonical marked cycle. -/
theorem basisMarkedGlobalWeight_eq_cycleGlobalWeight
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (labeling : presentation.GlobalLabeling (S := S)) :
    basisMarkedGlobalWeight
        𝒞 automorphism presentation realization alpha labeling =
      presentation.cycleGlobalWeight
        𝒞 automorphism (realization.markedCycle alpha) labeling := by
  classical
  unfold basisMarkedGlobalWeight
  unfold CanonicalPresentation.cycleGlobalWeight
  apply Finset.prod_congr rfl
  intro index _
  exact basisMarkedComponentWeight_eq_cycleComponentWeight
    𝒞 automorphism presentation realization alpha
      (presentation.topology.formal.raw.components.get index)
      (labeling index)

/-- Formal basis-marked Kirby-colour sum. -/
noncomputable def basisMarkedLinearDiagram
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    LinearDiagram (R := K) (C := C) .unit .unit :=
  weightedSum
    (basisMarkedGlobalWeight 𝒞 automorphism presentation realization alpha)
    (presentation.termDiagram 𝒞)

/--
The complete basis-marked finite sum is definitionally tied to the raw-cycle
sum at the canonical marked cycle.
-/
theorem basisMarkedLinearDiagram_eq_cycleLinearDiagram
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    basisMarkedLinearDiagram
        𝒞 automorphism presentation realization alpha =
      presentation.cycleLinearDiagram
        𝒞 automorphism (realization.markedCycle alpha) := by
  unfold basisMarkedLinearDiagram
  unfold CanonicalPresentation.cycleLinearDiagram
  congr 1
  funext labeling
  exact basisMarkedGlobalWeight_eq_cycleGlobalWeight
    𝒞 automorphism presentation realization alpha labeling

/-- Raw scalar before handle normalization. -/
noncomputable def basisMarkedRawNumerator
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) : K :=
  𝒞.premodular.toFusionCategoryData.closedScalar
    (LinearDiagram.eval
      (basisMarkedLinearDiagram
        𝒞 automorphism presentation realization alpha))

/-- The raw basis-marked scalar equals its canonical marked-cycle scalar. -/
theorem basisMarkedRawNumerator_eq_cycleRawNumerator
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    basisMarkedRawNumerator
        𝒞 automorphism presentation realization alpha =
      presentation.cycleRawNumerator
        𝒞 automorphism (realization.markedCycle alpha) := by
  unfold basisMarkedRawNumerator
  unfold CanonicalPresentation.cycleRawNumerator
  rw [basisMarkedLinearDiagram_eq_cycleLinearDiagram]

/-- Normalization state of the basis-marked formula. -/
noncomputable def basisMarkedEvaluationState
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    EvaluationState (K := K) where
  counts := presentation.topology.counts
  rawNumerator :=
    basisMarkedRawNumerator 𝒞 automorphism presentation realization alpha

/--
The normalized value of one basis-marked presentation.

This is a function of an `H₂` class, not of a cycle representative.  It is
not yet named the final four-manifold invariant because basis-change and
Kirby-movie independence must still be proved.
-/
noncomputable def basisMarkedPresentationValue
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) : K :=
  (basisMarkedEvaluationState
    𝒞 automorphism presentation realization alpha).normalized
      (TwistedYetter.Kirby.CanonicalModularKirbyEvaluator.CanonicalPresentation.normalizationProfile
        𝒞)

/--
The corrected `H₂` formula is the raw cycle formula only at the canonical
basis-marked representative.  No claim is made for arbitrary homologous
cycles.
-/
theorem basisMarkedPresentationValue_eq_rawCycleColourEval
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (realization : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    basisMarkedPresentationValue
        𝒞 automorphism presentation realization alpha =
      presentation.rawCycleColourEval
        𝒞 automorphism (realization.markedCycle alpha) := by
  simp only [basisMarkedPresentationValue, basisMarkedEvaluationState,
    CanonicalPresentation.rawCycleColourEval,
    CanonicalPresentation.cycleEvaluationState,
    EvaluationState.normalized]
  rw [basisMarkedRawNumerator_eq_cycleRawNumerator]

/--
Two basis realizations that differ only by a finite reindexing.

Both the selected two-handle sphere and the coordinate of every `alpha` must
commute with the same equivalence.  This is stronger than merely asserting
that the two ranks agree.
-/
structure BasisReindexing
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    (left right : H2BasisRealization presentation) where
  indexEquiv : Fin left.rank ≃ Fin right.rank
  basisHandle_sound :
    (index : Fin left.rank) →
      right.basisHandle (indexEquiv index) =
        left.basisHandle index
  coordinates_sound :
    (alpha : presentation.topology.handleChain.SecondHomology) →
    (index : Fin left.rank) →
      right.coordinates alpha (indexEquiv index) =
        left.coordinates alpha index

namespace BasisReindexing

/-- The two proved partial inverses differ exactly by the basis reindexing. -/
theorem basisIndex?_eq_map
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    {left right : H2BasisRealization presentation}
    (reindexing : BasisReindexing left right)
    (handle : Fin presentation.topology.counts.h2) :
    right.basisIndex? handle =
      (left.basisIndex? handle).map reindexing.indexEquiv := by
  cases leftCase : left.basisIndex? handle with
  | none =>
      cases rightCase : right.basisIndex? handle with
      | none =>
          rfl
      | some rightIndex =>
          have handleRight :
              handle = right.basisHandle rightIndex :=
            right.basis_index_sound handle rightIndex rightCase
          have handleLeft :
              handle =
                left.basisHandle
                  (reindexing.indexEquiv.symm rightIndex) := by
            calc
              handle = right.basisHandle rightIndex := handleRight
              _ =
                  left.basisHandle
                    (reindexing.indexEquiv.symm rightIndex) := by
                simpa using
                  reindexing.basisHandle_sound
                    (reindexing.indexEquiv.symm rightIndex)
          have impossible :
              left.basisIndex? handle =
                some (reindexing.indexEquiv.symm rightIndex) := by
            rw [handleLeft]
            exact left.basis_index_roundtrip _
          rw [leftCase] at impossible
          contradiction
  | some leftIndex =>
      have handleLeft :
          handle = left.basisHandle leftIndex :=
        left.basis_index_sound handle leftIndex leftCase
      have handleRight :
          handle =
            right.basisHandle (reindexing.indexEquiv leftIndex) := by
        calc
          handle = left.basisHandle leftIndex := handleLeft
          _ =
              right.basisHandle
                (reindexing.indexEquiv leftIndex) :=
            (reindexing.basisHandle_sound leftIndex).symm
      rw [handleRight, right.basis_index_roundtrip]
      simp

/-- Reindexing a certified basis leaves every two-handle exponent unchanged. -/
theorem handleExponent_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    {left right : H2BasisRealization presentation}
    (reindexing : BasisReindexing left right)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (handle : Fin presentation.topology.counts.h2) :
    left.handleExponent alpha handle =
      right.handleExponent alpha handle := by
  unfold H2BasisRealization.handleExponent
  rw [reindexing.basisIndex?_eq_map handle]
  cases leftCase : left.basisIndex? handle with
  | none =>
      rfl
  | some index =>
      exact (reindexing.coordinates_sound alpha index).symm

/-- Reindexing leaves the exponent of every serialized component unchanged. -/
theorem componentExponent_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    {presentation : CanonicalPresentation manifold H2}
    {left right : H2BasisRealization presentation}
    (reindexing : BasisReindexing left right)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (component : ComponentSpec) :
    left.componentExponent alpha component =
      right.componentExponent alpha component := by
  unfold H2BasisRealization.componentExponent
  split
  · rfl
  · exact reindexing.handleExponent_eq alpha _

/-- Reindexing leaves every global-label coefficient unchanged. -/
theorem globalWeight_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {presentation : CanonicalPresentation manifold H2}
    {left right : H2BasisRealization presentation}
    (reindexing : BasisReindexing left right)
    (alpha : presentation.topology.handleChain.SecondHomology)
    (labeling : presentation.GlobalLabeling (S := S)) :
    basisMarkedGlobalWeight
        𝒞 automorphism presentation left alpha labeling =
      basisMarkedGlobalWeight
        𝒞 automorphism presentation right alpha labeling := by
  classical
  unfold basisMarkedGlobalWeight
  apply Finset.prod_congr rfl
  intro index _
  unfold basisMarkedComponentWeight
  rw [reindexing.componentExponent_eq]

/-- Reindexing leaves the complete formal Kirby-colour sum unchanged. -/
theorem linearDiagram_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {presentation : CanonicalPresentation manifold H2}
    {left right : H2BasisRealization presentation}
    (reindexing : BasisReindexing left right)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    basisMarkedLinearDiagram
        𝒞 automorphism presentation left alpha =
      basisMarkedLinearDiagram
        𝒞 automorphism presentation right alpha := by
  unfold basisMarkedLinearDiagram
  congr 1
  funext labeling
  exact reindexing.globalWeight_eq
    𝒞 automorphism alpha labeling

/-- The normalized basis-marked value is independent of basis ordering. -/
theorem presentationValue_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {presentation : CanonicalPresentation manifold H2}
    {left right : H2BasisRealization presentation}
    (reindexing : BasisReindexing left right)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    basisMarkedPresentationValue
        𝒞 automorphism presentation left alpha =
      basisMarkedPresentationValue
        𝒞 automorphism presentation right alpha := by
  have rawNumerator :
      basisMarkedRawNumerator
          𝒞 automorphism presentation left alpha =
        basisMarkedRawNumerator
          𝒞 automorphism presentation right alpha := by
    unfold basisMarkedRawNumerator
    rw [reindexing.linearDiagram_eq 𝒞 automorphism alpha]
  simp only [basisMarkedPresentationValue, basisMarkedEvaluationState,
    EvaluationState.normalized]
  rw [rawNumerator]

end BasisReindexing

/--
The exact graphical obligation for changing the selected sphere basis.

The hard mathematical content is visible: for every `alpha`, produce a proof
term in the closed tensor-automorphism coupon calculus connecting the two
finite sums.  No scalar equality is accepted as input.
-/
structure BasisChangeGraphicalRealization
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (left right : H2BasisRealization presentation) where
  calculate :
    (alpha : presentation.topology.handleChain.SecondHomology) →
      FusionLinearGeneratedCalculation
        𝒞.premodular.toFusionCategoryData automorphism
        (basisMarkedLinearDiagram
          𝒞 automorphism presentation left alpha)
        (basisMarkedLinearDiagram
          𝒞 automorphism presentation right alpha)

namespace BasisChangeGraphicalRealization

/-- A graphical basis-change calculation implies equality of normalized values. -/
theorem presentationValue_eq
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2)
    (left right : H2BasisRealization presentation)
    (realization :
      BasisChangeGraphicalRealization
        𝒞 automorphism presentation left right)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    basisMarkedPresentationValue
        𝒞 automorphism presentation left alpha =
      basisMarkedPresentationValue
        𝒞 automorphism presentation right alpha := by
  have linearEvaluation :=
    (realization.calculate alpha).eval_eq
  have rawNumerator :
      basisMarkedRawNumerator
          𝒞 automorphism presentation left alpha =
        basisMarkedRawNumerator
          𝒞 automorphism presentation right alpha :=
    congrArg
      𝒞.premodular.toFusionCategoryData.closedScalar
      linearEvaluation
  simp only [basisMarkedPresentationValue, basisMarkedEvaluationState,
    EvaluationState.normalized]
  rw [rawNumerator]

end BasisChangeGraphicalRealization

/--
A selected sphere basis together with graphical proofs comparing it to every
other certified sphere basis.

The field contains calculations, not the desired scalar equality.  It is the
remaining basis-independence proof object that must be constructed from
handle slides and coupon motion.
-/
structure BasisIndependenceProof
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    (presentation : CanonicalPresentation manifold H2) where
  selected : H2BasisRealization presentation
  compare :
    (other : H2BasisRealization presentation) →
      BasisChangeGraphicalRealization
        𝒞 automorphism presentation selected other

namespace BasisIndependenceProof

/--
The corrected `H₂`-level evaluator for one presentation.

The public argument is an actual handle-chain second-homology class.
-/
noncomputable def EvalC
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {presentation : CanonicalPresentation manifold H2}
    (proof : BasisIndependenceProof 𝒞 automorphism presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) : K :=
  basisMarkedPresentationValue
    𝒞 automorphism presentation proof.selected alpha

/-- The selected basis is immaterial among all certified sphere bases. -/
theorem EvalC_eq_basisMarkedPresentationValue
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {presentation : CanonicalPresentation manifold H2}
    (proof : BasisIndependenceProof 𝒞 automorphism presentation)
    (other : H2BasisRealization presentation)
    (alpha : presentation.topology.handleChain.SecondHomology) :
    proof.EvalC 𝒞 automorphism alpha =
      basisMarkedPresentationValue
        𝒞 automorphism presentation other alpha := by
  exact
    (proof.compare other).presentationValue_eq
      𝒞 automorphism presentation proof.selected other alpha

/--
The evaluator is a function on `H₂` itself.

No cycle representative occurs in this statement.  Equality of its inputs is
ordinary equality in the homology quotient.
-/
theorem EvalC_congr
    {manifold : ClosedConnectedSmoothOrientedFourManifoldInput}
    {H2 : Type uH} [AddCommGroup H2]
    (𝒞 : ModularCategory (K := K) (C := C) (S := S))
    (automorphism : TensorIdentityAutomorphism C)
    {presentation : CanonicalPresentation manifold H2}
    (proof : BasisIndependenceProof 𝒞 automorphism presentation)
    (alpha beta :
      presentation.topology.handleChain.SecondHomology)
    (equality : alpha = beta) :
    proof.EvalC 𝒞 automorphism alpha =
      proof.EvalC 𝒞 automorphism beta := by
  exact congrArg (proof.EvalC 𝒞 automorphism) equality

end BasisIndependenceProof

end CanonicalPresentation

end TwistedYetter.Kirby.H2BasisMarkedEvaluator
