import TwistedYetter.Kirby.Final.Semantics.Independent.Evaluator

/-!
# Finite-sum multiplicativity for split raw evaluators

This file contains no connected-sum topology.  It isolates the final finite
algebra step in the marked connected-sum proof: once target labelings are
identified with pairs of source labelings and the summand is proved to factor
pointwise, the complete raw sum factors.
-/

namespace TwistedYetter.StableNoGo

open CategoryTheory
open CategoryTheory.MonoidalCategory
open TwistedYetter.Semantics.Independent

universe uK

noncomputable section

variable {K : Type uK} [Field K] [IsAlgClosed K] [CharZero K]

namespace FiniteMorphismTrace

variable {C : Type*} [Category C]

/-- Equal finite traces have heterogeneously equal total composites. -/
theorem composeAll_heq_of_eq
    {eventCount : ℕ}
    {left right : FiniteMorphismTrace C eventCount}
    (equality : left = right) : HEq left.composeAll right.composeAll := by
  cases equality
  rfl

/-- Retain a fixed prefix of events from a finite morphism trace. -/
def takePrefix
    {prefixLength suffix : ℕ}
    (trace : FiniteMorphismTrace C (prefixLength + suffix)) :
    FiniteMorphismTrace C prefixLength where
  object i :=
    trace.object ⟨i.1, by
      have := i.2
      omega⟩
  edge i :=
    trace.edge ⟨i.1, by
      have := i.2
      omega⟩

theorem takePrefix_composePrefix
    {prefixLength suffix : ℕ}
    (trace : FiniteMorphismTrace C (prefixLength + suffix))
    (k : ℕ) (bound : k ≤ prefixLength) :
    (takePrefix trace).composePrefix k bound =
      trace.composePrefix k (by omega) := by
  induction k with
  | zero => rfl
  | succ k inductionHypothesis =>
      simp only [FiniteMorphismTrace.composePrefix]
      rw [inductionHypothesis]
      rfl

theorem takePrefix_composeAll
    {prefixLength suffix : ℕ}
    (trace : FiniteMorphismTrace C (prefixLength + suffix)) :
    (takePrefix trace).composeAll =
      trace.composePrefix prefixLength (by omega) := by
  exact takePrefix_composePrefix trace prefixLength _

/-- Drop a fixed prefix of events from a finite morphism trace. -/
def dropPrefix
    {prefixLength suffix : ℕ}
    (trace : FiniteMorphismTrace C (prefixLength + suffix)) :
    FiniteMorphismTrace C suffix where
  object i :=
    trace.object ⟨prefixLength + i.1, by
      have := i.2
      omega⟩
  edge i :=
    trace.edge ⟨prefixLength + i.1, by
      have := i.2
      omega⟩

/-- Remove the final event of a nonempty finite morphism trace. -/
def dropLast
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C (eventCount + 1)) :
    FiniteMorphismTrace C eventCount where
  object i :=
    trace.object ⟨i.1, by
      have := i.2
      omega⟩
  edge i :=
    trace.edge ⟨i.1, by
      have := i.2
      omega⟩

theorem dropLast_composePrefix
    {eventCount : ℕ}
    (trace : FiniteMorphismTrace C (eventCount + 1))
    (k : ℕ) (bound : k ≤ eventCount) :
    (dropLast trace).composePrefix k bound =
      trace.composePrefix k (by omega) := by
  induction k with
  | zero => rfl
  | succ k inductionHypothesis =>
      simp only [FiniteMorphismTrace.composePrefix]
      rw [inductionHypothesis]
      rfl

/-- Composition of a finite trace factors at any chosen event boundary. -/
theorem composeAll_eq_prefix_comp_dropPrefix
    {prefixLength suffix : ℕ}
    (trace : FiniteMorphismTrace C (prefixLength + suffix)) :
    trace.composeAll =
      trace.composePrefix prefixLength (by omega) ≫
        (dropPrefix trace).composeAll := by
  induction suffix with
  | zero =>
      simp [FiniteMorphismTrace.composeAll,
        FiniteMorphismTrace.composePrefix, dropPrefix]
  | succ suffix inductionHypothesis =>
      let initialTrace : FiniteMorphismTrace C (prefixLength + suffix) :=
        dropLast trace
      have prefixEquality :
          initialTrace.composePrefix prefixLength (by omega) =
            trace.composePrefix prefixLength (by omega) := by
        exact dropLast_composePrefix trace _ _
      have initialTotalEquality :
          initialTrace.composeAll =
            trace.composePrefix (prefixLength + suffix) (by omega) := by
        exact dropLast_composePrefix trace _ _
      have suffixEquality :
          (dropPrefix initialTrace).composeAll =
            (dropPrefix trace).composePrefix suffix (by omega) := by
        change
          (dropLast (dropPrefix trace)).composePrefix suffix _ = _
        exact dropLast_composePrefix (dropPrefix trace) _ _
      change
        trace.composePrefix (prefixLength + suffix) (by omega) ≫
            trace.edge ⟨prefixLength + suffix, by omega⟩ = _
      rw [← initialTotalEquality]
      rw [inductionHypothesis initialTrace]
      rw [prefixEquality]
      rw [suffixEquality]
      simp only [FiniteMorphismTrace.composeAll,
        FiniteMorphismTrace.composePrefix]
      simp [initialTrace, dropPrefix, dropLast, Category.assoc]

end FiniteMorphismTrace

/-- Canonical evaluation sends composition of closed ribbon morphisms to scalar multiplication. -/
theorem canonicalRibbonGraphicalEvaluation_comp
    (𝒞 : BundledPremodularCategory K)
    (left right : 𝟙_ 𝒞.C ⟶ 𝟙_ 𝒞.C) :
    canonicalRibbonGraphicalEvaluation 𝒞 (.morphism (left ≫ right)) =
      canonicalRibbonGraphicalEvaluation 𝒞 (.morphism left) *
        canonicalRibbonGraphicalEvaluation 𝒞 (.morphism right) := by
  exact 𝒞.closedScalar_comp left right

/-- One summand in the raw role-aware evaluator. -/
noncomputable def rawEvaluatorSummand
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (coefficients : ThamTwoHandleCoefficients diagram)
    (labeling : TwoHandleLabeling 𝒞η.category diagram) : K :=
  ordinaryKirbyWeight 𝒞η.category labeling *
    characterWeight 𝒞η labeling coefficients *
    canonicalRibbonGraphicalEvaluation 𝒞η.category
      (canonicalRoleAwareGraphCompiler
        𝒞η diagram presentation labeling coefficients)

theorem rawCoefficientSum_eq_sum_rawEvaluatorSummand
    (𝒞η : TwistedPremodularCategory K)
    (diagram : SpecialKirbyDiagram)
    (presentation : DottedCutPresentation diagram)
    (coefficients : ThamTwoHandleCoefficients diagram) :
    rawCoefficientSum 𝒞η diagram presentation coefficients =
      ∑ labeling, rawEvaluatorSummand
        𝒞η diagram presentation coefficients labeling := by
  rfl

/--
The raw finite sum is multiplicative once the split-labeling equivalence and
the pointwise factorization of every summand have been established.
-/
theorem rawCoefficientSum_mul_of_labelingEquiv
    (𝒞η : TwistedPremodularCategory K)
    (leftDiagram rightDiagram targetDiagram : SpecialKirbyDiagram)
    (leftPresentation : DottedCutPresentation leftDiagram)
    (rightPresentation : DottedCutPresentation rightDiagram)
    (targetPresentation : DottedCutPresentation targetDiagram)
    (leftCoefficients : ThamTwoHandleCoefficients leftDiagram)
    (rightCoefficients : ThamTwoHandleCoefficients rightDiagram)
    (targetCoefficients : ThamTwoHandleCoefficients targetDiagram)
    (labelingEquiv :
      TwoHandleLabeling 𝒞η.category targetDiagram ≃
        TwoHandleLabeling 𝒞η.category leftDiagram ×
          TwoHandleLabeling 𝒞η.category rightDiagram)
    (summandFactors :
      ∀ targetLabeling,
        rawEvaluatorSummand 𝒞η targetDiagram targetPresentation
            targetCoefficients targetLabeling =
          rawEvaluatorSummand 𝒞η leftDiagram leftPresentation
              leftCoefficients (labelingEquiv targetLabeling).1 *
            rawEvaluatorSummand 𝒞η rightDiagram rightPresentation
              rightCoefficients (labelingEquiv targetLabeling).2) :
    rawCoefficientSum 𝒞η targetDiagram targetPresentation targetCoefficients =
      rawCoefficientSum 𝒞η leftDiagram leftPresentation leftCoefficients *
        rawCoefficientSum 𝒞η rightDiagram rightPresentation rightCoefficients := by
  rw [rawCoefficientSum_eq_sum_rawEvaluatorSummand]
  rw [Fintype.sum_equiv labelingEquiv
    (rawEvaluatorSummand 𝒞η targetDiagram targetPresentation
      targetCoefficients)
    (fun labelings =>
      rawEvaluatorSummand 𝒞η leftDiagram leftPresentation
          leftCoefficients labelings.1 *
        rawEvaluatorSummand 𝒞η rightDiagram rightPresentation
          rightCoefficients labelings.2)
    summandFactors]
  rw [Fintype.sum_prod_type]
  rw [← Fintype.sum_mul_sum]
  rfl

end

end TwistedYetter.StableNoGo
