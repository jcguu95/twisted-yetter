import TwistedYetter.Kirby.DottedBoundaryGeometry

/-!
# Literature boundary for standard dotted-disk geometry

This module isolates the topology fact used to turn a standard dotted Kirby
presentation into the category-neutral `GeometrySystem` consumed by the
kernel-checked modular calculation.

The imported fact has three separately visible parts:

1. every dotted one-handle component has its standard oriented spanning disk,
   whose transverse punctures record the signed passages of two-handle
   attaching circles;
2. after turning the handle decomposition upside down, those signed
   incidences are exactly the corresponding degree-three boundary row in the
   handle chain complex; and
3. framed ribbon isotopy exposes the dotted disk as the open encircling window
   used by the local modular-vacuum calculation.

This is deliberately a non-executable literature boundary. Lean is not asked
to recover spanning disks or punctures from pixels or raw planar coordinates.
Instead, the final topology theory ranges only over the certified standard
dotted presentations defined below. The accepted existence and Kirby--Cerf
completeness of that domain remain visible in the final topology assumptions.
No category, evaluator, or equality of scalar values is stored here. All
finite-label calculations and descent to `H₂` occur after this boundary.

Source boundary:

* Gompf--Stipsicz, Section 5.1 (dotted-circle notation) and Section 4.2
  (handle-chain incidence);
* Tham, Definition 5.11, the `k = 3` case, interpreted under the upside-down
  convention fixed in this repository;
* Shum's coherence theorem for the framed ribbon isotopy used to expose the
  open dotted-encircling window.
-/

namespace TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry

open TwistedYetter.Kirby.CanonicalModularKirbyEvaluator
open TwistedYetter.Kirby.DottedBoundaryGeometry
open TwistedYetter.Kirby.KirbyCompleteness

universe uH

/-- Exact denominator of the imported standard dotted-geometry fact. -/
inductive AssumptionClass where
  | spanningDiskPunctures
  | dualBoundaryIncidence
  | canonicalTraceFactorization
  deriving Repr, BEq, DecidableEq

/-- Machine-visible list of the three accepted topology facts. -/
def requiredAssumptionClasses : List AssumptionClass :=
  [
    .spanningDiskPunctures,
    .dualBoundaryIncidence,
    .canonicalTraceFactorization
  ]

theorem required_assumption_class_count :
    requiredAssumptionClasses.length = 3 := by
  rfl

theorem required_assumption_classes_unique :
    requiredAssumptionClasses.Nodup := by
  decide

/-- Stable repository references for the imported topology fact. -/
def sourceRefs : List String :=
  [
    "ref:gompf-stipsicz-4-manifolds-kirby-calculus",
    "ref:tham-extended-crane-yetter-2021",
    "ref:shum-tortile-1994"
  ]

/-- Human-reviewable exact scope of the imported fact. -/
def exactImportedScope : String :=
  "For every canonical standard dotted Kirby presentation, choose the "
    ++ "standard oriented spanning disks. Their signed two-handle punctures "
    ++ "give the upside-down degree-three boundary rows, and framed ribbon "
    ++ "isotopy factors the canonical trace through the corresponding open "
    ++ "dotted-encircling windows."

/-- Explicit guard against interpreting the topology input as the result. -/
def sourceScopeCaveat : String :=
  "The certification does not supply a modular category, an evaluator, a scalar "
    ++ "equality, representative independence, local-move invariance, or a "
    ++ "four-manifold invariant. It does not parse raw diagram pixels or "
    ++ "infer hidden three-dimensional geometry."

/--
One canonical presentation certified as standard dotted Kirby geometry.

The certificate is category-neutral. Its `incidence_sound` fields
identify actual handle-chain rows, while its factorization fields contain
only generated framed-isotopy terms. The modular evaluation and homological
descent are proved downstream.
-/
structure StandardDottedCanonicalPresentation
    (manifold : ClosedConnectedSmoothOrientedFourManifoldInput)
    (H2 : Type uH) [AddCommGroup H2] where
  canonicalPresentation : CanonicalPresentation manifold H2
  dottedGeometry : GeometrySystem canonicalPresentation

end TwistedYetter.Kirby.LiteratureBackedDottedBoundaryGeometry
