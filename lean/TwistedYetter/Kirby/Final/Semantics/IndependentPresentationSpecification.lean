import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.List.Defs

/-!
# Independent human specification of a special Kirby diagram

This file is normative.  It was written from the human Kirby-diagram
definition without importing or inspecting this repository's presentation,
move, evaluator, Sage, or compatibility implementations.

A `SpecialKirbyDiagram` is deliberately not a complete handle presentation.
In particular, it does not contain attaching spheres for 3-handles.  It
contains:

* a dotted unlink encoding primal 1-handles;
* a framed link encoding primal 2-handles;
* a chosen simultaneous family of dotted spanning disks;
* the complete finite puncture and bunching data at those disks;
* a certificate that the boundary after the 0-, 1-, and 2-handles is
  `#^hThree (S¹ × S²)`.
* the coordinate-free integral handle boundary maps
  `C₃ → C₂ → C₁`, including their geometric realization certificates.

The last certificate is exactly what permits closure by `hThree` 3-handles
and one 4-handle without storing their attaching spheres.

No component orientation, category, character, homology class, label,
coupon, projector, evaluation, or scalar normalization occurs here.
-/

namespace TwistedYetter.Kirby.Final.IndependentPresentationSpecification

open CategoryTheory

universe uKnot uFramed uDisk uPoint uBunching uThreeManifold

/--
The geometric/topological primitives that this project does not reconstruct.

These names have their literal human meanings.  This boundary contains no
category-theoretic or evaluator data.
-/
structure KirbyGeometrySemantics where
  KnotInS3 : Type uKnot
  FramedKnotInS3 : Type uFramed
  EmbeddedDiskInS3 : Type uDisk
  IntersectionPoint : Type uPoint
  BunchingDatum : Type uBunching
  ClosedThreeManifold : Type uThreeManifold

  underlyingKnot : FramedKnotInS3 → KnotInS3
  diskBoundary : EmbeddedDiskInS3 → KnotInS3

  pairwiseDisjointKnots : List KnotInS3 → Prop
  pairwiseDisjointDisks : List EmbeddedDiskInS3 → Prop
  isUnlink : List KnotInS3 → Prop

  isTransverseIntersection :
    IntersectionPoint →
      EmbeddedDiskInS3 →
      FramedKnotInS3 →
      Prop

  bunchesExactly :
    BunchingDatum →
      List (IntersectionPoint × ℕ) →
      Prop

  boundaryAfterZeroOneTwoHandles :
    {nOne nTwo : ℕ} →
      (Fin nOne → KnotInS3) →
      (Fin nTwo → FramedKnotInS3) →
      ClosedThreeManifold

  connectedSumS1TimesS2 :
    ℕ → ClosedThreeManifold

  orientationPreservingDiffeomorphic :
    ClosedThreeManifold →
      ClosedThreeManifold →
      Prop

/--
One occurrence of an ordinary framed component through one chosen dotted
spanning disk.

There is intentionally no sign here.  Intersection signs are introduced
only after choosing the handle-chain coordinate orientations in the separate
H₂ semantics.
-/
structure DottedPuncture
    (geometry : KirbyGeometrySemantics)
    (nTwo : ℕ) where
  point : geometry.IntersectionPoint
  ordinaryComponent : Fin nTwo

/--
All evaluation-relevant geometry at one dotted component.

`punctures` is an ordered finite list.  The soundness and completeness fields
state that it is exactly the geometric intersection set, with no omitted or
foreign puncture.  `bunching` fixes the finite tensor-word reading needed by
the later unit-only cut.
-/
structure DottedSpanningDiskData
    (geometry : KirbyGeometrySemantics)
    {nOne nTwo : ℕ}
    (dotted : Fin nOne → geometry.KnotInS3)
    (ordinary : Fin nTwo → geometry.FramedKnotInS3)
    (dottedComponent : Fin nOne) where
  disk : geometry.EmbeddedDiskInS3
  boundary_is_dotted :
    geometry.diskBoundary disk = dotted dottedComponent

  punctures :
    List (DottedPuncture geometry nTwo)
  punctures_no_duplicates :
    punctures.Nodup

  punctures_sound :
    ∀ puncture ∈ punctures,
      geometry.isTransverseIntersection
        puncture.point
        disk
        (ordinary puncture.ordinaryComponent)

  punctures_complete :
    ∀ (point : geometry.IntersectionPoint)
      (component : Fin nTwo),
      geometry.isTransverseIntersection
        point
        disk
        (ordinary component) →
      ∃ puncture ∈ punctures,
        puncture.point = point ∧
          puncture.ordinaryComponent = component

  bunching : geometry.BunchingDatum
  bunching_exact :
    geometry.bunchesExactly
      bunching
      (punctures.map fun puncture =>
        (puncture.point, puncture.ordinaryComponent.val))

/--
The complete independent semantic input called a "special Kirby diagram" in
this project.

The unique primal 0-handle and unique primal 4-handle are part of the word
"special" and therefore are not mutable fields.  The actual 3-handle
attaching spheres are intentionally absent.
-/
structure SpecialKirbyDiagramBase
    (geometry : KirbyGeometrySemantics) where
  hOne : ℕ
  hTwo : ℕ
  hThree : ℕ

  dotted :
    Fin hOne → geometry.KnotInS3
  ordinary :
    Fin hTwo → geometry.FramedKnotInS3

  all_components_disjoint :
    geometry.pairwiseDisjointKnots
      (List.ofFn dotted ++
        List.ofFn (fun j => geometry.underlyingKnot (ordinary j)))

  dotted_is_unlink :
    geometry.isUnlink (List.ofFn dotted)

  dottedDisk :
    (i : Fin hOne) →
      DottedSpanningDiskData geometry dotted ordinary i

  dotted_disks_pairwise_disjoint :
    geometry.pairwiseDisjointDisks
      (List.ofFn fun i => (dottedDisk i).disk)

  closing_boundary_certificate :
    geometry.orientationPreservingDiffeomorphic
      (geometry.boundaryAfterZeroOneTwoHandles dotted ordinary)
      (geometry.connectedSumS1TimesS2 hThree)

/--
The mathematical meaning of the boundary certificate on the geometric base.

It says only that the 0/1/2-handlebody can be closed by `hThree` 3-handles and
one 4-handle.  It contains no evaluator equality.
-/
def HasStandardClosedCompletion
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagramBase geometry) : Prop :=
  geometry.orientationPreservingDiffeomorphic
    (geometry.boundaryAfterZeroOneTwoHandles
      diagram.dotted
      diagram.ordinary)
    (geometry.connectedSumS1TimesS2 diagram.hThree)

theorem hasStandardClosedCompletion
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagramBase geometry) :
    HasStandardClosedCompletion diagram :=
  diagram.closing_boundary_certificate

/--
Topology boundary T-H₂.

The map `boundaryTwo` is the coordinate-free incidence homomorphism obtained
from the framed 2-handle components and the complete transverse puncture data
on the chosen dotted spanning disks.

After choosing orientations of the relevant rank-one handle orientation
lines, its `(i,j)` matrix entry is the signed intersection number
`ordinary j · dottedDisk i`.  Reversing a chosen orientation changes the
corresponding row or column sign and does not change this coordinate-free
map.

This proposition contains no category or evaluator equality.
-/
axiom BoundaryTwoMatchesDottedPunctures
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagramBase geometry)
    (C₁ C₂ : ModuleCat ℤ)
    (boundaryTwo : C₂ ⟶ C₁) :
    Prop

/--
Topology boundary T-H₃.

The map `boundaryThree` is the coordinate-free handle boundary homomorphism
induced by the standard system of `diagram.hThree` closing 3-handles under
`diagram.closing_boundary_certificate`.

It is not an arbitrary homomorphism supplied independently of the closing
topology.  Full attaching-sphere embeddings are intentionally not public
fields.

This proposition contains no category or evaluator equality.
-/
axiom BoundaryThreeMatchesClosingSystem
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagramBase geometry)
    (C₂ C₃ : ModuleCat ℤ)
    (boundaryThree : C₃ ⟶ C₂) :
    Prop

/--
The coordinate-free integral handle-boundary package.

`C₁`, `C₂`, and `C₃` are finite free abelian groups of ranks `hOne`,
`hTwo`, and `hThree`.  The displayed equivalences assert only existence of
coordinate charts; no chart and hence no component orientation is part of
the diagram.
-/
structure SpecialKirbyHandleBoundaryData
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagramBase geometry) where
  C₁ : ModuleCat ℤ
  C₂ : ModuleCat ℤ
  C₃ : ModuleCat ℤ

  C₁_has_handle_rank :
    Nonempty (C₁ ≅ ModuleCat.of ℤ (Fin diagram.hOne → ℤ))
  C₂_has_handle_rank :
    Nonempty (C₂ ≅ ModuleCat.of ℤ (Fin diagram.hTwo → ℤ))
  C₃_has_handle_rank :
    Nonempty (C₃ ≅ ModuleCat.of ℤ (Fin diagram.hThree → ℤ))

  boundaryTwo : C₂ ⟶ C₁
  boundaryThree : C₃ ⟶ C₂

  boundary_squared_zero :
    boundaryThree ≫ boundaryTwo = 0

  boundaryTwo_is_geometric_incidence :
    BoundaryTwoMatchesDottedPunctures
      diagram C₁ C₂ boundaryTwo

  boundaryThree_is_closing_boundary :
    BoundaryThreeMatchesClosingSystem
      diagram C₂ C₃ boundaryThree

/--
The complete project-local meaning of `SpecialKirbyDiagram`.

It consists of the geometric dotted/framed diagram and its chosen dotted
disks, together with the coordinate-free `∂₃` and `∂₂` package certified to
come from that same geometry and closing system.
-/
structure SpecialKirbyDiagram
    (geometry : KirbyGeometrySemantics) where
  geometric : SpecialKirbyDiagramBase geometry
  handleBoundary : SpecialKirbyHandleBoundaryData geometric

/-- The chain condition, exposed under its mathematical name for audits. -/
theorem boundary_of_boundary_is_zero
    {geometry : KirbyGeometrySemantics}
    (diagram : SpecialKirbyDiagram geometry) :
    diagram.handleBoundary.boundaryThree ≫
      diagram.handleBoundary.boundaryTwo = 0 :=
  diagram.handleBoundary.boundary_squared_zero

end TwistedYetter.Kirby.Final.IndependentPresentationSpecification
