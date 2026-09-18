/- The filled region of a finite vertex set is bounded: a point far from the drawing of that set
lies in a face avoiding it, because the face of a point off the drawing has diameter at most the
uniform face bound of the periodic plane graph. -/
import UCPlanar.Support.TopoClusterFace
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

/-- **The filled region of a finite vertex set is bounded.**  Beyond the drawing of that set by
the face diameter, a point off the drawing lies in a face all of whose incident vertices are too
far to belong to the set, and the drawing itself has empty interior. -/
theorem isBounded_clusterRegion_of_finite (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    (hN : N.Finite) : Bornology.IsBounded (Q.embedding.clusterRegion N) := by
  classical
  obtain ⟨R, hR⟩ := Q.face_diameter
  obtain ⟨K₀, hK₀⟩ := (hN.image Q.embedding.pos).isBounded.subset_closedBall (0 : UCPlanar.Plane)
  refine (Metric.isBounded_closedBall (x := (0 : UCPlanar.Plane)) (r := K₀ + R)).subset ?_
  by_contra hsub
  rw [Set.not_subset] at hsub
  obtain ⟨p, hp, hpout⟩ := hsub
  have hfar : K₀ + R < dist p (0 : UCPlanar.Plane) :=
    lt_of_not_ge (fun h => hpout (Metric.mem_closedBall.mpr h))
  have hopen : IsOpen (Q.embedding.clusterRegion N ∩
      {q : UCPlanar.Plane | K₀ + R < dist q (0 : UCPlanar.Plane)}) :=
    (isOpen_clusterRegion Q.embedding N).inter
      (isOpen_lt continuous_const (continuous_id.dist continuous_const))
  obtain ⟨q, ⟨hq1, hq2⟩, hqt⟩ := exists_notMem_trace Q hopen ⟨p, hp, hfar⟩
  have hF : Q.embedding.IsFace (connectedComponentIn Q.embedding.traceᶜ q) := ⟨q, hqt, rfl⟩
  have hqF : q ∈ connectedComponentIn Q.embedding.traceᶜ q := mem_connectedComponentIn hqt
  have havoid : connectedComponentIn Q.embedding.traceᶜ q ∈ Q.embedding.facesAvoiding N := by
    refine ⟨hF, ?_⟩
    intro y hinc hyN
    have hball : closure (connectedComponentIn Q.embedding.traceᶜ q) ⊆ Metric.closedBall q R :=
      closure_minimal (fun z hz => Metric.mem_closedBall.mpr
        (by rw [dist_comm]; exact hR _ hF q hqF z hz)) Metric.isClosed_closedBall
    have h1 : dist q (Q.embedding.pos y) ≤ R := by
      rw [dist_comm]
      exact Metric.mem_closedBall.mp (hball (frontier_subset_closure hinc))
    have h2 : dist (Q.embedding.pos y) (0 : UCPlanar.Plane) ≤ K₀ :=
      Metric.mem_closedBall.mp (hK₀ ⟨y, hyN, rfl⟩)
    have h3 := dist_triangle q (Q.embedding.pos y) (0 : UCPlanar.Plane)
    have h4 : K₀ + R < dist q (0 : UCPlanar.Plane) := hq2
    linarith
  exact hq1 (subset_closure (Set.mem_biUnion havoid hqF))

end UCPlanar.Support
