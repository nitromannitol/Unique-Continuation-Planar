/- The boundary cycle theorem for polygonal plane embeddings. -/
import UCPlanar.Support.TopoPolyConn
import Mathlib

open Set
open scoped Classical
open scoped Graph

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- The drawing of a walk contains the drawing of each edge it uses. -/
theorem edgesTrace_walkEdges_subset (E : UCPlanar.PlaneEmbedding G) {x y : V} (γ : G.Walk x y) :
    E.edgesTrace {g | g ∈ γ.edges} ⊆ E.walkTrace γ := by
  induction γ with
  | nil =>
    intro q hq
    simp only [UCPlanar.PlaneEmbedding.edgesTrace, SimpleGraph.Walk.edges_nil,
      List.not_mem_nil, Set.mem_setOf_eq, Set.iUnion_of_empty, Set.iUnion_empty] at hq
    exact hq.elim
  | @cons a b c h tail ih =>
    intro q hq
    simp only [UCPlanar.PlaneEmbedding.edgesTrace, Set.mem_iUnion, Set.mem_setOf_eq,
      SimpleGraph.Walk.edges_cons, List.mem_cons, exists_prop] at hq
    obtain ⟨g, hg, hqg⟩ := hq
    rcases hg with rfl | hg
    · refine Or.inl ?_
      rw [← arcOf_eq E h]
      exact hqg
    · exact Or.inr (ih (Set.mem_biUnion hg hqg))

/-- **The drawing of a walk of positive length is the drawing of its edges.** -/
theorem walkTrace_eq_edgesTrace (E : UCPlanar.PlaneEmbedding G) {x y : V} (γ : G.Walk x y)
    (hlen : γ.length ≠ 0) : E.walkTrace γ = E.edgesTrace {g | g ∈ γ.edges} :=
  Set.Subset.antisymm
    (walkTrace_subset_edgesTrace_of_edges E γ (fun _ he => he) hlen)
    (edgesTrace_walkEdges_subset E γ)

/-- The point set of a list of edges is the transported drawing of that list. -/
theorem edgesCover_eq (E : UCPlanar.PlaneEmbedding G) {W : List (Sym2 V)}
    (hW : ∀ g ∈ W, g ∈ G.edgeSet) :
    Graph.edgesCover (edgeDrawing E) W = planeHomeo '' E.edgesTrace {g | g ∈ W} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro q hq
    obtain ⟨g, hg, hqg⟩ := Graph.mem_edgesCover_iff.mp hq
    rw [edgeArc_edgeDrawing E (hW g hg)] at hqg
    obtain ⟨w, hw, rfl⟩ := hqg
    exact ⟨w, Set.mem_biUnion hg hw, rfl⟩
  · rintro q ⟨w, hw, rfl⟩
    simp only [UCPlanar.PlaneEmbedding.edgesTrace, Set.mem_iUnion, Set.mem_setOf_eq,
      exists_prop] at hw
    obtain ⟨g, hg, hwg⟩ := hw
    refine Graph.mem_edgesCover hg ?_
    rw [edgeArc_edgeDrawing E (hW g hg)]
    exact ⟨w, hwg, rfl⟩

/-- Separation from infinity transports back from the Euclidean plane. -/
theorem mem_insideOf_of_image {S : Set UCPlanar.Plane} {q : UCPlanar.Plane}
    (h : planeHomeo q ∈ Schoenflies.inside (planeHomeo '' S)) : q ∈ insideOf S := by
  rw [← insideOf_eq_inside, ← image_insideOf planeHomeo S] at h
  obtain ⟨y, hy, hyq⟩ := h
  rwa [planeHomeo.injective hyq] at hy

/-- Separation from infinity transports to the Euclidean plane. -/
theorem mem_image_inside {S : Set UCPlanar.Plane} {q : UCPlanar.Plane} (h : q ∈ insideOf S) :
    planeHomeo q ∈ Schoenflies.inside (planeHomeo '' S) := by
  rw [← insideOf_eq_inside, ← image_insideOf planeHomeo S]
  exact Set.mem_image_of_mem _ h

/-- **The two connected base case of the boundary cycle theorem, for a polygonal embedding.**
The edges of the set draw a finite two connected polygonal plane graph; the point they separate
from infinity lies in a bounded face of it, so the polygonal face cycle theorem encloses it by a
cycle, which reads back as a cycle of the graph. -/
theorem twoConnectedBoundaryCycles_of_polygonal (E : UCPlanar.PlaneEmbedding G)
    (hpoly : E.IsPolygonalDrawing) : E.TwoConnectedBoundaryCycles := by
  intro T hT hdeg hsplit p hp
  classical
  obtain ⟨e₀, he₀⟩ := nonempty_of_separating E hp
  set H := edgeGraph E (↑T : Set (Sym2 V)) with hHdef
  haveI : H.Finite := finite_edgeGraph E T.finite_toSet
  have hdraw : Graph.IsDrawing H (edgeDrawing E) := isDrawing_edgeGraph E _
  have h2 : H.IsTwoConnected := isTwoConnected_edgeGraph E hT hdeg hsplit he₀
  have hpoint : Graph.pointSet H (edgeDrawing E) = planeHomeo '' E.edgesTrace ↑T :=
    pointSet_edgeGraph E hT
  have hins : planeHomeo p ∈ Schoenflies.inside (Graph.pointSet H (edgeDrawing E)) := by
    rw [hpoint]; exact mem_image_inside hp
  have hext : planeHomeo p ∈ Graph.exterior H (edgeDrawing E) := hins.1
  have hb : Bornology.IsBounded (Graph.face H (edgeDrawing E) (planeHomeo p)) := hins.2
  obtain ⟨e, u, v, D, hcyc, hin⟩ :=
    Graph.encloses_of_isBounded_face hdraw (isPolygonal_edgeArc E hpoly _) h2 hext hb
  obtain ⟨heT, heG, c, d, hcd, hu, hv⟩ := hcyc.isLink
  obtain ⟨b, γ, hpath, hedges, hb'⟩ := exists_path_of_isPath E hcyc.isPath c hu
  have hbd : b = d := posHomeo_injective E (hb'.symm.trans hv)
  subst hbd
  have hdc : G.Adj b c := by
    rw [← SimpleGraph.mem_edgeSet, ← Sym2.eq_swap, ← hcd]; exact heG
  have hsdc : s(b, c) = e := by rw [hcd, Sym2.eq_swap]
  have hnot : s(b, c) ∉ γ.edges := by rw [hsdc, hedges]; exact hcyc.notMem
  refine ⟨b, SimpleGraph.Walk.cons hdc γ, ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff γ hdc).mpr ⟨hpath, hnot⟩
  · intro g hg
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hsdc]; exact_mod_cast heT
    · rw [hedges] at hg
      exact_mod_cast (hcyc.isPath.isWalk.edge_mem hg).1
  · refine mem_insideOf_of_image ?_
    have hlist : (SimpleGraph.Walk.cons hdc γ).edges = e :: D := by
      rw [SimpleGraph.Walk.edges_cons, hsdc, hedges]
    have hWG : ∀ g ∈ (e :: D), g ∈ G.edgeSet := by
      intro g hg
      rw [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact heG
      · exact (hcyc.isPath.isWalk.edge_mem hg).2
    have htrace : planeHomeo '' E.walkTrace (SimpleGraph.Walk.cons hdc γ)
        = Graph.edgesCover (edgeDrawing E) (e :: D) := by
      rw [walkTrace_eq_edgesTrace E _ (by simp), hlist, edgesCover_eq E hWG]
    rw [htrace]
    exact hin

/-- **The two connected base case of the boundary cycle theorem**, for every plane embedding,
whose edges are drawn by polygonal arcs. -/
theorem twoConnectedBoundaryCycles (E : UCPlanar.PlaneEmbedding G) :
    E.TwoConnectedBoundaryCycles :=
  twoConnectedBoundaryCycles_of_polygonal E (isPolygonalDrawing E)

/-- **The boundary cycle theorem**, granting the splitting of an edge set at a single vertex.
Every finite edge set whose drawing separates a point of the plane from infinity carries a cycle
that separates it. -/
theorem hasBoundaryCycles (E : UCPlanar.PlaneEmbedding G) (hJ : E.EdgeSplitting) :
    E.HasBoundaryCycles :=
  hasBoundaryCycles_of_twoConnected E hJ (twoConnectedBoundaryCycles E)

end UCPlanar.Support
