/- Walks of a graph and walks of the finite plane graph its edges draw. -/
import UCPlanar.Support.TopoPolygonal
import Mathlib

open Set
open scoped Classical
open scoped Graph

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- Vertices are drawn injectively in the Euclidean plane. -/
theorem posHomeo_injective (E : UCPlanar.PlaneEmbedding G) :
    Function.Injective (fun z : V => planeHomeo (E.pos z)) :=
  fun _ _ h => E.pos_injective (planeHomeo.injective h)

/-- **A walk of the graph is a walk of the plane graph its edges draw.** -/
theorem isWalk_of_walk (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    {a b : V} (γ : G.Walk a b) (hγ : ∀ e ∈ γ.edges, e ∈ T)
    (ha : planeHomeo (E.pos a) ∈ V(edgeGraph E T)) :
    (edgeGraph E T).IsWalk (planeHomeo (E.pos a)) γ.edges (planeHomeo (E.pos b)) := by
  induction γ with
  | nil => exact Graph.IsWalk.nil ha
  | @cons x y z h tail ih =>
    have hxy : s(x, y) ∈ T := hγ _ (by simp)
    have hlink : (edgeGraph E T).IsLink s(x, y) (planeHomeo (E.pos x)) (planeHomeo (E.pos y)) :=
      ⟨hxy, h, x, y, rfl, rfl, rfl⟩
    rw [SimpleGraph.Walk.edges_cons]
    exact Graph.IsWalk.cons hlink
      (ih (fun e he => hγ e (by simp [he])) hlink.right_mem)

/-- **A vertex on a walk is drawn among the vertices the transported walk visits.** -/
theorem mem_walkVertices_of_mem_support (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    {a b : V} (γ : G.Walk a b) (hγ : ∀ e ∈ γ.edges, e ∈ T) :
    ∀ x ∈ γ.support, planeHomeo (E.pos x)
      ∈ (edgeGraph E T).walkVertices (planeHomeo (E.pos a)) γ.edges := by
  induction γ with
  | nil =>
    intro x hx
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
    subst hx
    exact Graph.mem_walkVertices_self
  | @cons p q r h tail ih =>
    intro x hx
    have hxy : s(p, q) ∈ T := hγ _ (by simp)
    have hlink : (edgeGraph E T).IsLink s(p, q) (planeHomeo (E.pos p)) (planeHomeo (E.pos q)) :=
      ⟨hxy, h, p, q, rfl, rfl, rfl⟩
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rw [SimpleGraph.Walk.edges_cons]
    rcases hx with rfl | hx
    · exact Graph.mem_walkVertices_self
    · exact Graph.mem_walkVertices_cons_of_mem hlink
        (ih (fun e he => hγ e (by simp [he])) x hx)

/-- **A walk of the drawn plane graph is a walk of the graph.** -/
theorem exists_walk_of_isWalk (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    {u v : Schoenflies.Plane} {W : List (Sym2 V)}
    (h : (edgeGraph E T).IsWalk u W v) :
    ∀ a : V, u = planeHomeo (E.pos a) →
      ∃ (b : V) (γ : G.Walk a b), γ.edges = W ∧ v = planeHomeo (E.pos b) := by
  induction h with
  | @nil x hx =>
    intro a ha
    exact ⟨a, SimpleGraph.Walk.nil, rfl, ha⟩
  | @cons p q r e W hl hW ih =>
    intro a ha
    obtain ⟨heT, heG, c, d, hcd, hpc, hqd⟩ := hl
    have hac : a = c := by
      refine posHomeo_injective E ?_
      show planeHomeo (E.pos a) = planeHomeo (E.pos c)
      rw [← ha, hpc]
    subst hac
    have hadj : G.Adj a d := by
      rw [← SimpleGraph.mem_edgeSet, ← hcd]; exact heG
    obtain ⟨b, γ, hedges, hb⟩ := ih d hqd
    exact ⟨b, SimpleGraph.Walk.cons hadj γ, by
      rw [SimpleGraph.Walk.edges_cons, hedges, hcd], hb⟩

/-- **A path of the drawn plane graph is a path of the graph.** -/
theorem exists_path_of_isPath (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    {u v : Schoenflies.Plane} {W : List (Sym2 V)}
    (h : (edgeGraph E T).IsPath u W v) :
    ∀ a : V, u = planeHomeo (E.pos a) →
      ∃ (b : V) (γ : G.Walk a b), γ.IsPath ∧ γ.edges = W ∧ v = planeHomeo (E.pos b) := by
  induction h with
  | @nil x hx =>
    intro a ha
    exact ⟨a, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, rfl, ha⟩
  | @cons p q r e W hl hW hfresh ih =>
    intro a ha
    obtain ⟨heT, heG, c, d, hcd, hpc, hqd⟩ := hl
    have hac : a = c := by
      refine posHomeo_injective E ?_
      show planeHomeo (E.pos a) = planeHomeo (E.pos c)
      rw [← ha, hpc]
    subst hac
    have hadj : G.Adj a d := by
      rw [← SimpleGraph.mem_edgeSet, ← hcd]; exact heG
    obtain ⟨b, γ, hpath, hedges, hb⟩ := ih d hqd
    have hedgeT : ∀ f ∈ γ.edges, f ∈ T := by
      intro f hf
      rw [hedges] at hf
      exact (hW.isWalk.edge_mem hf).1
    have hnot : a ∉ γ.support := by
      intro hmem
      apply hfresh
      have hv := mem_walkVertices_of_mem_support E γ hedgeT a hmem
      rw [hedges, ← hqd] at hv
      rw [ha]
      exact hv
    refine ⟨b, SimpleGraph.Walk.cons hadj γ, ?_, ?_, hb⟩
    · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, List.nodup_cons]
      exact ⟨hnot, (SimpleGraph.Walk.isPath_def γ).mp hpath⟩
    · rw [SimpleGraph.Walk.edges_cons, hedges, hcd]

end UCPlanar.Support
