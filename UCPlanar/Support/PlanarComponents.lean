/- Boundary representatives of components of induced subgraphs. -/
import UCPlanar.Support.PlanarTrace

open scoped Classical

/-- Every component has a vertex on the prescribed boundary. -/
theorem UCPlanar.Support.exists_component_boundary_vertex {V : Type*}
    (G : SimpleGraph V) (S B : Set V) (h : UCPlanar.ComponentsMeetBoundary G S B)
    (c : (G.induce S).ConnectedComponent) :
    ∃ x : S, x.val ∈ B ∧ (G.induce S).connectedComponentMk x = c := by
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h x =>
    obtain ⟨y, hy, hr⟩ := h x
    exact ⟨y, hy, (SimpleGraph.ConnectedComponent.sound hr).symm⟩

/-- Choose a boundary representative as a function of the entire component. -/
noncomputable def UCPlanar.Support.componentBoundaryVertex {V : Type*}
    (G : SimpleGraph V) (S B : Set V) (h : UCPlanar.ComponentsMeetBoundary G S B)
    (c : (G.induce S).ConnectedComponent) : S :=
  (UCPlanar.Support.exists_component_boundary_vertex G S B h c).choose

/-- The chosen vertex lies on the boundary and represents the specified component. -/
theorem UCPlanar.Support.componentBoundaryVertex_spec {V : Type*}
    (G : SimpleGraph V) (S B : Set V) (h : UCPlanar.ComponentsMeetBoundary G S B)
    (c : (G.induce S).ConnectedComponent) :
    (UCPlanar.Support.componentBoundaryVertex G S B h c).val ∈ B ∧
    (G.induce S).connectedComponentMk
      (UCPlanar.Support.componentBoundaryVertex G S B h c) = c := by
  exact (UCPlanar.Support.exists_component_boundary_vertex G S B h c).choose_spec

/-- Different components have different boundary representatives. -/
theorem UCPlanar.Support.componentBoundaryVertex_injective {V : Type*}
    (G : SimpleGraph V) (S B : Set V) (h : UCPlanar.ComponentsMeetBoundary G S B) :
    Function.Injective (fun c => (UCPlanar.Support.componentBoundaryVertex G S B h c).val) := by
  intro c d he
  have hs : UCPlanar.Support.componentBoundaryVertex G S B h c =
      UCPlanar.Support.componentBoundaryVertex G S B h d := Subtype.ext he
  have hc := congrArg (G.induce S).connectedComponentMk hs
  rwa [(UCPlanar.Support.componentBoundaryVertex_spec G S B h c).2,
    (UCPlanar.Support.componentBoundaryVertex_spec G S B h d).2] at hc

/-- Two vertices have the same boundary label exactly when they are connected within the set. -/
theorem UCPlanar.Support.boundary_labels_eq_iff_reachable {V : Type*}
    (G : SimpleGraph V) (S B : Set V) (h : UCPlanar.ComponentsMeetBoundary G S B)
    (x y : S) :
    (UCPlanar.Support.componentBoundaryVertex G S B h
      ((G.induce S).connectedComponentMk x)).val =
    (UCPlanar.Support.componentBoundaryVertex G S B h
      ((G.induce S).connectedComponentMk y)).val ↔ (G.induce S).Reachable x y := by
  constructor
  · intro he
    exact SimpleGraph.ConnectedComponent.exact
      (UCPlanar.Support.componentBoundaryVertex_injective G S B h he)
  · intro hr
    rw [SimpleGraph.ConnectedComponent.sound hr]

/-- Induced connectivity supplies an original graph walk entirely in the inducing set. -/
theorem UCPlanar.Support.exists_walk_in_set_of_induced_reachable {V : Type*}
    (G : SimpleGraph V) (S : Set V) (x y : S) (h : (G.induce S).Reachable x y) :
    ∃ p : G.Walk x.val y.val, ∀ z ∈ p.support, z ∈ S := by
  obtain ⟨q⟩ := h
  let φ : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
  refine ⟨q.map φ, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨w, _, rfl⟩ := hz
  exact w.property

/-- Join two attachments through a sign component, including both endpoint edges. -/
theorem UCPlanar.Support.walk_between_sign_attachments {V : Type*}
    (G : SimpleGraph V) (S : Set V) {z z' w w' p p' : V}
    (β : G.Walk z w) (δ : G.Walk z' w') (hp : p ∈ S) (hp' : p' ∈ S)
    (hwp : G.Adj w p) (hwp' : G.Adj w' p')
    (hr : (G.induce S).Reachable ⟨p, hp⟩ ⟨p', hp'⟩) :
    ∃ ξ : G.Walk z z', ∀ t ∈ ξ.support,
      t ∈ β.support ∨ t ∈ δ.support ∨ t ∈ S := by
  obtain ⟨r, hs⟩ := UCPlanar.Support.exists_walk_in_set_of_induced_reachable G S _ _ hr
  refine ⟨(β.concat hwp).append (r.append (δ.concat hwp').reverse), ?_⟩
  intro t ht
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
    List.mem_reverse, SimpleGraph.Walk.support_concat, List.mem_append,
    List.mem_singleton] at ht
  rcases ht with (ht | rfl) | ht | ht | rfl
  · exact Or.inl ht
  · exact Or.inr (Or.inr hp)
  · exact Or.inr (Or.inr (hs _ ht))
  · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr hp')
