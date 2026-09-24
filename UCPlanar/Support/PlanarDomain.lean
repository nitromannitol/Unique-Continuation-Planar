/- Walks and sign components restricted to a plane domain. -/
import UCPlanar.Support.PlanarAttachments

open scoped Classical

/-- Retaining exactly the edges drawn in a domain produces a subgraph. -/
theorem UCPlanar.PlaneEmbedding.exists_graph_with_edges_in {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) (D : Set UCPlanar.Plane) :
    ∃ H : SimpleGraph V, H ≤ G ∧ ∀ x y,
      H.Adj x y ↔ ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ D := by
  let H : SimpleGraph V := {
    Adj := fun x y => ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ D
    symm := ⟨by
      rintro x y ⟨h, hh⟩
      exact ⟨h.symm, by rwa [← E.edge_symm h]⟩⟩
    loopless := ⟨by rintro x ⟨h, _⟩; exact h.ne rfl⟩ }
  exact ⟨H, fun _ _ h => h.choose, fun _ _ => Iff.rfl⟩

/-- A walk whose full trace lies in a domain lifts to its edge-restricted subgraph. -/
theorem UCPlanar.PlaneEmbedding.exists_lift_walk_in_domain {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) (D : Set UCPlanar.Plane)
    (H : SimpleGraph V) (hHG : H ≤ G)
    (hH : ∀ x y, H.Adj x y ↔ ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ D)
    {x y : V} (p : G.Walk x y) (hp : E.walkTrace p ⊆ D) :
    ∃ q : H.Walk x y, q.mapLe hHG = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons x z y h p ih =>
    obtain ⟨q, hq⟩ := ih (fun _ ht => hp (Or.inr ht))
    have he : H.Adj x z := (hH x z).mpr ⟨h, fun _ ht => hp (Or.inl ht)⟩
    refine ⟨.cons he q, ?_⟩
    change SimpleGraph.Walk.cons (hHG he) (q.mapLe hHG) = SimpleGraph.Walk.cons h p
    rw [hq]

/-- Walks in the edge-restricted graph have their full drawing in the domain. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_mapLe_subset_domain {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) (D : Set UCPlanar.Plane)
    (H : SimpleGraph V) (hHG : H ≤ G)
    (hH : ∀ x y, H.Adj x y ↔ ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ D)
    {x y : V} (p : H.Walk x y) (hx : E.pos x ∈ D) :
    E.walkTrace (p.mapLe hHG) ⊆ D := by
  induction p with
  | nil => exact Set.singleton_subset_iff.mpr hx
  | @cons x z y h p ih =>
    obtain ⟨he, hD⟩ := (hH x z).mp h
    change Set.range (E.edge (hHG h)) ∪ E.walkTrace (p.mapLe hHG) ⊆ D
    exact Set.union_subset hD (ih (hD ⟨1, (E.edge he).target⟩))

/-- Restricting to edges drawn inside a cycle preserves access of sign components to its boundary. -/
theorem UCPlanar.PlaneEmbedding.componentsMeetBoundary_in_domain {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o)
    (H : SimpleGraph V) (hHG : H ≤ G)
    (hH : ∀ x y, H.Adj x y ↔ ∃ h : G.Adj x y,
      Set.range (E.edge h) ⊆ E.closedCycleDomain γ)
    (S : Set V) (hS : S ⊆ E.cycleRegion γ)
    (hB : UCPlanar.ComponentsMeetBoundary G S {v | v ∈ γ.support}) :
    UCPlanar.ComponentsMeetBoundary H S {v | v ∈ γ.support} := by
  intro x
  obtain ⟨y, hy, p, _, hs, ht⟩ := E.exists_sign_boundary_access γ S hS hB x
  obtain ⟨q, hq⟩ := E.exists_lift_walk_in_domain (E.closedCycleDomain γ) H hHG hH p ht
  have hs' : ∀ z ∈ q.reverse.support, z ∈ S := by
    intro z hz
    have hz' : z ∈ q.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hz
    apply hs z
    rw [← hq, SimpleGraph.Walk.support_mapLe_eq_support]
    exact hz'
  exact ⟨y, hy, ⟨q.reverse.induce S hs'⟩⟩

/-- Join two attachments by an interior sign walk, retaining support and drawing control. -/
theorem UCPlanar.PlaneEmbedding.walk_between_attachments_in_domain {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) (D : Set UCPlanar.Plane)
    (H : SimpleGraph V) (hHG : H ≤ G)
    (hH : ∀ x y, H.Adj x y ↔ ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ D)
    (S : Set V) {z z' w w' p p' : V} (β : G.Walk z w) (δ : G.Walk z' w')
    (hp : p ∈ S) (hp' : p' ∈ S) (hwp : G.Adj w p) (hwp' : G.Adj w' p')
    (hβ : E.walkTrace (β.concat hwp) ⊆ D) (hδ : E.walkTrace (δ.concat hwp') ⊆ D)
    (hr : (H.induce S).Reachable ⟨p, hp⟩ ⟨p', hp'⟩) :
    ∃ ξ : G.Walk z z', E.walkTrace ξ ⊆ D ∧
      ∀ t ∈ ξ.support, t ∈ β.support ∨ t ∈ δ.support ∨ t ∈ S := by
  obtain ⟨r, hs⟩ := UCPlanar.Support.exists_walk_in_set_of_induced_reachable H S _ _ hr
  have hR : E.walkTrace (r.mapLe hHG) ⊆ D :=
    E.walkTrace_mapLe_subset_domain D H hHG hH r
      (hβ ((E.pos_mem_walkTrace_iff (β.concat hwp) p).mpr (β.concat hwp).end_mem_support))
  refine ⟨(β.concat hwp).append ((r.mapLe hHG).append (δ.concat hwp').reverse), ?_, ?_⟩
  · rw [E.walkTrace_append, E.walkTrace_append, E.walkTrace_reverse]
    exact Set.union_subset hβ (Set.union_subset hR hδ)
  · intro t ht
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_reverse,
      List.mem_reverse, SimpleGraph.Walk.support_concat, List.mem_append,
      List.mem_singleton, SimpleGraph.Walk.support_mapLe_eq_support] at ht
    rcases ht with (ht | rfl) | ht | ht | rfl
    · exact Or.inl ht
    · exact Or.inr (Or.inr hp)
    · exact Or.inr (Or.inr (hs _ ht))
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr hp')

