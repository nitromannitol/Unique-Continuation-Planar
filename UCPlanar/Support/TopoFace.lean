/- The complementary faces of a drawn graph: their elementary properties. -/
import UCPlanar.Support.TopoRegion

open Set

open scoped Classical

namespace UCPlanar.Support

/-- A face is nonempty. -/
theorem isFace_nonempty {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {F : Set UCPlanar.Plane} (hF : E.IsFace F) : F.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := hF
  exact ⟨p, mem_connectedComponentIn hp⟩

/-- A face is connected. -/
theorem isFace_isPreconnected {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {F : Set UCPlanar.Plane} (hF : E.IsFace F) : IsPreconnected F := by
  obtain ⟨p, hp, rfl⟩ := hF
  exact isPreconnected_connectedComponentIn

/-- A face misses the drawing. -/
theorem isFace_subset_compl_trace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {F : Set UCPlanar.Plane} (hF : E.IsFace F) :
    F ⊆ E.traceᶜ := by
  obtain ⟨p, hp, rfl⟩ := hF
  exact connectedComponentIn_subset _ _

/-- Two faces are equal or disjoint. -/
theorem isFace_eq_or_disjoint {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {F H : Set UCPlanar.Plane} (hF : E.IsFace F) (hH : E.IsFace H) :
    F = H ∨ Disjoint F H := by
  obtain ⟨p, hp, rfl⟩ := hF
  obtain ⟨q, hq, rfl⟩ := hH
  by_cases hd : Disjoint (connectedComponentIn E.traceᶜ p) (connectedComponentIn E.traceᶜ q)
  · exact Or.inr hd
  · left
    rw [Set.not_disjoint_iff] at hd
    obtain ⟨z, hz1, hz2⟩ := hd
    rw [connectedComponentIn_eq hz1, connectedComponentIn_eq hz2]

/-- A face containing a point is determined by that point. -/
theorem isFace_eq_of_mem {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {F H : Set UCPlanar.Plane} (hF : E.IsFace F) (hH : E.IsFace H) {z : UCPlanar.Plane}
    (hzF : z ∈ F) (hzH : z ∈ H) : F = H := by
  rcases isFace_eq_or_disjoint E hF hH with h | h
  · exact h
  · exact absurd hzH (Set.disjoint_left.mp h hzF)

/-- The drawing of a walk lies in the drawing of the graph. -/
theorem walkTrace_subset_trace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) :
    E.walkTrace p ⊆ E.trace := by
  induction p with
  | nil => exact fun t ht => Or.inl ⟨_, ht.symm⟩
  | @cons a b c h q ih =>
    rintro t (ht | ht)
    · exact Or.inr ⟨a, b, h, ht⟩
    · exact ih ht

/-- No drawn vertex lies in a face. -/
theorem pos_notMem_isFace {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {F : Set UCPlanar.Plane} (hF : E.IsFace F) (x : V) : E.pos x ∉ F := fun hx =>
  isFace_subset_compl_trace E hF hx (Or.inl ⟨x, rfl⟩)

/-- One drawn edge, and nothing when the pair is not adjacent. -/
noncomputable def starEdge {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    (x y : V) : Set UCPlanar.Plane :=
  if h : G.Adj x y then Set.range (E.edge h) else ∅

/-- The drawn edges at a vertex. -/
def edgeStar {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) (x : V) :
    Set UCPlanar.Plane := {t | ∃ y, ∃ h : G.Adj x y, t ∈ Set.range (E.edge h)}

/-- A single drawn edge is compact. -/
theorem isCompact_starEdge {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    (x y : V) : IsCompact (starEdge E x y) := by
  rw [starEdge]
  split
  · exact isCompact_range (E.edge _).continuous
  · exact isCompact_empty

/-- The edges at a vertex are the edges to its neighbours. -/
theorem edgeStar_eq_biUnion {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (E : UCPlanar.PlaneEmbedding G) (x : V) :
    edgeStar E x = ⋃ y ∈ G.neighborFinset x, starEdge E x y := by
  ext t
  constructor
  · rintro ⟨y, h, ht⟩
    refine Set.mem_biUnion ((SimpleGraph.mem_neighborFinset G x y).mpr h) ?_
    rw [starEdge, dif_pos h]
    exact ht
  · intro ht
    rw [Set.mem_iUnion₂] at ht
    obtain ⟨y, hy, ht⟩ := ht
    have h : G.Adj x y := (SimpleGraph.mem_neighborFinset G x y).mp hy
    rw [starEdge, dif_pos h] at ht
    exact ⟨y, h, ht⟩

/-- In a locally finite graph the edges at a vertex form a compact set. -/
theorem isCompact_edgeStar {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    (E : UCPlanar.PlaneEmbedding G) (x : V) : IsCompact (edgeStar E x) := by
  rw [edgeStar_eq_biUnion]
  exact (G.neighborFinset x).isCompact_biUnion (fun y _ => isCompact_starEdge E x y)

/-- The drawing of a graph is its vertices together with the edges at each vertex. -/
theorem trace_eq_union_edgeStar {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) :
    E.trace = Set.range E.pos ∪ ⋃ x : V, edgeStar E x := by
  ext t
  constructor
  · rintro (ht | ⟨x, y, h, ht⟩)
    · exact Or.inl ht
    · exact Or.inr (Set.mem_iUnion.mpr ⟨x, y, h, ht⟩)
  · rintro (ht | ht)
    · exact Or.inl ht
    · obtain ⟨x, y, h, hx⟩ := Set.mem_iUnion.mp ht
      exact Or.inr ⟨x, y, h, hx⟩

/-- The edges at a vertex belong to the drawing. -/
theorem edgeStar_subset_trace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (x : V) : edgeStar E x ⊆ E.trace := by
  rintro t ⟨y, h, ht⟩
  exact Or.inr ⟨x, y, h, ht⟩

end UCPlanar.Support
