/- The drawing of a set of edges of a plane graph, and its splitting at a single common vertex. -/
import UCPlanar.Support.TopoSeparate
import Mathlib

open Set

/-- The plane arc drawn by an unordered pair of adjacent vertices. -/
def UCPlanar.PlaneEmbedding.arcOf {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (e : Sym2 V) : Set UCPlanar.Plane :=
  {p | ∃ x y, ∃ h : G.Adj x y, e = s(x, y) ∧ p ∈ Set.range (E.edge h)}

/-- The drawing of a set of edges. -/
def UCPlanar.PlaneEmbedding.edgesTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V)) : Set UCPlanar.Plane :=
  ⋃ e ∈ T, E.arcOf e

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- The arc of a drawn edge is the range of the path drawing it. -/
theorem arcOf_eq (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    E.arcOf s(x, y) = Set.range (E.edge h) := by
  ext p
  constructor
  · rintro ⟨u, w, k, hsym, hp⟩
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · rw [E.edge_symm h]
      exact hp
  · intro hp
    exact ⟨x, y, h, rfl, hp⟩

/-- The drawing of a set of edges grows with the set. -/
theorem edgesTrace_mono (E : UCPlanar.PlaneEmbedding G) {T U : Set (Sym2 V)} (h : T ⊆ U) :
    E.edgesTrace T ⊆ E.edgesTrace U :=
  Set.biUnion_subset_biUnion_left h

/-- The arc of an edge is compact. -/
theorem isCompact_arcOf (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    IsCompact (E.arcOf e) := by
  induction e with
  | _ x y =>
    rw [arcOf_eq E (by simpa using he)]
    exact isCompact_range (E.edge (by simpa using he)).continuous

/-- The drawing of a finite set of edges is compact, hence closed. -/
theorem isCompact_edgesTrace (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    (hfin : T.Finite) (hT : T ⊆ G.edgeSet) : IsCompact (E.edgesTrace T) :=
  hfin.isCompact_biUnion (fun _ he => isCompact_arcOf E (hT he))

/-- The drawing of a set of edges contains the drawing of each of its vertices. -/
theorem pos_mem_arcOf (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet)
    {z : V} (hz : z ∈ e) : E.pos z ∈ E.arcOf e := by
  induction e with
  | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    rw [arcOf_eq E hxy]
    rw [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨0, (E.edge hxy).source⟩
    · exact ⟨1, (E.edge hxy).target⟩

/-- **Two distinct drawn edges meet only at a vertex lying on both.** -/
theorem arcOf_inter_arcOf (E : UCPlanar.PlaneEmbedding G) {e f : Sym2 V}
    (he : e ∈ G.edgeSet) (hf : f ∈ G.edgeSet) (hef : e ≠ f) {p : UCPlanar.Plane}
    (hpe : p ∈ E.arcOf e) (hpf : p ∈ E.arcOf f) :
    ∃ z : V, z ∈ e ∧ z ∈ f ∧ p = E.pos z := by
  induction e with
  | _ x y =>
    induction f with
    | _ u w =>
      have hxy : G.Adj x y := by simpa using he
      have huw : G.Adj u w := by simpa using hf
      rw [arcOf_eq E hxy] at hpe
      rw [arcOf_eq E huw] at hpf
      have hne : ¬ ((x = u ∧ y = w) ∨ (x = w ∧ y = u)) := by
        intro hcase
        exact hef (by rw [Sym2.eq_iff]; exact hcase)
      obtain ⟨h1, h2⟩ := E.edge_inter hxy huw hne ⟨hpe, hpf⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
      rcases h1 with rfl | rfl
      · rcases h2 with h2 | h2
        · exact ⟨x, by simp, by rw [E.pos_injective h2]; simp, rfl⟩
        · exact ⟨x, by simp, by rw [E.pos_injective h2]; simp, rfl⟩
      · rcases h2 with h2 | h2
        · exact ⟨y, by simp, by rw [E.pos_injective h2]; simp, rfl⟩
        · exact ⟨y, by simp, by rw [E.pos_injective h2]; simp, rfl⟩

/-- **The drawings of two edge sets sharing a single vertex meet only at that vertex.** -/
theorem edgesTrace_inter_subset (E : UCPlanar.PlaneEmbedding G) {T U : Set (Sym2 V)}
    (hT : T ⊆ G.edgeSet) (hU : U ⊆ G.edgeSet) (hdisj : Disjoint T U) {v : V}
    (hmeet : ∀ z : V, (∃ e ∈ T, z ∈ e) → (∃ f ∈ U, z ∈ f) → z = v) :
    E.edgesTrace T ∩ E.edgesTrace U ⊆ {E.pos v} := by
  rintro p ⟨hpT, hpU⟩
  simp only [UCPlanar.PlaneEmbedding.edgesTrace, Set.mem_iUnion] at hpT hpU
  obtain ⟨e, he, hpe⟩ := hpT
  obtain ⟨f, hf, hpf⟩ := hpU
  have hef : e ≠ f := by
    rintro rfl
    exact Set.disjoint_left.mp hdisj he hf
  obtain ⟨z, hze, hzf, rfl⟩ := arcOf_inter_arcOf E (hT he) (hU hf) hef hpe hpf
  rw [hmeet z ⟨e, he, hze⟩ ⟨f, hf, hzf⟩]
  rfl

/-- The drawing of a union of edge sets is the union of their drawings. -/
theorem edgesTrace_union (E : UCPlanar.PlaneEmbedding G) (T U : Set (Sym2 V)) :
    E.edgesTrace (T ∪ U) = E.edgesTrace T ∪ E.edgesTrace U :=
  Set.biUnion_union T U _

/-- **A single drawn edge separates nothing from infinity.** -/
theorem insideOf_arcOf (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    insideOf (E.arcOf e) = ∅ := by
  induction e with
  | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    refine insideOf_eq_empty_of_image_isArc ?_
    rw [arcOf_eq E hxy]
    exact (isArcBetween_edge E hxy).isArc

end UCPlanar.Support
