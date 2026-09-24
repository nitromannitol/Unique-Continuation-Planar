/- Plane embeddings whose edges are drawn by polygonal arcs, and the finite plane graph that a
finite set of edges draws. -/
import UCPlanar.Support.TopoBlock
import Schoenflies.OuterChain
import Mathlib

open Set unitInterval
open scoped Classical
open scoped Graph

/-- **A polygonal plane embedding.**  Every edge is drawn by a polygonal arc.  This is the
hypothesis under which the finite plane graph drawn by a set of edges falls inside the scope of
the polygonal face cycle theorem. -/
def UCPlanar.PlaneEmbedding.IsPolygonalDrawing {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  ∀ e ∈ G.edgeSet, Schoenflies.IsPolygonal (UCPlanar.Support.planeHomeo '' E.arcOf e)

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- The chosen ordered representative of an unordered pair. -/
theorem mk_out (e : Sym2 V) : s(e.out.1, e.out.2) = e := Quot.out_eq e

/-- An edge of a simple graph joins the two components of its chosen representative. -/
theorem adj_out {e : Sym2 V} (he : e ∈ G.edgeSet) : G.Adj e.out.1 e.out.2 := by
  rw [← SimpleGraph.mem_edgeSet, mk_out]
  exact he

/-- The arc of an edge, read through its chosen ordered representative. -/
theorem arcOf_eq_out (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    E.arcOf e = Set.range (E.edge (adj_out he)) := by
  have h1 := arcOf_eq E (adj_out he)
  rwa [mk_out] at h1

/-- The parametrized drawing of an edge, in the Euclidean plane of the Jordan curve
development. -/
noncomputable def edgeDrawing (E : UCPlanar.PlaneEmbedding G) (e : Sym2 V) (t : ℝ) :
    Schoenflies.Plane :=
  if h : G.Adj e.out.1 e.out.2 then planeHomeo ((E.edge h).extend t) else 0

theorem edgeDrawing_eq (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    edgeDrawing E e = fun t => planeHomeo ((E.edge (adj_out he)).extend t) := by
  funext t
  rw [edgeDrawing, dif_pos (adj_out he)]

/-- The point set of a drawn edge is the transported arc of that edge. -/
theorem edgeArc_edgeDrawing (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    Graph.edgeArc (edgeDrawing E) e = planeHomeo '' E.arcOf e := by
  rw [Graph.edgeArc, edgeDrawing_eq E he, arcOf_eq_out E he, Set.image_eq_range,
    show (fun t : unitInterval => planeHomeo ((E.edge (adj_out he)).extend ↑t)) =
      (planeHomeo ∘ (E.edge (adj_out he))) from
      funext fun t => congrArg planeHomeo (Path.extend_extends' _ t)]
  exact Set.range_comp _ _

/-- An element of an unordered pair names the pair together with its partner. -/
theorem exists_mk_of_mem {z : V} {e : Sym2 V} (hz : z ∈ e) : ∃ w, e = s(z, w) :=
  Sym2.mem_iff_exists.mp hz

/-- **The finite plane graph drawn by a set of edges.**  Its vertices are the drawn endpoints
of the edges of the set and its edges are the edges of the set, drawn by the same arcs. -/
noncomputable def edgeGraph (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V)) :
    Graph Schoenflies.Plane (Sym2 V) where
  vertexSet := {q | ∃ z : V, (∃ e ∈ T, e ∈ G.edgeSet ∧ z ∈ e) ∧ q = planeHomeo (E.pos z)}
  IsLink e x y := e ∈ T ∧ e ∈ G.edgeSet ∧ ∃ a b : V, e = s(a, b) ∧
    x = planeHomeo (E.pos a) ∧ y = planeHomeo (E.pos b)
  edgeSet := {e | e ∈ T ∧ e ∈ G.edgeSet}
  isLink_symm := by
    rintro e - 
    constructor
    rintro x y ⟨heT, heG, a, b, rfl, rfl, rfl⟩
    exact ⟨heT, heG, b, a, Sym2.eq_swap, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨-, -, a, b, hab, rfl, rfl⟩ ⟨-, -, a', b', hab', rfl, rfl⟩
    rw [hab, Sym2.eq_iff] at hab'
    rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · rintro ⟨heT, heG⟩
      exact ⟨planeHomeo (E.pos e.out.1), planeHomeo (E.pos e.out.2), heT, heG,
        e.out.1, e.out.2, (mk_out e).symm, rfl, rfl⟩
    · rintro ⟨x, y, heT, heG, -⟩
      exact ⟨heT, heG⟩
  left_mem_of_isLink := by
    rintro e x y ⟨heT, heG, a, b, rfl, rfl, -⟩
    exact ⟨a, ⟨s(a, b), heT, heG, by simp⟩, rfl⟩

@[simp] theorem edgeSet_edgeGraph (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V)) :
    E(edgeGraph E T) = {e | e ∈ T ∧ e ∈ G.edgeSet} := rfl

@[simp] theorem vertexSet_edgeGraph (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V)) :
    V(edgeGraph E T) =
      {q | ∃ z : V, (∃ e ∈ T, e ∈ G.edgeSet ∧ z ∈ e) ∧ q = planeHomeo (E.pos z)} := rfl

theorem isLink_edgeGraph_iff (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V))
    (e : Sym2 V) (x y : Schoenflies.Plane) :
    (edgeGraph E T).IsLink e x y ↔ e ∈ T ∧ e ∈ G.edgeSet ∧ ∃ a b : V, e = s(a, b) ∧
      x = planeHomeo (E.pos a) ∧ y = planeHomeo (E.pos b) := Iff.rfl

/-- The drawn endpoints of an edge of the set are vertices of the graph it draws. -/
theorem mem_vertexSet_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    {e : Sym2 V} (heT : e ∈ T) (heG : e ∈ G.edgeSet) {z : V} (hz : z ∈ e) :
    planeHomeo (E.pos z) ∈ V(edgeGraph E T) := ⟨z, ⟨e, heT, heG, hz⟩, rfl⟩

/-- **The edges of the set are drawn as a plane graph.** -/
theorem isDrawing_edgeGraph (E : UCPlanar.PlaneEmbedding G) (T : Set (Sym2 V)) :
    Graph.IsDrawing (edgeGraph E T) (edgeDrawing E) where
  edge_param := by
    rintro e ⟨heT, heG⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [edgeDrawing_eq E heG]
      exact (planeHomeo.continuous.comp (E.edge (adj_out heG)).continuous_extend).continuousOn
    · rw [edgeDrawing_eq E heG]
      intro s hs t ht hst
      simp only at hst
      have h2 : (E.edge (adj_out heG)).extend s = (E.edge (adj_out heG)).extend t :=
        planeHomeo.injective hst
      rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at h2
      exact Subtype.ext_iff.mp (E.edge_injective (adj_out heG) h2)
    · refine ⟨heT, heG, e.out.1, e.out.2, (mk_out e).symm, ?_, ?_⟩ <;>
        rw [edgeDrawing_eq E heG] <;> simp
  vertex_mem_edgeArc := by
    rintro e x y v ⟨heT, heG, a, b, hab, rfl, rfl⟩ ⟨z, -, rfl⟩ hv
    rw [edgeArc_edgeDrawing E heG, arcOf_eq_out E heG] at hv
    obtain ⟨q, hq, hqz⟩ := hv
    have hzq : E.pos z = q := (planeHomeo.injective hqz).symm
    have hz : E.pos z ∈ Set.range (E.edge (adj_out heG)) := by rw [hzq]; exact hq
    have hmem : z ∈ e := by
      rcases E.vertex_on_edge (adj_out heG) z hz with h | h
      · rw [h]; exact Sym2.out_fst_mem e
      · rw [h]; exact Sym2.out_snd_mem e
    rw [hab, Sym2.mem_iff] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_inter := by
    rintro e f ⟨heT, heG⟩ ⟨hfT, hfG⟩ hef p hpe hpf
    rw [edgeArc_edgeDrawing E heG] at hpe
    rw [edgeArc_edgeDrawing E hfG] at hpf
    obtain ⟨q, hq, rfl⟩ := hpe
    obtain ⟨q', hq', hqq⟩ := hpf
    have hqeq : q' = q := planeHomeo.injective hqq
    subst hqeq
    obtain ⟨z, hze, hzf, rfl⟩ := arcOf_inter_arcOf E heG hfG hef hq hq'
    obtain ⟨w, hw⟩ := exists_mk_of_mem hze
    obtain ⟨w', hw'⟩ := exists_mk_of_mem hzf
    exact ⟨⟨z, ⟨e, heT, heG, hze⟩, rfl⟩,
      ⟨planeHomeo (E.pos w), heT, heG, z, w, hw, rfl, rfl⟩,
      ⟨planeHomeo (E.pos w'), hfT, hfG, z, w', hw', rfl, rfl⟩⟩

/-- An unordered pair has at most the two components of its chosen representative. -/
theorem mem_pair_subset (e : Sym2 V) : {z : V | z ∈ e} ⊆ {e.out.1, e.out.2} := by
  intro z hz
  have hz' : z ∈ s(e.out.1, e.out.2) := by rw [mk_out]; exact hz
  rw [Sym2.mem_iff] at hz'
  simpa using hz'

/-- The vertices carried by a set of edges. -/
theorem finite_edgeVertices {T : Set (Sym2 V)} (hfin : T.Finite) :
    {z : V | ∃ e ∈ T, e ∈ G.edgeSet ∧ z ∈ e}.Finite := by
  refine Set.Finite.subset (hfin.biUnion (fun e _ => (Set.finite_singleton e.out.2).insert e.out.1))
    ?_
  rintro z ⟨e, heT, -, hz⟩
  exact Set.mem_biUnion heT (mem_pair_subset e hz)

/-- The finite edge set draws a finite plane graph. -/
theorem finite_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)} (hfin : T.Finite) :
    (edgeGraph E T).Finite where
  finite_vertexSet := by
    refine Set.Finite.subset ((finite_edgeVertices (G := G) hfin).image
      (fun z => planeHomeo (E.pos z))) ?_
    rintro q ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  finite_edgeSet := hfin.subset (fun e he => he.1)

/-- **The drawn graph occupies exactly the drawing of the edge set.** -/
theorem pointSet_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    (hT : T ⊆ G.edgeSet) :
    Graph.pointSet (edgeGraph E T) (edgeDrawing E) = planeHomeo '' E.edgesTrace T := by
  have harcs : (⋃ e ∈ E(edgeGraph E T), Graph.edgeArc (edgeDrawing E) e)
      = planeHomeo '' E.edgesTrace T := by
    refine Set.Subset.antisymm ?_ ?_
    · intro q hq
      simp only [Set.mem_iUnion] at hq
      obtain ⟨e, he, hqe⟩ := hq
      rw [edgeArc_edgeDrawing E (hT he.1) ] at hqe
      obtain ⟨w, hw, rfl⟩ := hqe
      exact ⟨w, Set.mem_biUnion he.1 hw, rfl⟩
    · rintro q ⟨w, hw, rfl⟩
      simp only [UCPlanar.PlaneEmbedding.edgesTrace, Set.mem_iUnion] at hw
      obtain ⟨e, he, hwe⟩ := hw
      refine Set.mem_biUnion (show e ∈ E(edgeGraph E T) from ⟨he, hT he⟩) ?_
      rw [edgeArc_edgeDrawing E (hT he)]
      exact ⟨w, hwe, rfl⟩
  rw [Graph.pointSet, harcs]
  refine Set.union_eq_self_of_subset_left ?_
  rintro q ⟨z, ⟨e, heT, heG, hz⟩, rfl⟩
  exact ⟨E.pos z, Set.mem_biUnion heT (pos_mem_arcOf E heG hz), rfl⟩

/-- **Every plane embedding draws its edges by polygonal arcs**, by the structure's own field,
read on the unordered pair through its chosen ordered representative. -/
theorem isPolygonalDrawing (E : UCPlanar.PlaneEmbedding G) : E.IsPolygonalDrawing := by
  intro e he
  rw [arcOf_eq_out E he]
  exact E.edge_polygonal (adj_out he)

/-- A polygonal embedding draws every edge of the set by a polygonal arc. -/
theorem isPolygonal_edgeArc (E : UCPlanar.PlaneEmbedding G) (hpoly : E.IsPolygonalDrawing)
    (T : Set (Sym2 V)) :
    ∀ g ∈ E(edgeGraph E T), Schoenflies.IsPolygonal (Graph.edgeArc (edgeDrawing E) g) := by
  rintro g ⟨-, hgG⟩
  rw [edgeArc_edgeDrawing E hgG]
  exact hpoly g hgG

end UCPlanar.Support
