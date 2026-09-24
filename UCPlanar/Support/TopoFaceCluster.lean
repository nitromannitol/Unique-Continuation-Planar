/- The cluster of faces meeting a vertex set, the open plane region it fills, and the cycle of
the graph that surrounds that region. -/
import UCPlanar.Support.TopoCluster
import UCPlanar.Support.TopoProper
import Mathlib

open Set
open scoped Classical

/-- **The faces of a plane embedding form a locally finite family.**  Every point of the plane
has a neighbourhood meeting only finitely many faces. -/
def UCPlanar.PlaneEmbedding.LocallyFiniteFaces {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  LocallyFinite (fun F : {F : Set UCPlanar.Plane // E.IsFace F} => (F : Set UCPlanar.Plane))

/-- The faces none of whose incident vertices lies in `N`. -/
def UCPlanar.PlaneEmbedding.facesAvoiding {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (N : Set V) : Set (Set UCPlanar.Plane) :=
  {F | E.IsFace F ∧ ∀ y, E.Incident F y → y ∉ N}

/-- **The region filled by the faces that meet `N`.**  It is the complement of the closure of
the union of the faces avoiding `N`, so it holds every point of the plane that no such face
reaches, in particular the drawing of every vertex of `N`. -/
def UCPlanar.PlaneEmbedding.clusterRegion {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (N : Set V) : Set UCPlanar.Plane :=
  (closure (⋃ F ∈ E.facesAvoiding N, F))ᶜ

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **Every vertex of a periodic plane graph has a neighbour.**  A nonzero period moves a vertex,
so the graph has two vertices, and a walk between them starts with an edge. -/
theorem exists_adj_of_periodic (Q : UCPlanar.PeriodicPlaneGraph V) (x : V) :
    ∃ y, Q.graph.Adj x y := by
  classical
  set a : LatticeProb.Site 2 := fun i => if i = 0 then 1 else 0 with ha
  have hane : (fun i => ((a i : ℤ) : ℝ)) ≠ (0 : UCPlanar.Plane) := by
    intro h
    have h0 := congrFun h 0
    simp [ha] at h0
  have hper : Q.period (fun i => ((a i : ℤ) : ℝ)) ≠ 0 := by
    intro h
    exact hane (by simpa using (Q.period.map_eq_zero_iff).mp h)
  have hne : Q.shift a x ≠ x := by
    intro h
    have h1 : Q.pos (Q.shift a x) = Q.pos x := by rw [h]
    rw [Q.pos_shift a x] at h1
    have h2 : Q.pos x + Q.period (fun i => ((a i : ℤ) : ℝ)) = Q.pos x + 0 := by simpa using h1
    exact hper (add_left_cancel h2)
  have key : ∀ (y : V), Q.graph.Walk x y → x ≠ y → ∃ z, Q.graph.Adj x z := by
    intro y w hxy
    cases w with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, h⟩
  obtain ⟨w⟩ := Q.connected.preconnected x (Q.shift a x)
  exact key _ w (fun h => hne h.symm)

/-- **The drawing of a periodic plane graph is the drawing of its edge set.**  Every drawn vertex
lies on one of the arcs at it. -/
theorem trace_eq_edgesTrace (Q : UCPlanar.PeriodicPlaneGraph V) :
    Q.embedding.trace = Q.embedding.edgesTrace Q.graph.edgeSet := by
  ext p
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, y, h, hp⟩)
    · obtain ⟨y, hy⟩ := exists_adj_of_periodic Q x
      have hmem : s(x, y) ∈ Q.graph.edgeSet := hy
      exact Set.mem_biUnion hmem (pos_mem_arcOf Q.embedding hmem (by simp))
    · have hmem : s(x, y) ∈ Q.graph.edgeSet := h
      refine Set.mem_biUnion hmem ?_
      rw [arcOf_eq Q.embedding h]
      exact hp
  · intro hp
    obtain ⟨e, _, hpe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding hp
    obtain ⟨x, y, h, _, hpr⟩ := hpe
    exact Or.inr ⟨x, y, h, hpr⟩

/-- The filled region is open. -/
theorem isOpen_clusterRegion (E : UCPlanar.PlaneEmbedding G) (N : Set V) :
    IsOpen (E.clusterRegion N) := isClosed_closure.isOpen_compl

/-- **Local finiteness of the faces is a statement about the drawing.**  A point off the drawing
lies in a face, and that face is an open neighbourhood of it meeting no other face, so the only
points at which local finiteness has content are the drawn ones. -/
theorem locallyFiniteFaces_of_trace (Q : UCPlanar.PeriodicPlaneGraph V)
    (h : ∀ p ∈ Q.embedding.trace, ∃ t ∈ nhds p,
      {F : {F : Set UCPlanar.Plane // Q.embedding.IsFace F} |
        ((F : Set UCPlanar.Plane) ∩ t).Nonempty}.Finite) :
    Q.embedding.LocallyFiniteFaces := by
  intro p
  by_cases hp : p ∈ Q.embedding.trace
  · exact h p hp
  · have hface : Q.embedding.IsFace (connectedComponentIn Q.embedding.traceᶜ p) := ⟨p, hp, rfl⟩
    refine ⟨connectedComponentIn Q.embedding.traceᶜ p,
      (isOpen_isFace Q hface).mem_nhds (mem_connectedComponentIn hp), ?_⟩
    refine Set.Finite.subset (Set.finite_singleton
      (⟨connectedComponentIn Q.embedding.traceᶜ p, hface⟩ :
        {F : Set UCPlanar.Plane // Q.embedding.IsFace F})) ?_
    rintro ⟨F, hF⟩ ⟨q, hq1, hq2⟩
    refine Set.mem_singleton_iff.mpr (Subtype.ext ?_)
    rcases isFace_eq_or_disjoint Q.embedding hF hface with heq | hdis
    · exact heq
    · exact absurd (Set.disjoint_left.mp hdis hq1) (by simpa using hq2)


/-- A locally finite family of faces has the closure of its union equal to the union of the
closures. -/
theorem closure_biUnion_facesAvoiding (E : UCPlanar.PlaneEmbedding G)
    (hLF : E.LocallyFiniteFaces) (N : Set V) :
    closure (⋃ F ∈ E.facesAvoiding N, F) = ⋃ F ∈ E.facesAvoiding N, closure F := by
  classical
  have hinj : Function.Injective
      (fun F : {F : Set UCPlanar.Plane // F ∈ E.facesAvoiding N} =>
        (⟨F.val, F.2.1⟩ : {F : Set UCPlanar.Plane // E.IsFace F})) := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun (F : {F : Set UCPlanar.Plane // E.IsFace F}) => F.val) hab
    simpa using h
  have hsub : LocallyFinite
      (fun F : {F : Set UCPlanar.Plane // F ∈ E.facesAvoiding N} => (F : Set UCPlanar.Plane)) :=
    hLF.comp_injective hinj
  rw [Set.biUnion_eq_iUnion, Set.biUnion_eq_iUnion, hsub.closure_iUnion]

/-- A point of the filled region is reached by no face avoiding `N`. -/
theorem mem_clusterRegion_iff (E : UCPlanar.PlaneEmbedding G) (hLF : E.LocallyFiniteFaces)
    (N : Set V) (p : UCPlanar.Plane) :
    p ∈ E.clusterRegion N ↔ ∀ F ∈ E.facesAvoiding N, p ∉ closure F := by
  have h := closure_biUnion_facesAvoiding E hLF N
  constructor
  · intro hp F hF hcl
    exact hp (by rw [h]; exact Set.mem_biUnion hF hcl)
  · intro hall hp
    rw [h] at hp
    obtain ⟨F, hF, hcl⟩ := Set.mem_iUnion₂.mp hp
    exact hall F hF hcl

/-- **The drawing of a vertex of `N` lies in the filled region.**  A face reaching that drawing
has the vertex on its frontier, hence is incident to a vertex of `N` and does not avoid `N`. -/
theorem pos_mem_clusterRegion (E : UCPlanar.PlaneEmbedding G) (hLF : E.LocallyFiniteFaces)
    {N : Set V} {x : V} (hx : x ∈ N) : E.pos x ∈ E.clusterRegion N := by
  rw [mem_clusterRegion_iff E hLF]
  intro F hF hcl
  have hnf : E.pos x ∉ F := pos_notMem_isFace E hF.1 x
  rw [closure_eq_self_union_frontier] at hcl
  rcases hcl with h | h
  · exact hnf h
  · exact hF.2 x h hx

/-- The filled region is confined by any set outside which some face avoiding `N` reaches every
point. -/
theorem clusterRegion_subset_of_cover (E : UCPlanar.PlaneEmbedding G) {N : Set V}
    {A : Set UCPlanar.Plane}
    (h : ∀ p, p ∉ A → ∃ F ∈ E.facesAvoiding N, p ∈ closure F) : E.clusterRegion N ⊆ A := by
  intro p hp
  by_contra hA
  obtain ⟨F, hF, hcl⟩ := h p hA
  exact hp (closure_mono (Set.subset_biUnion_of_mem (u := fun F => F) hF) hcl)

/-- The filled region is bounded as soon as every point outside a bounded set is reached by a
face avoiding `N`. -/
theorem isBounded_clusterRegion_of_cover (E : UCPlanar.PlaneEmbedding G) {N : Set V}
    {A : Set UCPlanar.Plane} (hA : Bornology.IsBounded A)
    (h : ∀ p, p ∉ A → ∃ F ∈ E.facesAvoiding N, p ∈ closure F) :
    Bornology.IsBounded (E.clusterRegion N) :=
  hA.subset (clusterRegion_subset_of_cover E h)

/-- A frontier point of the filled region is reached by a face avoiding `N`. -/
theorem exists_facesAvoiding_of_mem_frontier (E : UCPlanar.PlaneEmbedding G)
    (hLF : E.LocallyFiniteFaces) {N : Set V} {p : UCPlanar.Plane}
    (hp : p ∈ frontier (E.clusterRegion N)) :
    ∃ F ∈ E.facesAvoiding N, p ∈ closure F := by
  have hfr : frontier (E.clusterRegion N)
      = frontier (closure (⋃ F ∈ E.facesAvoiding N, F)) := by
    rw [UCPlanar.PlaneEmbedding.clusterRegion, frontier_compl]
  rw [hfr] at hp
  have hmem : p ∈ closure (closure (⋃ F ∈ E.facesAvoiding N, F)) := hp.1
  rw [closure_closure, closure_biUnion_facesAvoiding E hLF N] at hmem
  obtain ⟨F, hF, hcl⟩ := Set.mem_iUnion₂.mp hmem
  exact ⟨F, hF, hcl⟩

/-- **A vertex on the frontier of the filled region is incident to a face avoiding `N`.** -/
theorem incident_facesAvoiding_of_pos_mem_frontier (E : UCPlanar.PlaneEmbedding G)
    (hLF : E.LocallyFiniteFaces) {N : Set V} {x : V}
    (hx : E.pos x ∈ frontier (E.clusterRegion N)) :
    ∃ F ∈ E.facesAvoiding N, E.Incident F x := by
  obtain ⟨F, hF, hcl⟩ := exists_facesAvoiding_of_mem_frontier E hLF hx
  refine ⟨F, hF, ?_⟩
  have hnf : E.pos x ∉ F := pos_notMem_isFace E hF.1 x
  rw [closure_eq_self_union_frontier] at hcl
  rcases hcl with h | h
  · exact absurd h hnf
  · exact h

/-- A vertex on the frontier of the filled region does not lie in `N`. -/
theorem notMem_of_pos_mem_frontier (E : UCPlanar.PlaneEmbedding G)
    (hLF : E.LocallyFiniteFaces) {N : Set V} {x : V}
    (hx : E.pos x ∈ frontier (E.clusterRegion N)) : x ∉ N := by
  obtain ⟨F, hF, hinc⟩ := incident_facesAvoiding_of_pos_mem_frontier E hLF hx
  exact hF.2 x hinc

/-- The frontier of the filled region is part of the drawing. -/
theorem frontier_clusterRegion_subset_trace (Q : UCPlanar.PeriodicPlaneGraph V) (N : Set V)
    (hLF : Q.embedding.LocallyFiniteFaces) :
    frontier (Q.embedding.clusterRegion N) ⊆ Q.embedding.trace := by
  intro p hp
  obtain ⟨F, hF, hcl⟩ := exists_facesAvoiding_of_mem_frontier Q.embedding hLF hp
  have hop : IsOpen F := isOpen_isFace Q hF.1
  have hnF : p ∉ F := by
    intro hpF
    have hpc : p ∈ closure (Q.embedding.clusterRegion N) := hp.1
    obtain ⟨q, hqF, hqC⟩ := (mem_closure_iff.mp hpc) F hop hpF
    exact hqC (subset_closure (Set.subset_biUnion_of_mem (u := fun F => F) hF hqF))
  rw [closure_eq_self_union_frontier] at hcl
  rcases hcl with h | h
  · exact absurd h hnF
  · exact frontier_isFace_subset_trace Q hF.1 h

/-- The frontier of the filled region is covered by the arcs of the graph, so the only content
of the boundary edge set is that finitely many arcs, each lying wholly on the frontier, suffice. -/
theorem frontier_clusterRegion_subset_edgesTrace (Q : UCPlanar.PeriodicPlaneGraph V) (N : Set V)
    (hLF : Q.embedding.LocallyFiniteFaces) :
    frontier (Q.embedding.clusterRegion N) ⊆ Q.embedding.edgesTrace Q.graph.edgeSet := by
  rw [← trace_eq_edgesTrace Q]
  exact frontier_clusterRegion_subset_trace Q N hLF

/-- **The cycle surrounding the cluster of faces meeting `N`.**  When the filled region is
bounded and its frontier is drawn exactly by a finite edge set, that edge set carries a cycle
enclosing any prescribed vertex of `N`, and no vertex of the cycle lies in `N`. -/
theorem exists_surrounding_cycle (E : UCPlanar.PlaneEmbedding G)
    (hbc : E.HasBoundaryCycles) (hLF : E.LocallyFiniteFaces) {N : Set V} {x₀ : V} (hx₀ : x₀ ∈ N)
    (hbdd : Bornology.IsBounded (E.clusterRegion N))
    {T : Finset (Sym2 V)} (hT : ↑T ⊆ G.edgeSet)
    (hcover : frontier (E.clusterRegion N) ⊆ E.edgesTrace ↑T)
    (harc : ∀ e ∈ T, E.arcOf e ⊆ frontier (E.clusterRegion N)) :
    ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ (∀ e ∈ γ.edges, e ∈ T) ∧
      x₀ ∈ E.cycleRegion γ ∧ (∀ z ∈ γ.support, z ∉ N) ∧
      (∀ z ∈ γ.support, ∃ F ∈ E.facesAvoiding N, E.Incident F z) ∧
      E.pos x₀ ∈ insideOf (E.walkTrace γ) ∧
      E.walkTrace γ ⊆ frontier (E.clusterRegion N) := by
  obtain ⟨b, γ, hcyc, hedges, hreg, hfr, hin, hwt⟩ :=
    exists_cluster_cycle E hbc (isOpen_clusterRegion E N) hbdd
      (pos_mem_clusterRegion E hLF hx₀) hT hcover harc
  exact ⟨b, γ, hcyc, hedges, hreg,
    fun z hz => notMem_of_pos_mem_frontier E hLF (hfr z hz),
    fun z hz => incident_facesAvoiding_of_pos_mem_frontier E hLF (hfr z hz), hin, hwt⟩

end UCPlanar.Support
