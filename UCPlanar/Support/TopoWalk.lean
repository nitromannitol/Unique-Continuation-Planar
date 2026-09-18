/- Combinatorial facts about drawn walks: common points are common vertices. -/
import UCPlanar.Support.TopoBridge

open scoped Classical

namespace UCPlanar.Support

/-- A non-vertex point of a drawn walk lies on one of its drawn edges, whose two ends are in
the walk's support. -/
theorem exists_edge_of_mem_walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {a b : V} (q : G.Walk a b) {t : UCPlanar.Plane}
    (ht : t ∈ E.walkTrace q) (htv : t ∉ Set.range E.pos) :
    ∃ x y : V, ∃ h : G.Adj x y, t ∈ Set.range (E.edge h) ∧ x ∈ q.support ∧ y ∈ q.support := by
  induction q with
  | nil =>
      rw [UCPlanar.PlaneEmbedding.walkTrace] at ht
      simp only [Set.mem_singleton_iff] at ht
      subst ht
      exact absurd (Set.mem_range_self _) htv
  | @cons a c b h tail ih =>
      rw [UCPlanar.PlaneEmbedding.walkTrace, Set.mem_union] at ht
      rcases ht with ht | ht
      · exact ⟨a, c, h, ht, List.mem_cons_self,
          List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support tail)⟩
      · obtain ⟨x, y, k, hk, hx, hy⟩ := ih ht
        exact ⟨x, y, k, hk, List.mem_cons_of_mem a hx, List.mem_cons_of_mem a hy⟩

/-- Two drawn edges either have the same two ends, or their ranges meet only in the drawn ends
of the first. -/
theorem edge_range_inter_or_eq {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y u v : V} (h : G.Adj x y) (k : G.Adj u v) :
    Set.range (E.edge h) ∩ Set.range (E.edge k) ⊆ {E.pos x, E.pos y} ∨
      ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
  by_cases hd : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  · exact Or.inr hd
  · exact Or.inl (fun t ht => (E.edge_inter h k hd ht).1)


/-- A non-vertex point of a drawn walk lies on one of its drawn edges, and that edge is an edge
of the walk. -/
theorem exists_edge_of_mem_walkTrace_edges {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {a b : V} (q : G.Walk a b) {t : UCPlanar.Plane}
    (ht : t ∈ E.walkTrace q) (htv : t ∉ Set.range E.pos) :
    ∃ x y : V, ∃ h : G.Adj x y, t ∈ Set.range (E.edge h) ∧ x ∈ q.support ∧ y ∈ q.support ∧
      s(x, y) ∈ q.edges := by
  induction q with
  | nil =>
      rw [UCPlanar.PlaneEmbedding.walkTrace] at ht
      simp only [Set.mem_singleton_iff] at ht
      subst ht
      exact absurd (Set.mem_range_self _) htv
  | @cons a c b h tail ih =>
      rw [UCPlanar.PlaneEmbedding.walkTrace, Set.mem_union] at ht
      rcases ht with ht | ht
      · exact ⟨a, c, h, ht, List.mem_cons_self,
          List.mem_cons_of_mem a (SimpleGraph.Walk.start_mem_support tail),
          by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self⟩
      · obtain ⟨x, y, k, hk, hx, hy, hmem⟩ := ih ht
        exact ⟨x, y, k, hk, List.mem_cons_of_mem a hx, List.mem_cons_of_mem a hy,
          by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hmem⟩

/-- An edge whose two ends lie on a simple path, and which is not an edge of the path, meets the
path's trace only in its two drawn ends. -/
theorem edge_range_inter_walkTrace_subset_of_notMem_edges {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y a b : V} (h : G.Adj x y) (p : G.Walk a b)
    (hx : x ∈ p.support) (hy : y ∈ p.support) (hne : s(x, y) ∉ p.edges) :
    Set.range (E.edge h) ∩ E.walkTrace p ⊆ {E.pos x, E.pos y} := by
  intro t ht
  by_cases htv : t ∈ Set.range E.pos
  · obtain ⟨u, rfl⟩ := htv
    have hu : u ∈ p.support := (E.pos_mem_walkTrace_iff p u).mp ht.2
    rcases E.vertex_on_edge h u ht.1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · obtain ⟨u, v, k, hk, hu, hv, hmem⟩ := exists_edge_of_mem_walkTrace_edges E p ht.2 htv
    rcases UCPlanar.Support.edge_range_inter_or_eq E h k with hsub | hcase
    · exact hsub ⟨ht.1, hk⟩
    · exfalso
      rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne hmem
      · exact hne (by rwa [Sym2.eq_swap] at hmem)

/-- A common point of two drawn walks is a common vertex of the two walks. -/
theorem exists_common_vertex_of_walkTrace_inter {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {a b c d : V} (p : G.Walk a b) (q : G.Walk c d)
    {t : UCPlanar.Plane} (htp : t ∈ E.walkTrace p) (htq : t ∈ E.walkTrace q) :
    ∃ v ∈ p.support, v ∈ q.support := by
  by_cases htv : t ∈ Set.range E.pos
  · obtain ⟨v, rfl⟩ := htv
    exact ⟨v, (E.pos_mem_walkTrace_iff p v).mp htp, (E.pos_mem_walkTrace_iff q v).mp htq⟩
  · obtain ⟨x, y, h, hxh, hx, hy⟩ := exists_edge_of_mem_walkTrace E p htp htv
    obtain ⟨u, v, k, huk, hu, hv⟩ := exists_edge_of_mem_walkTrace E q htq htv
    have hmem : t ∈ Set.range (E.edge h) ∩ Set.range (E.edge k) := ⟨hxh, huk⟩
    rcases edge_range_inter_or_eq E h k with hsub | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hsub hmem with h' | h'
      · exact absurd ⟨x, h'.symm⟩ htv
      · exact absurd ⟨y, h'.symm⟩ htv
    · exact ⟨x, hx, hu⟩
    · exact ⟨x, hx, hv⟩

/-- The transported trace of a drawn cycle is a Jordan curve. -/
theorem isJordanCurve_topoTrace_cycle {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) (hγ : γ.IsCycle) :
    Schoenflies.IsJordanCurve (topoTrace E γ) := by
  cases γ with
  | nil => exact absurd SimpleGraph.Walk.Nil.nil hγ.not_nil
  | @cons o v o h τ =>
    have hcyc := (SimpleGraph.Walk.cons_isCycle_iff τ h).mp hγ
    have hτpath : τ.IsPath := hcyc.1
    have hne : s(o, v) ∉ τ.edges := hcyc.2
    have hlen : τ.length ≠ 0 := by
      intro h0
      rw [SimpleGraph.Walk.length_eq_zero_iff] at h0
      cases h0
      exact absurd rfl h.ne
    have hA := isArcBetween_edge E h
    have hB := isArcBetween_topoTrace_of_isPath E τ hτpath hlen
    have hmeet : ∀ z ∈ planeHomeo '' Set.range (E.edge h), z ∈ topoTrace E τ →
        z = planeHomeo (E.pos o) ∨ z = planeHomeo (E.pos v) := by
      intro z hz1 hz2
      obtain ⟨w, hw, rfl⟩ := hz1
      obtain ⟨w', hw', hww'⟩ := hz2
      have hww : w = w' := planeHomeo.injective hww'.symm
      subst hww
      have hw'' : w ∈ Set.range (E.edge h.symm) := by rwa [E.edge_symm h] at hw
      have hne' : s(v, o) ∉ τ.edges := by rw [Sym2.eq_swap]; exact hne
      have hmem := edge_range_inter_walkTrace_subset_of_notMem_edges E h.symm τ
        (SimpleGraph.Walk.start_mem_support τ) (SimpleGraph.Walk.end_mem_support τ) hne'
        ⟨hw'', hw'⟩
      rcases hmem with he | he
      · exact Or.inr (congrArg planeHomeo he)
      · exact Or.inl (congrArg planeHomeo he)
    have hJ := Schoenflies.IsJordanCurve.of_two_arcs hA hB hmeet
    rw [topoTrace, UCPlanar.PlaneEmbedding.walkTrace, Set.image_union]
    exact hJ
