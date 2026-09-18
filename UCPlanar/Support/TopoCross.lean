/- Interleaved chords of a drawn cycle share a vertex. -/
import UCPlanar.Support.TopoCycleArcs
import UCPlanar.Support.TopoGenCrosscut

open Set SimpleGraph

open scoped Classical

namespace UCPlanar.Support

/-- An edge of a walk joins two consecutive vertices of it. -/
theorem mem_edges_iff_getVert {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    ∃ m, m < p.length ∧ e = s(p.getVert m, p.getVert (m + 1)) := by
  rw [SimpleGraph.Walk.edges, List.mem_map] at he
  obtain ⟨d, hd, hde⟩ := he
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hd
  refine ⟨n, ?_, ?_⟩
  · rw [← SimpleGraph.Walk.length_darts]
    exact hn
  · rw [← hde, SimpleGraph.Walk.darts_getElem_eq_getVert n hn]
    rfl

/-- Two vertices of a cycle that are not consecutive on it are not joined by one of its
edges. -/
theorem cycle_edge_not_mem {V : Type*} {G : SimpleGraph V} {o : V}
    (γ : G.Walk o o) (hγ : γ.IsCycle) {a b : ℕ} (hab : a + 1 < b) (hb : b < γ.length)
    (hwrap : 0 < a ∨ b + 1 < γ.length) :
    s(γ.getVert a, γ.getVert b) ∉ γ.edges := by
  intro hmem
  have hinj : ∀ m m' : ℕ, m ≤ γ.length - 1 → m' ≤ γ.length - 1 →
      γ.getVert m = γ.getVert m' → m = m' :=
    fun m m' hm hm' h => hγ.getVert_injOn' (by simpa using hm) (by simpa using hm') h
  have hzero : γ.getVert γ.length = γ.getVert 0 := by
    rw [SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
  obtain ⟨m, hm, hme⟩ := mem_edges_iff_getVert γ hmem
  rw [Sym2.eq_iff] at hme
  rcases hme with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hma : a = m := hinj a m (by omega) (by omega) h1
    have : b = m + 1 := hinj b (m + 1) (by omega) (by omega) h2
    omega
  · have hmb : b = m := hinj b m (by omega) (by omega) h2
    by_cases hml : m + 1 = γ.length
    · rw [hml, hzero] at h1
      have : a = 0 := hinj a 0 (by omega) (by omega) h1
      omega
    · have : a = m + 1 := hinj a (m + 1) (by omega) (by omega) h1
      omega

/-- **Two chords of a drawn cycle whose four ends interleave around it share a vertex.** -/
theorem exists_common_vertex_of_chords {V : Type*} {G : SimpleGraph V} {o : V}
    (E : UCPlanar.PlaneEmbedding G) (γ : G.Walk o o) (hγ : γ.IsCycle) {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < γ.length)
    (p : G.Walk (γ.getVert i) (γ.getVert k)) (q : G.Walk (γ.getVert j) (γ.getVert l))
    (hpd : E.walkTrace p ⊆ E.closedCycleDomain γ)
    (hqd : E.walkTrace q ⊆ E.closedCycleDomain γ)
    (hcp : IsChord γ p) (hcq : IsChord γ q) :
    ∃ v ∈ p.support, v ∈ q.support := by
  classical
  have hinj : ∀ m m' : ℕ, m ≤ γ.length - 1 → m' ≤ γ.length - 1 →
      γ.getVert m = γ.getVert m' → m = m' :=
    fun m m' hm hm' h => hγ.getVert_injOn' (by simpa using hm) (by simpa using hm') h
  -- the two chords, made simple
  have hp'sup : ∀ v ∈ p.bypass.support, v ∈ p.support := fun v hv => p.support_bypass_subset_support hv
  have hq'sup : ∀ v ∈ q.bypass.support, v ∈ q.support := fun v hv => q.support_bypass_subset_support hv
  have hp'tr : E.walkTrace p.bypass ⊆ E.closedCycleDomain γ :=
    (walkTrace_bypass_subset E p).trans hpd
  have hq'tr : E.walkTrace q.bypass ⊆ E.closedCycleDomain γ :=
    (walkTrace_bypass_subset E q).trans hqd
  have hcp' : IsChord γ p.bypass := fun v hv hg => hcp v (hp'sup v hv) hg
  have hcq' : IsChord γ q.bypass := fun v hv hg => hcq v (hq'sup v hv) hg
  have hik : γ.getVert i ≠ γ.getVert k := fun h => by
    have := hinj i k (by omega) (by omega) h; omega
  have hjl : γ.getVert j ≠ γ.getVert l := fun h => by
    have := hinj j l (by omega) (by omega) h; omega
  have hplen : p.bypass.length ≠ 0 := fun h0 => hik (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  have hqlen : q.bypass.length ≠ 0 := fun h0 => hjl (SimpleGraph.Walk.eq_of_length_eq_zero h0)
  -- the two chords do not run along the cycle
  have hepk : s(γ.getVert i, γ.getVert k) ∉ γ.edges :=
    cycle_edge_not_mem γ hγ (by omega) (by omega) (Or.inr (by omega))
  have heql : s(γ.getVert j, γ.getVert l) ∉ γ.edges :=
    cycle_edge_not_mem γ hγ (by omega) (by omega) (Or.inl (by omega))
  -- the interiors of the chords lie strictly inside the cycle
  have hinside : ∀ {x y : V} (w : G.Walk x y), IsChord γ w → s(x, y) ∉ γ.edges →
      E.walkTrace w ⊆ E.closedCycleDomain γ →
      topoTrace E w \ ({planeHomeo (E.pos x), planeHomeo (E.pos y)} : Set Schoenflies.Plane)
        ⊆ Schoenflies.inside (topoTrace E γ) := by
    intro x y w hch hxy hsub
    have hset : topoTrace E w \ ({planeHomeo (E.pos x), planeHomeo (E.pos y)} :
        Set Schoenflies.Plane)
        = planeHomeo '' (E.walkTrace w \ ({E.pos x, E.pos y} : Set UCPlanar.Plane)) := by
      rw [Set.image_sdiff planeHomeo.injective, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [hset, ← insideOf_eq_inside, topoTrace, ← image_insideOf planeHomeo (E.walkTrace γ)]
    exact Set.image_mono (chord_trace_diff_subset_inside E γ w hch hxy hsub)
  -- the crosscut configuration
  obtain ⟨A₁, A₂, hcut, hjA₁, hjA₂, hlA₂, hlA₁⟩ := exists_cutPair_cycle E γ hγ hij hjk hkl hl
  obtain ⟨z, hzQ, hzP⟩ := alternating_inter_nonempty_arc
    (isJordanCurve_topoTrace_cycle E γ hγ)
    (isArcBetween_topoTrace_of_isPath E p.bypass p.bypass_isPath hplen)
    (hinside p.bypass hcp' hepk hp'tr)
    (Set.mem_image_of_mem _ ((E.pos_mem_walkTrace_iff γ _).mpr (γ.getVert_mem_support i)))
    (Set.mem_image_of_mem _ ((E.pos_mem_walkTrace_iff γ _).mpr (γ.getVert_mem_support k)))
    hcut
    (isArcBetween_topoTrace_of_isPath E q.bypass q.bypass_isPath hqlen).isPreconnected_diff
    (hinside q.bypass hcq' heql hq'tr)
    (isArcBetween_topoTrace_of_isPath E q.bypass q.bypass_isPath hqlen).left_mem_closure_diff
    (isArcBetween_topoTrace_of_isPath E q.bypass q.bypass_isPath hqlen).right_mem_closure_diff
    hjA₁ hjA₂ hlA₂ hlA₁
  obtain ⟨t, htq, rfl⟩ := hzQ.1
  obtain ⟨t', htp, htt⟩ := hzP
  have htt' : t' = t := planeHomeo.injective htt
  subst htt'
  obtain ⟨v, hv₁, hv₂⟩ := exists_common_vertex_of_walkTrace_inter E p.bypass q.bypass htp htq
  exact ⟨v, hp'sup v hv₁, hq'sup v hv₂⟩

end UCPlanar.Support
