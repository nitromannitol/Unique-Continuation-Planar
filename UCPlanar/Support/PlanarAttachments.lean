/- Short interior attachments and access to the boundary. -/
import UCPlanar.Support.PlanarBoundary
import UCPlanar.Support.PlanarMetric
import UCPlanar.Support.PlanarComponents

open scoped Classical

/-- A short path remote from the boundary complement can contact the boundary only in `Z`. -/
theorem UCPlanar.Support.short_path_boundary_contact_mem {V : Type*} {G : SimpleGraph V}
    {x y : V} (p : G.Walk x y) (B Z : Finset V) (L : ℕ) (hp : p.length ≤ L)
    (hfar : ∀ b ∈ B \ Z, L < G.dist x b) :
    ∀ z ∈ p.support, z ∈ B → z ∈ Z := by
  intro z hz hzB
  by_contra hn
  have hd := UCPlanar.Support.dist_le_length_of_mem_support p hz
  have hf := hfar z (Finset.mem_sdiff.mpr ⟨hzB, hn⟩)
  omega

/-- A nearby vertex outside `Z` cannot lie on a remote boundary. -/
theorem UCPlanar.Support.near_vertex_not_boundary {V : Type*} {G : SimpleGraph V}
    {x y : V} (B Z : Finset V) (L : ℕ)
    (hfar : ∀ b ∈ B \ Z, L < G.dist x b) (hy : y ∉ Z) (hxy : G.dist x y ≤ L) :
    y ∉ B := by
  intro hb
  have hf := hfar y (Finset.mem_sdiff.mpr ⟨hb, hy⟩)
  omega

/-- Remote face attachments can be based on `Z` with both complete traces in the bounded domain. -/
theorem UCPlanar.PlaneEmbedding.remote_facePathToSigns_interior {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {o z : V}
    (γ : G.Walk o o) (Z : Finset V) (P M : Set V) (L : ℕ) (hL : E.FaceBound L)
    (hz : z ∈ Z) (hZ : Z ⊆ γ.support.toFinset)
    (hZP : Disjoint (Z : Set V) P) (hZM : Disjoint (Z : Set V) M)
    (hP : P ⊆ E.cycleRegion γ) (hM : M ⊆ E.cycleRegion γ)
    (hface : E.FacePathToSigns P M z)
    (hfar : ∀ b ∈ γ.support.toFinset \ Z, L < G.dist z b) :
    ∃ v ∈ Z, ∃ w p m, ∃ β : G.Walk v w, β.IsPath ∧ β.length < L ∧
      (∀ t ∈ β.support, t ∉ P ∪ M ∧ G.dist z t ≤ L) ∧
      p ∈ P ∧ m ∈ M ∧ G.dist z p ≤ L ∧ G.dist z m ≤ L ∧
      ∃ hwp : G.Adj w p, ∃ hwm : G.Adj w m,
        E.walkTrace (β.concat hwp) ⊆ E.closedCycleDomain γ ∧
        E.walkTrace (β.concat hwm) ⊆ E.closedCycleDomain γ := by
  obtain ⟨w, β, hβ, hlen, ha, ⟨p, hp, hwp, hdp⟩, ⟨m, hm, hwm, hdm⟩⟩ :=
    E.facePathToSigns_metric hface L hL
  have hpZ : p ∉ Z := fun ht => Set.disjoint_left.mp hZP ht hp
  have hmZ : m ∉ Z := fun ht => Set.disjoint_left.mp hZM ht hm
  have hpγ : p ∉ γ.support := fun ht =>
    UCPlanar.Support.near_vertex_not_boundary γ.support.toFinset Z L hfar hpZ hdp
      (List.mem_toFinset.mpr ht)
  have hmγ : m ∉ γ.support := fun ht =>
    UCPlanar.Support.near_vertex_not_boundary γ.support.toFinset Z L hfar hmZ hdm
      (List.mem_toFinset.mpr ht)
  obtain ⟨v, hv, q, hq, hql, hs, htp, htm⟩ := E.exists_interior_sign_attachments
    γ β hβ (List.mem_toFinset.mp (hZ hz)) (hP hp) hpγ
    (fun ht => ha p ht (Or.inl hp)) (hM hm) hmγ
    (fun ht => ha m ht (Or.inr hm)) hwp hwm
  have hvZ : v ∈ Z := UCPlanar.Support.short_path_boundary_contact_mem β
    γ.support.toFinset Z L hlen.le hfar v (hs v q.start_mem_support)
    (List.mem_toFinset.mpr hv)
  refine ⟨v, hvZ, w, p, m, q, hq, hql.trans_lt hlen, ?_, hp, hm, hdp, hdm,
    hwp, hwm, htp, htm⟩
  intro t ht
  exact ⟨ha t (hs t ht),
    (UCPlanar.Support.dist_le_length_of_mem_support β (hs t ht)).trans hlen.le⟩

/-- Every sign vertex has an interior path from a boundary vertex of its sign component. -/
theorem UCPlanar.PlaneEmbedding.exists_sign_boundary_access {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {o : V}
    (γ : G.Walk o o) (S : Set V) (hS : S ⊆ E.cycleRegion γ)
    (hB : UCPlanar.ComponentsMeetBoundary G S {v | v ∈ γ.support}) (x : S) :
    ∃ y : S, y.val ∈ γ.support ∧ ∃ p : G.Walk y.val x.val,
      p.IsPath ∧ (∀ z ∈ p.support, z ∈ S) ∧
      E.walkTrace p ⊆ E.closedCycleDomain γ := by
  by_cases hx : x.val ∈ γ.support
  · refine ⟨x, hx, .nil, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
    · intro z hz
      have he : z = x.val := List.mem_singleton.mp hz
      exact he ▸ x.property
    · intro t ht
      have he : t = E.pos x.val := ht
      exact Or.inl (he ▸ (E.pos_mem_walkTrace_iff γ x.val).mpr hx)
  · obtain ⟨y, hy, hr⟩ := hB x
    obtain ⟨p, hp⟩ := hr.exists_isPath
    let φ : G.induce S →g G := ⟨Subtype.val, fun h => h⟩
    let q : G.Walk x.val y.val := p.map φ
    have hq : q.IsPath := hp.map (f := φ) Subtype.val_injective
    have hs : ∀ z ∈ q.reverse.support, z ∈ S := by
      intro z hz
      simp only [SimpleGraph.Walk.support_reverse, List.mem_reverse, q,
        SimpleGraph.Walk.support_map, List.mem_map] at hz
      obtain ⟨t, _, rfl⟩ := hz
      exact t.property
    obtain ⟨v, hv, r, hpath, _, hsub, hc⟩ := UCPlanar.Support.exists_last_boundary_tail
      q.reverse hq.reverse γ.support.toFinset (List.mem_toFinset.mpr hy)
    have hvS := hs v (hsub v r.start_mem_support)
    refine ⟨⟨v, hvS⟩, List.mem_toFinset.mp hv, r, hpath,
      fun z hz => hs z (hsub z hz), ?_⟩
    exact E.boundary_path_trace_subset_closedCycleDomain γ r hpath
      (List.mem_toFinset.mp hv) (hS x.property) hx
      (fun z hz hzg => hc z hz (List.mem_toFinset.mpr hzg))

