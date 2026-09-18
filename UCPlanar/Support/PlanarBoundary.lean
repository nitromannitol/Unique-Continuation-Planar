/- Boundary contacts and complementary components of plane walks. -/
import UCPlanar.Support.PlanarInterior
import Mathlib.Topology.Order.IntermediateValue

open scoped Classical

/-- Removing the source of an embedded edge leaves the image of the positive parameters. -/
theorem UCPlanar.PlaneEmbedding.edge_range_sdiff_source {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    Set.range (E.edge h) \ {E.pos x} = (E.edge h) '' Set.Ioi 0 := by
  ext t
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    refine ⟨s, ?_, rfl⟩
    apply lt_of_le_of_ne (show (0 : unitInterval) ≤ s from bot_le)
    intro he
    apply hs
    change E.edge h s = E.pos x
    rw [← he, (E.edge h).source]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    intro he
    have he' : E.edge h s = E.edge h 0 := he.trans (E.edge h).source.symm
    exact (ne_of_gt hs) (E.edge_injective h he')

/-- An edge with one endpoint off a walk meets its trace only at the other endpoint. -/
theorem UCPlanar.PlaneEmbedding.edge_inter_walkTrace_subset {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y a b : V} (h : G.Adj x y)
    (p : G.Walk a b) (hy : y ∉ p.support) :
    Set.range (E.edge h) ∩ E.walkTrace p ⊆ {E.pos x} := by
  induction p with
  | @nil a =>
    rintro t ⟨ht, ha⟩
    have he : t = E.pos a := ha
    rcases E.vertex_on_edge h a (he ▸ ht) with rfl | rfl
    · exact he
    · exact False.elim (hy (by simp))
  | @cons a b c k p ih =>
    have hy' : y ∉ p.support := fun ht => hy (by simp [ht])
    rintro t ⟨ht, hk | hp⟩
    · have hn : ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
        rintro (⟨_, rfl⟩ | ⟨_, rfl⟩)
        · exact hy (by simp [p.start_mem_support])
        · exact hy (by simp)
      have hh := (E.edge_inter h k hn ⟨ht, hk⟩).1
      rcases hh with he | he
      · exact he
      · exfalso
        apply hy
        apply (E.pos_mem_walkTrace_iff (SimpleGraph.Walk.cons k p) y).mp
        rw [← he]
        exact Or.inl hk
    · exact ih hy' ⟨ht, hp⟩

/-- An embedded edge remains connected after deleting its source. -/
theorem UCPlanar.PlaneEmbedding.isPreconnected_edge_without_source {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    IsPreconnected (Set.range (E.edge h) \ {E.pos x}) := by
  rw [E.edge_range_sdiff_source h]
  exact isPreconnected_Ioi.image _ (E.edge h).continuous.continuousOn

/-- Reversing a graph walk preserves its geometric trace. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_reverse {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) :
    E.walkTrace p.reverse = E.walkTrace p := by
  induction p with
  | nil => rfl
  | @cons x y z h p ih =>
    rw [SimpleGraph.Walk.reverse_cons,
      E.walkTrace_append, ih]
    change E.walkTrace p ∪ (Set.range (E.edge h.symm) ∪ {E.pos x}) =
      Set.range (E.edge h) ∪ E.walkTrace p
    rw [← E.edge_symm h]
    have hx : ({E.pos x} : Set UCPlanar.Plane) ⊆ Set.range (E.edge h) := by
      exact Set.singleton_subset_iff.mpr ⟨0, (E.edge h).source⟩
    rw [Set.union_eq_left.mpr hx, Set.union_comm]

/-- Deleting the start of a simple path leaves a connected trace. -/
theorem UCPlanar.PlaneEmbedding.isPreconnected_walkTrace_without_start {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) :
    IsPreconnected (E.walkTrace p \ {E.pos x}) := by
  cases p with
  | nil => simpa only [walkTrace, Set.sdiff_self] using
      (isPreconnected_empty : IsPreconnected (∅ : Set UCPlanar.Plane))
  | @cons x z y h p =>
    have hx : x ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp |>.2
    have hx' : E.pos x ∉ E.walkTrace p := fun ht => hx ((E.pos_mem_walkTrace_iff p x).mp ht)
    have he : E.walkTrace (SimpleGraph.Walk.cons h p) \ {E.pos x} =
        (Set.range (E.edge h) \ {E.pos x}) ∪ E.walkTrace p := by
      change (Set.range (E.edge h) ∪ E.walkTrace p) \ {E.pos x} = _
      ext t
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ha | hb, hn⟩
        · exact Or.inl ⟨ha, hn⟩
        · exact Or.inr hb
      · rintro (⟨ha, hn⟩ | hb)
        · exact ⟨Or.inl ha, hn⟩
        · exact ⟨Or.inr hb, fun ht => hx' (ht ▸ hb)⟩
    rw [he]
    apply (E.isPreconnected_edge_without_source h).union (E.pos z)
    · refine ⟨⟨1, (E.edge h).target⟩, ?_⟩
      intro he
      exact h.ne (E.pos_injective he).symm
    · exact (E.pos_mem_walkTrace_iff p z).mpr p.start_mem_support
    · exact E.isPreconnected_walkTrace p

/-- A path with only its initial vertex on a walk has no further geometric contact. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_without_start_avoids {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y a b : V}
    (p : G.Walk x y) (hp : p.IsPath) (γ : G.Walk a b)
    (hc : ∀ z ∈ p.support, z ∈ γ.support → z = x) :
    E.walkTrace p \ {E.pos x} ⊆ (E.walkTrace γ)ᶜ := by
  cases p with
  | nil => simp only [walkTrace, Set.sdiff_self, Set.empty_subset]
  | @cons x z y h p =>
    have hx : x ∉ p.support := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp |>.2
    have ha : ∀ t ∈ p.support, t ∉ γ.support := by
      intro t ht hg
      have he := hc t (by simp [ht]) hg
      exact hx (he ▸ ht)
    intro t ht hg
    rcases ht with ⟨he | ht, hn⟩
    · exact hn (E.edge_inter_walkTrace_subset h γ (ha z p.start_mem_support) ⟨he, hg⟩)
    · exact Set.disjoint_left.mp (E.disjoint_walkTrace p γ ha) ht hg

/-- All noninitial points of a boundary-contact path belong to the endpoint component. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_without_start_subset_component {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y a b : V}
    (p : G.Walk x y) (hp : p.IsPath) (γ : G.Walk a b) (hxy : x ≠ y)
    (hc : ∀ z ∈ p.support, z ∈ γ.support → z = x) :
    E.walkTrace p \ {E.pos x} ⊆ connectedComponentIn (E.walkTrace γ)ᶜ (E.pos y) := by
  apply (E.isPreconnected_walkTrace_without_start p hp).subset_connectedComponentIn
  · refine ⟨(E.pos_mem_walkTrace_iff p y).mpr p.end_mem_support, ?_⟩
    intro he
    exact hxy (E.pos_injective he).symm
  · exact E.walkTrace_without_start_avoids p hp γ hc

/-- The cycle trace together with all bounded complementary plane components. -/
def UCPlanar.PlaneEmbedding.closedCycleDomain {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) : Set UCPlanar.Plane :=
  {t | t ∈ E.walkTrace γ ∨ (t ∉ E.walkTrace γ ∧
    Bornology.IsBounded (connectedComponentIn (E.walkTrace γ)ᶜ t))}

/-- A simple path from the boundary to a strictly interior vertex has its full trace inside. -/
theorem UCPlanar.PlaneEmbedding.boundary_path_trace_subset_closedCycleDomain {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {o x y : V}
    (γ : G.Walk o o) (p : G.Walk x y) (hp : p.IsPath) (hx : x ∈ γ.support)
    (hy : y ∈ E.cycleRegion γ) (hy' : y ∉ γ.support)
    (hc : ∀ z ∈ p.support, z ∈ γ.support → z = x) :
    E.walkTrace p ⊆ E.closedCycleDomain γ := by
  have hxy : x ≠ y := by rintro rfl; exact hy' hx
  have hb : Bornology.IsBounded (connectedComponentIn (E.walkTrace γ)ᶜ (E.pos y)) := by
    exact (hy.resolve_left hy').2
  intro t ht
  by_cases he : t = E.pos x
  · exact Or.inl (he ▸ (E.pos_mem_walkTrace_iff γ x).mpr hx)
  · have hc' := E.walkTrace_without_start_subset_component p hp γ hxy hc ⟨ht, he⟩
    refine Or.inr ⟨connectedComponentIn_subset _ _ hc', ?_⟩
    rwa [← connectedComponentIn_eq hc']

/-- The geometric domain and the vertex region agree on drawn vertices. -/
theorem UCPlanar.PlaneEmbedding.pos_mem_closedCycleDomain_iff {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) (x : V) :
    E.pos x ∈ E.closedCycleDomain γ ↔ x ∈ E.cycleRegion γ := by
  simp only [closedCycleDomain, cycleRegion, Set.mem_setOf_eq, E.pos_mem_walkTrace_iff]

/-- Trimming a common zero path produces two attachments lying in the closed cycle domain. -/
theorem UCPlanar.PlaneEmbedding.exists_interior_sign_attachments {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {o z w p m : V}
    (γ : G.Walk o o) (β : G.Walk z w) (hβ : β.IsPath) (hz : z ∈ γ.support)
    (hp : p ∈ E.cycleRegion γ) (hp' : p ∉ γ.support) (hpβ : p ∉ β.support)
    (hm : m ∈ E.cycleRegion γ) (hm' : m ∉ γ.support) (hmβ : m ∉ β.support)
    (hwp : G.Adj w p) (hwm : G.Adj w m) :
    ∃ v ∈ γ.support, ∃ q : G.Walk v w, q.IsPath ∧ q.length ≤ β.length ∧
      (∀ t ∈ q.support, t ∈ β.support) ∧
      E.walkTrace (q.concat hwp) ⊆ E.closedCycleDomain γ ∧
      E.walkTrace (q.concat hwm) ⊆ E.closedCycleDomain γ := by
  obtain ⟨v, hv, q, hq, hlen, hs, hc⟩ := UCPlanar.Support.exists_last_boundary_tail β hβ
    γ.support.toFinset (List.mem_toFinset.mpr hz)
  have hv' : v ∈ γ.support := List.mem_toFinset.mp hv
  refine ⟨v, hv', q, hq, hlen, hs, ?_, ?_⟩
  · apply E.boundary_path_trace_subset_closedCycleDomain γ (q.concat hwp)
      (hq.concat (fun ht => hpβ (hs _ ht)) hwp) hv' hp hp'
    intro t ht hg
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hc t ht (List.mem_toFinset.mpr hg)
    · exact False.elim (hp' hg)
  · apply E.boundary_path_trace_subset_closedCycleDomain γ (q.concat hwm)
      (hq.concat (fun ht => hmβ (hs _ ht)) hwm) hv' hm hm'
    intro t ht hg
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hc t ht (List.mem_toFinset.mpr hg)
    · exact False.elim (hm' hg)

