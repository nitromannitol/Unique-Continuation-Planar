/- Connected traces in complementary regions of a drawn cycle. -/
import UCPlanar.Support.PlanarTrace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

open scoped Classical

/-- The geometric trace of a walk is connected. -/
theorem UCPlanar.PlaneEmbedding.isPreconnected_walkTrace {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) :
    IsPreconnected (E.walkTrace p) := by
  induction p with
  | nil => exact isPreconnected_singleton
  | @cons x y z h p ih =>
    exact (isPreconnected_range (E.edge h).continuous).union (E.pos y)
      ⟨1, (E.edge h).target⟩ ((E.pos_mem_walkTrace_iff p y).mpr p.start_mem_support) ih

/-- A walk avoiding a cycle stays in one complementary plane component. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_subset_cycleComponent {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y o : V}
    (p : G.Walk x y) (γ : G.Walk o o)
    (ha : ∀ z ∈ p.support, z ∉ γ.support) :
    E.walkTrace p ⊆ connectedComponentIn (E.walkTrace γ)ᶜ (E.pos x) := by
  apply (E.isPreconnected_walkTrace p).subset_connectedComponentIn
    ((E.pos_mem_walkTrace_iff p x).mpr p.start_mem_support)
  intro t ht
  exact Set.disjoint_left.mp (E.disjoint_walkTrace p γ ha) ht

/-- A cycle-avoiding walk starting inside has its full trace in the bounded region. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_in_bounded_cycle_component {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y o : V}
    (p : G.Walk x y) (γ : G.Walk o o)
    (ha : ∀ z ∈ p.support, z ∉ γ.support) (hx : x ∈ E.cycleRegion γ) :
    ∀ t ∈ E.walkTrace p, t ∉ E.walkTrace γ ∧
      Bornology.IsBounded (connectedComponentIn (E.walkTrace γ)ᶜ t) := by
  rcases hx with hx | ⟨_, hb⟩
  · exact False.elim (ha x p.start_mem_support hx)
  · intro t ht
    have hc := E.walkTrace_subset_cycleComponent p γ ha ht
    refine ⟨connectedComponentIn_subset _ _ hc, ?_⟩
    rwa [← connectedComponentIn_eq hc]

/-- A simple path has a terminal subpath meeting the boundary only at its start. -/
theorem UCPlanar.Support.exists_last_boundary_tail {V : Type*}
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (B : Finset V) (hx : x ∈ B) :
    ∃ z ∈ B, ∃ q : G.Walk z y, q.IsPath ∧ q.length ≤ p.length ∧
      (∀ t ∈ q.support, t ∈ p.support) ∧
      (∀ t ∈ q.support, t ∈ B → t = z) := by
  classical
  have hn : (B.filter (fun t => t ∈ p.reverse.support)).Nonempty := by
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using p.start_mem_support
  obtain ⟨z, hz, hzp, hfirst⟩ := p.reverse.exists_mem_support_forall_mem_support_imp_eq B hn
  refine ⟨z, hz, (p.reverse.takeUntil z hzp).reverse,
    (hp.reverse.takeUntil hzp).reverse, ?_, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.length_reverse] using
      p.reverse.length_takeUntil_le_length hzp
  · intro t ht
    have hq : t ∈ (p.reverse.takeUntil z hzp).support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ht
    have hr := p.reverse.support_takeUntil_subset_support hzp hq
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hr
  · intro t ht htB
    apply hfirst t htB
    simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ht
