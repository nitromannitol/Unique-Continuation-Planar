/- Incidence and separation of drawn graph walks. -/
import UCPlanar.Support.PlanarCycle
import Mathlib.Tactic

/-- A drawn walk passes through exactly its support vertices. -/
theorem UCPlanar.PlaneEmbedding.pos_mem_walkTrace_iff {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) (z : V) :
    E.pos z ∈ E.walkTrace p ↔ z ∈ p.support := by
  induction p with
  | nil => simp [walkTrace, E.pos_injective.eq_iff]
  | @cons x y w h p ih =>
    simp only [walkTrace, Set.mem_union, SimpleGraph.Walk.support_cons, List.mem_cons]
    constructor
    · rintro (he | hp)
      · rcases E.vertex_on_edge h z he with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr p.start_mem_support
      · exact Or.inr (ih.mp hp)
    · rintro (rfl | hp)
      · exact Or.inl ⟨0, (E.edge h).source⟩
      · exact Or.inr (ih.mpr hp)

/-- The trace of a finite graph walk is compact. -/
theorem UCPlanar.PlaneEmbedding.isCompact_walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) :
    IsCompact (E.walkTrace p) := by
  induction p with
  | nil => exact isCompact_singleton
  | cons h p ih => exact (isCompact_range (E.edge h).continuous).union ih

/-- Concatenation of walks takes the union of their geometric traces. -/
theorem UCPlanar.PlaneEmbedding.walkTrace_append {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    E.walkTrace (p.append q) = E.walkTrace p ∪ E.walkTrace q := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.nil_append, walkTrace]
    exact (Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr
      ((E.pos_mem_walkTrace_iff q _).mpr q.start_mem_support))).symm
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, walkTrace, ih, Set.union_assoc]

/-- Edges with four distinct endpoints have disjoint drawn ranges. -/
theorem UCPlanar.PlaneEmbedding.disjoint_edge_ranges {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y u v : V} (h : G.Adj x y) (k : G.Adj u v)
    (hxu : x ≠ u) (hxv : x ≠ v) (hyu : y ≠ u) (hyv : y ≠ v) :
    Disjoint (Set.range (E.edge h)) (Set.range (E.edge k)) := by
  apply Set.disjoint_left.mpr
  intro t ht hk
  have hn : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
    rintro (⟨h, _⟩ | ⟨h, _⟩)
    · exact hxu h
    · exact hxv h
  have hh := E.edge_inter h k hn ⟨ht, hk⟩
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hh
  rcases hh with ⟨hx | hy, hu | hv⟩
  · exact hxu (E.pos_injective (hx.symm.trans hu))
  · exact hxv (E.pos_injective (hx.symm.trans hv))
  · exact hyu (E.pos_injective (hy.symm.trans hu))
  · exact hyv (E.pos_injective (hy.symm.trans hv))

/-- An edge avoiding the vertices of a walk avoids its entire drawing. -/
theorem UCPlanar.PlaneEmbedding.disjoint_edge_walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {u v x y : V} (h : G.Adj u v) (p : G.Walk x y)
    (hu : u ∉ p.support) (hv : v ∉ p.support) :
    Disjoint (Set.range (E.edge h)) (E.walkTrace p) := by
  induction p with
  | @nil a =>
    apply Set.disjoint_left.mpr
    intro t ht hx
    have htx : t = E.pos a := hx
    rw [htx] at ht
    rcases E.vertex_on_edge h a ht with rfl | rfl
    · exact hu (by simp)
    · exact hv (by simp)
  | @cons x y z k p ih =>
    have hu' : u ∉ p.support := fun hm => hu (by simp [hm])
    have hv' : v ∉ p.support := fun hm => hv (by simp [hm])
    change Disjoint (Set.range (E.edge h)) (Set.range (E.edge k) ∪ E.walkTrace p)
    apply disjoint_sup_right.mpr
    refine ⟨E.disjoint_edge_ranges h k ?_ ?_ ?_ ?_, ih hu' hv'⟩
    · intro he; subst u; exact hu (by simp)
    · intro he; subst u; exact hu' p.start_mem_support
    · intro he; subst v; exact hv (by simp)
    · intro he; subst v; exact hv' p.start_mem_support

/-- Disjoint vertex supports give disjoint geometric walk traces. -/
theorem UCPlanar.PlaneEmbedding.disjoint_walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y u v : V} (p : G.Walk x y) (q : G.Walk u v)
    (hpq : ∀ z ∈ p.support, z ∉ q.support) :
    Disjoint (E.walkTrace p) (E.walkTrace q) := by
  induction p with
  | @nil a =>
    apply Set.disjoint_left.mpr
    intro t ht hq
    have ht' : t = E.pos a := ht
    rw [ht'] at hq
    exact hpq a (by simp) ((E.pos_mem_walkTrace_iff q a).mp hq)
  | cons h p ih =>
    apply disjoint_sup_left.mpr
    refine ⟨E.disjoint_edge_walkTrace h q ?_ ?_, ih ?_⟩
    · exact hpq _ (by simp)
    · exact hpq _ (by simp [p.start_mem_support])
    · intro z hz
      exact hpq z (by simp [hz])
