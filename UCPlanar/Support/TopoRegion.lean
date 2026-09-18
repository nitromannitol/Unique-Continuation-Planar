/- The region a drawn closed walk encloses, read as a Jordan domain. -/
import UCPlanar.Support.TopoTransport
import UCPlanar.Support.TopoWalk

open Set

namespace UCPlanar.Support

/-- In the plane the complement of a bounded set is unbounded. -/
theorem not_isBounded_compl_of_isBounded {A : Set Schoenflies.Plane}
    (hA : Bornology.IsBounded A) : ¬ Bornology.IsBounded Aᶜ := by
  intro h
  have hu : Bornology.IsBounded (Set.univ : Set Schoenflies.Plane) := by
    have h2 := hA.union h
    rwa [Set.union_compl_self] at h2
  exact NormedSpace.unbounded_univ ℝ Schoenflies.Plane hu

/-- **A simple arc encloses nothing.**  Its complement is connected, hence is the single
unbounded component. -/
theorem inside_eq_empty_of_isArc {A : Set Schoenflies.Plane} (hA : Schoenflies.IsArc A) :
    Schoenflies.inside A = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hz, hb⟩
  have hconn : IsConnected Aᶜ := Schoenflies.arc_complement hA
  rw [hconn.isPreconnected.connectedComponentIn hz] at hb
  exact not_isBounded_compl_of_isBounded hA.isCompact.isBounded hb

/-- Enlarging a set can only enlarge the region it encloses. -/
theorem insideOf_sdiff_subset {X : Type*} [TopologicalSpace X] [Bornology X]
    {S T : Set X} (h : S ⊆ T) : insideOf S \ T ⊆ insideOf T := by
  rintro x ⟨⟨hxS, hb⟩, hxT⟩
  refine ⟨hxT, hb.subset ?_⟩
  exact connectedComponentIn_mono x (Set.compl_subset_compl.mpr h)

/-- **The region of a drawn closed walk is the Jordan domain of its transported trace.** -/
theorem mem_cycleRegion_iff_inside {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) (x : V) :
    x ∈ E.cycleRegion γ ↔
      x ∈ γ.support ∨ planeHomeo (E.pos x) ∈ Schoenflies.inside (topoTrace E γ) := by
  have hkey : planeHomeo '' insideOf (E.walkTrace γ) = insideOf (topoTrace E γ) :=
    image_insideOf planeHomeo (E.walkTrace γ)
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← insideOf_eq_inside, ← hkey]
      exact Set.mem_image_of_mem _ h
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ?_
      rw [← insideOf_eq_inside, ← hkey] at h
      obtain ⟨y, hy, hyx⟩ := h
      rwa [planeHomeo.injective hyx] at hy

/-- A drawn closed walk whose trace is a simple arc encloses only its own vertices. -/
theorem cycleRegion_eq_support_of_isArc {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o)
    (hA : Schoenflies.IsArc (topoTrace E γ)) :
    E.cycleRegion γ = {x | x ∈ γ.support} := by
  ext x
  rw [mem_cycleRegion_iff_inside, inside_eq_empty_of_isArc hA]
  simp

/-- **The enclosed region is a graph separator.**  A walk from a vertex of the region to a
vertex outside it passes through the closed walk. -/
theorem exists_mem_support_of_cycleRegion {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y o : V} (p : G.Walk x y) (γ : G.Walk o o)
    (hx : x ∈ E.cycleRegion γ) (hy : y ∉ E.cycleRegion γ) :
    ∃ z ∈ p.support, z ∈ γ.support := by
  by_contra hcon
  have hcon' : ∀ z ∈ p.support, z ∉ γ.support := fun z hz hz2 => hcon ⟨z, hz, hz2⟩
  have hmain := E.walkTrace_in_bounded_cycle_component p γ hcon' hx
  exact hy (Or.inr (hmain (E.pos y) ((E.pos_mem_walkTrace_iff p y).mpr p.end_mem_support)))

/-- A closed walk drawn inside the trace of another encloses no more than it does. -/
theorem cycleRegion_mono {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o b : V} (γ : G.Walk o o) (δ : G.Walk b b)
    (h : E.walkTrace γ ⊆ E.walkTrace δ) : E.cycleRegion γ ⊆ E.cycleRegion δ := by
  intro x hx
  by_cases hxδ : x ∈ δ.support
  · exact Or.inl hxδ
  · have hpos : E.pos x ∉ E.walkTrace δ := fun hc =>
      hxδ ((E.pos_mem_walkTrace_iff δ x).mp hc)
    rcases hx with hx | hx
    · exact absurd (h ((E.pos_mem_walkTrace_iff γ x).mpr hx)) hpos
    · exact Or.inr (insideOf_sdiff_subset h ⟨hx, hpos⟩)

/-- Retracing a walk backwards adds nothing to its trace. -/
theorem walkTrace_append_reverse {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) :
    E.walkTrace (p.append p.reverse) = E.walkTrace p := by
  rw [E.walkTrace_append, E.walkTrace_reverse, Set.union_self]

/-- **A there-and-back closed walk encloses nothing.**  Its trace is the arc drawn by the
underlying simple path. -/
theorem cycleRegion_append_reverse {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (hne : p.length ≠ 0) :
    E.cycleRegion (p.append p.reverse) = {z | z ∈ (p.append p.reverse).support} := by
  refine cycleRegion_eq_support_of_isArc E _ ?_
  have harc := isArcBetween_topoTrace_of_isPath E p hp hne
  have : topoTrace E (p.append p.reverse) = topoTrace E p := by
    rw [topoTrace, topoTrace, walkTrace_append_reverse]
  rw [this]
  exact harc.isArc

/-- The drawn trace of a cycle separates the plane. -/
theorem isSeparating_topoTrace_cycle {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) (hγ : γ.IsCycle) :
    Schoenflies.IsSeparating (topoTrace E γ) :=
  Schoenflies.jordan_curve_theorem (isJordanCurve_topoTrace_cycle E γ hγ)

end UCPlanar.Support
