/- Transport of drawn traces to the Euclidean plane of the Jordan-curve development. -/
import UCPlanar.Support.PlanarBoundary
import Schoenflies.JordanClosed
import Schoenflies.GeneralCrosscut

open scoped Classical

namespace UCPlanar.Support

/-- The transported trace of a drawn walk. -/
def topoTrace {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {x y : V} (p : G.Walk x y) : Set Schoenflies.Plane := planeHomeo '' E.walkTrace p

/-- The transported trace of a drawn edge is an arc between the transported endpoints. -/
theorem isArcBetween_edge {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {x y : V} (h : G.Adj x y) :
    Schoenflies.IsArcBetween (planeHomeo '' Set.range (E.edge h)) (planeHomeo (E.pos x))
      (planeHomeo (E.pos y)) := by
  refine ⟨fun t => planeHomeo ((E.edge h).extend t),
    planeHomeo.continuous.comp (E.edge h).continuous_extend |>.continuousOn, ?_, ?_,
    by simp, by simp⟩
  · intro s hs t ht hst
    simp only at hst
    have h2 : (E.edge h).extend s = (E.edge h).extend t := planeHomeo.injective hst
    rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at h2
    exact Subtype.ext_iff.mp (E.edge_injective h h2)
  · rw [Set.image_eq_range]
    rw [show (fun t : unitInterval => planeHomeo ((E.edge h).extend ↑t)) =
        (planeHomeo ∘ (E.edge h)) from
      funext fun t => congrArg planeHomeo (Path.extend_extends' _ t)]
    exact Set.range_comp _ _

/-- The transported trace of a drawn walk is preconnected. -/
theorem isPreconnected_topoTrace {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {x y : V} (p : G.Walk x y) : IsPreconnected (topoTrace E p) := by
  exact (E.isPreconnected_walkTrace p).image _ planeHomeo.continuous.continuousOn

/-- The transported trace of a drawn walk is compact. -/
theorem isCompact_topoTrace {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {x y : V} (p : G.Walk x y) : IsCompact (topoTrace E p) := by
  exact (E.isCompact_walkTrace p).image planeHomeo.continuous

/-- The transported trace of a drawn walk is closed. -/
theorem isClosed_topoTrace {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {x y : V} (p : G.Walk x y) : IsClosed (topoTrace E p) := by
  exact (E.isCompact_walkTrace p).image planeHomeo.continuous |>.isClosed

/-- The transported trace of a drawn walk contains the transported start vertex. -/
theorem pos_mem_topoTrace {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    {x y : V} (p : G.Walk x y) : planeHomeo (E.pos x) ∈ topoTrace E p := by
  exact Set.mem_image_of_mem _ ((E.pos_mem_walkTrace_iff p x).mpr (SimpleGraph.Walk.start_mem_support p))

/-- The transported trace of a drawn walk is contained in the transported closed cycle domain. -/
theorem topoTrace_subset_topologicalDomain {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) {x y : V} (p : G.Walk x y)
    (h : E.walkTrace p ⊆ E.closedCycleDomain γ) :
    topoTrace E p ⊆ planeHomeo '' E.closedCycleDomain γ := by
  exact Set.image_mono h

/-- The transported trace of a simple drawn path is an arc between its endpoints. -/
theorem isArcBetween_topoTrace_of_isPath {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (hne : p.length ≠ 0) :
    Schoenflies.IsArcBetween (topoTrace E p) (planeHomeo (E.pos x)) (planeHomeo (E.pos y)) := by
  induction p with
  | nil => exact absurd rfl hne
  | @cons x z y h q ih =>
    have hqpath : q.IsPath := hp.of_cons
    have hxq : x ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff h q).mp hp).2
    cases q with
    | nil =>
      have hsub : ({E.pos z} : Set UCPlanar.Plane) ⊆ Set.range (E.edge h) :=
        Set.singleton_subset_iff.mpr ⟨1, (E.edge h).target⟩
      have hwt : E.walkTrace (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) =
          Set.range (E.edge h) := by
        simp only [UCPlanar.PlaneEmbedding.walkTrace]
        exact Set.union_eq_left.mpr hsub
      rw [topoTrace, hwt]
      exact isArcBetween_edge E h
    | cons h' q' =>
      have harc : Schoenflies.IsArcBetween (topoTrace E (SimpleGraph.Walk.cons h' q'))
          (planeHomeo (E.pos z)) (planeHomeo (E.pos y)) := ih hqpath (by simp)
      have hside : ∀ w ∈ planeHomeo '' Set.range (E.edge h),
          w ∈ topoTrace E (SimpleGraph.Walk.cons h' q') → w = planeHomeo (E.pos z) := by
        intro w hw1 hw2
        obtain ⟨u, hu, rfl⟩ := hw1
        obtain ⟨v, hv, huv⟩ := hw2
        have huv' : u = v := planeHomeo.injective huv.symm
        subst huv'
        have hmem : u ∈ Set.range (E.edge h) ∩
            E.walkTrace (SimpleGraph.Walk.cons h' q') := ⟨hu, hv⟩
        have hinter := E.edge_inter_walkTrace_subset h.symm
          (SimpleGraph.Walk.cons h' q') hxq
        rw [← E.edge_symm h] at hinter
        have h1 := hinter hmem
        simp only [Set.mem_singleton_iff] at h1
        rw [h1]
      have hglue := (isArcBetween_edge E h).concatenate harc hside
      convert hglue using 2
      simp only [topoTrace, UCPlanar.PlaneEmbedding.walkTrace, Set.image_union]

end UCPlanar.Support
