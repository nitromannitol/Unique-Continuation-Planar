/- Step 3 of Section 3 run on the connected component of the filled cluster through the chosen
vertex: the cycle is then drawn on the frontier of that component, every one of its vertices is
incident to a face of the component, and the face path of the topological lemma follows from the
face walks. -/
import UCPlanar.Support.TopoClusterFace
import UCPlanar.Support.TopoStep3
import Mathlib

open Set
open scoped Classical

/-- **The frontier of the cluster component through a vertex is drawn by a finite edge set.**
Some finite set of edges covers the frontier of the connected component of the filled region
through the drawing of `x₀`, and each of its arcs lies on that frontier. -/
def UCPlanar.PlaneEmbedding.HasComponentBoundary {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (N : Set V) (x₀ : V) : Prop :=
  ∃ T : Finset (Sym2 V), ↑T ⊆ G.edgeSet ∧
    frontier (connectedComponentIn (E.clusterRegion N) (E.pos x₀)) ⊆ E.edgesTrace ↑T ∧
    ∀ e ∈ T, E.arcOf e ⊆ frontier (connectedComponentIn (E.clusterRegion N) (E.pos x₀))

namespace UCPlanar.Support

variable {V : Type*}

/-- **The cycle around the cluster component.**  It encloses `x₀`, avoids `N`, and is drawn on the
frontier of the component, hence also on the frontier of the whole filled region. -/
theorem exists_component_cycle (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles) {N : Set V} {x₀ : V} (hx₀ : x₀ ∈ N)
    (hbdd : Bornology.IsBounded (Q.embedding.clusterRegion N))
    (hcb : Q.embedding.HasComponentBoundary N x₀) :
    ∃ (b : V) (γ : Q.graph.Walk b b), γ.IsCycle ∧ x₀ ∈ Q.embedding.cycleRegion γ ∧
      (∀ z ∈ γ.support, z ∉ N) ∧
      Q.embedding.pos x₀ ∈ insideOf (Q.embedding.walkTrace γ) ∧
      Q.embedding.walkTrace γ ⊆
        frontier (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)) ∧
      ∀ z ∈ γ.support, Q.embedding.pos z ∈ frontier (Q.embedding.clusterRegion N) := by
  obtain ⟨T, hT, hcover, harc⟩ := hcb
  have hx₀c : Q.embedding.pos x₀ ∈ Q.embedding.clusterRegion N :=
    pos_mem_clusterRegion Q.embedding (locallyFiniteFaces Q) hx₀
  have hOmOpen : IsOpen (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)) :=
    (isOpen_clusterRegion Q.embedding N).connectedComponentIn
  have hOmB : Bornology.IsBounded
      (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)) :=
    hbdd.subset (connectedComponentIn_subset _ _)
  obtain ⟨b, γ, hcyc, -, hreg, hfr, hin, hwt⟩ :=
    exists_cluster_cycle Q.embedding hbc hOmOpen hOmB (mem_connectedComponentIn hx₀c) hT
      hcover harc
  have hfrsub : frontier (connectedComponentIn (Q.embedding.clusterRegion N)
      (Q.embedding.pos x₀)) ⊆ frontier (Q.embedding.clusterRegion N) :=
    frontier_connectedComponentIn_subset (isOpen_clusterRegion Q.embedding N) _
  exact ⟨b, γ, hcyc, hreg,
    fun z hz => notMem_of_pos_mem_frontier Q.embedding (locallyFiniteFaces Q) (hfrsub (hfr z hz)),
    hin, hwt, fun z hz => hfrsub (hfr z hz)⟩

/-- **Step 3 of Section 3 for the zero case, run on the neighbour-buffered cluster in the ball.**
The cluster is taken around the vertices inside the ball of radius `m` that are nonzero or have a
nonzero neighbour.  A vertex of the cycle inside that ball therefore has no nonzero neighbour,
and one outside it that does have a nonzero neighbour sits in the buffer of the sphere, where the
conclusion asks nothing of it: its nonzero neighbour is within the buffer of a vertex of the
cycle, so the walk along a face of the cluster from a vertex of the cycle that is NOT in that
buffer is stopped strictly inside the cycle, where every neighbour is enclosed. -/
theorem surroundedBy_of_component_zero_buffered (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles) (hFW : Q.embedding.FaceWalks)
    {L : ℕ} (hL : Q.embedding.FaceBound L)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (o : V) (m r : ℕ) (hLr : L + 1 ≤ r)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {x₀ : V} (hx₀m : Q.graph.dist o x₀ ≤ m) (hx₀f : (0:ℝ) < |f x₀|)
    (hbdd : Bornology.IsBounded
      (Q.embedding.clusterRegion {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ (0:ℝ) < |f v|) ∧
        Q.graph.dist o y ≤ m}))
    (hcb : Q.embedding.HasComponentBoundary
      {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ (0:ℝ) < |f v|) ∧ Q.graph.dist o y ≤ m} x₀)
    (hconf : ∀ z : V, Q.embedding.pos z ∈ frontier (connectedComponentIn
        (Q.embedding.clusterRegion {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ (0:ℝ) < |f v|) ∧
          Q.graph.dist o y ≤ m}) (Q.embedding.pos x₀)) →
      Q.graph.dist o z ≤ m + L)
    (hharmreg : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ z ∈ Q.embedding.cycleRegion γ, LatticeProb.Network.netLaplacian Q.graph c f z = 0) :
    Q.SurroundedBy r {x : V | |f x| ≤ 0} {x : V | 0 < f x} {x : V | f x < 0} ∅ o m x₀ := by
  classical
  set W : Set V := {x : V | |f x| ≤ 0} with hW
  set N : Set V := {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ (0:ℝ) < |f v|) ∧
    Q.graph.dist o y ≤ m} with hNdef
  have hx₀N : x₀ ∈ N := ⟨⟨x₀, Or.inl rfl, hx₀f⟩, hx₀m⟩
  obtain ⟨b, γ, hcyc, hreg, hout, hin, hwt, hfr⟩ :=
    exists_component_cycle Q hbc hx₀N hbdd hcb
  have hconfL : ∀ z ∈ γ.support, Q.graph.dist o z ≤ m + L := fun z hz =>
    hconf z (hwt ((Q.embedding.pos_mem_walkTrace_iff γ z).mpr hz))
  have hconf' : ∀ z ∈ γ.support, Q.graph.dist o z ≤ m + r := by
    intro z hz
    have := hconfL z hz
    omega
  have hdich : ∀ z ∈ γ.support, |f z| ≤ 0 ∨ m < Q.graph.dist o z := by
    intro z hz
    by_cases hd : Q.graph.dist o z ≤ m
    · refine Or.inl ?_
      by_contra hcon
      exact hout z hz ⟨⟨z, Or.inl rfl, lt_of_not_ge hcon⟩, hd⟩
    · exact Or.inr (lt_of_not_ge hd)
  have hNmem : ∀ z, (0:ℝ) < |f z| → Q.graph.dist o z ≤ m → z ∈ N :=
    fun z hz hd => ⟨⟨z, Or.inl rfl, hz⟩, hd⟩
  obtain ⟨u, hu, hfar⟩ :=
    exists_far_mem_cycleRegion_abs Q hc o m f 0 hharm hNmem hx₀m hx₀f hout hreg
  have hzero : ∀ z ∈ γ.support,
      ¬ UCPlanar.NearBoundaryOutside Q.graph W o m r z → z ∈ W :=
    mem_of_not_nearBoundaryOutside Q W o m r γ hdich hconf'
  have heq : ({x : V | f x < -0} : Set V) = {x : V | f x < 0} := by ext x; simp
  rw [← heq]
  refine surroundedBy_of_cycle Q hc f 0 o m r hcyc hreg ⟨u, hu, hfar⟩ hdich hconf'
    (hharmreg b γ hreg hconfL) ?_
  intro z hz hnz
  have hfz : f z = 0 := by
    have := hzero z hz hnz
    rw [hW] at this
    simpa using abs_nonpos_iff.mp this
  have hstop : ∀ y ∈ Q.embedding.cycleRegion γ, Q.graph.dist z y ≤ L →
      (∃ v, Q.graph.Adj y v ∧ f v ≠ 0) →
      ∀ v, Q.graph.Adj y v → v ∈ Q.embedding.cycleRegion γ := by
    intro y hy hzy hex v hv
    by_cases hyc : y ∈ γ.support
    · exfalso
      obtain ⟨v', hv', hfv'⟩ := hex
      have hyN : y ∉ N := hout y hyc
      have hyfar : m < Q.graph.dist o y := by
        by_contra hcon
        exact hyN ⟨⟨v', Or.inr hv', abs_pos.mpr hfv'⟩, not_lt.mp hcon⟩
      have hyL : Q.graph.dist o y ≤ m + L := hconfL y hyc
      have hyv : Q.graph.dist y v' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hv'
      have hzv : Q.graph.dist z v' ≤ Q.graph.dist z y + Q.graph.dist y v' :=
        Q.connected.dist_triangle
      have hov : Q.graph.dist o v' = Q.graph.dist o y ∨
          Q.graph.dist o v' = Q.graph.dist o y + 1 ∨
          Q.graph.dist o v' = Q.graph.dist o y - 1 := SimpleGraph.Adj.diff_dist_adj hv'
      refine hnz ⟨v', by omega, ?_, by omega, by omega⟩
      simp only [Set.mem_setOf_eq, not_le]
      exact abs_pos.mpr hfv'
    · exact adj_mem_cycleRegion Q.embedding γ hy hyc hv
  have hres := facePathToSigns_cluster_zero_stop Q hFW hL hc f
    (N := N) (fun y hy => by
      obtain ⟨v, hv, hfv⟩ := hy.1
      exact ⟨v, hv, by simpa using abs_pos.mp hfv⟩)
    hx₀N hwt hin (hharmreg b γ hreg hconfL) hstop hz hfz
  simpa using hres

end UCPlanar.Support
