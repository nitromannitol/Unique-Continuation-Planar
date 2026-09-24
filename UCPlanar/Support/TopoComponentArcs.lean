/- The frontier of a component of the filled cluster is a union of whole arcs.  At a point of
that frontier the drawing has a face of the component on one side and a face avoiding the vertex
set on the other, and the arc through the point lies on the frontier of both. -/
import UCPlanar.Support.TopoPuncture
import UCPlanar.Support.TopoClusterFace
import UCPlanar.Support.TopoClusterEdges
import UCPlanar.Support.TopoStep3Component
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- The closure of a face avoiding `N` misses the filled region. -/
theorem closure_facesAvoiding_subset_compl (E : UCPlanar.PlaneEmbedding G) {N : Set V}
    {F : Set UCPlanar.Plane} (hF : F ∈ E.facesAvoiding N) :
    closure F ⊆ (E.clusterRegion N)ᶜ := by
  intro z hz hc
  exact hc (closure_mono (Set.subset_biUnion_of_mem (u := fun F => F) hF) hz)

/-- **The face of the cluster component on the inner side of a frontier point.** -/
theorem exists_insideFace_of_mem_frontier (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {w p : UCPlanar.Plane}
    (hp : p ∈ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    ∃ F, Q.embedding.IsFace F ∧ p ∈ frontier F ∧
      F ⊆ connectedComponentIn (Q.embedding.clusterRegion N) w := by
  obtain ⟨F, hF, hpcl, hFsub, -⟩ :=
    exists_clusterFace_of_mem_closure Q (frontier_subset_closure hp)
  refine ⟨F, hF, ?_, hFsub⟩
  have hpt : p ∈ Q.embedding.trace :=
    frontier_clusterRegion_subset_trace Q N (locallyFiniteFaces Q)
      (frontier_connectedComponentIn_subset (isOpen_clusterRegion Q.embedding N) _ hp)
  rw [closure_eq_self_union_frontier] at hpcl
  rcases hpcl with h | h
  · exact absurd hpt (isFace_subset_compl_trace Q.embedding hF h)
  · exact h

/-- **The face avoiding `N` on the outer side of a frontier point.** -/
theorem exists_outsideFace_of_mem_frontier (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {w p : UCPlanar.Plane}
    (hp : p ∈ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    ∃ F₀ ∈ Q.embedding.facesAvoiding N, p ∈ frontier F₀ := by
  have hpfr : p ∈ frontier (Q.embedding.clusterRegion N) :=
    frontier_connectedComponentIn_subset (isOpen_clusterRegion Q.embedding N) _ hp
  obtain ⟨F₀, hF₀, hpcl⟩ :=
    exists_facesAvoiding_of_mem_frontier Q.embedding (locallyFiniteFaces Q) hpfr
  refine ⟨F₀, hF₀, ?_⟩
  have hpt : p ∈ Q.embedding.trace :=
    frontier_clusterRegion_subset_trace Q N (locallyFiniteFaces Q) hpfr
  rw [closure_eq_self_union_frontier] at hpcl
  rcases hpcl with h | h
  · exact absurd hpt (isFace_subset_compl_trace Q.embedding hF₀.1 h)
  · exact h

/-- **An arc meeting the frontier of a cluster component away from its ends lies on that
frontier.**  The arc lies on the frontier of the face of the component beside the point, hence in
the closure of the component, and on the frontier of the face avoiding `N` beside the point,
hence outside the filled region altogether. -/
theorem arcOf_subset_frontier_component (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {w : UCPlanar.Plane} {e : Sym2 V} (he : e ∈ Q.graph.edgeSet) {p : UCPlanar.Plane}
    (hp : p ∈ Q.embedding.arcOf e) (hpv : ∀ v : V, p ≠ Q.embedding.pos v)
    (hpf : p ∈ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    Q.embedding.arcOf e ⊆ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w) := by
  set Om : Set UCPlanar.Plane :=
    connectedComponentIn (Q.embedding.clusterRegion N) w with hOm
  have hOmOpen : IsOpen Om := (isOpen_clusterRegion Q.embedding N).connectedComponentIn
  obtain ⟨F₁, hF₁, hpf₁, hF₁sub⟩ := exists_insideFace_of_mem_frontier Q hpf
  obtain ⟨F₀, hF₀, hpf₀⟩ := exists_outsideFace_of_mem_frontier Q hpf
  have h₁ := arcOf_subset_frontier Q hF₁ he hp hpv hpf₁
  have h₀ := arcOf_subset_frontier Q hF₀.1 he hp hpv hpf₀
  intro z hz
  rw [hOmOpen.frontier_eq]
  refine ⟨closure_mono hF₁sub (frontier_subset_closure (h₁ hz)), ?_⟩
  intro hzOm
  have hzc : z ∈ Q.embedding.clusterRegion N := connectedComponentIn_subset _ _ hzOm
  exact closure_facesAvoiding_subset_compl Q.embedding hF₀ (frontier_subset_closure (h₀ hz)) hzc

/-- **Every point of the frontier of a cluster component lies on a whole arc of that frontier.**
At a point that is not a drawn vertex this is the propagation along the arc; at a drawn vertex
the point is not isolated in the frontier, because a punctured ball around it would otherwise be
split by the component and the complement of its closure, and a nearby frontier point supplies an
arc through the vertex. -/
theorem exists_arc_of_mem_frontier_component (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {w p : UCPlanar.Plane}
    (hpf : p ∈ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    ∃ e ∈ Q.graph.edgeSet, p ∈ Q.embedding.arcOf e ∧
      Q.embedding.arcOf e ⊆ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w) := by
  classical
  set Om : Set UCPlanar.Plane :=
    connectedComponentIn (Q.embedding.clusterRegion N) w with hOm
  have hOmOpen : IsOpen Om := (isOpen_clusterRegion Q.embedding N).connectedComponentIn
  have hfrt : frontier Om ⊆ Q.embedding.trace := fun q hq =>
    frontier_clusterRegion_subset_trace Q N (locallyFiniteFaces Q)
      (frontier_connectedComponentIn_subset (isOpen_clusterRegion Q.embedding N) _ hq)
  have hpt : p ∈ Q.embedding.trace := hfrt hpf
  by_cases hpv : ∀ v : V, p ≠ Q.embedding.pos v
  · rw [trace_eq_edgesTrace Q] at hpt
    obtain ⟨e, he, hpe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding hpt
    exact ⟨e, he, hpe, arcOf_subset_frontier_component Q he hpe hpv hpf⟩
  · -- a ball meeting only the arcs through `p` and no other drawn vertex
    obtain ⟨T, hTfin, hTsub, hTcov⟩ := exists_finite_trace_near Q p 1
    set U : Set (Sym2 V) := {f ∈ T | p ∉ Q.embedding.arcOf f} with hU
    have hUfin : U.Finite := hTfin.subset (fun f hf => hf.1)
    have hUclosed : IsClosed (⋃ f ∈ U, Q.embedding.arcOf f) :=
      hUfin.isClosed_biUnion (fun f hf => (isCompact_arcOf Q.embedding (hTsub hf.1)).isClosed)
    have hpU : p ∉ ⋃ f ∈ U, Q.embedding.arcOf f := by
      intro hc
      obtain ⟨f, hf, hpf'⟩ := Set.mem_iUnion₂.mp hc
      exact hf.2 hpf'
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl p hpU
    set W : Set UCPlanar.Plane :=
      (fun v : V => Q.embedding.pos v) '' {v : V | Q.embedding.pos v ∈ Metric.closedBall p 1 ∧
        Q.embedding.pos v ≠ p} with hW
    have hWfin : W.Finite :=
      Set.Finite.image _ ((finite_pos_meeting_bounded Q Metric.isBounded_closedBall).subset
        (fun v hv => hv.1))
    have hpW : p ∉ W := by
      rintro ⟨v, hv, hvp⟩
      exact hv.2 hvp
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.isOpen_iff.mp hWfin.isClosed.isOpen_compl p hpW
    set ε : ℝ := min (min ε₁ ε₂) 1 with hεdef
    have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) one_pos
    -- the point is not isolated in the frontier of the component
    have hin : p ∈ closure Om := frontier_subset_closure hpf
    have hout : p ∈ closure (closure Om)ᶜ := by
      obtain ⟨F₀, hF₀, hpf₀⟩ := exists_outsideFace_of_mem_frontier Q hpf
      have hsub : F₀ ⊆ (closure Om)ᶜ := by
        intro z hz hcl
        obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl F₀ (isOpen_isFace Q hF₀.1) hz
        exact closure_facesAvoiding_subset_compl Q.embedding hF₀ (subset_closure hy1)
          (connectedComponentIn_subset _ _ hy2)
      exact closure_mono hsub (frontier_subset_closure hpf₀)
    obtain ⟨q, hqf, hqb, hqp⟩ := exists_mem_frontier_ne Om hOmOpen hin hout hε
    have hqt : q ∈ Q.embedding.trace := hfrt hqf
    have hq1 : q ∈ Metric.closedBall p 1 :=
      Metric.closedBall_subset_closedBall (min_le_right _ _)
        (Metric.ball_subset_closedBall hqb)
    obtain ⟨f, hf, hqe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding (hTcov q hq1 hqt)
    have hpf' : p ∈ Q.embedding.arcOf f := by
      by_contra hcon
      exact hb₁ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hqb)
        (le_trans (min_le_left _ _) (min_le_left _ _)))) (Set.mem_biUnion ⟨hf, hcon⟩ hqe)
    have hqv : ∀ v : V, q ≠ Q.embedding.pos v := by
      intro v hc
      refine hb₂ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hqb)
        (le_trans (min_le_left _ _) (min_le_right _ _)))) ?_
      exact ⟨v, ⟨by rw [← hc]; exact hq1, by rw [← hc]; exact hqp⟩, hc.symm⟩
    exact ⟨f, hTsub hf, hpf', arcOf_subset_frontier_component Q (hTsub hf) hqe hqv hqf⟩

/-- **The frontier of a bounded cluster component is drawn by a finite edge set.**  This is the
boundary edge set of Step 3 for the component through a chosen vertex. -/
theorem hasComponentBoundary (Q : UCPlanar.PeriodicPlaneGraph V) (N : Set V) (x₀ : V)
    (hbdd : Bornology.IsBounded (Q.embedding.clusterRegion N)) :
    Q.embedding.HasComponentBoundary N x₀ := by
  classical
  set Om : Set UCPlanar.Plane :=
    connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀) with hOm
  have hOmB : Bornology.IsBounded Om := hbdd.subset (connectedComponentIn_subset _ _)
  set S : Set (Sym2 V) := {e : Sym2 V | e ∈ Q.graph.edgeSet ∧ (Q.embedding.arcOf e).Nonempty ∧
    Q.embedding.arcOf e ⊆ frontier Om} with hS
  have hfin : S.Finite := by
    refine Set.Finite.subset
      (finite_edges_meeting_bounded Q (A := frontier Om)
        (hOmB.closure.subset frontier_subset_closure)) ?_
    rintro e ⟨he, ⟨q, hq⟩, hsub⟩
    exact ⟨he, q, hq, hsub hq⟩
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
    exact he.1
  · intro q hq
    obtain ⟨e, he, hqe, hsub⟩ := exists_arc_of_mem_frontier_component Q hq
    refine Set.mem_biUnion (?_ : e ∈ (hfin.toFinset : Set (Sym2 V))) hqe
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨he, ⟨q, hqe⟩, hsub⟩
  · intro e he
    rw [Set.Finite.mem_toFinset] at he
    exact he.2.2

/-- **The confinement of the frontier of a cluster component.**  A vertex drawn on the frontier
of the component is incident to a face of the cluster, that face carries a vertex of `N`, and two
vertices incident to one face are within the face bound of each other, so the frontier of the
cluster of a vertex set inside a ball stays within the face bound of that ball. -/
theorem dist_le_of_pos_mem_frontier_component (Q : UCPlanar.PeriodicPlaneGraph V)
    {L : ℕ} (hL : Q.embedding.FaceBound L) (hFW : Q.embedding.FaceWalks)
    {N : Set V} {o : V} {k : ℕ} (hN : ∀ y ∈ N, Q.graph.dist o y ≤ k)
    {w : UCPlanar.Plane} {z : V}
    (hz : Q.embedding.pos z ∈ frontier (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    Q.graph.dist o z ≤ k + L := by
  obtain ⟨F, hF, hincz, -, y, hincy, hyN⟩ :=
    exists_clusterFace_incident Q (frontier_subset_closure hz)
  have h1 : Q.graph.dist y z ≤ L := exists_short_face_walk Q hL hFW hF hincy hincz
  have h2 : Q.graph.dist o y ≤ k := hN y hyN
  have h3 : Q.graph.dist o z ≤ Q.graph.dist o y + Q.graph.dist y z := Q.connected.dist_triangle
  omega

/-- **A vertex drawn inside the filled cluster is within the face bound of the cluster set.**
Every face reaching such a vertex is a face of the cluster, hence carries a vertex of `N`. -/
theorem dist_le_of_pos_mem_clusterRegion (Q : UCPlanar.PeriodicPlaneGraph V)
    {L : ℕ} (hL : Q.embedding.FaceBound L) (hFW : Q.embedding.FaceWalks)
    {N : Set V} {o : V} {k : ℕ} (hN : ∀ y ∈ N, Q.graph.dist o y ≤ k)
    {z : V} (hz : Q.embedding.pos z ∈ Q.embedding.clusterRegion N) :
    Q.graph.dist o z ≤ k + L := by
  obtain ⟨F, hF, hincz, -, y, hincy, hyN⟩ :=
    exists_clusterFace_incident Q (subset_closure (mem_connectedComponentIn hz))
  have h1 : Q.graph.dist y z ≤ L := exists_short_face_walk Q hL hFW hF hincy hincz
  have h2 : Q.graph.dist o y ≤ k := hN y hyN
  have h3 : Q.graph.dist o z ≤ Q.graph.dist o y + Q.graph.dist y z := Q.connected.dist_triangle
  omega

/-- **A cycle drawn inside a disc encloses only vertices inside that disc**, in the graph metric
up to the comparison constant of the periodic graph.  This is the geometric bound on the region
Step 3 encloses: the drawing of an enclosed vertex cannot be farther from the centre than the
drawing of the cycle, since beyond the disc the complement of the drawing is unbounded. -/
theorem exists_dist_le_of_cycleRegion_ball (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (o b : V) (γ : P.graph.Walk b b) (R : ℝ), 0 ≤ R →
      P.embedding.walkTrace γ ⊆ Metric.closedBall (P.embedding.pos o) R →
      ∀ z ∈ P.embedding.cycleRegion γ, (P.graph.dist o z : ℝ) ≤ K * R + K := by
  obtain ⟨K, hK0, hK⟩ := exists_dist_le_norm P.toPeriodicGraph
  refine ⟨K, hK0, ?_⟩
  intro o b γ R hR htrace z hz
  have key : ‖P.pos o - P.pos z‖ ≤ R := by
    have hkey : ‖P.embedding.pos z - P.embedding.pos o‖ ≤ R := by
      rcases hz with hz | ⟨-, hz2⟩
      · have hmem : P.embedding.pos z ∈ P.embedding.walkTrace γ :=
          (P.embedding.pos_mem_walkTrace_iff γ z).mpr hz
        have := htrace hmem
        rwa [Metric.mem_closedBall, dist_eq_norm] at this
      · by_contra hcon
        exact not_isBounded_component_of_far (P.embedding.walkTrace γ) (P.embedding.pos o) R hR
          htrace (P.embedding.pos z) (lt_of_not_ge hcon) hz2
    rw [← P.embedding_pos, ← norm_neg]
    simpa using hkey
  have hdist := hK o z
  have hmul : K * ‖P.pos o - P.pos z‖ ≤ K * R := mul_le_mul_of_nonneg_left key hK0.le
  linarith

/-- Every point of a drawn walk is within the arc bound of the drawing of one of its vertices. -/
theorem exists_support_norm_le {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ (u v : V) (h : G.Adj u v), ∀ p ∈ Set.range (E.edge h), ‖p - E.pos u‖ ≤ D)
    {x y : V} (w : G.Walk x y) :
    ∀ p ∈ E.walkTrace w, ∃ z ∈ w.support, ‖p - E.pos z‖ ≤ D := by
  induction w with
  | @nil u =>
      intro p hp
      have hp' : p = E.pos u := by simpa [UCPlanar.PlaneEmbedding.walkTrace] using hp
      exact ⟨u, by simp, by rw [hp']; simpa using hD0⟩
  | @cons u v z h q ih =>
      intro p hp
      rcases hp with hp | hp
      · exact ⟨u, by simp, hD u v h p hp⟩
      · obtain ⟨t, ht, hts⟩ := ih p hp
        exact ⟨t, by simp [SimpleGraph.Walk.support_cons, ht], hts⟩

/-- **A cycle whose vertices stay in a graph ball encloses only vertices of a ball whose radius is
a constant multiple of it.**  The constant is the product of the arc bound with the comparison
constant between the graph metric and the plane metric, and it is what the harmonicity of the
enclosed vertices has to be asked on. -/
theorem exists_dist_le_of_cycleRegion_dist (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (o b : V) (γ : P.graph.Walk b b) (k : ℕ),
      (∀ z ∈ γ.support, P.graph.dist o z ≤ k) →
      ∀ z ∈ P.embedding.cycleRegion γ, (P.graph.dist o z : ℝ) ≤ C * k + C := by
  obtain ⟨K, hK0, hKball⟩ := exists_dist_le_of_cycleRegion_ball P
  obtain ⟨D, hD0, hD⟩ := exists_arc_bound P
  have hD' : ∀ (u v : V) (h : P.graph.Adj u v), ∀ p ∈ Set.range (P.embedding.edge h),
      ‖p - P.embedding.pos u‖ ≤ D := hD
  refine ⟨3 * K * D + K, by positivity, ?_⟩
  intro o b γ k hk z hz
  set R : ℝ := D * (k + 2) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have htrace : P.embedding.walkTrace γ ⊆ Metric.closedBall (P.embedding.pos o) R := by
    intro p hp
    obtain ⟨t, ht, hpt⟩ := exists_support_norm_le P.embedding D hD0 hD' γ p hp
    obtain ⟨w, hw⟩ := (P.connected.preconnected o t).exists_walk_length_eq_dist
    have hmem : P.embedding.pos t ∈ P.embedding.walkTrace w :=
      (P.embedding.pos_mem_walkTrace_iff w t).mpr w.end_mem_support
    have h1 : ‖P.embedding.pos t - P.embedding.pos o‖ ≤ D * (w.length + 1) :=
      norm_sub_le_of_mem_walkTrace P.embedding D hD0 hD' w _ hmem
    have h2 : (w.length : ℝ) ≤ (k : ℝ) := by
      rw [hw]
      exact_mod_cast hk t ht
    have h3 : ‖p - P.embedding.pos o‖ ≤ ‖p - P.embedding.pos t‖
        + ‖P.embedding.pos t - P.embedding.pos o‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub p (P.embedding.pos t) (P.embedding.pos o)
      simpa using this
    rw [Metric.mem_closedBall, dist_eq_norm, hRdef]
    nlinarith [hpt, h1, h2, h3, hD0]
  have hkey := hKball o b γ R hR0 htrace z hz
  rw [hRdef] at hkey
  have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hKD : 0 ≤ K * D := mul_nonneg hK0.le hD0
  nlinarith [hkey, hKD, hk0, mul_nonneg hKD hk0, mul_nonneg hK0.le hk0]

end UCPlanar.Support
