/- The two bookkeeping inputs of the face path of Step 3: every point on the frontier of the
filled cluster through a vertex is on the frontier of a face of that cluster, and every vertex
incident to such a face lies in the region the surrounding cycle bounds. -/
import UCPlanar.Support.TopoLines
import UCPlanar.Support.TopoClusterInside
import UCPlanar.Support.TopoFaceBand
import UCPlanar.Support.TopoWalksExternal
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **The drawing has empty interior.**  Near any point the drawing is the drawing of finitely
many edges, whose arcs lie on finitely many lines, and a finite union of lines contains no
nonempty open set. -/
theorem eq_empty_of_isOpen_subset_trace (Q : UCPlanar.PeriodicPlaneGraph V)
    {U : Set UCPlanar.Plane} (hU : IsOpen U) (hsub : U ⊆ Q.embedding.trace) : U = ∅ := by
  classical
  by_contra hne
  obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨T, hTfin, hTsub, hTcov⟩ := exists_finite_trace_near Q p 1
  obtain ⟨L, hL1, hL2⟩ := exists_lines_edgesTrace Q.embedding hTfin hTsub
  have hUopen : IsOpen (U ∩ Metric.ball p 1) := hU.inter Metric.isOpen_ball
  have hsub2 : U ∩ Metric.ball p 1 ⊆ ⋃ l ∈ L, lineSet l := by
    rintro q ⟨hqU, hqB⟩
    exact hL2 (hTcov q (Metric.ball_subset_closedBall hqB) (hsub hqU))
  have hemp := eq_empty_of_isOpen_subset_lines L hL1 _ hUopen hsub2
  have hmem : p ∈ U ∩ Metric.ball p 1 := ⟨hp, Metric.mem_ball_self one_pos⟩
  rw [hemp] at hmem
  exact hmem

/-- **A nonempty open set holds a point off the drawing.** -/
theorem exists_notMem_trace (Q : UCPlanar.PeriodicPlaneGraph V)
    {U : Set UCPlanar.Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ q ∈ U, q ∉ Q.embedding.trace := by
  by_contra hcon
  push Not at hcon
  exact absurd (eq_empty_of_isOpen_subset_trace Q hU hcon) (Set.nonempty_iff_ne_empty.mp hne)

/-- **A face containing a point of the filled region is a face of the cluster.**  It cannot avoid
`N`, so it carries a vertex of `N` and is contained in the filled region. -/
theorem isFace_mem_cluster (Q : UCPlanar.PeriodicPlaneGraph V) (hLF : Q.embedding.LocallyFiniteFaces)
    {N : Set V} {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    {q : UCPlanar.Plane} (hq : q ∈ F) (hqc : q ∈ Q.embedding.clusterRegion N) :
    F ⊆ Q.embedding.clusterRegion N ∧ ∃ y, Q.embedding.Incident F y ∧ y ∈ N := by
  have havoid : F ∉ Q.embedding.facesAvoiding N := by
    intro hmem
    exact hqc (subset_closure (Set.mem_biUnion hmem hq))
  have hy : ∃ y, Q.embedding.Incident F y ∧ y ∈ N := by
    by_contra hcon
    push Not at hcon
    exact havoid ⟨hF, fun y hinc => hcon y hinc⟩
  obtain ⟨y, hinc, hyN⟩ := hy
  exact ⟨isFace_subset_clusterRegion Q hLF hF hyN hinc, ⟨y, hinc, hyN⟩⟩

/-- **Every point in the closure of a cluster component is on the closure of a face of that
component.**  Near the point only finitely many faces are in play; if none of their closures
reached the point, a small neighbourhood would meet the component in a nonempty open set, which
holds a point off the drawing, and the face of that point is one of the finitely many. -/
theorem exists_clusterFace_of_mem_closure (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {w p : UCPlanar.Plane}
    (hp : p ∈ closure (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    ∃ F, Q.embedding.IsFace F ∧ p ∈ closure F ∧
      F ⊆ connectedComponentIn (Q.embedding.clusterRegion N) w ∧
      ∃ y, Q.embedding.Incident F y ∧ y ∈ N := by
  classical
  set hLF := locallyFiniteFaces Q with hLFdef
  set Om : Set UCPlanar.Plane := connectedComponentIn (Q.embedding.clusterRegion N) w with hOm
  have hOmOpen : IsOpen Om := (isOpen_clusterRegion Q.embedding N).connectedComponentIn
  obtain ⟨t, ht, hfin⟩ := hLF p
  set SS : Set (Set UCPlanar.Plane) :=
    {F | Q.embedding.IsFace F ∧ (F ∩ t).Nonempty ∧ F ⊆ Om} with hSS
  have hSSfin : SS.Finite := by
    have himg : SS ⊆ Subtype.val ''
        {i : {F : Set UCPlanar.Plane // Q.embedding.IsFace F} | ((i : Set UCPlanar.Plane) ∩ t).Nonempty} := by
      rintro F ⟨hF, hFt, -⟩
      exact ⟨⟨F, hF⟩, hFt, rfl⟩
    exact Set.Finite.subset (hfin.image _) himg
  have hclosed : IsClosed (⋃ F ∈ SS, closure F) :=
    hSSfin.isClosed_biUnion (fun F _ => isClosed_closure)
  have hmain : p ∈ ⋃ F ∈ SS, closure F := by
    by_contra hcon
    set W : Set UCPlanar.Plane := (⋃ F ∈ SS, closure F)ᶜ ∩ interior t with hW
    have hWopen : IsOpen W := hclosed.isOpen_compl.inter isOpen_interior
    have hpW : p ∈ W := ⟨hcon, mem_interior_iff_mem_nhds.mpr ht⟩
    have hWne : (W ∩ Om).Nonempty := mem_closure_iff.mp hp W hWopen hpW
    obtain ⟨q, ⟨hqW, hqOm⟩, hqt⟩ :=
      exists_notMem_trace Q (hWopen.inter hOmOpen) hWne
    have hqc : q ∈ Q.embedding.clusterRegion N := connectedComponentIn_subset _ _ hqOm
    set F : Set UCPlanar.Plane := connectedComponentIn Q.embedding.traceᶜ q with hF
    have hFface : Q.embedding.IsFace F := ⟨q, hqt, rfl⟩
    have hqF : q ∈ F := mem_connectedComponentIn hqt
    obtain ⟨hFsub, hyN⟩ := isFace_mem_cluster Q hLF hFface hqF hqc
    have hFOm : F ⊆ Om := by
      have h1 : F ⊆ connectedComponentIn (Q.embedding.clusterRegion N) q :=
        (isFace_isPreconnected Q.embedding hFface).subset_connectedComponentIn hqF hFsub
      rwa [hOm, connectedComponentIn_eq hqOm]
    have hFSS : F ∈ SS := ⟨hFface, ⟨q, hqF, interior_subset hqW.2⟩, hFOm⟩
    exact hqW.1 (Set.mem_biUnion hFSS (subset_closure hqF))
  obtain ⟨F, hFSS, hpcl⟩ := Set.mem_iUnion₂.mp hmain
  exact ⟨F, hFSS.1, hpcl, hFSS.2.2,
    (isFace_mem_cluster Q hLF hFSS.1 (isFace_nonempty Q.embedding hFSS.1).choose_spec
      (connectedComponentIn_subset _ _ (hFSS.2.2 (isFace_nonempty Q.embedding hFSS.1).choose_spec))).2⟩


/-- **A vertex on the frontier of a cluster component is incident to a face of that component.**
This is the paper's "since `z` is adjacent to a face `F` in `K`". -/
theorem exists_clusterFace_incident (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {w : UCPlanar.Plane} {z : V}
    (hz : Q.embedding.pos z ∈ closure (connectedComponentIn (Q.embedding.clusterRegion N) w)) :
    ∃ F, Q.embedding.IsFace F ∧ Q.embedding.Incident F z ∧
      F ⊆ connectedComponentIn (Q.embedding.clusterRegion N) w ∧
      ∃ y, Q.embedding.Incident F y ∧ y ∈ N := by
  obtain ⟨F, hF, hcl, hFOm, hy⟩ := exists_clusterFace_of_mem_closure Q hz
  refine ⟨F, hF, ?_, hFOm, hy⟩
  rw [closure_eq_self_union_frontier] at hcl
  rcases hcl with h | h
  · exact absurd h (pos_notMem_isFace Q.embedding hF z)
  · exact h

/-- **Every vertex incident to a face of the cluster component lies in the region the surrounding
cycle bounds.**  The face lies in the component, whose closure the cycle encloses. -/
theorem incident_mem_cycleRegion_of_subset (E : UCPlanar.PlaneEmbedding G) {N : Set V}
    {p : UCPlanar.Plane} (hp : p ∈ E.clusterRegion N) {b : V} {γ : G.Walk b b}
    (hγ : E.walkTrace γ ⊆ frontier (E.clusterRegion N))
    (hin : p ∈ UCPlanar.Support.insideOf (E.walkTrace γ))
    {F : Set UCPlanar.Plane} (hF : F ⊆ connectedComponentIn (E.clusterRegion N) p)
    {y : V} (hy : E.Incident F y) : y ∈ E.cycleRegion γ := by
  refine mem_cycleRegion_of_pos_mem_closure E hp hγ hin ?_
  exact closure_mono hF (frontier_subset_closure hy)


/-- **Every vertex of a cycle drawn on the frontier of the cluster component is incident to a
face of the cluster inside the cycle.**  This is the paper's "since `z` is adjacent to a face
`F` in `K`" together with the containment of `F` in the region the cycle bounds. -/
theorem exists_clusterFace_of_cycle (Q : UCPlanar.PeriodicPlaneGraph V) {N : Set V}
    {x₀ b : V} {γ : Q.graph.Walk b b} (hx₀ : x₀ ∈ N)
    (hγ : Q.embedding.walkTrace γ ⊆
      frontier (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)))
    (hin : Q.embedding.pos x₀ ∈ UCPlanar.Support.insideOf (Q.embedding.walkTrace γ))
    {z : V} (hz : z ∈ γ.support) :
    ∃ F, Q.embedding.IsFace F ∧ Q.embedding.Incident F z ∧
      (∀ y, Q.embedding.Incident F y → y ∈ Q.embedding.cycleRegion γ) ∧
      ∃ w, Q.embedding.Incident F w ∧ w ∈ N := by
  have hposz : Q.embedding.pos z ∈ Q.embedding.walkTrace γ :=
    (Q.embedding.pos_mem_walkTrace_iff γ z).mpr hz
  have hcl : Q.embedding.pos z ∈
      closure (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)) :=
    frontier_subset_closure (hγ hposz)
  obtain ⟨F, hF, hincz, hFOm, w, hincw, hwN⟩ := exists_clusterFace_incident Q hcl
  have hx₀c : Q.embedding.pos x₀ ∈ Q.embedding.clusterRegion N :=
    pos_mem_clusterRegion Q.embedding (locallyFiniteFaces Q) hx₀
  have hγ' : Q.embedding.walkTrace γ ⊆ frontier (Q.embedding.clusterRegion N) :=
    hγ.trans (frontier_connectedComponentIn_subset (isOpen_clusterRegion Q.embedding N) _)
  exact ⟨F, hF, hincz,
    fun y hy => incident_mem_cycleRegion_of_subset Q.embedding hx₀c hγ' hin hFOm hy,
    ⟨w, hincw, hwN⟩⟩

/-- **The third hypothesis of the topological lemma at a vertex of the Step 3 cycle, zero
case.**  The face of the cluster at the vertex lies inside the cycle, so the walk along its
frontier and the harmonic completion of the opposite sign produce the face path. -/
theorem facePathToSigns_cluster_zero (Q : UCPlanar.PeriodicPlaneGraph V)
    (hFW : Q.embedding.FaceWalks) {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond Q.graph c) (f : V → ℝ) {N : Set V}
    (hN : ∀ y ∈ N, f y ≠ 0) {x₀ b : V} {γ : Q.graph.Walk b b} (hx₀ : x₀ ∈ N)
    (hγ : Q.embedding.walkTrace γ ⊆
      frontier (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)))
    (hin : Q.embedding.pos x₀ ∈ UCPlanar.Support.insideOf (Q.embedding.walkTrace γ))
    (hharmreg : ∀ y ∈ Q.embedding.cycleRegion γ,
      LatticeProb.Network.netLaplacian Q.graph c f y = 0)
    (hnb : ∀ y ∈ Q.embedding.cycleRegion γ, ∀ u, Q.graph.Adj y u →
      u ∈ Q.embedding.cycleRegion γ)
    {z : V} (hz : z ∈ γ.support) (hfz : f z = 0) :
    Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ 0 < f x}
      {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < 0} z := by
  obtain ⟨F, hF, hincz, hFreg, w, hincw, hwN⟩ := exists_clusterFace_of_cycle Q hx₀ hγ hin hz
  exact facePathToSigns_step3 Q.embedding hc hFW f γ hF
    (fun y hy => hharmreg y (hFreg y hy)) hFreg
    (fun y hy u hu => hnb y (hFreg y hy) u hu) hincz hfz hincw (hN w hwN)

/-- **The third hypothesis of the topological lemma at a vertex of the Step 3 cycle, banded
case.**  Either the vertex carries a face path to both sign sets, or it is within the face bound
of a vertex whose value lies inside the band, in which case Section 4 discards it. -/
theorem facePathToSigns_cluster_band (Q : UCPlanar.PeriodicPlaneGraph V)
    (hFW : Q.embedding.FaceWalks) {L : ℕ} (hL : Q.embedding.FaceBound L) (f : V → ℝ)
    {A B : ℝ} (hAB : A < B) {N : Set V} (hN : ∀ y ∈ N, A < |f y|)
    {x₀ b : V} {γ : Q.graph.Walk b b} (hx₀ : x₀ ∈ N)
    (hγ : Q.embedding.walkTrace γ ⊆
      frontier (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)))
    (hin : Q.embedding.pos x₀ ∈ UCPlanar.Support.insideOf (Q.embedding.walkTrace γ))
    (hup : ∀ y ∈ Q.embedding.cycleRegion γ, |f y| ≤ A → ∀ u, Q.graph.Adj y u → B ≤ f u →
      ∃ v, Q.graph.Adj y v ∧ f v < -A)
    (hdn : ∀ y ∈ Q.embedding.cycleRegion γ, |f y| ≤ A → ∀ u, Q.graph.Adj y u → f u ≤ -B →
      ∃ v, Q.graph.Adj y v ∧ A < f v)
    (hnb : ∀ y ∈ Q.embedding.cycleRegion γ, ∀ u, Q.graph.Adj y u →
      u ∈ Q.embedding.cycleRegion γ)
    {z : V} (hz : z ∈ γ.support) (hfz : |f z| ≤ A) :
    Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x}
        {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A} z ∨
      ∃ y, Q.graph.dist z y ≤ L ∧ A < |f y| ∧ |f y| < B := by
  obtain ⟨F, hF, hincz, hFreg, w, hincw, hwN⟩ := exists_clusterFace_of_cycle Q hx₀ hγ hin hz
  exact facePathToSigns_band_dist Q.embedding hFW hL f hAB γ hF
    (fun y hy hfy u hu => hup y (hFreg y hy) hfy u hu)
    (fun y hy hfy u hu => hdn y (hFreg y hy) hfy u hu)
    hFreg (fun y hy u hu => hnb y (hFreg y hy) u hu) hincz hfz hincw (hN w hwN)

/-- **The third hypothesis of the topological lemma at a vertex of the Step 3 cycle, zero case,
with the neighbour-buffered cluster.**  A vertex of the cluster need only have a neighbour where
the function does not vanish, and the containment of neighbours is asked only at a vertex that
has such a neighbour. -/
theorem facePathToSigns_cluster_zero_stop (Q : UCPlanar.PeriodicPlaneGraph V)
    (hFW : Q.embedding.FaceWalks) {L : ℕ} (hL : Q.embedding.FaceBound L) {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond Q.graph c) (f : V → ℝ) {N : Set V}
    (hN : ∀ y ∈ N, ∃ u, (u = y ∨ Q.graph.Adj y u) ∧ f u ≠ 0)
    {x₀ b : V} {γ : Q.graph.Walk b b} (hx₀ : x₀ ∈ N)
    (hγ : Q.embedding.walkTrace γ ⊆
      frontier (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)))
    (hin : Q.embedding.pos x₀ ∈ UCPlanar.Support.insideOf (Q.embedding.walkTrace γ))
    (hharmreg : ∀ y ∈ Q.embedding.cycleRegion γ,
      LatticeProb.Network.netLaplacian Q.graph c f y = 0)
    {z : V}
    (hstop : ∀ y ∈ Q.embedding.cycleRegion γ, Q.graph.dist z y ≤ L →
      (∃ u, Q.graph.Adj y u ∧ f u ≠ 0) →
      ∀ u, Q.graph.Adj y u → u ∈ Q.embedding.cycleRegion γ)
    (hz : z ∈ γ.support) (hfz : f z = 0) :
    Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ 0 < f x}
      {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < 0} z := by
  obtain ⟨F, hF, hincz, hFreg, w, hincw, hwN⟩ := exists_clusterFace_of_cycle Q hx₀ hγ hin hz
  exact facePathToSigns_step3_stop Q.embedding hc hFW f γ hF
    (fun y hy => hharmreg y (hFreg y hy)) hFreg
    (fun y hy hex u hu =>
      hstop y (hFreg y hy) (exists_short_face_walk Q hL hFW hF hincz hy) hex u hu)
    hincz hfz hincw (hN w hwN)

/-- **The third hypothesis of the topological lemma at a vertex of the Step 3 cycle, banded case,
with the neighbour-buffered cluster.** -/
theorem facePathToSigns_cluster_band_stop (Q : UCPlanar.PeriodicPlaneGraph V)
    (hFW : Q.embedding.FaceWalks) {L : ℕ} (hL : Q.embedding.FaceBound L) (f : V → ℝ)
    {A B : ℝ} (hAB : A < B) {N : Set V}
    (hN : ∀ y ∈ N, ∃ u, (u = y ∨ Q.graph.Adj y u) ∧ A < |f u|)
    {x₀ b : V} {γ : Q.graph.Walk b b} (hx₀ : x₀ ∈ N)
    (hγ : Q.embedding.walkTrace γ ⊆
      frontier (connectedComponentIn (Q.embedding.clusterRegion N) (Q.embedding.pos x₀)))
    (hin : Q.embedding.pos x₀ ∈ UCPlanar.Support.insideOf (Q.embedding.walkTrace γ))
    (hup : ∀ y ∈ Q.embedding.cycleRegion γ, |f y| ≤ A → ∀ u, Q.graph.Adj y u → B ≤ f u →
      ∃ v, Q.graph.Adj y v ∧ f v < -A)
    (hdn : ∀ y ∈ Q.embedding.cycleRegion γ, |f y| ≤ A → ∀ u, Q.graph.Adj y u → f u ≤ -B →
      ∃ v, Q.graph.Adj y v ∧ A < f v)
    {z : V}
    (hstop : ∀ y ∈ Q.embedding.cycleRegion γ, Q.graph.dist z y ≤ L →
      (∃ u, Q.graph.Adj y u ∧ A < |f u|) →
      ∀ u, Q.graph.Adj y u → u ∈ Q.embedding.cycleRegion γ)
    (hz : z ∈ γ.support) (hfz : |f z| ≤ A) :
    Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x}
        {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A} z ∨
      ∃ y, Q.graph.dist z y ≤ L ∧ A < |f y| ∧ |f y| < B := by
  obtain ⟨F, hF, hincz, hFreg, w, hincw, hwN⟩ := exists_clusterFace_of_cycle Q hx₀ hγ hin hz
  exact facePathToSigns_band_dist_stop Q.embedding hFW hL f hAB γ hF
    (fun y hy hfy u hu => hup y (hFreg y hy) hfy u hu)
    (fun y hy hfy u hu => hdn y (hFreg y hy) hfy u hu)
    hFreg (fun y hy hex u hu =>
      hstop y (hFreg y hy) (exists_short_face_walk Q hL hFW hF hincz hy) hex u hu)
    hincz hfz hincw (hN w hwN)

end UCPlanar.Support
