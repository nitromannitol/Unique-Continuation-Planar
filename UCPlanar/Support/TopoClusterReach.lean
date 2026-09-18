/- The cycle around the cluster reaches the sphere: the maximum principle drives a path of large
values from the chosen vertex to the sphere, and that path cannot leave the region the cycle
bounds without meeting the cycle, whose vertices carry no large value. -/
import UCPlanar.Support.TopoClusterInside
import UCPlanar.Support.TopoClusterBoundary
import UCPlanar.Support.TopoRegion
import UCPlanar.Support.ZeroAssemble
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **A walk confined to `N` cannot leave the region bounded by a cycle avoiding `N`.**  One more
step from its end therefore lands in that region as well. -/
theorem mem_cycleRegion_of_walk_avoiding (E : UCPlanar.PlaneEmbedding G) {b : V}
    {γ : G.Walk b b} {N : Set V} (hout : ∀ z ∈ γ.support, z ∉ N) {x₀ w y : V}
    (hx₀ : x₀ ∈ E.cycleRegion γ) (p : G.Walk x₀ w) (hp : ∀ z ∈ p.support, z ∈ N)
    (hwy : G.Adj w y) : y ∈ E.cycleRegion γ := by
  by_contra hy
  obtain ⟨u, hu, huγ⟩ := exists_mem_support_of_cycleRegion E (p.concat hwy) γ hx₀ hy
  simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hu
  rcases hu with hu | hu
  · exact hout u huγ (hp u hu)
  · subst hu
    exact hy (Or.inl huγ)

/-- **The maximum principle drives the cluster to the sphere.**  A vertex of the ball of radius
`m` where the function exceeds the threshold is joined, inside the set of such vertices, to a
vertex outside that ball; since the cycle avoids that set, the far vertex lies in the region the
cycle bounds. -/
theorem exists_far_mem_cycleRegion (Q : UCPlanar.PeriodicPlaneGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c) (o : V) (m : ℕ)
    (f : V → ℝ) (A : ℝ)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {N : Set V} (hN : ∀ z, A < f z → Q.graph.dist o z ≤ m → z ∈ N)
    {x₀ : V} (hx₀ : Q.graph.dist o x₀ ≤ m) (hfx₀ : A < f x₀)
    {b : V} {γ : Q.graph.Walk b b} (hout : ∀ z ∈ γ.support, z ∉ N)
    (hx₀reg : x₀ ∈ Q.embedding.cycleRegion γ) :
    ∃ u, u ∈ Q.embedding.cycleRegion γ ∧ m < Q.graph.dist o u := by
  classical
  haveI := infinite_of_periodic Q.toPeriodicGraph
  have hharm' : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c (fun z => f z - A) z = 0 := by
    intro z hz
    rw [netLaplacian_sub_const]
    exact hharm z hz
  have hx₀mem : x₀ ∈ Q.toPeriodicGraph.ball o m :=
    (mem_ball_iff_dist Q.toPeriodicGraph o x₀ m).mpr hx₀
  obtain ⟨w, p, hsupp, y, hwy, hyS⟩ :=
    exists_positive_path_to_boundary Q.connected hc (Q.toPeriodicGraph.ball o m)
      (fun z => f z - A) hharm' x₀ hx₀mem (by simpa using sub_pos.mpr hfx₀)
  have hpN : ∀ z ∈ p.support, z ∈ N := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hsupp z hz
    have hz2' : 0 < f z - A := hz2
    exact hN z (by linarith) ((mem_ball_iff_dist Q.toPeriodicGraph o z m).mp hz1)
  have hyfar : m < Q.graph.dist o y := by
    by_contra hle
    exact hyS ((mem_ball_iff_dist Q.toPeriodicGraph o y m).mpr (by omega))
  exact ⟨y, mem_cycleRegion_of_walk_avoiding Q.embedding hout hx₀reg p hpN hwy, hyfar⟩

/-- **The maximum principle drives the cluster to the sphere, either sign.** -/
theorem exists_far_mem_cycleRegion_abs (Q : UCPlanar.PeriodicPlaneGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c) (o : V) (m : ℕ)
    (f : V → ℝ) (A : ℝ)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {N : Set V} (hN : ∀ z, A < |f z| → Q.graph.dist o z ≤ m → z ∈ N)
    {x₀ : V} (hx₀ : Q.graph.dist o x₀ ≤ m) (hfx₀ : A < |f x₀|)
    {b : V} {γ : Q.graph.Walk b b} (hout : ∀ z ∈ γ.support, z ∉ N)
    (hx₀reg : x₀ ∈ Q.embedding.cycleRegion γ) :
    ∃ u, u ∈ Q.embedding.cycleRegion γ ∧ m < Q.graph.dist o u := by
  rcases lt_abs.mp hfx₀ with h | h
  · exact exists_far_mem_cycleRegion Q hc o m f A hharm
      (fun z hz => hN z (lt_of_lt_of_le hz (le_abs_self _))) hx₀ h hout hx₀reg
  · have hharm' : ∀ z ∈ Q.toPeriodicGraph.ball o m,
        LatticeProb.Network.netLaplacian Q.graph c (fun z => -f z) z = 0 := by
      intro z hz
      rw [netLaplacian_neg, hharm z hz, neg_zero]
    exact exists_far_mem_cycleRegion Q hc o m (fun z => -f z) A hharm'
      (fun z hz => hN z (lt_of_lt_of_le hz (neg_le_abs _))) hx₀ h hout hx₀reg

/-- **Three clauses of `SurroundedBy` at once.**  The cycle around the cluster of the vertices of
the ball of radius `m` where the function is large encloses the chosen such vertex, its region
reaches past the sphere of radius `m`, and each of its own vertices carries a small value or lies
outside that sphere. -/
theorem exists_step3_cycle_reaching (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles) (hLF : Q.embedding.LocallyFiniteFaces)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (A : ℝ) (o : V) (m : ℕ)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {x₀ : V} (hx₀m : Q.graph.dist o x₀ ≤ m) (hx₀f : A < |f x₀|)
    (hbdd : Bornology.IsBounded
      (Q.embedding.clusterRegion {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}))
    (hcb : Q.embedding.HasClusterBoundary
      {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}) :
    ∃ (b : V) (γ : Q.graph.Walk b b), γ.IsCycle ∧ x₀ ∈ Q.embedding.cycleRegion γ ∧
      (∃ u ∈ Q.embedding.cycleRegion γ, m < Q.graph.dist o u) ∧
      (∀ z ∈ γ.support, |f z| ≤ A ∨ m < Q.graph.dist o z) ∧
      (∀ z ∈ γ.support, ∃ F ∈ Q.embedding.facesAvoiding
        {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}, Q.embedding.Incident F z) ∧
      ∀ z ∈ γ.support, Q.embedding.pos z ∈ frontier (Q.embedding.clusterRegion
        {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}) := by
  classical
  set W : Set V := {x : V | |f x| ≤ A} with hW
  set N : Set V := {y | y ∉ W ∧ Q.graph.dist o y ≤ m} with hNdef
  have hx₀W : x₀ ∉ W := by
    rw [hW]
    simpa using hx₀f
  obtain ⟨b, γ, hcyc, hreg, hout, hinc, hfr⟩ :=
    exists_cycle_of_clusterBoundary Q.embedding hbc hLF (N := N) ⟨hx₀W, hx₀m⟩ hbdd hcb
  have hNmem : ∀ z, A < |f z| → Q.graph.dist o z ≤ m → z ∈ N := by
    intro z hz hd
    exact ⟨by rw [hW]; simpa using hz, hd⟩
  obtain ⟨u, hu, hfar⟩ :=
    exists_far_mem_cycleRegion_abs Q hc o m f A hharm hNmem hx₀m hx₀f hout hreg
  refine ⟨b, γ, hcyc, hreg, ⟨u, hu, hfar⟩, ?_, hinc, hfr⟩
  intro z hz
  by_cases hzW : z ∈ W
  · exact Or.inl hzW
  · exact Or.inr (by
      by_contra hle
      exact hout z hz ⟨hzW, by omega⟩)

/-- A walk confined to a set of vertices is a walk of the induced subgraph. -/
theorem reachable_induce_of_walk {S : Set V} {x y : V} (p : G.Walk x y) :
    (∀ z ∈ p.support, z ∈ S) → ∀ (hx : x ∈ S) (hy : y ∈ S),
      (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction p with
  | nil => intro _ hx hy; exact SimpleGraph.Reachable.refl _
  | @cons a b c h tail ih =>
    intro hsupp ha hc
    have hb : b ∈ S := hsupp b (by simp)
    have hadj : (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by simpa using h
    exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable hadj)
      (ih (fun z hz => hsupp z (by simp [hz])) hb hc)

/-- **Every sign component inside the cycle reaches the cycle.**  The maximum principle inside
the finite region the cycle bounds sends a path of large values from any interior vertex to a
vertex adjacent to the complement of that region; the path cannot cross the cycle, so it ends on
the cycle itself, where the boundary condition applies. -/
theorem componentsMeetBoundary_of_harmonic (Q : UCPlanar.PeriodicPlaneGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (A : ℝ) {b : V} {γ : Q.graph.Walk b b} (hγ : γ.IsCycle)
    (hharm : ∀ z ∈ Q.embedding.cycleRegion γ,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    (bdry : Set V) (hbdry : ∀ z ∈ γ.support, A < f z → z ∈ bdry) :
    UCPlanar.ComponentsMeetBoundary Q.graph
      {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x} bdry := by
  classical
  haveI := infinite_of_periodic Q.toPeriodicGraph
  set P : Set V := {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x} with hP
  set S : Finset V := (finite_cycleRegion Q γ hγ).toFinset with hSdef
  have hSmem : ∀ z : V, z ∈ S ↔ z ∈ Q.embedding.cycleRegion γ := by
    intro z
    rw [hSdef, Set.Finite.mem_toFinset]
  have hharm' : ∀ z ∈ S, LatticeProb.Network.netLaplacian Q.graph c (fun z => f z - A) z = 0 := by
    intro z hz
    rw [netLaplacian_sub_const]
    exact hharm z ((hSmem z).mp hz)
  rintro ⟨x, hx⟩
  obtain ⟨w, p, hsupp, y, hwy, hyS⟩ :=
    exists_positive_path_to_boundary Q.connected hc S (fun z => f z - A) hharm' x
      ((hSmem x).mpr hx.1) (by simpa using sub_pos.mpr hx.2)
  have hpP : ∀ z ∈ p.support, z ∈ P := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hsupp z hz
    have hz2' : 0 < f z - A := hz2
    exact ⟨(hSmem z).mp hz1, by linarith⟩
  have hyreg : y ∉ Q.embedding.cycleRegion γ := fun h => hyS ((hSmem y).mpr h)
  obtain ⟨u, hu, huγ⟩ :=
    exists_mem_support_of_cycleRegion Q.embedding (p.concat hwy) γ hx.1 hyreg
  simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hu
  have hup : u ∈ p.support := by
    rcases hu with hu | hu
    · exact hu
    · subst hu
      exact absurd (Or.inl huγ) hyreg
  have huP : u ∈ P := hpP u hup
  refine ⟨⟨u, huP⟩, hbdry u huγ huP.2, ?_⟩
  exact reachable_induce_of_walk (p.takeUntil u hup)
    (fun z hz => hpP z (SimpleGraph.Walk.support_takeUntil_subset_support p hup hz)) hx huP

/-- **Every negative sign component inside the cycle reaches the cycle.** -/
theorem componentsMeetBoundary_of_harmonic_neg (Q : UCPlanar.PeriodicPlaneGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (A : ℝ) {b : V} {γ : Q.graph.Walk b b} (hγ : γ.IsCycle)
    (hharm : ∀ z ∈ Q.embedding.cycleRegion γ,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    (bdry : Set V) (hbdry : ∀ z ∈ γ.support, f z < -A → z ∈ bdry) :
    UCPlanar.ComponentsMeetBoundary Q.graph
      {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A} bdry := by
  have hset : {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A}
      = {x | x ∈ Q.embedding.cycleRegion γ ∧ A < (fun z => -f z) x} := by
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith⟩
  rw [hset]
  refine componentsMeetBoundary_of_harmonic Q hc (fun z => -f z) A hγ ?_ bdry ?_
  · intro z hz
    rw [netLaplacian_neg, hharm z hz, neg_zero]
  · intro z hz hlt
    exact hbdry z hz (by linarith)

/-- **The cycle of Step 3 surrounds the vertex in the sense of Section 3.**  A cycle that
encloses `x₀`, whose region reaches past the sphere of radius `m`, whose vertices carry a small
value or lie outside that sphere and stay within the buffer, and inside which the function is
harmonic and every boundary vertex carries a face path to both signs, satisfies every clause of
`SurroundedBy` with nothing discarded. -/
theorem surroundedBy_of_cycle (Q : UCPlanar.PeriodicPlaneGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (A : ℝ) (o : V) (m r : ℕ) {b : V} {γ : Q.graph.Walk b b} (hγ : γ.IsCycle)
    {x₀ : V} (hin : x₀ ∈ Q.embedding.cycleRegion γ)
    (hfar : ∃ u ∈ Q.embedding.cycleRegion γ, m < Q.graph.dist o u)
    (hdich : ∀ z ∈ γ.support, |f z| ≤ A ∨ m < Q.graph.dist o z)
    (hconf : ∀ z ∈ γ.support, Q.graph.dist o z ≤ m + r)
    (hharmreg : ∀ z ∈ Q.embedding.cycleRegion γ,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    (hface : ∀ z ∈ γ.support,
      ¬ UCPlanar.NearBoundaryOutside Q.graph {x : V | |f x| ≤ A} o m r z →
      Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x}
        {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A} z) :
    Q.SurroundedBy r {x : V | |f x| ≤ A} {x : V | A < f x} {x : V | f x < -A} ∅ o m x₀ := by
  classical
  have hdich' : ∀ z ∈ γ.support, z ∈ {x : V | |f x| ≤ A} ∨ m < Q.graph.dist o z := hdich
  have hzero : ∀ z ∈ γ.support,
      ¬ UCPlanar.NearBoundaryOutside Q.graph {x : V | |f x| ≤ A} o m r z →
        z ∈ {x : V | |f x| ≤ A} :=
    mem_of_not_nearBoundaryOutside Q {x : V | |f x| ≤ A} o m r γ hdich' hconf
  have hnear : ∀ z ∈ γ.support, A < |f z| →
      UCPlanar.NearBoundaryOutside Q.graph {x : V | |f x| ≤ A} o m r z := by
    intro z hz hlarge
    by_contra hcon
    have := hzero z hz hcon
    simp only [Set.mem_setOf_eq] at this
    linarith
  obtain ⟨u, hu, hfaru⟩ := hfar
  refine ⟨b, γ, hγ, hin, ⟨u, hu, by omega⟩, hzero, fun z hz hnz _ => hface z hz hnz, ?_, ?_⟩
  · refine componentsMeetBoundary_of_harmonic Q hc f A hγ hharmreg _ ?_
    intro z hz hlt
    exact ⟨hz, Or.inl (hnear z hz (lt_of_lt_of_le hlt (le_abs_self _)))⟩
  · refine componentsMeetBoundary_of_harmonic_neg Q hc f A hγ hharmreg _ ?_
    intro z hz hlt
    exact ⟨hz, Or.inl (hnear z hz (by
      have : -f z ≤ |f z| := neg_le_abs _
      linarith))⟩

/-- **Step 3 of Section 3, end to end.**  From the boundary cycle theorem, local finiteness of the
faces, a bounded filled cluster with a finite boundary edge set, and the three remaining local
inputs — the frontier of the cluster stays within the buffer of the sphere, the function is
harmonic at every vertex the cycle encloses, and every vertex of the cycle outside the buffer
carries a face path to both signs — the vertex is surrounded in the sense of Section 3, with
nothing discarded. -/
theorem surroundedBy_of_cluster (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles) (hLF : Q.embedding.LocallyFiniteFaces)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (A : ℝ) (o : V) (m r : ℕ)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {x₀ : V} (hx₀m : Q.graph.dist o x₀ ≤ m) (hx₀f : A < |f x₀|)
    (hbdd : Bornology.IsBounded
      (Q.embedding.clusterRegion {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}))
    (hcb : Q.embedding.HasClusterBoundary
      {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m})
    (hconf : ∀ z : V, Q.embedding.pos z ∈ frontier (Q.embedding.clusterRegion
      {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}) → Q.graph.dist o z ≤ m + r)
    (hharmreg : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ z ∈ γ.support, z ∉ {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}) →
      ∀ z ∈ Q.embedding.cycleRegion γ, LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    (hface : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ z ∈ γ.support, z ∉ {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}) →
      ∀ z ∈ γ.support, ¬ UCPlanar.NearBoundaryOutside Q.graph {x : V | |f x| ≤ A} o m r z →
        Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x}
          {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A} z) :
    Q.SurroundedBy r {x : V | |f x| ≤ A} {x : V | A < f x} {x : V | f x < -A} ∅ o m x₀ := by
  obtain ⟨b, γ, hcyc, hreg, hfar, hdich, _, hfr⟩ :=
    exists_step3_cycle_reaching Q hbc hLF hc f A o m hharm hx₀m hx₀f hbdd hcb
  have hout : ∀ z ∈ γ.support, z ∉ {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m} := by
    intro z hz hmem
    rcases hdich z hz with h | h
    · exact hmem.1 h
    · exact absurd hmem.2 (by omega)
  exact surroundedBy_of_cycle Q hc f A o m r hcyc hreg hfar hdich
    (fun z hz => hconf z (hfr z hz)) (hharmreg b γ hreg hout) (hface b γ hreg hout)

end UCPlanar.Support
