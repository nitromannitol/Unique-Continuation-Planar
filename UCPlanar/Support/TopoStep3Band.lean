/- Step 3 of Section 4 at a positive threshold, run on the connected component of the filled
cluster through the chosen vertex.  The cycle is the one of Step 3, the face path at each of its
vertices comes from the walk along a face of the cluster, and the vertices where that walk stops
inside the band are collected into the discarded set of the surrounding property. -/
import UCPlanar.Support.TopoStep3Component
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support


variable {V : Type*}

/-- **The surrounding property from a cycle, with a discarded set.**  This is Step 3's assembly
with the face path demanded only at the cycle vertices outside the discarded set; the two
component conditions are unchanged, because the boundary set they use only grows. -/
theorem surroundedBy_of_cycle_discard (Q : UCPlanar.PeriodicPlaneGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (A : ℝ) (o : V) (m r : ℕ) {b : V} {γ : Q.graph.Walk b b} (hγ : γ.IsCycle)
    {x₀ : V} (hin : x₀ ∈ Q.embedding.cycleRegion γ)
    (hfar : ∃ u ∈ Q.embedding.cycleRegion γ, m < Q.graph.dist o u)
    (hdich : ∀ z ∈ γ.support, |f z| ≤ A ∨ m < Q.graph.dist o z)
    (hconf : ∀ z ∈ γ.support, Q.graph.dist o z ≤ m + r)
    (hharmreg : ∀ z ∈ Q.embedding.cycleRegion γ,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    (D : Finset V)
    (hface : ∀ z ∈ γ.support,
      ¬ UCPlanar.NearBoundaryOutside Q.graph {x : V | |f x| ≤ A} o m r z → z ∉ D →
      Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ A < f x}
        {x | x ∈ Q.embedding.cycleRegion γ ∧ f x < -A} z) :
    Q.SurroundedBy r {x : V | |f x| ≤ A} {x : V | A < f x} {x : V | f x < -A} D o m x₀ := by
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
  refine ⟨b, γ, hγ, hin, ⟨u, hu, by omega⟩, hzero, fun z hz hnz hnD => hface z hz hnz hnD, ?_, ?_⟩
  · refine componentsMeetBoundary_of_harmonic Q hc f A hγ hharmreg _ ?_
    intro z hz hlt
    exact ⟨hz, Or.inl (hnear z hz (lt_of_lt_of_le hlt (le_abs_self _)))⟩
  · refine componentsMeetBoundary_of_harmonic_neg Q hc f A hγ hharmreg _ ?_
    intro z hz hlt
    exact ⟨hz, Or.inl (hnear z hz (by
      have : -f z ≤ |f z| := neg_le_abs _
      linarith))⟩



/-- **Step 3 of Section 4 at a positive threshold, run on the neighbour-buffered cluster in the
ball.**  The cluster is taken around the vertices inside the ball of radius `m` whose value, or
the value at one of whose neighbours, exceeds the threshold.  A vertex of the cycle inside that
ball therefore has no such neighbour, and one outside it that does have such a neighbour sits in
the buffer of the sphere; so the walk along a face of the cluster from a vertex of the cycle
outside that buffer is stopped strictly inside the cycle, where every neighbour is enclosed. -/
theorem surroundedBy_of_component_band_buffered (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles) (hFW : Q.embedding.FaceWalks)
    {L : ℕ} (hL : Q.embedding.FaceBound L)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) {A B : ℝ} (hAB : A < B) (o : V) (m r : ℕ) (hLr : L + 1 ≤ r)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {x₀ : V} (hx₀m : Q.graph.dist o x₀ ≤ m) (hx₀f : A < |f x₀|)
    (hbdd : Bornology.IsBounded
      (Q.embedding.clusterRegion {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ A < |f v|) ∧
        Q.graph.dist o y ≤ m}))
    (hcb : Q.embedding.HasComponentBoundary
      {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ A < |f v|) ∧ Q.graph.dist o y ≤ m} x₀)
    (hconf : ∀ z : V, Q.embedding.pos z ∈ frontier (connectedComponentIn
        (Q.embedding.clusterRegion {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ A < |f v|) ∧
          Q.graph.dist o y ≤ m}) (Q.embedding.pos x₀)) →
      Q.graph.dist o z ≤ m + L)
    (hharmreg : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ z ∈ Q.embedding.cycleRegion γ, LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    (hup : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ y ∈ Q.embedding.cycleRegion γ, |f y| ≤ A → ∀ u, Q.graph.Adj y u → B ≤ f u →
      ∃ v, Q.graph.Adj y v ∧ f v < -A)
    (hdn : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ y ∈ Q.embedding.cycleRegion γ, |f y| ≤ A → ∀ u, Q.graph.Adj y u → f u ≤ -B →
      ∃ v, Q.graph.Adj y v ∧ A < f v) :
    ∃ D : Finset V, (∀ z ∈ D, Q.graph.dist o z ≤ m + r ∧
        ∃ y, Q.graph.dist z y ≤ r ∧ A < |f y| ∧ |f y| < B) ∧
      Q.SurroundedBy r {x : V | |f x| ≤ A} {x : V | A < f x} {x : V | f x < -A} D o m x₀ := by
  classical
  set W : Set V := {x : V | |f x| ≤ A} with hW
  set N : Set V := {y | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ A < |f v|) ∧
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
  have hdich : ∀ z ∈ γ.support, |f z| ≤ A ∨ m < Q.graph.dist o z := by
    intro z hz
    by_cases hd : Q.graph.dist o z ≤ m
    · refine Or.inl ?_
      by_contra hcon
      exact hout z hz ⟨⟨z, Or.inl rfl, lt_of_not_ge hcon⟩, hd⟩
    · exact Or.inr (lt_of_not_ge hd)
  have hNmem : ∀ z, A < |f z| → Q.graph.dist o z ≤ m → z ∈ N :=
    fun z hz hd => ⟨⟨z, Or.inl rfl, hz⟩, hd⟩
  obtain ⟨u, hu, hfar⟩ :=
    exists_far_mem_cycleRegion_abs Q hc o m f A hharm hNmem hx₀m hx₀f hout hreg
  have hzero : ∀ z ∈ γ.support,
      ¬ UCPlanar.NearBoundaryOutside Q.graph W o m r z → z ∈ W :=
    mem_of_not_nearBoundaryOutside Q W o m r γ hdich hconf'
  refine ⟨γ.support.toFinset.filter
      (fun z => ∃ y, Q.graph.dist z y ≤ L ∧ A < |f y| ∧ |f y| < B), ?_, ?_⟩
  · intro z hz
    rw [Finset.mem_filter, List.mem_toFinset] at hz
    obtain ⟨y, hy1, hy2, hy3⟩ := hz.2
    exact ⟨hconf' z hz.1, y, by omega, hy2, hy3⟩
  · refine surroundedBy_of_cycle_discard Q hc f A o m r hcyc hreg ⟨u, hu, hfar⟩ hdich hconf'
      (hharmreg b γ hreg hconfL) _ ?_
    intro z hz hnz hnD
    have hfz : |f z| ≤ A := hzero z hz hnz
    have hstop : ∀ y ∈ Q.embedding.cycleRegion γ, Q.graph.dist z y ≤ L →
        (∃ v, Q.graph.Adj y v ∧ A < |f v|) →
        ∀ v, Q.graph.Adj y v → v ∈ Q.embedding.cycleRegion γ := by
      intro y hy hzy hex v hv
      by_cases hyc : y ∈ γ.support
      · exfalso
        obtain ⟨v', hv', hfv'⟩ := hex
        have hyN : y ∉ N := hout y hyc
        have hyfar : m < Q.graph.dist o y := by
          by_contra hcon
          exact hyN ⟨⟨v', Or.inr hv', hfv'⟩, not_lt.mp hcon⟩
        have hyL : Q.graph.dist o y ≤ m + L := hconfL y hyc
        have hyv : Q.graph.dist y v' = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hv'
        have hzv : Q.graph.dist z v' ≤ Q.graph.dist z y + Q.graph.dist y v' :=
          Q.connected.dist_triangle
        have hov : Q.graph.dist o v' = Q.graph.dist o y ∨
            Q.graph.dist o v' = Q.graph.dist o y + 1 ∨
            Q.graph.dist o v' = Q.graph.dist o y - 1 := SimpleGraph.Adj.diff_dist_adj hv'
        refine hnz ⟨v', by omega, ?_, by omega, by omega⟩
        simp only [Set.mem_setOf_eq, not_le]
        exact hfv'
      · exact adj_mem_cycleRegion Q.embedding γ hy hyc hv
    have hres := facePathToSigns_cluster_band_stop Q hFW hL f hAB
      (N := N) (fun y hy => hy.1)
      hx₀N hwt hin (hup b γ hreg hconfL) (hdn b γ hreg hconfL) hstop hz hfz
    rcases hres with h | h
    · exact h
    · exact absurd (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hz, h⟩) hnD

end UCPlanar.Support
