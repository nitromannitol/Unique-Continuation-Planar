/- Step 3 of Section 3 with local finiteness of the faces discharged: the faces of a periodic
plane drawing are locally finite, so the cluster construction needs only the boundary cycle
statement together with the local conditions on the cluster. -/
import UCPlanar.Support.TopoLines
import UCPlanar.Support.TopoClusterReach
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

/-- **The cycle produced by Step 3, with local finiteness of the faces discharged.** -/
theorem exists_step3_cycle_reaching' (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles)
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
        {y | y ∉ {x : V | |f x| ≤ A} ∧ Q.graph.dist o y ≤ m}) :=
  exists_step3_cycle_reaching Q hbc (locallyFiniteFaces Q) hc f A o m hharm hx₀m hx₀f hbdd hcb

/-- **Step 3 of Section 3 end to end, with local finiteness of the faces discharged.**  What is
left of the hypotheses is the boundary cycle theorem, the boundedness of the filled cluster and
its finite boundary edge set, and the three local conditions of the cluster. -/
theorem surroundedBy_of_cluster' (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles)
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
    Q.SurroundedBy r {x : V | |f x| ≤ A} {x : V | A < f x} {x : V | f x < -A} ∅ o m x₀ :=
  surroundedBy_of_cluster Q hbc (locallyFiniteFaces Q) hc f A o m r hharm hx₀m hx₀f hbdd hcb
    hconf hharmreg hface

end UCPlanar.Support
