/- Step 3 of Sections 3 and 4 with every topological input discharged: the boundary cycles come
from the cited splitting theorem, the face walks from the cited unicoherence, the filled cluster
is bounded because the cluster set lies in a ball and faces have bounded diameter, its frontier is
drawn by a finite edge set and stays within the face bound of that ball.  What is left is the
harmonicity of the function at the vertices the cycle encloses. -/
import UCPlanar.Support.TopoStep3Component
import UCPlanar.Support.TopoStep3Band
import UCPlanar.Support.TopoComponentArcs
import UCPlanar.Support.TopoClusterBounded
import UCPlanar.Support.ZeroAssemble
import UCPlanar.Support.TopoPolyCycle
import UCPlanar.External.EdgeSplitting
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

/-- The cluster set of Step 3 lies in the ball of radius `m`, hence is finite. -/
theorem finite_bufferedCluster (Q : UCPlanar.PeriodicPlaneGraph V) (f : V → ℝ) (A : ℝ)
    (o : V) (m : ℕ) :
    {y : V | (∃ v, (v = y ∨ Q.graph.Adj y v) ∧ A < |f v|) ∧ Q.graph.dist o y ≤ m}.Finite := by
  classical
  refine Set.Finite.subset (Q.toPeriodicGraph.ball o m).finite_toSet ?_
  intro y hy
  exact (mem_ball_iff_dist Q.toPeriodicGraph o y m).mpr hy.2

/-- **Step 3 of Section 3, zero case, with every topological input discharged.** -/
theorem surroundedBy_zero_closed (Q : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting Q.embedding)
    (hU : UCPlanar.External.Unicoherence Q.embedding)
    {L : ℕ} (hL : Q.embedding.FaceBound L)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) (o : V) (m r : ℕ) (hLr : L + 1 ≤ r)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {x₀ : V} (hx₀m : Q.graph.dist o x₀ ≤ m) (hx₀f : (0:ℝ) < |f x₀|)
    (hharmreg : ∀ (b : V) (γ : Q.graph.Walk b b), x₀ ∈ Q.embedding.cycleRegion γ →
      (∀ w ∈ γ.support, Q.graph.dist o w ≤ m + L) →
      ∀ z ∈ Q.embedding.cycleRegion γ, LatticeProb.Network.netLaplacian Q.graph c f z = 0) :
    Q.SurroundedBy r {x : V | |f x| ≤ 0} {x : V | 0 < f x} {x : V | f x < 0} ∅ o m x₀ := by
  classical
  have hbdd := isBounded_clusterRegion_of_finite Q (finite_bufferedCluster Q f 0 o m)
  exact surroundedBy_of_component_zero_buffered Q
    (hasBoundaryCycles Q.embedding (edgeSplitting_of_external Q.embedding hES))
    (faceWalks_of_unicoherence Q hU) hL hc f o m r hLr hharm hx₀m hx₀f hbdd
    (hasComponentBoundary Q _ x₀ hbdd)
    (fun z hz => dist_le_of_pos_mem_frontier_component Q hL (faceWalks_of_unicoherence Q hU)
      (fun y hy => hy.2) hz)
    hharmreg

/-- **Step 3 of Section 4 at a positive threshold, with every topological input discharged.** -/
theorem surroundedBy_band_closed (Q : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting Q.embedding)
    (hU : UCPlanar.External.Unicoherence Q.embedding)
    {L : ℕ} (hL : Q.embedding.FaceBound L)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond Q.graph c)
    (f : V → ℝ) {A B : ℝ} (hAB : A < B) (o : V) (m r : ℕ) (hLr : L + 1 ≤ r)
    (hharm : ∀ z ∈ Q.toPeriodicGraph.ball o m,
      LatticeProb.Network.netLaplacian Q.graph c f z = 0)
    {x₀ : V} (hx₀m : Q.graph.dist o x₀ ≤ m) (hx₀f : A < |f x₀|)
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
  have hbdd := isBounded_clusterRegion_of_finite Q (finite_bufferedCluster Q f A o m)
  exact surroundedBy_of_component_band_buffered Q
    (hasBoundaryCycles Q.embedding (edgeSplitting_of_external Q.embedding hES))
    (faceWalks_of_unicoherence Q hU) hL hc f hAB o m r hLr hharm hx₀m hx₀f hbdd
    (hasComponentBoundary Q _ x₀ hbdd)
    (fun z hz => dist_le_of_pos_mem_frontier_component Q hL (faceWalks_of_unicoherence Q hU)
      (fun y hy => hy.2) hz)
    hharmreg hup hdn

end UCPlanar.Support
