/-
Translation invariance of the network Laplacian on a periodic graph, and the
finite supremum norm.
-/
import UCPlanar.Support.Periodic
import UCPlanar.Support.Harmonic

open scoped BigOperators Classical
set_option autoImplicit false

/-- The network Laplacian commutes with a lattice translation, by periodicity of
the conductance. -/
theorem UCPlanar.Support.netLaplacian_shift {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : P.PeriodicConductance c) (f : V → ℝ)
    (a : LatticeProb.Site 2) (x : V) :
    LatticeProb.Network.netLaplacian P.graph c (fun y => f (P.shift a y)) x
      = LatticeProb.Network.netLaplacian P.graph c f (P.shift a x) := by
  classical
  rw [LatticeProb.Network.netLaplacian, LatticeProb.Network.netLaplacian]
  refine Finset.sum_bij (fun y _ => P.shift a y) ?_ ?_ ?_ ?_
  · intro y hy
    exact (SimpleGraph.mem_neighborFinset P.graph (P.shift a x) (P.shift a y)).mpr
      (((P.shift_adj a x y).mpr) ((SimpleGraph.mem_neighborFinset P.graph x y).mp hy))
  · intro y1 hy1 y2 hy2 h
    have h1 : P.shift (-a) (P.shift a y1) = P.shift (-a) (P.shift a y2) := by rw [h]
    rw [← P.shift_add, neg_add_cancel, P.shift_zero, ← P.shift_add, neg_add_cancel,
      P.shift_zero] at h1
    exact h1
  · intro b hb
    refine ⟨P.shift (-a) b, ?_, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset P.graph x (P.shift (-a) b)).mpr
        ((P.shift_adj a x (P.shift (-a) b)).mp (by
          rw [← P.shift_add, add_neg_cancel, P.shift_zero]
          exact (SimpleGraph.mem_neighborFinset P.graph (P.shift a x) b).mp hb))
    · rw [← P.shift_add, add_neg_cancel, P.shift_zero]
  · intro y hy
    rw [hc a x y]

/-- A translation difference of a harmonic function is harmonic on the set of
points whose translate also lies in the domain. -/
theorem UCPlanar.Support.harmonicOn_shift_sub {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : P.PeriodicConductance c) (f : V → ℝ) (S : Set V)
    (a : LatticeProb.Site 2)
    (hf : LatticeProb.Network.HarmonicOn P.graph c f S) :
    LatticeProb.Network.HarmonicOn P.graph c (fun y => f (P.shift a y) - f y)
      (S ∩ {x | P.shift a x ∈ S}) := by
  intro x hx
  have h1 : LatticeProb.Network.netLaplacian P.graph c (fun y => f (P.shift a y)) x
      = LatticeProb.Network.netLaplacian P.graph c f (P.shift a x) :=
    UCPlanar.Support.netLaplacian_shift P c hc f a x
  have h2 : (fun y => f (P.shift a y) - f y)
      = (fun y => f (P.shift a y)) + (fun y => (-1 : ℝ) * f y) := by
    funext y
    simp [sub_eq_add_neg]
  rw [h2, LatticeProb.Network.netLaplacian_add, h1, LatticeProb.Network.netLaplacian_smul,
    hf (P.shift a x) hx.2, hf x hx.1]
  ring

/-- Monotonicity of the finite supremum norm. -/
theorem UCPlanar.Support.supNorm_mono {V : Type*} {S T : Finset V} (hST : S ⊆ T) (f : V → ℝ) :
    UCPlanar.supNorm S f ≤ UCPlanar.supNorm T f := by
  classical
  simp only [UCPlanar.supNorm]
  exact_mod_cast Finset.sup_mono hST
