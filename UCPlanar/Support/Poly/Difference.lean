/-
Forward difference operators along lattice shifts, and their iterates.
-/
import UCPlanar.Support.Poly.Basic
import UCPlanar.Support.Poly.Caccioppoli

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar

/-- The forward difference of `f` along the lattice shift `a`. -/
def PeriodicGraph.diff {V : Type*} (P : PeriodicGraph V) (a : LatticeProb.Site 2)
    (f : V → ℝ) : V → ℝ :=
  fun x => f (P.shift a x) - f x

/-- The `m`-fold forward difference of `f` along the lattice shift `a`. -/
def PeriodicGraph.iterDiff {V : Type*} (P : PeriodicGraph V) (a : LatticeProb.Site 2)
    (m : ℕ) (f : V → ℝ) : V → ℝ :=
  (P.diff a)^[m] f

/-- The set of points whose first `m` translates along `a` all lie in `S`. -/
def PeriodicGraph.shiftBall {V : Type*} (P : PeriodicGraph V) (a : LatticeProb.Site 2)
    (m : ℕ) (S : Set V) : Set V :=
  {x | ∀ k ≤ m, P.shift (k • a) x ∈ S}

end UCPlanar

theorem netLaplacian_shift {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hp : P.PeriodicConductance c) (a : LatticeProb.Site 2) (f : V → ℝ) (x : V) :
    LatticeProb.Network.netLaplacian P.graph c (fun y => f (P.shift a y)) x
      = LatticeProb.Network.netLaplacian P.graph c f (P.shift a x) := by
  rw [LatticeProb.Network.netLaplacian, LatticeProb.Network.netLaplacian]
  refine Finset.sum_bij (fun y _ => P.shift a y) ?_ ?_ ?_ ?_
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact (P.shift_adj a x y).mpr hy
  · intro y₁ _ y₂ _ h
    have h' := congrArg (P.shift (-a)) h
    rw [← P.shift_add, ← P.shift_add, neg_add_cancel, P.shift_zero, P.shift_zero] at h'
    exact h'
  · intro y hy
    refine ⟨P.shift (-a) y, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      exact (P.shift_adj a x (P.shift (-a) y)).mp (by
        rw [← P.shift_add, add_neg_cancel, P.shift_zero]; exact hy)
    · rw [← P.shift_add, add_neg_cancel, P.shift_zero]
  · intro y hy
    rw [hp a x y]

theorem harmonic_shift_sub {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hp : P.PeriodicConductance c) (a : LatticeProb.Site 2) (f : V → ℝ) (S : Set V)
    (hS : ∀ x ∈ S, P.shift a x ∈ S)
    (hf : LatticeProb.Network.HarmonicOn P.graph c f S) :
    LatticeProb.Network.HarmonicOn P.graph c (fun y => f (P.shift a y) - f y) S := by
  intro x hx
  have h : (fun y => f (P.shift a y) - f y)
      = (fun y => f (P.shift a y)) + (fun y => -f y) := by
    funext y; exact sub_eq_add_neg _ _
  rw [h, LatticeProb.Network.netLaplacian_add,
    UCPlanar.Support.netLaplacian_shift (P := P) (c := c) (hc := hp) (a := a) (f := f) (x := x),
    hf (P.shift a x) (hS x hx)]
  have hneg : (fun y => -f y) = (fun y => (-1 : ℝ) * f y) := by
    funext y; ring
  rw [hneg, LatticeProb.Network.netLaplacian_smul, hf x hx]
  ring

theorem moser_on_difference {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c) (w : ℝ) (hw : 0 < w)
    (hW : ∀ x ∈ P.square 1, w ≤ LatticeProb.Network.weight P.graph c x)
    (a : LatticeProb.Site 2)
    (h13 : P.square 1 ⊆ P.square 3)
    (h34 : P.square 3 ⊆ P.square 4)
    (hshift : ∀ x ∈ P.square 3, P.shift a x ∈ P.square 4)
    (f : V → ℝ)
    (hf : ∀ x ∈ P.square 4, LatticeProb.Network.netLaplacian P.graph c f x = 0) :
    ∑ x ∈ P.square 1, (f (P.shift a x) - f x) ^ 2
      ≤ (1 / w) * ∑ x ∈ P.square 1, ∑ y ∈ P.graph.neighborFinset x,
          c x y * (f (P.shift a y) - f y) ^ 2 := by
  have hg_eq : (fun y => f (P.shift a y) - f y)
      = (fun y => f (P.shift a y)) + (fun y => -f y) := by
    funext y; exact sub_eq_add_neg _ _
  have hneg : ∀ x, LatticeProb.Network.netLaplacian P.graph c (fun y => -f y) x
      = -LatticeProb.Network.netLaplacian P.graph c f x := by
    intro x
    have h : (fun y => -f y) = (fun y => (-1 : ℝ) * f y) := by funext y; ring
    rw [h, LatticeProb.Network.netLaplacian_smul]
    ring
  have hg : ∀ x ∈ P.square 1,
      LatticeProb.Network.netLaplacian P.graph c (fun y => f (P.shift a y) - f y) x = 0 := by
    intro x hx
    have h1 : LatticeProb.Network.netLaplacian P.graph c (fun y => f (P.shift a y)) x
        = LatticeProb.Network.netLaplacian P.graph c f (P.shift a x) :=
      UCPlanar.Support.netLaplacian_shift P c hp f a x
    have h2 : LatticeProb.Network.netLaplacian P.graph c (fun y => -f y) x
        = -LatticeProb.Network.netLaplacian P.graph c f x := hneg x
    have h3 : LatticeProb.Network.netLaplacian P.graph c f (P.shift a x) = 0 :=
      hf (P.shift a x) (hshift x (h13 hx))
    have h4 : LatticeProb.Network.netLaplacian P.graph c f x = 0 := hf x (h34 (h13 hx))
    rw [hg_eq, LatticeProb.Network.netLaplacian_add, h1, h2, h3, h4]
    ring
  exact UCPlanar.Support.moser_estimate hc (P.square 1)
    (fun y => f (P.shift a y) - f y) w hw hg hW
