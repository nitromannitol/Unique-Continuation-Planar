/-
Membership, monotonicity and the effect of a lattice translation on the geometric
squares of a periodic graph.
-/
import UCPlanar.Support.Poly.Difference

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- A vertex `x` lies in the square `P.square R` iff each coordinate of its position
`P.pos x` has absolute value at most `R`. -/
theorem mem_square_iff {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (x : V) :
    x ∈ P.square R ↔ ∀ i, |P.pos x i| ≤ R := by
  simp [UCPlanar.PeriodicGraph.square, Set.Finite.mem_toFinset]

/-- The squares `P.square r` are monotone increasing in the radius `r`. -/
theorem square_mono {V : Type*} (P : UCPlanar.PeriodicGraph V) {r s : ℝ} (hrs : r ≤ s) :
    P.square r ⊆ P.square s := by
  intro x hx
  rw [mem_square_iff] at hx ⊢
  exact fun i => le_trans (hx i) hrs

/-- A lattice shift by `a` moves a vertex from the square of radius `t` into the square of
radius `t + M`, where `M` bounds the shift's own period coordinates. -/
theorem shift_mem_square {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (a : LatticeProb.Site 2) (M : ℝ) (hM : ∀ i, |P.period (fun i => (a i : ℝ)) i| ≤ M)
    (t : ℝ) (x : V) (hx : x ∈ P.square t) : P.shift a x ∈ P.square (t + M) := by
  rw [mem_square_iff] at hx ⊢
  intro i
  rw [P.pos_shift a x]
  calc |P.pos x i + P.period (fun j => (a j : ℝ)) i|
      ≤ |P.pos x i| + |P.period (fun j => (a j : ℝ)) i| := abs_add_le _ _
    _ ≤ t + M := add_le_add (hx i) (hM i)

end UCPlanar.Support
