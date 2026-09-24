/- The shared network Laplacian as its explicit eight-term sum. -/
import UCPlanar.Support.CrossingFinite
import UCPlanar.Support.CrossingNeighbors
import UCPlanar.Support.CrossingConductance
import UCPlanar.Support.CrossingCoefficients
import UCPlanar.Support.CrossingSum
open scoped Classical BigOperators

theorem UCPlanar.Support.crossing_laplacian (a b t d : ℝ)
    (ha : 0<a) (hb : 0<b) (ht : 0<t) (hd : 0<d)
    (f : LatticeProb.Site 2 → ℝ) (x : LatticeProb.Site 2) :
    LatticeProb.Network.netLaplacian UCPlanar.crossingGraph
      (UCPlanar.crossingConductance a b t d) f x =
    (if Even (x 0+x 1) then a else b)*(f (x-LatticeProb.unit 0)-f x) +
    (if Even (x 0+x 1) then a else b)*(f (x-LatticeProb.unit 1)-f x) +
    (if Even (x 0+x 1) then b else a)*(f (x+LatticeProb.unit 0)-f x) +
    (if Even (x 0+x 1) then b else a)*(f (x+LatticeProb.unit 1)-f x) +
    (if Even (x 0+x 1) then t else 0)*(f (x+(2:ℤ) • UCPlanar.diagonalStep)-f x) +
    (if Even (x 0+x 1) then t else 0)*(f (x-(2:ℤ) • UCPlanar.diagonalStep)-f x) +
    (if Even (x 0+x 1) then d else 0)*(f (x+UCPlanar.diagonalStep)-f x) +
    (if Even (x 0+x 1) then d else 0)*(f (x-UCPlanar.diagonalStep)-f x) := by
  let S : Finset (LatticeProb.Site 2) :=
    {x - LatticeProb.unit 0, x - LatticeProb.unit 1,
     x + LatticeProb.unit 0, x + LatticeProb.unit 1,
     x + (2 : ℤ) • UCPlanar.diagonalStep, x - (2 : ℤ) • UCPlanar.diagonalStep,
     x + UCPlanar.diagonalStep, x - UCPlanar.diagonalStep}
  rw [LatticeProb.Network.netLaplacian,
    LatticeProb.Network.sum_neighborFinset_eq_sum x S
      (fun y => UCPlanar.crossingConductance a b t d x y * (f y - f x)) ?_ ?_]
  · change (∑ y ∈ S, _) = _
    rw [UCPlanar.Support.sum_eight]
    rw [UCPlanar.Support.weight_minus_zero, UCPlanar.Support.weight_minus_one,
      UCPlanar.Support.weight_plus_zero, UCPlanar.Support.weight_plus_one,
      UCPlanar.Support.weight_two_plus, UCPlanar.Support.weight_two_minus,
      UCPlanar.Support.weight_diag_plus, UCPlanar.Support.weight_diag_minus]
  · intro y hy
    rw [(UCPlanar.Support.crossing_isCond a b t d ha hb ht hd).zero_of_not_adj hy, zero_mul]
  · intro y hy _
    exact UCPlanar.Support.neighbor_mem_eight x y ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
