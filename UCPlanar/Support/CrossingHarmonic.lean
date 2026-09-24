/- The diagonal sequence solves the weighted graph equation at every vertex. -/
import UCPlanar.Support.CrossingLaplacian
import UCPlanar.Support.CounterexampleAlgebra
open scoped Classical

theorem UCPlanar.Support.diagonal_laplacian (a b t d : ℝ)
    (ha : 0<a) (hb : 0<b) (ht : 0<t) (hd : 0<d)
    (hbalance : t*((-b/a)^2+(-b/a)⁻¹^2-2)+d*((-b/a)+(-b/a)⁻¹-2)-2*(a+b)=0)
    (x : LatticeProb.Site 2) :
    LatticeProb.Network.netLaplacian UCPlanar.crossingGraph
      (UCPlanar.crossingConductance a b t d) (UCPlanar.diagonalFunction a b) x = 0 := by
  rw [UCPlanar.Support.crossing_laplacian a b t d ha hb ht hd]
  have hq := UCPlanar.Support.ratio_nonzero a b ha hb
  by_cases he : Even (x 0 + x 1)
  · simp only [if_pos he]
    have hn := UCPlanar.Support.nearest_diagonal (x 0) (x 1) (Int.even_iff.mp he)
    by_cases hx : x 0 = x 1
    · have hs := UCPlanar.Support.diagonal_sequence_balance (-b/a) a b t d hq hbalance (x 0)
      simp only [hx] at hs
      simp (disch := omega) [UCPlanar.diagonalFunction, LatticeProb.unit, UCPlanar.diagonalStep, hx]
      split_ifs <;> first | omega | linear_combination hs
    · simp [UCPlanar.diagonalFunction, LatticeProb.unit, UCPlanar.diagonalStep, hx]
      split_ifs <;> first | omega | norm_num
  · simp only [if_neg he, zero_mul, add_zero]
    have hx : x 0 ≠ x 1 := UCPlanar.Support.diagonal_parity (x 0) (x 1) (by simpa [Int.even_iff] using he)
    by_cases h1 : x 0 = x 1 + 1
    · have hr := UCPlanar.Support.diagonal_recurrence a b (ne_of_gt ha) (ne_of_gt hb) (x 0)
      simp only [h1, add_sub_cancel_right] at hr
      simp (disch := omega) [UCPlanar.diagonalFunction, LatticeProb.unit, h1]
      split_ifs <;> first | omega | linear_combination hr
    · by_cases h2 : x 1 = x 0 + 1
      · have hr := UCPlanar.Support.diagonal_recurrence a b (ne_of_gt ha) (ne_of_gt hb) (x 1)
        simp only [h2, add_sub_cancel_right] at hr
        simp (disch := omega) [UCPlanar.diagonalFunction, LatticeProb.unit, h2]
        split_ifs <;> first | omega | linear_combination hr
      · simp [UCPlanar.diagonalFunction, LatticeProb.unit, hx, h1]
        split_ifs <;> first | omega | norm_num
