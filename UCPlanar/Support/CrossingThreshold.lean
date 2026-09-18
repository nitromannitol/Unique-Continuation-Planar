/- Positivity of the third conductance under the threshold in Section 5. -/
import UCPlanar.Support.CounterexampleAlgebra

theorem UCPlanar.Support.third_positive (a b t : ℝ) (ha : 0<a) (hb : 0<b)
    (hab : a ≠ b) (ht : 2*a^2*b^2/((a-b)^2*(a+b)) < t) : 0<t := by
  apply lt_trans _ ht
  exact div_pos (by positivity)
    (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hab)) (add_pos ha hb))
