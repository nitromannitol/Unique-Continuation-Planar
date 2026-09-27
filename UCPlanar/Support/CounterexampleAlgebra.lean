/-
Algebra and lattice parity for the diagonal harmonic function of Section 5.
The ratio is `-A₂/A₁`, and the fourth conductance is
`A₃ (A₁-A₂)²/(A₁ A₂) - 2 A₁ A₂/(A₁+A₂)`.
-/
import LatticeProb.Network.Basic
import Mathlib.Tactic

open scoped BigOperators Classical
set_option autoImplicit false

/-- The diagonal ratio `-b/a` is nonzero when both conductances `a` and `b` are positive. -/
theorem UCPlanar.Support.ratio_nonzero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : -b/a ≠ 0 := by
  exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt hb)) (ne_of_gt ha)

/-- **The fourth conductance is positive above threshold.**  For conductances `a ≠ b`, the
quantity `t·(a-b)²/(ab) - 2ab/(a+b)` is positive once `t` exceeds `2a²b²/((a-b)²(a+b))`. -/
theorem UCPlanar.Support.fourth_positive (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (ht : 2 * a^2 * b^2 / ((a-b)^2 * (a+b)) < t) :
    0 < t * (a-b)^2 / (a*b) - 2*a*b/(a+b) := by
  have hs : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hd : 0 < (a-b)^2*(a+b) := mul_pos hs (add_pos ha hb)
  have ht' := (div_lt_iff₀ hd).mp ht
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (add_pos ha hb) (mul_pos ha hb)).mpr
  nlinarith

/-- **The conductance balance equation holds at the diagonal ratio.**  With `q = -b/a` and `d`
the fourth conductance from `fourth_positive`, the balance identity
`t(q²+q⁻¹²-2)+d(q+q⁻¹-2)-2(a+b)=0` is a pure field computation via `field_simp`/`ring`. -/
theorem UCPlanar.Support.diagonal_balance (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a+b ≠ 0) :
    let q := -b/a
    let d := t*(a-b)^2/(a*b)-2*a*b/(a+b)
    t*(q^2+q⁻¹^2-2)+d*(q+q⁻¹-2)-2*(a+b)=0 := by
  dsimp
  field_simp
  ring

/-- **The diagonal geometric sequence satisfies its two-term recurrence.**  For every integer
`i`, `a·q^i + b·q^{i-1} = 0` where `q = -b/a`, obtained by factoring one power of `q` out of
`q^i` and clearing denominators. -/
theorem UCPlanar.Support.diagonal_recurrence (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (i : ℤ) :
    a * (-b/a)^i + b * (-b/a)^(i-1) = 0 := by
  have hq : -b/a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have he : (-b/a)^i = (-b/a)^(i-1)*(-b/a) := by
    conv_lhs => rw [show i = (i-1)+1 by omega]
    rw [zpow_add₀ hq, zpow_one]
  rw [he]
  field_simp
  ring

/-- The step-one discrete second difference of the geometric sequence `q^i` factors as
`q^{i+1}+q^{i-1}-2q^i = (q+q⁻¹-2)·q^i`, a pure algebraic identity for `q ≠ 0`. -/
theorem UCPlanar.Support.diagonal_shift_plus (q : ℝ) (hq : q ≠ 0) (i : ℤ) :
    q^(i+1)+q^(i-1)-2*q^i = (q+q⁻¹-2)*q^i := by
  rw [zpow_add₀ hq, zpow_sub₀ hq, zpow_one, div_eq_mul_inv]
  ring

/-- The step-two discrete second difference of the geometric sequence `q^i` factors as
`q^{i+2}+q^{i-2}-2q^i = (q²+q⁻¹²-2)·q^i`, the step-two analogue of `diagonal_shift_plus`. -/
theorem UCPlanar.Support.diagonal_shift_two (q : ℝ) (hq : q ≠ 0) (i : ℤ) :
    q^(i+2)+q^(i-2)-2*q^i = (q^2+q⁻¹^2-2)*q^i := by
  norm_num only [zpow_add₀ hq, zpow_sub₀ hq, div_eq_mul_inv]
  field_simp

/-- **The conductance balance equation propagates to every diagonal index.**  Given the balance
identity `h` (as produced by `diagonal_balance`) at one point, factoring both discrete
differences via `diagonal_shift_two` and `diagonal_shift_plus` shows the shifted identity
`t(q^{i+2}+q^{i-2}-2q^i)+d(q^{i+1}+q^{i-1}-2q^i)-2(a+b)q^i=0` holds for every integer `i`. -/
theorem UCPlanar.Support.diagonal_sequence_balance (q a b t d : ℝ) (hq : q ≠ 0)
    (h : t*(q^2+q⁻¹^2-2)+d*(q+q⁻¹-2)-2*(a+b)=0) (i : ℤ) :
    t*(q^(i+2)+q^(i-2)-2*q^i)+d*(q^(i+1)+q^(i-1)-2*q^i)-2*(a+b)*q^i=0 := by
  have hp : q^(i+1)+q^(i-1)-2*q^i = (q+q⁻¹-2)*q^i := by
    rw [zpow_add₀ hq, zpow_sub₀ hq, zpow_one, div_eq_mul_inv]
    ring
  have ht : q^(i+2)+q^(i-2)-2*q^i = (q^2+q⁻¹^2-2)*q^i := by
    norm_num only [zpow_add₀ hq, zpow_sub₀ hq, div_eq_mul_inv]
    field_simp
  rw [hp, ht]
  calc
    t * ((q ^ 2 + q⁻¹ ^ 2 - 2) * q ^ i) +
        d * ((q + q⁻¹ - 2) * q ^ i) - 2 * (a + b) * q ^ i =
        (t*(q^2+q⁻¹^2-2)+d*(q+q⁻¹-2)-2*(a+b))*q^i := by ring
    _ = 0 := by rw [h, zero_mul]

/-- If `i+j` is odd then `i ≠ j`, since `i=j` would force the sum `i+j=2i` to be even. -/
theorem UCPlanar.Support.diagonal_parity (i j : ℤ) (h : (i+j)%2 ≠ 0) : i ≠ j := by
  omega

/-- **Same-parity diagonal sites are never unit-shift neighbors.**  If `i+j` is even then none of
`i+1`, `i-1` equals `j`, and `i` equals neither `j+1` nor `j-1`, since a unit shift always
flips the parity of the sum. -/
theorem UCPlanar.Support.nearest_diagonal (i j : ℤ) (h : (i+j)%2=0) :
    i+1 ≠ j ∧ i-1 ≠ j ∧ i ≠ j+1 ∧ i ≠ j-1 := by
  omega

/-- The four-way unit-shift-adjacency disjunction `i+1=j ∨ i-1=j ∨ i=j+1 ∨ i=j-1` collapses to
the two distinct relations `i=j+1 ∨ j=i+1`, since each pair of clauses restates the other. -/
theorem UCPlanar.Support.odd_neighbors_pair (i j : ℤ) :
    (i+1=j ∨ i-1=j ∨ i=j+1 ∨ i=j-1) ↔ (i=j+1 ∨ j=i+1) := by
  omega

/-- Cancelling a common shift `k` from both sides: `i+k=j+k ↔ i=j`. -/
theorem UCPlanar.Support.diagonal_shift_iff (i j k : ℤ) : i+k=j+k ↔ i=j := by
  omega
