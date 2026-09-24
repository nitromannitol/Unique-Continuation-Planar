/-
Algebra and lattice parity for the diagonal harmonic function of Section 5.
The ratio is `-A₂/A₁`, and the fourth conductance is
`A₃ (A₁-A₂)²/(A₁ A₂) - 2 A₁ A₂/(A₁+A₂)`.
-/
import LatticeProb.Network.Basic
import Mathlib.Tactic

open scoped BigOperators Classical
set_option autoImplicit false

theorem UCPlanar.Support.ratio_nonzero (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : -b/a ≠ 0 := by
  exact div_ne_zero (neg_ne_zero.mpr (ne_of_gt hb)) (ne_of_gt ha)

theorem UCPlanar.Support.fourth_positive (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (ht : 2 * a^2 * b^2 / ((a-b)^2 * (a+b)) < t) :
    0 < t * (a-b)^2 / (a*b) - 2*a*b/(a+b) := by
  have hs : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hd : 0 < (a-b)^2*(a+b) := mul_pos hs (add_pos ha hb)
  have ht' := (div_lt_iff₀ hd).mp ht
  apply sub_pos.mpr
  apply (div_lt_div_iff₀ (add_pos ha hb) (mul_pos ha hb)).mpr
  nlinarith

theorem UCPlanar.Support.diagonal_balance (a b t : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a+b ≠ 0) :
    let q := -b/a
    let d := t*(a-b)^2/(a*b)-2*a*b/(a+b)
    t*(q^2+q⁻¹^2-2)+d*(q+q⁻¹-2)-2*(a+b)=0 := by
  dsimp
  field_simp
  ring

theorem UCPlanar.Support.diagonal_recurrence (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (i : ℤ) :
    a * (-b/a)^i + b * (-b/a)^(i-1) = 0 := by
  have hq : -b/a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) ha
  have he : (-b/a)^i = (-b/a)^(i-1)*(-b/a) := by
    conv_lhs => rw [show i = (i-1)+1 by omega]
    rw [zpow_add₀ hq, zpow_one]
  rw [he]
  field_simp
  ring

theorem UCPlanar.Support.diagonal_shift_plus (q : ℝ) (hq : q ≠ 0) (i : ℤ) :
    q^(i+1)+q^(i-1)-2*q^i = (q+q⁻¹-2)*q^i := by
  rw [zpow_add₀ hq, zpow_sub₀ hq, zpow_one, div_eq_mul_inv]
  ring

theorem UCPlanar.Support.diagonal_shift_two (q : ℝ) (hq : q ≠ 0) (i : ℤ) :
    q^(i+2)+q^(i-2)-2*q^i = (q^2+q⁻¹^2-2)*q^i := by
  norm_num only [zpow_add₀ hq, zpow_sub₀ hq, div_eq_mul_inv]
  field_simp

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

theorem UCPlanar.Support.diagonal_parity (i j : ℤ) (h : (i+j)%2 ≠ 0) : i ≠ j := by
  omega

theorem UCPlanar.Support.nearest_diagonal (i j : ℤ) (h : (i+j)%2=0) :
    i+1 ≠ j ∧ i-1 ≠ j ∧ i ≠ j+1 ∧ i ≠ j-1 := by
  omega

theorem UCPlanar.Support.odd_neighbors_pair (i j : ℤ) :
    (i+1=j ∨ i-1=j ∨ i=j+1 ∨ i=j-1) ↔ (i=j+1 ∨ j=i+1) := by
  omega

theorem UCPlanar.Support.diagonal_shift_iff (i j k : ℤ) : i+k=j+k ↔ i=j := by
  omega
