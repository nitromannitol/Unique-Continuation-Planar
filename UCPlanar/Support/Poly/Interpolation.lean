/-
Newton interpolation on a lattice orbit: the interpolating polynomial of the
mixed-difference data, its total degree, and the remainder estimate.
-/
import UCPlanar.Support.Poly.Newton
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- The binomial polynomial `X.choose j` in one variable, as a polynomial with
real coefficients. -/
noncomputable def choosePoly (j : ℕ) : Polynomial ℝ :=
  Polynomial.C ((j.factorial : ℝ)⁻¹)
    * ∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))

/-- The binomial polynomial evaluated at a natural number is the binomial
coefficient. -/
theorem choosePoly_eval_nat (j n : ℕ) :
    (choosePoly j).eval (n : ℝ) = (n.choose j : ℝ) := by
  rw [choosePoly, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have h : ∀ i ∈ Finset.range j, (Polynomial.eval (n : ℝ)) (Polynomial.X - Polynomial.C (i : ℝ))
      = (n : ℝ) - (i : ℝ) := by
    intro i _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_congr rfl h]
  have hprod : (∏ i ∈ Finset.range j, ((n : ℝ) - (i : ℝ)))
      = ((n.descFactorial j : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    by_cases hj : j ≤ n
    · apply Finset.prod_congr rfl
      intro i hi
      have hi' : i ≤ n := by
        have : i < j := Finset.mem_range.mp hi
        omega
      rw [Nat.cast_sub hi']
    · push Not at hj
      rw [Finset.prod_eq_zero (Finset.mem_range.mpr hj) (by simp),
          Finset.prod_eq_zero (Finset.mem_range.mpr hj) (by simp)]
  rw [hprod, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero j), one_mul]

/-- The binomial polynomial has degree at most `j`. -/
theorem choosePoly_natDegree_le (j : ℕ) : (choosePoly j).natDegree ≤ j := by
  have hterm : ∀ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ)).natDegree ≤ 1 := by
    intro i _
    calc (Polynomial.X - Polynomial.C (i : ℝ)).natDegree
        ≤ max Polynomial.X.natDegree (Polynomial.C (i : ℝ)).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ 1 := by
          rw [Polynomial.natDegree_C]
          exact max_le Polynomial.natDegree_X_le (by norm_num)
  have hprod : (∏ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ))).natDegree ≤ j := by
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have h1 : ∑ i ∈ Finset.range j, (Polynomial.X - Polynomial.C (i : ℝ)).natDegree
        ≤ ∑ _i ∈ Finset.range j, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hterm i hi
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_id] at h1
    exact h1
  rw [choosePoly]
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [Polynomial.natDegree_C, zero_add]
  exact hprod

/-- The two-variable Newton interpolating polynomial of the mixed-difference
data of `F` at the origin. -/
noncomputable def newtonPoly2 (F : ℕ × ℕ → ℝ) (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1),
    MvPolynomial.C (((fwdDiff (1, 0))^[a] ((fwdDiff (0, 1))^[b] F)) (0, 0))
      * (Polynomial.toMvPolynomial (0 : Fin 2) (choosePoly a))
      * (Polynomial.toMvPolynomial (1 : Fin 2) (choosePoly b))

/-- The total degree of a univariate polynomial read in one variable is at most
its degree. -/
theorem toMvPolynomial_totalDegree_le {σ : Type*} (i : σ) (p : Polynomial ℝ) :
    ((Polynomial.toMvPolynomial i) p).totalDegree ≤ p.natDegree := by
  conv_lhs => rw [Polynomial.as_sum_range p]
  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le (fun k hk => ?_)
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X]
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X_pow]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- The interpolating polynomial has total degree at most `2 * m`. -/
theorem newtonPoly2_totalDegree_le (F : ℕ × ℕ → ℝ) (m : ℕ) :
    (newtonPoly2 F m).totalDegree ≤ 2 * m := by
  rw [newtonPoly2]
  refine MvPolynomial.totalDegree_finsetSum_le (fun a ha => ?_)
  refine MvPolynomial.totalDegree_finsetSum_le (fun b hb => ?_)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  refine le_trans (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl) ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  have ha' : a ≤ m := by have := Finset.mem_range.mp ha; omega
  have hb' : b ≤ m := by have := Finset.mem_range.mp hb; omega
  have h1 := toMvPolynomial_totalDegree_le (0 : Fin 2) (choosePoly a)
  have h2 := toMvPolynomial_totalDegree_le (1 : Fin 2) (choosePoly b)
  have h3 := choosePoly_natDegree_le a
  have h4 := choosePoly_natDegree_le b
  linarith

/-- The interpolating polynomial reproduces the mixed-difference data at the
origin. -/
theorem newtonPoly2_eval_zero (F : ℕ × ℕ → ℝ) (m : ℕ) :
    MvPolynomial.eval (fun _ : Fin 2 => (0 : ℝ)) (UCPlanar.Support.newtonPoly2 F m)
      = F (0, 0) := by
  have h0 : Polynomial.eval (0 : ℝ) (UCPlanar.Support.choosePoly 0) = 1 := by
    rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num,
      UCPlanar.Support.choosePoly_eval_nat, Nat.choose_self, Nat.cast_one]
  have hb0 : ∀ b : ℕ, b ≠ 0 → Polynomial.eval (0 : ℝ) (UCPlanar.Support.choosePoly b) = 0 := by
    intro b hb
    rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num,
      UCPlanar.Support.choosePoly_eval_nat,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb), Nat.cast_zero]
  rw [UCPlanar.Support.newtonPoly2, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single 0]
  · rw [MvPolynomial.eval_sum, Finset.sum_eq_single 0]
    · simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
      rw [Function.iterate_zero_apply, h0]
      simp
    · intro b _ hb
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
      rw [hb0 b hb]
      simp
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
  · intro a _ ha
    simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_toMvPolynomial]
    rw [hb0 a ha]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h

/-- The truncated two-variable Newton interpolating polynomial: only the mixed
differences of total order at most `m` are used, so the total degree is at most
`m`. -/
noncomputable def newtonPoly2Trunc (F : ℕ × ℕ → ℝ) (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - a),
    MvPolynomial.C (((fwdDiff (1, 0))^[a] ((fwdDiff (0, 1))^[b] F)) (0, 0))
      * (Polynomial.toMvPolynomial (0 : Fin 2) (choosePoly a))
      * (Polynomial.toMvPolynomial (1 : Fin 2) (choosePoly b))

/-- The truncated interpolating polynomial has total degree at most `m`. -/
theorem newtonPoly2Trunc_totalDegree_le (F : ℕ × ℕ → ℝ) (m : ℕ) :
    (newtonPoly2Trunc F m).totalDegree ≤ m := by
  rw [newtonPoly2Trunc]
  refine MvPolynomial.totalDegree_finsetSum_le fun a ha => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun b hb => ?_
  have key : (Polynomial.toMvPolynomial (0 : Fin 2) (choosePoly a)).totalDegree +
      (Polynomial.toMvPolynomial (1 : Fin 2) (choosePoly b)).totalDegree ≤ a + b :=
    add_le_add
      (le_trans (toMvPolynomial_totalDegree_le 0 _) (choosePoly_natDegree_le a))
      (le_trans (toMvPolynomial_totalDegree_le 1 _) (choosePoly_natDegree_le b))
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  refine le_trans (add_le_add (MvPolynomial.totalDegree_mul _ _) le_rfl) ?_
  rw [MvPolynomial.totalDegree_C]
  have ha' : a < m + 1 := Finset.mem_range.mp ha
  have hb' : b < m + 1 - a := Finset.mem_range.mp hb
  omega

/-- The truncated interpolating polynomial reproduces the value at the origin. -/
theorem newtonPoly2Trunc_eval_zero (F : ℕ × ℕ → ℝ) (m : ℕ) :
    MvPolynomial.eval (fun _ : Fin 2 => (0 : ℝ)) (UCPlanar.Support.newtonPoly2Trunc F m)
      = F (0, 0) := by
  have h0 : Polynomial.eval (0 : ℝ) (UCPlanar.Support.choosePoly 0) = 1 := by
    rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num,
      UCPlanar.Support.choosePoly_eval_nat, Nat.choose_self, Nat.cast_one]
  have hb0 : ∀ b : ℕ, b ≠ 0 → Polynomial.eval (0 : ℝ) (UCPlanar.Support.choosePoly b) = 0 := by
    intro b hb
    rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) by norm_num,
      UCPlanar.Support.choosePoly_eval_nat,
      Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb), Nat.cast_zero]
  rw [UCPlanar.Support.newtonPoly2Trunc, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single 0]
  · rw [MvPolynomial.eval_sum]
    rw [Finset.sum_eq_single 0]
    · simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
      rw [h0]
      simp
    · intro b _ hb
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
      rw [hb0 b hb]
      simp
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  · intro a _ ha
    rw [MvPolynomial.eval_sum]
    apply Finset.sum_eq_zero
    intro b _
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
    rw [hb0 a ha]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h


/-- Iterating the one-dimensional forward difference of the first coordinate
sequence is the two-dimensional forward difference in the first coordinate. -/
theorem fwdDiff_fst_iter (H : ℕ × ℕ → ℝ) (i x₀ y : ℕ) :
    (fwdDiff (1 : ℕ))^[i] (fun x => H (x, y)) x₀ = ((fwdDiff (1, 0))^[i] H) (x₀, y) := by
  induction i generalizing x₀ with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [fwdDiff, Prod.mk_add_mk]
    rw [ih (x₀ + 1), ih x₀]
    rfl

/-- Iterating the one-dimensional forward difference of the second coordinate
sequence is the two-dimensional forward difference in the second coordinate. -/
theorem fwdDiff_snd_iter (H : ℕ × ℕ → ℝ) (j x y₀ : ℕ) :
    (fwdDiff (1 : ℕ))^[j] (fun y => H (x, y)) y₀ = ((fwdDiff (0, 1))^[j] H) (x, y₀) := by
  induction j generalizing y₀ with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [fwdDiff]
    rw [ih (y₀ + 1), ih y₀]
    simp [Prod.mk_add_mk]

/-- Iterating the forward difference over a finite linear combination. -/
theorem fwdDiff_iter_sum (s : Finset ℕ) (c : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (i : ℕ) :
    (fwdDiff (1 : ℕ))^[i] (fun x => ∑ j ∈ s, c j * g j x)
      = fun x => ∑ j ∈ s, c j * ((fwdDiff (1 : ℕ))^[i] (g j)) x := by
  induction i with
  | zero => funext x; simp only [Function.iterate_zero_apply]
  | succ i ih =>
    funext x
    simp only [Function.iterate_succ_apply', fwdDiff]
    simp only [ih]
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The mixed forward difference at the origin is the iterated one-dimensional
difference of the coordinate slices. -/
theorem mixedDiff_origin (F : ℕ × ℕ → ℝ) (i j : ℕ) :
    ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
      = (fwdDiff (1 : ℕ))^[i] (fun x => (fwdDiff (1 : ℕ))^[j] (fun y => F (x, y)) 0) 0 := by
  simp only [UCPlanar.Support.fwdDiff_snd_iter F]
  rw [← UCPlanar.Support.fwdDiff_fst_iter ((fwdDiff (0, 1))^[j] F) i 0 0]

/-- Evaluation of the two-variable Newton polynomial at a lattice point is the
double sum of the mixed differences against the binomial coefficients. -/
theorem newtonPoly2_eval_eq_sum (F : ℕ × ℕ → ℝ) (m a b : ℕ) :
    MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
      (newtonPoly2 F m)
      = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
            * (a.choose i : ℝ) * (b.choose j : ℝ) := by
  rw [newtonPoly2]
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_toMvPolynomial]
  simp [choosePoly_eval_nat]
  try ring

theorem newtonPoly2_eval_eq (F : ℕ × ℕ → ℝ) (m a b : ℕ) (ha : a ≤ m) (hb : b ≤ m) :
    MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
      (UCPlanar.Support.newtonPoly2 F m) = F (a, b) := by
  rw [UCPlanar.Support.newtonPoly2_eval_eq_sum]
  rw [Finset.sum_comm]
  have h_inner : ∀ j, ∑ i ∈ Finset.range (m + 1), ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (a.choose i : ℝ) * (b.choose j : ℝ) = ((fwdDiff (1 : ℕ))^[j] (fun y => F (a, y)) 0) * (b.choose j : ℝ) := by
    intro j
    rw [← Finset.sum_mul]
    congr 1
    have hsum : ∑ i ∈ Finset.range (m + 1), ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (a.choose i : ℝ) = ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) * ((fwdDiff (1 : ℕ))^[i] (fun x => (fwdDiff (1 : ℕ))^[j] (fun y => F (x, y)) 0) 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [UCPlanar.Support.mixedDiff_origin]
      rw [mul_comm]
    rw [hsum]
    exact newtonPoly_eq_of_le (fun x => (fwdDiff (1 : ℕ))^[j] (fun y => F (x, y)) 0) m a ha
  rw [Finset.sum_congr rfl (fun j hj => h_inner j)]
  rw [show (∑ j ∈ Finset.range (m + 1), ((fwdDiff (1 : ℕ))^[j] (fun y => F (a, y)) 0) * (b.choose j : ℝ)) = ∑ j ∈ Finset.range (m + 1), (b.choose j : ℝ) * ((fwdDiff (1 : ℕ))^[j] (fun y => F (a, y)) 0) from by
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]]
  exact newtonPoly_eq_of_le (fun y => F (a, y)) m b hb

/-- Evaluation of the truncated two-variable Newton polynomial at a lattice
point is the truncated double sum of the mixed differences. -/
theorem newtonPoly2Trunc_eval_eq_sum (F : ℕ × ℕ → ℝ) (m a b : ℕ) :
    MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
      (newtonPoly2Trunc F m)
      = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1 - i),
          ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
            * (a.choose i : ℝ) * (b.choose j : ℝ) := by
  rw [newtonPoly2Trunc]
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_toMvPolynomial]
  simp [choosePoly_eval_nat]

/-- The truncated two-variable Newton polynomial reproduces `F` at every lattice
point `(a, b)` with `a + b ≤ m`. -/
theorem newtonPoly2Trunc_eval_eq (F : ℕ × ℕ → ℝ) (m a b : ℕ) (hab : a + b ≤ m) :
    MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
      (UCPlanar.Support.newtonPoly2Trunc F m) = F (a, b) := by
  have hinner : ∀ i : ℕ,
      (∑ j ∈ Finset.range (m + 1 - i),
        ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
          * (a.choose i : ℝ) * (b.choose j : ℝ))
      = ∑ j ∈ Finset.range (m + 1),
        ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
          * (a.choose i : ℝ) * (b.choose j : ℝ) := by
    intro i
    refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.sub_le _ _)) ?_
    intro j hj hjs
    simp only [Finset.mem_range] at hj hjs
    push Not at hjs
    by_cases hia : i ≤ a
    · have hbj : b < j := by omega
      simp [Nat.choose_eq_zero_of_lt hbj]
    · have hai : a < i := by omega
      simp [Nat.choose_eq_zero_of_lt hai]
  rw [UCPlanar.Support.newtonPoly2Trunc_eval_eq_sum,
    Finset.sum_congr rfl (fun i _ => hinner i),
    ← UCPlanar.Support.newtonPoly2_eval_eq_sum,
    UCPlanar.Support.newtonPoly2_eval_eq F m a b (by omega) (by omega)]



theorem fwdDiff_snd_iter_fst (G : ℕ × ℕ → ℝ) (j x y : ℕ) :
    ((fwdDiff (0, 1))^[j] (fwdDiff (1, 0) G)) (x, y)
      = ((fwdDiff (0, 1))^[j] G) (x + 1, y) - ((fwdDiff (0, 1))^[j] G) (x, y) := by
  induction j generalizing x y with
  | zero => simp [fwdDiff]
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [fwdDiff, Prod.mk_add_mk, Nat.add_zero]
    rw [ih x (y + 1), ih x y]
    ring

theorem fwdDiff_comm (F : ℕ × ℕ → ℝ) (i j x y : ℕ) :
    ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (x, y)
      = ((fwdDiff (0, 1))^[j] ((fwdDiff (1, 0))^[i] F)) (x, y) := by
  induction i generalizing x with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [fwdDiff, Prod.mk_add_mk, Nat.add_zero]
    rw [ih (x + 1), ih x, fwdDiff_snd_iter_fst]

end UCPlanar.Support

namespace UCPlanar.Support

/-- The sharp two-variable discrete Taylor remainder, with the bound on the mixed differences
of total order `m+1` required only at the lattice points of the rectangle `[0,a] × [0,b]` that
the `(m+1)`-fold summation visits: the error of the truncated Newton polynomial at `(a,b)` is
at most the binomial coefficient `(a+b).choose (m+1)` times that bound.  The binomial
coefficient is the Vandermonde convolution of the two one-variable remainders. -/
theorem newtonPoly2Trunc_remainder_choose (F : ℕ × ℕ → ℝ) (m a b : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i j : ℕ, i + j = m + 1 → ∀ t y : ℕ, t + i ≤ a → y + j ≤ b →
      |((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (t, y)| ≤ M) :
    |F (a, b) - MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
        (UCPlanar.Support.newtonPoly2Trunc F m)| ≤ (((a + b).choose (m + 1) : ℕ) : ℝ) * M := by
  rw [UCPlanar.Support.newtonPoly2Trunc_eval_eq_sum]
  have h1 : |F (a, b) - newtonPoly (fun x => F (x, b)) m a|
      ≤ (a.choose (m + 1) : ℝ) * M := by
    refine taylor_remainder_bound_choose_local (fun x => F (x, b)) m a M hM0 (fun t ht => ?_)
    have h := hM (m + 1) 0 (by omega) t b ht (by omega)
    rw [Function.iterate_zero_apply] at h
    rw [UCPlanar.Support.fwdDiff_fst_iter F (m + 1) t b]
    exact h
  have h2 : ∀ i : ℕ, i ≤ m → i ≤ a →
      |((fwdDiff (1, 0))^[i] F) (0, b)
        - ∑ j ∈ Finset.range (m + 1 - i),
            ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
              * (b.choose j : ℝ)|
      ≤ (b.choose (m + 1 - i) : ℝ) * M := by
    intro i hi hia
    have h := taylor_remainder_bound_choose_local
      (fun y => ((fwdDiff (1, 0))^[i] F) (0, y)) (m - i) b M hM0 (fun t ht => ?_)
    · rw [newtonPoly] at h
      rw [show m - i + 1 = m + 1 - i by omega] at h
      have hsub : (∑ j ∈ Finset.range (m + 1 - i),
            (b.choose j : ℝ) * (fwdDiff (1 : ℕ))^[j]
              (fun y => ((fwdDiff (1, 0))^[i] F) (0, y)) 0)
          = ∑ j ∈ Finset.range (m + 1 - i),
              ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
                * (b.choose j : ℝ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [UCPlanar.Support.fwdDiff_snd_iter, UCPlanar.Support.fwdDiff_comm]
        ring
      rw [hsub] at h
      exact h
    · rw [show m - i + 1 = m + 1 - i by omega]
      rw [UCPlanar.Support.fwdDiff_snd_iter, ← UCPlanar.Support.fwdDiff_comm]
      refine hM i (m + 1 - i) (by omega) 0 t (by omega) ?_
      omega
  have hsplit : F (a, b) - ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1 - i),
        ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (a.choose i : ℝ) * (b.choose j : ℝ)
      = (F (a, b) - newtonPoly (fun x => F (x, b)) m a)
        + ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
            (((fwdDiff (1, 0))^[i] F) (0, b)
              - ∑ j ∈ Finset.range (m + 1 - i),
                  ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
                    * (b.choose j : ℝ)) := by
    rw [newtonPoly]
    simp only [UCPlanar.Support.fwdDiff_fst_iter]
    have hfac : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1 - i),
          ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (a.choose i : ℝ) * (b.choose j : ℝ))
        = ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
            (∑ j ∈ Finset.range (m + 1 - i),
              ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (b.choose j : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfac]
    have hfac2 : (∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
          (∑ j ∈ Finset.range (m + 1 - i),
            ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (b.choose j : ℝ)))
        = ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
            (((fwdDiff (1, 0))^[i] F) (0, b)
              - (((fwdDiff (1, 0))^[i] F) (0, b)
                - ∑ j ∈ Finset.range (m + 1 - i),
                    ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (b.choose j : ℝ))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfac2]
    have hfac3 : (∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
          (((fwdDiff (1, 0))^[i] F) (0, b)
            - (((fwdDiff (1, 0))^[i] F) (0, b)
              - ∑ j ∈ Finset.range (m + 1 - i),
                  ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (b.choose j : ℝ))))
        = (∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) * ((fwdDiff (1, 0))^[i] F) (0, b))
          - ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
              (((fwdDiff (1, 0))^[i] F) (0, b)
                - ∑ j ∈ Finset.range (m + 1 - i),
                    ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0) * (b.choose j : ℝ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hfac3]
    ring
  rw [hsplit]
  have hvand : (∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) * (b.choose (m + 1 - i) : ℝ))
      + (a.choose (m + 1) : ℝ) = (((a + b).choose (m + 1) : ℕ) : ℝ) := by
    have h := _root_.sum_range_choose_mul_choose a b (m + 1)
    have hcast : ((∑ i ∈ Finset.range (m + 1 + 1), a.choose i * b.choose (m + 1 - i) : ℕ) : ℝ)
        = (((a + b).choose (m + 1) : ℕ) : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    rw [Nat.cast_sum, Finset.sum_range_succ] at hcast
    simpa using hcast
  calc |(F (a, b) - newtonPoly (fun x => F (x, b)) m a)
        + ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
            (((fwdDiff (1, 0))^[i] F) (0, b)
              - ∑ j ∈ Finset.range (m + 1 - i),
                  ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
                    * (b.choose j : ℝ))|
      ≤ |F (a, b) - newtonPoly (fun x => F (x, b)) m a|
        + |∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) *
            (((fwdDiff (1, 0))^[i] F) (0, b)
              - ∑ j ∈ Finset.range (m + 1 - i),
                  ((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j] F)) (0, 0)
                    * (b.choose j : ℝ))| := abs_add_le _ _
    _ ≤ (a.choose (m + 1) : ℝ) * M
        + ∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) * ((b.choose (m + 1 - i) : ℝ) * M) := by
        refine add_le_add h1 ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
        by_cases hia : i ≤ a
        · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          exact mul_le_mul_of_nonneg_left (h2 i hi' hia) (Nat.cast_nonneg _)
        · have hz : a.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [hz]
    _ = (((a + b).choose (m + 1) : ℕ) : ℝ) * M := by
        rw [← hvand]
        rw [show (∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) * ((b.choose (m + 1 - i) : ℝ) * M))
            = (∑ i ∈ Finset.range (m + 1), (a.choose i : ℝ) * (b.choose (m + 1 - i) : ℝ)) * M from by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring]
        ring

end UCPlanar.Support
