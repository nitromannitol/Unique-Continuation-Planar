/-
Newton interpolation on a lattice orbit of a periodic graph: the interpolating
polynomial of the mixed-difference data of a harmonic function, and the
remainder estimate along lattice steps.
-/
import UCPlanar.Support.Poly.Interpolation
import UCPlanar.Support.Poly.Caccioppoli
import UCPlanar.Support.Poly.Difference
import UCPlanar.Support.Approximation
import UCPlanar.Support.Poly.Factorial

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- The first lattice generator. -/
noncomputable def e₁ : LatticeProb.Site 2 := Pi.single 0 1

/-- The second lattice generator. -/
noncomputable def e₂ : LatticeProb.Site 2 := Pi.single 1 1

/-- The lattice coordinate of a site. -/
noncomputable def coord (k : LatticeProb.Site 2) : ℕ × ℕ :=
  ((k 0).toNat, (k 1).toNat)

/-- The value of `f` at the lattice point `a e₁ + b e₂` above `v`. -/
noncomputable def orbitCoord {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (v : V) (a b : ℕ) : ℝ :=
  f (P.shift ((a : ℤ) • e₁ + (b : ℤ) • e₂) v)

/-- The Newton interpolating polynomial of the mixed-difference data of `f` at
`v`, of total degree at most `2 * m`. -/
noncomputable def orbitPoly {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (v : V) (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  newtonPoly2Trunc (fun ab : ℕ × ℕ => orbitCoord P f v ab.1 ab.2) m

/-- The interpolating polynomial has total degree at most `m`. -/
theorem orbitPoly_totalDegree_le {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (v : V) (m : ℕ) : (orbitPoly P f v m).totalDegree ≤ m := by
  exact newtonPoly2Trunc_totalDegree_le _ m

/-- The interpolating polynomial reproduces `f` at the base point. -/
theorem orbitPoly_eval_zero {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (v : V) (m : ℕ) :
    MvPolynomial.eval (fun _ : Fin 2 => (0 : ℝ)) (orbitPoly P f v m) = f v := by
  rw [orbitPoly, newtonPoly2Trunc_eval_zero]
  simp [orbitCoord, UCPlanar.PeriodicGraph.shift_zero]

/-- The orbit interpolating polynomial reproduces `f` at every lattice point of
the orbit whose coordinate sum is at most `m`. -/
theorem orbitPoly_eval_eq {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (v : V) (m a b : ℕ) (hab : a + b ≤ m) :
    MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
      (orbitPoly P f v m)
      = f (P.shift ((a : ℤ) • e₁ + (b : ℤ) • e₂) v) := by
  rw [orbitPoly, newtonPoly2Trunc_eval_eq _ m a b hab]; rfl

end UCPlanar.Support

theorem pos_shift_orbit {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (a b : ℕ) :
    P.pos (P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v)
      = P.pos v + (a : ℝ) • P.period (fun i => ((UCPlanar.Support.e₁ : LatticeProb.Site 2) i : ℝ))
        + (b : ℝ) • P.period (fun i => ((UCPlanar.Support.e₂ : LatticeProb.Site 2) i : ℝ)) := by
  rw [UCPlanar.PeriodicGraph.pos_shift]
  have h1 : (fun i : Fin 2 => (((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) i : ℝ))
      = (a : ℝ) • (fun i : Fin 2 => ((UCPlanar.Support.e₁ : LatticeProb.Site 2) i : ℝ))
        + (b : ℝ) • (fun i : Fin 2 => ((UCPlanar.Support.e₂ : LatticeProb.Site 2) i : ℝ)) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h1, map_add, map_smul, map_smul]
  ring

/-- Assembly of the polynomial approximation from the orbit remainder bound. -/
theorem polynomialApproximation_of_remainder {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (R : ℝ) (m : ℕ) (v : V) (f : V → ℝ) (α δ : ℝ)
    (hrem : ∀ x ∈ P.square (δ * R), P.OnOrbit v x →
      |f x - MvPolynomial.eval (P.pos x) (UCPlanar.Support.orbitPoly P f v m)|
        ≤ α ^ m * UCPlanar.supNorm (P.square (3 * R)) f) :
    P.PolynomialApproximation R m v f α δ :=
  ⟨UCPlanar.Support.orbitPoly P f v m, UCPlanar.Support.orbitPoly_totalDegree_le P f v m, hrem⟩

theorem mixedDiff_zero {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (v : V) (f : V → ℝ)
    (a b : ℕ) (hab : a + b = 0)
    (hx : P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v
      ∈ P.square (3 * R)) :
    |UCPlanar.Support.orbitCoord P f v a b| ≤ UCPlanar.supNorm (P.square (3 * R)) f := by
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  subst ha; subst hb
  simp only [Nat.cast_zero, zero_smul, add_zero, UCPlanar.Support.orbitCoord]
  rw [P.shift_zero]
  simp only [Nat.cast_zero, zero_smul, add_zero] at hx
  rw [P.shift_zero] at hx
  have h := Finset.le_sup (s := P.square (3 * R)) (f := fun x => ‖f x‖₊) hx
  rw [UCPlanar.supNorm]
  have h2 : (‖f v‖₊ : ℝ) ≤ ((P.square (3 * R)).sup fun x => ‖f x‖₊ : NNReal) := by exact_mod_cast h
  simpa [Real.norm_eq_abs] using h2


/-- The sharp orbit remainder, with the bound on the mixed differences of total order `m+1`
required only at the orbit points of the rectangle `[0,a] × [0,b]`. -/
theorem UCPlanar.Support.orbitPoly_remainder_choose {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (f : V → ℝ) (v : V) (m a b : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i j : ℕ, i + j = m + 1 → ∀ t y : ℕ, t + i ≤ a → y + j ≤ b →
      |((fwdDiff (1, 0))^[i] ((fwdDiff (0, 1))^[j]
        (fun ab : ℕ × ℕ => UCPlanar.Support.orbitCoord P f v ab.1 ab.2))) (t, y)| ≤ M) :
    |UCPlanar.Support.orbitCoord P f v a b
        - MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ))
            (UCPlanar.Support.orbitPoly P f v m)| ≤ (((a + b).choose (m + 1) : ℕ) : ℝ) * M := by
  rw [UCPlanar.Support.orbitPoly]
  exact UCPlanar.Support.newtonPoly2Trunc_remainder_choose _ m a b M hM0 hM

/-- The sharp remainder beats the derivative bound: the binomial coefficient of the discrete
Taylor remainder at order `m+1` against the derivative bound `(C (m+1) / R) ^ (m+1)` is at most
`α ^ m`, once the lattice displacement `a + b` is at most `α R / (6 C)`. -/
theorem choose_mul_pow_le_of_margin (a b m : ℕ) (α C R : ℝ)
    (hα : 0 < α) (hα2 : α ≤ 2) (hC : 0 < C) (hR : 0 < R)
    (hab : (a : ℝ) + b ≤ (α / (6 * C)) * R) :
    (((a + b).choose (m + 1) : ℕ) : ℝ) * ((C / R) * ((m : ℝ) + 1)) ^ (m + 1) ≤ α ^ m := by
  have hA : 0 ≤ C / R := le_of_lt (div_pos hC hR)
  have step1 : (((a + b).choose (m + 1) : ℕ) : ℝ) * (C / R * ((m : ℝ) + 1)) ^ (m + 1) ≤
      (3 * (C / R) * ((a : ℝ) + b)) ^ (m + 1) := by
    have h := UCPlanar.Support.choose_mul_pow_le (a + b) (m + 1) (C / R) hA
    push_cast at h ⊢
    exact h
  have hstep2 : 3 * (C / R) * ((a : ℝ) + b) ≤ α / 2 := by
    have h3 : 0 ≤ 3 * (C / R) := by positivity
    have h := mul_le_mul_of_nonneg_left hab h3
    have heq : 3 * (C / R) * (α / (6 * C) * R) = α / 2 := by
      field_simp
      ring
    linarith [h, heq]
  have hstep3 : (3 * (C / R) * ((a : ℝ) + b)) ^ (m + 1) ≤ (α / 2) ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hstep2 _
  have hstep4 : (α / 2) ^ (m + 1) ≤ α ^ m := by
    rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ (m + 1)), pow_succ α m]
    have h2 : (2:ℝ) ≤ 2 ^ (m + 1) := by
      calc (2:ℝ) = 2 ^ 1 := by ring
        _ ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 1 m)
    have hαm : 0 < α ^ m := pow_pos hα m
    calc α ^ m * α ≤ α ^ m * 2 := mul_le_mul_of_nonneg_left hα2 (le_of_lt hαm)
      _ ≤ α ^ m * 2 ^ (m + 1) := mul_le_mul_of_nonneg_left h2 (le_of_lt hαm)
  exact le_trans step1 (le_trans hstep3 hstep4)
