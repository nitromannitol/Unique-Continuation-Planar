/-
The bridge from the polynomial approximation lemma to the one-dimensional propagation: the
approximating polynomial, read in the lattice coordinates of an orbit and restricted to one
line of that orbit, is the univariate polynomial the discrete Remez inequality consumes.
-/
import UCPlanar.Support.ThreeLine
import UCPlanar.Support.Poly.LatVar
import UCPlanar.Support.Poly.CaccioppoliLattice

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

open UCPlanar.Support

/-- Fixing the first variable of a bivariate polynomial. -/
noncomputable def lineRestrictSnd (q : MvPolynomial (Fin 2) ℝ) (s : ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval
    (fun i : Fin 2 => if i = 0 then Polynomial.C s else (Polynomial.X : Polynomial ℝ)) q

theorem lineRestrictSnd_eval (q : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    (lineRestrictSnd q s).eval t
      = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else t) q := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp [lineRestrictSnd]
  | add p₁ p₂ h₁ h₂ => simp [lineRestrictSnd, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
  | mul_X p i h =>
      simp only [lineRestrictSnd, map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul,
        MvPolynomial.eval_X] at *
      rw [h]
      fin_cases i <;> simp

/-- The restriction to a vertical line has degree at most the total degree. -/
theorem lineRestrictSnd_natDegree_le (q : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    (lineRestrictSnd q s).natDegree ≤ q.totalDegree := by
  classical
  rw [lineRestrictSnd]
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro d hd
  have hprod : (MvPolynomial.aeval
      (fun i : Fin 2 => if i = 0 then Polynomial.C s else (Polynomial.X : Polynomial ℝ)))
        (MvPolynomial.monomial d (MvPolynomial.coeff d q))
      = Polynomial.C (MvPolynomial.coeff d q)
          * ((Polynomial.C s) ^ d 0 * (Polynomial.X : Polynomial ℝ) ^ d 1) := by
    rw [MvPolynomial.aeval_monomial]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [hprod]
  have h1 : ((Polynomial.C s : Polynomial ℝ) ^ d 0 * (Polynomial.X : Polynomial ℝ) ^ d 1).natDegree
      ≤ d 1 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hx : ((Polynomial.X : Polynomial ℝ) ^ d 1).natDegree = d 1 := by simp
    have hc : ((Polynomial.C s : Polynomial ℝ) ^ d 0).natDegree = 0 := by
      rw [← Polynomial.C_pow]; simp
    omega
  have h2 : (Polynomial.C (MvPolynomial.coeff d q)
      * ((Polynomial.C s : Polynomial ℝ) ^ d 0 * (Polynomial.X : Polynomial ℝ) ^ d 1)).natDegree
      ≤ d 1 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hc : (Polynomial.C (MvPolynomial.coeff d q)).natDegree = 0 := Polynomial.natDegree_C _
    omega
  have h3 : d 1 ≤ q.totalDegree := by
    refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    omega
  omega

/-- The data of a function along the orbit of `v`, in lattice coordinates. -/
noncomputable def orbLine {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V) :
    ℤ → ℤ → ℝ :=
  fun s t => f (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v)

/-- **The bridge, horizontal lines.**  The polynomial approximation of `ucplanar.tex:438-445`
supplies, along every horizontal line of the orbit of `v` that stays inside the square where the
approximation holds, the line data `PolyLine` that the one-dimensional propagation consumes. -/
theorem polyLine_horizontal {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m N : ℕ)
    (v : V) (f : V → ℝ) (α δ : ℝ) (t : ℤ)
    (happ : P.PolynomialApproximation R m v f α δ)
    (hin : ∀ s : ℤ, |s| ≤ 2*(N : ℤ) →
      P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v ∈ P.square (δ * R)) :
    PolyLine N m (fun s => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  obtain ⟨p, hdeg, hbound⟩ := happ
  refine ⟨lineRestrict (latVar P v p) (t : ℝ), ?_, ?_⟩
  · exact le_trans (lineRestrict_natDegree_le _ _)
      (le_trans (latVar_totalDegree_le P v p) hdeg)
  · intro s hs
    have hx := hin s hs
    have hor : P.OnOrbit v
        (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v) := ⟨_, rfl⟩
    have h := hbound _ hx hor
    have heval : (lineRestrict (latVar P v p) (t : ℝ)).eval (s : ℝ)
        = MvPolynomial.eval
            (P.pos (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v)) p := by
      rw [lineRestrict_eval, ← latVar_eval_orbit P v p s t]
    simp only [orbLine]
    rw [heval]
    exact h

/-- **The bridge, vertical lines.**  The same polynomial, restricted to a vertical line of the
orbit. -/
theorem polyLine_vertical {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m N : ℕ)
    (v : V) (f : V → ℝ) (α δ : ℝ) (s : ℤ)
    (happ : P.PolynomialApproximation R m v f α δ)
    (hin : ∀ t : ℤ, |t| ≤ 2*(N : ℤ) →
      P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v ∈ P.square (δ * R)) :
    PolyLine N m (fun t => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  obtain ⟨p, hdeg, hbound⟩ := happ
  refine ⟨lineRestrictSnd (latVar P v p) (s : ℝ), ?_, ?_⟩
  · exact le_trans (lineRestrictSnd_natDegree_le _ _)
      (le_trans (latVar_totalDegree_le P v p) hdeg)
  · intro t ht
    have hx := hin t ht
    have hor : P.OnOrbit v
        (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v) := ⟨_, rfl⟩
    have h := hbound _ hx hor
    have heval : (lineRestrictSnd (latVar P v p) (s : ℝ)).eval (t : ℝ)
        = MvPolynomial.eval
            (P.pos (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v)) p := by
      rw [lineRestrictSnd_eval, ← latVar_eval_orbit P v p s t]
    simp only [orbLine]
    rw [heval]
    exact h


/-- An orbit point whose lattice coordinates are at most `L` in absolute value lies in the
square of radius `ρ + B L`, where `ρ` bounds the drawing of the base vertex and `B` bounds the
operator norm of the period map.  This is what puts a whole lattice line inside the square where
the polynomial approximation holds. -/
theorem shift_mem_square {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (s t : ℤ)
    (ρ B L : ℝ) (hB0 : 0 ≤ B) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖)
    (hv : ‖P.pos v‖ ≤ ρ) (hs : |(s:ℝ)| ≤ L) (ht : |(t:ℝ)| ≤ L) :
    P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v ∈ P.square (ρ + B * L) := by
  have hnn : (0:ℝ) ≤ ρ + B * L := by positivity
  rw [mem_square_iff_norm P hnn, pos_shift_coord P v s t]
  have hcoord : ‖(fun k : Fin 2 => if k = 0 then (s : ℝ) else (t : ℝ))‖ ≤ L := by
    refine (pi_norm_le_iff_of_nonneg hL).mpr ?_
    intro i
    fin_cases i
    · simpa [Real.norm_eq_abs] using hs
    · simpa [Real.norm_eq_abs] using ht
  calc ‖P.pos v + P.period (fun k : Fin 2 => if k = 0 then (s : ℝ) else (t : ℝ))‖
      ≤ ‖P.pos v‖ + ‖P.period (fun k : Fin 2 => if k = 0 then (s : ℝ) else (t : ℝ))‖ :=
        norm_add_le _ _
    _ ≤ ρ + B * L := by
        have h := hB (fun k : Fin 2 => if k = 0 then (s : ℝ) else (t : ℝ))
        have h2 : B * ‖(fun k : Fin 2 => if k = 0 then (s : ℝ) else (t : ℝ))‖ ≤ B * L :=
          mul_le_mul_of_nonneg_left hcoord hB0
        linarith


/-- The line data of a horizontal line, from the polynomial approximation and the geometry: if
the drawing of `v` has norm at most `ρ` and `ρ + 2BN` is within the square where the
approximation holds, every horizontal line of the orbit of `v` over `[-2N, 2N]` carries it. -/
theorem polyLine_horizontal_of_fit {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m N : ℕ)
    (v : V) (f : V → ℝ) (α δ ρ B : ℝ) (hB0 : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖) (hv : ‖P.pos v‖ ≤ ρ)
    (hfit : ρ + B * (2*(N:ℝ)) ≤ δ * R)
    (happ : P.PolynomialApproximation R m v f α δ) (t : ℤ) (ht : |t| ≤ 2*(N:ℤ)) :
    PolyLine N m (fun s => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  refine polyLine_horizontal P R m N v f α δ t happ ?_
  intro s hs
  have h1 : |(s:ℝ)| ≤ 2*(N:ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hs
  have h2 : |(t:ℝ)| ≤ 2*(N:ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast ht
  have hmem := shift_mem_square P v s t ρ B (2*(N:ℝ)) hB0 (by positivity) hρ hB hv h1 h2
  exact UCPlanar.Support.square_mono P hfit hmem

/-- The same for a vertical line. -/
theorem polyLine_vertical_of_fit {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m N : ℕ)
    (v : V) (f : V → ℝ) (α δ ρ B : ℝ) (hB0 : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖) (hv : ‖P.pos v‖ ≤ ρ)
    (hfit : ρ + B * (2*(N:ℝ)) ≤ δ * R)
    (happ : P.PolynomialApproximation R m v f α δ) (s : ℤ) (hs : |s| ≤ 2*(N:ℤ)) :
    PolyLine N m (fun t => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  refine polyLine_vertical P R m N v f α δ s happ ?_
  intro t ht
  have h1 : |(s:ℝ)| ≤ 2*(N:ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hs
  have h2 : |(t:ℝ)| ≤ 2*(N:ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast ht
  have hmem := shift_mem_square P v s t ρ B (2*(N:ℝ)) hB0 (by positivity) hρ hB hv h1 h2
  exact UCPlanar.Support.square_mono P hfit hmem

end UCPlanar.Support.Three
