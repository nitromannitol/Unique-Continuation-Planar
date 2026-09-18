/-
The change of variables in the other direction: a polynomial of the plane coordinates is read
as a polynomial of the lattice coordinates along an orbit.  This is what turns the approximating
polynomial of the polynomial approximation lemma, which is evaluated at the drawing of a vertex,
into a polynomial of the two integer coordinates of that vertex in its orbit.
-/
import UCPlanar.Support.Poly.Change

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- The affine form giving the `i`-th plane coordinate of the orbit point of `v` whose lattice
coordinates are the two variables. -/
noncomputable def posForm {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (i : Fin 2) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (P.pos v i)
    + ∑ j : Fin 2, MvPolynomial.C (P.period (Pi.single j (1:ℝ)) i) * MvPolynomial.X j

theorem posForm_totalDegree_le {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (i : Fin 2) :
    (posForm P v i).totalDegree ≤ 1 := by
  rw [posForm]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    omega
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le ?_)
    intro j _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X]

theorem posForm_eval {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (i : Fin 2)
    (u : UCPlanar.Plane) :
    MvPolynomial.eval u (posForm P v i) = (P.pos v + P.period u) i := by
  rw [posForm]
  simp only [map_add, MvPolynomial.eval_C, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    Pi.add_apply]
  have hu := linear_coord P.period u i
  rw [hu]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- The change of variables: substituting the affine plane-coordinate forms into a polynomial
of the plane coordinates gives a polynomial of the lattice coordinates. -/
noncomputable def latVar {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V)
    (p : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.bind₁ (posForm P v) p

theorem latVar_totalDegree_le {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V)
    (p : MvPolynomial (Fin 2) ℝ) : (latVar P v p).totalDegree ≤ p.totalDegree :=
  totalDegree_bind₁_le p (posForm P v) (posForm_totalDegree_le P v)

theorem latVar_eval {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V)
    (p : MvPolynomial (Fin 2) ℝ) (u : UCPlanar.Plane) :
    MvPolynomial.eval u (latVar P v p) = MvPolynomial.eval (P.pos v + P.period u) p := by
  rw [latVar]
  have h := MvPolynomial.aeval_bind₁ u (posForm P v) p
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  have hfun : (fun i => MvPolynomial.eval u (posForm P v i)) = (P.pos v + P.period u) := by
    funext i
    exact posForm_eval P v i u
  rw [hfun]

/-- The lattice coordinates of the orbit point `shift (a e₁ + b e₂) v`. -/
theorem pos_shift_coord {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (a b : ℤ) :
    P.pos (P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v)
      = P.pos v + P.period (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ)) := by
  have hfun : (fun j : Fin 2 =>
      ((((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ))
      = (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ)) := by
    funext j
    fin_cases j <;> simp [UCPlanar.Support.e₁, UCPlanar.Support.e₂]
  rw [P.pos_shift, hfun]

/-- At an orbit point the change of variables evaluates the polynomial of the plane coordinates
at the drawing of that point. -/
theorem latVar_eval_orbit {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V)
    (p : MvPolynomial (Fin 2) ℝ) (a b : ℤ) :
    MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ)) (latVar P v p)
      = MvPolynomial.eval
          (P.pos (P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v)) p := by
  rw [latVar_eval, pos_shift_coord]

end UCPlanar.Support
