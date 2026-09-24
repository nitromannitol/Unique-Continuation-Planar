/-
The change of variables from lattice coordinates to positions in the plane: an invertible affine
substitution, which does not raise the total degree, carries the Newton interpolating polynomial
of the orbit data to a polynomial evaluated at the drawing of the vertex.
-/
import UCPlanar.Support.Poly.Rebase

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- Substituting polynomials of total degree at most one does not raise the total degree. -/
theorem totalDegree_bind₁_le {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (g : σ → MvPolynomial σ ℝ) (hg : ∀ i, (g i).totalDegree ≤ 1) :
    (MvPolynomial.bind₁ g p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le ?_
  intro d hd
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  have hterm : ∀ i ∈ d.support, (g i ^ d i).totalDegree ≤ d i := by
    intro i _
    refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
    calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
      _ = d i := Nat.mul_one _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsum : ∑ i ∈ d.support, d i = d.sum fun _ e => e := rfl
  rw [hsum]
  exact MvPolynomial.le_totalDegree hd

/-- A linear map of the plane is read off its values on the two coordinate vectors. -/
theorem linear_coord (T : UCPlanar.Plane ≃ₗ[ℝ] UCPlanar.Plane) (u : UCPlanar.Plane) (i : Fin 2) :
    T u i = ∑ j : Fin 2, u j * T (Pi.single j (1:ℝ)) i := by
  have hu : u = ∑ j : Fin 2, u j • (Pi.single j (1:ℝ) : Fin 2 → ℝ) := by
    funext k
    simp [Pi.single_apply]
  rw [hu, map_sum]
  simp [Finset.sum_apply, mul_comm]

/-- The affine form that reads the `i`-th lattice coordinate of a position relative to `v'`. -/
noncomputable def coordForm {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V) (i : Fin 2) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (- (P.period.symm (P.pos v') i))
    + ∑ j : Fin 2, MvPolynomial.C (P.period.symm (Pi.single j (1:ℝ)) i) * MvPolynomial.X j

theorem coordForm_totalDegree_le {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V) (i : Fin 2) :
    (coordForm P v' i).totalDegree ≤ 1 := by
  rw [coordForm]
  refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]
    omega
  · refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le ?_)
    intro j _
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X]

theorem coordForm_eval {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V) (i : Fin 2)
    (u : UCPlanar.Plane) :
    MvPolynomial.eval u (coordForm P v' i) = P.period.symm (u - P.pos v') i := by
  rw [coordForm]
  simp only [map_add, MvPolynomial.eval_C, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  have hlin : P.period.symm (u - P.pos v') = P.period.symm u - P.period.symm (P.pos v') :=
    map_sub _ _ _
  rw [hlin]
  have hu := linear_coord P.period.symm u i
  simp only [Pi.sub_apply]
  rw [hu]
  have hs : (∑ j : Fin 2, P.period.symm (Pi.single j (1:ℝ)) i * u j)
      = ∑ j : Fin 2, u j * P.period.symm (Pi.single j (1:ℝ)) i :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring

/-- The change of variables: substituting the affine coordinate forms into a polynomial of the
lattice coordinates. -/
noncomputable def changeVar {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V)
    (q : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.bind₁ (coordForm P v') q

theorem changeVar_totalDegree_le {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V)
    (q : MvPolynomial (Fin 2) ℝ) : (changeVar P v' q).totalDegree ≤ q.totalDegree :=
  totalDegree_bind₁_le q (coordForm P v') (coordForm_totalDegree_le P v')

theorem changeVar_eval {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V)
    (q : MvPolynomial (Fin 2) ℝ) (u : UCPlanar.Plane) :
    MvPolynomial.eval u (changeVar P v' q)
      = MvPolynomial.eval (fun i => P.period.symm (u - P.pos v') i) q := by
  rw [changeVar]
  have h := MvPolynomial.aeval_bind₁ u (coordForm P v') q
  simp only [MvPolynomial.aeval_eq_eval] at h
  rw [h]
  have hfun : (fun i => MvPolynomial.eval u (coordForm P v' i))
      = (fun i => P.period.symm (u - P.pos v') i) := by
    funext i
    exact coordForm_eval P v' i u
  rw [hfun]

/-- At an orbit point the change of variables evaluates the polynomial at the lattice
coordinates of that point. -/
theorem changeVar_eval_orbit {V : Type*} (P : UCPlanar.PeriodicGraph V) (v' : V)
    (q : MvPolynomial (Fin 2) ℝ) (a b : ℕ) :
    MvPolynomial.eval
        (P.pos (P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v'))
        (changeVar P v' q)
      = MvPolynomial.eval (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ)) q := by
  rw [changeVar_eval]
  have hfun : (fun i => P.period.symm
      (P.pos (P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v')
        - P.pos v') i)
      = (fun k : Fin 2 => if k = 0 then (a : ℝ) else (b : ℝ)) := by
   funext i
   have hpos := P.pos_shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v'
   rw [hpos]
   have hsub : P.pos v'
      + P.period (fun j => ((((a : ℤ) • UCPlanar.Support.e₁
          + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)) - P.pos v'
      = P.period (fun j => ((((a : ℤ) • UCPlanar.Support.e₁
          + (b : ℤ) • UCPlanar.Support.e₂) j : ℤ) : ℝ)) := by
     abel
   rw [hsub, LinearEquiv.symm_apply_apply]
   fin_cases i <;>
     simp [UCPlanar.Support.e₁, UCPlanar.Support.e₂]
  rw [hfun]

end UCPlanar.Support
