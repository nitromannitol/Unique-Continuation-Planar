/-
The one-dimensional propagation of the three-ball proposition.

The paper propagates along a line not a bare function but a function that is uniformly close
to a polynomial of low degree, supplied by the polynomial approximation lemma.  The propagation
is then the discrete Remez inequality with two triangle inequalities around it, and this is the
display at `ucplanar.tex:504-508`.
-/
import UCPlanar.Support.ThreeBall

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

/-- The line data supplied by the polynomial approximation lemma: `g` is within `ε` of a
polynomial of degree at most `m` at every integer point of `[-2N, 2N]`. -/
def PolyLine (N m : ℕ) (g : ℤ → ℝ) (ε : ℝ) : Prop :=
  ∃ q : Polynomial ℝ, q.natDegree ≤ m ∧
    ∀ s : ℤ, |s| ≤ 2 * (N : ℤ) → |g s - q.eval (s : ℝ)| ≤ ε

/-- **The one-dimensional propagation**, `ucplanar.tex:495-508`.  A function within `ε` of a
polynomial of degree `m < N`, bounded by `A` at half of the integer points of `[-N, N]`, is
bounded by `(A + ε)(16N/(N-m))^m + ε` at every integer point of `[-2N, 2N]`. -/
theorem oneDim_from_poly (hremez : RemezInput) (N m : ℕ) (hN : 0 < N) (hm : (m : ℝ) < (N : ℝ))
    (g : ℤ → ℝ) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hline : PolyLine N m g ε)
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ A) :
    ∀ s : ℤ, |s| ≤ 2 * (N : ℤ) →
      |g s| ≤ (A + ε) * (16 * (N : ℝ) / ((N : ℝ) - (m : ℝ))) ^ m + ε := by
  classical
  obtain ⟨q, hdeg, happ⟩ := hline
  obtain ⟨S, hSsub, hScard, hSval⟩ := hS
  have hR : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hceil : ⌈(N:ℝ)⌉₊ = N := by simp
  -- on the dense half of `[-N, N]` the polynomial is bounded by `A + ε`
  have hqS : ∀ s ∈ S, |q.eval (s : ℝ)| ≤ A + ε := by
    intro s hs
    have hsegs : s ∈ seg N := hSsub hs
    have hsN : |s| ≤ (N : ℤ) := by
      rw [seg, Finset.mem_Icc] at hsegs
      rw [abs_le]
      exact ⟨hsegs.1, hsegs.2⟩
    have hs2 : |s| ≤ 2 * (N : ℤ) := by omega
    have h1 := hSval s hs
    have h2 := happ s hs2
    calc |q.eval (s : ℝ)| = |g s - (g s - q.eval (s : ℝ))| := by ring_nf
      _ ≤ |g s| + |g s - q.eval (s : ℝ)| := abs_sub _ _
      _ ≤ A + ε := add_le_add h1 h2
  -- the discrete Remez inequality
  intro s hs
  have hsR : |(s : ℝ)| ≤ 2 * (N : ℝ) := by
    have : |(s : ℤ)| ≤ 2 * (N : ℤ) := hs
    have h := (abs_le.mp this)
    rw [abs_le]
    constructor
    · have := h.1; exact_mod_cast (by exact_mod_cast this : ((-(2 * (N:ℤ)) : ℤ) : ℝ) ≤ (s : ℝ))
    · have := h.2; exact_mod_cast this
  have hq := hremez (N:ℝ) m (A + ε) q (by linarith) hR hm hdeg
    ⟨S, by rwa [hceil], by rwa [hceil], hqS⟩ s hsR
  have happs := happ s hs
  calc |g s| = |q.eval (s : ℝ) + (g s - q.eval (s : ℝ))| := by ring_nf
    _ ≤ |q.eval (s : ℝ)| + |g s - q.eval (s : ℝ)| := abs_add_le _ _
    _ ≤ (A + ε) * (16 * (N : ℝ) / ((N : ℝ) - (m : ℝ))) ^ m + ε := add_le_add hq happs

/-- Fixing the second variable of a bivariate polynomial.  Restricting the approximating
polynomial of the polynomial approximation lemma to one horizontal line of the orbit is what
feeds the discrete Remez inequality, which is univariate. -/
noncomputable def lineRestrict (q : MvPolynomial (Fin 2) ℝ) (t : ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval
    (fun i : Fin 2 => if i = 0 then (Polynomial.X : Polynomial ℝ) else Polynomial.C t) q

theorem lineRestrict_eval (q : MvPolynomial (Fin 2) ℝ) (t s : ℝ) :
    (lineRestrict q t).eval s
      = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then s else t) q := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp [lineRestrict]
  | add p₁ p₂ h₁ h₂ => simp [lineRestrict, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
  | mul_X p i h =>
      simp only [lineRestrict, map_mul, MvPolynomial.aeval_X, Polynomial.eval_mul,
        MvPolynomial.eval_X] at *
      rw [h]
      fin_cases i <;> simp

/-- The restriction to a line has degree at most the total degree. -/
theorem lineRestrict_natDegree_le (q : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    (lineRestrict q t).natDegree ≤ q.totalDegree := by
  classical
  rw [lineRestrict]
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro d hd
  have hprod : (MvPolynomial.aeval
      (fun i : Fin 2 => if i = 0 then (Polynomial.X : Polynomial ℝ) else Polynomial.C t))
        (MvPolynomial.monomial d (MvPolynomial.coeff d q))
      = Polynomial.C (MvPolynomial.coeff d q)
          * ((Polynomial.X : Polynomial ℝ) ^ d 0 * (Polynomial.C t) ^ d 1) := by
    rw [MvPolynomial.aeval_monomial]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [hprod]
  have h1 : ((Polynomial.X : Polynomial ℝ) ^ d 0 * (Polynomial.C t) ^ d 1).natDegree ≤ d 0 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hx : ((Polynomial.X : Polynomial ℝ) ^ d 0).natDegree = d 0 := by
      simp
    have hc : ((Polynomial.C t : Polynomial ℝ) ^ d 1).natDegree = 0 := by
      rw [← Polynomial.C_pow]; simp
    omega
  have h2 : (Polynomial.C (MvPolynomial.coeff d q)
      * ((Polynomial.X : Polynomial ℝ) ^ d 0 * (Polynomial.C t) ^ d 1)).natDegree ≤ d 0 := by
    refine le_trans (Polynomial.natDegree_mul_le) ?_
    have hc : (Polynomial.C (MvPolynomial.coeff d q)).natDegree = 0 := Polynomial.natDegree_C _
    omega
  have h3 : d 0 ≤ q.totalDegree := by
    refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    omega
  omega

end UCPlanar.Support.Three
