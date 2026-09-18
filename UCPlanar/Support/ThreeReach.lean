/-
The reach of the one-dimensional propagation.

The propagation of ThreeProp.lean doubles the interval, because the cited discrete Remez
inequality passes from `[-R, R]` to `[-2R, 2R]`.  The lattice box inscribed in a geometric
square and the lattice box circumscribing the doubled square differ by the distortion of the
period map, so the propagation has to reach `2^J` times the density interval, for a `J` fixed by
the graph.  Iterating the Remez inequality on the approximating polynomial does this: each
doubling costs a factor `32^m`, and an approximation quality `α = 2^{-24J}` still beats the
accumulated factor at the fourth root, which is what the exponent `1/4` of the propagation asks.
-/
import UCPlanar.Support.ThreeProp

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

/-- The approximation quality of the polynomial approximation at reach `2^J`. -/
noncomputable def alphaJ (J : ℕ) : ℝ := ((2:ℝ) ^ (24*J))⁻¹

theorem alphaJ_pos (J : ℕ) : 0 < alphaJ J := by
  rw [alphaJ]; positivity

theorem alphaJ_pow (J i : ℕ) : alphaJ J ^ i = ((2:ℝ) ^ (24*J*i))⁻¹ := by
  rw [alphaJ, inv_pow, ← pow_mul]

/-- **One doubling of the Remez inequality.**  A polynomial of degree at most `m ≤ N/2` bounded
by `A` at half of the integer points of `[-N, N]` is bounded by `A·32^m` on `[-2N, 2N]`. -/
theorem remez_dense (hremez : RemezInput) (N m : ℕ) (hN : 0 < N) (h2m : 2*m ≤ N)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ m) (A : ℝ) (hA : 0 ≤ A)
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
      ∀ s ∈ S, |p.eval (s:ℝ)| ≤ A) :
    ∀ s : ℤ, |s| ≤ 2*(N:ℤ) → |p.eval (s:ℝ)| ≤ A * (32:ℝ)^m := by
  have hR' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hm : (m:ℝ) < (N:ℝ) := by
    have : m < N := by omega
    exact_mod_cast this
  have hceil : ⌈(N:ℝ)⌉₊ = N := by simp
  have hS' : ∃ S : Finset ℤ, S ⊆ seg ⌈(N:ℝ)⌉₊ ∧ 2 * S.card ≥ (seg ⌈(N:ℝ)⌉₊).card ∧
      ∀ s ∈ S, |p.eval (s:ℝ)| ≤ A := by rw [hceil]; exact hS
  intro s hs
  have hsR : |(s:ℝ)| ≤ 2 * (N:ℝ) := by
    rw [← Int.cast_abs]; exact_mod_cast hs
  refine le_trans (hremez (N:ℝ) m A p hA hR' hm hdeg hS' s hsR) ?_
  have hpos : (0:ℝ) < (N:ℝ) - (m:ℝ) := by linarith
  have hratio : (16*(N:ℝ)/((N:ℝ)-(m:ℝ)))^m ≤ (32:ℝ)^m := by
    refine pow_le_pow_left₀ ?_ (ratio_le_32 N m hN h2m) m
    positivity
  exact mul_le_mul_of_nonneg_left hratio hA

/-- The same doubling from a bound at every integer point of `[-R, R]`. -/
theorem remez_full (hremez : RemezInput) (R m : ℕ) (hR : 0 < R) (h2m : 2*m ≤ R)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ m) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ s : ℤ, |s| ≤ (R:ℤ) → |p.eval (s:ℝ)| ≤ A) :
    ∀ s : ℤ, |s| ≤ 2*(R:ℤ) → |p.eval (s:ℝ)| ≤ A * (32:ℝ)^m := by
  refine remez_dense hremez R m hR h2m p hdeg A hA ⟨seg R, le_refl _, by omega, ?_⟩
  intro s hs
  rw [seg, Finset.mem_Icc] at hs
  exact h s (by rw [abs_le]; omega)

/-- **The reach of the Remez inequality.**  Iterating the doubling `J` times carries the bound
from the dense half of `[-N, N]` to every integer point of `[-2^J N, 2^J N]`, at the cost of
`32^m` per doubling. -/
theorem remez_reach (hremez : RemezInput) (N m : ℕ) (hN : 0 < N) (h2m : 2*m ≤ N)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ m) (A : ℝ) (hA : 0 ≤ A)
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
      ∀ s ∈ S, |p.eval (s:ℝ)| ≤ A) :
    ∀ J : ℕ, 1 ≤ J → ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) → |p.eval (s:ℝ)| ≤ A * ((32:ℝ)^m)^J := by
  intro J
  induction J with
  | zero => intro h; omega
  | succ i ih =>
    intro _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · intro s hs
      have h := remez_dense hremez N m hN h2m p hdeg A hA hS s (by simpa using hs)
      simpa using h
    · have hprev := ih hi
      have hRpos : 0 < 2^i*N := by positivity
      have h2mR : 2*m ≤ 2^i*N := by
        have : N ≤ 2^i*N := Nat.le_mul_of_pos_left N (by positivity)
        omega
      have hAA : (0:ℝ) ≤ A * ((32:ℝ)^m)^i := by positivity
      have hbase : ∀ s : ℤ, |s| ≤ ((2^i*N : ℕ):ℤ) → |p.eval (s:ℝ)| ≤ A * ((32:ℝ)^m)^i := by
        intro s hs
        refine hprev s ?_
        push_cast at hs ⊢
        exact hs
      have hstep := remez_full hremez (2^i*N) m hRpos h2mR p hdeg _ hAA hbase
      intro s hs
      have hs' : |s| ≤ 2*((2^i*N : ℕ):ℤ) := by
        push_cast
        calc |s| ≤ 2^(i+1)*(N:ℤ) := hs
          _ = 2*(2^i*(N:ℤ)) := by ring
      have := hstep s hs'
      calc |p.eval (s:ℝ)| ≤ A * ((32:ℝ)^m)^i * (32:ℝ)^m := this
        _ = A * ((32:ℝ)^m)^(i+1) := by ring

/-- The line data at reach `2^J`: `g` is within `ε` of a polynomial of degree at most `m` at
every integer point of `[-2^J N, 2^J N]`. -/
def PolyReach (J N m : ℕ) (g : ℤ → ℝ) (ε : ℝ) : Prop :=
  ∃ q : Polynomial ℝ, q.natDegree ≤ m ∧
    ∀ s : ℤ, |s| ≤ 2^J * (N : ℤ) → |g s - q.eval (s : ℝ)| ≤ ε

/-- **The one-dimensional propagation at reach `2^J`**, the generalization of
`oneDim_from_poly`: a function within `ε` of a polynomial of degree `m ≤ N/2`, bounded by `A`
at half of the integer points of `[-N, N]`, is bounded by `(A + ε)(32^m)^J + ε` on
`[-2^J N, 2^J N]`. -/
theorem oneDim_reach (hremez : RemezInput) (J N m : ℕ) (hN : 0 < N) (h2m : 2*m ≤ N)
    (hJ : 1 ≤ J) (g : ℤ → ℝ) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hline : PolyReach J N m g ε)
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ A) :
    ∀ s : ℤ, |s| ≤ 2^J * (N:ℤ) → |g s| ≤ (A + ε) * ((32:ℝ)^m)^J + ε := by
  classical
  obtain ⟨q, hdeg, happ⟩ := hline
  obtain ⟨S, hSsub, hScard, hSval⟩ := hS
  have hone : (1:ℤ) ≤ 2^J := one_le_pow₀ (by norm_num)
  have hqS : ∀ s ∈ S, |q.eval (s:ℝ)| ≤ A + ε := by
    intro s hs
    have hsegs : s ∈ seg N := hSsub hs
    have hsN : |s| ≤ (N:ℤ) := by
      rw [seg, Finset.mem_Icc] at hsegs
      rw [abs_le]; exact ⟨hsegs.1, hsegs.2⟩
    have hs2 : |s| ≤ 2^J * (N:ℤ) := by nlinarith [Int.natCast_nonneg N, abs_nonneg s]
    calc |q.eval (s:ℝ)| = |g s - (g s - q.eval (s:ℝ))| := by ring_nf
      _ ≤ |g s| + |g s - q.eval (s:ℝ)| := abs_sub _ _
      _ ≤ A + ε := add_le_add (hSval s hs) (happ s hs2)
  have hbd := remez_reach hremez N m hN h2m q hdeg (A + ε) (by linarith) ⟨S, hSsub, hScard, hqS⟩
    J hJ
  intro s hs
  calc |g s| = |q.eval (s:ℝ) + (g s - q.eval (s:ℝ))| := by ring_nf
    _ ≤ |q.eval (s:ℝ)| + |g s - q.eval (s:ℝ)| := abs_add_le _ _
    _ ≤ (A + ε) * ((32:ℝ)^m)^J + ε := add_le_add (hbd s hs) (happ s hs)

/-- The Remez factor accumulated over `J` doublings, in base two. -/
theorem pow32_pow (m J : ℕ) : ((32:ℝ)^m)^J = (2:ℝ)^(5*J*m) := by
  rw [show (32:ℝ) = 2^(5:ℕ) by norm_num, ← pow_mul, ← pow_mul]
  congr 1
  ring

/-- The fourth root of a power of two. -/
theorem rpow_two_pow_J (k : ℕ) : ((2:ℝ) ^ (24*k)) ^ (1/4:ℝ) = (2:ℝ) ^ (6*k) := by
  rw [← Real.rpow_natCast (2:ℝ) (24*k), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ((24*k : ℕ):ℝ) * (1/4:ℝ) = ((6*k : ℕ):ℝ) by push_cast; ring]
  rw [Real.rpow_natCast]

/-- **The minimal-degree arithmetic at reach `2^J`.**  If the degree `i+1` is minimal with
`alphaJ J ^ (i+1) * M ≤ 1`, so that `alphaJ J ^ i * M > 1`, then the Remez factor accumulated
over the `J` doublings is at most `2^{6J} M^{1/4}`. -/
theorem pow32_le_of_min_J (J i : ℕ) (M : ℝ) (h : 1 < alphaJ J ^ i * M) :
    ((32:ℝ)^(i+1))^J ≤ (2:ℝ)^(6*J) * M ^ (1/4:ℝ) := by
  have h2 : (0:ℝ) < (2:ℝ) ^ (24*(J*i)) := by positivity
  have hMgt : ((2:ℝ) ^ (24*(J*i))) < M := by
    rw [alphaJ_pow] at h
    rw [show 24*J*i = 24*(J*i) by ring] at h
    rw [inv_mul_eq_div, lt_div_iff₀ h2] at h
    linarith
  have hroot : (2:ℝ) ^ (6*(J*i)) ≤ M ^ (1/4:ℝ) := by
    rw [← rpow_two_pow_J (J*i)]
    exact Real.rpow_le_rpow (le_of_lt h2) (le_of_lt hMgt) (by norm_num)
  have hbase : ((32:ℝ)^(i+1))^J = (2:ℝ)^(5*J*(i+1)) := pow32_pow (i+1) J
  have hstep : (2:ℝ)^(5*J*(i+1)) ≤ (2:ℝ)^(6*J) * (2:ℝ)^(6*(J*i)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by ring_nf; omega)
  have hpos : (0:ℝ) < (2:ℝ)^(6*J) := by positivity
  calc ((32:ℝ)^(i+1))^J = (2:ℝ)^(5*J*(i+1)) := hbase
    _ ≤ (2:ℝ)^(6*J) * (2:ℝ)^(6*(J*i)) := hstep
    _ ≤ (2:ℝ)^(6*J) * M ^ (1/4:ℝ) := mul_le_mul_of_nonneg_left hroot hpos.le

/-- The constant of the one-dimensional propagation at reach `2^J`.  At `J = 1` it is the
`192` of `ThreeProp.lean`. -/
noncomputable def CJ (J : ℕ) : ℝ := 3 * (2:ℝ)^(6*J)

theorem CJ_ge_three (J : ℕ) : 3 ≤ CJ J := by
  rw [CJ]
  have : (1:ℝ) ≤ (2:ℝ)^(6*J) := one_le_pow₀ (by norm_num)
  linarith

theorem CJ_pos (J : ℕ) : 0 < CJ J := lt_of_lt_of_le (by norm_num) (CJ_ge_three J)

/-- The minimal degree at which the approximation error drops below one, at reach `2^J`. -/
theorem exists_minimal_degree_J (J N : ℕ) (M : ℝ) (_hN : 2 ≤ N)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (hM : M ≤ (2:ℝ)^((3*J+2)*N)) :
    ∃ j : ℕ, 2*j ≤ N ∧ alphaJ J ^ j * M ≤ 1 ∧
      ∀ i : ℕ, i + 1 = j → 1 < alphaJ J ^ i * M := by
  classical
  have hhalf : alphaJ J ^ (N/2) * M ≤ 1 := by
    have hpos : (0:ℝ) < (2:ℝ) ^ (24*J*(N/2)) := by positivity
    rw [alphaJ_pow, inv_mul_eq_div, div_le_one hpos]
    exact le_trans hM (pow_le_pow_right₀ (by norm_num) (by omega))
  have hex : ∃ j : ℕ, alphaJ J ^ j * M ≤ 1 := ⟨N/2, hhalf⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · have hle := Nat.find_min' hex hhalf
    omega
  · intro i hi
    exact not_le.mp (Nat.find_min hex (by omega))

/-- **Case 1 of the one-dimensional propagation at reach `2^J`.** -/
theorem oneDim_case_small_J (hremez : RemezInput) (J N : ℕ) (hN : 6 ≤ N) (hJ : 1 ≤ J)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (g : ℤ → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hcase : M ≤ (2:ℝ)^((3*J+2)*N))
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyReach J N m g (alphaJ J ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ 1) :
    ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) → |g s| ≤ CJ J * M ^ (1/4:ℝ) := by
  have hNpos : 0 < N := by omega
  obtain ⟨j, h2j, hj, hmin⟩ := exists_minimal_degree_J J N M (by omega) hH1 hcase
  have hε0 : 0 ≤ alphaJ J ^ j * M := by
    have := alphaJ_pos J
    positivity
  have hbd := oneDim_reach hremez J N j hNpos h2j hJ g 1 (alphaJ J ^ j * M)
      (by norm_num) hε0 (hline j h2j) hS
  intro s hs
  have h1 := hbd s hs
  have hfac : (1:ℝ) ≤ ((32:ℝ)^j)^J := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have h2 : (1 + alphaJ J ^ j * M) * ((32:ℝ)^j)^J + alphaJ J ^ j * M ≤ 3 * ((32:ℝ)^j)^J := by
    nlinarith [hj, hε0, hfac]
  have h3 : (3:ℝ) * ((32:ℝ)^j)^J ≤ CJ J * M ^ (1/4:ℝ) := by
    have hMroot : (1:ℝ) ≤ M ^ (1/4:ℝ) := Real.one_le_rpow hM (by norm_num)
    have hpow : (1:ℝ) ≤ (2:ℝ)^(6*J) := one_le_pow₀ (by norm_num)
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero, one_pow, CJ]
      nlinarith
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have := pow32_le_of_min_J J i M (hmin i rfl)
      rw [CJ]
      nlinarith
  linarith [h1, h2, h3]

/-- **Case 2 of the one-dimensional propagation at reach `2^J`.** -/
theorem oneDim_case_large_J (hremez : RemezInput) (J N : ℕ) (hN : 6 ≤ N) (hJ : 1 ≤ J)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (hH2 : 5*J*(N/2) + 2*N ≤ (3*J+2)*N)
    (g : ℤ → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hcase : (2:ℝ)^((3*J+2)*N) < M)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyReach J N m g (alphaJ J ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ 1) :
    ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) → |g s| ≤ 3 * M / 2 ^ (2*N) := by
  have hNpos : 0 < N := by omega
  set h := N/2 with hh
  have h2h : 2*h ≤ N := by omega
  have hH3 : 5*J*h + 2*N ≤ 24*J*h := le_trans hH2 hH1
  have hH4 : 2*N ≤ 24*J*h := le_trans (Nat.le_add_left _ _) hH3
  have hε0 : 0 ≤ alphaJ J ^ h * M := by
    have := alphaJ_pos J
    positivity
  have hbd := oneDim_reach hremez J N h hNpos h2h hJ g 1 (alphaJ J ^ h * M)
      (by norm_num) hε0 (hline h h2h) hS
  intro s hs
  have h1 := hbd s hs
  have hεeq : alphaJ J ^ h * M = M / 2 ^ (24*J*h) := by
    rw [alphaJ_pow]
    field_simp
  have hfaceq : ((32:ℝ)^h)^J = (2:ℝ)^(5*J*h) := pow32_pow h J
  have e1 : (2:ℝ)^(5*J*h) * 2 ^ (2*N) ≤ M := by
    rw [← pow_add]
    exact le_trans (pow_le_pow_right₀ (by norm_num) hH2) (le_of_lt hcase)
  have e2 : (M / 2 ^ (24*J*h)) * ((2:ℝ)^(5*J*h) * 2 ^ (2*N)) ≤ M := by
    rw [← pow_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hpow : (2:ℝ) ^ (5*J*h + 2*N) ≤ (2:ℝ) ^ (24*J*h) :=
      pow_le_pow_right₀ (by norm_num) hH3
    nlinarith [hpow, hM]
  have e3 : (M / 2 ^ (24*J*h)) * 2 ^ (2*N) ≤ M := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hpow : (2:ℝ) ^ (2*N) ≤ (2:ℝ) ^ (24*J*h) :=
      pow_le_pow_right₀ (by norm_num) hH4
    nlinarith [hpow, hM]
  have hε0' : 0 ≤ M / 2 ^ (24*J*h) := by positivity
  have hpowpos : (0:ℝ) < 2 ^ (2*N) := by positivity
  have key : (1 + M / 2 ^ (24*J*h)) * (2:ℝ)^(5*J*h) + M / 2 ^ (24*J*h)
      ≤ 3 * M / 2 ^ (2*N) := by
    rw [le_div_iff₀ hpowpos]
    calc ((1 + M / 2 ^ (24*J*h)) * (2:ℝ)^(5*J*h) + M / 2 ^ (24*J*h)) * 2 ^ (2*N)
        = (2:ℝ)^(5*J*h) * 2 ^ (2*N) + (M / 2 ^ (24*J*h)) * ((2:ℝ)^(5*J*h) * 2 ^ (2*N))
            + (M / 2 ^ (24*J*h)) * 2 ^ (2*N) := by ring
      _ ≤ M + M + M := by linarith [e1, e2, e3]
      _ = 3 * M := by ring
  rw [hεeq, hfaceq] at h1
  linarith [h1, key]

/-- **The one-dimensional propagation at reach `2^J`**, the two cases together. -/
theorem oneDim_propagation_J (hremez : RemezInput) (J N : ℕ) (hN : 6 ≤ N) (hJ : 1 ≤ J)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (hH2 : 5*J*(N/2) + 2*N ≤ (3*J+2)*N)
    (g : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyReach J N m g (alphaJ J ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ 1) :
    ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) → |g s| ≤ CJ J * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N) := by
  intro s hs
  rcases le_or_gt M ((2:ℝ)^((3*J+2)*N)) with hc | hc
  · have h := oneDim_case_small_J hremez J N hN hJ hH1 g M hM hc hline hS s hs
    have hnn : (0:ℝ) ≤ 3 * M / 2 ^ (2*N) := by positivity
    linarith
  · have h := oneDim_case_large_J hremez J N hN hJ hH1 hH2 g M hM hc hline hS s hs
    have hnn : (0:ℝ) ≤ CJ J * M ^ (1/4:ℝ) := by
      have := CJ_pos J
      positivity
    linarith

/-- Dividing the line data by a positive constant. -/
theorem polyReach_div (J N m : ℕ) (g : ℤ → ℝ) (ε A : ℝ) (hA : 0 < A) (h : PolyReach J N m g ε) :
    PolyReach J N m (fun s => g s / A) (ε / A) := by
  obtain ⟨q, hdeg, hq⟩ := h
  refine ⟨Polynomial.C A⁻¹ * q, ?_, ?_⟩
  · exact le_trans (Polynomial.natDegree_mul_le) (by simpa using hdeg)
  · intro s hs
    have h1 := hq s hs
    have : (Polynomial.C A⁻¹ * q).eval (s:ℝ) = q.eval (s:ℝ) / A := by
      simp [Polynomial.eval_mul, div_eq_inv_mul]
    rw [this, div_sub_div_same, abs_div, abs_of_pos hA]
    gcongr

/-- The one-dimensional propagation at reach `2^J` from a general bound `A ≥ 1` on the dense
half, by scaling. -/
theorem oneDim_scaled_J (hremez : RemezInput) (J N : ℕ) (hN : 6 ≤ N) (hJ : 1 ≤ J)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (hH2 : 5*J*(N/2) + 2*N ≤ (3*J+2)*N)
    (g : ℤ → ℝ) (A M : ℝ) (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hgM : ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) → |g s| ≤ M)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyReach J N m g (alphaJ J ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ A) :
    ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) →
      |g s| ≤ CJ J * A ^ (3/4:ℝ) * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N) := by
  intro s hs
  have hA0 : (0:ℝ) < A := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  have hC := CJ_ge_three J
  have hdecay : (0:ℝ) ≤ 3 * M / 2 ^ (2*N) := by positivity
  have hApow : A ^ (3/4:ℝ) * A ^ (1/4:ℝ) = A := by
    rw [← Real.rpow_add hA0]; norm_num
  rcases le_or_gt M A with hMA | hMA
  · have h1 := hgM s hs
    have h2 : M ^ (3/4:ℝ) ≤ A ^ (3/4:ℝ) := Real.rpow_le_rpow hM0.le hMA (by norm_num)
    have h3 : M ^ (3/4:ℝ) * M ^ (1/4:ℝ) = M := by
      rw [← Real.rpow_add hM0]; norm_num
    have h5 : M ≤ A ^ (3/4:ℝ) * M ^ (1/4:ℝ) := by
      calc M = M ^ (3/4:ℝ) * M ^ (1/4:ℝ) := h3.symm
        _ ≤ A ^ (3/4:ℝ) * M ^ (1/4:ℝ) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hM0.le _)
    have h6 : (0:ℝ) ≤ A ^ (3/4:ℝ) * M ^ (1/4:ℝ) := by positivity
    nlinarith
  · obtain ⟨S, hSsub, hScard, hSval⟩ := hS
    have hMA1 : 1 ≤ M / A := (one_le_div hA0).mpr hMA.le
    have hline' : ∀ m : ℕ, 2*m ≤ N →
        PolyReach J N m (fun x => g x / A) (alphaJ J ^ m * (M / A)) := by
      intro m hm
      have h := polyReach_div J N m g (alphaJ J ^ m * M) A hA0 (hline m hm)
      have heq : alphaJ J ^ m * M / A = alphaJ J ^ m * (M / A) := by ring
      rwa [heq] at h
    have hS' : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
        ∀ x ∈ S, |g x / A| ≤ 1 := by
      refine ⟨S, hSsub, hScard, ?_⟩
      intro x hx
      rw [abs_div, abs_of_pos hA0, div_le_one hA0]
      exact hSval x hx
    have h := oneDim_propagation_J hremez J N hN hJ hH1 hH2 (fun x => g x / A) (M / A) hMA1
      hline' hS' s hs
    rw [abs_div, abs_of_pos hA0, div_le_iff₀ hA0] at h
    have key : A * (M/A) ^ (1/4:ℝ) = A ^ (3/4:ℝ) * M ^ (1/4:ℝ) := by
      rw [Real.div_rpow hM0.le hA0.le]
      field_simp
      linear_combination -hApow
    have hrewrite : (CJ J * (M/A) ^ (1/4:ℝ) + 3 * (M/A) / 2 ^ (2*N)) * A
        = CJ J * (A * (M/A) ^ (1/4:ℝ)) + 3 * M / 2 ^ (2*N) := by
      field_simp
    rw [hrewrite, key] at h
    linarith

/-- The arithmetic of the second propagation at reach `2^J`: the bound produced by the first
one, raised to `3/4` and multiplied by `M^{1/4}`, is again of the shape of the three-ball
conclusion. -/
theorem compose_bound_J (J N : ℕ) (M B : ℝ) (hM : 1 ≤ M) (hB0 : 0 ≤ B)
    (hB : B ≤ CJ J * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N)) :
    CJ J * B ^ (3/4:ℝ) * M ^ (1/4:ℝ)
      ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) + 6 * CJ J * M / 2 ^ N := by
  have hM0 : (0:ℝ) < M := by linarith
  have hc := CJ_ge_three J
  have hc0 := CJ_pos J
  have hquarter : (0:ℝ) ≤ M ^ (1/4:ℝ) := Real.rpow_nonneg hM0.le _
  have hthree : (0:ℝ) ≤ M ^ (3/4:ℝ) := Real.rpow_nonneg hM0.le _
  have hmul : M ^ (3/4:ℝ) * M ^ (1/4:ℝ) = M := by
    rw [← Real.rpow_add hM0]; norm_num
  have hdecay : (0:ℝ) ≤ 6 * CJ J * M / 2 ^ N := by positivity
  rcases le_or_gt (3 * M / 2 ^ (2*N)) (CJ J * M ^ (1/4:ℝ)) with hcase | hcase
  · have h1 : B ≤ 2 * CJ J * M ^ (1/4:ℝ) := by linarith
    have h2 : B ^ (3/4:ℝ) ≤ (2 * CJ J * M ^ (1/4:ℝ)) ^ (3/4:ℝ) :=
      Real.rpow_le_rpow hB0 h1 (by norm_num)
    have h3 : (2 * CJ J * M ^ (1/4:ℝ)) ^ (3/4:ℝ)
        = (2 * CJ J) ^ (3/4:ℝ) * (M ^ (1/4:ℝ)) ^ (3/4:ℝ) :=
      Real.mul_rpow (by linarith) hquarter
    have h4 : (2 * CJ J) ^ (3/4:ℝ) ≤ 2 * CJ J := by
      calc (2 * CJ J) ^ (3/4:ℝ) ≤ (2 * CJ J) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        _ = 2 * CJ J := Real.rpow_one _
    have hX : (0:ℝ) ≤ (M ^ (1/4:ℝ)) ^ (3/4:ℝ) := Real.rpow_nonneg hquarter _
    have h5 : B ^ (3/4:ℝ) ≤ 2 * CJ J * (M ^ (1/4:ℝ)) ^ (3/4:ℝ) := by
      refine le_trans h2 (le_of_eq h3 |>.trans ?_)
      exact mul_le_mul_of_nonneg_right h4 hX
    have h6 := rpow_seven_sixteen M hM
    calc CJ J * B ^ (3/4:ℝ) * M ^ (1/4:ℝ)
        ≤ CJ J * (2 * CJ J * (M ^ (1/4:ℝ)) ^ (3/4:ℝ)) * M ^ (1/4:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hc0.le) hquarter
      _ = 2 * (CJ J)^2 * ((M ^ (1/4:ℝ)) ^ (3/4:ℝ) * M ^ (1/4:ℝ)) := by ring
      _ ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) := mul_le_mul_of_nonneg_left h6 (by positivity)
      _ ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) + 6 * CJ J * M / 2 ^ N := by linarith
  · have hdd : 6 * M / 2 ^ (2*N) = 2 * (3 * M / 2 ^ (2*N)) := by ring
    have h1 : B ≤ 6 * M / 2 ^ (2*N) := by rw [hdd]; linarith
    have hd : (0:ℝ) < (2:ℝ) ^ (2*N) := by positivity
    have hpos : (0:ℝ) < (2:ℝ) ^ N := by positivity
    have hden : (0:ℝ) < ((2:ℝ) ^ (2*N)) ^ (3/4:ℝ) := Real.rpow_pos_of_pos hd _
    have h2 : B ^ (3/4:ℝ) ≤ (6 * M / 2 ^ (2*N)) ^ (3/4:ℝ) :=
      Real.rpow_le_rpow hB0 h1 (by norm_num)
    have h3 : (6 * M / 2 ^ (2*N)) ^ (3/4:ℝ)
        = (6:ℝ) ^ (3/4:ℝ) * M ^ (3/4:ℝ) / ((2:ℝ) ^ (2*N)) ^ (3/4:ℝ) := by
      rw [Real.div_rpow (by positivity) hd.le, Real.mul_rpow (by norm_num) hM0.le]
    have h4 : (6:ℝ) ^ (3/4:ℝ) ≤ 6 := by
      calc (6:ℝ) ^ (3/4:ℝ) ≤ (6:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 6 := Real.rpow_one _
    have hnum : (6:ℝ) ^ (3/4:ℝ) * M ^ (3/4:ℝ) ≤ 6 * M ^ (3/4:ℝ) :=
      mul_le_mul_of_nonneg_right h4 hthree
    have hstep : (6:ℝ) ^ (3/4:ℝ) * M ^ (3/4:ℝ) / ((2:ℝ) ^ (2*N)) ^ (3/4:ℝ)
        ≤ 6 * M ^ (3/4:ℝ) / (2:ℝ) ^ N := by
      rw [div_le_div_iff₀ hden hpos]
      calc (6:ℝ) ^ (3/4:ℝ) * M ^ (3/4:ℝ) * (2:ℝ) ^ N ≤ 6 * M ^ (3/4:ℝ) * (2:ℝ) ^ N :=
            mul_le_mul_of_nonneg_right hnum hpos.le
        _ ≤ 6 * M ^ (3/4:ℝ) * ((2:ℝ) ^ (2*N)) ^ (3/4:ℝ) :=
            mul_le_mul_of_nonneg_left (two_pow_rpow_ge N) (by positivity)
    have h5 : B ^ (3/4:ℝ) ≤ 6 * M ^ (3/4:ℝ) / (2:ℝ) ^ N := by
      refine le_trans h2 ?_
      rw [h3]
      exact hstep
    have hsqrt : (0:ℝ) ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) := by positivity
    calc CJ J * B ^ (3/4:ℝ) * M ^ (1/4:ℝ)
        ≤ CJ J * (6 * M ^ (3/4:ℝ) / (2:ℝ) ^ N) * M ^ (1/4:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hc0.le) hquarter
      _ = 6 * CJ J * (M ^ (3/4:ℝ) * M ^ (1/4:ℝ)) / (2:ℝ) ^ N := by field_simp
      _ = 6 * CJ J * M / (2:ℝ) ^ N := by rw [hmul]
      _ ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) + 6 * CJ J * M / 2 ^ N := by linarith

/-- **The two-dimensional propagation at reach `2^J`.**  The one-dimensional propagation is
applied first along the horizontal lines carrying a dense half of the points where `|u| ≤ 1`,
and then along every vertical line, whose own dense half is that set of horizontal lines. -/
theorem prop2d_core_J (hremez : RemezInput) (J N : ℕ) (hN : 6 ≤ N) (hJ : 1 ≤ J)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (hH2 : 5*J*(N/2) + 2*N ≤ (3*J+2)*N)
    (u : ℤ → ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hbound : ∀ s t : ℤ, |s| ≤ 2^J*(N:ℤ) → |t| ≤ 2^J*(N:ℤ) → |u s t| ≤ M)
    (hlineH : ∀ m : ℕ, 2*m ≤ N → ∀ t : ℤ, |t| ≤ 2^J*(N:ℤ) →
      PolyReach J N m (fun s => u s t) (alphaJ J ^ m * M))
    (hlineV : ∀ m : ℕ, 2*m ≤ N → ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) →
      PolyReach J N m (fun t => u s t) (alphaJ J ^ m * M))
    (T : Finset ℤ) (hTsub : T ⊆ seg N) (hTcard : 2 * T.card ≥ (seg N).card)
    (hTline : ∀ t ∈ T, ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
      ∀ s ∈ S, |u s t| ≤ 1) :
    ∀ s t : ℤ, |s| ≤ 2^J*(N:ℤ) → |t| ≤ 2^J*(N:ℤ) →
      |u s t| ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) + (6 * CJ J + 3) * M / 2 ^ N := by
  have hM0 : (0:ℝ) < M := by linarith
  have hc := CJ_ge_three J
  have hc0 := CJ_pos J
  have hquarter : (1:ℝ) ≤ M ^ (1/4:ℝ) := Real.one_le_rpow hM (by norm_num)
  set B := CJ J * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N) with hBdef
  have hone : (1:ℤ) ≤ 2^J := one_le_pow₀ (by norm_num)
  have hseg : ∀ y : ℤ, y ∈ seg N → |y| ≤ 2^J*(N:ℤ) := by
    intro y hy
    rw [seg, Finset.mem_Icc] at hy
    have hyN : |y| ≤ (N:ℤ) := by rw [abs_le]; exact ⟨hy.1, hy.2⟩
    nlinarith [Int.natCast_nonneg N, abs_nonneg y]
  have hH : ∀ y ∈ T, ∀ x : ℤ, |x| ≤ 2^J*(N:ℤ) → |u x y| ≤ B :=
    fun y hy x hx => oneDim_propagation_J hremez J N hN hJ hH1 hH2 (fun z => u z y) M hM
      (fun m hm => hlineH m hm y (hseg y (hTsub hy))) (hTline y hy) x hx
  have hdec : (0:ℝ) ≤ 3 * M / 2 ^ (2*N) := by positivity
  have hB1 : (1:ℝ) ≤ B := by
    rw [hBdef]
    nlinarith
  have hB0 : (0:ℝ) ≤ B := by linarith
  intro s t hs ht
  have hV := oneDim_scaled_J hremez J N hN hJ hH1 hH2 (fun y => u s y) B M hB1 hM
      (fun y hy => hbound s y hs hy) (fun m hm => hlineV m hm s hs)
      ⟨T, hTsub, hTcard, fun y hy => hH y hy s hs⟩ t ht
  have hcomp := compose_bound_J J N M B hM hB0 (le_of_eq hBdef)
  have hlast : 3 * M / 2 ^ (2*N) ≤ 3 * M / 2 ^ N := by
    have h1 : (0:ℝ) < (2:ℝ) ^ N := by positivity
    have h2 : (2:ℝ) ^ N ≤ (2:ℝ) ^ (2*N) := two_pow_le_two_pow N (2*N) (by omega)
    gcongr
  have hsum : 6 * CJ J * M / 2 ^ N + 3 * M / 2 ^ N = (6 * CJ J + 3) * M / 2 ^ N := by
    field_simp
  linarith

/-- **The three-ball inequality on a lattice box, at reach `2^J`.**  A function whose line data
is supplied at every degree up to `N/2` along both families of lattice lines out to the box of
radius `2^J N`, bounded by `M` there and by one on a `(1-ε)` fraction of the box of radius `N`,
obeys the three-ball bound on the box of radius `2^J N`. -/
theorem threeBall_reach (hremez : RemezInput) (J N : ℕ) (hN : 6 ≤ N) (hJ : 1 ≤ J)
    (hH1 : (3*J+2)*N ≤ 24*J*(N/2)) (hH2 : 5*J*(N/2) + 2*N ≤ (3*J+2)*N)
    (u : ℤ → ℤ → ℝ) (M ε : ℝ) (hM : 1 ≤ M) (hε : ε ≤ 1/4)
    (hbound : ∀ s t : ℤ, |s| ≤ 2^J*(N:ℤ) → |t| ≤ 2^J*(N:ℤ) → |u s t| ≤ M)
    (hlineH : ∀ m : ℕ, 2*m ≤ N → ∀ t : ℤ, |t| ≤ 2^J*(N:ℤ) →
      PolyReach J N m (fun s => u s t) (alphaJ J ^ m * M))
    (hlineV : ∀ m : ℕ, 2*m ≤ N → ∀ s : ℤ, |s| ≤ 2^J*(N:ℤ) →
      PolyReach J N m (fun t => u s t) (alphaJ J ^ m * M))
    (hdens : (1 - ε) * ((box N).card : ℝ) ≤
      (((box N).filter (fun x => |u x.1 x.2| ≤ 1)).card : ℝ)) :
    ∀ s t : ℤ, |s| ≤ 2^J*(N:ℤ) → |t| ≤ 2^J*(N:ℤ) →
      |u s t| ≤ 2 * (CJ J)^2 * M ^ (1/2:ℝ) + (6 * CJ J + 3) * M / 2 ^ N := by
  obtain ⟨T, hTsub, hTcard, hTline⟩ := cover_step_density N u ε hε hdens
  exact prop2d_core_J hremez J N hN hJ hH1 hH2 u M hM hbound hlineH hlineV T hTsub hTcard hTline

end UCPlanar.Support.Three
