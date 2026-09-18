/-
The one-dimensional propagation of the three-ball proposition, in the two cases of
`ucplanar.tex:495-540`, and its composition along the two families of lattice lines.

The constants are those of the paper: the approximation quality is `α = 2⁻²⁴` and the case
split is at `M = 32^N`, which is `M exp(βN) = 1` for `β = -log 32`.
-/
import UCPlanar.Support.ThreeBridge

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

/-- The approximation quality of the polynomial approximation lemma used in the three-ball
proof.  It has to beat the growth of the Remez factor at the fourth root, which is what
`32 ≤ αThree⁻¹ ^ (1/4)` says. -/
noncomputable def alphaThree : ℝ := ((2:ℝ) ^ (24:ℕ))⁻¹

theorem alphaThree_pos : 0 < alphaThree := by
  rw [alphaThree]; positivity

theorem alphaThree_lt_one : alphaThree < 1 := by
  rw [alphaThree]
  rw [inv_lt_one_iff₀]
  right
  norm_num

theorem alphaThree_pow (i : ℕ) : alphaThree ^ i = ((2:ℝ) ^ (24*i))⁻¹ := by
  rw [alphaThree, inv_pow, ← pow_mul]

/-- The Remez ratio of the propagation is at most `32`, since the degree is at most `N/2`. -/
theorem ratio_le_32 (N m : ℕ) (hN : 0 < N) (hm : 2*m ≤ N) :
    16 * (N:ℝ) / ((N:ℝ) - (m:ℝ)) ≤ 32 := by
  have hm' : 2 * (m:ℝ) ≤ (N:ℝ) := by exact_mod_cast hm
  have hN' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hpos : (0:ℝ) < (N:ℝ) - (m:ℝ) := by linarith
  rw [div_le_iff₀ hpos]
  linarith

/-- The fourth root of a power of two. -/
theorem rpow_two_pow (i : ℕ) : ((2:ℝ) ^ (24*i)) ^ (1/4:ℝ) = (64:ℝ) ^ i := by
  rw [← Real.rpow_natCast (2:ℝ) (24*i), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ((24*i : ℕ):ℝ) * (1/4:ℝ) = ((6*i : ℕ):ℝ) by push_cast; ring]
  rw [Real.rpow_natCast, pow_mul]
  norm_num

/-- **Case 1 arithmetic.**  If the degree `i+1` is minimal with `α^(i+1) M ≤ 1`, so that
`α^i M > 1`, then the Remez factor `32^(i+1)` is at most `64 M^{1/4}`. -/
theorem pow32_le_of_min (i : ℕ) (M : ℝ) (h : 1 < alphaThree ^ i * M) :
    (32:ℝ) ^ (i+1) ≤ 64 * M ^ (1/4:ℝ) := by
  have h2 : (0:ℝ) < (2:ℝ) ^ (24*i) := by positivity
  have hMgt : ((2:ℝ) ^ (24*i)) < M := by
    rw [alphaThree_pow] at h
    rw [inv_mul_eq_div, lt_div_iff₀ h2] at h
    linarith
  have hroot : (64:ℝ) ^ i ≤ M ^ (1/4:ℝ) := by
    rw [← rpow_two_pow i]
    exact Real.rpow_le_rpow (le_of_lt h2) (le_of_lt hMgt) (by norm_num)
  have h32 : (32:ℝ) ^ (i+1) ≤ 64 * (64:ℝ) ^ i := by
    rw [pow_succ]
    have : (32:ℝ) ^ i ≤ (64:ℝ) ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
    nlinarith [pow_pos (show (0:ℝ) < 32 by norm_num) i]
  calc (32:ℝ) ^ (i+1) ≤ 64 * (64:ℝ) ^ i := h32
    _ ≤ 64 * M ^ (1/4:ℝ) := by
        have := hroot
        linarith


/-- Monotonicity of the powers of two. -/
theorem two_pow_le_two_pow (a b : ℕ) (h : a ≤ b) : (2:ℝ) ^ a ≤ (2:ℝ) ^ b :=
  pow_le_pow_right₀ (by norm_num) h

/-- `32^N` in base two. -/
theorem pow32_eq (N : ℕ) : (32:ℝ) ^ N = (2:ℝ) ^ (5*N) := by
  rw [pow_mul]
  norm_num

/-- In the first case of the propagation a degree `N/2` already makes the approximation error
at most one, so the minimal such degree is at most `N/2`. -/
theorem alphaThree_half_le (N : ℕ) (M : ℝ) (hM : M ≤ (32:ℝ) ^ N) (hN : 2 ≤ N) :
    alphaThree ^ (N/2) * M ≤ 1 := by
  have hexp : 5 * N ≤ 24 * (N/2) := by omega
  have hpos : (0:ℝ) < (2:ℝ) ^ (24*(N/2)) := by positivity
  rw [alphaThree_pow, inv_mul_eq_div, div_le_one hpos]
  calc M ≤ (32:ℝ) ^ N := hM
    _ = (2:ℝ) ^ (5*N) := pow32_eq N
    _ ≤ (2:ℝ) ^ (24*(N/2)) := two_pow_le_two_pow _ _ hexp


/-- The minimal degree at which the approximation error drops below one, as in case 1 of
`ucplanar.tex:495-510`, together with its minimality. -/
theorem exists_minimal_degree (N : ℕ) (M : ℝ) (hN : 2 ≤ N) (hM : M ≤ (32:ℝ) ^ N) :
    ∃ j : ℕ, 2*j ≤ N ∧ alphaThree ^ j * M ≤ 1 ∧ ∀ i : ℕ, i + 1 = j → 1 < alphaThree ^ i * M := by
  classical
  have hex : ∃ j : ℕ, alphaThree ^ j * M ≤ 1 := ⟨N/2, alphaThree_half_le N M hM hN⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · have hle := Nat.find_min' hex (alphaThree_half_le N M hM hN)
    omega
  · intro i hi
    exact not_le.mp (Nat.find_min hex (by omega))

/-- **Case 1 of the one-dimensional propagation**, `ucplanar.tex:495-510`: if the outer bound is
below `32^N`, the minimal degree with approximation error at most one gives the bound
`192 M^{1/4}` on the doubled interval. -/
theorem oneDim_case_small (hremez : RemezInput) (N : ℕ) (hN : 6 ≤ N) (g : ℤ → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hcase : M ≤ (32:ℝ) ^ N)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyLine N m g (alphaThree ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ 1) :
    ∀ s : ℤ, |s| ≤ 2*(N:ℤ) → |g s| ≤ 192 * M ^ (1/4:ℝ) := by
  have hNpos : 0 < N := by omega
  obtain ⟨j, h2j, hj, hmin⟩ := exists_minimal_degree N M (by omega) hcase
  have hjlt : (j:ℝ) < (N:ℝ) := by
    have : j < N := by omega
    exact_mod_cast this
  have hε0 : 0 ≤ alphaThree ^ j * M := by
    have := alphaThree_pos
    positivity
  have hbd := oneDim_from_poly hremez N j hNpos hjlt g 1 (alphaThree ^ j * M)
      (by norm_num) hε0 (hline j h2j) hS
  intro s hs
  have h1 := hbd s hs
  have hratio : (16 * (N:ℝ) / ((N:ℝ) - (j:ℝ))) ^ j ≤ (32:ℝ) ^ j := by
    refine pow_le_pow_left₀ ?_ (ratio_le_32 N j hNpos h2j) j
    have hpos : (0:ℝ) < (N:ℝ) - (j:ℝ) := by linarith
    positivity
  have h32pos : (1:ℝ) ≤ (32:ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h2 : (1 + alphaThree ^ j * M) * (16*(N:ℝ)/((N:ℝ)-(j:ℝ))) ^ j + alphaThree ^ j * M
      ≤ 3 * (32:ℝ) ^ j := by nlinarith [hratio, hj, hε0, h32pos]
  have h3 : (3:ℝ) * (32:ℝ) ^ j ≤ 192 * M ^ (1/4:ℝ) := by
    have hMroot : (1:ℝ) ≤ M ^ (1/4:ℝ) := Real.one_le_rpow hM (by norm_num)
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, pow_zero]
      linarith
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have := pow32_le_of_min i M (hmin i rfl)
      linarith
  linarith [h1, h2, h3]

/-- **Case 2 of the one-dimensional propagation**, `ucplanar.tex:512-530`: if the outer bound
exceeds `32^N`, the degree `N/2` gives the exponentially small bound `3 M / 2^{2N}`. -/
theorem oneDim_case_large (hremez : RemezInput) (N : ℕ) (hN : 6 ≤ N) (g : ℤ → ℝ) (M : ℝ)
    (hM : 1 ≤ M) (hcase : (32:ℝ) ^ N < M)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyLine N m g (alphaThree ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ 1) :
    ∀ s : ℤ, |s| ≤ 2*(N:ℤ) → |g s| ≤ 3 * M / 2 ^ (2*N) := by
  have hNpos : 0 < N := by omega
  set h := N/2 with hh
  have h2h : 2*h ≤ N := by omega
  have hhlt : (h:ℝ) < (N:ℝ) := by
    have : h < N := by omega
    exact_mod_cast this
  have hε0 : 0 ≤ alphaThree ^ h * M := by
    have := alphaThree_pos
    positivity
  have hbd := oneDim_from_poly hremez N h hNpos hhlt g 1 (alphaThree ^ h * M)
      (by norm_num) hε0 (hline h h2h) hS
  intro s hs
  have h1 := hbd s hs
  have hratio : (16 * (N:ℝ) / ((N:ℝ) - (h:ℝ))) ^ h ≤ (32:ℝ) ^ h := by
    refine pow_le_pow_left₀ ?_ (ratio_le_32 N h hNpos h2h) h
    have hpos : (0:ℝ) < (N:ℝ) - (h:ℝ) := by linarith
    positivity
  have hεeq : alphaThree ^ h * M = M / 2 ^ (24*h) := by
    rw [alphaThree_pow]
    field_simp
  have e1 : (32:ℝ) ^ h * 2 ^ (2*N) ≤ M := by
    rw [pow32_eq, ← pow_add]
    calc (2:ℝ) ^ (5*h + 2*N) ≤ (2:ℝ) ^ (5*N) := two_pow_le_two_pow _ _ (by omega)
      _ ≤ M := by rw [← pow32_eq]; linarith
  have e2 : (M / 2 ^ (24*h)) * ((32:ℝ) ^ h * 2 ^ (2*N)) ≤ M := by
    rw [pow32_eq, ← pow_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hpow : (2:ℝ) ^ (5*h + 2*N) ≤ (2:ℝ) ^ (24*h) := two_pow_le_two_pow _ _ (by omega)
    nlinarith [hpow, hM]
  have e3 : (M / 2 ^ (24*h)) * 2 ^ (2*N) ≤ M := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have hpow : (2:ℝ) ^ (2*N) ≤ (2:ℝ) ^ (24*h) := two_pow_le_two_pow _ _ (by omega)
    nlinarith [hpow, hM]
  have hε0' : 0 ≤ M / 2 ^ (24*h) := by positivity
  have hpowpos : (0:ℝ) < 2 ^ (2*N) := by positivity
  have key : (1 + M / 2 ^ (24*h)) * (16*(N:ℝ)/((N:ℝ)-(h:ℝ))) ^ h + M / 2 ^ (24*h)
      ≤ 3 * M / 2 ^ (2*N) := by
    rw [le_div_iff₀ hpowpos]
    have hratio' : (1 + M / 2 ^ (24*h)) * (16*(N:ℝ)/((N:ℝ)-(h:ℝ))) ^ h
        ≤ (1 + M / 2 ^ (24*h)) * (32:ℝ) ^ h :=
      mul_le_mul_of_nonneg_left hratio (by linarith)
    calc ((1 + M / 2 ^ (24*h)) * (16*(N:ℝ)/((N:ℝ)-(h:ℝ))) ^ h + M / 2 ^ (24*h)) * 2 ^ (2*N)
        ≤ ((1 + M / 2 ^ (24*h)) * (32:ℝ) ^ h + M / 2 ^ (24*h)) * 2 ^ (2*N) := by
          exact mul_le_mul_of_nonneg_right (by linarith) hpowpos.le
      _ = (32:ℝ) ^ h * 2 ^ (2*N) + (M / 2 ^ (24*h)) * ((32:ℝ) ^ h * 2 ^ (2*N))
            + (M / 2 ^ (24*h)) * 2 ^ (2*N) := by ring
      _ ≤ M + M + M := by linarith [e1, e2, e3]
      _ = 3 * M := by ring
  rw [hεeq] at h1
  linarith [h1, key]

/-- Dividing the line data by a positive constant. -/
theorem polyLine_div (N m : ℕ) (g : ℤ → ℝ) (ε A : ℝ) (hA : 0 < A) (h : PolyLine N m g ε) :
    PolyLine N m (fun s => g s / A) (ε / A) := by
  obtain ⟨q, hdeg, hq⟩ := h
  refine ⟨Polynomial.C A⁻¹ * q, ?_, ?_⟩
  · exact le_trans (Polynomial.natDegree_mul_le) (by simpa using hdeg)
  · intro s hs
    have h1 := hq s hs
    have : (Polynomial.C A⁻¹ * q).eval (s:ℝ) = q.eval (s:ℝ) / A := by
      simp [Polynomial.eval_mul, div_eq_inv_mul]
    rw [this, div_sub_div_same, abs_div, abs_of_pos hA]
    gcongr


/-- **The one-dimensional propagation**, the two cases of `ucplanar.tex:495-540` together: a
function whose line data is approximated at every degree up to `N/2`, bounded by one on half of
the integer points of `[-N, N]`, is bounded on `[-2N, 2N]` by `192 M^{1/4} + 3 M 2^{-2N}`. -/
theorem oneDim_propagation (hremez : RemezInput) (N : ℕ) (hN : 6 ≤ N) (g : ℤ → ℝ) (M : ℝ)
    (hM : 1 ≤ M)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyLine N m g (alphaThree ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ 1) :
    ∀ s : ℤ, |s| ≤ 2*(N:ℤ) → |g s| ≤ 192 * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N) := by
  intro s hs
  rcases le_or_gt M ((32:ℝ) ^ N) with hc | hc
  · have h := oneDim_case_small hremez N hN g M hM hc hline hS s hs
    have hnn : (0:ℝ) ≤ 3 * M / 2 ^ (2*N) := by positivity
    linarith
  · have h := oneDim_case_large hremez N hN g M hM hc hline hS s hs
    have hnn : (0:ℝ) ≤ 192 * M ^ (1/4:ℝ) := by positivity
    linarith

/-- The one-dimensional propagation from a general bound `A ≥ 1` on the dense half of the line,
by scaling.  This is what the second, vertical, application of the propagation consumes. -/
theorem oneDim_scaled (hremez : RemezInput) (N : ℕ) (hN : 6 ≤ N) (g : ℤ → ℝ) (A M : ℝ)
    (hA : 1 ≤ A) (hM : 1 ≤ M)
    (hgM : ∀ s : ℤ, |s| ≤ 2*(N:ℤ) → |g s| ≤ M)
    (hline : ∀ m : ℕ, 2*m ≤ N → PolyLine N m g (alphaThree ^ m * M))
    (hS : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧ ∀ s ∈ S, |g s| ≤ A) :
    ∀ s : ℤ, |s| ≤ 2*(N:ℤ) →
      |g s| ≤ 192 * A ^ (3/4:ℝ) * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N) := by
  intro s hs
  have hA0 : (0:ℝ) < A := by linarith
  have hM0 : (0:ℝ) < M := by linarith
  have hdecay : (0:ℝ) ≤ 3 * M / 2 ^ (2*N) := by positivity
  have hApow : A ^ (3/4:ℝ) * A ^ (1/4:ℝ) = A := by
    rw [← Real.rpow_add hA0]
    norm_num
  rcases le_or_gt M A with hMA | hMA
  · have h1 := hgM s hs
    have h2 : M ^ (3/4:ℝ) ≤ A ^ (3/4:ℝ) := Real.rpow_le_rpow hM0.le hMA (by norm_num)
    have h3 : M ^ (3/4:ℝ) * M ^ (1/4:ℝ) = M := by
      rw [← Real.rpow_add hM0]
      norm_num
    have h5 : M ≤ A ^ (3/4:ℝ) * M ^ (1/4:ℝ) := by
      calc M = M ^ (3/4:ℝ) * M ^ (1/4:ℝ) := h3.symm
        _ ≤ A ^ (3/4:ℝ) * M ^ (1/4:ℝ) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hM0.le _)
    have h6 : (0:ℝ) ≤ A ^ (3/4:ℝ) * M ^ (1/4:ℝ) := by positivity
    linarith
  · obtain ⟨S, hSsub, hScard, hSval⟩ := hS
    have hMA1 : 1 ≤ M / A := (one_le_div hA0).mpr hMA.le
    have hline' : ∀ m : ℕ, 2*m ≤ N →
        PolyLine N m (fun x => g x / A) (alphaThree ^ m * (M / A)) := by
      intro m hm
      have h := polyLine_div N m g (alphaThree ^ m * M) A hA0 (hline m hm)
      have heq : alphaThree ^ m * M / A = alphaThree ^ m * (M / A) := by ring
      rwa [heq] at h
    have hS' : ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
        ∀ x ∈ S, |g x / A| ≤ 1 := by
      refine ⟨S, hSsub, hScard, ?_⟩
      intro x hx
      rw [abs_div, abs_of_pos hA0, div_le_one hA0]
      exact hSval x hx
    have h := oneDim_propagation hremez N hN (fun x => g x / A) (M / A) hMA1 hline' hS' s hs
    rw [abs_div, abs_of_pos hA0, div_le_iff₀ hA0] at h
    have key : A * (M/A) ^ (1/4:ℝ) = A ^ (3/4:ℝ) * M ^ (1/4:ℝ) := by
      rw [Real.div_rpow hM0.le hA0.le]
      field_simp
      linear_combination -hApow
    have hrewrite : (192 * (M/A) ^ (1/4:ℝ) + 3 * (M/A) / 2 ^ (2*N)) * A
        = 192 * (A * (M/A) ^ (1/4:ℝ)) + 3 * M / 2 ^ (2*N) := by
      field_simp
    rw [hrewrite, key] at h
    linarith


/-- A power of two against a fractional power of its square. -/
theorem two_pow_rpow_ge (N : ℕ) : (2:ℝ) ^ N ≤ ((2:ℝ) ^ (2*N)) ^ (3/4:ℝ) := by
  have h1 : ((2:ℝ) ^ (2*N)) ^ (3/4:ℝ) = (2:ℝ) ^ (((2*N : ℕ):ℝ) * (3/4:ℝ)) := by
    rw [← Real.rpow_natCast (2:ℝ) (2*N), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : (2:ℝ) ^ N = (2:ℝ) ^ ((N : ℕ):ℝ) := by
    rw [Real.rpow_natCast]
  rw [h1, h2]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ?_
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- **The exponent of the two propagations.**  Applying the propagation along the two families
of lines composes the exponent `1/4` with itself into `2·(1/4) - (1/4)² = 7/16`, which is at
most `1/2`.  This is the point of running the one-dimensional step at `1/4` rather than at the
`1/2` of `ucplanar.tex:508`: two applications of an exponent `θ` give `2θ - θ²`, which exceeds
`1/2` when `θ = 1/2`. -/
theorem rpow_seven_sixteen (M : ℝ) (hM : 1 ≤ M) :
    (M ^ (1/4:ℝ)) ^ (3/4:ℝ) * M ^ (1/4:ℝ) ≤ M ^ (1/2:ℝ) := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have h1 : (M ^ (1/4:ℝ)) ^ (3/4:ℝ) = M ^ (3/16:ℝ) := by
    rw [← Real.rpow_mul hM0]
    norm_num
  have h2 : M ^ (3/16:ℝ) * M ^ (1/4:ℝ) = M ^ (7/16:ℝ) := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < M)]
    norm_num
  rw [h1, h2]
  exact Real.rpow_le_rpow_of_exponent_le hM (by norm_num)

/-- The arithmetic of the second propagation: the bound produced by the first one, raised to
`3/4` and multiplied by `M^{1/4}`, is again of the shape of the three-ball conclusion. -/
theorem compose_bound (N : ℕ) (M B : ℝ) (hM : 1 ≤ M) (hB0 : 0 ≤ B)
    (hB : B ≤ 192 * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N)) :
    192 * B ^ (3/4:ℝ) * M ^ (1/4:ℝ) ≤ 73728 * M ^ (1/2:ℝ) + 1152 * M / 2 ^ N := by
  have hM0 : (0:ℝ) < M := by linarith
  have hquarter : (0:ℝ) ≤ M ^ (1/4:ℝ) := Real.rpow_nonneg hM0.le _
  have hthree : (0:ℝ) ≤ M ^ (3/4:ℝ) := Real.rpow_nonneg hM0.le _
  have hmul : M ^ (3/4:ℝ) * M ^ (1/4:ℝ) = M := by
    rw [← Real.rpow_add hM0]
    norm_num
  rcases le_or_gt (3 * M / 2 ^ (2*N)) (192 * M ^ (1/4:ℝ)) with hc | hc
  · have h1 : B ≤ 384 * M ^ (1/4:ℝ) := by linarith
    have h2 : B ^ (3/4:ℝ) ≤ (384 * M ^ (1/4:ℝ)) ^ (3/4:ℝ) :=
      Real.rpow_le_rpow hB0 h1 (by norm_num)
    have h3 : (384 * M ^ (1/4:ℝ)) ^ (3/4:ℝ)
        = (384:ℝ) ^ (3/4:ℝ) * (M ^ (1/4:ℝ)) ^ (3/4:ℝ) :=
      Real.mul_rpow (by norm_num) hquarter
    have h4 : (384:ℝ) ^ (3/4:ℝ) ≤ 384 := by
      calc (384:ℝ) ^ (3/4:ℝ) ≤ (384:ℝ) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 384 := Real.rpow_one _
    have hX : (0:ℝ) ≤ (M ^ (1/4:ℝ)) ^ (3/4:ℝ) := Real.rpow_nonneg hquarter _
    have h5 : B ^ (3/4:ℝ) ≤ 384 * (M ^ (1/4:ℝ)) ^ (3/4:ℝ) := by
      refine le_trans h2 (le_of_eq h3 |>.trans ?_)
      exact mul_le_mul_of_nonneg_right h4 hX
    have h6 := rpow_seven_sixteen M hM
    have hdecay : (0:ℝ) ≤ 1152 * M / 2 ^ N := by positivity
    nlinarith [h5, h6, hquarter, hX, hdecay]
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
    have hfinal : 192 * B ^ (3/4:ℝ) * M ^ (1/4:ℝ) ≤ 1152 * M / 2 ^ N := by
      have hstep2 : 192 * B ^ (3/4:ℝ) * M ^ (1/4:ℝ)
          ≤ 192 * (6 * M ^ (3/4:ℝ) / (2:ℝ) ^ N) * M ^ (1/4:ℝ) := by
        have := mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℝ) ≤ 192)
        exact mul_le_mul_of_nonneg_right this hquarter
      have heq : 192 * (6 * M ^ (3/4:ℝ) / (2:ℝ) ^ N) * M ^ (1/4:ℝ)
          = 1152 * (M ^ (3/4:ℝ) * M ^ (1/4:ℝ)) / (2:ℝ) ^ N := by
        field_simp
        ring
      rw [heq, hmul] at hstep2
      exact hstep2
    have hsqrt : (0:ℝ) ≤ 73728 * M ^ (1/2:ℝ) := by positivity
    linarith


/-- **The two-dimensional propagation.**  The one-dimensional propagation is applied first
along the horizontal lines carrying a dense half of the points where `|u| ≤ 1`, and then along
every vertical line, whose own dense half is exactly that set of horizontal lines.  This is the
step described at `ucplanar.tex:488` ("We estimate ... and then repeat, propagating the bounds
from the horizontal direction to the vertical direction"). -/
theorem prop2d_core (hremez : RemezInput) (N : ℕ) (hN : 6 ≤ N) (u : ℤ → ℤ → ℝ) (M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ s t : ℤ, |s| ≤ 2*(N:ℤ) → |t| ≤ 2*(N:ℤ) → |u s t| ≤ M)
    (hlineH : ∀ m : ℕ, 2*m ≤ N → ∀ t : ℤ, |t| ≤ 2*(N:ℤ) →
      PolyLine N m (fun s => u s t) (alphaThree ^ m * M))
    (hlineV : ∀ m : ℕ, 2*m ≤ N → ∀ s : ℤ, |s| ≤ 2*(N:ℤ) →
      PolyLine N m (fun t => u s t) (alphaThree ^ m * M))
    (T : Finset ℤ) (hTsub : T ⊆ seg N) (hTcard : 2 * T.card ≥ (seg N).card)
    (hTline : ∀ t ∈ T, ∃ S : Finset ℤ, S ⊆ seg N ∧ 2 * S.card ≥ (seg N).card ∧
      ∀ s ∈ S, |u s t| ≤ 1) :
    ∀ s t : ℤ, |s| ≤ 2*(N:ℤ) → |t| ≤ 2*(N:ℤ) →
      |u s t| ≤ 73728 * M ^ (1/2:ℝ) + 1155 * M / 2 ^ N := by
  have hM0 : (0:ℝ) < M := by linarith
  have hquarter : (1:ℝ) ≤ M ^ (1/4:ℝ) := Real.one_le_rpow hM (by norm_num)
  set B := 192 * M ^ (1/4:ℝ) + 3 * M / 2 ^ (2*N) with hBdef
  have hseg : ∀ y : ℤ, y ∈ seg N → |y| ≤ 2*(N:ℤ) := by
    intro y hy
    rw [seg, Finset.mem_Icc] at hy
    rw [abs_le]
    omega
  have hH : ∀ y ∈ T, ∀ x : ℤ, |x| ≤ 2*(N:ℤ) → |u x y| ≤ B :=
    fun y hy x hx => oneDim_propagation hremez N hN (fun z => u z y) M hM
      (fun m hm => hlineH m hm y (hseg y (hTsub hy))) (hTline y hy) x hx
  have hdec : (0:ℝ) ≤ 3 * M / 2 ^ (2*N) := by positivity
  have hB1 : (1:ℝ) ≤ B := by
    rw [hBdef]
    linarith
  have hB0 : (0:ℝ) ≤ B := by linarith
  intro s t hs ht
  have hV := oneDim_scaled hremez N hN (fun y => u s y) B M hB1 hM
      (fun y hy => hbound s y hs hy) (fun m hm => hlineV m hm s hs)
      ⟨T, hTsub, hTcard, fun y hy => hH y hy s hs⟩ t ht
  have hcomp := compose_bound N M B hM hB0 (le_of_eq hBdef)
  have hlast : 3 * M / 2 ^ (2*N) ≤ 3 * M / 2 ^ N := by
    have h1 : (0:ℝ) < (2:ℝ) ^ N := by positivity
    have h2 : (2:ℝ) ^ N ≤ (2:ℝ) ^ (2*N) := two_pow_le_two_pow N (2*N) (by omega)
    gcongr
  have hsum : 1152 * M / 2 ^ N + 3 * M / 2 ^ N = 1155 * M / 2 ^ N := by ring
  linarith


/-- **The three-ball inequality on a lattice box.**  A function whose line data is supplied at
every degree up to `N/2` along both families of lattice lines, bounded by `M` on the box of
radius `2N` and by one on a `(1-ε)` fraction of the box of radius `N`, obeys the three-ball
bound on the box of radius `2N`.  This is the lattice content of `ucplanar.tex:486-540`; the
counting that produces the dense set of lines is the half-lines lemma. -/
theorem threeBall_lattice (hremez : RemezInput) (N : ℕ) (hN : 6 ≤ N) (u : ℤ → ℤ → ℝ) (M ε : ℝ)
    (hM : 1 ≤ M) (hε : ε ≤ 1/4)
    (hbound : ∀ s t : ℤ, |s| ≤ 2*(N:ℤ) → |t| ≤ 2*(N:ℤ) → |u s t| ≤ M)
    (hlineH : ∀ m : ℕ, 2*m ≤ N → ∀ t : ℤ, |t| ≤ 2*(N:ℤ) →
      PolyLine N m (fun s => u s t) (alphaThree ^ m * M))
    (hlineV : ∀ m : ℕ, 2*m ≤ N → ∀ s : ℤ, |s| ≤ 2*(N:ℤ) →
      PolyLine N m (fun t => u s t) (alphaThree ^ m * M))
    (hdens : (1 - ε) * ((box N).card : ℝ) ≤
      (((box N).filter (fun x => |u x.1 x.2| ≤ 1)).card : ℝ)) :
    ∀ s t : ℤ, |s| ≤ 2*(N:ℤ) → |t| ≤ 2*(N:ℤ) →
      |u s t| ≤ 73728 * M ^ (1/2:ℝ) + 1155 * M / 2 ^ N := by
  obtain ⟨T, hTsub, hTcard, hTline⟩ := cover_step_density N u ε hε hdens
  exact prop2d_core hremez N hN u M hM hbound hlineH hlineV T hTsub hTcard hTline

end UCPlanar.Support.Three
