/-
The bootstrap of the exponential lower bound.

The chain dichotomy only starts once the maximum exceeds a fixed constant.  That is forced by the
gradient estimate: a function which is at least `2` somewhere and at most `1` on a large portion
of every square cannot have all of its lattice increments small, because small increments
propagate the value `2` along a whole orbit, and an orbit is a fixed positive fraction of a
square.  This module proves the propagation.
-/
import UCPlanar.Support.LowerVolume
import UCPlanar.Support.Poly.DerivBound
import Mathlib.Data.Int.Interval

open scoped Classical
set_option autoImplicit false

namespace UCPlanar.Support.Lower

/-- A one-dimensional walk with increments at most `δ` moves the value by at most `|q| δ`. -/
theorem line_walk (h : ℤ → ℝ) (δ : ℝ) (_hδ : 0 ≤ δ) (T : ℤ)
    (hstep : ∀ q : ℤ, |q| ≤ T → |q+1| ≤ T → |h (q+1) - h q| ≤ δ) :
    ∀ q : ℤ, |q| ≤ T → |h q - h 0| ≤ (q.natAbs : ℝ) * δ := by
  intro q
  induction q using Int.induction_on with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hn1 : |(n:ℤ)| ≤ T := by rw [abs_le] at hn ⊢; omega
    have h1 := ih hn1
    have h2 : |h ((n:ℤ)+1) - h (n:ℤ)| ≤ δ := hstep n hn1 hn
    have h3 : |h ((n:ℤ)+1) - h 0| ≤ |h ((n:ℤ)+1) - h (n:ℤ)| + |h (n:ℤ) - h 0| := by
      have := abs_add_le (h ((n:ℤ)+1) - h (n:ℤ)) (h (n:ℤ) - h 0)
      simpa using this
    have hna : ((n:ℤ)).natAbs = n := by omega
    have hna1 : (((n:ℤ)+1)).natAbs = n + 1 := by omega
    rw [hna1]
    rw [hna] at h1
    push_cast
    linarith
  | pred n ih =>
    intro hn
    have hn1 : |(-(n:ℤ))| ≤ T := by rw [abs_le] at hn ⊢; omega
    have h1 := ih hn1
    have h2 := hstep (-(n:ℤ)-1) hn (by rw [abs_le] at hn1 ⊢; omega)
    have heq : (-(n:ℤ)-1)+1 = -(n:ℤ) := by omega
    rw [heq] at h2
    have h3 : |h (-(n:ℤ)-1) - h 0| ≤ |h (-(n:ℤ)-1) - h (-(n:ℤ))| + |h (-(n:ℤ)) - h 0| := by
      have := abs_add_le (h (-(n:ℤ)-1) - h (-(n:ℤ))) (h (-(n:ℤ)) - h 0)
      simpa using this
    have h6 : |h (-(n:ℤ)-1) - h (-(n:ℤ))| = |h (-(n:ℤ)) - h (-(n:ℤ)-1)| := abs_sub_comm _ _
    have hna : (-(n:ℤ)).natAbs = n := by omega
    have hna1 : ((-(n:ℤ)-1)).natAbs = n + 1 := by omega
    rw [hna1]
    rw [hna] at h1
    push_cast
    linarith [h1, h2, h3, h6.le, h6.ge]

/-- **The grid walk.**  A function on the lattice square of half-side `T` whose increments along
the two generators are at most `δ` differs from its value at the origin by at most `2Tδ`. -/
theorem grid_walk (g : ℤ → ℤ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (T : ℤ) (_hT : 0 ≤ T)
    (hcol : ∀ q : ℤ, |q| ≤ T → |q+1| ≤ T → |g 0 (q+1) - g 0 q| ≤ δ)
    (hrow : ∀ p q : ℤ, |p| ≤ T → |p+1| ≤ T → |q| ≤ T → |g (p+1) q - g p q| ≤ δ) :
    ∀ p q : ℤ, |p| ≤ T → |q| ≤ T → |g p q - g 0 0| ≤ (2*(T:ℝ))*δ := by
  intro p q hp hq
  have hcolbound : |g 0 q - g 0 0| ≤ (q.natAbs : ℝ) * δ :=
    line_walk (fun s => g 0 s) δ hδ T hcol q hq
  have hrowbound : |g p q - g 0 q| ≤ (p.natAbs : ℝ) * δ :=
    line_walk (fun s => g s q) δ hδ T (fun s hs hs1 => hrow s q hs hs1 hq) p hp
  have htri : |g p q - g 0 0| ≤ |g p q - g 0 q| + |g 0 q - g 0 0| := by
    have := abs_add_le (g p q - g 0 q) (g 0 q - g 0 0)
    simpa using this
  have hpT : (p.natAbs : ℝ) ≤ (T:ℝ) := by
    have hp' := hp
    rw [abs_le] at hp'
    have h : ((p.natAbs : ℕ) : ℤ) ≤ T := by omega
    have h2 := (Int.cast_le (R := ℝ)).mpr h
    simpa using h2
  have hqT : (q.natAbs : ℝ) ≤ (T:ℝ) := by
    have hq' := hq
    rw [abs_le] at hq'
    have h : ((q.natAbs : ℕ) : ℤ) ≤ T := by omega
    have h2 := (Int.cast_le (R := ℝ)).mpr h
    simpa using h2
  nlinarith [htri, hcolbound, hrowbound, hpT, hqT, hδ]

/-- The lattice vector with the given two coordinates. -/
def vec (p q : ℤ) : LatticeProb.Site 2 := fun i => if i = 0 then p else q

theorem vec_zero : vec 0 0 = 0 := by
  funext i; by_cases h : i = 0 <;> simp [vec, h]

theorem vec_succ_fst (p q : ℤ) : vec (p+1) q = vec 1 0 + vec p q := by
  funext i
  by_cases h : i = 0 <;> simp [vec, h]
  omega

theorem vec_succ_snd (q : ℤ) : vec 0 (q+1) = vec 0 1 + vec 0 q := by
  funext i
  by_cases h : i = 0 <;> simp [vec, h]
  omega

theorem vec_injective {p q p' q' : ℤ} (h : vec p q = vec p' q') : p = p' ∧ q = q' := by
  constructor
  · have := congrFun h 0; simpa [vec] using this
  · have := congrFun h 1; simpa [vec] using this

/-- **Small lattice increments propagate the value along the whole orbit.** -/
theorem orbit_propagation {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (x₀ : V)
    (δ : ℝ) (hδ : 0 ≤ δ) (T : ℤ) (hT : 0 ≤ T)
    (hrow : ∀ p q : ℤ, |p| ≤ T → |p+1| ≤ T → |q| ≤ T →
       |f (P.shift (vec 1 0) (P.shift (vec p q) x₀)) - f (P.shift (vec p q) x₀)| ≤ δ)
    (hcol : ∀ q : ℤ, |q| ≤ T → |q+1| ≤ T →
       |f (P.shift (vec 0 1) (P.shift (vec 0 q) x₀)) - f (P.shift (vec 0 q) x₀)| ≤ δ) :
    ∀ p q : ℤ, |p| ≤ T → |q| ≤ T → |f (P.shift (vec p q) x₀) - f x₀| ≤ 2*(T:ℝ)*δ := by
  intro p q hp hq
  have hbase : f (P.shift (vec 0 0) x₀) = f x₀ := by rw [vec_zero, P.shift_zero]
  have hkey := grid_walk (fun p q => f (P.shift (vec p q) x₀)) δ hδ T hT
    (by
      intro q hq1 hq2
      have heq : P.shift (vec 0 (q+1)) x₀ = P.shift (vec 0 1) (P.shift (vec 0 q) x₀) := by
        rw [vec_succ_snd, P.shift_add]
      simpa [heq] using hcol q hq1 hq2)
    (by
      intro p' q' hp1 hp2 hq1
      have heq : P.shift (vec (p'+1) q') x₀ = P.shift (vec 1 0) (P.shift (vec p' q') x₀) := by
        rw [vec_succ_fst, P.shift_add]
      simpa [heq] using hrow p' q' hp1 hp2 hq1)
    p q hp hq
  rwa [hbase] at hkey

/-- **A whole orbit of exceptional vertices.**  If every orbit point of the lattice box of
half-side `T` lies in the square and carries `|f| > 1`, the exceptional count of the square is at
least `(2T+1)²`. -/
theorem orbit_exceptional {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (x₀ : V)
    (S : ℝ) (T : ℕ)
    (hall : ∀ p q : ℤ, |p| ≤ (T:ℤ) → |q| ≤ (T:ℤ) → P.shift (vec p q) x₀ ∈ P.square S)
    (hbig : ∀ p q : ℤ, |p| ≤ (T:ℤ) → |q| ≤ (T:ℤ) → 1 < |f (P.shift (vec p q) x₀)|) :
    (2*T+1)^2 ≤ ((P.square S).filter (fun x => ¬ (|f x| ≤ 1))).card := by
  classical
  set Box : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(T:ℤ)) (T:ℤ)) ×ˢ (Finset.Icc (-(T:ℤ)) (T:ℤ)) with hBox
  have hmem : ∀ z ∈ Box, P.shift (vec z.1 z.2) x₀ ∈ (P.square S).filter (fun x => ¬ (|f x| ≤ 1)) := by
    intro z hz
    rw [hBox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hz
    have h1 : |z.1| ≤ (T:ℤ) := by rw [abs_le]; exact ⟨hz.1.1, hz.1.2⟩
    have h2 : |z.2| ≤ (T:ℤ) := by rw [abs_le]; exact ⟨hz.2.1, hz.2.2⟩
    exact Finset.mem_filter.mpr ⟨hall z.1 z.2 h1 h2, not_le.mpr (hbig z.1 z.2 h1 h2)⟩
  have hinj : ∀ z ∈ (Box : Set (ℤ × ℤ)), ∀ w ∈ (Box : Set (ℤ × ℤ)),
      P.shift (vec z.1 z.2) x₀ = P.shift (vec w.1 w.2) x₀ → z = w := by
    intro z _ w _ h
    have h1 : vec z.1 z.2 = vec w.1 w.2 := UCPlanar.Support.shift_site_injective P x₀ h
    obtain ⟨e1, e2⟩ := vec_injective h1
    exact Prod.ext e1 e2
  have hcard : Box.card ≤ ((P.square S).filter (fun x => ¬ (|f x| ≤ 1))).card :=
    Finset.card_le_card_of_injOn (fun z => P.shift (vec z.1 z.2) x₀) hmem hinj
  have hIcc : (Finset.Icc (-(T:ℤ)) (T:ℤ)).card = 2 * T + 1 := by
    rw [Int.card_Icc]; omega
  have hBoxCard : Box.card = (2*T+1)^2 := by
    rw [hBox, Finset.card_product, hIcc]
    ring
  omega

/-- **The gradient estimate along one lattice generator.**  The derivative bound at word length
one: a single lattice increment of a harmonic function on `Q_{3R}` is at most `C₁/R` times its
maximum there.  This is the estimate that turns a large increment at the scale `√N` into a large
maximum at the scale `N^{3/4}`. -/
theorem single_step_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c) (a₁ a₂ : LatticeProb.Site 2) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ R : ℝ, 1 ≤ R → C₁ ≤ R → ∀ f : V → ℝ,
      (∀ x ∈ P.square (3*R), LatticeProb.Network.netLaplacian P.graph c f x = 0) →
      ∀ x ∈ P.square R, ∀ a : LatticeProb.Site 2, (a = a₁ ∨ a = a₂) →
        |f (P.shift a x) - f x| ≤ (C₁/R) * UCPlanar.supNorm (P.square (3*R)) f := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := UCPlanar.Support.exists_derivative_bound P c hc hp hMos a₁ a₂
  refine ⟨C₁, hC₁0, ?_⟩
  intro R hR hCR f hf x hx a ha
  have hw := hC₁ R hR [a] (by
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact ha) (by simp) (by simpa using hCR) f hf x hx
  have hval : P.diffWord [a] f x = f (P.shift a x) - f x := rfl
  rw [hval] at hw
  simpa using hw

/-- **All lattice increments cannot be small.**  If `f` is at least `2` at a vertex, every
lattice increment along the two generators inside the orbit box is at most `δ` with `2Tδ ≤ 1/4`,
and the orbit box sits inside `Q_S`, then the whole orbit carries `|f| > 1`, so the exceptional
count of `Q_S` is at least `(2T+1)²`, which the density forbids. -/
theorem small_increments_contradict {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (x₀ : V) (S ε δ : ℝ) (T : ℕ) (hδ : 0 ≤ δ)
    (hx₀ : 2 ≤ f x₀)
    (hδT : 2*(T:ℝ)*δ ≤ 1/4)
    (hall : ∀ p q : ℤ, |p| ≤ (T:ℤ) → |q| ≤ (T:ℤ) → P.shift (vec p q) x₀ ∈ P.square S)
    (hdens : 1 - ε ≤ UCPlanar.boundedDensity (P.square S) f 1)
    (hcount : ε * (((P.square S).card : ℕ) : ℝ) < (((2*T+1)^2 : ℕ) : ℝ))
    (hrow : ∀ p q : ℤ, |p| ≤ (T:ℤ) → |p+1| ≤ (T:ℤ) → |q| ≤ (T:ℤ) →
       |f (P.shift (vec 1 0) (P.shift (vec p q) x₀)) - f (P.shift (vec p q) x₀)| ≤ δ)
    (hcol : ∀ q : ℤ, |q| ≤ (T:ℤ) → |q+1| ≤ (T:ℤ) →
       |f (P.shift (vec 0 1) (P.shift (vec 0 q) x₀)) - f (P.shift (vec 0 q) x₀)| ≤ δ) :
    False := by
  classical
  have hTnn : (0:ℤ) ≤ (T:ℤ) := Int.natCast_nonneg T
  have hprop := orbit_propagation P f x₀ δ hδ (T:ℤ) hTnn hrow hcol
  have hbig : ∀ p q : ℤ, |p| ≤ (T:ℤ) → |q| ≤ (T:ℤ) → 1 < |f (P.shift (vec p q) x₀)| := by
    intro p q hp hq
    have h1 := hprop p q hp hq
    have h2 : |f (P.shift (vec p q) x₀) - f x₀| ≤ 1/4 := by
      refine le_trans h1 ?_
      have : ((T:ℤ) : ℝ) = (T:ℕ) := by push_cast; ring
      rw [this]
      exact hδT
    have h3 : 7/4 ≤ f (P.shift (vec p q) x₀) := by
      have := abs_le.mp h2
      linarith [this.1, this.2, hx₀]
    calc (1:ℝ) < 7/4 := by norm_num
      _ ≤ f (P.shift (vec p q) x₀) := h3
      _ ≤ |f (P.shift (vec p q) x₀)| := le_abs_self _
  have hexc := orbit_exceptional P f x₀ S T hall hbig
  set A := P.square S with hA
  have hAne : A.Nonempty := by
    refine ⟨x₀, ?_⟩
    have := hall 0 0 (by simp) (by simp)
    rwa [vec_zero, P.shift_zero] at this
  have hApos : (0:ℝ) < (A.card : ℝ) := by
    have : 0 < A.card := Finset.card_pos.mpr hAne
    exact_mod_cast this
  have hgood : (1 - ε) * (A.card : ℝ) ≤ ((A.filter (fun x => |f x| ≤ 1)).card : ℝ) := by
    have h := hdens
    simp only [UCPlanar.boundedDensity] at h
    rw [le_div_iff₀ hApos] at h
    linarith
  have hsplit : ((A.filter (fun x => |f x| ≤ 1)).card : ℝ)
      + ((A.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) = (A.card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not (s := A) (p := fun x => |f x| ≤ 1)
    exact_mod_cast this
  have hbad : ((A.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) ≤ ε * (A.card : ℝ) := by linarith
  have hexcR : (((2*T+1)^2 : ℕ) : ℝ) ≤ ((A.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) := by
    exact_mod_cast hexc
  linarith [hexcR, hbad, hcount]

/-- **The orbit box sits in a square.**  The drawing of a lattice vector of coordinates at most
`T` has length at most `B T`, so the orbit box of half-side `T` around a vertex of `Q_r` lies in
`Q_{r + BT}`. -/
theorem orbit_in_square {V : Type*} (P : UCPlanar.PeriodicGraph V) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖) (x₀ : V) (r : ℝ)
    (hx₀ : x₀ ∈ P.square r) (T : ℕ) :
    ∀ p q : ℤ, |p| ≤ (T:ℤ) → |q| ≤ (T:ℤ) →
      P.shift (vec p q) x₀ ∈ P.square (r + B*(T:ℝ)) := by
  intro p q hp hq
  have hnorm : ‖(fun i => (((vec p q) i : ℤ) : ℝ))‖ ≤ (T:ℝ) := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    have hj : |((vec p q) j : ℤ)| ≤ (T:ℤ) := by
      by_cases h : j = 0 <;> simp [vec, h] <;> [exact hp; exact hq]
    have h1 : |((((vec p q) j : ℤ)) : ℝ)| ≤ (T:ℝ) := by
      have := (Int.cast_le (R := ℝ)).mpr hj
      rwa [Int.cast_abs] at this
    simpa [Real.norm_eq_abs] using h1
  have hM : ∀ i, |P.period (fun i => (((vec p q) i : ℤ) : ℝ)) i| ≤ B*(T:ℝ) := by
    intro i
    have h1 := norm_le_pi_norm (P.period (fun i => (((vec p q) i : ℤ) : ℝ))) i
    rw [Real.norm_eq_abs] at h1
    refine le_trans h1 (le_trans (hB _) ?_)
    exact mul_le_mul_of_nonneg_left hnorm hB0
  exact UCPlanar.Support.shift_mem_square P (vec p q) (B*(T:ℝ)) hM r x₀ hx₀

end UCPlanar.Support.Lower
