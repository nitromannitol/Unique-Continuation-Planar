/-
Finite weighted graph Laplacians and harmonicity.
The paper uses the negative of the shared network Laplacian.
-/
import LatticeProb.Network.Basic
import Mathlib.Tactic

open scoped BigOperators Classical
set_option autoImplicit false

/-- **The weighted Laplacian is the negative of the network Laplacian.**  Expanding
`netLaplacian` and negating the sum term by term gives `∑ c(x,y)(f(x) - f(y)) = -Δf(x)`. -/
theorem UCPlanar.Support.laplacian_sign {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (c : V → V → ℝ) (f : V → ℝ) (x : V) :
    ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) = - LatticeProb.Network.netLaplacian G c f x := by
  classical
  simp only [LatticeProb.Network.netLaplacian, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- **Harmonicity restricts to subsets.**  A function harmonic on `S` is harmonic on any
`T ⊆ S`. -/
theorem UCPlanar.Support.harmonic_mono {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} {f : V → ℝ} {S T : Set V}
    (h : LatticeProb.Network.HarmonicOn G c f S) (hTS : T ⊆ S) :
    LatticeProb.Network.HarmonicOn G c f T := by
  intro x hx
  exact h x (hTS hx)

/-- **The sum of two harmonic functions is harmonic**, since `netLaplacian` is additive. -/
theorem UCPlanar.Support.harmonic_add {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} {f g : V → ℝ} {S : Set V}
    (hf : LatticeProb.Network.HarmonicOn G c f S) (hg : LatticeProb.Network.HarmonicOn G c g S) :
    LatticeProb.Network.HarmonicOn G c (f + g) S := by
  intro x hx
  rw [LatticeProb.Network.netLaplacian_add, hf x hx, hg x hx, add_zero]

/-- **A scalar multiple of a harmonic function is harmonic**, since `netLaplacian` is
`ℝ`-linear. -/
theorem UCPlanar.Support.harmonic_smul {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} {f : V → ℝ} {S : Set V}
    (hf : LatticeProb.Network.HarmonicOn G c f S) (a : ℝ) :
    LatticeProb.Network.HarmonicOn G c (fun x => a * f x) S := by
  intro x hx
  rw [LatticeProb.Network.netLaplacian_smul, hf x hx, mul_zero]

/-- **A positively weighted sum that vanishes has a negative term.**  If `∑ cᵢfᵢ = 0` with all
`cᵢ > 0` on `s` and some `fᵢ > 0`, some other `fⱼ` must be negative, else the sum would be
strictly positive. -/
theorem UCPlanar.Support.weighted_opposite {ι : Type*} (s : Finset ι) (c f : ι → ℝ)
    (hc : ∀ i ∈ s, 0 < c i) (hzero : ∑ i ∈ s, c i * f i = 0)
    (i : ι) (hi : i ∈ s) (hfi : 0 < f i) : ∃ j ∈ s, f j < 0 := by
  classical
  by_contra h
  push Not at h
  have hp : 0 < ∑ j ∈ s, c j * f j :=
    Finset.sum_pos' (fun j hj => mul_nonneg (hc j hj).le (h j hj))
      ⟨i, hi, mul_pos (hc i hi) hfi⟩
  linarith

/-- **A harmonic maximum is constant on its neighbors.**  If `x` is a pointwise maximum among
its neighbors and `netLaplacian` vanishes at `x`, each term `c(x,y)(f(y) - f(x))` of the sum is
nonpositive, so the sum vanishing forces every term, hence every neighbor value, to be `f(x)`. -/
theorem UCPlanar.Support.maximum_neighbors {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} {f : V → ℝ} (hc : LatticeProb.Network.IsCond G c) (x : V)
    (hh : LatticeProb.Network.netLaplacian G c f x = 0)
    (hmax : ∀ y, G.Adj x y → f y ≤ f x) : ∀ y, G.Adj x y → f y = f x := by
  classical
  rw [LatticeProb.Network.netLaplacian] at hh
  have hn : ∀ y ∈ G.neighborFinset x, c x y * (f y - f x) ≤ 0 := by
    intro y hy
    have ha := (SimpleGraph.mem_neighborFinset G x y).mp hy
    exact mul_nonpos_of_nonneg_of_nonpos (hc.pos ha).le (sub_nonpos.mpr (hmax y ha))
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hn).mp hh
  intro y hy
  have he := hz y ((SimpleGraph.mem_neighborFinset G x y).mpr hy)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hc.pos hy).ne')

/-- **A weighted sum in a bounded conductance band that vanishes has a very negative term.**
If `∑ cᵢfᵢ = 0` with each `cᵢ ∈ [lam, big]` and one `fᵢ` exceeds `big · s.card · A / lam`, some
other `fⱼ` must fall below `-A`, by bounding the sum's parts against the band's extremes. -/
theorem UCPlanar.Support.band_opposite {ι : Type*} (s : Finset ι) (c f : ι → ℝ)
    (A lam big : ℝ) (hA : 0 ≤ A) (hlam : 0 < lam) (hbig : 0 ≤ big)
    (hc : ∀ i ∈ s, lam ≤ c i ∧ c i ≤ big) (hmean : ∑ i ∈ s, c i * f i = 0)
    (i : ι) (hi : i ∈ s) (hlarge : big * s.card * A < lam * f i) :
    ∃ j ∈ s, f j < -A := by
  classical
  by_contra hn
  push Not at hn
  have hc0 : ∀ j ∈ s, 0 ≤ c j := fun j hj => le_trans hlam.le (hc j hj).1
  have hb : ∀ j ∈ s, -big*A ≤ c j*f j := by
    intro j hj
    have h1 := mul_le_mul_of_nonneg_left (hn j hj) (hc0 j hj)
    have h2 := mul_le_mul_of_nonneg_right (hc j hj).2 hA
    nlinarith
  have hsum : ∑ j ∈ s, (c j*f j+big*A) = (s.card : ℝ)*big*A := by
    rw [Finset.sum_add_distrib, hmean, Finset.sum_const, nsmul_eq_mul]
    ring
  have hone : c i*f i+big*A ≤ ∑ j ∈ s, (c j*f j+big*A) :=
    Finset.single_le_sum (f := fun j => c j*f j+big*A)
      (fun j hj => by nlinarith [hb j hj]) hi
  rw [hsum] at hone
  have hfi : 0 < f i := by
    have hn0 : 0 ≤ big * (s.card : ℝ) * A := by positivity
    nlinarith
  have hweight := mul_le_mul_of_nonneg_right (hc i hi).1 hfi.le
  have hba : 0 ≤ big*A := mul_nonneg hbig hA
  nlinarith
