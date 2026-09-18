/-
The discrete Caccioppoli inequality for a forward difference along a lattice vector.

The variational Caccioppoli inequality of `Caccioppoli.lean` controls the Dirichlet energy of
a harmonic function across the edges of the graph.  A lattice vector is not an edge, but a
vertex and its translate are joined by a walk of bounded length, and the walks emanating from
the points of one square are translates of finitely many fixed walks, so each of them can be
compared with the energy of the square it lies in.
-/
import UCPlanar.Support.Poly.Elliptic
import UCPlanar.Support.Poly.Square

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- The square of radius `R` is the set of vertices whose drawing has norm at most `R`. -/
theorem mem_square_iff_norm {V : Type*} (P : UCPlanar.PeriodicGraph V) {R : ℝ} (hR : 0 ≤ R)
    (x : V) : x ∈ P.square R ↔ ‖P.pos x‖ ≤ R := by
  rw [mem_square_iff]
  constructor
  · intro h
    refine (pi_norm_le_iff_of_nonneg hR).mpr ?_
    intro i
    simpa [Real.norm_eq_abs] using h i
  · intro h i
    have h2 : ‖P.pos x i‖ ≤ R := le_trans (norm_le_pi_norm (P.pos x) i) h
    simpa [Real.norm_eq_abs] using h2

/-- The clamp to `[0,1]` is 1-Lipschitz. -/
theorem abs_clamp_sub_clamp_le (a b : ℝ) :
    |min (max a 0) 1 - min (max b 0) 1| ≤ |a - b| := by
  have hlip : LipschitzWith 1 (fun t : ℝ => min (max t 0) 1) :=
    (LipschitzWith.id.max_const 0).min_const 1
  have h := hlip.dist_le_mul a b
  simpa [Real.dist_eq] using h

/-- The Lipschitz cutoff of a pair of nested squares: one on `Q_ρ`, zero off `Q_τ`. -/
noncomputable def cutoff {V : Type*} (P : UCPlanar.PeriodicGraph V) (ρ τ : ℝ) : V → ℝ :=
  fun z => min (max ((τ - ‖P.pos z‖) / (τ - ρ)) 0) 1

theorem cutoff_nonneg {V : Type*} (P : UCPlanar.PeriodicGraph V) (ρ τ : ℝ) (z : V) :
    0 ≤ cutoff P ρ τ z := le_min (le_max_right _ _) zero_le_one

theorem cutoff_le_one {V : Type*} (P : UCPlanar.PeriodicGraph V) (ρ τ : ℝ) (z : V) :
    cutoff P ρ τ z ≤ 1 := min_le_right _ _

theorem cutoff_eq_one {V : Type*} (P : UCPlanar.PeriodicGraph V) {ρ τ : ℝ} (hρτ : ρ < τ)
    (hρ0 : 0 ≤ ρ) {z : V} (hz : z ∈ P.square ρ) : cutoff P ρ τ z = 1 := by
  have hn : ‖P.pos z‖ ≤ ρ := (mem_square_iff_norm P hρ0 z).mp hz
  have h1 : (1:ℝ) ≤ (τ - ‖P.pos z‖) / (τ - ρ) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h2 : (1:ℝ) ≤ max ((τ - ‖P.pos z‖) / (τ - ρ)) 0 := le_trans h1 (le_max_left _ _)
  exact min_eq_right h2

theorem cutoff_eq_zero {V : Type*} (P : UCPlanar.PeriodicGraph V) {ρ τ : ℝ} (hρτ : ρ < τ)
    (hτ0 : 0 ≤ τ) {z : V} (hz : z ∉ P.square τ) : cutoff P ρ τ z = 0 := by
  have hn : τ < ‖P.pos z‖ := by
    rw [← not_le]
    exact fun h => hz ((mem_square_iff_norm P hτ0 z).mpr h)
  have h1 : (τ - ‖P.pos z‖) / (τ - ρ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h2 : max ((τ - ‖P.pos z‖) / (τ - ρ)) 0 = 0 := max_eq_right h1
  rw [cutoff, h2]
  exact min_eq_left zero_le_one

theorem cutoff_lipschitz {V : Type*} (P : UCPlanar.PeriodicGraph V) {ρ τ D : ℝ} (hρτ : ρ < τ)
    {z w : V} (hD : ‖P.pos z - P.pos w‖ ≤ D) :
    |cutoff P ρ τ z - cutoff P ρ τ w| ≤ D / (τ - ρ) := by
  have hgap : (0:ℝ) < τ - ρ := by linarith
  refine le_trans (abs_clamp_sub_clamp_le _ _) ?_
  have hsub : (τ - ‖P.pos z‖) / (τ - ρ) - (τ - ‖P.pos w‖) / (τ - ρ)
      = (‖P.pos w‖ - ‖P.pos z‖) / (τ - ρ) := by
    rw [div_sub_div_same]; ring_nf
  have hnum : |‖P.pos w‖ - ‖P.pos z‖| ≤ D :=
    calc |‖P.pos w‖ - ‖P.pos z‖| = |‖P.pos z‖ - ‖P.pos w‖| := abs_sub_comm _ _
      _ ≤ ‖P.pos z - P.pos w‖ := abs_norm_sub_norm_le _ _
      _ ≤ D := hD
  rw [hsub, abs_div, abs_of_pos hgap]
  gcongr

/-- **A double count.**  A sum over the neighbours of the points of `S` is at most the maximal
degree times the sum over any set containing those neighbours. -/
theorem sum_neighbor_le {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (Δ : ℕ)
    (hΔ : ∀ x : V, (G.neighborFinset x).card ≤ Δ) (S T : Finset V) (g : V → ℝ)
    (hg : ∀ w, 0 ≤ g w) (hST : ∀ z ∈ S, ∀ w, G.Adj z w → w ∈ T) :
    ∑ z ∈ S, ∑ w ∈ G.neighborFinset z, g w ≤ (Δ : ℝ) * ∑ w ∈ T, g w := by
  classical
  have h1 : ∀ z ∈ S, ∑ w ∈ G.neighborFinset z, g w
      = ∑ w ∈ T, (if G.Adj z w then g w else 0) := by
    intro z hz
    have hA : ∑ w ∈ G.neighborFinset z, g w
        = ∑ w ∈ G.neighborFinset z, (if G.Adj z w then g w else 0) := by
      refine Finset.sum_congr rfl ?_
      intro w hw
      have h : G.Adj z w := by simpa using hw
      simp [h]
    have hB : ∑ w ∈ G.neighborFinset z, (if G.Adj z w then g w else 0)
        = ∑ w ∈ T, (if G.Adj z w then g w else 0) := by
      refine Finset.sum_subset ?_ ?_
      · intro w hw
        exact hST z hz w (by simpa using hw)
      · intro w _ hwn
        have h : ¬ G.Adj z w := by simpa using hwn
        simp [h]
    rw [hA, hB]
  calc ∑ z ∈ S, ∑ w ∈ G.neighborFinset z, g w
      = ∑ z ∈ S, ∑ w ∈ T, (if G.Adj z w then g w else 0) :=
        Finset.sum_congr rfl (fun z hz => h1 z hz)
    _ = ∑ w ∈ T, ∑ z ∈ S, (if G.Adj z w then g w else 0) := Finset.sum_comm
    _ ≤ ∑ w ∈ T, (Δ : ℝ) * g w := by
        refine Finset.sum_le_sum ?_
        intro w _
        have hsub : S.filter (fun z => G.Adj z w) ⊆ G.neighborFinset w := by
          intro z hz
          simp only [Finset.mem_filter] at hz
          simpa using hz.2.symm
        have hcard : (S.filter (fun z => G.Adj z w)).card ≤ Δ :=
          le_trans (Finset.card_le_card hsub) (hΔ w)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hg w)
    _ = (Δ : ℝ) * ∑ w ∈ T, g w := by rw [Finset.mul_sum]

/-- **The Caccioppoli energy bound on nested squares.**  The Dirichlet energy of a harmonic
function on `Q_ρ` is at most a constant multiple of `(D/(τ-ρ))²` times its `ℓ²` norm on `Q_s`,
where the cutoff runs from `Q_ρ` up to `Q_τ` and the outer square leaves room for one edge. -/
theorem energy_le {V : Type*} (P : UCPlanar.PeriodicGraph V) {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond P.graph c) {κ K D : ℝ} {Δ : ℕ}
    (hκ0 : 0 < κ) (hK0 : 0 ≤ K) (hD0 : 0 ≤ D)
    (hcb : ∀ x y, P.graph.Adj x y → κ ≤ c x y ∧ c x y ≤ K)
    (hD : ∀ x y, P.graph.Adj x y → ‖P.pos x - P.pos y‖ ≤ D)
    (hΔ : ∀ x : V, (P.graph.neighborFinset x).card ≤ Δ)
    {ρ τ s : ℝ} (hρ0 : 0 ≤ ρ) (hρτ : ρ < τ) (hτs : τ + 2*D ≤ s)
    (f : V → ℝ)
    (hf : ∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) :
    ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z, (f z - f w) ^ 2
      ≤ (8 * K * Δ / κ) * (D / (τ - ρ)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 := by
  classical
  set σ : ℝ := τ + D with hσdef
  set η : V → ℝ := cutoff P ρ τ with hηdef
  have hτ0 : (0:ℝ) ≤ τ := le_trans hρ0 hρτ.le
  have hτσ : τ ≤ σ := by rw [hσdef]; linarith
  have hσs : σ ≤ s := by rw [hσdef]; linarith
  have hρσ : ρ ≤ σ := le_trans hρτ.le hτσ
  have hgap : (0:ℝ) < τ - ρ := by linarith
  -- the neighbours of `Q_τ` lie in `Q_σ`
  have hnb : ∀ x ∈ P.square τ, ∀ y, P.graph.Adj x y → y ∈ P.square σ := by
    intro x hx y hxy
    rw [mem_square_iff_norm P hτ0] at hx
    rw [mem_square_iff_norm P (by linarith : (0:ℝ) ≤ σ)]
    calc ‖P.pos y‖ = ‖P.pos x - (P.pos x - P.pos y)‖ := by ring_nf
      _ ≤ ‖P.pos x‖ + ‖P.pos x - P.pos y‖ := norm_sub_le _ _
      _ ≤ τ + D := add_le_add hx (hD x y hxy)
  have hfS : ∀ x ∈ P.square σ, LatticeProb.Network.netLaplacian P.graph c f x = 0 :=
    fun x hx => hf x (square_mono P hσs hx)
  have hηzero : ∀ x, x ∉ P.square τ → η x = 0 :=
    fun x hx => cutoff_eq_zero P hρτ hτ0 hx
  have hcac := UCPlanar.Support.caccioppoli hc (P.square σ) (P.square τ) f η hfS hηzero
    (square_mono P hτσ) hnb
  -- the left side dominates `κ` times the energy on `Q_ρ`
  have hlow : κ * ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z, (f z - f w) ^ 2
      ≤ ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
          c x y * (f x - f y) ^ 2 * η x ^ 2 := by
    have hterm : ∀ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z, κ * (f z - f w) ^ 2
        ≤ ∑ w ∈ P.graph.neighborFinset z, c z w * (f z - f w) ^ 2 * η z ^ 2 := by
      intro z hz
      refine Finset.sum_le_sum ?_
      intro w hw
      have hadj : P.graph.Adj z w := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
      have hη1 : η z = 1 := cutoff_eq_one P hρτ hρ0 hz
      rw [hη1, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_right (hcb z w hadj).1 (sq_nonneg _)
    have hsub : ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z,
          c z w * (f z - f w) ^ 2 * η z ^ 2
        ≤ ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
            c x y * (f x - f y) ^ 2 * η x ^ 2 := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (square_mono P hρσ) ?_
      intro z _ _
      refine Finset.sum_nonneg fun w _ => ?_
      have := hc.nonneg z w
      positivity
    calc κ * ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z, (f z - f w) ^ 2
        = ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z, κ * (f z - f w) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
      _ ≤ ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z,
            c z w * (f z - f w) ^ 2 * η z ^ 2 := Finset.sum_le_sum hterm
      _ ≤ _ := hsub
  -- the right side is controlled by the Lipschitz constant of the cutoff
  have hself : ∑ x ∈ P.square σ, ∑ _y ∈ P.graph.neighborFinset x, f x ^ 2
      ≤ (Δ : ℝ) * ∑ x ∈ P.square s, f x ^ 2 := by
    have h1 : ∀ x ∈ P.square σ, ∑ _y ∈ P.graph.neighborFinset x, f x ^ 2 ≤ (Δ : ℝ) * f x ^ 2 := by
      intro x _
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hΔ x) (sq_nonneg _)
    calc ∑ x ∈ P.square σ, ∑ _y ∈ P.graph.neighborFinset x, f x ^ 2
        ≤ ∑ x ∈ P.square σ, (Δ : ℝ) * f x ^ 2 := Finset.sum_le_sum h1
      _ = (Δ : ℝ) * ∑ x ∈ P.square σ, f x ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (Δ : ℝ) * ∑ x ∈ P.square s, f x ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (square_mono P hσs)
            (fun x _ _ => sq_nonneg _)
  have hother : ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x, f y ^ 2
      ≤ (Δ : ℝ) * ∑ x ∈ P.square s, f x ^ 2 := by
    refine sum_neighbor_le Δ hΔ (P.square σ) (P.square s) (fun w => f w ^ 2)
      (fun w => sq_nonneg _) ?_
    intro z hz w hzw
    have hz' : ‖P.pos z‖ ≤ σ := (mem_square_iff_norm P (by linarith : (0:ℝ) ≤ σ) z).mp hz
    rw [mem_square_iff_norm P (by linarith : (0:ℝ) ≤ s)]
    calc ‖P.pos w‖ = ‖P.pos z - (P.pos z - P.pos w)‖ := by ring_nf
      _ ≤ ‖P.pos z‖ + ‖P.pos z - P.pos w‖ := norm_sub_le _ _
      _ ≤ σ + D := add_le_add hz' (hD z w hzw)
      _ ≤ s := by rw [hσdef]; linarith
  have hhigh : 4 * ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
        c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2
      ≤ 8 * K * (Δ : ℝ) * (D / (τ - ρ)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 := by
    have hterm : ∀ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2
        ≤ ∑ y ∈ P.graph.neighborFinset x,
            K * (D / (τ - ρ)) ^ 2 * (f x ^ 2 + f y ^ 2) := by
      intro x _
      refine Finset.sum_le_sum ?_
      intro y hy
      have hadj : P.graph.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      have hcK : c x y ≤ K := (hcb x y hadj).2
      have hc0 : 0 ≤ c x y := hc.nonneg x y
      have hlip : |η x - η y| ≤ D / (τ - ρ) := cutoff_lipschitz P hρτ (hD x y hadj)
      have hsq : (η x - η y) ^ 2 ≤ (D / (τ - ρ)) ^ 2 := by
        have h := sq_abs (η x - η y)
        nlinarith [abs_nonneg (η x - η y), hlip]
      have hsum0 : (0:ℝ) ≤ f x ^ 2 + f y ^ 2 := by positivity
      have hB0 : (0:ℝ) ≤ (η x - η y) ^ 2 := sq_nonneg _
      calc c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2
          ≤ K * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
            nlinarith [mul_nonneg hsum0 hB0, hcK]
        _ ≤ K * (f x ^ 2 + f y ^ 2) * (D / (τ - ρ)) ^ 2 := by
            nlinarith [mul_nonneg hK0 hsum0, hsq]
        _ = K * (D / (τ - ρ)) ^ 2 * (f x ^ 2 + f y ^ 2) := by ring
    have hsplit : ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x, (f x ^ 2 + f y ^ 2)
        ≤ 2 * (Δ : ℝ) * ∑ x ∈ P.square s, f x ^ 2 := by
      have hdec : ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x, (f x ^ 2 + f y ^ 2)
          = (∑ x ∈ P.square σ, ∑ _y ∈ P.graph.neighborFinset x, f x ^ 2)
            + ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x, f y ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by rw [← Finset.sum_add_distrib]
      rw [hdec]
      linarith [hself, hother]
    have heq : ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
          K * (D / (τ - ρ)) ^ 2 * (f x ^ 2 + f y ^ 2)
        = K * (D / (τ - ρ)) ^ 2
            * ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x, (f x ^ 2 + f y ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
    calc 4 * ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2
        ≤ 4 * ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x,
            K * (D / (τ - ρ)) ^ 2 * (f x ^ 2 + f y ^ 2) := by
          have := Finset.sum_le_sum hterm
          linarith
      _ = 4 * (K * (D / (τ - ρ)) ^ 2
            * ∑ x ∈ P.square σ, ∑ y ∈ P.graph.neighborFinset x, (f x ^ 2 + f y ^ 2)) := by
          rw [heq]
      _ ≤ 4 * (K * (D / (τ - ρ)) ^ 2 * (2 * (Δ : ℝ) * ∑ x ∈ P.square s, f x ^ 2)) := by
          have hKD : (0:ℝ) ≤ K * (D / (τ - ρ)) ^ 2 := by positivity
          nlinarith [hsplit, hKD]
      _ = 8 * K * (Δ : ℝ) * (D / (τ - ρ)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 := by ring
  have hchain : κ * ∑ z ∈ P.square ρ, ∑ w ∈ P.graph.neighborFinset z, (f z - f w) ^ 2
      ≤ 8 * K * (Δ : ℝ) * (D / (τ - ρ)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 :=
    le_trans hlow (le_trans hcac hhigh)
  have hrw : (8 * K * (Δ : ℝ) / κ) * (D / (τ - ρ)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2
      = (8 * K * (Δ : ℝ) * (D / (τ - ρ)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2) / κ := by
    field_simp
  rw [hrw, le_div_iff₀ hκ0, mul_comm]
  exact hchain

/-- The squared lattice difference is at most the length of a connecting chain times the
Dirichlet energy at the points of that chain. -/
theorem diff_sq_le_chain {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (x : V) (a : LatticeProb.Site 2) (L : ℕ) (z : ℕ → V)
    (hz0 : z 0 = x) (hzL : z L = P.shift a x)
    (hstep : ∀ i, z (i+1) = z i ∨ P.graph.Adj (z i) (z (i+1))) :
    P.diff a f x ^ 2 ≤ (L : ℝ) * ∑ i ∈ Finset.range L,
      ∑ w ∈ P.graph.neighborFinset (z i), (f (z i) - f w) ^ 2 := by
  classical
  have hbase : P.diff a f x ^ 2
      ≤ (L : ℝ) * ∑ i ∈ Finset.range L, (f (z (i+1)) - f (z i)) ^ 2 := by
    have h := UCPlanar.Support.sq_sub_le_range_sum (fun i => f (z i)) L
    simp only [hz0, hzL] at h
    simpa [UCPlanar.PeriodicGraph.diff] using h
  have hterm : ∀ i ∈ Finset.range L, (f (z (i+1)) - f (z i)) ^ 2
      ≤ ∑ w ∈ P.graph.neighborFinset (z i), (f (z i) - f w) ^ 2 := by
    intro i _
    rcases hstep i with heq | hadj
    · rw [heq, sub_self]
      simpa using Finset.sum_nonneg (fun w (_ : w ∈ P.graph.neighborFinset (z i)) => sq_nonneg (f (z i) - f w))
    · have hmem : z (i+1) ∈ P.graph.neighborFinset (z i) :=
        (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj
      have hsq : (f (z (i+1)) - f (z i)) ^ 2 = (f (z i) - f (z (i+1))) ^ 2 := by ring
      rw [hsq]
      exact Finset.single_le_sum
        (f := fun w => (f (z i) - f w) ^ 2) (fun w _ => sq_nonneg _) hmem
  exact le_trans hbase
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg L))

/-- **The discrete Caccioppoli inequality for a forward difference along a lattice vector.**
The constant depends on the network and on the vector, not on the two scales, and the gap
between the scales is asked to exceed that same constant, which is what puts the translate of
the inner square inside the outer one. -/
theorem exists_lattice_caccioppoli {V : Type*} (P : UCPlanar.PeriodicGraph V) {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (a : LatticeProb.Site 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ r s : ℝ, 0 < r → r + C ≤ s → ∀ f : V → ℝ,
      (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) →
      ∑ x ∈ P.square r, P.diff a f x ^ 2
        ≤ (C / (s - r)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_edge_bound P
  obtain ⟨κ, K, hκ0, hK0, hcb⟩ := exists_cond_bounds P hc hp
  obtain ⟨Δ, hΔ⟩ := exists_neighbor_card_bound P
  obtain ⟨L, hLwalk⟩ := exists_shift_walk_length P a
  have hcov : ∀ x : V, ∃ vb : V × LatticeProb.Site 2,
      vb.1 ∈ P.representatives ∧ P.shift vb.2 vb.1 = x := by
    intro x
    obtain ⟨v, hv, b, hb⟩ := P.covers x
    exact ⟨(v, b), hv, hb⟩
  set ch : V → V × LatticeProb.Site 2 := fun x => Classical.choose (hcov x) with hchdef
  have hch : ∀ x : V, (ch x).1 ∈ P.representatives ∧ P.shift (ch x).2 (ch x).1 = x :=
    fun x => Classical.choose_spec (hcov x)
  have hQex : ∀ v : V, ∃ p : P.graph.Walk v (P.shift a v),
      v ∈ P.representatives → p.length ≤ L := by
    intro v
    by_cases hv : v ∈ P.representatives
    · obtain ⟨p, hp'⟩ := hLwalk v hv
      exact ⟨p, fun _ => hp'⟩
    · exact ⟨(P.connected.preconnected v (P.shift a v)).some, fun h => absurd h hv⟩
  set Q : ∀ v : V, P.graph.Walk v (P.shift a v) := fun v => Classical.choose (hQex v) with hQdef
  have hQlen : ∀ v ∈ P.representatives, (Q v).length ≤ L :=
    fun v hv => Classical.choose_spec (hQex v) hv
  set zz : V → ℕ → V := fun x i => P.shift (ch x).2 ((Q (ch x).1).getVert i) with hzzdef
  have hz0 : ∀ x : V, zz x 0 = x := by
    intro x
    rw [hzzdef]
    simp only [SimpleGraph.Walk.getVert_zero]
    exact (hch x).2
  have hzL : ∀ x : V, zz x L = P.shift a x := by
    intro x
    have hlen : (Q (ch x).1).length ≤ L := hQlen _ (hch x).1
    rw [hzzdef]
    simp only [(Q (ch x).1).getVert_of_length_le hlen]
    rw [← P.shift_add, add_comm, P.shift_add, (hch x).2]
  have hzstep : ∀ (x : V) (i : ℕ), zz x (i+1) = zz x i ∨ P.graph.Adj (zz x i) (zz x (i+1)) := by
    intro x i
    by_cases hi : i < (Q (ch x).1).length
    · right
      exact (P.shift_adj _ _ _).mpr ((Q (ch x).1).adj_getVert_succ hi)
    · left
      rw [not_lt] at hi
      rw [hzzdef]
      simp only
      rw [(Q (ch x).1).getVert_of_length_le hi,
        (Q (ch x).1).getVert_of_length_le (le_trans hi (Nat.le_succ i))]
  have hzpos : ∀ (x : V) (i : ℕ), ‖P.pos (zz x i) - P.pos x‖ ≤ D * (L : ℝ) := by
    intro x i
    have hlen : (Q (ch x).1).length ≤ L := hQlen _ (hch x).1
    have hbase := norm_pos_getVert_sub P D hD0 hD (Q (ch x).1) i
    have hpx : P.pos x = P.pos (ch x).1 + P.period (fun j => (((ch x).2 j : ℤ) : ℝ)) := by
      conv_lhs => rw [← (hch x).2]
      rw [P.pos_shift]
    have hpos : P.pos (zz x i) - P.pos x
        = P.pos ((Q (ch x).1).getVert i) - P.pos (ch x).1 := by
      rw [hzzdef]
      simp only
      rw [P.pos_shift, hpx]
      abel
    rw [hpos, ← norm_neg, neg_sub]
    refine le_trans hbase ?_
    have : ((Q (ch x).1).length : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlen
    nlinarith
  -- the constants
  set Rc : ℝ := (P.representatives.card : ℝ) with hRcdef
  have hRc0 : (0:ℝ) ≤ Rc := by rw [hRcdef]; positivity
  set B : ℝ := 32 * (L:ℝ)^2 * Rc * K * (Δ:ℝ) * D^2 / κ with hBdef
  set Cm : ℝ := 2*D*((L:ℝ)+2) + 1 with hCmdef
  set C : ℝ := max Cm (max B 1) with hCdef
  have hC1 : (1:ℝ) ≤ C := le_trans (le_max_right B 1) (le_max_right Cm _)
  have hC0 : (0:ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hCB : B ≤ C := le_trans (le_max_left B 1) (le_max_right Cm _)
  have hCCm : Cm ≤ C := le_max_left _ _
  refine ⟨C, hC0, ?_⟩
  intro r s hr hrs f hf
  have hsr : C ≤ s - r := by linarith
  have hsr0 : (0:ℝ) < s - r := lt_of_lt_of_le hC0 hsr
  set ρ : ℝ := r + D * (L:ℝ) with hρdef
  set τ : ℝ := ρ + (s - r)/2 with hτdef
  have hL0 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  have hρ0 : (0:ℝ) ≤ ρ := by rw [hρdef]; nlinarith
  have hρτ : ρ < τ := by rw [hτdef]; linarith
  have hmargin : 2*D*((L:ℝ)+2) ≤ s - r := by
    have : Cm ≤ s - r := le_trans hCCm hsr
    rw [hCmdef] at this
    linarith
  have hτs : τ + 2*D ≤ s := by
    rw [hτdef, hρdef]
    nlinarith
  have hgapval : τ - ρ = (s - r)/2 := by rw [hτdef]; ring
  -- the chain stays in the inner square
  have hzmem : ∀ x ∈ P.square r, ∀ i, zz x i ∈ P.square ρ := by
    intro x hx i
    have hxn : ‖P.pos x‖ ≤ r := (mem_square_iff_norm P hr.le x).mp hx
    rw [mem_square_iff_norm P hρ0]
    calc ‖P.pos (zz x i)‖ = ‖P.pos x + (P.pos (zz x i) - P.pos x)‖ := by ring_nf
      _ ≤ ‖P.pos x‖ + ‖P.pos (zz x i) - P.pos x‖ := norm_add_le _ _
      _ ≤ r + D * (L:ℝ) := add_le_add hxn (hzpos x i)
  set H : V → ℝ := fun z => ∑ w ∈ P.graph.neighborFinset z, (f z - f w) ^ 2 with hHdef
  have hH0 : ∀ z, 0 ≤ H z := fun z => Finset.sum_nonneg fun w _ => sq_nonneg _
  -- the fibrewise injection
  have hfib : ∀ v ∈ P.representatives, ∀ i : ℕ,
      ∑ x ∈ (P.square r).filter (fun x => (ch x).1 = v), H (zz x i) ≤ ∑ z ∈ P.square ρ, H z := by
    intro v _ i
    have hinj : ∀ x ∈ (P.square r).filter (fun x => (ch x).1 = v),
        ∀ y ∈ (P.square r).filter (fun x => (ch x).1 = v), zz x i = zz y i → x = y := by
      intro x hx y hy hxy
      rw [Finset.mem_filter] at hx hy
      have hvx : (ch x).1 = v := hx.2
      have hvy : (ch y).1 = v := hy.2
      have hb : (ch x).2 = (ch y).2 := by
        have hxy2 := hxy
        simp only [hzzdef] at hxy2
        rw [hvx, hvy] at hxy2
        exact shift_site_injective P ((Q v).getVert i) hxy2
      calc x = P.shift (ch x).2 (ch x).1 := (hch x).2.symm
        _ = P.shift (ch y).2 (ch y).1 := by rw [hb, hvx, hvy]
        _ = y := (hch y).2
    rw [← Finset.sum_image hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => hH0 z)
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hzmem x (Finset.mem_filter.mp hx).1 i
  have hper : ∀ i : ℕ, ∑ x ∈ P.square r, H (zz x i) ≤ Rc * ∑ z ∈ P.square ρ, H z := by
    intro i
    have hmaps : ∀ x ∈ P.square r, (ch x).1 ∈ P.representatives := fun x _ => (hch x).1
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => H (zz x i))]
    calc ∑ v ∈ P.representatives, ∑ x ∈ (P.square r).filter (fun x => (ch x).1 = v), H (zz x i)
        ≤ ∑ _v ∈ P.representatives, ∑ z ∈ P.square ρ, H z :=
          Finset.sum_le_sum (fun v hv => hfib v hv i)
      _ = Rc * ∑ z ∈ P.square ρ, H z := by rw [Finset.sum_const, nsmul_eq_mul, hRcdef]
  -- the chain bound, summed
  have hE0 : (0:ℝ) ≤ ∑ z ∈ P.square ρ, H z := Finset.sum_nonneg fun z _ => hH0 z
  have hchain : ∑ x ∈ P.square r, P.diff a f x ^ 2
      ≤ (L:ℝ) * ((L:ℝ) * (Rc * ∑ z ∈ P.square ρ, H z)) := by
    have h1 : ∑ x ∈ P.square r, P.diff a f x ^ 2
        ≤ ∑ x ∈ P.square r, (L:ℝ) * ∑ i ∈ Finset.range L, H (zz x i) :=
      Finset.sum_le_sum (fun x _ =>
        diff_sq_le_chain P f x a L (zz x) (hz0 x) (hzL x) (hzstep x))
    have h2 : ∑ x ∈ P.square r, (L:ℝ) * ∑ i ∈ Finset.range L, H (zz x i)
        = (L:ℝ) * ∑ i ∈ Finset.range L, ∑ x ∈ P.square r, H (zz x i) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    have h3 : ∑ i ∈ Finset.range L, ∑ x ∈ P.square r, H (zz x i)
        ≤ ∑ _i ∈ Finset.range L, Rc * ∑ z ∈ P.square ρ, H z :=
      Finset.sum_le_sum (fun i _ => hper i)
    have h4 : ∑ _i ∈ Finset.range L, Rc * ∑ z ∈ P.square ρ, H z
        = (L:ℝ) * (Rc * ∑ z ∈ P.square ρ, H z) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h2] at h1
    refine le_trans h1 ?_
    have := mul_le_mul_of_nonneg_left (le_trans h3 (le_of_eq h4)) hL0
    exact this
  -- the energy bound
  have henergy := energy_le P hc hκ0 hK0.le hD0 hcb hD hΔ hρ0 hρτ hτs f hf
  rw [hgapval] at henergy
  have hfs0 : (0:ℝ) ≤ ∑ x ∈ P.square s, f x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hDgap : (D / ((s - r)/2)) ^ 2 = 4 * D^2 / (s - r)^2 := by
    field_simp
    ring
  rw [hDgap] at henergy
  -- assemble
  have hstep1 : ∑ x ∈ P.square r, P.diff a f x ^ 2
      ≤ (L:ℝ)^2 * Rc * ((8 * K * (Δ:ℝ) / κ) * (4 * D^2 / (s - r)^2)
          * ∑ x ∈ P.square s, f x ^ 2) := by
    have hcoef : (0:ℝ) ≤ (L:ℝ)^2 * Rc := by positivity
    have h := mul_le_mul_of_nonneg_left henergy hcoef
    calc ∑ x ∈ P.square r, P.diff a f x ^ 2
        ≤ (L:ℝ) * ((L:ℝ) * (Rc * ∑ z ∈ P.square ρ, H z)) := hchain
      _ = (L:ℝ)^2 * Rc * ∑ z ∈ P.square ρ, H z := by ring
      _ ≤ _ := h
  refine le_trans hstep1 ?_
  have hBval : (L:ℝ)^2 * Rc * ((8 * K * (Δ:ℝ) / κ) * (4 * D^2 / (s - r)^2))
      = B / (s - r)^2 := by
    rw [hBdef]
    field_simp
    ring
  have hrw2 : (L:ℝ)^2 * Rc * ((8 * K * (Δ:ℝ) / κ) * (4 * D^2 / (s - r)^2)
        * ∑ x ∈ P.square s, f x ^ 2)
      = (B / (s - r)^2) * ∑ x ∈ P.square s, f x ^ 2 := by
    rw [← hBval]; ring
  rw [hrw2, div_pow]
  refine mul_le_mul_of_nonneg_right ?_ hfs0
  have hCsq : B ≤ C^2 := by nlinarith
  exact div_le_div_of_nonneg_right hCsq (by positivity) |>.trans_eq rfl

end UCPlanar.Support
