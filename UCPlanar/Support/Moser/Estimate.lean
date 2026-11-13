/-
The discrete Moser estimate on a periodic graph with a periodic conductance, derived from a
Sobolev bound along lattice orbits and the iterated discrete Caccioppoli inequality.
-/
import UCPlanar.External.MoserEstimate
import UCPlanar.Support.Poly.CaccioppoliLattice
import UCPlanar.Support.Poly.Word
import UCPlanar.Support.Moser.Orbit

/-!
# The discrete Moser estimate from an orbit Sobolev bound

For a function `f` on a periodic graph and a vertex `x` whose lattice orbit
`{P.shift ![i, j] x : i, j ≤ n}` lies in the square `Q_t`, an orbit Sobolev bound controls
`|f x|` by the `ℓ²` norms over `Q_t` of `f`, of its two first differences and of its mixed
second difference, with the weights `1 / (n + 1)`, `1`, `1` and `n + 1`.

This file shows that such a bound implies `UCPlanar.External.MoserEstimate`, and, with the orbit
Sobolev bound `UCPlanar.Support.abs_le_orbit_sobolev`, that the Moser estimate holds. For a function
harmonic on `Q_s` and `x ∈ Q_r`, with `ρ = s - r`, the orbit of side `n = ⌊ρ / (8K)⌋` lies in
`Q_{r + ρ/4}`, the iterated Caccioppoli inequality bounds the first differences by `4K / ρ` and
the mixed difference by `(4K / ρ)²` in `ℓ²`, and the four terms add up to `20K / ρ` times the
`ℓ²` norm of `f` on `Q_s`. When `ρ < 8K` the trivial bound `|f x| ≤ ‖f‖_{ℓ²(Q_s)}` suffices.

## Main results

* `UCPlanar.Support.moserEstimate_of_orbit`: an orbit Sobolev bound implies the Moser
  estimate.
* `UCPlanar.Support.moserEstimate_holds`: the Moser estimate holds for every periodic graph and
  every conductance.
-/

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- The two unit lattice vectors. -/
private abbrev unitWord : List (LatticeProb.Site 2) := [![1, 0], ![0, 1]]

/-- A Caccioppoli inequality with constant `C` also holds with any larger constant. -/
private theorem caccioppoli_mono {V : Type*} (P : UCPlanar.PeriodicGraph V) {c : V → V → ℝ}
    (a : LatticeProb.Site 2) {C K : ℝ} (hC : 0 < C) (hCK : C ≤ K)
    (hcac : ∀ r s : ℝ, 0 < r → r + C ≤ s → ∀ f : V → ℝ,
      (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) →
      ∑ x ∈ P.square r, P.diff a f x ^ 2 ≤ (C / (s - r)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2) :
    ∀ r s : ℝ, 0 < r → r + K ≤ s → ∀ f : V → ℝ,
      (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) →
      ∑ x ∈ P.square r, P.diff a f x ^ 2 ≤ (K / (s - r)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 := by
  intro r s hr hrs f hf
  have hsr : 0 < s - r := by linarith
  refine le_trans (hcac r s hr (by linarith) f hf) ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun x _ => sq_nonneg (f x))
  have h1 : 0 ≤ C / (s - r) := div_nonneg hC.le hsr.le
  have h2 : C / (s - r) ≤ K / (s - r) := div_le_div_of_nonneg_right hCK hsr.le
  exact pow_le_pow_left₀ h1 h2 2

/-- One constant `K ≥ 1` serves both as a Caccioppoli constant and as a bound on the period
coordinates for each of the two unit lattice vectors. -/
private theorem exists_unit_constant {V : Type*} (P : UCPlanar.PeriodicGraph V)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ a ∈ unitWord,
      (∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ K) ∧
      ∀ r s : ℝ, 0 < r → r + K ≤ s → ∀ f : V → ℝ,
        (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) →
        ∑ x ∈ P.square r, P.diff a f x ^ 2 ≤ (K / (s - r)) ^ 2 * ∑ x ∈ P.square s, f x ^ 2 := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_lattice_caccioppoli P hc hp ![1, 0]
  obtain ⟨C₂, hC₂, h₂⟩ := exists_lattice_caccioppoli P hc hp ![0, 1]
  set M : ℝ := ∑ a ∈ ({![1, 0], ![0, 1]} : Finset (LatticeProb.Site 2)),
    ∑ i : Fin 2, |P.period (fun j => (a j : ℝ)) i| with hM
  have hcoord : ∀ a ∈ unitWord, ∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ M := by
    intro a ha i
    have ha' : a ∈ ({![1, 0], ![0, 1]} : Finset (LatticeProb.Site 2)) := by
      simpa [unitWord] using ha
    calc |P.period (fun j => (a j : ℝ)) i|
        ≤ ∑ i : Fin 2, |P.period (fun j => (a j : ℝ)) i| :=
          Finset.single_le_sum (f := fun i => |P.period (fun j => (a j : ℝ)) i|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ M :=
          Finset.single_le_sum (f := fun a : LatticeProb.Site 2 =>
              ∑ i : Fin 2, |P.period (fun j => (a j : ℝ)) i|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) ha'
  refine ⟨max (max C₁ C₂) (max M 1), le_trans (le_max_right M 1) (le_max_right _ _), ?_⟩
  intro a ha
  refine ⟨fun i => le_trans (hcoord a ha i) (le_trans (le_max_left M 1) (le_max_right _ _)), ?_⟩
  simp only [unitWord, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact caccioppoli_mono P _ hC₁
      (le_trans (le_max_left C₁ C₂) (le_max_left _ _)) h₁
  · exact caccioppoli_mono P _ hC₂
      (le_trans (le_max_right C₁ C₂) (le_max_left _ _)) h₂

/-- If `X ≤ c² S` with `c ≥ 0`, then `√X ≤ c √S`. -/
private theorem sqrt_le_mul_sqrt {X S c : ℝ} (hc : 0 ≤ c) (h : X ≤ c ^ 2 * S) :
    Real.sqrt X ≤ c * Real.sqrt S := by
  calc Real.sqrt X ≤ Real.sqrt (c ^ 2 * S) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt S := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The orbit `{P.shift ![i, j] x : i, j ≤ n}` of a vertex `x ∈ Q_r` lies in `Q_{r + 2nK}`
when `K` bounds the period coordinates of the two unit lattice vectors. -/
private theorem orbit_mem_square {V : Type*} (P : UCPlanar.PeriodicGraph V) (K : ℝ)
    (hK : ∀ a ∈ unitWord, ∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ K)
    (r : ℝ) (x : V) (hx : x ∈ P.square r) (n : ℕ) :
    ∀ i ≤ n, ∀ j ≤ n,
      P.shift ![(i : ℤ), (j : ℤ)] x ∈ P.square (r + 2 * (n : ℝ) * K) := by
  intro i hi j hj
  have hK1 := hK ![1, 0] (by simp [unitWord])
  have hK2 := hK ![0, 1] (by simp [unitWord])
  have hvec : (fun k => ((![(i : ℤ), (j : ℤ)] : LatticeProb.Site 2) k : ℝ))
      = (i : ℝ) • (fun k => ((![1, 0] : LatticeProb.Site 2) k : ℝ))
        + (j : ℝ) • (fun k => ((![0, 1] : LatticeProb.Site 2) k : ℝ)) := by
    funext k
    fin_cases k <;> simp
  have hin : (i : ℝ) ≤ n := by exact_mod_cast hi
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK1 0)
  refine shift_mem_square P _ (2 * (n : ℝ) * K) (fun k => ?_) r x hx
  rw [hvec, map_add, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |(i : ℝ) * P.period (fun k => ((![1, 0] : LatticeProb.Site 2) k : ℝ)) k
        + (j : ℝ) * P.period (fun k => ((![0, 1] : LatticeProb.Site 2) k : ℝ)) k|
      ≤ |(i : ℝ) * P.period (fun k => ((![1, 0] : LatticeProb.Site 2) k : ℝ)) k|
        + |(j : ℝ) * P.period (fun k => ((![0, 1] : LatticeProb.Site 2) k : ℝ)) k| :=
        abs_add_le _ _
    _ = (i : ℝ) * |P.period (fun k => ((![1, 0] : LatticeProb.Site 2) k : ℝ)) k|
        + (j : ℝ) * |P.period (fun k => ((![0, 1] : LatticeProb.Site 2) k : ℝ)) k| := by
        rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
    _ ≤ (n : ℝ) * K + (n : ℝ) * K :=
        add_le_add (mul_le_mul hin (hK1 k) (abs_nonneg _) (Nat.cast_nonneg n))
          (mul_le_mul hjn (hK2 k) (abs_nonneg _) (Nat.cast_nonneg n))
    _ = 2 * (n : ℝ) * K := by ring

/-- **The discrete Moser estimate from an orbit Sobolev bound.** If, for every function `f`,
vertex `x`, side `n` and radius `t` such that the lattice orbit `{P.shift ![i, j] x : i, j ≤ n}`
lies in `Q_t`, the value `|f x|` is bounded by the `ℓ²` norms over `Q_t` of `f`, of its first
differences and of its mixed second difference, with the weights `1 / (n + 1)`, `1`, `1` and
`n + 1`, then the Moser estimate holds. -/
theorem moserEstimate_of_orbit {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (horbit : ∀ (f : V → ℝ) (x : V) (n : ℕ) (t : ℝ),
      (∀ i ≤ n, ∀ j ≤ n, P.shift ![(i : ℤ), (j : ℤ)] x ∈ P.square t) →
      |f x| ≤ (1 / ((n : ℝ) + 1)) * Real.sqrt (∑ y ∈ P.square t, f y ^ 2)
        + Real.sqrt (∑ y ∈ P.square t, P.diff ![1, 0] f y ^ 2)
        + Real.sqrt (∑ y ∈ P.square t, P.diff ![0, 1] f y ^ 2)
        + ((n : ℝ) + 1) *
            Real.sqrt (∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2)) :
    UCPlanar.External.MoserEstimate P c := by
  intro hc hp
  obtain ⟨K, hK1, hK⟩ := exists_unit_constant P hc hp
  have hK0 : 0 < K := by linarith
  have hcoord : ∀ a ∈ unitWord, ∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ K :=
    fun a ha => (hK a ha).1
  refine ⟨20 * K, by positivity, ?_⟩
  intro r s hr hrs f hf x hx
  set ρ : ℝ := s - r with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  set S : ℝ := ∑ y ∈ P.square s, f y ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => sq_nonneg (f y)
  have hA0 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  have hsum_mono : ∀ u, u ≤ s → ∑ y ∈ P.square u, f y ^ 2 ≤ S := fun u hu =>
    Finset.sum_le_sum_of_subset_of_nonneg (square_mono P hu) fun y _ _ => sq_nonneg (f y)
  by_cases hbig : 8 * K ≤ ρ
  · -- the orbit of side `n` lies in `Q_t`, and the Caccioppoli iteration bounds each term
    set n : ℕ := ⌊ρ / (8 * K)⌋₊ with hn
    set t : ℝ := r + ρ / 4 with ht
    have hn_le : (n : ℝ) ≤ ρ / (8 * K) := Nat.floor_le (by positivity)
    have hn_lt : ρ / (8 * K) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hnK : 8 * K * (n : ℝ) ≤ ρ := by
      rw [le_div_iff₀ (by positivity)] at hn_le; linarith
    have hnK' : ρ < 8 * K * ((n : ℝ) + 1) := by
      rw [div_lt_iff₀ (by positivity)] at hn_lt; linarith
    have hbox : ∀ i ≤ n, ∀ j ≤ n, P.shift ![(i : ℤ), (j : ℤ)] x ∈ P.square t := by
      intro i hi j hj
      refine square_mono P ?_ (orbit_mem_square P K hcoord r x hx n i hi j hj)
      linarith
    have hgap : 0 < ρ / 4 := by positivity
    have hKgap : K ≤ ρ / 4 := by linarith
    have hcac : ∀ w : List (LatticeProb.Site 2), (∀ a ∈ w, a ∈ unitWord) →
        (w.length : ℝ) ≤ 3 →
        ∑ y ∈ P.square t, P.diffWord w f y ^ 2 ≤ ((K / (ρ / 4)) ^ w.length) ^ 2 * S := by
      intro w hw hlen
      refine le_trans (diffWord_l2_iterate P c hp K K (ρ / 4) hK0 hK0.le hgap hKgap hKgap w
        (fun a ha => hcoord a (hw a ha)) (fun a ha => (hK a (hw a ha)).2) f t
        (by linarith) (fun y hy => hf y (square_mono P ?_ hy))) ?_
      · linarith [mul_le_mul_of_nonneg_right hlen hgap.le]
      · refine mul_le_mul_of_nonneg_left (hsum_mono _ ?_) (by positivity)
        linarith [mul_le_mul_of_nonneg_right hlen hgap.le]
    have hq' : K / (ρ / 4) = 4 * K / ρ := by rw [div_div_eq_mul_div]; ring
    have hq : 0 ≤ 4 * K / ρ := by positivity
    have h0 : Real.sqrt (∑ y ∈ P.square t, f y ^ 2) ≤ Real.sqrt S :=
      Real.sqrt_le_sqrt (hsum_mono t (by linarith))
    have h1 : Real.sqrt (∑ y ∈ P.square t, P.diff ![1, 0] f y ^ 2)
        ≤ 4 * K / ρ * Real.sqrt S := by
      have h : ∑ y ∈ P.square t, P.diffWord [![1, 0]] f y ^ 2 ≤ ((K / (ρ / 4)) ^ 1) ^ 2 * S :=
        hcac [![1, 0]] (by simp [unitWord]) (by norm_num)
      rw [pow_one, hq'] at h
      exact sqrt_le_mul_sqrt hq h
    have h2 : Real.sqrt (∑ y ∈ P.square t, P.diff ![0, 1] f y ^ 2)
        ≤ 4 * K / ρ * Real.sqrt S := by
      have h : ∑ y ∈ P.square t, P.diffWord [![0, 1]] f y ^ 2 ≤ ((K / (ρ / 4)) ^ 1) ^ 2 * S :=
        hcac [![0, 1]] (by simp [unitWord]) (by norm_num)
      rw [pow_one, hq'] at h
      exact sqrt_le_mul_sqrt hq h
    have h12 : Real.sqrt (∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2)
        ≤ (4 * K / ρ) ^ 2 * Real.sqrt S := by
      have h : ∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2
          ≤ ((K / (ρ / 4)) ^ 2) ^ 2 * S :=
        hcac [![1, 0], ![0, 1]] (fun a ha => ha) (by norm_num)
      rw [hq'] at h
      exact sqrt_le_mul_sqrt (by positivity) h
    have hcoef0 : 1 / ((n : ℝ) + 1) ≤ 8 * K / ρ := by
      rw [div_le_div_iff₀ (by positivity) hρ0]; linarith
    have hcoef3 : ((n : ℝ) + 1) * (4 * K / ρ) ^ 2 ≤ 4 * K / ρ := by
      have hrw : ((n : ℝ) + 1) * (4 * K / ρ) ^ 2 = 4 * K / ρ * (4 * K * ((n : ℝ) + 1) / ρ) := by
        ring
      have hle : 4 * K * ((n : ℝ) + 1) / ρ ≤ 1 := by
        rw [div_le_iff₀ hρ0]; linarith
      rw [hrw]
      calc 4 * K / ρ * (4 * K * ((n : ℝ) + 1) / ρ) ≤ 4 * K / ρ * 1 :=
            mul_le_mul_of_nonneg_left hle hq
        _ = 4 * K / ρ := mul_one _
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h3 : ((n : ℝ) + 1) *
        Real.sqrt (∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2)
        ≤ 4 * K / ρ * Real.sqrt S :=
      calc ((n : ℝ) + 1) *
            Real.sqrt (∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2)
          ≤ ((n : ℝ) + 1) * ((4 * K / ρ) ^ 2 * Real.sqrt S) :=
            mul_le_mul_of_nonneg_left h12 hn1
        _ = (((n : ℝ) + 1) * (4 * K / ρ) ^ 2) * Real.sqrt S := by ring
        _ ≤ 4 * K / ρ * Real.sqrt S := mul_le_mul_of_nonneg_right hcoef3 hA0
    have h0' : 1 / ((n : ℝ) + 1) * Real.sqrt (∑ y ∈ P.square t, f y ^ 2)
        ≤ 8 * K / ρ * Real.sqrt S :=
      mul_le_mul hcoef0 h0 (Real.sqrt_nonneg _) (by positivity)
    calc |f x| ≤ (1 / ((n : ℝ) + 1)) * Real.sqrt (∑ y ∈ P.square t, f y ^ 2)
          + Real.sqrt (∑ y ∈ P.square t, P.diff ![1, 0] f y ^ 2)
          + Real.sqrt (∑ y ∈ P.square t, P.diff ![0, 1] f y ^ 2)
          + ((n : ℝ) + 1) *
              Real.sqrt (∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2) :=
          horbit f x n t hbox
      _ ≤ 8 * K / ρ * Real.sqrt S + 4 * K / ρ * Real.sqrt S + 4 * K / ρ * Real.sqrt S
          + 4 * K / ρ * Real.sqrt S := add_le_add (add_le_add (add_le_add h0' h1) h2) h3
      _ = 20 * K / (s - r) * Real.sqrt S := by rw [← hρ]; ring
  · -- small gap: the trivial bound
    have hsmall : ρ < 8 * K := not_le.mp hbig
    have hxs : x ∈ P.square s := square_mono P hrs.le hx
    have htriv : |f x| ≤ Real.sqrt S :=
      Real.abs_le_sqrt (Finset.single_le_sum (f := fun y => f y ^ 2)
        (fun y _ => sq_nonneg (f y)) hxs)
    have hge : 1 ≤ 20 * K / (s - r) := by
      rw [← hρ, le_div_iff₀ hρ0]; linarith
    calc |f x| ≤ Real.sqrt S := htriv
      _ = 1 * Real.sqrt S := (one_mul _).symm
      _ ≤ 20 * K / (s - r) * Real.sqrt S := mul_le_mul_of_nonneg_right hge hA0

/-- **The discrete Moser estimate holds** for every periodic graph and every conductance. -/
theorem moserEstimate_holds {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ) :
    UCPlanar.External.MoserEstimate P c :=
  moserEstimate_of_orbit P c fun f x n t hbox => abs_le_orbit_sobolev P f x n t hbox

end UCPlanar.Support
