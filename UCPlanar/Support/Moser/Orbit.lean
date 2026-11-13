/-
The discrete Sobolev bound transported to a lattice orbit of a periodic graph.
-/
import UCPlanar.Support.Moser.LatticeSobolev
import UCPlanar.Support.Poly.Word

/-!
# The Sobolev bound on a lattice orbit

For a function `f` on the vertices of a periodic graph, a vertex `x` and a box `{0, …, n}²` of
lattice translates of `x` contained in a geometric square `P.square t`, the value `|f x|` is bounded
by the `ℓ²` norms over `P.square t` of `f`, of its two forward differences along the coordinate
directions and of their mixed second difference.

The bound is the discrete Sobolev bound `UCPlanar.Support.abs_le_box_sobolev` applied to
`G i j = f (P.shift ![i, j] x)`. The map `(i, j) ↦ P.shift ![i, j] x` is injective, so the sums of
squares over the box are at most the sums of squares over the square.

## Main results

* `UCPlanar.Support.abs_le_orbit_sobolev`: the bound on `|f x|`.
-/

open Finset

namespace UCPlanar.Support

/-- Distinct pairs of integers give distinct points of a lattice orbit. -/
private theorem shift_orbit_injective {V : Type*} (P : UCPlanar.PeriodicGraph V) (x : V) :
    Function.Injective fun p : ℕ × ℕ => P.shift ![(p.1 : ℤ), (p.2 : ℤ)] x := by
  intro p q h
  have hpos := congrArg P.pos h
  rw [P.pos_shift, P.pos_shift] at hpos
  have h2 := P.period.injective (add_left_cancel hpos)
  have h0 := congrFun h2 0
  have h1 := congrFun h2 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_natCast, Nat.cast_inj] at h0 h1
  exact Prod.ext h0 h1

/-- A sum of squares over a box of lattice translates is at most the sum over a square containing
the box. -/
private theorem sum_orbit_sq_le {V : Type*} (P : UCPlanar.PeriodicGraph V) (x : V) (n : ℕ) (t : ℝ)
    (hbox : ∀ i ≤ n, ∀ j ≤ n, P.shift ![(i : ℤ), (j : ℤ)] x ∈ P.square t) (h : V → ℝ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), h (P.shift ![(i : ℤ), (j : ℤ)] x) ^ 2
      ≤ ∑ y ∈ P.square t, h y ^ 2 := by
  classical
  rw [← Finset.sum_product' (f := fun (i j : ℕ) => h (P.shift ![(i : ℤ), (j : ℤ)] x) ^ 2),
    ← Finset.sum_image (f := fun y => h y ^ 2)
      (g := fun p : ℕ × ℕ => P.shift ![(p.1 : ℤ), (p.2 : ℤ)] x)
      ((shift_orbit_injective P x).injOn)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
  intro y hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hy
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  exact hbox p.1 (by omega) p.2 (by omega)

/-- The value of `f` at `x` is controlled by the `ℓ²` norms over a geometric square `P.square t`
of `f`, of its forward differences along the two coordinate directions and of their mixed second
difference, provided the box `{0, …, n}²` of lattice translates of `x` lies in the square. -/
theorem abs_le_orbit_sobolev {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (x : V) (n : ℕ) (t : ℝ)
    (hbox : ∀ i ≤ n, ∀ j ≤ n, P.shift ![(i : ℤ), (j : ℤ)] x ∈ P.square t) :
    |f x| ≤ (1 / ((n : ℝ) + 1)) * Real.sqrt (∑ y ∈ P.square t, f y ^ 2)
      + Real.sqrt (∑ y ∈ P.square t, P.diff ![1, 0] f y ^ 2)
      + Real.sqrt (∑ y ∈ P.square t, P.diff ![0, 1] f y ^ 2)
      + ((n : ℝ) + 1) *
          Real.sqrt (∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2) := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℝ, ∀ i j, G i j = f (P.shift ![(i : ℤ), (j : ℤ)] x) :=
    ⟨fun i j => f (P.shift ![(i : ℤ), (j : ℤ)] x), fun _ _ => rfl⟩
  have e1 : ∀ i j : ℕ, P.shift ![1, 0] (P.shift ![(i : ℤ), (j : ℤ)] x)
      = P.shift ![((i + 1 : ℕ) : ℤ), (j : ℤ)] x := by
    intro i j
    rw [← P.shift_add]
    congr 1
    ext k
    fin_cases k <;> simp [add_comm]
  have e2 : ∀ i j : ℕ, P.shift ![0, 1] (P.shift ![(i : ℤ), (j : ℤ)] x)
      = P.shift ![(i : ℤ), ((j + 1 : ℕ) : ℤ)] x := by
    intro i j
    rw [← P.shift_add]
    congr 1
    ext k
    fin_cases k <;> simp [add_comm]
  have h00 : G 0 0 = f x := by
    have h0 : (![((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ)] : LatticeProb.Site 2) = 0 := by
      ext k
      fin_cases k <;> simp
    rw [hG, h0, P.shift_zero]
  have hD1 : ∀ i j, G (i + 1) j - G i j = P.diff ![1, 0] f (P.shift ![(i : ℤ), (j : ℤ)] x) := by
    intro i j
    simp only [hG, UCPlanar.PeriodicGraph.diff, e1]
  have hD2 : ∀ i j, G i (j + 1) - G i j = P.diff ![0, 1] f (P.shift ![(i : ℤ), (j : ℤ)] x) := by
    intro i j
    simp only [hG, UCPlanar.PeriodicGraph.diff, e2]
  have hD12 : ∀ i j, G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j
      = P.diffWord [![1, 0], ![0, 1]] f (P.shift ![(i : ℤ), (j : ℤ)] x) := by
    intro i j
    simp only [hG, UCPlanar.PeriodicGraph.diffWord, List.foldr_cons, List.foldr_nil,
      UCPlanar.PeriodicGraph.diff, e1, e2]
    ring
  have key := abs_le_box_sobolev G n
  have s0 : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), G i j ^ 2
      ≤ ∑ y ∈ P.square t, f y ^ 2 := by
    simp only [hG]
    exact sum_orbit_sq_le P x n t hbox f
  have s1 : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (G (i + 1) j - G i j) ^ 2
      ≤ ∑ y ∈ P.square t, P.diff ![1, 0] f y ^ 2 := by
    simp only [hD1]
    exact sum_orbit_sq_le P x n t hbox (P.diff ![1, 0] f)
  have s2 : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (G i (j + 1) - G i j) ^ 2
      ≤ ∑ y ∈ P.square t, P.diff ![0, 1] f y ^ 2 := by
    simp only [hD2]
    exact sum_orbit_sq_le P x n t hbox (P.diff ![0, 1] f)
  have s12 : ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
      (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j) ^ 2
      ≤ ∑ y ∈ P.square t, P.diffWord [![1, 0], ![0, 1]] f y ^ 2 := by
    simp only [hD12]
    exact sum_orbit_sq_le P x n t hbox (P.diffWord [![1, 0], ![0, 1]] f)
  rw [← h00]
  refine key.trans ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hn' : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt s0) hn') (Real.sqrt_le_sqrt s1))
    (Real.sqrt_le_sqrt s2)) (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt s12) hn)

end UCPlanar.Support
