/-
A discrete Sobolev bound on a box of `ℕ × ℕ`.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt

/-!
# A discrete Sobolev bound on a box

This file proves the lattice analogue of the embedding `H²(ℝ²) ⊆ L^∞`: the value of a function
`G : ℕ → ℕ → ℝ` at the corner `(0, 0)` of the box `{0, …, n}²` is controlled by the `ℓ²` norms on the
box of `G`, of its two first differences and of its mixed second difference.

The argument uses, for every point `(a₁, a₂)` of the box, the identity
`G 0 0 = G a₁ a₂ - ∑_{j < a₂} D₂G a₁ j - ∑_{i < a₁} D₁G i a₂ + ∑_{i < a₁} ∑_{j < a₂} D₁D₂G i j`.
Averaging over the `(n + 1)²` points of the box and applying the Cauchy-Schwarz inequality gives the
bound.

## Main results

* `UCPlanar.Support.abs_le_box_sobolev`: the bound on `|G 0 0|`.
-/

open Finset

namespace UCPlanar.Support

/-- The telescoping identity on a box with corners `(0, 0)` and `(a₁, a₂)`. -/
private theorem corner_eq (G : ℕ → ℕ → ℝ) (a₁ a₂ : ℕ) :
    G 0 0 = G a₁ a₂ - ∑ j ∈ range a₂, (G a₁ (j + 1) - G a₁ j)
      - ∑ i ∈ range a₁, (G (i + 1) a₂ - G i a₂)
      + ∑ i ∈ range a₁, ∑ j ∈ range a₂,
          (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j) := by
  have hinner : ∀ i, ∑ j ∈ range a₂, (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j)
      = (G (i + 1) a₂ - G i a₂) - (G (i + 1) 0 - G i 0) := by
    intro i
    have h := Finset.sum_range_sub (fun j => G (i + 1) j - G i j) a₂
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by ring
  have houter : ∑ i ∈ range a₁, ((G (i + 1) a₂ - G i a₂) - (G (i + 1) 0 - G i 0))
      = (G a₁ a₂ - G 0 a₂) - (G a₁ 0 - G 0 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => G i a₂),
      Finset.sum_range_sub (fun i => G i 0)]
  have h1 := Finset.sum_range_sub (fun j => G a₁ j) a₂
  have h2 := Finset.sum_range_sub (fun i => G i a₂) a₁
  rw [Finset.sum_congr rfl fun i _ => hinner i, houter, h1, h2]
  ring

/-- The Cauchy-Schwarz inequality for a sum of absolute values over a square box. -/
private theorem sum_abs_le_mul_sqrt (N : ℕ) (h : ℕ → ℕ → ℝ) :
    ∑ i ∈ range N, ∑ j ∈ range N, |h i j| ≤
      (N : ℝ) * Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N, h i j ^ 2) := by
  rw [← Finset.sum_product' (f := fun i j => |h i j|),
    ← Finset.sum_product' (f := fun i j => h i j ^ 2)]
  set S := ∑ p ∈ range N ×ˢ range N, h p.1 p.2 ^ 2 with hS
  set T := ∑ p ∈ range N ×ˢ range N, |h p.1 p.2| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hcs := sq_sum_le_card_mul_sum_sq (s := range N ×ˢ range N)
    (f := fun p : ℕ × ℕ => |h p.1 p.2|)
  simp only [sq_abs, Finset.card_product, Finset.card_range, Nat.cast_mul] at hcs
  calc T = Real.sqrt (T ^ 2) := (Real.sqrt_sq hT0).symm
    _ ≤ Real.sqrt (((N : ℝ) * N) * S) := Real.sqrt_le_sqrt hcs
    _ = (N : ℝ) * Real.sqrt S := by
      rw [Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self (Nat.cast_nonneg _)]

/-- The value of `G` at the corner of the box `{0, …, n}²` is controlled by the `ℓ²` norms on the box
of `G`, its two first differences and its mixed second difference. -/
theorem abs_le_box_sobolev (G : ℕ → ℕ → ℝ) (n : ℕ) :
    |G 0 0| ≤ (1 / ((n : ℝ) + 1)) *
        Real.sqrt (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), G i j ^ 2)
      + Real.sqrt (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (G (i + 1) j - G i j) ^ 2)
      + Real.sqrt (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (G i (j + 1) - G i j) ^ 2)
      + ((n : ℝ) + 1) * Real.sqrt (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j) ^ 2) := by
  set N := n + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hNr : ((n : ℝ) + 1) = (N : ℝ) := by simp [hN]
  rw [hNr]
  -- the absolute values of the box sums of the differences
  set R₂ : ℕ → ℝ := fun a₁ => ∑ j ∈ range N, |G a₁ (j + 1) - G a₁ j| with hR₂
  set R₁ : ℕ → ℝ := fun a₂ => ∑ i ∈ range N, |G (i + 1) a₂ - G i a₂| with hR₁
  set Q : ℝ := ∑ i ∈ range N, ∑ j ∈ range N,
    |G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j| with hQ
  -- the pointwise bound at each point of the box
  have hpt : ∀ a₁ ∈ range N, ∀ a₂ ∈ range N, |G 0 0| ≤ |G a₁ a₂| + R₂ a₁ + R₁ a₂ + Q := by
    intro a₁ ha₁ a₂ ha₂
    have ha₁' : a₁ ≤ N := (Finset.mem_range.1 ha₁).le
    have ha₂' : a₂ ≤ N := (Finset.mem_range.1 ha₂).le
    have h2 : |∑ j ∈ range a₂, (G a₁ (j + 1) - G a₁ j)| ≤ R₂ a₁ :=
      (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha₂')
          fun _ _ _ => abs_nonneg _
    have h1 : |∑ i ∈ range a₁, (G (i + 1) a₂ - G i a₂)| ≤ R₁ a₂ :=
      (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha₁')
          fun _ _ _ => abs_nonneg _
    have h12 : |∑ i ∈ range a₁, ∑ j ∈ range a₂,
        (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j)| ≤ Q := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ range a₁, |∑ j ∈ range a₂,
              (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j)|
          ≤ ∑ i ∈ range a₁, ∑ j ∈ range N,
              |G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j| := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact (Finset.abs_sum_le_sum_abs _ _).trans <|
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha₂')
                fun _ _ _ => abs_nonneg _
        _ ≤ Q := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ha₁')
              fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hc := corner_eq G a₁ a₂
    calc |G 0 0| = |G a₁ a₂ - ∑ j ∈ range a₂, (G a₁ (j + 1) - G a₁ j)
          - ∑ i ∈ range a₁, (G (i + 1) a₂ - G i a₂)
          + ∑ i ∈ range a₁, ∑ j ∈ range a₂,
              (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j)| := by rw [← hc]
      _ ≤ |G a₁ a₂| + |∑ j ∈ range a₂, (G a₁ (j + 1) - G a₁ j)|
          + |∑ i ∈ range a₁, (G (i + 1) a₂ - G i a₂)|
          + |∑ i ∈ range a₁, ∑ j ∈ range a₂,
              (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j)| := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ?_ le_rfl
        refine (abs_sub _ _).trans ?_
        refine add_le_add ?_ le_rfl
        exact abs_sub _ _
      _ ≤ |G a₁ a₂| + R₂ a₁ + R₁ a₂ + Q := by gcongr
  -- sum the pointwise bound over the box
  have hsum : (N : ℝ) * N * |G 0 0| ≤ ∑ a₁ ∈ range N, ∑ a₂ ∈ range N, |G a₁ a₂|
      + N * ∑ a₁ ∈ range N, R₂ a₁ + N * ∑ a₂ ∈ range N, R₁ a₂ + (N : ℝ) * N * Q := by
    calc (N : ℝ) * N * |G 0 0|
        = ∑ a₁ ∈ range N, ∑ a₂ ∈ range N, |G 0 0| := by
          simp [Finset.sum_const, Finset.card_range, mul_assoc]
      _ ≤ ∑ a₁ ∈ range N, ∑ a₂ ∈ range N, (|G a₁ a₂| + R₂ a₁ + R₁ a₂ + Q) :=
          Finset.sum_le_sum fun a₁ ha₁ => Finset.sum_le_sum fun a₂ ha₂ => hpt a₁ ha₁ a₂ ha₂
      _ = ∑ a₁ ∈ range N, ∑ a₂ ∈ range N, |G a₁ a₂|
          + N * ∑ a₁ ∈ range N, R₂ a₁ + N * ∑ a₂ ∈ range N, R₁ a₂ + (N : ℝ) * N * Q := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
  -- Cauchy-Schwarz for each of the four box sums
  have c0 := sum_abs_le_mul_sqrt N (fun i j => G i j)
  have c2 := sum_abs_le_mul_sqrt N (fun i j => G i (j + 1) - G i j)
  have c1 := sum_abs_le_mul_sqrt N (fun i j => G (i + 1) j - G i j)
  have c12 := sum_abs_le_mul_sqrt N
    (fun i j => G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j)
  have hR₂sum : ∑ a₁ ∈ range N, R₂ a₁ = ∑ i ∈ range N, ∑ j ∈ range N, |G i (j + 1) - G i j| := rfl
  have hR₁sum : ∑ a₂ ∈ range N, R₁ a₂ = ∑ i ∈ range N, ∑ j ∈ range N, |G (i + 1) j - G i j| :=
    Finset.sum_comm
  rw [hR₂sum, hR₁sum] at hsum
  have key : (N : ℝ) * N * |G 0 0| ≤ (N : ℝ) * N * ((1 / (N : ℝ)) *
        Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N, G i j ^ 2)
      + Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N, (G (i + 1) j - G i j) ^ 2)
      + Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N, (G i (j + 1) - G i j) ^ 2)
      + (N : ℝ) * Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N,
          (G (i + 1) (j + 1) - G (i + 1) j - G i (j + 1) + G i j) ^ 2)) := by
    have e0 : (N : ℝ) * N * ((1 / (N : ℝ)) *
        Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N, G i j ^ 2))
        = N * Real.sqrt (∑ i ∈ range N, ∑ j ∈ range N, G i j ^ 2) := by
      field_simp
    have m2 := mul_le_mul_of_nonneg_left c2 hNpos.le
    have m1 := mul_le_mul_of_nonneg_left c1 hNpos.le
    have m12 := mul_le_mul_of_nonneg_left c12 (mul_self_nonneg (N : ℝ))
    rw [mul_add, mul_add, mul_add, e0]
    nlinarith [hsum, c0, m2, m1, m12]
  exact le_of_mul_le_mul_left key (by positivity)

end UCPlanar.Support
