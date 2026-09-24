import UCPlanar.Support.RemezCheb

/-!
# Lagrange interpolation at compressed nodes and the Remez comparison

The algebraic heart of the Remez inequality: if the nodes `x 0 < ... < x n` at which a
degree-≤ n polynomial `q` is bounded by `1` dominate the Chebyshev equioscillation nodes
`η_k = cos((n−k)π/n)` (pointwise from above and in mutual distances from below), then the
value of `q` at any point to the right of all `x k` is bounded by `T_n` there.
-/

namespace UCPlanar.Support

open Polynomial Real Finset
open Polynomial.Chebyshev

/-- The Lagrange interpolation identity at `n + 1` distinct nodes. -/
theorem eval_eq_sum_nodal {n : ℕ} (q : ℝ[X]) (hq : q.natDegree ≤ n) (x : ℕ → ℝ)
    (hdist : ∀ j ≤ n, ∀ k ≤ n, j ≠ k → x j ≠ x k) (t : ℝ) :
    q.eval t = ∑ k ∈ range (n + 1),
      q.eval (x k) * (∏ i ∈ range (n + 1) \ {k}, (t - x i)) /
        (∏ i ∈ range (n + 1) \ {k}, (x k - x i)) := by
  classical
  set den : ℕ → ℝ := fun k ↦ ∏ i ∈ range (n + 1) \ {k}, (x k - x i) with hden
  set N : ℕ → ℝ[X] := fun k ↦ ∏ i ∈ range (n + 1) \ {k}, (X - C (x i)) with hN
  have hden_ne : ∀ k ≤ n, den k ≠ 0 := fun k hk ↦
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ by
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
      exact sub_ne_zero.mpr (hdist k hk i (by omega) (Ne.symm hi.2))
  set P : ℝ[X] := ∑ k ∈ range (n + 1), C (q.eval (x k) / den k) * N k with hP
  have hNeval : ∀ k ≤ n, ∀ y, (N k).eval y = ∏ i ∈ range (n + 1) \ {k}, (y - x i) := by
    intro k _ y
    rw [hN, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by simp
  have hPj : ∀ j ≤ n, P.eval (x j) = q.eval (x j) := by
    intro j hj
    rw [hP, Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single j]
    · rw [eval_mul, eval_C, hNeval j hj]
      exact div_mul_cancel₀ _ (hden_ne j hj)
    · intro k hk hkj
      rw [Finset.mem_range] at hk
      rw [eval_mul, eval_C, hNeval k (by omega)]
      rw [Finset.prod_eq_zero (i := j)]
      · simp
      · rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
        exact ⟨by omega, Ne.symm hkj⟩
      · simp
    · intro hcon
      exact absurd (Finset.mem_range.mpr (by omega)) hcon
  have hdeg : P.natDegree ≤ n := by
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    calc (C (q.eval (x k) / den k) * N k).natDegree
        ≤ (C (q.eval (x k) / den k)).natDegree + (N k).natDegree := Polynomial.natDegree_mul_le
      _ ≤ (N k).natDegree := by
          have hC : (C (q.eval (x k) / den k)).natDegree = 0 := Polynomial.natDegree_C _
          omega
      _ ≤ ∑ i ∈ range (n + 1) \ {k}, (X - C (x i)).natDegree := by
          simp only [hN]
          exact Polynomial.natDegree_prod_le _ _
      _ = (range (n + 1) \ {k}).card := by simp
      _ = n := by
        have hcard : (range (n + 1) \ {k}).card = (n + 1) - 1 := by
          rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr
            (Finset.mem_range.mpr (by omega))), Finset.card_range, Finset.card_singleton]
        omega
  have hsub : q - P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (q - P)
      (f := fun j : Fin (n + 1) ↦ x j) ?_ ?_ ?_
    · intro a b hab
      by_contra hne
      exact hdist a (by omega) b (by omega) (fun h ↦ hne (Fin.ext h)) hab
    · intro j
      rw [eval_sub, hPj j (by omega), sub_self]
    · calc (q - P).natDegree ≤ max q.natDegree P.natDegree := Polynomial.natDegree_sub_le _ _
        _ ≤ n := max_le hq hdeg
        _ < Fintype.card (Fin (n + 1)) := by simp
  have hqP : q = P := sub_eq_zero.mp hsub
  calc q.eval t = P.eval t := by rw [hqP]
    _ = ∑ k ∈ range (n + 1), q.eval (x k) / den k * (N k).eval t := by
        rw [hP, Polynomial.eval_finsetSum]
        exact Finset.sum_congr rfl fun k _ ↦ by rw [eval_mul, eval_C]
    _ = ∑ k ∈ range (n + 1),
          q.eval (x k) * (∏ i ∈ range (n + 1) \ {k}, (t - x i)) / den k := by
        exact Finset.sum_congr rfl fun k hk ↦ by
          rw [Finset.mem_range] at hk
          rw [hNeval k (by omega)]; exact div_mul_eq_mul_div _ _ _

/-- The sign of the Chebyshev nodal denominator: there are exactly `n − k` negative
factors `η_k − η_i` (those with `i > k`). -/
theorem prod_chebNode_sub_eq {n : ℕ} (hn : n ≠ 0) {k : ℕ} (hk : k ≤ n) :
    ∏ i ∈ range (n + 1) \ {k}, (chebNode n k - chebNode n i)
      = (-1) ^ (n - k) * ∏ i ∈ range (n + 1) \ {k}, |chebNode n k - chebNode n i| := by
  have hsplit : range (n + 1) \ {k} = range k ∪ Ico (k + 1) (n + 1) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_union,
      Finset.mem_Ico]
    omega
  have hdisj : Disjoint (range k) (Ico (k + 1) (n + 1)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_range] at hi1
    simp only [Finset.mem_Ico] at hi2
    omega
  rw [hsplit, Finset.prod_union hdisj, Finset.prod_union hdisj]
  have hleft : ∏ i ∈ range k, (chebNode n k - chebNode n i)
      = ∏ i ∈ range k, |chebNode n k - chebNode n i| :=
    Finset.prod_congr rfl fun i hi ↦ by
      rw [Finset.mem_range] at hi
      exact (abs_of_pos (sub_pos.mpr (chebNode_lt_chebNode hn hk hi))).symm
  have hright : ∏ i ∈ Ico (k + 1) (n + 1), (chebNode n k - chebNode n i)
      = (-1) ^ (n - k) * ∏ i ∈ Ico (k + 1) (n + 1), |chebNode n k - chebNode n i| := by
    have h1 : ∀ i ∈ Ico (k + 1) (n + 1),
        chebNode n k - chebNode n i = -(chebNode n i - chebNode n k) := fun i _ ↦ by ring
    rw [Finset.prod_congr rfl h1, Finset.prod_neg]
    have hcard : (Ico (k + 1) (n + 1)).card = n - k := by rw [Nat.card_Ico]; omega
    rw [hcard]
    congr 1
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [Finset.mem_Ico] at hi
      have hlt : chebNode n k < chebNode n i := chebNode_lt_chebNode hn (by omega) (by omega)
      rw [abs_of_neg (sub_neg.mpr hlt)]
      ring
  rw [hleft, hright]
  ring

/-- The value of `T_n` as a sum of nonnegative terms at any point: Lagrange interpolation
at the equioscillation nodes, with the signs resolved. -/
theorem eval_chebT_eq_sum {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    (T ℝ (n : ℤ)).eval y = ∑ k ∈ range (n + 1),
      (∏ i ∈ range (n + 1) \ {k}, (y - chebNode n i)) /
        (∏ i ∈ range (n + 1) \ {k}, |chebNode n k - chebNode n i|) := by
  have hdist : ∀ j ≤ n, ∀ k ≤ n, j ≠ k → chebNode n j ≠ chebNode n k := by
    intro j hj k hk hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact ne_of_lt (chebNode_lt_chebNode hn hk h)
    · exact ne_of_gt (chebNode_lt_chebNode hn hj h)
  have hnat : (T ℝ (n : ℤ)).natDegree ≤ n := by rw [natDegree_T, Int.natAbs_natCast]
  rw [eval_eq_sum_nodal (T ℝ (n : ℤ)) hnat (chebNode n) hdist y]
  exact Finset.sum_congr rfl fun k hk ↦ by
    rw [Finset.mem_range] at hk
    have hk' : k ≤ n := by omega
    rw [eval_chebT_chebNode hn hk', prod_chebNode_sub_eq hn hk']
    exact mul_div_mul_left _ _ (by simp)

/-- The Remez comparison at a point: a degree-≤ n polynomial bounded by `1` at nodes
`x k` that dominate the Chebyshev nodes is bounded by `T_n` to the right of all nodes. -/
theorem abs_eval_le_chebT_eval {n : ℕ} (hn : n ≠ 0) (q : ℝ[X]) (hq : q.natDegree ≤ n)
    (s : ℝ) (x : ℕ → ℝ)
    (hdist : ∀ j ≤ n, ∀ k ≤ n, j ≠ k → x j ≠ x k)
    (hxb : ∀ k ≤ n, |q.eval (x k)| ≤ 1)
    (hxub : ∀ k ≤ n, x k ≤ 1 + s)
    (hlb : ∀ k ≤ n, chebNode n k ≤ x k)
    (hcomp : ∀ j ≤ n, ∀ k ≤ n, |chebNode n j - chebNode n k| ≤ |x j - x k|) :
    |q.eval (1 + s)| ≤ (T ℝ (n : ℤ)).eval (1 + s) := by
  have hxnum : ∀ k ≤ n, ∀ i ∈ range (n + 1) \ {k}, 0 ≤ 1 + s - x i := by
    intro k _ i hi
    rw [Finset.mem_sdiff, Finset.mem_range] at hi
    exact sub_nonneg.mpr (hxub i (by omega))
  have hηpos : ∀ k ≤ n, 0 < ∏ i ∈ range (n + 1) \ {k}, |chebNode n k - chebNode n i| := by
    intro k hk
    exact Finset.prod_pos fun i hi ↦ by
      rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
      rcases lt_or_gt_of_ne hi.2 with h | h
      · exact abs_pos.mpr (sub_pos.mpr (chebNode_lt_chebNode hn hk h)).ne'
      · exact abs_pos.mpr (sub_neg.mpr (chebNode_lt_chebNode hn (by omega) h)).ne
  rw [eval_eq_sum_nodal q hq x hdist (1 + s), eval_chebT_eq_sum hn (1 + s)]
  calc |∑ k ∈ range (n + 1),
        q.eval (x k) * (∏ i ∈ range (n + 1) \ {k}, (1 + s - x i)) /
          (∏ i ∈ range (n + 1) \ {k}, (x k - x i))|
      ≤ ∑ k ∈ range (n + 1),
        |q.eval (x k)| * ((∏ i ∈ range (n + 1) \ {k}, (1 + s - x i)) /
          (∏ i ∈ range (n + 1) \ {k}, |x k - x i|)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk ↦ ?_)
        rw [Finset.mem_range] at hk
        have hk' : k ≤ n := by omega
        rw [abs_div, abs_mul, abs_of_nonneg (Finset.prod_nonneg (hxnum k hk')),
          Finset.abs_prod, mul_div_assoc]
    _ ≤ ∑ k ∈ range (n + 1),
        (∏ i ∈ range (n + 1) \ {k}, (1 + s - x i)) /
          (∏ i ∈ range (n + 1) \ {k}, |x k - x i|) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [Finset.mem_range] at hk
        have hk' : k ≤ n := by omega
        have hnonneg : 0 ≤ (∏ i ∈ range (n + 1) \ {k}, (1 + s - x i)) /
            (∏ i ∈ range (n + 1) \ {k}, |x k - x i|) :=
          div_nonneg (Finset.prod_nonneg (hxnum k hk'))
            (Finset.prod_nonneg fun i _ ↦ abs_nonneg _)
        exact mul_le_of_le_one_left hnonneg (hxb k (by omega))
    _ ≤ ∑ k ∈ range (n + 1),
        (∏ i ∈ range (n + 1) \ {k}, (1 + s - chebNode n i)) /
          (∏ i ∈ range (n + 1) \ {k}, |chebNode n k - chebNode n i|) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [Finset.mem_range] at hk
        have hk' : k ≤ n := by omega
        refine div_le_div₀ ?_ ?_ (hηpos k hk') ?_
        · exact Finset.prod_nonneg fun i hi ↦ by
            rw [Finset.mem_sdiff, Finset.mem_range] at hi
            exact sub_nonneg.mpr ((hlb i (by omega)).trans (hxub i (by omega)))
        · exact Finset.prod_le_prod (hxnum k hk') fun i hi ↦ by
            rw [Finset.mem_sdiff, Finset.mem_range] at hi
            exact sub_le_sub_left (hlb i (by omega)) _
        · exact Finset.prod_le_prod (fun i hi ↦ abs_nonneg _) fun i hi ↦ by
            rw [Finset.mem_sdiff, Finset.mem_range] at hi
            exact hcomp k hk' i (by omega)

end UCPlanar.Support
