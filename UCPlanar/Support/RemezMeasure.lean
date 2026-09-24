import UCPlanar.Support.RemezLagrange
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Monotone

/-!
# The sharp Remez inequality

For a real polynomial `q` of degree at most `n` bounded by `1` on a subset of
`[-1, 1+s]` of Lebesgue measure at least `2`, the maximum of `|q|` on `[-1, 1+s]` is at
most `T_n(1+s)` (Remez's inequality, sharp form).  The proof follows Bojanov's
elementary argument: the compression `F(t) = -1 + |{|q| ≤ 1} ∩ [-1, t]|` is
`1`-Lipschitz with `F ≤ id`, so the preimages of the Chebyshev equioscillation nodes
under `F` are nodes where `|q| ≤ 1` that dominate the Chebyshev nodes, and the Lagrange
comparison of `RemezLagrange.lean` applies.
-/

open Polynomial Real Set Finset MeasureTheory
open Polynomial.Chebyshev

namespace UCPlanar.Support

/-- The admissible set: points of `Icc (-1) (1+s)` where `|q| ≤ 1`. -/
noncomputable def remezSet (q : ℝ[X]) (s : ℝ) : Set ℝ :=
  Set.Icc (-1) (1 + s) ∩ {t | |q.eval t| ≤ 1}

/-- The compression function: `F(t) = -1 + |remezSet q s ∩ Icc (-1) t|`. -/
noncomputable def remezVol (q : ℝ[X]) (s t : ℝ) : ℝ :=
  -1 + (volume (remezSet q s ∩ Set.Icc (-1) t)).toReal

theorem measurableSet_remezSet (q : ℝ[X]) (s : ℝ) : MeasurableSet (remezSet q s) :=
  MeasurableSet.inter measurableSet_Icc
    ((isClosed_Iic.preimage (q.continuous.abs)).measurableSet)

theorem isClosed_remezSet (q : ℝ[X]) (s : ℝ) : IsClosed (remezSet q s) :=
  IsClosed.inter isClosed_Icc (isClosed_Iic.preimage (q.continuous.abs))

theorem volume_remezSet_lt_top (q : ℝ[X]) (s : ℝ) : volume (remezSet q s) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

theorem volume_remezSet_inter_Icc_lt_top (q : ℝ[X]) (s t : ℝ) :
    volume (remezSet q s ∩ Set.Icc (-1) t) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono Set.inter_subset_left) ?_
  exact volume_remezSet_lt_top q s

theorem remezSet_nonempty_of_two_le (q : ℝ[X]) (s : ℝ)
    (hE : 2 ≤ (volume (remezSet q s)).toReal) : (remezSet q s).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, measure_empty, ENNReal.toReal_zero] at hE
  norm_num at hE

theorem remezVol_mono (q : ℝ[X]) (s : ℝ) : Monotone (remezVol q s) := by
  intro t u htu
  show -1 + (volume (remezSet q s ∩ Set.Icc (-1) t)).toReal
    ≤ -1 + (volume (remezSet q s ∩ Set.Icc (-1) u)).toReal
  exact add_le_add_right (ENNReal.toReal_mono (volume_remezSet_inter_Icc_lt_top q s u).ne
    (measure_mono (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc_right htu)))) _

/-- The key estimate: the compression is `1`-Lipschitz. -/
theorem remezVol_lipschitz (q : ℝ[X]) (s : ℝ) (t u : ℝ) :
    |remezVol q s u - remezVol q s t| ≤ |u - t| := by
  wlog htu : t ≤ u generalizing t u with H
  · rw [abs_sub_comm (u : ℝ), abs_sub_comm (remezVol q s u)]
    exact H u t (le_of_not_ge htu)
  rw [abs_of_nonneg (sub_nonneg.mpr htu),
    abs_of_nonneg (sub_nonneg.mpr (remezVol_mono q s htu))]
  by_cases ht : t < -1
  · -- below the window: `F t = -1`
    have hI : Set.Icc (-1 : ℝ) t = ∅ := Set.Icc_eq_empty (not_le.mpr ht)
    have hFt : remezVol q s t = -1 := by
      unfold remezVol
      rw [hI, Set.inter_empty, measure_empty, ENNReal.toReal_zero, add_zero]
    rw [hFt]
    have hle : (volume (remezSet q s ∩ Set.Icc (-1) u)).toReal ≤ u - t := by
      have h1 : volume (remezSet q s ∩ Set.Icc (-1) u) ≤ volume (Set.Icc (-1) u) :=
        measure_mono Set.inter_subset_right
      rw [Real.volume_Icc] at h1
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rw [ENNReal.toReal_ofReal'] at h2
      refine h2.trans ?_
      rw [max_le_iff]
      exact ⟨by linarith, by linarith⟩
    unfold remezVol
    linarith
  · push Not at ht
    -- the interval splits at `t`
    have hsplit : remezSet q s ∩ Set.Icc (-1) u
        = (remezSet q s ∩ Set.Icc (-1) t) ∪ (remezSet q s ∩ Set.Ioc t u) := by
      rw [← Set.inter_union_distrib_left, Set.Icc_union_Ioc_eq_Icc ht htu]
    have hdisj : Disjoint (remezSet q s ∩ Set.Icc (-1) t) (remezSet q s ∩ Set.Ioc t u) := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      exact absurd (hx2.2.1.trans_le hx1.2.2) (lt_irrefl _)
    have hvol : volume (remezSet q s ∩ Set.Icc (-1) u)
        = volume (remezSet q s ∩ Set.Icc (-1) t) + volume (remezSet q s ∩ Set.Ioc t u) := by
      rw [hsplit]
      exact measure_union hdisj
        ((measurableSet_remezSet q s).inter measurableSet_Ioc)
    have hfin1 : volume (remezSet q s ∩ Set.Icc (-1) t) ≠ ⊤ :=
      (volume_remezSet_inter_Icc_lt_top q s t).ne
    have hfin2 : volume (remezSet q s ∩ Set.Ioc t u) ≠ ⊤ := by
      have h1 : volume (remezSet q s ∩ Set.Ioc t u) ≤ volume (Set.Ioc t u) :=
        measure_mono Set.inter_subset_right
      rw [Real.volume_Ioc] at h1
      exact (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top).ne
    unfold remezVol
    rw [hvol, ENNReal.toReal_add hfin1 hfin2]
    have hle : (volume (remezSet q s ∩ Set.Ioc t u)).toReal ≤ u - t := by
      have h1 : volume (remezSet q s ∩ Set.Ioc t u) ≤ volume (Set.Ioc t u) :=
        measure_mono Set.inter_subset_right
      rw [Real.volume_Ioc] at h1
      have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (sub_nonneg.mpr htu)] at h2
    linarith

theorem continuous_remezVol (q : ℝ[X]) (s : ℝ) : Continuous (remezVol q s) := by
  have h : LipschitzWith 1 (remezVol q s) := by
    have h' := LipschitzWith.of_dist_le' (f := remezVol q s) (K := 1) (fun t u ↦ by
      rw [Real.dist_eq, Real.dist_eq, one_mul,
        abs_sub_comm (remezVol q s t) (remezVol q s u), abs_sub_comm t u]
      exact remezVol_lipschitz q s t u)
    rwa [Real.toNNReal_one] at h'
  exact h.continuous

theorem remezVol_neg_one (q : ℝ[X]) (s : ℝ) : remezVol q s (-1) = -1 := by
  have h0 : volume (remezSet q s ∩ Set.Icc (-1) (-1)) = 0 := by
    rw [Set.Icc_self]
    exact le_antisymm ((measure_mono Set.inter_subset_right).trans
      (le_of_eq Real.volume_singleton)) bot_le
  unfold remezVol
  rw [h0, ENNReal.toReal_zero, add_zero]

theorem remezVol_le_self (q : ℝ[X]) (s : ℝ) {t : ℝ} (ht : -1 ≤ t) :
    remezVol q s t ≤ t := by
  have hle : volume (remezSet q s ∩ Set.Icc (-1) t) ≤ volume (Set.Icc (-1) t) :=
    measure_mono Set.inter_subset_right
  rw [Real.volume_Icc] at hle
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ t - -1)] at htr
  unfold remezVol
  linarith

/-- Remez's inequality at the right endpoint (the heart of the proof). -/
theorem remez_endpoint (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (q : ℝ[X]) (hq : q.natDegree ≤ n)
    (hE : 2 ≤ (volume (remezSet q s)).toReal) :
    |q.eval (1 + s)| ≤ (T ℝ (n : ℤ)).eval (1 + s) := by
  rcases eq_or_ne n 0 with rfl | hn
  · -- degree zero: the constant is attained on the admissible set
    have hq0 : q.natDegree = 0 := Nat.le_zero.mp hq
    obtain ⟨t₀, ht₀⟩ := remezSet_nonempty_of_two_le q s hE
    have hev : q.eval (1 + s) = q.eval t₀ := by
      conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hq0]
      conv_rhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hq0]
      simp
    have hT : (T ℝ ((0 : ℕ) : ℤ)).eval (1 + s) = 1 := by
      rw [Nat.cast_zero, T_zero, eval_one]
    rw [hev, hT]
    exact ht₀.2
  · set F := remezVol q s with hF
    have hFcont : Continuous F := continuous_remezVol q s
    have hFleft : F (-1) = -1 := remezVol_neg_one q s
    have hFright : 1 ≤ F (1 + s) := by
      have hint : remezSet q s ∩ Set.Icc (-1) (1 + s) = remezSet q s :=
        Set.inter_eq_left.mpr Set.inter_subset_left
      have h := hE
      rw [hF, remezVol, hint]
      linarith
    -- node selection: `x k ∈ remezSet q s` with `F (x k) = chebNode n k`
    have hsel : ∀ k ≤ n, ∃ xk, xk ∈ remezSet q s ∧ F xk = chebNode n k := by
      intro k hk
      rcases eq_or_ne k 0 with rfl | hk0
      · -- the leftmost point of the admissible set
        have hne := remezSet_nonempty_of_two_le q s hE
        have hbdd : BddBelow (remezSet q s) := ⟨-1, fun x hx ↦ hx.1.1⟩
        refine ⟨sInf (remezSet q s), (isClosed_remezSet q s).csInf_mem hne hbdd, ?_⟩
        have hsub : remezSet q s ∩ Set.Icc (-1) (sInf (remezSet q s))
            ⊆ {sInf (remezSet q s)} := by
          intro x hx
          rw [Set.mem_singleton_iff]
          exact le_antisymm hx.2.2 (csInf_le hbdd hx.1)
        have hvol0 : volume (remezSet q s ∩ Set.Icc (-1) (sInf (remezSet q s))) = 0 :=
          le_antisymm ((measure_mono hsub).trans (le_of_eq Real.volume_singleton))
            bot_le
        rw [hF, remezVol, hvol0, ENNReal.toReal_zero, add_zero, chebNode_zero hn]
      · -- the general node: least point where the compression reaches `η_k`
        have hkη : -1 < chebNode n k := by
          rw [← chebNode_zero hn]
          exact chebNode_lt_chebNode hn hk (Nat.pos_of_ne_zero hk0)
        set A := Set.Icc (-1) (1 + s) ∩ F ⁻¹' (Set.Ici (chebNode n k)) with hA
        have hAcl : IsClosed A := IsClosed.inter isClosed_Icc (isClosed_Ici.preimage hFcont)
        have hAne : A.Nonempty := ⟨1 + s,
          ⟨⟨by linarith, le_refl _⟩, by
            rw [Set.mem_preimage, Set.mem_Ici]
            exact (chebNode_mem_Icc n k).2.trans hFright⟩⟩
        have hAbdd : BddBelow A := ⟨-1, fun x hx ↦ hx.1.1⟩
        set xk := sInf A with hxk
        have hxkA : xk ∈ A := hAcl.csInf_mem hAne hAbdd
        have hxkIcc : xk ∈ Set.Icc (-1) (1 + s) := hxkA.1
        have hFge : chebNode n k ≤ F xk := hxkA.2
        have hxkgt : -1 < xk := by
          rcases eq_or_lt_of_le hxkIcc.1 with h | h
          · rw [← h, hFleft] at hFge
            linarith
          · exact h
        have hFle : F xk ≤ chebNode n k := by
          by_contra hgt
          push Not at hgt
          set δ := min ((F xk - chebNode n k) / 2) ((xk + 1) / 2) with hδ
          have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
          have htmem : xk - δ ∈ A := by
            refine ⟨⟨by linarith [min_le_right ((F xk - chebNode n k) / 2) ((xk + 1) / 2),
                hxkgt],
              by linarith [hxkIcc.2, hδ0]⟩, ?_⟩
            have hli := remezVol_lipschitz q s (xk - δ) xk
            rw [← hF] at hli
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ xk - (xk - δ))] at hli
            have hδle : δ ≤ (F xk - chebNode n k) / 2 := min_le_left _ _
            rw [Set.mem_preimage, Set.mem_Ici]
            have h1 : F xk - F (xk - δ) ≤ δ := by
              calc F xk - F (xk - δ) ≤ |F xk - F (xk - δ)| := le_abs_self _
                _ ≤ xk - (xk - δ) := hli
                _ = δ := by ring
            linarith
          exact absurd (csInf_le hAbdd htmem) (by linarith [hδ0])
        have hxkE : xk ∈ remezSet q s := by
          refine ⟨hxkIcc, ?_⟩
          by_contra hnot
          rw [Set.mem_setOf_eq, not_le] at hnot
          have hopen : IsOpen {t : ℝ | 1 < |q.eval t|} := isOpen_Ioi.preimage q.continuous.abs
          rw [Metric.isOpen_iff] at hopen
          obtain ⟨ε, hε0, hε⟩ := hopen xk hnot
          set δ := min (ε / 2) ((xk + 1) / 2) with hδ
          have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
          have htmem : xk - δ ∈ A := by
            refine ⟨⟨by linarith [min_le_right (ε / 2) ((xk + 1) / 2)],
              by linarith [min_le_left (ε / 2) ((xk + 1) / 2), hxkIcc.2]⟩, ?_⟩
            have hset : remezSet q s ∩ Set.Icc (-1) xk
                = remezSet q s ∩ Set.Icc (-1) (xk - δ) := by
              apply Set.Subset.antisymm
              · intro u hu
                refine ⟨hu.1, hu.2.1, ?_⟩
                by_contra hle
                push Not at hle
                have hdist : dist u xk < ε := by
                  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu.2.2)]
                  have hδle : δ ≤ ε / 2 := min_le_left _ _
                  linarith [hu.2.2]
                have hbig : 1 < |q.eval u| := hε hdist
                exact absurd hbig (not_lt.mpr hu.1.2)
              · exact Set.inter_subset_inter_right _
                  (Set.Icc_subset_Icc_right (by linarith [hδ0]))
            rw [Set.mem_preimage, Set.mem_Ici]
            have hFF : F (xk - δ) = F xk := by simp only [hF, remezVol, hset]
            linarith [hFge, hFF]
          exact absurd (csInf_le hAbdd htmem) (by linarith [hδ0])
        exact ⟨xk, hxkE, le_antisymm hFle hFge⟩
    choose x' hxE hxF using hsel
    set x : ℕ → ℝ := fun k ↦ if hk : k ≤ n then x' k hk else 0 with hx
    have hxE' : ∀ k ≤ n, x k ∈ remezSet q s := fun k hk ↦ by
      simp only [hx, dif_pos hk]
      exact hxE k hk
    have hxF' : ∀ k ≤ n, F (x k) = chebNode n k := fun k hk ↦ by
      simp only [hx, dif_pos hk]
      exact hxF k hk
    apply abs_eval_le_chebT_eval hn q hq s x
    · intro j hj k hk hjk heq
      have h1 := hxF' j hj
      have h2 := hxF' k hk
      rw [heq] at h1
      have hnj := h1.symm.trans h2
      rcases lt_or_gt_of_ne hjk with h | h
      · exact absurd hnj (ne_of_lt (chebNode_lt_chebNode hn hk h))
      · exact absurd hnj (ne_of_gt (chebNode_lt_chebNode hn hj h))
    · exact fun k hk ↦ (hxE' k hk).2
    · exact fun k hk ↦ (hxE' k hk).1.2
    · intro k hk
      rw [← hxF' k hk]
      exact remezVol_le_self q s (hxE' k hk).1.1
    · intro j hj k hk
      rw [← hxF' j hj, ← hxF' k hk]
      exact remezVol_lipschitz q s (x k) (x j)

/-- The affine polynomial `t ↦ c*t + e` has degree one for `c ≠ 0`. -/
theorem natDegree_affine {c e : ℝ} (hc : c ≠ 0) : (C c * X + C e).natDegree = 1 := by
  have h1 : (C c * X : ℝ[X]).natDegree = 1 := Polynomial.natDegree_C_mul_X c hc
  have h2 : (C e : ℝ[X]).natDegree < (C c * X : ℝ[X]).natDegree := by
    rw [h1, Polynomial.natDegree_C]
    exact Nat.one_pos
  exact (natDegree_add_eq_left_of_natDegree_lt h2).trans h1

/-- The reflected admissible set. -/
theorem remezSet_reflect_subset (s : ℝ) (q : ℝ[X]) :
    (fun t ↦ s - t) ⁻¹' remezSet q s ⊆ remezSet (q.comp (C s - X)) s := by
  intro t ht
  have ht1 : s - t ∈ Set.Icc (-1) (1 + s) := ht.1
  have ht2 : |q.eval (s - t)| ≤ 1 := ht.2
  refine ⟨⟨by linarith [ht1.2], by linarith [ht1.1]⟩, ?_⟩
  have hev : (q.comp (C s - X)).eval t = q.eval (s - t) := by
    rw [Polynomial.eval_comp]
    simp [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  show |(q.comp (C s - X)).eval t| ≤ 1
  rw [hev]
  exact ht2

/-- Reflection about `s/2` preserves Lebesgue measure. -/
theorem volume_reflect_preimage (s : ℝ) (S : Set ℝ) :
    volume ((fun t ↦ s - t) ⁻¹' S) = volume S := by
  have h1 : (fun t ↦ s - t) = (fun u ↦ s + u) ∘ (fun t ↦ (-1 : ℝ) * t) := by
    funext t
    simp only [Function.comp_apply]
    ring
  rw [h1, Set.preimage_comp, Real.volume_preimage_mul_left (by norm_num : (-1 : ℝ) ≠ 0),
    MeasureTheory.measure_preimage_add]
  norm_num

/-- Remez's inequality at the left endpoint. -/
theorem remez_endpoint_left (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (q : ℝ[X]) (hq : q.natDegree ≤ n)
    (hE : 2 ≤ (volume (remezSet q s)).toReal) :
    |q.eval (-1)| ≤ (T ℝ (n : ℤ)).eval (1 + s) := by
  set qr := q.comp (C s - X) with hqr
  have hC1 : (C s - X : ℝ[X]).natDegree = 1 := by
    have h : C s - X = -(X - C s) := by ring
    rw [h, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have hqrdeg : qr.natDegree ≤ n := by
    rw [hqr, Polynomial.natDegree_comp, hC1, mul_one]
    exact hq
  have hEr : 2 ≤ (volume (remezSet qr s)).toReal := by
    have hvol : volume (remezSet q s) ≤ volume (remezSet qr s) := by
      rw [← volume_reflect_preimage s (remezSet q s)]
      exact measure_mono (remezSet_reflect_subset s q)
    exact hE.trans (ENNReal.toReal_mono (volume_remezSet_lt_top qr s).ne hvol)
  have h := remez_endpoint n s hs qr hqrdeg hEr
  have hev : qr.eval (1 + s) = q.eval (-1) := by
    rw [hqr, Polynomial.eval_comp]
    have h2 : (C s - X : ℝ[X]).eval (1 + s) = -1 := by
      simp [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    rw [h2]
  rwa [hev] at h

/-- The sharp Remez inequality on `[-1, 1+s]`. -/
theorem remez_eval_le (n : ℕ) (s : ℝ) (hs : 0 ≤ s) (q : ℝ[X]) (hq : q.natDegree ≤ n)
    (hE : 2 ≤ (volume (remezSet q s)).toReal) :
    ∀ y ∈ Set.Icc (-1) (1 + s), |q.eval y| ≤ (T ℝ (n : ℤ)).eval (1 + s) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with rfl | hy1
  · exact remez_endpoint_left n s hs q hq hE
  rcases eq_or_lt_of_le hy.2 with rfl | hy2
  · exact remez_endpoint n s hs q hq hE
  -- interior point: the sliding argument
  set E := remezSet q s with hEdef
  have hsplit : E ⊆ (E ∩ Set.Icc (-1) y) ∪ (E ∩ Set.Icc y (1 + s)) := by
    intro t ht
    rcases le_or_gt t y with h | h
    · exact Or.inl ⟨ht, ht.1.1, h⟩
    · exact Or.inr ⟨ht, le_of_lt h, ht.1.2⟩
  have hfin1 : volume (E ∩ Set.Icc (-1) y) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) (volume_remezSet_lt_top q s)).ne
  have hfin2 : volume (E ∩ Set.Icc y (1 + s)) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) (volume_remezSet_lt_top q s)).ne
  have hvol2 : 2 ≤ (volume (E ∩ Set.Icc (-1) y)).toReal
      + (volume (E ∩ Set.Icc y (1 + s))).toReal := by
    have h1 : volume E ≤ volume (E ∩ Set.Icc (-1) y) + volume (E ∩ Set.Icc y (1 + s)) :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    rw [← ENNReal.toReal_add hfin1 hfin2]
    exact hE.trans (ENNReal.toReal_mono (ENNReal.add_lt_top.mpr
      ⟨hfin1.lt_top, hfin2.lt_top⟩).ne h1)
  set lam : ℝ := 2 / (2 + s) with hlam
  have hs2 : (0 : ℝ) < 2 + s := by linarith
  by_cases hcase : lam * (y + 1) ≤ (volume (E ∩ Set.Icc (-1) y)).toReal
  · -- the left part is dense: slide it onto the whole window
    set c := (y + 1) / (2 + s) with hc
    have hc0 : (0 : ℝ) < c := div_pos (by linarith) hs2
    set e := c - 1 with he
    have hα1 : c * (-1) + e = -1 := by rw [he]; ring
    have hα2 : c * (1 + s) + e = y := by
      rw [he, hc]
      field_simp
      ring
    set α : ℝ[X] := C c * X + C e with hα
    have hαdeg : α.natDegree = 1 := natDegree_affine (ne_of_gt hc0)
    set q1 := q.comp α with hq1
    have hq1deg : q1.natDegree ≤ n := by
      rw [hq1, Polynomial.natDegree_comp, hαdeg, mul_one]
      exact hq
    have hpre : (fun t ↦ c * t + e) ⁻¹' (E ∩ Set.Icc (-1) y) ⊆ remezSet q1 s := by
      intro t ht
      have hαt : c * t + e ∈ E ∩ Set.Icc (-1) y := ht
      have hte : t ∈ Set.Icc (-1) (1 + s) := by
        constructor
        · by_contra h2
          rw [not_le] at h2
          have h3 : c * t + e < c * (-1) + e := by
            linarith [mul_lt_mul_of_pos_left h2 hc0]
          linarith [hαt.2.1, hα1]
        · by_contra h3
          rw [not_le] at h3
          have h4 : c * (1 + s) + e < c * t + e := by
            linarith [mul_lt_mul_of_pos_left h3 hc0]
          linarith [hαt.2.2, hα2]
      refine ⟨hte, ?_⟩
      have hev : q1.eval t = q.eval (c * t + e) := by
        rw [hq1, Polynomial.eval_comp, hα]
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      show |q1.eval t| ≤ 1
      rw [hev]
      exact hαt.1.2
    have hvolt : volume ((fun t ↦ c * t + e) ⁻¹' (E ∩ Set.Icc (-1) y))
        = ENNReal.ofReal |c⁻¹| * volume (E ∩ Set.Icc (-1) y) := by
      have hfun : (fun t ↦ c * t + e) = (fun u ↦ e + u) ∘ (fun t ↦ c * t) := by
        funext t
        simp only [Function.comp_apply]
        ring
      rw [hfun, Set.preimage_comp, Real.volume_preimage_mul_left (ne_of_gt hc0),
        MeasureTheory.measure_preimage_add]
    have hE1 : 2 ≤ (volume (remezSet q1 s)).toReal := by
      have hmono : volume ((fun t ↦ c * t + e) ⁻¹' (E ∩ Set.Icc (-1) y))
          ≤ volume (remezSet q1 s) := measure_mono hpre
      rw [hvolt] at hmono
      have htr := ENNReal.toReal_mono (volume_remezSet_lt_top q1 s).ne hmono
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
        abs_of_nonneg (le_of_lt (inv_pos_of_pos hc0))] at htr
      have hkey : (2 : ℝ) ≤ c⁻¹ * (volume (E ∩ Set.Icc (-1) y)).toReal := by
        have hlam2 : lam * (y + 1) = 2 * c := by rw [hlam, hc]; ring
        have hc2 : c⁻¹ * (2 * c) = 2 := by
          rw [mul_comm (2 : ℝ) c, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc0), one_mul]
        calc (2 : ℝ) = c⁻¹ * (lam * (y + 1)) := by rw [hlam2, hc2]
          _ ≤ c⁻¹ * (volume (E ∩ Set.Icc (-1) y)).toReal :=
            mul_le_mul_of_nonneg_left hcase (le_of_lt (inv_pos_of_pos hc0))
      exact hkey.trans htr
    have h1 := remez_endpoint n s hs q1 hq1deg hE1
    have hev : q1.eval (1 + s) = q.eval y := by
      rw [hq1, Polynomial.eval_comp, hα]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hα2]
    rwa [hev] at h1
  · -- the right part is dense: slide it and use the left endpoint
    rw [not_le] at hcase
    have hv2 : lam * (1 + s - y) ≤ (volume (E ∩ Set.Icc y (1 + s))).toReal := by
      have h1 : (2 : ℝ) = lam * (y + 1) + lam * (1 + s - y) := by
        rw [hlam]
        field_simp
        ring
      linarith [hvol2, hcase, h1]
    set c := (1 + s - y) / (2 + s) with hc
    have hc0 : (0 : ℝ) < c := div_pos (by linarith) hs2
    set e := y + c with he
    have hβ1 : c * (-1) + e = y := by rw [he]; ring
    have hβ2 : c * (1 + s) + e = 1 + s := by
      rw [he, hc]
      field_simp
      ring
    set β : ℝ[X] := C c * X + C e with hβ
    have hβdeg : β.natDegree = 1 := natDegree_affine (ne_of_gt hc0)
    set q2 := q.comp β with hq2
    have hq2deg : q2.natDegree ≤ n := by
      rw [hq2, Polynomial.natDegree_comp, hβdeg, mul_one]
      exact hq
    have hpre : (fun t ↦ c * t + e) ⁻¹' (E ∩ Set.Icc y (1 + s)) ⊆ remezSet q2 s := by
      intro t ht
      have hαt : c * t + e ∈ E ∩ Set.Icc y (1 + s) := ht
      have hte : t ∈ Set.Icc (-1) (1 + s) := by
        constructor
        · by_contra h2
          rw [not_le] at h2
          have h3 : c * t + e < c * (-1) + e := by
            linarith [mul_lt_mul_of_pos_left h2 hc0]
          linarith [hαt.2.1, hβ1]
        · by_contra h3
          rw [not_le] at h3
          have h4 : c * (1 + s) + e < c * t + e := by
            linarith [mul_lt_mul_of_pos_left h3 hc0]
          linarith [hαt.2.2, hβ2]
      refine ⟨hte, ?_⟩
      have hev : q2.eval t = q.eval (c * t + e) := by
        rw [hq2, Polynomial.eval_comp, hβ]
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      show |q2.eval t| ≤ 1
      rw [hev]
      exact hαt.1.2
    have hvolt : volume ((fun t ↦ c * t + e) ⁻¹' (E ∩ Set.Icc y (1 + s)))
        = ENNReal.ofReal |c⁻¹| * volume (E ∩ Set.Icc y (1 + s)) := by
      have hfun : (fun t ↦ c * t + e) = (fun u ↦ e + u) ∘ (fun t ↦ c * t) := by
        funext t
        simp only [Function.comp_apply]
        ring
      rw [hfun, Set.preimage_comp, Real.volume_preimage_mul_left (ne_of_gt hc0),
        MeasureTheory.measure_preimage_add]
    have hE2 : 2 ≤ (volume (remezSet q2 s)).toReal := by
      have hmono : volume ((fun t ↦ c * t + e) ⁻¹' (E ∩ Set.Icc y (1 + s)))
          ≤ volume (remezSet q2 s) := measure_mono hpre
      rw [hvolt] at hmono
      have htr := ENNReal.toReal_mono (volume_remezSet_lt_top q2 s).ne hmono
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
        abs_of_nonneg (le_of_lt (inv_pos_of_pos hc0))] at htr
      have hkey : (2 : ℝ) ≤ c⁻¹ * (volume (E ∩ Set.Icc y (1 + s))).toReal := by
        have hlam2 : lam * (1 + s - y) = 2 * c := by rw [hlam, hc]; ring
        have hc2 : c⁻¹ * (2 * c) = 2 := by
          rw [mul_comm (2 : ℝ) c, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc0), one_mul]
        calc (2 : ℝ) = c⁻¹ * (lam * (1 + s - y)) := by rw [hlam2, hc2]
          _ ≤ c⁻¹ * (volume (E ∩ Set.Icc y (1 + s))).toReal :=
            mul_le_mul_of_nonneg_left hv2 (le_of_lt (inv_pos_of_pos hc0))
      exact hkey.trans htr
    have h2 := remez_endpoint_left n s hs q2 hq2deg hE2
    have hev : q2.eval (-1) = q.eval y := by
      rw [hq2, Polynomial.eval_comp, hβ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hβ1]
    rwa [hev] at h2

/-- Remez's inequality on an arbitrary interval `Icc a b`: a degree-≤ n polynomial bounded
by `A` on a subset of measure at least `μ` is bounded by `A * T_n(2(b−a)/μ − 1)`. -/
theorem remez_interval (n : ℕ) (a b : ℝ) (hab : a < b) (p : ℝ[X]) (hp : p.natDegree ≤ n)
    (A : ℝ) (hA : 0 ≤ A) (μ : ℝ) (hμ0 : 0 < μ)
    (hμ : μ ≤ (volume (Set.Icc a b ∩ {t | |p.eval t| ≤ A})).toReal) :
    ∀ t ∈ Set.Icc a b, |p.eval t| ≤ A * (T ℝ (n : ℤ)).eval (2 * (b - a) / μ - 1) := by
  set E := Set.Icc a b ∩ {t | |p.eval t| ≤ A} with hEdef
  have hvolE : volume E ≤ volume (Set.Icc a b) := measure_mono Set.inter_subset_left
  rw [Real.volume_Icc] at hvolE
  have hμba : μ ≤ b - a := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolE
    rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ b - a)] at h
    exact hμ.trans h
  have hz1 : 1 ≤ 2 * (b - a) / μ - 1 := by
    have h1 : μ ≤ 2 * (b - a) := by linarith
    have h2 : (2 : ℝ) ≤ 2 * (b - a) / μ := (le_div_iff₀ hμ0).mpr (by linarith)
    linarith
  rcases eq_or_lt_of_le hA with rfl | hA
  · -- A = 0: p vanishes on a set of positive measure, hence p = 0
    have hp0 : p = 0 := by
      by_contra hpne
      have hsub : E ⊆ {t | p.eval t = 0} := by
        intro t ht
        exact abs_nonpos_iff.mp ht.2
      have hfin : {t : ℝ | p.eval t = 0} = ↑p.roots.toFinset := by
        ext t
        simp [Polynomial.mem_roots hpne, Polynomial.IsRoot.def]
      have hvol0 : volume E = 0 := by
        have hcount : {t : ℝ | p.eval t = 0}.Countable := by
          rw [hfin]
          exact Finset.countable_toSet _
        exact measure_mono_null hsub (Set.Countable.measure_zero hcount volume)
      rw [hvol0, ENNReal.toReal_zero] at hμ
      linarith
    intro t _
    rw [hp0]
    simp only [Polynomial.eval_zero, abs_zero]
    exact mul_nonneg hA (le_trans zero_le_one (one_le_eval_T_real _ hz1))
  · -- rescale to the normalized window
    set q := C A⁻¹ * p with hq
    have hqdeg : q.natDegree ≤ n := by
      rw [hq, Polynomial.natDegree_C_mul (inv_ne_zero (ne_of_gt hA))]
      exact hp
    have hsublevel : {t : ℝ | |q.eval t| ≤ 1} = {t | |p.eval t| ≤ A} := by
      ext t
      rw [hq]
      simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C,
        abs_mul, abs_inv, abs_of_pos hA]
      constructor
      · intro h
        have := (inv_mul_le_iff₀ hA).mp h
        rwa [mul_one] at this
      · intro h
        rw [inv_mul_le_iff₀ hA, mul_one]
        exact h
    have hs : (0 : ℝ) ≤ 2 * (b - a) / μ - 2 := by linarith
    -- the affine map from the window onto Icc a b
    set c := μ / 2 with hc
    have hc0 : (0 : ℝ) < c := by linarith
    set e := a + c with he
    have hφ1 : c * (-1) + e = a := by rw [he]; ring
    have hφ2 : c * (2 * (b - a) / μ - 1) + e = b := by
      rw [he, hc]
      field_simp
      ring
    set φ : ℝ[X] := C c * X + C e with hφ
    have hφdeg : φ.natDegree = 1 := natDegree_affine (ne_of_gt hc0)
    set pt := q.comp φ with hpt
    have hptdeg : pt.natDegree ≤ n := by
      rw [hpt, Polynomial.natDegree_comp, hφdeg, mul_one]
      exact hqdeg
    have hpre : (fun t ↦ c * t + e) ⁻¹' E
        ⊆ remezSet pt (2 * (b - a) / μ - 2) := by
      intro t ht
      have hφt : c * t + e ∈ E := ht
      have hte : t ∈ Set.Icc (-1) (2 * (b - a) / μ - 1) := by
        constructor
        · by_contra h2
          rw [not_le] at h2
          have h3 : c * t + e < c * (-1) + e := by
            linarith [mul_lt_mul_of_pos_left h2 hc0]
          linarith [hφt.1.1, hφ1]
        · by_contra h3
          rw [not_le] at h3
          have h4 : c * (2 * (b - a) / μ - 1) + e < c * t + e := by
            linarith [mul_lt_mul_of_pos_left h3 hc0]
          linarith [hφt.1.2, hφ2]
      refine ⟨?_, ?_⟩
      · show t ∈ Set.Icc (-1) (1 + (2 * (b - a) / μ - 2))
        have : 1 + (2 * (b - a) / μ - 2) = 2 * (b - a) / μ - 1 := by ring
        rwa [this]
      · have hev : pt.eval t = q.eval (c * t + e) := by
          rw [hpt, Polynomial.eval_comp, hφ]
          simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        have hq1 : |q.eval (c * t + e)| ≤ 1 :=
          (Set.ext_iff.mp hsublevel (c * t + e)).mpr hφt.2
        show |pt.eval t| ≤ 1
        rw [hev]
        exact hq1
    have hvolt : volume ((fun t ↦ c * t + e) ⁻¹' E)
        = ENNReal.ofReal |c⁻¹| * volume E := by
      have hfun : (fun t ↦ c * t + e) = (fun u ↦ e + u) ∘ (fun t ↦ c * t) := by
        funext t
        simp only [Function.comp_apply]
        ring
      rw [hfun, Set.preimage_comp, Real.volume_preimage_mul_left (ne_of_gt hc0),
        MeasureTheory.measure_preimage_add]
    have hE1 : 2 ≤ (volume (remezSet pt (2 * (b - a) / μ - 2))).toReal := by
      have hmono : volume ((fun t ↦ c * t + e) ⁻¹' E)
          ≤ volume (remezSet pt (2 * (b - a) / μ - 2)) := measure_mono hpre
      rw [hvolt] at hmono
      have htr := ENNReal.toReal_mono
        (volume_remezSet_lt_top pt (2 * (b - a) / μ - 2)).ne hmono
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
        abs_of_nonneg (le_of_lt (inv_pos_of_pos hc0))] at htr
      have hkey : (2 : ℝ) ≤ c⁻¹ * (volume E).toReal := by
        have h2 : c⁻¹ * μ = 2 := by
          rw [hc]
          field_simp
        calc (2 : ℝ) = c⁻¹ * μ := h2.symm
          _ ≤ c⁻¹ * (volume E).toReal :=
            mul_le_mul_of_nonneg_left hμ (le_of_lt (inv_pos_of_pos hc0))
      exact hkey.trans htr
    have hmain := remez_eval_le n (2 * (b - a) / μ - 2) hs pt hptdeg hE1
    rw [show 1 + (2 * (b - a) / μ - 2) = 2 * (b - a) / μ - 1 from by ring] at hmain
    intro t ht
    -- the preimage of t under the affine map
    set u := (t - e) / c with hu
    have humem : u ∈ Set.Icc (-1) (2 * (b - a) / μ - 1) := by
      constructor
      · rw [hu, le_div_iff₀ hc0]
        linarith [ht.1, hφ1]
      · rw [hu, div_le_iff₀ hc0]
        linarith [ht.2, hφ2]
    have hφu : c * u + e = t := by
      rw [hu]
      field_simp
      ring
    have h1 := hmain u humem
    have hev : pt.eval u = q.eval t := by
      rw [hpt, Polynomial.eval_comp, hφ]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        hφu]
    rw [hev] at h1
    have h2 : p.eval t = A * q.eval t := by
      rw [hq]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hA), one_mul]
    rw [h2, abs_mul, abs_of_pos hA]
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hA)

end UCPlanar.Support
