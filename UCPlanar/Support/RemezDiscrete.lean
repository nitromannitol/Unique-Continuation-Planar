import UCPlanar.Support.RemezMeasure
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.GetD

/-!
# The discrete Remez inequality

Buhovsky, Logunov, Malinnikova, Sodin, *A discrete harmonic function bounded on a large
portion of `Z²` is constant*, Corollary 2.2: a real polynomial `p` of degree at most
`m < R` bounded by `A` on at least half of the integer points of `[-R, R]` is bounded by
`A * (16R / (R - m))^m` on the integer points of `[-2R, 2R]`.

The proof follows BLMS: between consecutive points of the dense set `S`, at least
`|S| - 1 - (m - 1)` unit intervals contain no root of the derivative of `p`; on each such
interval `p` has no interior extremum, so `|p| ≤ A` throughout.  The admissible set
`{|p| ≤ A}` therefore has Lebesgue measure at least `|S| - m` inside the window
`[-2⌈R⌉, 2⌈R⌉]`, and the sharp Remez inequality of `RemezMeasure.lean` applies.
-/

open Polynomial Real Set Finset MeasureTheory
open Polynomial.Chebyshev
open scoped ENNReal

namespace UCPlanar.Support.Three

/-- The integer interval `[-N, N]`. -/
noncomputable def seg (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

end UCPlanar.Support.Three

namespace UCPlanar.Support

/-- The `i`-th element of a finset of integers in increasing order, extended by `0`
outside the range. -/
noncomputable def sortEnum (S : Finset ℤ) (i : ℕ) : ℤ := (S.sort (· ≤ ·)).getD i 0

theorem sortEnum_eq_get {S : Finset ℤ} {i : ℕ} (hi : i < S.card) :
    sortEnum S i = (S.sort (· ≤ ·)).get ⟨i, by rwa [Finset.length_sort]⟩ :=
  List.getD_eq_getElem _ _ _

theorem sortEnum_mem {S : Finset ℤ} {i : ℕ} (hi : i < S.card) : sortEnum S i ∈ S := by
  rw [sortEnum_eq_get hi]
  exact (Finset.mem_sort _).mp (List.get_mem _ _)

theorem sortEnum_strictMono {S : Finset ℤ} {i j : ℕ} (hij : i < j) (hj : j < S.card) :
    sortEnum S i < sortEnum S j := by
  rw [sortEnum_eq_get (by omega : i < S.card), sortEnum_eq_get hj]
  exact (Finset.sortedLT_sort S).strictMono_get (Fin.mk_lt_mk.mpr hij)

/-- One-sided extremum bound: if the derivative of `p` has no zero in `Ioo a b`, then
`p x ≤ max (p a) (p b)` on `Icc a b`.  A point above both endpoint values would force an
interior maximum, where the derivative vanishes. -/
theorem eval_le_max_of_derivative_ne_zero_on {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Set.Ioo a b, p.derivative.eval y ≠ 0) :
    ∀ x ∈ Set.Icc a b, p.eval x ≤ max (p.eval a) (p.eval b) := by
  intro x hx
  by_contra hxm
  rw [not_le] at hxm
  have hxioo : x ∈ Set.Ioo a b := by
    constructor
    · rcases eq_or_lt_of_le hx.1 with heq | hlt
      · exfalso
        rw [← heq] at hxm
        exact not_lt_of_ge (le_max_left _ _) hxm
      · exact hlt
    · rcases eq_or_lt_of_le hx.2 with heq | hlt
      · exfalso
        rw [heq] at hxm
        exact not_lt_of_ge (le_max_right _ _) hxm
      · exact hlt
  have hcont : ContinuousOn (fun y => p.eval y) (Set.Icc a b) := p.continuous.continuousOn
  obtain ⟨ξ, hξ, hξmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hcont
  have hξgt : max (p.eval a) (p.eval b) < p.eval ξ := lt_of_lt_of_le hxm (hξmax hx)
  have hξioo : ξ ∈ Set.Ioo a b := by
    constructor
    · rcases eq_or_lt_of_le hξ.1 with heq | hlt
      · exfalso
        rw [← heq] at hξgt
        exact not_lt_of_ge (le_max_left _ _) hξgt
      · exact hlt
    · rcases eq_or_lt_of_le hξ.2 with heq | hlt
      · exfalso
        rw [heq] at hξgt
        exact not_lt_of_ge (le_max_right _ _) hξgt
      · exact hlt
  have hloc : IsLocalMax (fun y => p.eval y) ξ :=
    hξmax.isLocalMax
      (Filter.mem_of_superset (Ioo_mem_nhds hξioo.1 hξioo.2) Ioo_subset_Icc_self)
  have hder : p.derivative.eval ξ = 0 := by
    have h1 : deriv (fun y => p.eval y) ξ = 0 := hloc.deriv_eq_zero
    rw [(p.hasDerivAt ξ).deriv] at h1
    exact h1
  exact h ξ hξioo hder

/-- Two-sided version: `|p x| ≤ max |p a| |p b|` on `Icc a b`. -/
theorem abs_eval_le_max_of_derivative_ne_zero_on {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Set.Ioo a b, p.derivative.eval y ≠ 0) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    |p.eval x| ≤ max |p.eval a| |p.eval b| := by
  have hup := eval_le_max_of_derivative_ne_zero_on hab h x hx
  have hneg : ∀ y ∈ Set.Ioo a b, (-p).derivative.eval y ≠ 0 := by
    intro y hy h0
    rw [Polynomial.derivative_neg, Polynomial.eval_neg] at h0
    exact h y hy (neg_eq_zero.mp h0)
  have hdn := eval_le_max_of_derivative_ne_zero_on (p := -p) hab hneg x hx
  simp only [Polynomial.eval_neg] at hdn
  have hmin : min (p.eval a) (p.eval b) ≤ p.eval x := by
    rcases le_total (p.eval a) (p.eval b) with hcase | hcase
    · rw [min_eq_left hcase]
      rw [max_eq_left (neg_le_neg hcase)] at hdn
      linarith [hdn]
    · rw [min_eq_right hcase]
      rw [max_eq_right (neg_le_neg hcase)] at hdn
      linarith [hdn]
  have hnegmax : min (-|p.eval a|) (-|p.eval b|) = -max |p.eval a| |p.eval b| := by
    rcases le_total |p.eval a| |p.eval b| with hcase | hcase
    · rw [min_eq_right (neg_le_neg hcase), max_eq_right hcase]
    · rw [min_eq_left (neg_le_neg hcase), max_eq_left hcase]
  refine abs_le.mpr ⟨?_, hup.trans (max_le_max (le_abs_self _) (le_abs_self _))⟩
  calc -max |p.eval a| |p.eval b| = min (-|p.eval a|) (-|p.eval b|) := hnegmax.symm
    _ ≤ min (p.eval a) (p.eval b) := min_le_min (neg_abs_le _) (neg_abs_le _)
    _ ≤ p.eval x := hmin

/-- The discrete Remez inequality, BLMS Corollary 2.2: a real polynomial of degree at most
`m < R` bounded by `A` on at least half of the integer points of `[-R, R]` is bounded by
`A * (16R / (R - m))^m` on the integer points of `[-2R, 2R]`. -/
theorem discreteRemez (R : ℝ) (m : ℕ) (A : ℝ) (p : Polynomial ℝ)
    (hA : 0 ≤ A) (hR : 0 < R) (hmR : (m : ℝ) < R) (hp : p.natDegree ≤ m)
    (hS : ∃ S : Finset ℤ, S ⊆ Three.seg ⌈R⌉₊ ∧
      2 * S.card ≥ (Three.seg ⌈R⌉₊).card ∧ ∀ s ∈ S, |p.eval (s : ℝ)| ≤ A)
    (s : ℤ) (hs : |(s : ℝ)| ≤ 2 * R) :
    |p.eval (s : ℝ)| ≤ A * (16 * R / (R - m)) ^ m := by
  classical
  obtain ⟨S, hSsub, hScard, hSbound⟩ := hS
  set N := ⌈R⌉₊ with hN
  have hRN : R ≤ (N : ℝ) := Nat.le_ceil R
  have hNpos' : 0 < N := Nat.ceil_pos.mpr hR
  have hmN : m < N := by exact_mod_cast hmR.trans_le hRN
  have hRm : (0 : ℝ) < R - (m : ℝ) := by linarith [hmR]
  -- cardinality estimates for `S`
  have hsegcard : (Three.seg N).card = 2 * N + 1 := by
    have hunfold : Three.seg N = Finset.Icc (-(N : ℤ)) (N : ℤ) := rfl
    rw [hunfold, Int.card_Icc]
    have hcast : ((N : ℤ) + 1 - -(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, Int.toNat_natCast]
  rw [hsegcard] at hScard
  have htge : N + 1 ≤ S.card := by omega
  have htle : S.card ≤ 2 * N + 1 := by
    have h1 := Finset.card_le_card hSsub
    rw [hsegcard] at h1
    exact h1
  set t := S.card with ht
  by_cases hp0 : p.natDegree = 0
  · -- `p` is constant: the bound comes from any point of `S`
    have hev : ∀ y : ℝ, p.eval y = p.coeff 0 := by
      intro y
      rw [Polynomial.eq_C_of_natDegree_eq_zero hp0]
      simp [Polynomial.eval_C, Polynomial.coeff_C]
    obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
    have hb0 := hSbound s₀ hs₀
    rw [hev] at hb0 ⊢
    have hbase : (1 : ℝ) ≤ 16 * R / (R - (m : ℝ)) := by
      rw [le_div_iff₀ hRm]
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [hR, hm0]
    have h1 : (1 : ℝ) ≤ (16 * R / (R - (m : ℝ))) ^ m := one_le_pow₀ hbase
    calc |p.coeff 0| ≤ A := hb0
      _ = A * 1 := (mul_one A).symm
      _ ≤ A * (16 * R / (R - (m : ℝ))) ^ m := mul_le_mul_of_nonneg_left h1 hA
  · -- `p` is nonconstant: the BLMS interval argument
    have hderne : p.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hp0
    have hRcard : p.derivative.roots.toFinset.card ≤ m - 1 := by
      calc p.derivative.roots.toFinset.card ≤ Multiset.card p.derivative.roots :=
            Multiset.toFinset_card_le _
        _ ≤ p.derivative.natDegree := Polynomial.card_roots' _
        _ ≤ p.natDegree - 1 := Polynomial.natDegree_derivative_le _
        _ ≤ m - 1 := Nat.sub_le_sub_right hp 1
    -- intervals between consecutive points of `S` containing a root of `p'`
    set bad := (Finset.range (t - 1)).filter (fun i =>
      ∃ r ∈ p.derivative.roots.toFinset,
        r ∈ Set.Ioo ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ))) with hbaddef
    set f : ℕ → ℝ := fun i =>
      if h : ∃ r ∈ p.derivative.roots.toFinset,
          r ∈ Set.Ioo ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ))
      then h.choose else 0 with hfdef
    have hf1 : ∀ i ∈ bad, f i ∈ p.derivative.roots.toFinset := by
      intro i hi
      have h2 := (Finset.mem_filter.mp hi).2
      simp only [hfdef, dif_pos h2]
      exact h2.choose_spec.1
    have hf2 : ∀ i ∈ bad,
        f i ∈ Set.Ioo ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ)) := by
      intro i hi
      have h2 := (Finset.mem_filter.mp hi).2
      simp only [hfdef, dif_pos h2]
      exact h2.choose_spec.2
    have hinj : Set.InjOn f ↑bad := by
      intro i hi j hj hij
      by_contra hne
      have hiG : i < t - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have hjG : j < t - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : sortEnum S (i + 1) ≤ sortEnum S j := by
          rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with heq | hlt2
          · exact le_of_eq (congrArg (sortEnum S) heq)
          · exact le_of_lt (sortEnum_strictMono hlt2 (by omega))
        have hfi := hf2 i hi
        have hfj := hf2 j hj
        rw [hij] at hfi
        have hcast : ((sortEnum S (i + 1) : ℤ) : ℝ) ≤ ((sortEnum S j : ℤ) : ℝ) :=
          Int.cast_le.mpr hle
        linarith [hfi.2, hfj.1, hcast]
      · have hle : sortEnum S (j + 1) ≤ sortEnum S i := by
          rcases eq_or_lt_of_le (show j + 1 ≤ i by omega) with heq | hgt2
          · exact le_of_eq (congrArg (sortEnum S) heq)
          · exact le_of_lt (sortEnum_strictMono hgt2 (by omega))
        have hfi := hf2 i hi
        have hfj := hf2 j hj
        rw [← hij] at hfj
        have hcast : ((sortEnum S (j + 1) : ℤ) : ℝ) ≤ ((sortEnum S i : ℤ) : ℝ) :=
          Int.cast_le.mpr hle
        linarith [hfj.2, hfi.1, hcast]
    have hbadcard : bad.card ≤ m - 1 :=
      (Finset.card_le_card_of_injOn f (fun i hi => hf1 i hi) hinj).trans hRcard
    -- the good intervals
    set G := Finset.range (t - 1) \ bad with hGdef
    have hGcard : t - m ≤ G.card := by
      have hbadsub : bad ⊆ Finset.range (t - 1) := Finset.filter_subset _ _
      rw [hGdef, Finset.card_sdiff_of_subset hbadsub, Finset.card_range]
      omega
    have hgood : ∀ i ∈ G,
        ∀ y ∈ Set.Ioo ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ)),
          p.derivative.eval y ≠ 0 := by
      intro i hi y hy hy0
      have hyr : y ∈ p.derivative.roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hderne]
        exact hy0
      have hib : i ∈ bad := by
        rw [hbaddef]
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hi).1, ⟨y, hyr, hy⟩⟩
      exact (Finset.mem_sdiff.mp hi).2 hib
    have hbound : ∀ i ∈ G,
        ∀ x ∈ Set.Icc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ)),
          |p.eval x| ≤ A := by
      intro i hi x hx
      have hi1 : i < t - 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
      have hle : ((sortEnum S i : ℤ) : ℝ) ≤ ((sortEnum S (i + 1) : ℤ) : ℝ) :=
        Int.cast_le.mpr (le_of_lt (sortEnum_strictMono (by omega) (by omega)))
      refine (abs_eval_le_max_of_derivative_ne_zero_on hle (hgood i hi) x hx).trans ?_
      exact max_le (hSbound _ (sortEnum_mem (by omega))) (hSbound _ (sortEnum_mem (by omega)))
    -- the union of the good half-open intervals has measure `≥ G.card`
    have hsub : (⋃ i ∈ G, Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ)))
        ⊆ Set.Icc (-2 * (N : ℝ)) (2 * (N : ℝ)) ∩ {x | |p.eval x| ≤ A} := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hiG, hxi⟩ := hx
      have hi1 : i < t - 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hiG).1
      have hmem1 := Finset.mem_Icc.mp (hSsub (sortEnum_mem (by omega : i < S.card)))
      have hmem2 := Finset.mem_Icc.mp (hSsub (sortEnum_mem (by omega : i + 1 < S.card)))
      constructor
      · constructor
        · have hc1 : ((-(N : ℤ) : ℤ) : ℝ) ≤ ((sortEnum S i : ℤ) : ℝ) :=
            Int.cast_le.mpr hmem1.1
          push_cast at hc1
          linarith [hxi.1, hc1]
        · have hc2 : ((sortEnum S (i + 1) : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) :=
            Int.cast_le.mpr hmem2.2
          push_cast at hc2
          linarith [hxi.2, hc2]
      · exact hbound i hiG x ⟨le_of_lt hxi.1, hxi.2⟩
    have hdisj : (↑G : Set ℕ).PairwiseDisjoint
        (fun i => Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ))) := by
      have aux : ∀ i j : ℕ, i ∈ G → j ∈ G → i < j →
          Disjoint (Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ)))
            (Set.Ioc ((sortEnum S j : ℝ)) ((sortEnum S (j + 1) : ℝ))) := by
        intro i j hi hj hlt
        have hi1 : i < t - 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
        have hj1 : j < t - 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hj).1
        have hle : sortEnum S (i + 1) ≤ sortEnum S j := by
          rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with heq | hlt2
          · exact le_of_eq (congrArg (sortEnum S) heq)
          · exact le_of_lt (sortEnum_strictMono hlt2 (by omega))
        apply Set.disjoint_left.mpr
        intro x hx1 hx2
        have hcast : ((sortEnum S (i + 1) : ℤ) : ℝ) ≤ ((sortEnum S j : ℤ) : ℝ) :=
          Int.cast_le.mpr hle
        linarith [hx1.2, hx2.1, hcast]
      intro i hi j hj hij
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact aux i j hi hj hlt
      · exact Disjoint.symm (aux j i hj hi hgt)
    have hvolsum : volume (⋃ i ∈ G, Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ)))
        = ∑ i ∈ G, volume (Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ))) :=
      measure_biUnion_finset hdisj (fun i _ => measurableSet_Ioc)
    have hvolge : (G.card : ℝ≥0∞)
        ≤ volume (⋃ i ∈ G, Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ))) := by
      rw [hvolsum]
      calc (G.card : ℝ≥0∞) = ∑ i ∈ G, (1 : ℝ≥0∞) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ i ∈ G, volume (Set.Ioc ((sortEnum S i : ℝ)) ((sortEnum S (i + 1) : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi1 : i < t - 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
          have hdiff : (1 : ℝ)
              ≤ ((sortEnum S (i + 1) : ℤ) : ℝ) - ((sortEnum S i : ℤ) : ℝ) := by
            have hlt : sortEnum S i < sortEnum S (i + 1) :=
              sortEnum_strictMono (by omega) (by omega)
            have h2 : ((sortEnum S i + 1 : ℤ) : ℝ) ≤ ((sortEnum S (i + 1) : ℤ) : ℝ) :=
              Int.cast_le.mpr (by omega)
            push_cast at h2
            linarith
          rw [Real.volume_Ioc, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hdiff
    have hfin' : volume (Set.Icc (-2 * (N : ℝ)) (2 * (N : ℝ)) ∩ {x | |p.eval x| ≤ A}) ≠ ⊤ :=
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne
    have hvolbound : (G.card : ℝ)
        ≤ (volume (Set.Icc (-2 * (N : ℝ)) (2 * (N : ℝ)) ∩ {x | |p.eval x| ≤ A})).toReal := by
      have h1 : (G.card : ℝ≥0∞)
          ≤ volume (Set.Icc (-2 * (N : ℝ)) (2 * (N : ℝ)) ∩ {x | |p.eval x| ≤ A}) :=
        hvolge.trans (measure_mono hsub)
      have h2 := ENNReal.toReal_mono hfin' h1
      rwa [ENNReal.toReal_natCast] at h2
    have hμ0 : (0 : ℝ) < (G.card : ℝ) := by
      have h1 : 0 < G.card := by omega
      exact_mod_cast h1
    -- Remez's inequality on the window `[-2N, 2N]`
    have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos'
    have hRmez := remez_interval m (-2 * (N : ℝ)) (2 * (N : ℝ)) (by linarith) p hp A hA
      (G.card : ℝ) hμ0 hvolbound
    have hsmem : (s : ℝ) ∈ Set.Icc (-2 * (N : ℝ)) (2 * (N : ℝ)) := by
      have h2 := abs_le.mp hs
      constructor <;> linarith [h2.1, h2.2, hRN]
    have hfin := hRmez (s : ℝ) hsmem
    set x := 8 * (N : ℝ) / (G.card : ℝ) - 1 with hx
    have hxarg : 2 * (2 * (N : ℝ) - -2 * (N : ℝ)) / (G.card : ℝ) - 1 = x := by
      rw [hx]
      ring
    rw [hxarg] at hfin
    -- compare the Chebyshev value with `(16R / (R - m))^m`
    have hGle : G.card ≤ 2 * N := by
      calc G.card ≤ (Finset.range (t - 1)).card := Finset.card_le_card Finset.sdiff_subset
        _ = t - 1 := Finset.card_range _
        _ ≤ 2 * N := by omega
    have hGleR : (G.card : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hGle
    have hx1 : 1 ≤ x := by
      rw [hx]
      have h2 : (2 : ℝ) ≤ 8 * (N : ℝ) / (G.card : ℝ) :=
        (le_div_iff₀ hμ0).mpr (by linarith [hGleR, hNposR])
      linarith
    have hT1 : (T ℝ (m : ℤ)).eval x ≤ (2 * x) ^ m := chebT_eval_le m hx1
    have hμge : (N : ℝ) + 1 - (m : ℝ) ≤ (G.card : ℝ) := by
      have h1 : N + 1 - m ≤ G.card := by omega
      have h2 : ((N + 1 - m : ℕ) : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub (by omega : m ≤ N + 1), Nat.cast_add, Nat.cast_one] at h2
      linarith
    have hkey : 16 * (N : ℝ) / (G.card : ℝ) ≤ 16 * R / (R - (m : ℝ)) := by
      rw [div_le_div_iff₀ hμ0 hRm]
      have h1 : 16 * R * ((N : ℝ) + 1 - (m : ℝ)) ≤ 16 * R * (G.card : ℝ) :=
        mul_le_mul_of_nonneg_left hμge (by linarith [hR])
      have h2 : 16 * (N : ℝ) * (R - (m : ℝ)) ≤ 16 * R * ((N : ℝ) + 1 - (m : ℝ)) := by
        have heq : 16 * R * ((N : ℝ) + 1 - (m : ℝ)) - 16 * (N : ℝ) * (R - (m : ℝ))
            = 16 * (R + (m : ℝ) * ((N : ℝ) - R)) := by ring
        have hmn : (0 : ℝ) ≤ (m : ℝ) * ((N : ℝ) - R) :=
          mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hRN)
        linarith [heq, hmn, hR]
      linarith [h1, h2]
    have h2x : 2 * x ≤ 16 * R / (R - (m : ℝ)) := by
      have h3 : 2 * x = 16 * (N : ℝ) / (G.card : ℝ) - 2 := by
        rw [hx]
        ring
      linarith [h3, hkey]
    have hpow : (2 * x) ^ m ≤ (16 * R / (R - (m : ℝ))) ^ m :=
      pow_le_pow_left₀ (by linarith [hx1]) h2x m
    calc |p.eval (s : ℝ)| ≤ A * (T ℝ (m : ℤ)).eval x := hfin
      _ ≤ A * (2 * x) ^ m := mul_le_mul_of_nonneg_left hT1 hA
      _ ≤ A * (16 * R / (R - (m : ℝ))) ^ m := mul_le_mul_of_nonneg_left hpow hA

end UCPlanar.Support
