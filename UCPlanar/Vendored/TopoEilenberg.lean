/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Bonanno/QuantumZipper/Proofs/Complex/TopoEilenberg.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `QuantumZipper.CA.Topo` is renamed `UCPlanar.Vendored.Topo`, the module paths of
   local imports are changed, and `Set.domRestrict` and `continuousOn_iff_continuous_domRestrict` are
   replaced by `Set.restrict` and `continuousOn_iff_continuous_restrict`, their counterparts in the
   Mathlib version this repository uses. -/
/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.TopoEilenberg at commit 31e7483; only the module paths of local imports are changed. -/
import UCPlanar.Vendored.TopoDegree
import UCPlanar.Vendored.TopoSep
import Mathlib.Analysis.Complex.Tietze

/-!
# Eilenberg's criterion (EXT-CA node T2)

For a compact `J ⊆ ℂ` and `a, b ∉ J`, the points `a` and `b` lie in the same component of `Jᶜ`
iff `z ↦ (z - a) / (z - b)` has a continuous logarithm on `J`.

* `hasLogOn_of_not_separates` (easy direction, T2(i));
* `not_separates_of_hasLogOn` (hard direction, T2(ii)).

**Source.** R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021),
Exercise 4.37(i) (S. Eilenberg 1936), printed p. 215, PDF p. 240, with its hints.

* (⇒) Burckel's hint points to the proof of 4.30 (join `a` to `b` in `ℂ \ K` by small steps, each
  factor `(z - a_k)/(z - a_{k+1})` has a principal logarithm on `K`). We use the same small-step
  factor (`hasLogOn_ratio_step`), organized as a clopen argument: the set of `c ∉ J` for which
  `(z - a)/(z - c)` has a log on `J` is open and has open complement in `Jᶜ` (own organization of
  the argument, avoiding paths).
* (⇐) Burckel's hint: extend the log (Tietze, 4.25), and if `a` lies in a bounded component `C`
  of `ℂ \ K` not containing `b`, then `z - a` has a zero-free continuous extension to `K ∪ C`,
  contradicting 4.31 (no retraction / degree). Here 4.31 is proved inline with the loop degree of
  node T1: the function `Φ = (z - a) · e^{-G(z)} / (z - b)` on `C`, `Φ = 1` off `C`, is continuous
  and zero-free on `ℂ \ {a}`, its loops around `a` have degree `1` on small circles and `0` on
  large ones, contradicting homotopy invariance (`loopDeg_homotopy`). If `a`'s component is
  unbounded, then `b`'s is bounded (T6) and we swap `a`, `b`.
-/

open Complex Set Metric Real

namespace UCPlanar.Vendored.Topo

/-- Small step: if `‖b - c‖ < ‖z - c‖` on `J`, a log of `(z - a)/(z - b)` gives one of
`(z - a)/(z - c)` (multiply by the principal log of `(z - b)/(z - c)`). -/
theorem hasLogOn_ratio_step {J : Set ℂ} {a b c : ℂ} (h : ∀ z ∈ J, ‖b - c‖ < ‖z - c‖)
    (hb : HasLogOn (fun z => (z - a) / (z - b)) J) :
    HasLogOn (fun z => (z - a) / (z - c)) J := by
  obtain ⟨L, hLc, hL⟩ := hb
  have hzc : ∀ z ∈ J, z - c ≠ 0 := fun z hz h0 => by
    have := h z hz; rw [h0, norm_zero] at this; exact (norm_nonneg _).not_gt this
  have hzb : ∀ z ∈ J, z - b ≠ 0 := fun z hz h0 => by
    have := h z hz; rw [sub_eq_zero.1 h0] at this; exact lt_irrefl _ this
  have hq : ∀ z ∈ J, (z - b) / (z - c) ∈ slitPlane := by
    intro z hz
    have e : (z - b) / (z - c) = 1 + (c - b) / (z - c) := by
      field_simp [hzc z hz]; ring
    rw [e]
    apply mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hzc z hz)), norm_sub_rev]
    exact h z hz
  refine ⟨fun z => L z + Complex.log ((z - b) / (z - c)), ?_, fun z hz => ?_⟩
  · refine hLc.add (ContinuousOn.clog ?_ hq)
    exact (continuousOn_id.sub continuousOn_const).div (continuousOn_id.sub continuousOn_const)
      hzc
  · simp only
    rw [Complex.exp_add, hL z hz, Complex.exp_log (slitPlane_ne_zero (hq z hz))]
    field_simp [hzb z hz, hzc z hz]

/-- Near a point `c ∉ J` (`J` closed), whether `(z - a)/(z - b)` has a log on `J` does not
depend on `b`. -/
theorem exists_ball_hasLogOn_iff {J : Set ℂ} (hJ : IsClosed J) (a : ℂ) {c : ℂ} (hc : c ∉ J) :
    ∃ r > 0, ball c r ⊆ Jᶜ ∧ ∀ b ∈ ball c r,
      (HasLogOn (fun z => (z - a) / (z - b)) J ↔ HasLogOn (fun z => (z - a) / (z - c)) J) := by
  obtain ⟨r, hr, hrJ⟩ := Metric.isOpen_iff.1 hJ.isOpen_compl c hc
  refine ⟨r / 2, by positivity, (ball_subset_ball (by linarith)).trans hrJ, fun b hb => ?_⟩
  rw [mem_ball, dist_eq_norm] at hb
  have hzr : ∀ z ∈ J, r ≤ ‖z - c‖ := fun z hz => by
    by_contra hlt
    exact hrJ (by rw [mem_ball, dist_eq_norm]; linarith) hz
  constructor
  · exact hasLogOn_ratio_step fun z hz => by linarith [hzr z hz]
  · refine hasLogOn_ratio_step fun z hz => ?_
    have := norm_sub_norm_le (z - c) (b - c)
    rw [show z - c - (b - c) = z - b by ring] at this
    rw [norm_sub_rev]
    linarith [hzr z hz]

/-- **T2(i)** (Eilenberg, easy direction; Burckel Ex. 4.37(i)). If `b` lies in the component of
`Jᶜ` containing `a`, then `(z - a)/(z - b)` has a continuous logarithm on `J`. -/
theorem hasLogOn_of_not_separates {J : Set ℂ} {a b : ℂ} (hJ : IsCompact J)
    (hab : b ∈ connectedComponentIn Jᶜ a) : HasLogOn (fun z => (z - a) / (z - b)) J := by
  have hJc := hJ.isClosed
  have ha : a ∉ J := connectedComponentIn_nonempty_iff.1 ⟨b, hab⟩
  let P : ℂ → Prop := fun c => HasLogOn (fun z => (z - a) / (z - c)) J
  have hopen : ∀ Q : Prop → Prop, (∀ p q : Prop, (p ↔ q) → (Q p ↔ Q q)) →
      IsOpen {c | c ∉ J ∧ Q (P c)} := by
    intro Q hQ
    refine Metric.isOpen_iff.2 fun c ⟨hc, hQc⟩ => ?_
    obtain ⟨r, hr, hrJ, hiff⟩ := exists_ball_hasLogOn_iff hJc a hc
    exact ⟨r, hr, fun b hb => ⟨hrJ hb, (hQ _ _ (hiff b hb)).2 hQc⟩⟩
  have hU := hopen id (fun _ _ h => h)
  have hV := hopen Not (fun _ _ h => not_congr h)
  have hPa : P a := ⟨fun _ => 0, continuousOn_const, fun z hz => by
    have : z - a ≠ 0 := sub_ne_zero.2 fun h => ha (h ▸ hz)
    simp [div_self this]⟩
  have hsub := (isPreconnected_connectedComponentIn (F := Jᶜ) (x := a)).subset_left_of_subset_union
    hU hV (Set.disjoint_left.2 fun c h1 h2 => h2.2 h1.2)
    (fun c hc => by
      have hcJ : c ∉ J := connectedComponentIn_subset _ _ hc
      by_cases hPc : P c
      · exact Or.inl ⟨hcJ, hPc⟩
      · exact Or.inr ⟨hcJ, hPc⟩)
    ⟨a, mem_connectedComponentIn ha, ha, hPa⟩
  exact (hsub hab).2

/-- The frontier of a component of the complement of a closed set lies in the set. -/
theorem frontier_connectedComponentIn_compl_subset {J : Set ℂ} (hJ : IsClosed J) (a : ℂ) :
    frontier (connectedComponentIn Jᶜ a) ⊆ J := by
  intro z hz
  by_contra hzJ
  have hVo : IsOpen (connectedComponentIn Jᶜ a) := hJ.isOpen_compl.connectedComponentIn
  have hzV : z ∉ connectedComponentIn Jᶜ a := by rw [hVo.frontier_eq] at hz; exact hz.2
  have hWo : IsOpen (connectedComponentIn Jᶜ z) := hJ.isOpen_compl.connectedComponentIn
  obtain ⟨w, hwW, hwV⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _ hWo
    (mem_connectedComponentIn hzJ)
  apply hzV
  rw [connectedComponentIn_eq hwV, ← connectedComponentIn_eq hwW]
  exact mem_connectedComponentIn hzJ

/-- Core of T2(ii) (Burckel 4.31 via loop degree): if `a`'s component `V` of `Jᶜ` is bounded and
does not contain `b ∉ J`, then `(z - a)/(z - b)` has no continuous logarithm on `J`. -/
theorem false_of_hasLogOn_of_isBounded {J : Set ℂ} {a b : ℂ} (hJ : IsClosed J) (ha : a ∉ J)
    (hb : b ∉ J) (hbV : b ∉ connectedComponentIn Jᶜ a)
    (hV : Bornology.IsBounded (connectedComponentIn Jᶜ a))
    (h : HasLogOn (fun z => (z - a) / (z - b)) J) : False := by
  classical
  set V := connectedComponentIn Jᶜ a with hVdef
  have hVo : IsOpen V := hJ.isOpen_compl.connectedComponentIn
  have haV : a ∈ V := mem_connectedComponentIn ha
  have hfr : frontier V ⊆ J := frontier_connectedComponentIn_compl_subset hJ a
  have hbcl : b ∉ closure V := fun hbc => hb (hfr (by rw [hVo.frontier_eq]; exact ⟨hbc, hbV⟩))
  have hab : a ≠ b := fun e => hbV (e ▸ haV)
  obtain ⟨L, hLc, hL⟩ := h
  -- Tietze extension of the logarithm
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hJ
    (⟨J.restrict L, continuousOn_iff_continuous_restrict.1 hLc⟩ : C(J, ℂ))
  have hGL : ∀ z ∈ J, G z = L z := fun z hz => by
    have := DFunLike.congr_fun hG ⟨z, hz⟩
    exact this.trans rfl
  -- the pasted function
  let c : ℂ → ℂ := fun z => Complex.exp (-G z) / (z - b)
  let Φ : ℂ → ℂ := fun z => if z ∈ V then (z - a) * c z else 1
  have hΦc : Continuous Φ := by
    refine continuous_if (fun z hz => ?_) ?_ continuousOn_const
    · have hzJ : z ∈ J := hfr hz
      have hzb : z - b ≠ 0 := sub_ne_zero.2 fun e => hb (e ▸ hzJ)
      have hza : z - a ≠ 0 := sub_ne_zero.2 fun e => ha (e ▸ hzJ)
      have := hL z hzJ
      simp only at this
      simp only [c, hGL z hzJ, Complex.exp_neg, this]
      field_simp [hzb, hza]
    · refine (continuousOn_id.sub continuousOn_const).mul ?_
      exact (G.continuous.neg.cexp).continuousOn.div (continuousOn_id.sub continuousOn_const)
        fun z hz => sub_ne_zero.2 fun e => hbcl (e ▸ hz)
  have hΦ0 : ∀ z, z ≠ a → Φ z ≠ 0 := by
    intro z hz
    by_cases hzV : z ∈ V
    · simp only [Φ, hzV, ↓reduceIte, c]
      have hzb : z - b ≠ 0 := sub_ne_zero.2 fun e => hbV (e ▸ hzV)
      exact mul_ne_zero (sub_ne_zero.2 hz) (div_ne_zero (Complex.exp_ne_zero _) hzb)
    · simp [Φ, hzV, ↓reduceIte]
  -- small circles
  have hca : c a ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) (sub_ne_zero.2 hab)
  have hcc : ContinuousAt c a :=
    (G.continuous.neg.cexp.continuousAt).div (continuousAt_id.sub continuousAt_const)
      (sub_ne_zero.2 hab)
  obtain ⟨ε, hε, hεc⟩ := Metric.continuousAt_iff.1 hcc ‖c a‖ (norm_pos_iff.2 hca)
  obtain ⟨ε', hε', hε'V⟩ := Metric.isOpen_iff.1 hVo a haV
  set r := min ε ε' / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by rw [hr]; linarith [min_le_left ε ε']
  have hrε' : r < ε' := by rw [hr]; linarith [min_le_right ε ε']
  -- large circles
  obtain ⟨M, hM⟩ := hV.subset_closedBall 0
  set R := |M| + ‖a‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  have hRout : ∀ θ : ℝ, circleMap a R θ ∉ V := fun θ hθ => by
    have h1 := hM hθ
    rw [mem_closedBall_zero_iff] at h1
    have h2 : ‖circleMap a R θ - a‖ ≤ ‖circleMap a R θ‖ + ‖a‖ := norm_sub_le _ _
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR0] at h2
    linarith [le_abs_self M]
  -- the homotopy of circles
  let ρ : unitInterval → ℝ := fun s => (1 - (s : ℝ)) * r + (s : ℝ) * R
  have hρ : ∀ s, ρ s ≠ 0 := fun s => by
    apply ne_of_gt
    simp only [ρ]
    rcases (s.2.1 : (0:ℝ) ≤ s).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using hr0
    · have := mul_pos h0 hR0
      have := mul_nonneg (sub_nonneg.2 (s.2.2 : (s:ℝ) ≤ 1)) hr0.le
      linarith
  let H : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => Φ (circleMap a (ρ p.2) (2 * π * (p.1 : ℝ))), by
      refine hΦc.comp ?_
      simp only [circleMap, ρ]
      fun_prop⟩
  have hH0 : ∀ p, H p ≠ 0 := fun p => hΦ0 _ (circleMap_ne_center (hρ p.2))
  have hHc : ∀ s, H (0, s) = H (1, s) := fun s => by
    simp only [H, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero, mul_one]
    rw [← (periodic_circleMap a (ρ s)) 0, zero_add]
  have hdeg := loopDeg_homotopy H hH0 hHc
  -- degree 0 on the large circle
  have hdeg1 : loopDeg (slice H 1) (fun _ => hH0 _) = 0 := by
    refine loopDeg_unique _ _ (by simpa [slice] using hHc 1) (L := fun _ => 0) continuous_const
      (fun t => ?_) (by simp)
    have : ρ 1 = R := by simp [ρ]
    simp [slice, H, Φ, this, hRout]
  -- degree 1 on the small circle
  let δ : C(unitInterval, ℂ) := circleLoop r * ContinuousMap.const unitInterval (c a)
  have hδ0 : ∀ t, δ t ≠ 0 := fun t => by
    simpa [δ] using mul_ne_zero (circleLoop_ne_zero hr0.ne' t) hca
  have hcl : circleLoop r 0 = circleLoop r 1 := by
    simp only [circleLoop, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one, mul_zero,
      mul_one]
    rw [← (periodic_circleMap 0 r) 0, zero_add]
  have hδc : δ 0 = δ 1 := by
    simp only [δ, ContinuousMap.mul_apply, ContinuousMap.const_apply, hcl]
  have hdegδ : loopDeg δ hδ0 = 1 := by
    have e := loopDeg_mul (circleLoop r) (ContinuousMap.const unitInterval (c a))
      (circleLoop_ne_zero hr0.ne') (fun _ => hca) hcl rfl
    rw [loopDeg_circle hr0.ne', loopDeg_const] at e
    simpa using e
  have hdeg0 : loopDeg (slice H 0) (fun _ => hH0 _) = 1 := by
    rw [← hdegδ]
    refine loopDeg_eq_of_norm_sub_lt _ _ _ _ (by simpa [slice] using hHc 0) hδc fun t => ?_
    have hρ0 : ρ 0 = r := by simp [ρ]
    set z := circleMap a r (2 * π * (t : ℝ)) with hz
    have hza : z - a = circleMap 0 r (2 * π * (t : ℝ)) := circleMap_sub_center _ _ _
    have hzn : ‖z - a‖ = r := by rw [hza, norm_circleMap_zero, abs_of_pos hr0]
    have hzV : z ∈ V := hε'V (by rw [mem_ball, dist_eq_norm, hzn]; exact hrε')
    have hcz : ‖c z - c a‖ < ‖c a‖ := by
      have := hεc (x := z) (by rw [dist_eq_norm, hzn]; exact hrε)
      rwa [dist_eq_norm] at this
    have e1 : slice H 0 t = (z - a) * c z := by
      show Φ (circleMap a (ρ 0) (2 * π * (t : ℝ))) = _
      rw [hρ0, ← hz]
      simp only [Φ, hzV, ↓reduceIte]
    have e2 : δ t = (z - a) * c a := by
      show circleMap 0 r (2 * π * (t : ℝ)) * c a = _
      rw [hza]
    rw [e1, e2, ← mul_sub, norm_mul, norm_mul, hzn]
    exact mul_lt_mul_of_pos_left hcz hr0
  rw [hdeg0, hdeg1] at hdeg
  exact one_ne_zero hdeg

/-- **T2(ii)** (Eilenberg, hard direction; Burckel Ex. 4.37(i)). If `(z - a)/(z - b)` has a
continuous logarithm on the compact set `J` (`a, b ∉ J`), then `J` does not separate `a` and `b`. -/
theorem not_separates_of_hasLogOn {J : Set ℂ} {a b : ℂ} (hJ : IsCompact J) (ha : a ∉ J)
    (hb : b ∉ J) (h : HasLogOn (fun z => (z - a) / (z - b)) J) :
    b ∈ connectedComponentIn Jᶜ a := by
  by_contra hbV
  by_cases hV : Bornology.IsBounded (connectedComponentIn Jᶜ a)
  · exact false_of_hasLogOn_of_isBounded hJ.isClosed ha hb hbV hV h
  -- otherwise `b`'s component is bounded (only one unbounded component, T6); swap `a` and `b`
  obtain ⟨R, hR⟩ := hJ.isBounded.subset_ball (0 : ℂ)
  set p : ℂ := ((|R| + 1 : ℝ) : ℂ)
  have hp : R < ‖p‖ := by
    simp only [p, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]; linarith [le_abs_self R]
  have hunb : ∀ x ∉ J, ¬ Bornology.IsBounded (connectedComponentIn Jᶜ x) →
      x ∈ connectedComponentIn Jᶜ p := fun x hx hxb =>
    subset_connectedComponentIn_compl_of_unbounded hR isPreconnected_connectedComponentIn hxb
      (Set.disjoint_left.2 fun _ hz => connectedComponentIn_subset _ _ hz) hp
      (mem_connectedComponentIn hx)
  have hapc := hunb a ha hV
  have hW : Bornology.IsBounded (connectedComponentIn Jᶜ b) := by
    by_contra hW
    apply hbV
    rw [← connectedComponentIn_eq hapc]
    exact hunb b hb hW
  have haW : a ∉ connectedComponentIn Jᶜ b := fun h' => hbV (by
    rw [← connectedComponentIn_eq h']; exact mem_connectedComponentIn hb)
  obtain ⟨L, hLc, hL⟩ := h
  refine false_of_hasLogOn_of_isBounded hJ.isClosed hb ha haW hW
    ⟨fun z => -L z, hLc.neg, fun z hz => ?_⟩
  rw [Complex.exp_neg, hL z hz, inv_div]

end UCPlanar.Vendored.Topo
