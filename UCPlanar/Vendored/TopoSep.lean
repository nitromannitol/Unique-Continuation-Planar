/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Bonanno/QuantumZipper/Proofs/Complex/TopoSep.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `QuantumZipper.CA.Topo` is renamed `UCPlanar.Vendored.Topo`, and the module paths
   of local imports are changed. -/
/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.TopoSep at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Separation predicate, the unbounded component (T6), and ULC sets (T7)

EXT_CA blueprint nodes T6 and T7 (task CA-T67).

* `Separates J a b`: `a, b ∉ J` and `b` is not in the component of `Jᶜ` containing `a`.
* **T6.** If `J ⊆ ball 0 R`, all points of norm `> R` lie in one component of `Jᶜ`
  (`mem_connectedComponentIn_compl_of_lt_norm`), and every preconnected unbounded set disjoint
  from `J` lies in it (`subset_connectedComponentIn_compl_of_unbounded`). Own elementary proof:
  `{z | R < ‖z‖}` is the continuous image of `Ioi R × ℝ` under `(r, θ) ↦ r e^{iθ}`.
* **T7.** Uniform local connectedness `ULC` (Newman, *Elements of the Topology of Plane Sets of
  Points*, 2nd ed. 1964, Ch. VI §13, p. 160 (PDF p. 83); Pommerenke, *Boundary Behaviour of
  Conformal Maps* (1992), §2.2, p. 22). We use `diam β ≤ ε` instead of Newman's `< ε`
  (equivalent as a property of `E`).
  - `ULC.of_isCompact_of_forall`: a compact set that is "lc at each of its points" in Newman's
    sense is ULC. This is Newman Thm 13.1 (2) / Cor. 1 (p. 160); we follow the same compactness
    argument, phrased with the Lebesgue number lemma instead of subsequences.
  - `ULC.of_isCompact_locallyConnected`: compact + locally connected ⇒ ULC (Newman Cor. 1).
  - `ULC.image_Icc`: the image of a continuous path `[0,1] → ℂ` (not necessarily injective) is ULC.
    Own elementary proof: lc at `γ s₀` via uniform continuity of `γ` and compactness of
    `{t | dist(t, γ⁻¹{γ s₀}) ≥ η}`.
  - `ULC.union_of_isCompact_of_isClosed` / `ULC.union`: union of two ULC sets, one compact and
    one closed. Own elementary proof: a point of `E₁` close to `E₂` is close to `E₁ ∩ E₂`
    (compactness), and the two connecting sets are glued at a point of `E₁ ∩ E₂`. The
    hypotheses `(E₁ ∩ E₂).Finite`, `(E₁ ∩ E₂).Nonempty` of the task statement are not needed.
  - `ULC.sphere`: circles are ULC (image of `[0,1]` under `t ↦ c + r e^{2πit}`).
-/

open Set Metric

namespace UCPlanar.Vendored.Topo

/-- The exterior `{z | R < ‖z‖}` of a disk is preconnected. -/
theorem isPreconnected_setOf_lt_norm (R : ℝ) : IsPreconnected {z : ℂ | R < ‖z‖} := by
  have h : {z : ℂ | R < ‖z‖} =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (Ioi R ×ˢ univ) := by
    ext z
    constructor
    · intro hz
      exact ⟨(‖z‖, Complex.arg z), ⟨hz, trivial⟩, Complex.norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨⟨r, θ⟩, ⟨hr, -⟩, rfl⟩
      simp only [mem_setOf_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      exact lt_of_lt_of_le hr (le_abs_self r)
  rw [h]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _ (by fun_prop : Continuous
    (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I))).continuousOn

theorem setOf_lt_norm_subset_compl {J : Set ℂ} {R : ℝ} (hJ : J ⊆ Metric.ball 0 R) :
    {z : ℂ | R < ‖z‖} ⊆ Jᶜ := fun z hz hzJ => by
  have := hJ hzJ
  rw [mem_ball_zero_iff] at this
  exact lt_asymm this hz

/-- **T6 (b).** A preconnected unbounded set disjoint from `J ⊆ ball 0 R` lies in the unbounded
component of `Jᶜ`. -/
theorem subset_connectedComponentIn_compl_of_unbounded {J S : Set ℂ} {R : ℝ}
    (hJ : J ⊆ Metric.ball 0 R) (hS : IsPreconnected S) (hSu : ¬ Bornology.IsBounded S)
    (hSJ : Disjoint S J) {a : ℂ} (ha : R < ‖a‖) : S ⊆ connectedComponentIn Jᶜ a := by
  obtain ⟨s, hsS, hs⟩ : ∃ s ∈ S, R < ‖s‖ := by
    by_contra h
    simp only [not_exists, not_and, not_lt] at h
    exact hSu ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz => by
      rw [mem_closedBall_zero_iff]; exact h z hz)
  have hU : IsPreconnected (S ∪ {z : ℂ | R < ‖z‖}) :=
    hS.union s hsS hs (isPreconnected_setOf_lt_norm R)
  have hUJ : S ∪ {z : ℂ | R < ‖z‖} ⊆ Jᶜ :=
    union_subset (fun z hz hzJ => Set.disjoint_left.1 hSJ hz hzJ) (setOf_lt_norm_subset_compl hJ)
  exact subset_union_left.trans (hU.subset_connectedComponentIn (Or.inr ha) hUJ)

/-- **T7.** Uniform local connectedness (Newman 1964, VI §13, p. 160; Pommerenke 1992, p. 22). -/
def ULC (E : Set ℂ) : Prop := ∀ ε > 0, ∃ δ > 0, ∀ a ∈ E, ∀ b ∈ E, dist a b < δ →
  ∃ β ⊆ E, IsPreconnected β ∧ a ∈ β ∧ b ∈ β ∧ Metric.diam β ≤ ε

/-- A compact set which is locally connected at each of its points (in Newman's sense: points
near `x` are joined to `x` inside `E` by preconnected sets of small diameter) is ULC.
Newman (1964), Thm 13.1 (2) and Cor. 1, p. 160. -/
theorem ULC.of_isCompact_of_forall {E : Set ℂ} (hE : IsCompact E)
    (h : ∀ x ∈ E, ∀ ε > 0, ∃ ρ > 0, ∀ a ∈ E, dist a x < ρ →
      ∃ β ⊆ E, IsPreconnected β ∧ x ∈ β ∧ a ∈ β ∧ Metric.diam β ≤ ε) : ULC E := by
  intro ε hε
  choose! ρ hρpos hρ using fun x hx => h x hx (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric
    (c := fun x : E => ball (x : ℂ) (ρ x)) hE (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hρpos x hx)⟩)
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  obtain ⟨⟨x, hx⟩, hx'⟩ := hcov a ha
  have ha' : dist a x < ρ x := hx' (mem_ball_self hδ)
  have hb' : dist b x < ρ x := hx' (by rw [mem_ball, dist_comm]; exact hab)
  obtain ⟨β₁, h₁E, h₁c, h₁x, h₁a, h₁d⟩ := hρ x hx a ha ha'
  obtain ⟨β₂, h₂E, h₂c, h₂x, h₂b, h₂d⟩ := hρ x hx b hb hb'
  refine ⟨β₁ ∪ β₂, union_subset h₁E h₂E, h₁c.union x h₁x h₂x h₂c, Or.inl h₁a, Or.inr h₂b, ?_⟩
  calc diam (β₁ ∪ β₂) ≤ diam β₁ + dist x x + diam β₂ := diam_union h₁x h₂x
    _ ≤ ε := by rw [dist_self]; linarith

/-- The image of a continuous path `[0,1] → ℂ` is ULC. Own elementary proof (the path need not be
injective): uniform continuity of `γ` plus `ULC.of_isCompact_of_forall`. -/
theorem ULC.image_Icc {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc 0 1)) :
    ULC (γ '' Set.Icc 0 1) := by
  have hK : IsCompact (Icc (0 : ℝ) 1) := isCompact_Icc
  refine ULC.of_isCompact_of_forall (hK.image_of_continuousOn hγ) ?_
  rintro _ ⟨s₀, -, rfl⟩ ε hε
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hγ) (ε / 2) (half_pos hε)
  set P : Set ℝ := {s ∈ Icc (0 : ℝ) 1 | γ s = γ s₀} with hP_def
  set C : Set ℝ := Icc (0 : ℝ) 1 \ thickening η P with hC_def
  have hC : IsCompact C := hK.diff isOpen_thickening
  have hCγ : IsClosed (γ '' C) := (hC.image_of_continuousOn (hγ.mono sdiff_subset)).isClosed
  have hnot : γ s₀ ∉ γ '' C := by
    rintro ⟨t, ⟨ht, htP⟩, hteq⟩
    exact htP (self_subset_thickening hη P ⟨ht, hteq⟩)
  obtain ⟨ρ, hρ, hρC⟩ := Metric.isOpen_iff.1 hCγ.isOpen_compl _ hnot
  refine ⟨ρ, hρ, ?_⟩
  rintro _ ⟨t, ht, rfl⟩ hdist
  have htC : t ∉ C := fun htC => hρC (mem_ball.2 hdist) ⟨t, htC, rfl⟩
  obtain ⟨s, ⟨hs, hsP⟩, hts⟩ : ∃ s ∈ P, dist t s < η := by
    by_contra hcon
    exact htC ⟨ht, fun hth => hcon (mem_thickening_iff.1 hth)⟩
  have hsub : uIcc s t ⊆ Icc 0 1 := uIcc_subset_Icc hs ht
  refine ⟨γ '' uIcc s t, image_mono hsub, isPreconnected_uIcc.image _ (hγ.mono hsub),
    ⟨s, left_mem_uIcc, hsP⟩, ⟨t, right_mem_uIcc, rfl⟩, ?_⟩
  refine (diam_le_of_subset_closedBall (x := γ s₀) (half_pos hε).le ?_).trans (by linarith)
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_closedBall, ← hsP]
  refine (hηu u (hsub hu) s hs ?_).le
  have := abs_sub_left_of_mem_uIcc hu
  rw [Real.dist_eq] at hts ⊢
  linarith

/-- Union of a compact ULC set and a closed ULC set is ULC. Own elementary proof. -/
theorem ULC.union_of_isCompact_of_isClosed {E₁ E₂ : Set ℂ} (h₁ : IsCompact E₁)
    (h₂ : IsClosed E₂) (u₁ : ULC E₁) (u₂ : ULC E₂) : ULC (E₁ ∪ E₂) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hu₁⟩ := u₁ (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hu₂⟩ := u₂ (ε / 2) (half_pos hε)
  set η := min δ₁ δ₂ / 2 with hη_def
  have hη : 0 < η := by positivity
  set C := E₁ \ thickening η (E₁ ∩ E₂) with hC_def
  have hC : IsCompact C := h₁.diff isOpen_thickening
  obtain ⟨d, hd, hdC⟩ := hC.exists_thickening_subset_open h₂.isOpen_compl (by
    rintro x ⟨hx1, hxt⟩ hx2
    exact hxt (self_subset_thickening hη _ ⟨hx1, hx2⟩))
  have hmin1 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
  have hmin2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
  have hηd : min η d ≤ η := min_le_left η d
  have hdd : min η d ≤ d := min_le_right η d
  refine ⟨min η d, lt_min hη hd, ?_⟩
  have cross : ∀ a ∈ E₁, ∀ b ∈ E₂, dist a b < min η d →
      ∃ β ⊆ E₁ ∪ E₂, IsPreconnected β ∧ a ∈ β ∧ b ∈ β ∧ diam β ≤ ε := by
    intro a ha b hb hab
    have haC : a ∉ C := fun haC => hdC (mem_thickening_iff.2
      ⟨a, haC, by rw [dist_comm]; exact hab.trans_le hdd⟩) hb
    obtain ⟨p, ⟨hp1, hp2⟩, hap⟩ : ∃ p ∈ E₁ ∩ E₂, dist a p < η := by
      by_contra hcon
      exact haC ⟨ha, fun hth => hcon (mem_thickening_iff.1 hth)⟩
    obtain ⟨β₁, hβ₁E, hβ₁c, hβ₁a, hβ₁p, hβ₁d⟩ := hu₁ a ha p hp1 (by linarith)
    obtain ⟨β₂, hβ₂E, hβ₂c, hβ₂p, hβ₂b, hβ₂d⟩ := hu₂ p hp2 b hb (by
      calc dist p b ≤ dist p a + dist a b := dist_triangle _ _ _
        _ < δ₂ := by rw [dist_comm]; linarith)
    refine ⟨β₁ ∪ β₂, union_subset_union hβ₁E hβ₂E, hβ₁c.union p hβ₁p hβ₂p hβ₂c, Or.inl hβ₁a,
      Or.inr hβ₂b, ?_⟩
    calc diam (β₁ ∪ β₂) ≤ diam β₁ + dist p p + diam β₂ := diam_union hβ₁p hβ₂p
      _ ≤ ε := by rw [dist_self]; linarith
  rintro a (ha | ha) b (hb | hb) hab
  · obtain ⟨β, hβE, hβc, hβa, hβb, hβd⟩ := hu₁ a ha b hb (by linarith)
    exact ⟨β, hβE.trans subset_union_left, hβc, hβa, hβb, hβd.trans (by linarith)⟩
  · exact cross a ha b hb hab
  · obtain ⟨β, hβE, hβc, hβb, hβa, hβd⟩ := cross b hb a ha (by rwa [dist_comm])
    exact ⟨β, hβE, hβc, hβa, hβb, hβd⟩
  · obtain ⟨β, hβE, hβc, hβa, hβb, hβd⟩ := hu₂ a ha b hb (by linarith)
    exact ⟨β, hβE.trans subset_union_right, hβc, hβa, hβb, hβd.trans (by linarith)⟩

/-- **T7 (unions).** The task's statement; the hypotheses `hfin`, `hne` are not needed
(see `ULC.union_of_isCompact_of_isClosed`). -/
theorem ULC.union {E₁ E₂ : Set ℂ} (h₁ : IsCompact E₁) (h₂ : IsCompact E₂) (u₁ : ULC E₁)
    (u₂ : ULC E₂) (_hfin : (E₁ ∩ E₂).Finite) (_hne : (E₁ ∩ E₂).Nonempty) : ULC (E₁ ∪ E₂) :=
  ULC.union_of_isCompact_of_isClosed h₁ h₂.isClosed u₁ u₂

/-- **T7 (circles).** Every sphere in `ℂ` is ULC. -/
theorem ULC.sphere (c : ℂ) (r : ℝ) : ULC (Metric.sphere c r) := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [sphere_eq_empty_of_neg hr]
    intro ε _
    exact ⟨1, one_pos, fun a ha => ha.elim⟩
  · have hs : Metric.sphere c r = (fun t : ℝ => circleMap c r (2 * Real.pi * t)) '' Icc 0 1 := by
      apply Subset.antisymm
      · intro z hz
        rw [← abs_of_nonneg hr, ← image_circleMap_Ioc] at hz
        obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
        have hπ : 0 < 2 * Real.pi := by positivity
        refine ⟨θ / (2 * Real.pi), ⟨div_nonneg h0.le hπ.le, ?_⟩, ?_⟩
        · rw [div_le_one hπ]
          exact h1
        · show circleMap c r (2 * Real.pi * (θ / (2 * Real.pi))) = circleMap c r θ
          congr 1
          field_simp
      · rintro _ ⟨t, -, rfl⟩
        exact circleMap_mem_sphere c hr _
    rw [hs]
    exact ULC.image_Icc ((continuous_circleMap c r).comp
      (continuous_const.mul continuous_id)).continuousOn

end UCPlanar.Vendored.Topo
