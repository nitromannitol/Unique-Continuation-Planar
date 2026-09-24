/- The local structure of the drawing at a point interior to one arc: exactly two segments
radiate from such a point, which is what the corner theorem consumes, so the frontier of a face
is covered by whole arcs. -/
import UCPlanar.Support.TopoCorner
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

/-- **A continuous map injective on a compact set is an embedding there.**  Points of the image
close to the image of a parameter come from parameters close to it. -/
theorem exists_ball_image_subset {φ : ℝ → UCPlanar.Plane} (hc : Continuous φ)
    {C : Set ℝ} (hC : IsCompact C) (hinj : Set.InjOn φ C)
    {J : Set ℝ} (hJ : IsOpen J) {t₀ : ℝ} (ht₀C : t₀ ∈ C) (ht₀ : t₀ ∈ J) :
    ∃ ε > 0, Metric.ball (φ t₀) ε ∩ φ '' C ⊆ φ '' (C ∩ J) := by
  have hK : IsCompact (C \ J) := hC.diff hJ
  have him : IsClosed (φ '' (C \ J)) := (hK.image hc).isClosed
  have hnot : φ t₀ ∉ φ '' (C \ J) := by
    rintro ⟨s, hs, hse⟩
    have hst : s = t₀ := hinj hs.1 ht₀C hse
    exact hs.2 (by rw [hst]; exact ht₀)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp him.isOpen_compl _ hnot
  refine ⟨ε, hε, ?_⟩
  rintro x ⟨hxb, s, hsC, rfl⟩
  by_contra hcon
  exact hball hxb ⟨s, ⟨hsC, fun hsJ => hcon ⟨s, ⟨hsC, hsJ⟩, rfl⟩⟩, rfl⟩

/-- A point of a segment lies on the ray from its first end towards the second. -/
theorem sameRay_sub_of_mem_segment {p d x : UCPlanar.Plane} (hx : x ∈ segment ℝ p d) :
    SameRay ℝ (x - p) (d - p) := by
  have h := (mem_segment_iff_sameRay (𝕜 := ℝ)).mp hx
  have h2 := (SameRay.refl (x - p)).add_right h
  have : x - p + (d - x) = d - p := by abel
  rwa [this] at h2

/-- A point on the ray towards `d` and no farther than `d` lies on the segment. -/
theorem mem_segment_of_sameRay {p d x : UCPlanar.Plane} (h : SameRay ℝ (x - p) (d - p))
    (hn : ‖x - p‖ ≤ ‖d - p‖) : x ∈ segment ℝ p d := by
  rcases eq_or_ne x p with hxe | hxp
  · rw [hxe]; exact left_mem_segment ℝ p d
  have hx0 : x - p ≠ 0 := sub_ne_zero.mpr hxp
  have hd0 : d - p ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn
    exact hx0 (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := h.exists_pos hx0 hd0
  have hxd : x - p = (r₂ / r₁) • (d - p) := by
    have : (r₁⁻¹ * r₁) • (x - p) = (r₁⁻¹ * r₂) • (d - p) := by
      rw [mul_smul, mul_smul, hr]
    rw [inv_mul_cancel₀ (ne_of_gt hr₁), one_smul] at this
    rw [this, div_eq_inv_mul]
  set t : ℝ := r₂ / r₁ with ht
  have ht0 : 0 < t := div_pos hr₂ hr₁
  have htn : ‖x - p‖ = t * ‖d - p‖ := by
    rw [hxd, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have ht1 : t ≤ 1 := by
    have hdn : 0 < ‖d - p‖ := norm_pos_iff.mpr hd0
    nlinarith [htn, hn]
  refine ⟨1 - t, t, by linarith, le_of_lt ht0, by ring, ?_⟩
  have : x = p + t • (d - p) := by
    rw [← hxd]; abel
  rw [this]
  module

/-- Two vectors on one ray with the same length are equal. -/
theorem eq_of_sameRay_of_norm_eq {u v : UCPlanar.Plane} (h : SameRay ℝ u v)
    (hn : ‖u‖ = ‖v‖) : u = v := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [norm_zero] at hn
    exact (norm_eq_zero.mp hn.symm).symm
  have hv : v ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn
    exact hu (norm_eq_zero.mp hn)
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := h.exists_pos hu hv
  have hnorm : r₁ * ‖u‖ = r₂ * ‖v‖ := by
    have := congrArg norm hr
    rwa [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr₁,
      abs_of_pos hr₂] at this
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hvn : 0 < ‖v‖ := by rw [← hn]; exact hun
  have hr12 : r₁ = r₂ := by
    rw [hn] at hnorm
    exact mul_right_cancel₀ (ne_of_gt hvn) hnorm
  have hkey : (r₁⁻¹ * r₁) • u = (r₁⁻¹ * r₂) • v := by rw [mul_smul, mul_smul, hr]
  rwa [inv_mul_cancel₀ (ne_of_gt hr₁), one_smul, ← hr12,
    inv_mul_cancel₀ (ne_of_gt hr₁), one_smul] at hkey

/-- **A connected piece of a finite radial union stays on one ray.**  The segments from the
centre whose direction differs from a given one form a closed set meeting the others only at the
centre, so a preconnected set avoiding the centre cannot meet both. -/
theorem sameRay_of_preconnected {p : UCPlanar.Plane} {D : Set UCPlanar.Plane} (hD : D.Finite)
    {S : Set UCPlanar.Plane} (hS : IsPreconnected S)
    (hSD : S ⊆ ⋃ d ∈ D, segment ℝ p d) (hSp : p ∉ S)
    {z z' : UCPlanar.Plane} (hz : z ∈ S) (hz' : z' ∈ S) :
    SameRay ℝ (z - p) (z' - p) := by
  by_contra hcon
  set Dg : Set UCPlanar.Plane := {d ∈ D | SameRay ℝ (d - p) (z - p)} with hDg
  set Db : Set UCPlanar.Plane := {d ∈ D | ¬ SameRay ℝ (d - p) (z - p)} with hDb
  have hKg : IsClosed (⋃ d ∈ Dg, segment ℝ p d) :=
    Set.Finite.isClosed_biUnion (hD.subset (fun d hd => hd.1))
      (fun d _ => (isCompact_segmentU p d).isClosed)
  have hKb : IsClosed (⋃ d ∈ Db, segment ℝ p d) :=
    Set.Finite.isClosed_biUnion (hD.subset (fun d hd => hd.1))
      (fun d _ => (isCompact_segmentU p d).isClosed)
  have hne : ∀ x ∈ S, ∀ d ∈ D, x ∈ segment ℝ p d → d ≠ p := by
    intro x hx d _ hxd hdp
    rw [hdp, segment_same, Set.mem_singleton_iff] at hxd
    exact hSp (hxd ▸ hx)
  have hcover : S ⊆ (⋃ d ∈ Dg, segment ℝ p d) ∪ ⋃ d ∈ Db, segment ℝ p d := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := Set.mem_iUnion₂.mp (hSD hx)
    by_cases hsr : SameRay ℝ (d - p) (z - p)
    · exact Or.inl (Set.mem_biUnion ⟨hd, hsr⟩ hxd)
    · exact Or.inr (Set.mem_biUnion ⟨hd, hsr⟩ hxd)
  have hzK : z ∈ ⋃ d ∈ Dg, segment ℝ p d := by
    obtain ⟨d, hd, hzd⟩ := Set.mem_iUnion₂.mp (hSD hz)
    have hdp : d ≠ p := hne z hz d hd hzd
    have hzp : z ≠ p := fun hc => hSp (hc ▸ hz)
    refine Set.mem_biUnion ⟨hd, ?_⟩ hzd
    exact (sameRay_sub_of_mem_segment hzd).symm
  have hz'K : z' ∈ ⋃ d ∈ Db, segment ℝ p d := by
    obtain ⟨d, hd, hz'd⟩ := Set.mem_iUnion₂.mp (hSD hz')
    have hdp : d ≠ p := hne z' hz' d hd hz'd
    refine Set.mem_biUnion ⟨hd, ?_⟩ hz'd
    intro hsr
    exact hcon ((((sameRay_sub_of_mem_segment hz'd).trans hsr)
      (fun hc => absurd (sub_eq_zero.mp hc) hdp)).symm)
  obtain ⟨x, hxS, hx1, hx2⟩ := (isPreconnected_closed_iff.mp hS) _ _ hKg hKb hcover
    ⟨z, hz, hzK⟩ ⟨z', hz', hz'K⟩
  obtain ⟨d₁, hd₁, hxd₁⟩ := Set.mem_iUnion₂.mp hx1
  obtain ⟨d₂, hd₂, hxd₂⟩ := Set.mem_iUnion₂.mp hx2
  have hxp : x ≠ p := fun hc => hSp (hc ▸ hxS)
  have hx0 : x - p ≠ 0 := sub_ne_zero.mpr hxp
  have h1 : SameRay ℝ (d₂ - p) (d₁ - p) :=
    ((sameRay_sub_of_mem_segment hxd₂).symm.trans (sameRay_sub_of_mem_segment hxd₁)
      (fun hc => absurd hc hx0))
  exact hd₂.2 (h1.trans hd₁.2 (fun hc => absurd (sub_eq_zero.mp hc)
    (hne x hxS d₁ hd₁.1 hxd₁)))

/-- **Near a point of the drawing which is not a drawn vertex the drawing is a single arc.**
Only finitely many arcs reach a bounded set and each of the others misses the point, so a small
enough ball meets no arc but the one through it. -/
theorem exists_ball_trace_eq_arcOf (Q : UCPlanar.PeriodicPlaneGraph V) {e : Sym2 V}
    (he : e ∈ Q.graph.edgeSet) {p : UCPlanar.Plane} (hp : p ∈ Q.embedding.arcOf e)
    (hpv : ∀ v : V, p ≠ Q.embedding.pos v) :
    ∃ ε > 0, Metric.ball p ε ∩ Q.embedding.trace = Metric.ball p ε ∩ Q.embedding.arcOf e := by
  obtain ⟨T, hTfin, hTsub, hTcov⟩ := exists_finite_trace_near Q p 1
  set U : Set (Sym2 V) := {f ∈ T | f ≠ e} with hU
  have hUfin : U.Finite := hTfin.subset (fun f hf => hf.1)
  have hUclosed : IsClosed (⋃ f ∈ U, Q.embedding.arcOf f) :=
    hUfin.isClosed_biUnion (fun f hf => (isCompact_arcOf Q.embedding (hTsub hf.1)).isClosed)
  have hpU : p ∉ ⋃ f ∈ U, Q.embedding.arcOf f := by
    intro hc
    obtain ⟨f, hf, hpf⟩ := Set.mem_iUnion₂.mp hc
    obtain ⟨z, -, -, hz⟩ :=
      arcOf_inter_arcOf Q.embedding he (hTsub hf.1) (Ne.symm hf.2) hp hpf
    exact hpv z hz
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl p hpU
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  refine Set.Subset.antisymm ?_ (fun q hq => ⟨hq.1, arcOf_subset_trace Q.embedding hq.2⟩)
  rintro q ⟨hqb, hqt⟩
  refine ⟨hqb, ?_⟩
  have hq1 : q ∈ Metric.closedBall p 1 :=
    Metric.closedBall_subset_closedBall (min_le_right ε₁ 1)
      (Metric.ball_subset_closedBall hqb)
  obtain ⟨f, hf, hqf⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding (hTcov q hq1 hqt)
  by_cases hfe : f = e
  · rwa [hfe] at hqf
  · exact absurd (Set.mem_biUnion (show f ∈ U from ⟨hf, hfe⟩) hqf)
      (hball (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hqb) (min_le_left ε₁ 1))))

variable {G : SimpleGraph V}

/-- The drawing of an edge, parametrized on the whole line through the clamped parameter. -/
noncomputable def arcParam (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    ℝ → UCPlanar.Plane := fun s => E.edge h (Set.projIcc (0:ℝ) 1 zero_le_one s)

theorem continuous_arcParam (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    Continuous (arcParam E h) :=
  (E.edge h).continuous.comp (continuous_projIcc)

theorem arcParam_mem (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) (s : ℝ) :
    arcParam E h s ∈ Set.range (E.edge h) := ⟨_, rfl⟩

theorem arcParam_image (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    arcParam E h '' Set.Icc (0:ℝ) 1 = Set.range (E.edge h) := by
  refine Set.Subset.antisymm (fun q hq => by obtain ⟨s, -, rfl⟩ := hq; exact ⟨_, rfl⟩) ?_
  rintro q ⟨t, rfl⟩
  refine ⟨(t : ℝ), t.2, ?_⟩
  show (E.edge h) (Set.projIcc (0:ℝ) 1 zero_le_one (t : ℝ)) = (E.edge h) t
  rw [Set.projIcc_val]

theorem injOn_arcParam (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    Set.InjOn (arcParam E h) (Set.Icc (0:ℝ) 1) := by
  intro a ha b hb hab
  have := E.edge_injective h hab
  have h1 : Set.projIcc (0:ℝ) 1 zero_le_one a = ⟨a, ha⟩ := Set.projIcc_of_mem _ ha
  have h2 : Set.projIcc (0:ℝ) 1 zero_le_one b = ⟨b, hb⟩ := Set.projIcc_of_mem _ hb
  rw [h1, h2] at this
  exact congrArg Subtype.val this

theorem arcParam_zero (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    arcParam E h 0 = E.pos x := by
  have : Set.projIcc (0:ℝ) 1 zero_le_one 0 = 0 := by
    apply Subtype.ext; simp [Set.projIcc]
  rw [arcParam, this]
  exact (E.edge h).source

theorem arcParam_one (E : UCPlanar.PlaneEmbedding G) {x y : V} (h : G.Adj x y) :
    arcParam E h 1 = E.pos y := by
  have : Set.projIcc (0:ℝ) 1 zero_le_one 1 = 1 := by
    apply Subtype.ext; simp [Set.projIcc]
  rw [arcParam, this]
  exact (E.edge h).target

/-- Scaling both vectors by a positive number does not change the ray relation. -/
theorem sameRay_smul_iff {a b : UCPlanar.Plane} {r : ℝ} (hr : 0 < r) :
    SameRay ℝ (r • a) (r • b) ↔ SameRay ℝ a b := by
  constructor
  · intro hs
    have h2 := (hs.nonneg_smul_left (le_of_lt (inv_pos.mpr hr))).nonneg_smul_right
      (le_of_lt (inv_pos.mpr hr))
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul, one_smul] at h2
  · intro hs
    exact (hs.nonneg_smul_left hr.le).nonneg_smul_right hr.le

/-- **At a point interior to one arc the drawing is exactly two segments radiating from it.**
The two pieces of the arc on either side of the parameter are connected pieces of the drawing
near the point, so each stays on one ray; the two rays differ because the pieces meet a small
circle about the point in different points. -/
theorem exists_two_rays_of_arcParam (Q : UCPlanar.PeriodicPlaneGraph V) {x y : V}
    (h : Q.graph.Adj x y) {p : UCPlanar.Plane} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0:ℝ) 1) (hpt : arcParam Q.embedding h t₀ = p)
    (harc : ∃ ε > 0, Metric.ball p ε ∩ Q.embedding.trace
      = Metric.ball p ε ∩ Set.range (Q.embedding.edge h)) :
    ∃ ε > 0, ∃ d₁ d₂ : UCPlanar.Plane, p ≠ d₁ ∧ p ≠ d₂ ∧
      (∀ t : ℝ, 0 < t → d₂ ≠ p + t • (d₁ - p)) ∧
      Metric.ball p ε ∩ Q.embedding.trace
        = Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
  classical
  obtain ⟨εa, hεa, harceq⟩ := harc
  obtain ⟨ε₀, hε₀, D, hDfin, hDeq⟩ := exists_radial_local Q p
  set φ : ℝ → UCPlanar.Plane := arcParam Q.embedding h with hφdef
  have hcont : Continuous φ := continuous_arcParam _ _
  have hinj : Set.InjOn φ (Set.Icc (0:ℝ) 1) := injOn_arcParam _ _
  have himg : φ '' Set.Icc (0:ℝ) 1 = Set.range (Q.embedding.edge h) := arcParam_image _ _
  have hφtrace : ∀ s, φ s ∈ Q.embedding.trace :=
    fun s => Or.inr ⟨x, y, h, arcParam_mem Q.embedding h s⟩
  have ht₀I : t₀ ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩
  have hne : ∀ s ∈ Set.Icc (0:ℝ) 1, s ≠ t₀ → φ s ≠ p := by
    intro s hs hst hc
    exact hst (hinj hs ht₀I (by rw [hc, hpt]))
  set ε' : ℝ := min εa ε₀ with hε'def
  have hε' : 0 < ε' := lt_min hεa hε₀
  -- the parameters near `t₀` stay in any ball about `p`
  have hnear : ∀ ζ : ℝ, 0 < ζ → ∃ δ > 0, ∀ s : ℝ, |s - t₀| ≤ δ → dist (φ s) p < ζ := by
    intro ζ hζ
    have hcz : ContinuousAt φ t₀ := hcont.continuousAt
    rw [Metric.continuousAt_iff] at hcz
    obtain ⟨δ, hδ, hδ'⟩ := hcz ζ hζ
    refine ⟨δ / 2, by linarith, fun s hs => ?_⟩
    have : dist s t₀ < δ := by
      rw [Real.dist_eq]; linarith
    have := hδ' this
    rwa [hpt] at this
  -- the radial set, with the centre removed
  set D₀ : Set UCPlanar.Plane := {d ∈ D | d ≠ p} with hD₀def
  have hD₀fin : D₀.Finite := hDfin.subset (fun d hd => hd.1)
  have hD₀ne : D₀.Nonempty := by
    obtain ⟨δ, hδ, hδ'⟩ := hnear ε' hε'
    set s : ℝ := min 1 (t₀ + δ) with hsdef
    have hs1 : s ≤ 1 := min_le_left _ _
    have hst : t₀ < s := lt_min ht₀.2 (by linarith)
    have hs0 : (0:ℝ) ≤ s := le_of_lt (lt_trans ht₀.1 hst)
    have hsI : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs0, hs1⟩
    have hsd : |s - t₀| ≤ δ := by
      rw [abs_of_pos (by linarith)]
      have : s ≤ t₀ + δ := min_le_right _ _
      linarith
    have hball : φ s ∈ Metric.ball p ε₀ :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (hδ' s hsd) (min_le_right εa ε₀))
    have hmem : φ s ∈ Metric.ball p ε₀ ∩ Q.embedding.trace := ⟨hball, hφtrace s⟩
    rw [hDeq] at hmem
    obtain ⟨d, hd, hsd'⟩ := Set.mem_iUnion₂.mp hmem.2
    refine ⟨d, hd, ?_⟩
    intro hdp
    rw [hdp, segment_same, Set.mem_singleton_iff] at hsd'
    exact hne s hsI (ne_of_gt hst) hsd'
  have hD₀eq : Metric.ball p ε₀ ∩ Q.embedding.trace
      = Metric.ball p ε₀ ∩ ⋃ d ∈ D₀, segment ℝ p d := by
    obtain ⟨d₀, hd₀⟩ := hD₀ne
    refine Set.Subset.antisymm ?_ ?_
    · intro q hq
      refine ⟨hq.1, ?_⟩
      rw [hDeq] at hq
      obtain ⟨d, hd, hqd⟩ := Set.mem_iUnion₂.mp hq.2
      by_cases hdp : d = p
      · rw [hdp, segment_same, Set.mem_singleton_iff] at hqd
        exact Set.mem_biUnion hd₀ (by rw [hqd]; exact left_mem_segment ℝ p d₀)
      · exact Set.mem_biUnion ⟨hd, hdp⟩ hqd
    · intro q hq
      refine ⟨hq.1, ?_⟩
      obtain ⟨d, hd, hqd⟩ := Set.mem_iUnion₂.mp hq.2
      have : q ∈ Metric.ball p ε₀ ∩ ⋃ d ∈ D, segment ℝ p d :=
        ⟨hq.1, Set.mem_biUnion hd.1 hqd⟩
      rw [← hDeq] at this
      exact this.2
  obtain ⟨c, hc0, hc⟩ : ∃ c > 0, ∀ d ∈ D₀, c ≤ ‖d - p‖ := by
    obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image hD₀fin.toFinset (fun d => ‖d - p‖)
      (by rwa [Set.Finite.toFinset_nonempty])
    refine ⟨‖d - p‖, ?_, fun e he => hmin e (hD₀fin.mem_toFinset.mpr he)⟩
    have : d ∈ D₀ := hD₀fin.mem_toFinset.mp hd
    exact norm_pos_iff.mpr (sub_ne_zero.mpr this.2)
  set ε₃ : ℝ := min ε' c with hε₃def
  have hε₃ : 0 < ε₃ := lt_min hε' hc0
  obtain ⟨δ, hδ, hδ'⟩ := hnear ε₃ hε₃
  set v : ℝ := max 0 (t₀ - δ) with hvdef
  set u : ℝ := min 1 (t₀ + δ) with hudef
  have hv0 : (0:ℝ) ≤ v := le_max_left _ _
  have hvt : v < t₀ := max_lt ht₀.1 (by linarith)
  have htu : t₀ < u := lt_min ht₀.2 (by linarith)
  have hu1 : u ≤ 1 := min_le_left _ _
  have hIcc : Set.Icc v u ⊆ Set.Icc (0:ℝ) 1 :=
    Set.Icc_subset_Icc hv0 hu1
  have hballs : ∀ s ∈ Set.Icc v u, φ s ∈ Metric.ball p ε₃ := by
    intro s hs
    refine Metric.mem_ball.mpr (hδ' s ?_)
    by_cases hst : s ≤ t₀
    · rw [abs_of_nonpos (by linarith)]
      have : t₀ - δ ≤ v := le_max_right _ _
      have := hs.1
      linarith
    · rw [not_le] at hst
      rw [abs_of_pos (by linarith)]
      have : u ≤ t₀ + δ := min_le_right _ _
      have := hs.2
      linarith
  obtain ⟨ε₁, hε₁, hJ⟩ := exists_ball_image_subset hcont (isCompact_Icc (a := (0:ℝ)) (b := 1))
    hinj (isOpen_Ioo (a := v) (b := u)) ht₀I ⟨hvt, htu⟩
  rw [hpt] at hJ
  set ε : ℝ := min ε₃ ε₁ with hεdef
  have hε : 0 < ε := lt_min hε₃ hε₁
  have hεε₃ : ε ≤ ε₃ := min_le_left _ _
  have hεε₀ : ε ≤ ε₀ := le_trans hεε₃ (le_trans (min_le_left ε' c) (min_le_right εa ε₀))
  have hεεa : ε ≤ εa := le_trans hεε₃ (le_trans (min_le_left ε' c) (min_le_left εa ε₀))
  have hεc : ε ≤ c := le_trans hεε₃ (min_le_right ε' c)
  -- the two pieces of the arc beside the parameter
  set A : Set UCPlanar.Plane := φ '' Set.Ico v t₀ with hAdef
  set B : Set UCPlanar.Plane := φ '' Set.Ioc t₀ u with hBdef
  have hApre : IsPreconnected A := (isPreconnected_Ico).image φ hcont.continuousOn
  have hBpre : IsPreconnected B := (isPreconnected_Ioc).image φ hcont.continuousOn
  have hAsub : A ⊆ ⋃ d ∈ D₀, segment ℝ p d := by
    rintro q ⟨s, hs, rfl⟩
    have hsIcc : s ∈ Set.Icc v u := ⟨hs.1, le_of_lt (lt_trans hs.2 htu)⟩
    have : φ s ∈ Metric.ball p ε₀ ∩ Q.embedding.trace :=
      ⟨Metric.ball_subset_ball (le_trans (min_le_left ε' c) (min_le_right εa ε₀))
        (hballs s hsIcc), hφtrace s⟩
    rw [hD₀eq] at this
    exact this.2
  have hBsub : B ⊆ ⋃ d ∈ D₀, segment ℝ p d := by
    rintro q ⟨s, hs, rfl⟩
    have hsIcc : s ∈ Set.Icc v u := ⟨le_of_lt (lt_trans hvt hs.1), hs.2⟩
    have : φ s ∈ Metric.ball p ε₀ ∩ Q.embedding.trace :=
      ⟨Metric.ball_subset_ball (le_trans (min_le_left ε' c) (min_le_right εa ε₀))
        (hballs s hsIcc), hφtrace s⟩
    rw [hD₀eq] at this
    exact this.2
  have hpA : p ∉ A := by
    rintro ⟨s, hs, hsp⟩
    exact hne s (hIcc ⟨hs.1, le_of_lt (lt_trans hs.2 htu)⟩) (ne_of_lt hs.2) hsp
  have hpB : p ∉ B := by
    rintro ⟨s, hs, hsp⟩
    exact hne s (hIcc ⟨le_of_lt (lt_trans hvt hs.1), hs.2⟩) (ne_of_gt hs.1) hsp
  -- points of the two pieces at one distance from the centre
  set g : ℝ → ℝ := fun s => ‖φ s - p‖ with hgdef
  have hgcont : Continuous g := (hcont.sub continuous_const).norm
  have hgt₀ : g t₀ = 0 := by simp [hgdef, hpt]
  have hvI : v ∈ Set.Icc (0:ℝ) 1 := hIcc ⟨le_refl v, le_of_lt (lt_trans hvt htu)⟩
  have huI : u ∈ Set.Icc (0:ℝ) 1 := hIcc ⟨le_of_lt (lt_trans hvt htu), le_refl u⟩
  have hcv : 0 < g v := norm_pos_iff.mpr (sub_ne_zero.mpr (hne v hvI (ne_of_lt hvt)))
  have hcu : 0 < g u := norm_pos_iff.mpr (sub_ne_zero.mpr (hne u huI (ne_of_gt htu)))
  set ρ : ℝ := min (min (g v) (g u)) ε / 2 with hρdef
  have hρ0 : 0 < ρ := by
    have : 0 < min (min (g v) (g u)) ε := lt_min (lt_min hcv hcu) hε
    rw [hρdef]; linarith
  have hρv : ρ ≤ g v := by
    have h1 : min (min (g v) (g u)) ε ≤ g v :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hρdef]; linarith
  have hρu : ρ ≤ g u := by
    have h1 : min (min (g v) (g u)) ε ≤ g u :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rw [hρdef]; linarith
  have hρε : ρ < ε := by
    have h1 : min (min (g v) (g u)) ε ≤ ε := min_le_right _ _
    rw [hρdef]; linarith
  obtain ⟨s₁, hs₁, hgs₁⟩ : ∃ s ∈ Set.Icc v t₀, g s = ρ := by
    have := intermediate_value_Icc' (le_of_lt hvt) hgcont.continuousOn
    have hmem : ρ ∈ Set.Icc (g t₀) (g v) := ⟨by rw [hgt₀]; exact le_of_lt hρ0, hρv⟩
    obtain ⟨s, hs, hgs⟩ := this hmem
    exact ⟨s, hs, hgs⟩
  obtain ⟨s₂, hs₂, hgs₂⟩ : ∃ s ∈ Set.Icc t₀ u, g s = ρ := by
    have := intermediate_value_Icc (le_of_lt htu) hgcont.continuousOn
    have hmem : ρ ∈ Set.Icc (g t₀) (g u) := ⟨by rw [hgt₀]; exact le_of_lt hρ0, hρu⟩
    obtain ⟨s, hs, hgs⟩ := this hmem
    exact ⟨s, hs, hgs⟩
  have hs₁t : s₁ < t₀ := lt_of_le_of_ne hs₁.2 (by intro hc; rw [hc, hgt₀] at hgs₁; linarith)
  have hs₂t : t₀ < s₂ := lt_of_le_of_ne hs₂.1 (by intro hc; rw [← hc, hgt₀] at hgs₂; linarith)
  have hn₁ : ‖φ s₁ - p‖ = ρ := hgs₁
  have hn₂ : ‖φ s₂ - p‖ = ρ := hgs₂
  have hz₁A : φ s₁ ∈ A := ⟨s₁, ⟨hs₁.1, hs₁t⟩, rfl⟩
  have hz₂B : φ s₂ ∈ B := ⟨s₂, ⟨hs₂t, hs₂.2⟩, rfl⟩
  have hz₁ne : φ s₁ - p ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn₁
    linarith
  have hz₂ne : φ s₂ - p ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hn₂
    linarith
  have hnsr : ¬ SameRay ℝ (φ s₁ - p) (φ s₂ - p) := by
    intro hsr
    have heqv : φ s₁ - p = φ s₂ - p :=
      eq_of_sameRay_of_norm_eq hsr (by rw [hn₁, hn₂])
    have : φ s₁ = φ s₂ := sub_left_inj.mp heqv
    have hseq : s₁ = s₂ := hinj (hIcc ⟨hs₁.1, le_of_lt (lt_trans hs₁t htu)⟩)
      (hIcc ⟨le_of_lt (lt_trans hvt hs₂t), hs₂.2⟩) this
    rw [hseq] at hs₁t
    linarith
  set k : ℝ := ε / ρ with hkdef
  have hk : 0 < k := div_pos hε hρ0
  set d₁ : UCPlanar.Plane := p + k • (φ s₁ - p) with hd₁def
  set d₂ : UCPlanar.Plane := p + k • (φ s₂ - p) with hd₂def
  have hd₁s : d₁ - p = k • (φ s₁ - p) := by rw [hd₁def]; module
  have hd₂s : d₂ - p = k • (φ s₂ - p) := by rw [hd₂def]; module
  have hkρ : k * ρ = ε := by rw [hkdef]; field_simp
  have hd₁n : ‖d₁ - p‖ = ε := by
    rw [hd₁s, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    rw [hn₁]
    exact hkρ
  have hd₂n : ‖d₂ - p‖ = ε := by
    rw [hd₂s, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    rw [hn₂]
    exact hkρ
  have hd₁ne : d₁ - p ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hd₁n
    linarith
  have hd₂ne : d₂ - p ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at hd₂n
    linarith
  have hray₁ : SameRay ℝ (φ s₁ - p) (d₁ - p) := by
    rw [hd₁s]; exact (SameRay.refl _).nonneg_smul_right hk.le
  have hray₂ : SameRay ℝ (φ s₂ - p) (d₂ - p) := by
    rw [hd₂s]; exact (SameRay.refl _).nonneg_smul_right hk.le
  refine ⟨ε, hε, d₁, d₂, ?_, ?_, ?_, ?_⟩
  · intro hc
    rw [← hc, sub_self, norm_zero] at hd₁n
    linarith
  · intro hc
    rw [← hc, sub_self, norm_zero] at hd₂n
    linarith
  · intro t ht hcon
    have h1 : k • (φ s₂ - p) = (t * k) • (φ s₁ - p) := by
      rw [← hd₂s, hcon, hd₁s]; module
    have h2 : φ s₂ - p = t • (φ s₁ - p) := by
      have h3 : k⁻¹ • (k • (φ s₂ - p)) = k⁻¹ • ((t * k) • (φ s₁ - p)) := by rw [h1]
      rw [smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt hk), one_smul] at h3
      rw [h3]
      congr 1
      field_simp
    refine hnsr ?_
    rw [h2]
    exact (SameRay.refl (φ s₁ - p)).nonneg_smul_right ht.le
  · refine Set.Subset.antisymm ?_ ?_
    · rintro q ⟨hqb, hqt⟩
      refine ⟨hqb, ?_⟩
      by_cases hqp : q = p
      · exact Or.inl (by rw [hqp]; exact left_mem_segment ℝ p d₁)
      have hqarc : q ∈ φ '' Set.Icc (0:ℝ) 1 := by
        rw [himg]
        have hmem : q ∈ Metric.ball p εa ∩ Q.embedding.trace :=
          ⟨Metric.ball_subset_ball hεεa hqb, hqt⟩
        rw [harceq] at hmem
        exact hmem.2
      obtain ⟨s, hs, hsq⟩ :=
        hJ ⟨Metric.ball_subset_ball (min_le_right ε₃ ε₁) hqb, hqarc⟩
      have hst : s ≠ t₀ := by
        intro hc
        exact hqp (by rw [← hsq, hc]; exact hpt)
      have hqn : ‖q - p‖ < ε := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hqb
      rcases lt_or_gt_of_ne hst with hlt | hgt
      · have hmemA : q ∈ A := ⟨s, ⟨le_of_lt hs.2.1, hlt⟩, hsq⟩
        have hsr := sameRay_of_preconnected hD₀fin hApre hAsub hpA hmemA hz₁A
        refine Or.inl (mem_segment_of_sameRay
          (hsr.trans hray₁ (fun hc => absurd hc hz₁ne)) ?_)
        rw [hd₁n]; exact le_of_lt hqn
      · have hmemB : q ∈ B := ⟨s, ⟨hgt, le_of_lt hs.2.2⟩, hsq⟩
        have hsr := sameRay_of_preconnected hD₀fin hBpre hBsub hpB hmemB hz₂B
        refine Or.inr (mem_segment_of_sameRay
          (hsr.trans hray₂ (fun hc => absurd hc hz₂ne)) ?_)
        rw [hd₂n]; exact le_of_lt hqn
    · rintro q ⟨hqb, hqs⟩
      refine ⟨hqb, ?_⟩
      have hqn : ‖q - p‖ < ε := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hqb
      have hfin : ∀ (z : UCPlanar.Plane) (dd : UCPlanar.Plane), z ∈ A ∪ B → z - p ≠ 0 →
          dd - p ≠ 0 → SameRay ℝ (z - p) (dd - p) → q ∈ segment ℝ p dd →
          q ∈ Q.embedding.trace := by
        intro z dd hzAB hzne hddne hray hqdd
        have hsr1 : SameRay ℝ (q - p) (dd - p) := sameRay_sub_of_mem_segment hqdd
        have hsr2 : SameRay ℝ (q - p) (z - p) :=
          hsr1.trans hray.symm (fun hc => absurd hc hddne)
        have hzsub : z ∈ ⋃ d ∈ D₀, segment ℝ p d := by
          rcases hzAB with hz | hz
          · exact hAsub hz
          · exact hBsub hz
        obtain ⟨d, hd, hzd⟩ := Set.mem_iUnion₂.mp hzsub
        have hsr3 : SameRay ℝ (q - p) (d - p) :=
          hsr2.trans (sameRay_sub_of_mem_segment hzd) (fun hc => absurd hc hzne)
        have hqd : q ∈ segment ℝ p d :=
          mem_segment_of_sameRay hsr3 (le_trans (le_of_lt hqn) (le_trans hεc (hc d hd)))
        have hmem : q ∈ Metric.ball p ε₀ ∩ ⋃ d ∈ D₀, segment ℝ p d :=
          ⟨Metric.ball_subset_ball hεε₀ hqb, Set.mem_biUnion hd hqd⟩
        rw [← hD₀eq] at hmem
        exact hmem.2
      rcases hqs with hq1 | hq2
      · exact hfin (φ s₁) d₁ (Or.inl hz₁A) hz₁ne hd₁ne hray₁ hq1
      · exact hfin (φ s₂) d₂ (Or.inr hz₂B) hz₂ne hd₂ne hray₂ hq2

/-- **Two segments radiate from a point interior to an arc of the drawing.** -/
theorem exists_two_rays_of_arc (Q : UCPlanar.PeriodicPlaneGraph V) {e : Sym2 V}
    (he : e ∈ Q.graph.edgeSet) {p : UCPlanar.Plane} (hp : p ∈ Q.embedding.arcOf e)
    (hpv : ∀ v : V, p ≠ Q.embedding.pos v) :
    ∃ ε > 0, ∃ d₁ d₂ : UCPlanar.Plane, p ≠ d₁ ∧ p ≠ d₂ ∧
      (∀ t : ℝ, 0 < t → d₂ ≠ p + t • (d₁ - p)) ∧
      Metric.ball p ε ∩ Q.embedding.trace
        = Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
  induction e with
  | _ a b =>
    have hab : Q.graph.Adj a b := by simpa using he
    rw [arcOf_eq Q.embedding hab] at hp
    obtain ⟨t, ht⟩ := hp
    have hptA : arcParam Q.embedding hab (t : ℝ) = p := by
      rw [arcParam, Set.projIcc_val]; exact ht
    have ht0 : ((t : ℝ)) ≠ 0 := by
      intro hc
      refine hpv a ?_
      rw [← hptA, hc]
      exact arcParam_zero _ _
    have ht1 : ((t : ℝ)) ≠ 1 := by
      intro hc
      refine hpv b ?_
      rw [← hptA, hc]
      exact arcParam_one _ _
    have htIoo : (t : ℝ) ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
    obtain ⟨ε, hε, heq⟩ := exists_ball_trace_eq_arcOf Q he
      (by rw [arcOf_eq Q.embedding hab]; exact ⟨t, ht⟩) hpv
    rw [arcOf_eq Q.embedding hab] at heq
    exact exists_two_rays_of_arcParam Q hab htIoo hptA ⟨ε, hε, heq⟩

/-- **Near a point interior to an arc and on the frontier of a face the whole drawing is on
that frontier.**  The two segments radiating from the point lie on the frontier by the corner
theorem, and near the point they are the drawing. -/
theorem exists_ball_trace_subset_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) {e : Sym2 V}
    (he : e ∈ Q.graph.edgeSet) {p : UCPlanar.Plane} (hp : p ∈ Q.embedding.arcOf e)
    (hpv : ∀ v : V, p ≠ Q.embedding.pos v) (hpf : p ∈ frontier F) :
    ∃ ε > 0, Metric.ball p ε ∩ Q.embedding.trace ⊆ frontier F := by
  obtain ⟨ε, hε, d₁, d₂, hne₁, hne₂, hopp, heq⟩ := exists_two_rays_of_arc Q he hp hpv
  obtain ⟨ε', hε', hle, hsub⟩ := two_rays_subset_frontier Q hF hε hne₁ hne₂ hopp heq hpf
  refine ⟨ε', hε', ?_⟩
  rintro q ⟨hqb, hqt⟩
  have hq : q ∈ Metric.ball p ε ∩ Q.embedding.trace :=
    ⟨Metric.ball_subset_ball hle hqb, hqt⟩
  rw [heq] at hq
  exact hsub ⟨hqb, hq.2⟩

/-- **An arc meeting the frontier of a face away from its ends lies on that frontier.**  The
parameters whose points are on the frontier are relatively open in the interior of the arc by
the local step and relatively closed because the frontier is closed, so they are all of it, and
the ends follow by taking closures. -/
theorem arcOf_subset_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) {e : Sym2 V}
    (he : e ∈ Q.graph.edgeSet) {p : UCPlanar.Plane} (hp : p ∈ Q.embedding.arcOf e)
    (hpv : ∀ v : V, p ≠ Q.embedding.pos v) (hpf : p ∈ frontier F) :
    Q.embedding.arcOf e ⊆ frontier F := by
  induction e with
  | _ a b =>
    have hab : Q.graph.Adj a b := by simpa using he
    have harc : Q.embedding.arcOf s(a, b) = Set.range (Q.embedding.edge hab) :=
      arcOf_eq Q.embedding hab
    set φ : ℝ → UCPlanar.Plane := arcParam Q.embedding hab with hφdef
    have hcont : Continuous φ := continuous_arcParam _ _
    have hinj : Set.InjOn φ (Set.Icc (0:ℝ) 1) := injOn_arcParam _ _
    have himg : φ '' Set.Icc (0:ℝ) 1 = Set.range (Q.embedding.edge hab) := arcParam_image _ _
    have hφarc : ∀ s, φ s ∈ Q.embedding.arcOf s(a, b) := by
      intro s; rw [harc]; exact arcParam_mem _ _ s
    -- interior parameters are not drawn vertices
    have hvert : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ v : V, φ s ≠ Q.embedding.pos v := by
      intro s hs v hc
      have hz : v ∈ s(a, b) := mem_of_pos_mem_arcOf Q.embedding he (hc ▸ hφarc s)
      have hsI : s ∈ Set.Icc (0:ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · have h0 : φ s = φ 0 := by rw [hc]; exact (arcParam_zero _ _).symm
        have := hinj hsI ⟨le_refl 0, zero_le_one⟩ h0
        exact absurd this (ne_of_gt hs.1)
      · have h1 : φ s = φ 1 := by rw [hc]; exact (arcParam_one _ _).symm
        have := hinj hsI ⟨zero_le_one, le_refl 1⟩ h1
        exact absurd this (ne_of_lt hs.2)
    -- the seed parameter
    obtain ⟨t, ht⟩ : ∃ t, Q.embedding.edge hab t = p := by rwa [harc] at hp
    have hptA : arcParam Q.embedding hab (t : ℝ) = p := by
      rw [arcParam, Set.projIcc_val]; exact ht
    have ht0 : ((t : ℝ)) ≠ 0 := by
      intro hc
      refine hpv a ?_
      rw [← hptA, hc]
      exact arcParam_zero _ _
    have ht1 : ((t : ℝ)) ≠ 1 := by
      intro hc
      refine hpv b ?_
      rw [← hptA, hc]
      exact arcParam_one _ _
    have htIoo : (t : ℝ) ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
    have hpt : φ (t : ℝ) = p := hptA
    -- the clopen argument on the open arc
    set Uo : Set ℝ := φ ⁻¹' (frontier F)ᶜ with hUodef
    set Ucl : Set ℝ := {s | ∃ δ > 0, Metric.ball s δ ∩ Set.Ioo (0:ℝ) 1 ⊆ φ ⁻¹' frontier F}
      with hUcldef
    have hUoopen : IsOpen Uo := isClosed_frontier.isOpen_compl.preimage hcont
    have hUclopen : IsOpen Ucl := by
      rw [Metric.isOpen_iff]
      rintro s ⟨δ, hδ, hsub⟩
      refine ⟨δ / 2, by linarith, ?_⟩
      intro s' hs'
      refine ⟨δ / 2, by linarith, ?_⟩
      rintro r ⟨hr1, hr2⟩
      refine hsub ⟨?_, hr2⟩
      have h1 : dist r s' < δ / 2 := Metric.mem_ball.mp hr1
      have h2 : dist s' s < δ / 2 := Metric.mem_ball.mp hs'
      have := dist_triangle r s' s
      exact Metric.mem_ball.mpr (by linarith)
    have hcover : Set.Ioo (0:ℝ) 1 ⊆ Uo ∪ Ucl := by
      intro s hs
      by_cases hsf : φ s ∈ frontier F
      · refine Or.inr ?_
        obtain ⟨ζ, hζ, hζsub⟩ :=
          exists_ball_trace_subset_frontier Q hF he (hφarc s) (hvert s hs) hsf
        obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ζ hζ
        refine ⟨δ, hδ, ?_⟩
        rintro r ⟨hr1, -⟩
        exact hζsub ⟨Metric.mem_ball.mpr (hδ' (Metric.mem_ball.mp hr1)),
          arcOf_subset_trace Q.embedding (hφarc r)⟩
      · exact Or.inl hsf
    have hempty : Set.Ioo (0:ℝ) 1 ∩ (Uo ∩ Ucl) = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro hs hso ⟨δ, hδ, hsub⟩
      exact hso (hsub ⟨Metric.mem_ball_self hδ, hs⟩)
    have hfront : ∀ s ∈ Set.Ioo (0:ℝ) 1, φ s ∈ frontier F := by
      intro s hs
      by_contra hsf
      have hne1 : (Set.Ioo (0:ℝ) 1 ∩ Uo).Nonempty := ⟨s, hs, hsf⟩
      have hne2 : (Set.Ioo (0:ℝ) 1 ∩ Ucl).Nonempty := by
        rcases hcover htIoo with hc | hc
        · exact absurd (show φ (t : ℝ) ∈ frontier F by rw [hpt]; exact hpf) hc
        · exact ⟨(t : ℝ), htIoo, hc⟩
      obtain ⟨r, hr, hr2⟩ := isPreconnected_Ioo Uo Ucl hUoopen hUclopen hcover hne1 hne2
      have : r ∈ Set.Ioo (0:ℝ) 1 ∩ (Uo ∩ Ucl) := ⟨hr, hr2⟩
      rw [hempty] at this
      exact this
    -- the ends by closure
    rw [harc, ← himg]
    have hIoo : Set.Icc (0:ℝ) 1 = closure (Set.Ioo (0:ℝ) 1) := (closure_Ioo (by norm_num)).symm
    rw [hIoo]
    refine le_trans (image_closure_subset_closure_image hcont) ?_
    have hcl : closure (frontier F) = frontier F := isClosed_frontier.closure_eq
    rw [← hcl]
    exact closure_mono (by rintro q ⟨r, hr, rfl⟩; exact hfront r hr)

/-- Only finitely many vertices are drawn in a bounded set. -/
theorem finite_pos_meeting_bounded (Q : UCPlanar.PeriodicPlaneGraph V)
    {A : Set UCPlanar.Plane} (hA : Bornology.IsBounded A) :
    {w : V | Q.embedding.pos w ∈ A}.Finite := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall (0 : UCPlanar.Plane)
  refine (Q.finite_squares R).subset ?_
  intro w hw i
  have hd : dist (Q.embedding.pos w) (0 : UCPlanar.Plane) ≤ R :=
    Metric.mem_closedBall.mp (hR hw)
  have hi : dist (Q.embedding.pos w i) ((0 : UCPlanar.Plane) i) ≤
      dist (Q.embedding.pos w) (0 : UCPlanar.Plane) := dist_le_pi_dist _ _ i
  have : |Q.embedding.pos w i| ≤ R := by
    have h0 : ((0 : UCPlanar.Plane) i) = 0 := rfl
    rw [h0, Real.dist_eq, sub_zero] at hi
    linarith
  rwa [Q.embedding_pos] at this

/-- The plane without a point is connected. -/
theorem isPreconnected_compl_singleton (p : UCPlanar.Plane) :
    IsPreconnected ({p}ᶜ : Set UCPlanar.Plane) :=
  (isConnected_compl_singleton_of_one_lt_rank (by simp) p).isPreconnected

/-- **The frontier of a bounded face is more than one point.**  A face and the complement of its
closure would otherwise separate the plane minus that point. -/
theorem frontier_not_subset_singleton (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) {v : V}
    (hp : Q.embedding.pos v ∈ frontier F) :
    ¬ frontier F ⊆ ({Q.embedding.pos v} : Set UCPlanar.Plane) := by
  intro hsub
  set p : UCPlanar.Plane := Q.embedding.pos v with hpdef
  obtain ⟨w, hw⟩ := exists_adj_of_periodic Q v
  have hwv : Q.embedding.pos w ≠ p := by
    intro hc
    exact hw.ne' (Q.embedding.pos_injective hc)
  have hwt : Q.embedding.pos w ∈ Q.embedding.trace := Or.inl ⟨w, rfl⟩
  have hwF : Q.embedding.pos w ∉ F := fun hc =>
    isFace_subset_compl_trace Q.embedding hF hc hwt
  have hclF : closure F ⊆ F ∪ ({p} : Set UCPlanar.Plane) := by
    intro q hq
    by_cases hqF : q ∈ F
    · exact Or.inl hqF
    · refine Or.inr (hsub ?_)
      rw [(isOpen_isFace Q hF).frontier_eq]
      exact ⟨hq, hqF⟩
  have hwcl : Q.embedding.pos w ∈ (closure F)ᶜ := by
    intro hc
    rcases hclF hc with h | h
    · exact hwF h
    · exact hwv h
  have hcover : ({p} : Set UCPlanar.Plane)ᶜ ⊆ F ∪ (closure F)ᶜ := by
    intro q hq
    by_cases hqc : q ∈ closure F
    · rcases hclF hqc with h | h
      · exact Or.inl h
      · exact absurd h hq
    · exact Or.inr hqc
  obtain ⟨q₀, hq₀⟩ := isFace_nonempty Q.embedding hF
  have hpF : p ∉ F := by
    have hfe := (isOpen_isFace Q hF).frontier_eq
    rw [hfe] at hp
    exact hp.2
  have hq₀p : q₀ ≠ p := fun hc => hpF (hc ▸ hq₀)
  obtain ⟨r, hr, hrF, hrcl⟩ := isPreconnected_compl_singleton p F (closure F)ᶜ
    (isOpen_isFace Q hF) isClosed_closure.isOpen_compl hcover
    ⟨q₀, hq₀p, hq₀⟩ ⟨Q.embedding.pos w, hwv, hwcl⟩
  exact hrcl (subset_closure hrF)

/-- **Every point of the frontier of a bounded face lies on a whole arc of that frontier.**  At a
point that is not a drawn vertex this is the propagation along the arc; at a drawn vertex the
frontier is connected, so the point is not isolated in it, and a nearby frontier point supplies
an arc through the vertex. -/
theorem exists_arc_of_mem_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    (hpre : IsPreconnected (frontier F)) {p : UCPlanar.Plane} (hpf : p ∈ frontier F) :
    ∃ e ∈ Q.graph.edgeSet, p ∈ Q.embedding.arcOf e ∧ Q.embedding.arcOf e ⊆ frontier F := by
  classical
  have hpt : p ∈ Q.embedding.trace := frontier_isFace_subset_trace Q hF hpf
  by_cases hpv : ∀ v : V, p ≠ Q.embedding.pos v
  · rw [trace_eq_edgesTrace Q] at hpt
    obtain ⟨e, he, hpe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding hpt
    exact ⟨e, he, hpe, arcOf_subset_frontier Q hF he hpe hpv hpf⟩
  · rw [Classical.not_forall] at hpv
    obtain ⟨v, hv⟩ := hpv
    rw [Classical.not_not] at hv
    -- a ball meeting only the arcs through `p` and no other drawn vertex
    obtain ⟨T, hTfin, hTsub, hTcov⟩ := exists_finite_trace_near Q p 1
    set U : Set (Sym2 V) := {f ∈ T | p ∉ Q.embedding.arcOf f} with hU
    have hUfin : U.Finite := hTfin.subset (fun f hf => hf.1)
    have hUclosed : IsClosed (⋃ f ∈ U, Q.embedding.arcOf f) :=
      hUfin.isClosed_biUnion (fun f hf => (isCompact_arcOf Q.embedding (hTsub hf.1)).isClosed)
    have hpU : p ∉ ⋃ f ∈ U, Q.embedding.arcOf f := by
      intro hc
      obtain ⟨f, hf, hpf'⟩ := Set.mem_iUnion₂.mp hc
      exact hf.2 hpf'
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl p hpU
    set W : Set UCPlanar.Plane :=
      (fun w : V => Q.embedding.pos w) '' {w : V | Q.embedding.pos w ∈ Metric.closedBall p 1 ∧
        Q.embedding.pos w ≠ p} with hW
    have hWfin : W.Finite :=
      Set.Finite.image _ ((finite_pos_meeting_bounded Q Metric.isBounded_closedBall).subset
        (fun w hw => hw.1))
    have hpW : p ∉ W := by
      rintro ⟨w, hw, hwp⟩
      exact hw.2 hwp
    obtain ⟨ε₂, hε₂, hb₂⟩ :=
      Metric.isOpen_iff.mp hWfin.isClosed.isOpen_compl p hpW
    set ε : ℝ := min (min ε₁ ε₂) 1 with hεdef
    have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) one_pos
    -- the point is not isolated in the frontier
    have hiso : ¬ (frontier F ∩ Metric.ball p ε ⊆ {p}) := by
      intro hc
      refine frontier_not_subset_singleton Q hF (v := v) (by rwa [← hv]) ?_
      rw [← hv]
      exact eq_singleton_of_isolated hpre hpf Metric.isOpen_ball (Metric.mem_ball_self hε) hc
    rw [Set.not_subset] at hiso
    obtain ⟨q, ⟨hqf, hqb⟩, hqp⟩ := hiso
    rw [Set.mem_singleton_iff] at hqp
    have hqt : q ∈ Q.embedding.trace := frontier_isFace_subset_trace Q hF hqf
    have hq1 : q ∈ Metric.closedBall p 1 :=
      Metric.closedBall_subset_closedBall (min_le_right _ _)
        (Metric.ball_subset_closedBall hqb)
    obtain ⟨f, hf, hqe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding (hTcov q hq1 hqt)
    have hpf' : p ∈ Q.embedding.arcOf f := by
      by_contra hcon
      exact hb₁ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hqb)
        (le_trans (min_le_left _ _) (min_le_left _ _)))) (Set.mem_biUnion ⟨hf, hcon⟩ hqe)
    have hqv : ∀ w : V, q ≠ Q.embedding.pos w := by
      intro w hc
      refine hb₂ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hqb)
        (le_trans (min_le_left _ _) (min_le_right _ _)))) ?_
      exact ⟨w, ⟨by rw [← hc]; exact hq1, by rw [← hc]; exact hqp⟩, hc.symm⟩
    exact ⟨f, hTsub hf, hpf', arcOf_subset_frontier Q hF (hTsub hf) hqe hqv hqf⟩

/-- **The frontier of a bounded face with connected frontier is drawn by finitely many whole
arcs.** -/
theorem faceFrontierArcs_of_preconnected (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    (hpre : IsPreconnected (frontier F)) (hbdd : Bornology.IsBounded F) :
    Q.embedding.FaceFrontierArcs F :=
  faceFrontierArcs_of_twoSided Q (hbdd.closure.subset frontier_subset_closure)
    (fun _ hp => exists_arc_of_mem_frontier Q hF hpre hp)

end UCPlanar.Support
