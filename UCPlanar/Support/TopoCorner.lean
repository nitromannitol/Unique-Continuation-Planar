/- The corner of a polygonal drawing.  Where the drawing near a point is two segments radiating
from it on two different lines, the two lines cut the ball into four convex cells which the two
free half lines join into two pieces, each with both segments in its closure.  A face beside the
corner contains one of the two pieces, so both segments lie on its frontier: this is the
two-sidedness of the drawing at a corner. -/
import UCPlanar.Support.TopoLocal
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

theorem mem_closure_inter_open {X : Type*} [TopologicalSpace X] {U A : Set X} {x : X}
    (hU : IsOpen U) (hx : x ∈ U) (hcl : x ∈ closure A) : x ∈ closure (U ∩ A) := by
  rw [mem_closure_iff]
  intro V hV hxV
  obtain ⟨t, htV, htA⟩ := (mem_closure_iff.mp hcl) (V ∩ U) (hV.inter hU) ⟨hxV, hx⟩
  exact ⟨t, htV.1, htV.2, htA⟩

theorem mem_halfPlane_of_sign {l : ℝ × ℝ × ℝ} {x : UCPlanar.Plane} {K u : ℝ}
    (hK : K ≠ 0) (hu : 0 < u)
    (hx : l.1 * x 0 + l.2.1 * x 1 - l.2.2 = u * K) :
    x ∈ halfPlane (decide (0 < K)) l := by
  unfold halfPlane
  by_cases hK0 : 0 < K
  · rw [if_pos (by simpa using hK0)]
    show l.2.2 < l.1 * x 0 + l.2.1 * x 1
    nlinarith
  · rw [if_neg (by simpa using hK0)]
    show l.1 * x 0 + l.2.1 * x 1 < l.2.2
    have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hK0) hK
    nlinarith

theorem mem_halfPlane_of_sign_neg {l : ℝ × ℝ × ℝ} {x : UCPlanar.Plane} {K t : ℝ}
    (hK : K ≠ 0) (ht : t < 0)
    (hx : l.1 * x 0 + l.2.1 * x 1 - l.2.2 = t * K) :
    x ∈ halfPlane (!decide (0 < K)) l := by
  unfold halfPlane
  by_cases hK0 : 0 < K
  · rw [if_neg (by simpa using hK0)]
    show l.1 * x 0 + l.2.1 * x 1 < l.2.2
    nlinarith
  · rw [if_pos (by simpa using hK0)]
    show l.2.2 < l.1 * x 0 + l.2.1 * x 1
    have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hK0) hK
    nlinarith

/-- An open half plane is open. -/
theorem isOpen_halfPlane (s : Bool) (l : ℝ × ℝ × ℝ) : IsOpen (halfPlane s l) := by
  have hcont : Continuous (fun x : UCPlanar.Plane => l.1 * x 0 + l.2.1 * x 1) :=
    (continuous_const.mul (continuous_apply 0)).add (continuous_const.mul (continuous_apply 1))
  unfold halfPlane
  split
  · exact isOpen_lt continuous_const hcont
  · exact isOpen_lt hcont continuous_const

theorem lval_param {l : ℝ × ℝ × ℝ} {p d : UCPlanar.Plane} (hp : p ∈ lineSet l) (t : ℝ) :
    l.1 * (p + t • (d - p)) 0 + l.2.1 * (p + t • (d - p)) 1 - l.2.2
      = t * (l.1 * d 0 + l.2.1 * d 1 - l.2.2) := by
  simp only [lineSet, Set.mem_setOf_eq] at hp
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (1 - t) * hp

theorem exists_pos_param_of_mem_segment {p d y : UCPlanar.Plane} (hy : y ∈ segment ℝ p d)
    (hne : y ≠ p) : ∃ u : ℝ, 0 < u ∧ y = p + u • (d - p) := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hy
  refine ⟨β, ?_, ?_⟩
  · rcases hβ.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hne
      have hα1 : α = 1 := by linarith [h]
      rw [← h, hα1]
      simp
  · have hα' : α = 1 - β := by linarith
    subst hα'
    match_scalars <;> ring


/-- A point of a line near its base is a bounded multiple along it. -/
theorem exists_param_ball {l : ℝ × ℝ × ℝ} (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    {p d x : UCPlanar.Plane} {ε : ℝ} (hp : p ∈ lineSet l) (hd : d ∈ lineSet l) (hne : p ≠ d)
    (hεd : ε ≤ ‖d - p‖) (hx : x ∈ Metric.ball p ε ∩ lineSet l) (hnot : x ∉ segment ℝ p d) :
    ∃ t : ℝ, t < 0 ∧ x = p + t • (d - p) := by
  obtain ⟨t, rfl⟩ := exists_param_of_mem_lineSet hl hp hd hne hx.2
  have hne0 : d - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hnorm : 0 < ‖d - p‖ := norm_pos_iff.mpr hne0
  have hdist : dist (p + t • (d - p)) p = |t| * ‖d - p‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hlt : |t| * ‖d - p‖ < ε := by rw [← hdist]; exact Metric.mem_ball.mp hx.1
  have habs : |t| < 1 := by nlinarith [abs_nonneg t]
  refine ⟨t, ?_, rfl⟩
  by_contra hge
  rw [not_lt] at hge
  exact hnot ⟨1 - t, t, by linarith [abs_lt.mp habs], hge, by ring, by match_scalars <;> ring⟩

/-- **Both sides of a corner of the drawing lie on the frontier of a face beside it.** -/
theorem corner_subset_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    {p d₁ d₂ : UCPlanar.Plane} {ε : ℝ} (hε : 0 < ε)
    {l₁ l₂ : ℝ × ℝ × ℝ} (hl₁ : l₁.1 ≠ 0 ∨ l₁.2.1 ≠ 0) (hl₂ : l₂.1 ≠ 0 ∨ l₂.2.1 ≠ 0)
    (hp₁ : p ∈ lineSet l₁) (hq₁ : d₁ ∈ lineSet l₁)
    (hp₂ : p ∈ lineSet l₂) (hq₂ : d₂ ∈ lineSet l₂)
    (hne₁ : p ≠ d₁) (hne₂ : p ≠ d₂)
    (hK₁ : l₂.1 * d₁ 0 + l₂.2.1 * d₁ 1 - l₂.2.2 ≠ 0)
    (hK₂ : l₁.1 * d₂ 0 + l₁.2.1 * d₂ 1 - l₁.2.2 ≠ 0)
    (hεd₁ : ε ≤ ‖d₁ - p‖) (hεd₂ : ε ≤ ‖d₂ - p‖)
    (htr : Metric.ball p ε ∩ Q.embedding.trace
      = Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂))
    (hpf : p ∈ frontier F) :
    Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) ⊆ frontier F := by
  classical
  set K₁ : ℝ := l₂.1 * d₁ 0 + l₂.2.1 * d₁ 1 - l₂.2.2 with hK₁def
  set K₂ : ℝ := l₁.1 * d₂ 0 + l₁.2.1 * d₂ 1 - l₁.2.2 with hK₂def
  set s₂ : Bool := decide (0 < K₁) with hs₂
  set s₁ : Bool := decide (0 < K₂) with hs₁
  set cell : Bool → Bool → Set UCPlanar.Plane := fun a b =>
    Metric.ball p ε ∩ halfPlane a l₁ ∩ halfPlane b l₂ with hcell
  set ray₁ : Set UCPlanar.Plane :=
    (Metric.ball p ε ∩ lineSet l₁) \ segment ℝ p d₁ with hray₁
  set ray₂ : Set UCPlanar.Plane :=
    (Metric.ball p ε ∩ lineSet l₂) \ segment ℝ p d₂ with hray₂
  have hseg₁ : segment ℝ p d₁ ⊆ lineSet l₁ := segment_subset_lineSet hp₁ hq₁
  have hseg₂ : segment ℝ p d₂ ⊆ lineSet l₂ := segment_subset_lineSet hp₂ hq₂
  -- the two open segments sit on one side of the other line
  have hside₁ : ∀ y ∈ segment ℝ p d₁, y ≠ p → y ∈ halfPlane s₂ l₂ := by
    intro y hy hyp
    obtain ⟨u, hu, rfl⟩ := exists_pos_param_of_mem_segment hy hyp
    exact mem_halfPlane_of_sign hK₁ hu (lval_param hp₂ u)
  have hside₂ : ∀ y ∈ segment ℝ p d₂, y ≠ p → y ∈ halfPlane s₁ l₁ := by
    intro y hy hyp
    obtain ⟨u, hu, rfl⟩ := exists_pos_param_of_mem_segment hy hyp
    exact mem_halfPlane_of_sign hK₂ hu (lval_param hp₁ u)
  have hsider₁ : ∀ x ∈ ray₁, x ∈ halfPlane (!s₂) l₂ := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := exists_param_ball hl₁ hp₁ hq₁ hne₁ hεd₁ hx.1 hx.2
    exact mem_halfPlane_of_sign_neg hK₁ ht (lval_param hp₂ t)
  have hsider₂ : ∀ x ∈ ray₂, x ∈ halfPlane (!s₁) l₁ := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := exists_param_ball hl₂ hp₂ hq₂ hne₂ hεd₂ hx.1 hx.2
    exact mem_halfPlane_of_sign_neg hK₂ ht (lval_param hp₁ t)
  have hdisj : ∀ (b : Bool) (l : ℝ × ℝ × ℝ) (x : UCPlanar.Plane),
      x ∈ halfPlane b l → x ∈ halfPlane (!b) l → False := by
    intro b l x h1 h2
    cases b
    · rw [halfPlane, if_neg (by simp)] at h1
      rw [Bool.not_false, halfPlane, if_pos (by simp)] at h2
      simp only [Set.mem_setOf_eq] at h1 h2
      linarith
    · rw [halfPlane, if_pos (by simp)] at h1
      rw [Bool.not_true, halfPlane, if_neg (by simp)] at h2
      simp only [Set.mem_setOf_eq] at h1 h2
      linarith
  have hset : ∀ a b : Bool,
      (Metric.ball p ε ∩ halfPlane b l₂) ∩ halfPlane a l₁ = cell a b := by
    intro a b
    ext x
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
  have hset' : ∀ a b : Bool,
      (Metric.ball p ε ∩ halfPlane a l₁) ∩ halfPlane b l₂ = cell a b := fun _ _ => rfl
  -- the cells and the two free rays miss the drawing
  have hcellt : ∀ a b : Bool, cell a b ⊆ Q.embedding.traceᶜ := by
    rintro a b x ⟨⟨hxb, hxa⟩, hxb2⟩ hxt
    have hmem : x ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
      rw [← htr]; exact ⟨hxb, hxt⟩
    rcases hmem.2 with h | h
    · exact halfPlane_subset_compl_lineSet a l₁ hxa (hseg₁ h)
    · exact halfPlane_subset_compl_lineSet b l₂ hxb2 (hseg₂ h)
  have hray₁t : ray₁ ⊆ Q.embedding.traceᶜ := by
    intro x hx hxt
    have hmem : x ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
      rw [← htr]; exact ⟨hx.1.1, hxt⟩
    rcases hmem.2 with h | h
    · exact hx.2 h
    · have hxp : x ≠ p := fun hc => hx.2 (hc ▸ left_mem_segment ℝ p d₁)
      exact halfPlane_subset_compl_lineSet s₁ l₁ (hside₂ x h hxp) hx.1.2
  have hray₂t : ray₂ ⊆ Q.embedding.traceᶜ := by
    intro x hx hxt
    have hmem : x ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
      rw [← htr]; exact ⟨hx.1.1, hxt⟩
    rcases hmem.2 with h | h
    · have hxp : x ≠ p := fun hc => hx.2 (hc ▸ left_mem_segment ℝ p d₂)
      exact halfPlane_subset_compl_lineSet s₂ l₂ (hside₁ x h hxp) hx.1.2
    · exact hx.2 h
  -- the closures of the cells hold the two open segments and the two free rays
  have hcl₁ : ∀ a : Bool, ∀ y ∈ Metric.ball p ε ∩ segment ℝ p d₁, y ≠ p →
      y ∈ closure (cell a s₂) := by
    intro a y hy hyp
    rw [← hset a s₂]
    exact mem_closure_inter_open (Metric.isOpen_ball.inter (isOpen_halfPlane s₂ l₂))
      ⟨hy.1, hside₁ y hy.2 hyp⟩ (lineSet_subset_closure_halfPlane l₁ hl₁ a (hseg₁ hy.2))
  have hcl₂ : ∀ b : Bool, ∀ y ∈ Metric.ball p ε ∩ segment ℝ p d₂, y ≠ p →
      y ∈ closure (cell s₁ b) := by
    intro b y hy hyp
    rw [← hset' s₁ b]
    exact mem_closure_inter_open (Metric.isOpen_ball.inter (isOpen_halfPlane s₁ l₁))
      ⟨hy.1, hside₂ y hy.2 hyp⟩ (lineSet_subset_closure_halfPlane l₂ hl₂ b (hseg₂ hy.2))
  have hclr₁ : ∀ a : Bool, ray₁ ⊆ closure (cell a (!s₂)) := by
    intro a x hx
    rw [← hset a (!s₂)]
    exact mem_closure_inter_open (Metric.isOpen_ball.inter (isOpen_halfPlane (!s₂) l₂))
      ⟨hx.1.1, hsider₁ x hx⟩ (lineSet_subset_closure_halfPlane l₁ hl₁ a hx.1.2)
  have hclr₂ : ∀ b : Bool, ray₂ ⊆ closure (cell (!s₁) b) := by
    intro b x hx
    rw [← hset' (!s₁) b]
    exact mem_closure_inter_open (Metric.isOpen_ball.inter (isOpen_halfPlane (!s₁) l₁))
      ⟨hx.1.1, hsider₂ x hx⟩ (lineSet_subset_closure_halfPlane l₂ hl₂ b hx.1.2)
  have hcellpre : ∀ a b : Bool, IsPreconnected (cell a b) := fun a b =>
    (((convex_ball p ε).inter (convex_halfPlane a l₁)).inter
      (convex_halfPlane b l₂)).isPreconnected
  -- the two free rays are nonempty
  have hfree : ∀ (d : UCPlanar.Plane) (l m : ℝ × ℝ × ℝ) (K : ℝ), p ∈ lineSet l → d ∈ lineSet l →
      p ∈ lineSet m → K = m.1 * d 0 + m.2.1 * d 1 - m.2.2 → K ≠ 0 → p ≠ d →
      (∀ y ∈ segment ℝ p d, y ≠ p → y ∈ halfPlane (decide (0 < K)) m) →
      ((Metric.ball p ε ∩ lineSet l) \ segment ℝ p d).Nonempty := by
    intro d l m K hpl hdl hpm hKdef hKne hpd hs
    have hd0 : d - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpd)
    have hdn : 0 < ‖d - p‖ := norm_pos_iff.mpr hd0
    have hq : 0 < ε / (2 * ‖d - p‖) := by positivity
    set t : ℝ := -(ε / (2 * ‖d - p‖)) with htdef
    have htneg : t < 0 := by rw [htdef]; linarith
    refine ⟨p + t • (d - p), ⟨?_, ?_⟩, ?_⟩
    · have hdist : dist (p + t • (d - p)) p = |t| * ‖d - p‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [Metric.mem_ball, hdist, abs_of_neg htneg, htdef]
      have : -(-(ε / (2 * ‖d - p‖))) * ‖d - p‖ = ε / 2 := by field_simp
      rw [this]
      linarith
    · have hval := lval_param (l := l) (d := d) hpl t
      simp only [lineSet, Set.mem_setOf_eq] at hdl ⊢
      have hzero : l.1 * d 0 + l.2.1 * d 1 - l.2.2 = 0 := by linarith
      rw [hzero, mul_zero] at hval
      linarith
    · intro hc
      have hhalf : p + t • (d - p) ∈ halfPlane (!decide (0 < K)) m :=
        mem_halfPlane_of_sign_neg hKne htneg (by rw [hKdef]; exact lval_param hpm t)
      have hnp : p + t • (d - p) ≠ p := by
        intro hcp
        exact halfPlane_subset_compl_lineSet (!decide (0 < K)) m hhalf (by rw [hcp]; exact hpm)
      exact hdisj (decide (0 < K)) m _ (hs _ hc hnp) hhalf
  have hr₁ne : ray₁.Nonempty :=
    hfree d₁ l₁ l₂ K₁ hp₁ hq₁ hp₂ hK₁def hK₁ hne₁ (fun y hy hyp => hside₁ y hy hyp)
  have hr₂ne : ray₂.Nonempty :=
    hfree d₂ l₂ l₁ K₂ hp₂ hq₂ hp₁ hK₂def hK₂ hne₂ (fun y hy hyp => hside₂ y hy hyp)
  have hmem : ∀ z, z ∈ Metric.ball p ε → z ∈ segment ℝ p d₁ ∪ segment ℝ p d₂ →
      z ∈ Q.embedding.trace := by
    intro z hz hzs
    have hzm : z ∈ Metric.ball p ε ∩ Q.embedding.trace := by rw [htr]; exact ⟨hz, hzs⟩
    exact hzm.2
  -- the two wedges
  set P₁ : Set UCPlanar.Plane := cell (!s₁) s₂ ∪ ray₂ with hP₁def
  set P₂ : Set UCPlanar.Plane := cell (!s₁) (!s₂) ∪ ray₂ ∪ ray₁ with hP₂def
  set P₃ : Set UCPlanar.Plane := cell s₁ (!s₂) ∪ ray₁ with hP₃def
  set Wb : Set UCPlanar.Plane := (P₁ ∪ P₂) ∪ P₃ with hWbdef
  have hP₁pre : IsPreconnected P₁ :=
    (hcellpre (!s₁) s₂).subset_closure Set.subset_union_left
      (Set.union_subset subset_closure (hclr₂ s₂))
  have hP₂pre : IsPreconnected P₂ :=
    (hcellpre (!s₁) (!s₂)).subset_closure
      (Set.subset_union_left.trans Set.subset_union_left)
      (Set.union_subset (Set.union_subset subset_closure (hclr₂ (!s₂))) (hclr₁ (!s₁)))
  have hP₃pre : IsPreconnected P₃ :=
    (hcellpre s₁ (!s₂)).subset_closure Set.subset_union_left
      (Set.union_subset subset_closure (hclr₁ s₁))
  obtain ⟨y₂, hy₂⟩ := hr₂ne
  obtain ⟨y₁, hy₁⟩ := hr₁ne
  have hWbpre : IsPreconnected Wb :=
    IsPreconnected.union y₁ (Or.inr (Or.inr hy₁)) (Or.inr hy₁)
      (hP₁pre.union y₂ (Or.inr hy₂) (Or.inl (Or.inr hy₂)) hP₂pre) hP₃pre
  have hWat : cell s₁ s₂ ⊆ Q.embedding.traceᶜ := hcellt s₁ s₂
  have hWbt : Wb ⊆ Q.embedding.traceᶜ :=
    Set.union_subset
      (Set.union_subset (Set.union_subset (hcellt (!s₁) s₂) hray₂t)
        (Set.union_subset (Set.union_subset (hcellt (!s₁) (!s₂)) hray₂t) hray₁t))
      (Set.union_subset (hcellt s₁ (!s₂)) hray₁t)
  have hclWa : ∀ y ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂), y ≠ p →
      y ∈ closure (cell s₁ s₂) := by
    intro y hy hyp
    rcases hy.2 with h | h
    · exact hcl₁ s₁ y ⟨hy.1, h⟩ hyp
    · exact hcl₂ s₂ y ⟨hy.1, h⟩ hyp
  have hclWb : ∀ y ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂), y ≠ p →
      y ∈ closure Wb := by
    intro y hy hyp
    rcases hy.2 with h | h
    · exact closure_mono (fun z hz => Or.inl (Or.inl (Or.inl hz)))
        (hcl₁ (!s₁) y ⟨hy.1, h⟩ hyp)
    · exact closure_mono (fun z hz => Or.inr (Or.inl hz)) (hcl₂ (!s₂) y ⟨hy.1, h⟩ hyp)
  have hbool : ∀ a b : Bool, a = b ∨ a = !b := by decide
  have hcover : Metric.ball p ε ∩ Q.embedding.traceᶜ ⊆ cell s₁ s₂ ∪ Wb := by
    rintro x ⟨hxb, hxt⟩
    have hx₁ : x ∉ segment ℝ p d₁ := fun hc => hxt (hmem x hxb (Or.inl hc))
    have hx₂ : x ∉ segment ℝ p d₂ := fun hc => hxt (hmem x hxb (Or.inr hc))
    by_cases h1 : x ∈ lineSet l₁
    · exact Or.inr (Or.inr (Or.inr ⟨⟨hxb, h1⟩, hx₁⟩))
    by_cases h2 : x ∈ lineSet l₂
    · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨⟨hxb, h2⟩, hx₂⟩)))
    obtain ⟨a, ha⟩ := exists_mem_halfPlane h1
    obtain ⟨b, hb⟩ := exists_mem_halfPlane h2
    have hxcell : x ∈ cell a b := ⟨⟨hxb, ha⟩, hb⟩
    rcases hbool a s₁ with hA | hA <;> rcases hbool b s₂ with hB | hB
    · exact Or.inl (by rw [← hA, ← hB]; exact hxcell)
    · exact Or.inr (Or.inr (Or.inl (by rw [← hA, ← hB]; exact hxcell)))
    · exact Or.inr (Or.inl (Or.inl (Or.inl (by rw [← hA, ← hB]; exact hxcell))))
    · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (by rw [← hA, ← hB]; exact hxcell)))))
  obtain ⟨p₀, hp₀, rfl⟩ := hF
  obtain ⟨q, hqb, hqF⟩ :=
    (mem_closure_iff.mp hpf.1) (Metric.ball p ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  have hqt : q ∉ Q.embedding.trace := connectedComponentIn_subset _ _ hqF
  have key : ∀ W : Set UCPlanar.Plane, IsPreconnected W → W ⊆ Q.embedding.traceᶜ → q ∈ W →
      (∀ y ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂), y ≠ p → y ∈ closure W) →
      Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) ⊆
        frontier (connectedComponentIn Q.embedding.traceᶜ p₀) := by
    intro W hWpre hWt hqW hWcl y hy
    by_cases hyp : y = p
    · rw [hyp]; exact hpf
    · have hWF : W ⊆ connectedComponentIn Q.embedding.traceᶜ p₀ := by
        have h1 : W ⊆ connectedComponentIn Q.embedding.traceᶜ q :=
          hWpre.subset_connectedComponentIn hqW hWt
        rw [connectedComponentIn_eq hqF]
        exact h1
      have hycl : y ∈ closure (connectedComponentIn Q.embedding.traceᶜ p₀) :=
        closure_mono hWF (hWcl y hy hyp)
      have hyt : y ∈ Q.embedding.trace := hmem y hy.1 hy.2
      have hynot : y ∉ connectedComponentIn Q.embedding.traceᶜ p₀ := fun hc =>
        (connectedComponentIn_subset _ _ hc) hyt
      rw [(isOpen_isFace Q ⟨p₀, hp₀, rfl⟩).frontier_eq]
      exact ⟨hycl, hynot⟩
  rcases hcover ⟨hqb, hqt⟩ with h | h
  · exact key (cell s₁ s₂) (hcellpre s₁ s₂) hWat h hclWa
  · exact key Wb hWbpre hWbt h hclWb


/-- **Two-sidedness at a corner, stated without naming the two lines.**  If near a point of the
frontier of a face the drawing is two segments radiating from the point and the second is not
along the line of the first, then a smaller ball has both segments on the frontier. -/
theorem corner_subset_frontier_of_local (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    {p d₁ d₂ : UCPlanar.Plane} {ε : ℝ} (hε : 0 < ε)
    (hne₁ : p ≠ d₁) (hne₂ : p ≠ d₂) (hnc : ∀ t : ℝ, d₂ ≠ p + t • (d₁ - p))
    (htr : Metric.ball p ε ∩ Q.embedding.trace
      = Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂))
    (hpf : p ∈ frontier F) :
    ∃ ε' > 0, ε' ≤ ε ∧
      Metric.ball p ε' ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) ⊆ frontier F := by
  obtain ⟨l₁, hl₁, hs₁⟩ := exists_line_of_segmentU p d₁
  obtain ⟨l₂, hl₂, hs₂⟩ := exists_line_of_segmentU p d₂
  have hp₁ : p ∈ lineSet l₁ := hs₁ (left_mem_segment ℝ p d₁)
  have hq₁ : d₁ ∈ lineSet l₁ := hs₁ (right_mem_segment ℝ p d₁)
  have hp₂ : p ∈ lineSet l₂ := hs₂ (left_mem_segment ℝ p d₂)
  have hq₂ : d₂ ∈ lineSet l₂ := hs₂ (right_mem_segment ℝ p d₂)
  have hK₂ : l₁.1 * d₂ 0 + l₁.2.1 * d₂ 1 - l₁.2.2 ≠ 0 := by
    intro hc
    have hd₂ : d₂ ∈ lineSet l₁ := by
      simp only [lineSet, Set.mem_setOf_eq]; linarith
    obtain ⟨t, ht⟩ := exists_param_of_mem_lineSet hl₁ hp₁ hq₁ hne₁ hd₂
    exact hnc t ht
  have hK₁ : l₂.1 * d₁ 0 + l₂.2.1 * d₁ 1 - l₂.2.2 ≠ 0 := by
    intro hc
    have hd₁ : d₁ ∈ lineSet l₂ := by
      simp only [lineSet, Set.mem_setOf_eq]; linarith
    obtain ⟨t, ht⟩ := exists_param_of_mem_lineSet hl₂ hp₂ hd₁ hne₁ hq₂
    exact hnc t ht
  have h₁ : 0 < ‖d₁ - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne₁))
  have h₂ : 0 < ‖d₂ - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne₂))
  refine ⟨min ε (min ‖d₁ - p‖ ‖d₂ - p‖), lt_min hε (lt_min h₁ h₂), min_le_left _ _, ?_⟩
  have hsub : Metric.ball p (min ε (min ‖d₁ - p‖ ‖d₂ - p‖)) ⊆ Metric.ball p ε :=
    Metric.ball_subset_ball (min_le_left _ _)
  have htr' : Metric.ball p (min ε (min ‖d₁ - p‖ ‖d₂ - p‖)) ∩ Q.embedding.trace
      = Metric.ball p (min ε (min ‖d₁ - p‖ ‖d₂ - p‖)) ∩
        (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hy : x ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
        rw [← htr]; exact ⟨hsub hx1, hx2⟩
      exact ⟨hx1, hy.2⟩
    · rintro ⟨hx1, hx2⟩
      have hy : x ∈ Metric.ball p ε ∩ Q.embedding.trace := by
        rw [htr]; exact ⟨hsub hx1, hx2⟩
      exact ⟨hx1, hy.2⟩
  exact corner_subset_frontier Q hF (lt_min hε (lt_min h₁ h₂)) hl₁ hl₂ hp₁ hq₁ hp₂ hq₂
    hne₁ hne₂ hK₁ hK₂ ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) htr' hpf


/-- **Two-sidedness where the drawing is two opposite half lines.** -/
theorem straight_subset_frontier_of_local (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    {p d₁ d₂ : UCPlanar.Plane} {ε t : ℝ} (hε : 0 < ε)
    (hne₁ : p ≠ d₁) (ht : t < 0) (hd₂ : d₂ = p + t • (d₁ - p))
    (htr : Metric.ball p ε ∩ Q.embedding.trace
      = Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂))
    (hpf : p ∈ frontier F) :
    ∃ ε' > 0, ε' ≤ ε ∧
      Metric.ball p ε' ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) ⊆ frontier F := by
  obtain ⟨l, hl, hs⟩ := exists_line_of_segmentU p d₁
  have hp₁ : p ∈ lineSet l := hs (left_mem_segment ℝ p d₁)
  have hq₁ : d₁ ∈ lineSet l := hs (right_mem_segment ℝ p d₁)
  have hq₂ : d₂ ∈ lineSet l := by
    have hval := lval_param (l := l) (d := d₁) hp₁ t
    simp only [lineSet, Set.mem_setOf_eq] at hq₁ ⊢
    rw [hd₂]
    have hzero : l.1 * d₁ 0 + l.2.1 * d₁ 1 - l.2.2 = 0 := by linarith
    rw [hzero, mul_zero] at hval
    linarith
  have h1t : (0:ℝ) < 1 - t := by linarith
  have h1t' : (1:ℝ) - t ≠ 0 := ne_of_gt h1t
  have hmid : p ∈ openSegment ℝ d₁ d₂ := by
    refine ⟨-t / (1 - t), 1 / (1 - t), div_pos (by linarith) h1t, div_pos one_pos h1t,
      by field_simp; ring, ?_⟩
    rw [hd₂]
    match_scalars <;> field_simp <;> ring
  have hd₁₂ : d₁ ≠ d₂ := by
    intro hc
    rw [← hc, openSegment_same, Set.mem_singleton_iff] at hmid
    exact hne₁ hmid
  obtain ⟨ε₁, hε₁, hεseg⟩ := exists_ball_lineSet_subset_segment hl hd₁₂ hmid hq₁ hq₂
  have hsplit : segment ℝ d₁ d₂ = segment ℝ d₁ p ∪ segment ℝ p d₂ :=
    segment_splitU (openSegment_subset_segment ℝ d₁ d₂ hmid)
  refine ⟨min ε ε₁, lt_min hε hε₁, min_le_left _ _, ?_⟩
  have hsub : Metric.ball p (min ε ε₁) ⊆ Metric.ball p ε :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hline : Metric.ball p (min ε ε₁) ∩ Q.embedding.trace ⊆ lineSet l := by
    rintro x ⟨hx1, hx2⟩
    have hy : x ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
      rw [← htr]; exact ⟨hsub hx1, hx2⟩
    rcases hy.2 with h | h
    · exact segment_subset_lineSet hp₁ hq₁ h
    · exact segment_subset_lineSet hp₁ hq₂ h
  have harc : Metric.ball p (min ε ε₁) ∩ lineSet l ⊆ Q.embedding.trace := by
    rintro x ⟨hx1, hx2⟩
    have hx : x ∈ segment ℝ d₁ d₂ :=
      hεseg ⟨Metric.ball_subset_ball (min_le_right _ _) hx1, hx2⟩
    rw [hsplit] at hx
    have hy : x ∈ Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) := by
      refine ⟨hsub hx1, ?_⟩
      rcases hx with h | h
      · exact Or.inl (by rwa [segment_symm] at h)
      · exact Or.inr h
    have hy2 : x ∈ Metric.ball p ε ∩ Q.embedding.trace := by rw [htr]; exact hy
    exact hy2.2
  intro x hx
  refine ball_inter_lineSet_subset_frontier Q hF (lt_min hε hε₁) hl hline harc hpf ⟨hx.1, ?_⟩
  rcases hx.2 with h | h
  · exact segment_subset_lineSet hp₁ hq₁ h
  · exact segment_subset_lineSet hp₁ hq₂ h

/-- **Two-sidedness where the drawing near a point is two half lines.**  Whether the two half
lines are opposite or make a corner, both of them lie on the frontier of any face beside the
point.  The only case excluded is that of two half lines in the same direction, where the
drawing near the point is a single half line and the point is an end of it. -/
theorem two_rays_subset_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F)
    {p d₁ d₂ : UCPlanar.Plane} {ε : ℝ} (hε : 0 < ε)
    (hne₁ : p ≠ d₁) (hne₂ : p ≠ d₂)
    (hopp : ∀ t : ℝ, 0 < t → d₂ ≠ p + t • (d₁ - p))
    (htr : Metric.ball p ε ∩ Q.embedding.trace
      = Metric.ball p ε ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂))
    (hpf : p ∈ frontier F) :
    ∃ ε' > 0, ε' ≤ ε ∧
      Metric.ball p ε' ∩ (segment ℝ p d₁ ∪ segment ℝ p d₂) ⊆ frontier F := by
  by_cases hco : ∃ t : ℝ, d₂ = p + t • (d₁ - p)
  · obtain ⟨t, ht⟩ := hco
    have ht0 : t ≠ 0 := by
      intro hc
      rw [hc, zero_smul, add_zero] at ht
      exact hne₂ ht.symm
    have htneg : t < 0 := by
      rcases lt_or_gt_of_ne ht0 with h | h
      · exact h
      · exact absurd ht (hopp t h)
    exact straight_subset_frontier_of_local Q hF hε hne₁ htneg ht htr hpf
  · rw [not_exists] at hco
    exact corner_subset_frontier_of_local Q hF hε hne₁ hne₂ hco htr hpf


end UCPlanar.Support
