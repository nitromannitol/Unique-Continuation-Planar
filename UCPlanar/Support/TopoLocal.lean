/- The local structure of a polygonal drawing.  Every arc of the drawing is covered by finitely
many segments lying on it, so inside a ball all but finitely many points of the drawing have a
neighbourhood in which the drawing is exactly a piece of one line.  Beside a face this turns the
straight local model into two-sidedness: off the finite set, the frontier of a face contains a
whole neighbourhood of each of its points in the drawing. -/
import UCPlanar.Support.TopoFaceWalks
import UCPlanar.Support.TopoProper
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- Two points of the plane agreeing in both coordinates are equal. -/
theorem plane_ext {p q : UCPlanar.Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- A point of a segment other than its two ends lies in the open segment. -/
theorem mem_openSegment_of_ne {a b p : UCPlanar.Plane} (hp : p ∈ segment ℝ a b)
    (ha : p ≠ a) (hb : p ≠ b) : p ∈ openSegment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, hx⟩ := hp
  refine ⟨α, β, ?_, ?_, hαβ, hx⟩
  · rcases hα.lt_or_eq with h | h
    · exact h
    · exfalso
      have hβ1 : β = 1 := by linarith [h]
      apply hb
      rw [← hx, ← h, hβ1]
      simp
  · rcases hβ.lt_or_eq with h | h
    · exact h
    · exfalso
      have hα1 : α = 1 := by linarith [h]
      apply ha
      rw [← hx, ← h, hα1]
      simp

/-- A line contains the segment between any two of its points. -/
theorem segment_subset_lineSet {l : ℝ × ℝ × ℝ} {a b : UCPlanar.Plane}
    (ha : a ∈ lineSet l) (hb : b ∈ lineSet l) : segment ℝ a b ⊆ lineSet l := by
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  simp only [lineSet, Set.mem_setOf_eq] at ha hb ⊢
  have h0 : (u • a + v • b) 0 = u * a 0 + v * b 0 := by simp
  have h1 : (u • a + v • b) 1 = u * a 1 + v * b 1 := by simp
  rw [h0, h1]
  linear_combination u * ha + v * hb + l.2.2 * huv

/-- A segment of the plane is compact. -/
theorem isCompact_segmentU (a b : UCPlanar.Plane) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image' ℝ a b]
  exact isCompact_Icc.image (by fun_prop)

/-- The identification with the Euclidean plane carries segments to segments. -/
theorem image_segment_planeHomeo (u v : UCPlanar.Plane) :
    planeHomeo '' (segment ℝ u v) = segment ℝ (planeHomeo u) (planeHomeo v) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a • u + b • v, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩

/-- **Every segment lies on a line.** -/
theorem exists_line_of_segmentU (u v : UCPlanar.Plane) :
    ∃ l : ℝ × ℝ × ℝ, (l.1 ≠ 0 ∨ l.2.1 ≠ 0) ∧ segment ℝ u v ⊆ lineSet l := by
  obtain ⟨a, b, c, hab, hseg⟩ := exists_line_of_segment (planeHomeo u) (planeHomeo v)
  refine ⟨(a, b, c), hab, ?_⟩
  intro x hx
  have hx' : planeHomeo x ∈ segment ℝ (planeHomeo u) (planeHomeo v) := by
    rw [← image_segment_planeHomeo]
    exact ⟨x, hx, rfl⟩
  have hlin := hseg _ hx'
  simp only [lineSet, Set.mem_setOf_eq]
  rw [planeHomeo_apply x 0, planeHomeo_apply x 1] at hlin
  exact hlin

/-- **Every point of a line is an affine combination of two distinct points of it.**  The two
coefficient pairs solve the same homogeneous equation, whose solution space is a line through
the origin, so the difference vectors are proportional. -/
theorem exists_param_of_mem_lineSet {l : ℝ × ℝ × ℝ} (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    {p q x : UCPlanar.Plane} (hp : p ∈ lineSet l) (hq : q ∈ lineSet l) (hpq : p ≠ q)
    (hx : x ∈ lineSet l) : ∃ t : ℝ, x = p + t • (q - p) := by
  simp only [lineSet, Set.mem_setOf_eq] at hp hq hx
  have hd0 : l.1 * (q 0 - p 0) + l.2.1 * (q 1 - p 1) = 0 := by linarith
  have he0 : l.1 * (x 0 - p 0) + l.2.1 * (x 1 - p 1) = 0 := by linarith
  rcases eq_or_ne l.1 0 with hA | hA
  · have hB : l.2.1 ≠ 0 := by
      rcases hl with h | h
      · exact absurd hA h
      · exact h
    rw [hA] at hd0 he0
    have h1d : q 1 - p 1 = 0 := by
      have h : l.2.1 * (q 1 - p 1) = 0 := by linarith
      exact (mul_eq_zero.mp h).resolve_left hB
    have h1e : x 1 - p 1 = 0 := by
      have h : l.2.1 * (x 1 - p 1) = 0 := by linarith
      exact (mul_eq_zero.mp h).resolve_left hB
    have hd0ne : q 0 - p 0 ≠ 0 := by
      intro hc
      exact hpq (plane_ext (by linarith) (by linarith))
    refine ⟨(x 0 - p 0) / (q 0 - p 0), plane_ext ?_ ?_⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    · rw [div_mul_cancel₀ _ hd0ne]; ring
    · rw [h1d, mul_zero, add_zero]; linarith
  · have h1d : q 1 - p 1 ≠ 0 := by
      intro hc
      rw [hc, mul_zero, add_zero] at hd0
      have h : q 0 - p 0 = 0 := (mul_eq_zero.mp hd0).resolve_left hA
      exact hpq (plane_ext (by linarith) (by linarith))
    have key : l.1 * ((x 0 - p 0) * (q 1 - p 1)) = l.1 * ((x 1 - p 1) * (q 0 - p 0)) := by
      linear_combination (q 1 - p 1) * he0 - (x 1 - p 1) * hd0
    have key2 : (x 0 - p 0) * (q 1 - p 1) = (x 1 - p 1) * (q 0 - p 0) := mul_left_cancel₀ hA key
    refine ⟨(x 1 - p 1) / (q 1 - p 1), plane_ext ?_ ?_⟩ <;>
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    · field_simp
      linarith [key2]
    · rw [div_mul_cancel₀ _ h1d]; ring

/-- **A line is determined by two distinct points on it.**  Two lines through the same two
points have the same point set, so two lines with different point sets meet at most once. -/
theorem lineSet_eq_of_two_points {l m : ℝ × ℝ × ℝ} (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    {p q : UCPlanar.Plane} (hpq : p ≠ q)
    (hpl : p ∈ lineSet l) (hql : q ∈ lineSet l) (hpm : p ∈ lineSet m) (hqm : q ∈ lineSet m) :
    lineSet l ⊆ lineSet m := by
  intro x hx
  obtain ⟨t, rfl⟩ := exists_param_of_mem_lineSet hl hpl hql hpq hx
  simp only [lineSet, Set.mem_setOf_eq] at hpm hqm ⊢
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (1 - t) * hpm + t * hqm

/-- **A polygonal carrier is covered by finitely many segments contained in it.** -/
theorem exists_segments_of_poly : ∀ vs : List Schoenflies.Plane,
    ∃ P : Set (Schoenflies.Plane × Schoenflies.Plane), P.Finite ∧
      (∀ q ∈ P, segment ℝ q.1 q.2 ⊆ Schoenflies.poly vs) ∧
      ∀ x ∈ Schoenflies.poly vs, ∃ q ∈ P, x ∈ segment ℝ q.1 q.2 := by
  intro vs
  induction vs with
  | nil => exact ⟨∅, Set.finite_empty, by simp, by simp⟩
  | cons u rest ih =>
    rcases rest with _ | ⟨v, rest'⟩
    · refine ⟨{(u, u)}, Set.finite_singleton _, ?_, ?_⟩
      · rintro q hq
        rw [Set.mem_singleton_iff] at hq
        subst hq
        simp [segment_same]
      · intro x hx
        rw [Schoenflies.poly_singleton, Set.mem_singleton_iff] at hx
        exact ⟨(u, u), rfl, by simp [segment_same, hx]⟩
    · obtain ⟨P, hPfin, hPsub, hPcov⟩ := ih
      refine ⟨insert (u, v) P, hPfin.insert _, ?_, ?_⟩
      · rintro q hq
        rcases hq with hq | hq
        · subst hq; exact Set.subset_union_left
        · exact (hPsub q hq).trans Set.subset_union_right
      · intro x hx
        rw [Schoenflies.poly_cons_cons] at hx
        rcases hx with hx | hx
        · exact ⟨(u, v), Set.mem_insert _ _, hx⟩
        · obtain ⟨q, hq, hxq⟩ := hPcov x hx
          exact ⟨q, Set.mem_insert_of_mem _ hq, hxq⟩

/-- **The arc of a drawn edge is covered by finitely many segments lying on it.** -/
theorem exists_segments_of_arcOf (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    ∃ P : Set (UCPlanar.Plane × UCPlanar.Plane), P.Finite ∧
      (∀ q ∈ P, segment ℝ q.1 q.2 ⊆ E.arcOf e) ∧
      ∀ x ∈ E.arcOf e, ∃ q ∈ P, x ∈ segment ℝ q.1 q.2 := by
  induction e with
  | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    obtain ⟨vs, hvs⟩ := E.edge_polygonal hxy
    have harc : planeHomeo '' E.arcOf s(x, y) = Schoenflies.poly vs := by
      rw [arcOf_eq E hxy]; exact hvs
    obtain ⟨P, hPfin, hPsub, hPcov⟩ := exists_segments_of_poly vs
    refine ⟨(fun q : Schoenflies.Plane × Schoenflies.Plane =>
      (planeHomeo.symm q.1, planeHomeo.symm q.2)) '' P, hPfin.image _, ?_, ?_⟩
    · rintro q ⟨q₀, hq₀, rfl⟩
      have h1 : planeHomeo '' segment ℝ (planeHomeo.symm q₀.1) (planeHomeo.symm q₀.2)
          = segment ℝ q₀.1 q₀.2 := by
        rw [image_segment_planeHomeo]
        simp
      have h2 : planeHomeo '' segment ℝ (planeHomeo.symm q₀.1) (planeHomeo.symm q₀.2)
          ⊆ planeHomeo '' E.arcOf s(x, y) := by
        rw [h1, harc]; exact hPsub q₀ hq₀
      exact (Set.image_subset_image_iff planeHomeo.injective).mp h2
    · intro z hz
      have hz' : planeHomeo z ∈ Schoenflies.poly vs := by
        rw [← harc]; exact ⟨z, hz, rfl⟩
      obtain ⟨q₀, hq₀, hzq⟩ := hPcov _ hz'
      refine ⟨(planeHomeo.symm q₀.1, planeHomeo.symm q₀.2), ⟨q₀, hq₀, rfl⟩, ?_⟩
      have h1 : planeHomeo '' segment ℝ (planeHomeo.symm q₀.1) (planeHomeo.symm q₀.2)
          = segment ℝ q₀.1 q₀.2 := by
        rw [image_segment_planeHomeo]; simp
      have hmem : planeHomeo z ∈ planeHomeo '' segment ℝ (planeHomeo.symm q₀.1)
          (planeHomeo.symm q₀.2) := by rw [h1]; exact hzq
      obtain ⟨w, hw, hwz⟩ := hmem
      rwa [planeHomeo.injective hwz] at hw

/-- **Cutting a segment at one of its points loses nothing.**  The two halves cover it. -/
theorem segment_splitU {a b p : UCPlanar.Plane} (hp : p ∈ segment ℝ a b) :
    segment ℝ a b = segment ℝ a p ∪ segment ℝ p b := by
  refine subset_antisymm ?_ (union_subset
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hp)
    ((convex_segment a b).segment_subset hp (right_mem_segment ℝ a b)))
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hp
  rintro x ⟨u, v, hu, hv, huv, rfl⟩
  rcases le_or_gt v β with hvβ | hvβ
  · left
    rcases eq_or_lt_of_le hβ with rfl | hβpos
    · have hv0 : v = 0 := le_antisymm hvβ hv
      have hu1 : u = 1 := by linarith
      subst hv0; subst hu1
      simp only [zero_smul, add_zero, one_smul]
      exact left_mem_segment ℝ a _
    · refine ⟨1 - v / β, v / β, by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hvβ hβpos.le, by positivity, by ring, ?_⟩
      have hβne : β ≠ 0 := ne_of_gt hβpos
      have hcoef : (1 - v / β) + (v / β) * α = u := by
        have hα' : α = 1 - β := by linarith
        field_simp
        nlinarith [hαβ, huv]
      have hcoef2 : (v / β) * β = v := div_mul_cancel₀ v hβne
      rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, hcoef, hcoef2]
  · right
    have hβlt : β < 1 := by linarith
    have hαpos : 0 < α := by
      have hα' : α = 1 - β := by linarith
      linarith
    have hαne : α ≠ 0 := ne_of_gt hαpos
    have hual : u ≤ α := by
      have hα' : α = 1 - β := by linarith
      linarith
    refine ⟨u / α, 1 - u / α, div_nonneg hu hαpos.le,
      by rw [sub_nonneg]; exact div_le_one_of_le₀ hual hαpos.le, by ring, ?_⟩
    have hcoef : (u / α) * β + (1 - u / α) = v := by
      have hα' : α = 1 - β := by linarith
      have hv' : v = 1 - u := by linarith
      subst hα'
      subst hv'
      field_simp
      ring
    have hcoef2 : (u / α) * α = u := div_mul_cancel₀ u hαne
    rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, hcoef2, hcoef]

/-- A point of the line through an interior point of a segment in the direction of one end stays
on the segment while its parameter stays in range. -/
theorem mem_segment_of_param {a b p : UCPlanar.Plane} {α β t : ℝ}
    (hβ : 0 < β) (hαβ : α + β = 1) (hp : α • a + β • b = p)
    (ht1 : t ≤ 1) (ht2 : -α ≤ t * β) : p + t • (a - p) ∈ segment ℝ a b := by
  refine ⟨α + t * β, (1 - t) * β, by linarith, by nlinarith, by nlinarith, ?_⟩
  subst hp
  match_scalars
  · linear_combination t * hαβ
  · ring

/-- **A short piece of the line through an interior point of a segment stays on the segment.** -/
theorem exists_ball_lineSet_subset_segment {l : ℝ × ℝ × ℝ} (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    {a b p : UCPlanar.Plane} (hab : a ≠ b) (hp : p ∈ openSegment ℝ a b)
    (ha : a ∈ lineSet l) (hb : b ∈ lineSet l) :
    ∃ ε > 0, Metric.ball p ε ∩ lineSet l ⊆ segment ℝ a b := by
  obtain ⟨α, β, hα, hβ, hαβ, hpe⟩ := hp
  have hpa : p ≠ a := by
    intro hc
    apply hab
    have hmem : a ∈ openSegment ℝ a b :=
      ⟨α, β, hα, hβ, hαβ, by rw [hpe]; exact hc⟩
    exact left_mem_openSegment_iff.mp hmem
  have hpl : p ∈ lineSet l :=
    segment_subset_lineSet ha hb (openSegment_subset_segment ℝ a b ⟨α, β, hα, hβ, hαβ, hpe⟩)
  have hne : a - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpa)
  have hnorm : 0 < ‖a - p‖ := norm_pos_iff.mpr hne
  refine ⟨min ‖a - p‖ ((α / β) * ‖a - p‖), lt_min hnorm (by positivity), ?_⟩
  rintro x ⟨hxb, hxl⟩
  obtain ⟨t, rfl⟩ := exists_param_of_mem_lineSet hl hpl ha hpa hxl
  have hd : |t| * ‖a - p‖ < min ‖a - p‖ ((α / β) * ‖a - p‖) := by
    have hdist : dist (p + t • (a - p)) p = |t| * ‖a - p‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rwa [← hdist]
  have h1 : |t| < 1 := by
    have := lt_of_lt_of_le hd (min_le_left _ _)
    nlinarith
  have h2 : |t| < α / β := by
    have := lt_of_lt_of_le hd (min_le_right _ _)
    nlinarith
  refine mem_segment_of_param hβ hαβ hpe ?_ ?_
  · have := le_abs_self t
    linarith
  · have h3 : -t ≤ |t| := neg_le_abs t
    have h4 : -t < α / β := lt_of_le_of_lt h3 h2
    have h5 : -t * β < α := (lt_div_iff₀ hβ).mp h4
    linarith

/-- **The drawing near a bounded set is covered by finitely many segments lying on it.**  Only
finitely many arcs reach the set, and each arc is covered by finitely many of its own
segments. -/
theorem exists_local_segments (Q : UCPlanar.PeriodicPlaneGraph V) (p₀ : UCPlanar.Plane)
    (r : ℝ) :
    ∃ PT : Set (UCPlanar.Plane × UCPlanar.Plane), PT.Finite ∧
      (∀ q ∈ PT, segment ℝ q.1 q.2 ⊆ Q.embedding.trace) ∧
      ∀ x ∈ Metric.closedBall p₀ r, x ∈ Q.embedding.trace →
        ∃ q ∈ PT, x ∈ segment ℝ q.1 q.2 := by
  classical
  obtain ⟨T, hTfin, hTsub, hTcov⟩ := exists_finite_trace_near Q p₀ r
  have hP : ∀ e : Sym2 V, ∃ P : Set (UCPlanar.Plane × UCPlanar.Plane), P.Finite ∧
      (∀ q ∈ P, segment ℝ q.1 q.2 ⊆ Q.embedding.arcOf e) ∧
      (e ∈ T → ∀ x ∈ Q.embedding.arcOf e, ∃ q ∈ P, x ∈ segment ℝ q.1 q.2) := by
    intro e
    by_cases he : e ∈ T
    · obtain ⟨P, h1, h2, h3⟩ := exists_segments_of_arcOf Q.embedding (hTsub he)
      exact ⟨P, h1, h2, fun _ => h3⟩
    · exact ⟨∅, Set.finite_empty, by simp, fun hc => absurd hc he⟩
  choose Pf hPfin hPsub hPcov using hP
  refine ⟨⋃ e ∈ T, Pf e, hTfin.biUnion (fun e _ => hPfin e), ?_, ?_⟩
  · intro q hq
    obtain ⟨e, he, hqe⟩ := Set.mem_iUnion₂.mp hq
    exact (hPsub e q hqe).trans (arcOf_subset_trace Q.embedding)
  · intro x hx hxt
    obtain ⟨e, he, hxe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding (hTcov x hx hxt)
    obtain ⟨q, hq, hxq⟩ := hPcov e he x hxe
    exact ⟨q, Set.mem_iUnion₂.mpr ⟨e, he, hq⟩, hxq⟩

/-- **The drawing is locally a line off a finite set.**  Inside any ball, all but finitely many
points of the drawing have a neighbourhood in which the drawing is exactly the piece of one
line: near such a point the drawing lies on the line and the line lies on the drawing.  The
excluded set is the ends of the finitely many segments covering the arcs that reach the ball,
together with the points where two of the lines carrying those segments cross. -/
theorem exists_finite_singular (Q : UCPlanar.PeriodicPlaneGraph V) (p₀ : UCPlanar.Plane)
    (r : ℝ) :
    ∃ Sg : Set UCPlanar.Plane, Sg.Finite ∧
      ∀ p ∈ Metric.ball p₀ r, p ∈ Q.embedding.trace → p ∉ Sg →
        ∃ ε > 0, ∃ l : ℝ × ℝ × ℝ, (l.1 ≠ 0 ∨ l.2.1 ≠ 0) ∧
          Metric.ball p ε ∩ Q.embedding.trace ⊆ lineSet l ∧
          Metric.ball p ε ∩ lineSet l ⊆ Q.embedding.trace := by
  classical
  obtain ⟨PT, hPTfin, hPTsub, hPTcov⟩ := exists_local_segments Q p₀ r
  choose lf hlf1 hlf2 using
    (fun q : UCPlanar.Plane × UCPlanar.Plane => exists_line_of_segmentU q.1 q.2)
  set S : Set UCPlanar.Plane := (fun q : UCPlanar.Plane × UCPlanar.Plane => q.1) '' PT ∪
    (fun q : UCPlanar.Plane × UCPlanar.Plane => q.2) '' PT with hS
  have hSfin : S.Finite := (hPTfin.image _).union (hPTfin.image _)
  set X : Set UCPlanar.Plane := {x | ∃ q₁ ∈ PT, ∃ q₂ ∈ PT,
    lineSet (lf q₁) ≠ lineSet (lf q₂) ∧ x ∈ lineSet (lf q₁) ∧ x ∈ lineSet (lf q₂)} with hX
  have hXfin : X.Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion hPTfin (fun q₁ _ =>
      Set.Finite.biUnion hPTfin (fun q₂ _ =>
        (?_ : {x : UCPlanar.Plane | lineSet (lf q₁) ≠ lineSet (lf q₂) ∧
          x ∈ lineSet (lf q₁) ∧ x ∈ lineSet (lf q₂)}.Finite)))) ?_
    · refine Set.Subsingleton.finite ?_
      rintro x ⟨hne, hx1, hx2⟩ y ⟨-, hy1, hy2⟩
      by_contra hxy
      exact hne (Set.Subset.antisymm
        (lineSet_eq_of_two_points (hlf1 q₁) hxy hx1 hy1 hx2 hy2)
        (lineSet_eq_of_two_points (hlf1 q₂) hxy hx2 hy2 hx1 hy1))
    · rintro x ⟨q₁, hq₁, q₂, hq₂, hne, hx1, hx2⟩
      exact Set.mem_iUnion₂.mpr ⟨q₁, hq₁, Set.mem_iUnion₂.mpr ⟨q₂, hq₂, ⟨hne, hx1, hx2⟩⟩⟩
  refine ⟨S ∪ X, hSfin.union hXfin, ?_⟩
  intro p hp hpt hpS
  have hpS' : p ∉ S := fun hc => hpS (Or.inl hc)
  have hpX : p ∉ X := fun hc => hpS (Or.inr hc)
  obtain ⟨q, hq, hpq⟩ := hPTcov p (Metric.ball_subset_closedBall hp) hpt
  have hq1 : p ≠ q.1 := fun hc => hpS' (Or.inl ⟨q, hq, hc.symm⟩)
  have hq2 : p ≠ q.2 := fun hc => hpS' (Or.inr ⟨q, hq, hc.symm⟩)
  have hq12 : q.1 ≠ q.2 := by
    intro hc
    rw [hc, segment_same, Set.mem_singleton_iff] at hpq
    exact hq2 hpq
  have hop : p ∈ openSegment ℝ q.1 q.2 := mem_openSegment_of_ne hpq hq1 hq2
  have hl1 : q.1 ∈ lineSet (lf q) := hlf2 q (left_mem_segment ℝ q.1 q.2)
  have hl2 : q.2 ∈ lineSet (lf q) := hlf2 q (right_mem_segment ℝ q.1 q.2)
  obtain ⟨ε₁, hε₁, hεseg⟩ :=
    exists_ball_lineSet_subset_segment (hlf1 q) hq12 hop hl1 hl2
  set Z : Set UCPlanar.Plane := ⋃ q' ∈ {q' ∈ PT | p ∉ segment ℝ q'.1 q'.2},
    segment ℝ q'.1 q'.2 with hZ
  have hZclosed : IsClosed Z :=
    Set.Finite.isClosed_biUnion (hPTfin.subset (fun q' hq' => hq'.1))
      (fun q' _ => (isCompact_segmentU q'.1 q'.2).isClosed)
  have hpZ : p ∉ Z := by
    intro hc
    obtain ⟨q', hq', hpq'⟩ := Set.mem_iUnion₂.mp hc
    exact hq'.2 hpq'
  obtain ⟨ε₃, hε₃, hεZ⟩ := Metric.isOpen_iff.mp hZclosed.isOpen_compl p hpZ
  have hε₂ : 0 < r - dist p p₀ := by
    have := Metric.mem_ball.mp hp
    linarith
  refine ⟨min ε₁ (min (r - dist p p₀) ε₃), lt_min hε₁ (lt_min hε₂ hε₃), lf q, hlf1 q, ?_, ?_⟩
  · rintro x ⟨hxb, hxt⟩
    have hxball : x ∈ Metric.closedBall p₀ r := by
      have h1 : dist x p < r - dist p p₀ :=
        lt_of_lt_of_le (Metric.mem_ball.mp hxb) ((min_le_right _ _).trans (min_le_left _ _))
      have h2 := dist_triangle x p p₀
      exact Metric.mem_closedBall.mpr (by linarith)
    obtain ⟨q', hq', hxq'⟩ := hPTcov x hxball hxt
    have hpq' : p ∈ segment ℝ q'.1 q'.2 := by
      by_contra hc
      have hxZ : x ∈ Z := Set.mem_iUnion₂.mpr ⟨q', ⟨hq', hc⟩, hxq'⟩
      exact (hεZ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hxb)
        ((min_le_right _ _).trans (min_le_right _ _))))) hxZ
    have hpl' : p ∈ lineSet (lf q') := hlf2 q' hpq'
    have hplq : p ∈ lineSet (lf q) := hlf2 q hpq
    have heq : lineSet (lf q') = lineSet (lf q) := by
      by_contra hne
      exact hpX ⟨q', hq', q, hq, hne, hpl', hplq⟩
    rw [← heq]
    exact hlf2 q' hxq'
  · rintro x ⟨hxb, hxl⟩
    have hxseg : x ∈ segment ℝ q.1 q.2 :=
      hεseg ⟨Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hxb) (min_le_left _ _)), hxl⟩
    exact hPTsub q hq hxseg

/-- **The frontier of a face is relatively open in the drawing off a finite set.**  Off the
singular points, the drawing near a frontier point is a straight piece, the side of the line
carrying the face is convex and misses the drawing, so the whole straight piece is on the
frontier.  This is the two-sidedness of an edge at every non-singular point. -/
theorem exists_finite_singular_frontier (Q : UCPlanar.PeriodicPlaneGraph V)
    (p₀ : UCPlanar.Plane) (r : ℝ) :
    ∃ Sg : Set UCPlanar.Plane, Sg.Finite ∧
      ∀ F, Q.embedding.IsFace F → ∀ p ∈ Metric.ball p₀ r, p ∈ frontier F → p ∉ Sg →
        ∃ ε > 0, Metric.ball p ε ∩ Q.embedding.trace ⊆ frontier F := by
  obtain ⟨Sg, hfin, hSg⟩ := exists_finite_singular Q p₀ r
  refine ⟨Sg, hfin, ?_⟩
  intro F hF p hp hpf hpS
  obtain ⟨ε, hε, l, hl, hline, harc⟩ :=
    hSg p hp (frontier_isFace_subset_trace Q hF hpf) hpS
  refine ⟨ε, hε, ?_⟩
  have hfr : Metric.ball p ε ∩ lineSet l ⊆ frontier F :=
    ball_inter_lineSet_subset_frontier Q hF hε hl hline harc hpf
  rintro x ⟨hxb, hxt⟩
  exact hfr ⟨hxb, hline ⟨hxb, hxt⟩⟩

/-- **The local structure of the drawing at a point.**  Near any point the drawing is exactly
finitely many segments radiating from that point: the segments covering the arcs that do not
already pass through the point are pushed away, and each segment through it is cut there into
its two halves. -/
theorem exists_radial_local (Q : UCPlanar.PeriodicPlaneGraph V) (p : UCPlanar.Plane) :
    ∃ ε > 0, ∃ D : Set UCPlanar.Plane, D.Finite ∧
      Metric.ball p ε ∩ Q.embedding.trace
        = Metric.ball p ε ∩ ⋃ d ∈ D, segment ℝ p d := by
  classical
  obtain ⟨PT, hPTfin, hPTsub, hPTcov⟩ := exists_local_segments Q p 1
  set PP : Set (UCPlanar.Plane × UCPlanar.Plane) := {q ∈ PT | p ∈ segment ℝ q.1 q.2} with hPP
  have hPPfin : PP.Finite := hPTfin.subset (fun q hq => hq.1)
  set Z : Set UCPlanar.Plane := ⋃ q' ∈ {q' ∈ PT | p ∉ segment ℝ q'.1 q'.2},
    segment ℝ q'.1 q'.2 with hZ
  have hZclosed : IsClosed Z :=
    Set.Finite.isClosed_biUnion (hPTfin.subset (fun q' hq' => hq'.1))
      (fun q' _ => (isCompact_segmentU q'.1 q'.2).isClosed)
  have hpZ : p ∉ Z := by
    intro hc
    obtain ⟨q', hq', hpq'⟩ := Set.mem_iUnion₂.mp hc
    exact hq'.2 hpq'
  obtain ⟨ε₃, hε₃, hεZ⟩ := Metric.isOpen_iff.mp hZclosed.isOpen_compl p hpZ
  refine ⟨min 1 ε₃, lt_min one_pos hε₃,
    (fun q : UCPlanar.Plane × UCPlanar.Plane => q.1) '' PP ∪
      (fun q : UCPlanar.Plane × UCPlanar.Plane => q.2) '' PP,
    (hPPfin.image _).union (hPPfin.image _), ?_⟩
  have hsplit : ∀ q ∈ PP, segment ℝ q.1 q.2 = segment ℝ p q.1 ∪ segment ℝ p q.2 := by
    intro q hq
    rw [segment_splitU hq.2, segment_symm]
  ext x
  constructor
  · rintro ⟨hxb, hxt⟩
    refine ⟨hxb, ?_⟩
    have hxc : x ∈ Metric.closedBall p 1 :=
      Metric.closedBall_subset_closedBall (min_le_left 1 ε₃)
        (Metric.ball_subset_closedBall hxb)
    obtain ⟨q, hq, hxq⟩ := hPTcov x hxc hxt
    have hpq : p ∈ segment ℝ q.1 q.2 := by
      by_contra hc
      have hxZ : x ∈ Z := Set.mem_iUnion₂.mpr ⟨q, ⟨hq, hc⟩, hxq⟩
      exact hεZ (Metric.mem_ball.mpr
        (lt_of_lt_of_le (Metric.mem_ball.mp hxb) (min_le_right 1 ε₃))) hxZ
    have hqPP : q ∈ PP := ⟨hq, hpq⟩
    rw [hsplit q hqPP] at hxq
    rcases hxq with hxq | hxq
    · exact Set.mem_biUnion (Or.inl ⟨q, hqPP, rfl⟩) hxq
    · exact Set.mem_biUnion (Or.inr ⟨q, hqPP, rfl⟩) hxq
  · rintro ⟨hxb, hxd⟩
    refine ⟨hxb, ?_⟩
    obtain ⟨d, hd, hxd'⟩ := Set.mem_iUnion₂.mp hxd
    rcases hd with ⟨q, hqPP, rfl⟩ | ⟨q, hqPP, rfl⟩
    · exact hPTsub q hqPP.1 (by rw [hsplit q hqPP]; exact Or.inl hxd')
    · exact hPTsub q hqPP.1 (by rw [hsplit q hqPP]; exact Or.inr hxd')

end UCPlanar.Support
