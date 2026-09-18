/- The faces of a periodic plane drawing form a locally finite family: near a point the drawing
is the drawing of finitely many polygonal arcs, each arc lies on finitely many lines, and a
convex open set minus a closed set contained in finitely many lines has only finitely many
components, because the open sign cells of the lines are convex and every component contains
one. -/
import UCPlanar.Support.TopoFaceLocal
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

/-- **Finitely many preconnected pieces bound the number of components.**  If each piece is a
preconnected subset of a set and every component of the set meets a piece, then the set has
finitely many components. -/
theorem finite_components_of_family {X ι : Type*} [TopologicalSpace X] [Finite ι] (S : Set X)
    (D : ι → Set X) (hpre : ∀ i, IsPreconnected (D i)) (hsub : ∀ i, D i ⊆ S)
    (hmeet : ∀ q ∈ S, ∃ i, ∃ d ∈ D i, d ∈ connectedComponentIn S q) :
    {C | ∃ q ∈ S, C = connectedComponentIn S q}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.finite_range (fun i : ι => ⋃ d ∈ D i, connectedComponentIn S d)) ?_
  rintro C ⟨q, hq, rfl⟩
  obtain ⟨i, d, hdD, hdc⟩ := hmeet q hq
  refine ⟨i, ?_⟩
  have hDsub : D i ⊆ connectedComponentIn S d :=
    (hpre i).subset_connectedComponentIn hdD (hsub i)
  have hdq : connectedComponentIn S q = connectedComponentIn S d := connectedComponentIn_eq hdc
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset ?_
    intro e he
    have hde : connectedComponentIn S d = connectedComponentIn S e :=
      connectedComponentIn_eq (hDsub he)
    rw [hdq, hde]
  · intro x hx
    refine Set.mem_biUnion hdD ?_
    rw [← hdq]
    exact hx

/-- A line of the plane, read off the coefficients of its equation. -/
def lineSet (l : ℝ × ℝ × ℝ) : Set UCPlanar.Plane :=
  {x | l.1 * x 0 + l.2.1 * x 1 = l.2.2}

/-- One of the two open half planes a line bounds. -/
def halfPlane (s : Bool) (l : ℝ × ℝ × ℝ) : Set UCPlanar.Plane :=
  if s then {x | l.2.2 < l.1 * x 0 + l.2.1 * x 1} else {x | l.1 * x 0 + l.2.1 * x 1 < l.2.2}

/-- The left-hand side of a line equation is linear. -/
theorem isLinearMap_coord (a b : ℝ) :
    IsLinearMap ℝ (fun x : UCPlanar.Plane => a * x 0 + b * x 1) := by
  constructor
  · intro x y
    simp only [Pi.add_apply]
    ring
  · intro r x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- A line is closed. -/
theorem isClosed_lineSet (l : ℝ × ℝ × ℝ) : IsClosed (lineSet l) := by
  have hcont : Continuous (fun x : UCPlanar.Plane => l.1 * x 0 + l.2.1 * x 1) :=
    (continuous_const.mul (continuous_apply 0)).add (continuous_const.mul (continuous_apply 1))
  exact isClosed_eq hcont continuous_const

theorem convex_halfPlane (s : Bool) (l : ℝ × ℝ × ℝ) : Convex ℝ (halfPlane s l) := by
  unfold halfPlane
  split
  · exact convex_halfSpace_gt (isLinearMap_coord l.1 l.2.1) l.2.2
  · exact convex_halfSpace_lt (isLinearMap_coord l.1 l.2.1) l.2.2

theorem halfPlane_subset_compl_lineSet (s : Bool) (l : ℝ × ℝ × ℝ) :
    halfPlane s l ⊆ (lineSet l)ᶜ := by
  intro x hx hcon
  rw [lineSet, Set.mem_setOf_eq] at hcon
  unfold halfPlane at hx
  split at hx
  · exact absurd hcon (ne_of_gt hx)
  · exact absurd hcon (ne_of_lt hx)

theorem exists_mem_halfPlane {l : ℝ × ℝ × ℝ} {x : UCPlanar.Plane} (h : x ∉ lineSet l) :
    ∃ s : Bool, x ∈ halfPlane s l := by
  rw [lineSet, Set.mem_setOf_eq] at h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ⟨false, by unfold halfPlane; simpa using hlt⟩
  · exact ⟨true, by unfold halfPlane; simpa using hgt⟩

/-- **A line has empty interior.**  Moving off a point of the line in the direction of the
coefficient vector leaves the line at once. -/
theorem eq_empty_of_isOpen_subset_lineSet (l : ℝ × ℝ × ℝ) (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    (U : Set UCPlanar.Plane) (hU : IsOpen U) (hsub : U ⊆ lineSet l) : U = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hpos : 0 < l.1 * l.1 + l.2.1 * l.2.1 := by
    rcases hl with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg l.2.1]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg l.1]
  set v : UCPlanar.Plane := ![l.1, l.2.1] with hv
  have hcont : Continuous (fun s : ℝ => x + s • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen ((fun s : ℝ => x + s • v) ⁻¹' U) := hU.preimage hcont
  have hzero : (0 : ℝ) ∈ (fun s : ℝ => x + s • v) ⁻¹' U := by simpa using hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have hmem : (ε / 2 : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have h1 := hsub (hball hmem)
  have h2 := hsub hx
  rw [lineSet, Set.mem_setOf_eq] at h1 h2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h1
  nlinarith [h1, h2, hpos, hε]

/-- **A finite union of lines has empty interior.** -/
theorem eq_empty_of_isOpen_subset_lines :
    ∀ (L : Finset (ℝ × ℝ × ℝ)), (∀ l ∈ L, l.1 ≠ 0 ∨ l.2.1 ≠ 0) →
      ∀ U : Set UCPlanar.Plane, IsOpen U → U ⊆ (⋃ l ∈ L, lineSet l) → U = ∅ := by
  intro L
  induction L using Finset.induction_on with
  | empty =>
    intro _ U _ hsub
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty] at hsub
    exact Set.subset_empty_iff.mp hsub
  | insert l L' hl ih =>
    intro hL U hU hsub
    have hUopen : IsOpen (U \ lineSet l) := hU.sdiff (isClosed_lineSet l)
    have hsub' : (U \ lineSet l) ⊆ ⋃ l' ∈ L', lineSet l' := by
      rintro x ⟨hxU, hxH⟩
      have hx := hsub hxU
      rw [Finset.set_biUnion_insert] at hx
      rcases hx with hx | hx
      · exact absurd hx hxH
      · exact hx
    have hempty := ih (fun l' hl' => hL l' (Finset.mem_insert_of_mem hl'))
      (U \ lineSet l) hUopen hsub'
    exact eq_empty_of_isOpen_subset_lineSet l (hL l (Finset.mem_insert_self l L')) U hU
      (Set.sdiff_eq_empty.mp hempty)

/-- **An open convex set minus a closed set carried by finitely many lines has finitely many
components.**  The open sign cells of the lines are convex, lie in the difference, and every
component of the difference contains a point off every line, hence meets a cell. -/
theorem finite_components_sdiff_lines (L : Finset (ℝ × ℝ × ℝ))
    (hL : ∀ l ∈ L, l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    {t A : Set UCPlanar.Plane} (htc : Convex ℝ t) (hto : IsOpen t) (hA : IsClosed A)
    (hAL : A ⊆ ⋃ l ∈ L, lineSet l) :
    {C | ∃ q ∈ t \ A, C = connectedComponentIn (t \ A) q}.Finite := by
  classical
  have hSopen : IsOpen (t \ A) := hto.sdiff hA
  refine finite_components_of_family (t \ A)
    (fun σ : {l // l ∈ L} → Bool => t ∩ ⋂ l : {l // l ∈ L}, halfPlane (σ l) (l : ℝ × ℝ × ℝ))
    (fun σ => Convex.isPreconnected (htc.inter (convex_iInter fun l => convex_halfPlane _ _)))
    ?_ ?_
  · intro σ x hx
    refine ⟨hx.1, fun hxA => ?_⟩
    obtain ⟨l, hl, hxl⟩ := Set.mem_iUnion₂.mp (hAL hxA)
    exact halfPlane_subset_compl_lineSet (σ ⟨l, hl⟩) l (Set.mem_iInter.mp hx.2 ⟨l, hl⟩) hxl
  · intro q hq
    have hCopen : IsOpen (connectedComponentIn (t \ A) q) := hSopen.connectedComponentIn
    have hCne : (connectedComponentIn (t \ A) q).Nonempty := ⟨q, mem_connectedComponentIn hq⟩
    have hnotsub : ¬ (connectedComponentIn (t \ A) q ⊆ ⋃ l ∈ L, lineSet l) := fun hsub =>
      (Set.nonempty_iff_ne_empty.mp hCne)
        (eq_empty_of_isOpen_subset_lines L hL _ hCopen hsub)
    obtain ⟨x, hxC, hxnot⟩ := Set.not_subset.mp hnotsub
    have hx : ∀ l : {l // l ∈ L}, ∃ s : Bool, x ∈ halfPlane s (l : ℝ × ℝ × ℝ) := by
      intro l
      refine exists_mem_halfPlane ?_
      intro hcon
      exact hxnot (Set.mem_iUnion₂.mpr ⟨(l : ℝ × ℝ × ℝ), l.2, hcon⟩)
    choose σ hσ using hx
    exact ⟨σ, x, ⟨(connectedComponentIn_subset _ _ hxC).1, Set.mem_iInter.mpr hσ⟩, hxC⟩


theorem exists_line_of_segment (u v : Schoenflies.Plane) :
    ∃ a b c : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧
      ∀ x ∈ segment ℝ u v, a * x 0 + b * x 1 = c := by
  by_cases huv : u = v
  · refine ⟨1, 0, u 0, Or.inl one_ne_zero, ?_⟩
    intro x hx
    rw [← huv, segment_same] at hx
    rw [hx]
    ring
  · refine ⟨v 1 - u 1, u 0 - v 0, (v 1 - u 1) * u 0 + (u 0 - v 0) * u 1, ?_, ?_⟩
    · by_contra hcon
      obtain ⟨h0, h1⟩ := not_or.mp hcon
      apply huv
      have e0 : u 0 = v 0 := by linarith [sub_eq_zero.mp (not_not.mp h1)]
      have e1 : u 1 = v 1 := by linarith [sub_eq_zero.mp (not_not.mp h0)]
      ext i
      fin_cases i
      · exact e0
      · exact e1
    · rintro x ⟨s, t, hs, ht, hst, rfl⟩
      have hx0 : (s • u + t • v) 0 = s * u 0 + t * v 0 := by simp
      have hx1 : (s • u + t • v) 1 = s * u 1 + t * v 1 := by simp
      rw [hx0, hx1]
      linear_combination (u 0 * v 1 - u 1 * v 0) * hst

theorem exists_lines_of_poly : ∀ vs : List Schoenflies.Plane,
    ∃ L : Finset (ℝ × ℝ × ℝ), (∀ l ∈ L, l.1 ≠ 0 ∨ l.2.1 ≠ 0) ∧
      ∀ x ∈ Schoenflies.poly vs, ∃ l ∈ L, l.1 * x 0 + l.2.1 * x 1 = l.2.2 := by
  intro vs
  induction vs with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons u rest ih =>
    rcases rest with _ | ⟨v, rest'⟩
    · refine ⟨{((1 : ℝ), (0 : ℝ), u 0)}, ?_, ?_⟩
      · intro l hl
        rw [Finset.mem_singleton] at hl
        subst hl
        exact Or.inl one_ne_zero
      · intro x hx
        rw [Schoenflies.poly_singleton, Set.mem_singleton_iff] at hx
        refine ⟨((1 : ℝ), (0 : ℝ), u 0), Finset.mem_singleton_self _, ?_⟩
        rw [hx]
        ring
    · obtain ⟨L, hL, hcov⟩ := ih
      obtain ⟨a, b, c, hab, hseg⟩ := exists_line_of_segment u v
      refine ⟨insert (a, b, c) L, ?_, ?_⟩
      · intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hl
        · exact hab
        · exact hL l hl
      · intro x hx
        rw [Schoenflies.poly_cons_cons] at hx
        rcases hx with hx | hx
        · exact ⟨(a, b, c), Finset.mem_insert_self _ _, hseg x hx⟩
        · obtain ⟨l, hlL, hlx⟩ := hcov x hx
          exact ⟨l, Finset.mem_insert_of_mem hlL, hlx⟩

variable {V : Type*} {G : SimpleGraph V}

/-- The homeomorphism to the Euclidean plane does not move coordinates. -/
theorem planeHomeo_apply (p : UCPlanar.Plane) (i : Fin 2) :
    (UCPlanar.Support.planeHomeo p) i = p i := rfl

/-- **The arc of a drawn edge lies on finitely many lines.**  The drawing is polygonal, and a
finite union of segments is carried by finitely many lines. -/
theorem exists_lines_arcOf (E : UCPlanar.PlaneEmbedding G) {e : Sym2 V} (he : e ∈ G.edgeSet) :
    ∃ L : Finset (ℝ × ℝ × ℝ), (∀ l ∈ L, l.1 ≠ 0 ∨ l.2.1 ≠ 0) ∧
      E.arcOf e ⊆ ⋃ l ∈ L, lineSet l := by
  induction e with
  | _ x y =>
    have hxy : G.Adj x y := by simpa using he
    obtain ⟨vs, hvs⟩ := E.edge_polygonal hxy
    obtain ⟨L, hL1, hL2⟩ := exists_lines_of_poly vs
    refine ⟨L, hL1, ?_⟩
    rw [arcOf_eq E hxy]
    rintro p hp
    have hmem : UCPlanar.Support.planeHomeo p ∈ Schoenflies.poly vs := by
      rw [← hvs]
      exact ⟨p, hp, rfl⟩
    obtain ⟨l, hl, hlp⟩ := hL2 _ hmem
    refine Set.mem_iUnion₂.mpr ⟨l, hl, ?_⟩
    rw [lineSet, Set.mem_setOf_eq]
    rw [planeHomeo_apply p 0, planeHomeo_apply p 1] at hlp
    exact hlp

/-- **The drawing of a finite edge set lies on finitely many lines.** -/
theorem exists_lines_edgesTrace (E : UCPlanar.PlaneEmbedding G) {T : Set (Sym2 V)}
    (hfin : T.Finite) (hT : T ⊆ G.edgeSet) :
    ∃ L : Finset (ℝ × ℝ × ℝ), (∀ l ∈ L, l.1 ≠ 0 ∨ l.2.1 ≠ 0) ∧
      E.edgesTrace T ⊆ ⋃ l ∈ L, lineSet l := by
  classical
  have h : ∀ e : Sym2 V, ∃ L : Finset (ℝ × ℝ × ℝ),
      (∀ l ∈ L, l.1 ≠ 0 ∨ l.2.1 ≠ 0) ∧ (e ∈ T → E.arcOf e ⊆ ⋃ l ∈ L, lineSet l) := by
    intro e
    by_cases he : e ∈ T
    · obtain ⟨L, h1, h2⟩ := exists_lines_arcOf E (hT he)
      exact ⟨L, h1, fun _ => h2⟩
    · exact ⟨∅, by simp, fun hc => absurd hc he⟩
  choose F hF1 hF2 using h
  refine ⟨hfin.toFinset.biUnion F, ?_, ?_⟩
  · intro l hl
    obtain ⟨e, _, hle⟩ := Finset.mem_biUnion.mp hl
    exact hF1 e l hle
  · intro p hp
    obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨l, hl, hpl⟩ := Set.mem_iUnion₂.mp (hF2 e he hpe)
    exact Set.mem_iUnion₂.mpr
      ⟨l, Finset.mem_biUnion.mpr ⟨e, hfin.mem_toFinset.mpr he, hl⟩, hpl⟩

/-- **The faces of a periodic plane drawing are locally finite.**  Near a point the drawing is
the drawing of finitely many edges, whose arcs lie on finitely many lines, so the ball minus the
drawing has finitely many components and therefore meets finitely many faces. -/
theorem locallyFiniteFaces (Q : UCPlanar.PeriodicPlaneGraph V) :
    Q.embedding.LocallyFiniteFaces := by
  classical
  refine locallyFiniteFaces_of_components Q ?_
  intro p
  obtain ⟨T, hTfin, hTsub, hTcov⟩ := exists_finite_trace_near Q p 1
  refine ⟨Metric.ball p 1, Metric.ball_mem_nhds p one_pos, ?_⟩
  have hEq : Metric.ball p 1 \ Q.embedding.trace
      = Metric.ball p 1 \ Q.embedding.edgesTrace T := by
    ext z
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hz, hzt⟩
      refine ⟨hz, fun hc => hzt ?_⟩
      rw [trace_eq_edgesTrace Q]
      exact edgesTrace_mono Q.embedding hTsub hc
    · rintro ⟨hz, hze⟩
      exact ⟨hz, fun hc => hze (hTcov z (Metric.ball_subset_closedBall hz) hc)⟩
  rw [hEq]
  obtain ⟨L, hL1, hL2⟩ := exists_lines_edgesTrace Q.embedding hTfin hTsub
  exact finite_components_sdiff_lines L hL1 (convex_ball p 1) Metric.isOpen_ball
    (isCompact_edgesTrace Q.embedding hTfin hTsub).isClosed hL2


/-- **Each open half plane of a line has the line in its closure.**  Moving off a point of the
line in the direction of the coefficient vector enters one half plane and moving the other way
enters the other, and both moves are arbitrarily small.  This is the first ingredient of the
two-sidedness of a drawn edge. -/
theorem lineSet_subset_closure_halfPlane (l : ℝ × ℝ × ℝ) (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    (s : Bool) :
    lineSet l ⊆ closure (halfPlane s l) := by
  intro x hx
  rw [lineSet, Set.mem_setOf_eq] at hx
  have hpos : 0 < l.1 * l.1 + l.2.1 * l.2.1 := by
    rcases hl with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg l.2.1]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg l.1]
  set v : UCPlanar.Plane := ![l.1, l.2.1] with hv
  have hnorm : 0 < ‖v‖ + 1 := by positivity
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := ε / (2 * (‖v‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hlt : δ * ‖v‖ < ε := by
    have h1 : δ * ‖v‖ ≤ δ * (‖v‖ + 1) := by nlinarith [norm_nonneg v]
    have h2 : δ * (2 * (‖v‖ + 1)) = ε := by
      rw [hδ]; field_simp
    nlinarith [hδpos, hnorm]
  set t : ℝ := if s then δ else -δ with ht
  have habs : |t| = δ := by
    rw [ht]
    by_cases hs : s
    · rw [if_pos hs, abs_of_pos hδpos]
    · rw [if_neg hs, abs_neg, abs_of_pos hδpos]
  refine ⟨x + t • v, ?_, ?_⟩
  · have h0 : (x + t • v) 0 = x 0 + t * l.1 := by simp [hv]
    have h1 : (x + t • v) 1 = x 1 + t * l.2.1 := by simp [hv]
    unfold halfPlane
    split
    · rename_i hs
      have hts : t = δ := by rw [ht, if_pos hs]
      show l.2.2 < l.1 * (x + t • v) 0 + l.2.1 * (x + t • v) 1
      rw [h0, h1, hts]
      nlinarith [hx, hpos, hδpos]
    · rename_i hs
      have hts : t = -δ := by rw [ht, if_neg hs]
      show l.1 * (x + t • v) 0 + l.2.1 * (x + t • v) 1 < l.2.2
      rw [h0, h1, hts]
      nlinarith [hx, hpos, hδpos]
  · rw [dist_eq_norm]
    have : x - (x + t • v) = -(t • v) := by abel
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, habs]
    exact hlt

/-- **A line that bounds a set from one side and misses it lies on its frontier.**  This is the
two-sidedness of a drawn edge in the form the boundary edge set of Step 3 needs: once one of the
two sides of a line belongs to a region the line avoids, the whole line is frontier. -/
theorem lineSet_subset_frontier_of_halfPlane_subset (l : ℝ × ℝ × ℝ) (hl : l.1 ≠ 0 ∨ l.2.1 ≠ 0)
    (s : Bool) {S : Set UCPlanar.Plane} (hsub : halfPlane s l ⊆ S)
    (hdisj : ∀ x ∈ lineSet l, x ∉ S) : lineSet l ⊆ frontier S := by
  intro x hx
  rw [frontier_eq_closure_inter_closure]
  exact ⟨closure_mono hsub (lineSet_subset_closure_halfPlane l hl s hx),
    subset_closure (show x ∈ Sᶜ from hdisj x hx)⟩

end UCPlanar.Support
