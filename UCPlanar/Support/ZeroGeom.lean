/- Periodic plane geometry: drawn edges are short, cycles enclose only a bounded region,
and the graph metric is controlled by the geometric one. -/
import UCPlanar.Support.ZeroLower
import UCPlanar.Support.PlanarTrace
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support


/-- The drawn arc of one edge stays within a bounded distance of its source vertex. -/
theorem arc_bounded_single {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G)
    (x y : V) (h : G.Adj x y) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p ∈ Set.range (E.edge h), ‖p - E.pos x‖ ≤ D := by
  classical
  have hcomp : IsCompact (Set.range (E.edge h)) := isCompact_range (E.edge h).continuous_toFun
  obtain ⟨C, hC⟩ := hcomp.isBounded.subset_closedBall (E.pos x)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  have hd := hC hp
  rw [Metric.mem_closedBall, dist_eq_norm] at hd
  exact hd.trans (le_max_left _ _)

/-- **Drawn edges are geometrically short.**  Finitely many edge orbits bound the whole drawn
arc, not merely the displacement between its endpoints. -/
theorem exists_arc_bound {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (x y : V) (h : P.graph.Adj x y),
      ∀ p ∈ Set.range (P.embedding.edge h), ‖p - P.embedding.pos x‖ ≤ D := by
  classical
  set A : Finset (V × V) :=
    P.representatives.biUnion (fun v => (P.graph.neighborFinset v).image (fun w => (v, w))) with hA
  have key : ∀ q : V × V, ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : P.graph.Adj q.1 q.2),
      ∀ p ∈ Set.range (P.embedding.edge h), ‖p - P.embedding.pos q.1‖ ≤ D := by
    intro q
    by_cases hq : P.graph.Adj q.1 q.2
    · obtain ⟨D, hD0, hD⟩ := arc_bounded_single P.embedding q.1 q.2 hq
      exact ⟨D, hD0, fun _ p hp => hD p hp⟩
    · exact ⟨0, le_rfl, fun h => absurd h hq⟩
  choose b hb0 hb using key
  refine ⟨∑ q ∈ A, b q, Finset.sum_nonneg (fun q _ => hb0 q), ?_⟩
  intro x y h p hp
  obtain ⟨v, hv, a, hav⟩ := P.covers x
  obtain ⟨w, hyw⟩ : ∃ w, P.shift a w = y :=
    ⟨P.shift (-a) y, by rw [← P.shift_add, add_neg_cancel, P.shift_zero]⟩
  subst hav
  subst hyw
  have hvw : P.graph.Adj v w := (P.shift_adj a v w).mp h
  have hmem : (v, w) ∈ A := by
    rw [hA]
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr
      ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr hvw, rfl⟩⟩
  have hrange : Set.range (P.embedding.edge h)
      = (fun p => p + P.period (fun i => (a i : ℝ))) '' Set.range (P.embedding.edge hvw) :=
    P.edge_shift a v w hvw
  rw [hrange] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hposshift : P.embedding.pos (P.shift a v)
      = P.embedding.pos v + P.period (fun i => (a i : ℝ)) := by
    rw [P.embedding_pos]; exact P.pos_shift a v
  have hsimp : q + P.period (fun i => (a i : ℝ)) - P.embedding.pos (P.shift a v)
      = q - P.embedding.pos v := by
    rw [hposshift]; abel
  rw [hsimp]
  exact le_trans (hb (v, w) hvw q hq)
    (Finset.single_le_sum (f := fun q : V × V => b q) (fun q _ => hb0 q) hmem)


/-- **Every point of the drawing of a walk is close to the drawn start**, within the length of
the walk times the arc bound. -/
theorem norm_sub_le_of_mem_walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ (u v : V) (h : G.Adj u v), ∀ p ∈ Set.range (E.edge h), ‖p - E.pos u‖ ≤ D)
    {x y : V} (w : G.Walk x y) :
    ∀ p ∈ E.walkTrace w, ‖p - E.pos x‖ ≤ D * (w.length + 1) := by
  induction w with
  | @nil u =>
      intro p hp
      have hp' : p = E.pos u := by simpa [UCPlanar.PlaneEmbedding.walkTrace] using hp
      subst hp'
      simp only [sub_self, norm_zero, SimpleGraph.Walk.length_nil, Nat.cast_zero, zero_add,
        mul_one]
      exact hD0
  | @cons u v z h q ih =>
      intro p hp
      have hqr : E.pos v ∈ Set.range (E.edge h) := ⟨1, (E.edge h).target⟩
      have hvu : ‖E.pos v - E.pos u‖ ≤ D := hD u v h _ hqr
      have hlen : (0:ℝ) ≤ (q.length : ℝ) := Nat.cast_nonneg _
      rcases hp with hp | hp
      · have := hD u v h p hp
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith
      · have h1 := ih p hp
        have h2 : ‖p - E.pos u‖ ≤ ‖p - E.pos v‖ + ‖E.pos v - E.pos u‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub p (E.pos v) (E.pos u)
          simpa using this
        simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith [h1, h2, hvu, hlen]


/-- A set containing a whole ray is unbounded. -/
theorem not_isBounded_of_ray (S : Set UCPlanar.Plane) (z v : UCPlanar.Plane) (hv : v ≠ 0)
    (hS : ∀ t : ℝ, 0 ≤ t → z + t • v ∈ S) : ¬ Bornology.IsBounded S := by
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set t : ℝ := (C + ‖z‖ + 1) / ‖v‖ with ht
  have ht0 : 0 ≤ t := by
    have : 0 ≤ C := le_trans (norm_nonneg _) (hC _ (hS 0 le_rfl))
    positivity
  have hmem := hS t ht0
  have hnorm : ‖z + t • v‖ ≤ C := hC _ hmem
  have h1 : ‖t • v‖ = t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
  have h2 : t * ‖v‖ = C + ‖z‖ + 1 := by
    rw [ht, div_mul_cancel₀]
    exact ne_of_gt hvpos
  have h3 : ‖t • v‖ ≤ ‖z + t • v‖ + ‖z‖ := by
    have := norm_sub_le (z + t • v) z
    simpa using this
  linarith [h1, h2, h3, hnorm]

/-- **A point far from a set inside a ball lies in an unbounded complementary component.**
A closed ball is convex, so a point outside it is cut off by a half plane, which is convex,
unbounded and disjoint from the set. -/
theorem not_isBounded_component_of_far (C : Set UCPlanar.Plane) (c₀ : UCPlanar.Plane) (R : ℝ)
    (hR : 0 ≤ R) (hC : C ⊆ Metric.closedBall c₀ R) (z : UCPlanar.Plane) (hz : R < ‖z - c₀‖) :
    ¬ Bornology.IsBounded (connectedComponentIn Cᶜ z) := by
  have hz' : z ∉ Metric.closedBall c₀ R := by
    simp only [Metric.mem_closedBall, dist_eq_norm]
    linarith
  obtain ⟨f, u, hfz, hfb⟩ :=
    geometric_hahn_banach_point_closed (convex_closedBall c₀ R) Metric.isClosed_closedBall hz'
  set H : Set UCPlanar.Plane := {w | f w < u} with hH
  have hzH : z ∈ H := hfz
  have hHC : H ⊆ Cᶜ := by
    intro w hw hwC
    exact absurd (hfb w (hC hwC)) (not_lt.mpr (le_of_lt hw))
  have hconv : Convex ℝ H := convex_halfSpace_lt (f.toLinearMap.isLinear) u
  have hsub : H ⊆ connectedComponentIn Cᶜ z :=
    hconv.isPreconnected.subset_connectedComponentIn hzH hHC
  have hc0 : c₀ ∈ Metric.closedBall c₀ R := Metric.mem_closedBall_self hR
  have hfc : u < f c₀ := hfb c₀ hc0
  have hfv : 0 < f (c₀ - z) := by
    rw [map_sub]; linarith
  have hvne : (c₀ - z) ≠ 0 := by
    intro h
    rw [h] at hfv
    simp at hfv
  have hray : ∀ t : ℝ, 0 ≤ t → z + t • (-(c₀ - z)) ∈ H := by
    intro t ht
    simp only [hH, Set.mem_setOf_eq, map_add, map_smul, map_neg, smul_eq_mul]
    nlinarith [hfz, hfv, ht]
  intro hb
  exact not_isBounded_of_ray H z (-(c₀ - z)) (neg_ne_zero.mpr hvne) hray (hb.subset hsub)


/-- **The graph metric is bounded by the geometric one.**  Finitely many vertex orbits and a
bounded translation step turn a small geometric displacement into a short walk. -/
theorem exists_dist_le_norm {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : V, (P.graph.dist x y : ℝ) ≤ K * ‖P.pos x - P.pos y‖ + K := by
  classical
  obtain ⟨K₀, hK₀0, hK₀⟩ := exists_step_bound P
  obtain ⟨Kl, hKl0, hKl⟩ := exists_lattice_count P.period
  set A : Finset (V × V) := P.representatives ×ˢ P.representatives with hA
  set C₁ : ℝ := ∑ q ∈ A, ‖P.pos q.1 - P.pos q.2‖ with hC₁def
  set C₂ : ℝ := ∑ q ∈ A, (P.graph.dist q.1 q.2 : ℝ) with hC₂def
  have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun q _ => Nat.cast_nonneg _
  have hC₁ : ∀ v ∈ P.representatives, ∀ w ∈ P.representatives,
      ‖P.pos v - P.pos w‖ ≤ C₁ := by
    intro v hv w hw
    have hmem : (v, w) ∈ A := by rw [hA]; exact Finset.mem_product.mpr ⟨hv, hw⟩
    exact Finset.single_le_sum (f := fun q : V × V => ‖P.pos q.1 - P.pos q.2‖)
      (fun q _ => norm_nonneg _) hmem
  have hC₂ : ∀ v ∈ P.representatives, ∀ w ∈ P.representatives,
      (P.graph.dist v w : ℝ) ≤ C₂ := by
    intro v hv w hw
    have hmem : (v, w) ∈ A := by rw [hA]; exact Finset.mem_product.mpr ⟨hv, hw⟩
    exact Finset.single_le_sum (f := fun q : V × V => (P.graph.dist q.1 q.2 : ℝ))
      (fun q _ => Nat.cast_nonneg _) hmem
  have hK₀R : (0:ℝ) < (K₀ : ℝ) := by exact_mod_cast hK₀0
  refine ⟨2*(K₀:ℝ)*Kl + C₂ + 2*(K₀:ℝ)*Kl*C₁ + 1, by positivity, ?_⟩
  intro x y
  obtain ⟨v, hv, b, hbv⟩ := P.covers x
  obtain ⟨w, hw, a, haw⟩ := P.covers y
  set M : ℝ := ‖P.pos x - P.pos y‖ + C₁ with hM
  have hM0 : 0 ≤ M := by positivity
  have hper : P.period (fun j => (((a - b) j : ℤ) : ℝ))
      = (P.pos y - P.pos x) + (P.pos v - P.pos w) := by
    rw [period_sub P a b, ← hbv, ← haw, P.pos_shift, P.pos_shift]
    abel
  have hperM : ‖P.period (fun j => (((a - b) j : ℤ) : ℝ))‖ ≤ M := by
    rw [hper, hM]
    have h1 : ‖(P.pos y - P.pos x) + (P.pos v - P.pos w)‖
        ≤ ‖P.pos y - P.pos x‖ + ‖P.pos v - P.pos w‖ := norm_add_le _ _
    have h2 : ‖P.pos y - P.pos x‖ = ‖P.pos x - P.pos y‖ := norm_sub_rev _ _
    have h3 := hC₁ v hv w hw
    linarith
  have hcoord : ∀ j, |(((a - b) j : ℤ) : ℝ)| ≤ Kl * M := hKl (a - b) M hperM
  have hnat : (((((a - b) 0).natAbs + ((a - b) 1).natAbs : ℕ)) : ℝ) ≤ 2 * (Kl * M) := by
    have h0 := hcoord 0
    have h1 := hcoord 1
    have e0 : ((((a - b) 0).natAbs : ℕ) : ℝ) = |(((a - b) 0 : ℤ) : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have e1 : ((((a - b) 1).natAbs : ℕ) : ℝ) = |(((a - b) 1 : ℤ) : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    push_cast
    rw [e0, e1] at *
    linarith
  have hshift : P.shift (a - b) (P.shift b w) = y := by
    rw [← P.shift_add, sub_add_cancel, haw]
  have hd1 : P.graph.dist x (P.shift b w) ≤ P.graph.dist v w := by
    rw [← hbv]
    exact dist_shift_le_dist P b v w
  have hd2 : P.graph.dist (P.shift b w) y ≤ K₀ * (((a - b) 0).natAbs + ((a - b) 1).natAbs) := by
    have := dist_shift_le_sum P K₀ hK₀ (P.shift b w) (a - b)
    rwa [hshift] at this
  have htri := P.connected.dist_triangle (u := x) (v := P.shift b w) (w := y)
  have hsum : P.graph.dist x y
      ≤ P.graph.dist v w + K₀ * (((a - b) 0).natAbs + ((a - b) 1).natAbs) := by omega
  have hsumR : (P.graph.dist x y : ℝ)
      ≤ (P.graph.dist v w : ℝ)
        + (K₀ : ℝ) * ((((a - b) 0).natAbs + ((a - b) 1).natAbs : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hvw := hC₂ v hv w hw
  have hstep : (K₀ : ℝ) * ((((a - b) 0).natAbs + ((a - b) 1).natAbs : ℕ) : ℝ)
      ≤ (K₀ : ℝ) * (2 * (Kl * M)) := by
    exact mul_le_mul_of_nonneg_left hnat (le_of_lt hK₀R)
  have hnorm0 : (0:ℝ) ≤ ‖P.pos x - P.pos y‖ := norm_nonneg _
  have key : (P.graph.dist x y : ℝ) ≤ C₂ + (K₀ : ℝ) * (2 * (Kl * M)) := by
    linarith [hsumR, hvw, hstep]
  have expand : (K₀ : ℝ) * (2 * (Kl * M))
      = 2*(K₀:ℝ)*Kl*‖P.pos x - P.pos y‖ + 2*(K₀:ℝ)*Kl*C₁ := by rw [hM]; ring
  have hKge : 2*(K₀:ℝ)*Kl ≤ 2*(K₀:ℝ)*Kl + C₂ + 2*(K₀:ℝ)*Kl*C₁ + 1 := by
    have : (0:ℝ) ≤ 2*(K₀:ℝ)*Kl*C₁ := by positivity
    linarith
  have h5 : 2*(K₀:ℝ)*Kl*‖P.pos x - P.pos y‖
      ≤ (2*(K₀:ℝ)*Kl + C₂ + 2*(K₀:ℝ)*Kl*C₁ + 1) * ‖P.pos x - P.pos y‖ :=
    mul_le_mul_of_nonneg_right hKge hnorm0
  have h6 : (0:ℝ) ≤ 2*(K₀:ℝ)*Kl := by positivity
  linarith [key, expand.le, expand.ge, h5, h6]

/-- **The region enclosed by a drawn cycle has diameter linear in the length of the cycle.**
Every point of the drawing is within `D` times the length of the drawn base vertex, a point
further away than that lies in an unbounded complementary component, and the graph metric is
controlled by the geometric one. -/
theorem cycleRegion_dist_le {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (o : V) (γ : P.graph.Walk o o) (x z : V),
      x ∈ P.embedding.cycleRegion γ → z ∈ P.embedding.cycleRegion γ →
      (P.graph.dist x z : ℝ) ≤ C * (γ.length + 1) := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_arc_bound P
  obtain ⟨K, hK0, hK⟩ := exists_dist_le_norm P.toPeriodicGraph
  refine ⟨2*K*D + K, by positivity, ?_⟩
  intro o γ x z hx hz
  set R : ℝ := D * (γ.length + 1) with hR
  have hR0 : 0 ≤ R := by positivity
  have htrace : P.embedding.walkTrace γ ⊆ Metric.closedBall (P.embedding.pos o) R := by
    intro p hp
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact norm_sub_le_of_mem_walkTrace P.embedding D hD0 hD γ p hp
  have key : ∀ y ∈ P.embedding.cycleRegion γ, ‖P.embedding.pos y - P.embedding.pos o‖ ≤ R := by
    intro y hy
    rcases hy with hy | ⟨hy1, hy2⟩
    · have : P.embedding.pos y ∈ P.embedding.walkTrace γ :=
        (P.embedding.pos_mem_walkTrace_iff γ y).mpr hy
      have := htrace this
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    · by_contra hcon
      exact not_isBounded_component_of_far (P.embedding.walkTrace γ) (P.embedding.pos o) R hR0
        htrace (P.embedding.pos y) (lt_of_not_ge hcon) hy2
  have hxz : ‖P.pos x - P.pos z‖ ≤ 2 * R := by
    have h1 := key x hx
    have h2 := key z hz
    have h3 : ‖P.embedding.pos x - P.embedding.pos z‖
        ≤ ‖P.embedding.pos x - P.embedding.pos o‖ + ‖P.embedding.pos z - P.embedding.pos o‖ := by
      have := norm_sub_le (P.embedding.pos x - P.embedding.pos o)
        (P.embedding.pos z - P.embedding.pos o)
      simpa using this
    rw [← P.embedding_pos]
    linarith
  have hdist := hK x z
  have hmul : K * ‖P.pos x - P.pos z‖ ≤ K * (2 * R) := mul_le_mul_of_nonneg_left hxz hK0.le
  have hone : (1:ℝ) ≤ (γ.length : ℝ) + 1 := by
    have : (0:ℝ) ≤ (γ.length : ℝ) := Nat.cast_nonneg _
    linarith
  have hKle : K ≤ K * ((γ.length : ℝ) + 1) := by nlinarith
  have hexp : K * (2 * R) = 2*K*D*((γ.length : ℝ) + 1) := by rw [hR]; ring
  nlinarith [hdist, hmul, hKle, hexp.le, hexp.ge]

/-- A cycle visits at least as many distinct vertices as its length. -/
theorem length_le_card_support {V : Type*} {G : SimpleGraph V} {o : V} (γ : G.Walk o o)
    (hγ : γ.IsCycle) : γ.length ≤ γ.support.toFinset.card := by
  classical
  have hnodup : γ.support.tail.Nodup := hγ.support_nodup
  have hsub : γ.support.tail.toFinset ⊆ γ.support.toFinset := by
    intro w hw
    simp only [List.mem_toFinset] at hw ⊢
    exact List.mem_of_mem_tail hw
  have h1 : γ.support.tail.toFinset.card = γ.support.tail.length :=
    List.toFinset_card_of_nodup hnodup
  have h2 : γ.support.tail.length = γ.length := by
    rw [List.length_tail, γ.length_support]
    omega
  have h3 := Finset.card_le_card hsub
  omega

/-- **A periodic graph has bounded degree**, because the translations act transitively on the
finitely many vertex orbits. -/
theorem exists_degree_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ d : ℕ, ∀ x, P.graph.degree x ≤ d := by
  classical
  refine ⟨∑ v ∈ P.representatives, P.graph.degree v, ?_⟩
  intro x
  obtain ⟨v, hv, a, hav⟩ := P.covers x
  have hx : P.shift (-a) x = v := by
    rw [← hav, ← P.shift_add, neg_add_cancel, P.shift_zero]
  have hsub : P.graph.neighborFinset x ⊆ (P.graph.neighborFinset v).image (P.shift a) := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    refine Finset.mem_image.mpr ⟨P.shift (-a) y, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset, ← hx]
      exact (P.shift_adj (-a) x y).mpr hy
    · rw [← P.shift_add, add_neg_cancel, P.shift_zero]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le (s := P.graph.neighborFinset v) (f := P.shift a)
  have hmem : P.graph.degree v ≤ ∑ w ∈ P.representatives, P.graph.degree w :=
    Finset.single_le_sum (f := fun w : V => P.graph.degree w) (fun w _ => Nat.zero_le _) hv
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at h1 h2
  omega

end UCPlanar.Support
