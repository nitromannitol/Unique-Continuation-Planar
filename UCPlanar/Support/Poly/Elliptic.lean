/-
Uniform ellipticity, bounded degree and bounded translation walks on a periodic network.
These are the geometric facts behind the discrete Caccioppoli inequality for a difference
along a lattice vector: the vector is crossed by a walk of bounded length, and the
conductance seen along that walk is bounded above and below.
-/
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.Poly.Difference
import Mathlib

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- A lattice translation is injective on vertices. -/
theorem shift_injective {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (a : LatticeProb.Site 2) : Function.Injective (P.shift a) := by
  intro x y hxy
  have h := congrArg (P.shift (-a)) hxy
  rwa [← P.shift_add, ← P.shift_add, neg_add_cancel, P.shift_zero, P.shift_zero] at h

/-- Distinct lattice vectors translate a vertex to distinct vertices. -/
theorem shift_site_injective {V : Type*} (P : UCPlanar.PeriodicGraph V) (z : V) :
    Function.Injective (fun b : LatticeProb.Site 2 => P.shift b z) := by
  intro a b hab
  have h1 : P.pos (P.shift a z) = P.pos (P.shift b z) := congrArg P.pos hab
  rw [P.pos_shift, P.pos_shift] at h1
  have h2 : P.period (fun i => (a i : ℝ)) = P.period (fun i => (b i : ℝ)) :=
    add_left_cancel h1
  have h3 : (fun i => (a i : ℝ)) = (fun i => (b i : ℝ)) := P.period.injective h2
  funext i
  have := congrFun h3 i
  exact_mod_cast this

/-- **The degree is uniformly bounded.**  Finitely many vertex orbits and local finiteness. -/
theorem exists_neighbor_card_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ Δ : ℕ, ∀ x : V, (P.graph.neighborFinset x).card ≤ Δ := by
  classical
  refine ⟨∑ v ∈ P.representatives, (P.graph.neighborFinset v).card, ?_⟩
  intro x
  obtain ⟨v, hv, a, hav⟩ := P.covers x
  have hcard : (P.graph.neighborFinset x).card = (P.graph.neighborFinset v).card := by
    subst hav
    refine Finset.card_bij (fun y _ => P.shift (-a) y) ?_ ?_ ?_
    · intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy ⊢
      have h := (P.shift_adj (-a) (P.shift a v) y).mpr hy
      rwa [← P.shift_add, neg_add_cancel, P.shift_zero] at h
    · intro y₁ _ y₂ _ h
      exact shift_injective P (-a) h
    · intro y hy
      refine ⟨P.shift a y, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset] at hy ⊢
        exact (P.shift_adj a v y).mpr hy
      · rw [← P.shift_add, neg_add_cancel, P.shift_zero]
  rw [hcard]
  exact Finset.single_le_sum (f := fun v : V => (P.graph.neighborFinset v).card)
    (fun v _ => Nat.zero_le _) hv

/-- **A vertex is joined to its lattice translate by a walk of bounded length.**  The graph is
connected and there are finitely many orbits, so one walk per representative suffices. -/
theorem exists_shift_walk_length {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (a : LatticeProb.Site 2) :
    ∃ L : ℕ, ∀ v ∈ P.representatives, ∃ p : P.graph.Walk v (P.shift a v), p.length ≤ L := by
  classical
  refine ⟨∑ v ∈ P.representatives, (P.connected.preconnected v (P.shift a v)).some.length, ?_⟩
  intro v hv
  refine ⟨(P.connected.preconnected v (P.shift a v)).some, ?_⟩
  exact Finset.single_le_sum
    (f := fun v : V => (P.connected.preconnected v (P.shift a v)).some.length)
    (fun v _ => Nat.zero_le _) hv

/-- **Uniform ellipticity.**  A periodic conductance is bounded above and below on the edges,
because there are finitely many edge orbits and the conductance is positive on each. -/
theorem exists_cond_bounds {V : Type*} (P : UCPlanar.PeriodicGraph V) {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c) :
    ∃ κ K : ℝ, 0 < κ ∧ 0 < K ∧ ∀ x y, P.graph.Adj x y → κ ≤ c x y ∧ c x y ≤ K := by
  classical
  set A : Finset (V × V) :=
    P.representatives.biUnion (fun v => (P.graph.neighborFinset v).image (fun w => (v, w))) with hA
  have hadj : ∀ q ∈ A, P.graph.Adj q.1 q.2 := by
    intro q hq
    rw [hA, Finset.mem_biUnion] at hq
    obtain ⟨v, _, hq⟩ := hq
    rw [Finset.mem_image] at hq
    obtain ⟨w, hw, rfl⟩ := hq
    exact (SimpleGraph.mem_neighborFinset _ _ _).mp hw
  refine ⟨∏ q ∈ A, min 1 (c q.1 q.2), 1 + ∑ q ∈ A, c q.1 q.2, ?_, ?_, ?_⟩
  · refine Finset.prod_pos ?_
    intro q hq
    exact lt_min one_pos (hc.pos (hadj q hq))
  · have : (0:ℝ) ≤ ∑ q ∈ A, c q.1 q.2 :=
      Finset.sum_nonneg (fun q _ => hc.nonneg _ _)
    linarith
  · intro x y hxy
    obtain ⟨v, hv, a, hav⟩ := P.covers x
    set w : V := P.shift (-a) y with hw
    have hyw : P.shift a w = y := by
      rw [hw, ← P.shift_add, add_neg_cancel, P.shift_zero]
    have hvw : P.graph.Adj v w := by
      rw [← P.shift_adj a v w, hav, hyw]; exact hxy
    have hmem : (v, w) ∈ A := by
      rw [hA]
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr
        ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr hvw, rfl⟩⟩
    have hcvw : c x y = c v w := by rw [← hav, ← hyw]; exact hp a v w
    rw [hcvw]
    constructor
    · have hsplit : ∏ q ∈ A, min 1 (c q.1 q.2)
          = min 1 (c v w) * ∏ q ∈ A.erase (v, w), min 1 (c q.1 q.2) :=
        (Finset.mul_prod_erase A (fun q => min 1 (c q.1 q.2)) hmem).symm
      have hrest : ∏ q ∈ A.erase (v, w), min 1 (c q.1 q.2) ≤ 1 :=
        Finset.prod_le_one (fun q _ => le_min zero_le_one (hc.nonneg _ _))
          (fun q _ => min_le_left _ _)
      have hpos : (0:ℝ) < min 1 (c v w) := lt_min one_pos (hc.pos hvw)
      have h2 : min 1 (c v w) * ∏ q ∈ A.erase (v, w), min 1 (c q.1 q.2)
          ≤ min 1 (c v w) * 1 := mul_le_mul_of_nonneg_left hrest hpos.le
      have h3 : min 1 (c v w) ≤ c v w := min_le_right _ _
      rw [hsplit]
      linarith
    · have := Finset.single_le_sum (f := fun q : V × V => c q.1 q.2)
        (fun q _ => hc.nonneg _ _) hmem
      linarith

/-- **A walk moves the drawing by at most its length times the edge bound**, at every step. -/
theorem norm_pos_getVert_sub {V : Type*} (P : UCPlanar.PeriodicGraph V) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x y, P.graph.Adj x y → ‖P.pos x - P.pos y‖ ≤ D) {u v : V}
    (p : P.graph.Walk u v) (i : ℕ) :
    ‖P.pos u - P.pos (p.getVert i)‖ ≤ D * p.length := by
  have h1 := UCPlanar.Support.norm_pos_sub_le_walk P D hD (p.take i)
  have h2 : ((p.take i).length : ℝ) ≤ (p.length : ℝ) := by
    have h : (p.take i).length ≤ p.length := by
      rw [SimpleGraph.Walk.take_length]; exact min_le_right _ _
    exact_mod_cast h
  calc ‖P.pos u - P.pos (p.getVert i)‖ ≤ D * ((p.take i).length : ℝ) := h1
    _ ≤ D * (p.length : ℝ) := by nlinarith

/-- Cauchy-Schwarz along a chain: a telescoped difference of `L` steps is at most `L` times
the sum of the squared steps. -/
theorem sq_sub_le_range_sum (g : ℕ → ℝ) (L : ℕ) :
    (g L - g 0) ^ 2 ≤ (L : ℝ) * ∑ i ∈ Finset.range L, (g (i+1) - g i) ^ 2 := by
  classical
  have htel : ∑ i ∈ Finset.range L, (g (i+1) - g i) = g L - g 0 :=
    Finset.sum_range_sub g L
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range L) (f := fun i => g (i+1) - g i)
  rw [htel, Finset.card_range] at hcs
  exact hcs

end UCPlanar.Support
