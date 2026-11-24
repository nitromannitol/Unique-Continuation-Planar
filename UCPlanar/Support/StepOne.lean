/- Step 1 of the proof of the zero case: harmonic functions across a cut of one or two edges,
and the network in which the finite side of a two-edge cut is replaced by a single edge. -/
import UCPlanar.Support.LiouKilled
import UCPlanar.Support.ZeroMax
import LatticeProb.Network.MaximumPrinciple
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

open LatticeProb.Network

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### Currents into a finite set -/

/-- The current entering the finite set `K` from the vertex `x` under the voltage `f`: the sum
of `c(x,y) (f y - f x)` over `y ∈ K`. When `c` is a conductance of the graph only the edges from
`x` into `K` contribute. -/
noncomputable def inflow (c : V → V → ℝ) (K : Finset V) (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ K, c x y * (f y - f x)

/-- The Laplacian at `x` is the sum over any finite set that contains the neighbours of `x`,
for a weight vanishing off the edges at `x`. -/
theorem netLaplacian_eq_sum_of_subset {c : V → V → ℝ} {x : V} (hc0 : ∀ y, ¬ G.Adj x y → c x y = 0)
    (f : V → ℝ) {T : Finset V} (hT : G.neighborFinset x ⊆ T) :
    netLaplacian G c f x = ∑ y ∈ T, c x y * (f y - f x) := by
  rw [netLaplacian]
  refine Finset.sum_subset hT fun y _ hy => ?_
  rw [hc0 y (fun h => hy ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)), zero_mul]

/-- The Laplacian at `x` depends only on the values at `x` and at its neighbours. -/
theorem netLaplacian_congr_local {c : V → V → ℝ} {f g : V → ℝ} {x : V} (hx : f x = g x)
    (hnb : ∀ y, G.Adj x y → f y = g y) : netLaplacian G c f x = netLaplacian G c g x := by
  rw [netLaplacian, netLaplacian]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [hx, hnb y ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)]

/-- **The maximum principle on a finite set, through its outer neighbours.** Two functions
harmonic on a finite set `K` of a connected graph which agree at every vertex outside `K`
adjacent to `K` agree on `K`. -/
theorem eqOn_of_harmonicOn_of_boundary (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (K : Finset V) {q : V} (hq : q ∉ K) {f g : V → ℝ}
    (hf : ∀ x ∈ K, netLaplacian G c f x = 0) (hg : ∀ x ∈ K, netLaplacian G c g x = 0)
    (hb : ∀ x ∈ K, ∀ y, G.Adj x y → y ∉ K → f y = g y) : ∀ x ∈ K, f x = g x := by
  set h : V → ℝ := fun v => if v ∈ K then f v - g v else 0 with hh
  have hlap : ∀ x ∈ K, netLaplacian G c h x = 0 := by
    intro x hx
    have hcongr : netLaplacian G c h x = netLaplacian G c (f - g) x := by
      refine netLaplacian_congr_local (by simp [hh, hx]) fun y hxy => ?_
      by_cases hy : y ∈ K
      · simp [hh, hy]
      · simp [hh, hy, hb x hx y hxy hy]
    rw [hcongr, netLaplacian_sub, hf x hx, hg x hx, sub_self]
  have hle := le_of_harmonicOn hG hc K ∅ h 0 hq (fun x hx _ => hlap x hx)
    (fun x hx => by simp [hh, hx]) (fun x hx => absurd hx (Set.notMem_empty x))
  have hge := le_of_harmonicOn hG hc K ∅ (fun v => -h v) 0 hq
    (fun x hx _ => by rw [netLaplacian_neg, hlap x hx, neg_zero])
    (fun x hx => by simp [hh, hx]) (fun x hx => absurd hx (Set.notMem_empty x))
  intro x hx
  have h1 := hle x
  have h2 := hge x
  simp only [hh, if_pos hx] at h1 h2
  linarith

/-! ### A finite piece attached at one vertex -/

/-- **A harmonic function is constant on a finite piece attached at one vertex.** If every edge
leaving the finite set `K` ends at the vertex `t`, as for the finite side of a bridge, a function
harmonic on `K` is equal on `K` to its value at `t`. -/
theorem eq_of_harmonicOn_of_cutVertex (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (K : Finset V) {t : V} (ht : t ∉ K) (hcut : ∀ x ∈ K, ∀ y, G.Adj x y → y ∉ K → y = t)
    {f : V → ℝ} (hf : ∀ x ∈ K, netLaplacian G c f x = 0) : ∀ x ∈ K, f x = f t :=
  eqOn_of_harmonicOn_of_boundary hG hc K ht hf (fun x _ => netLaplacian_const c (f t) x)
    (fun x hx y hxy hy => by rw [hcut x hx y hxy hy])

/-! ### The effective conductance of a finite piece with two exits -/

/-- **The Dirichlet problem on a finite set with arbitrary boundary values.** On a connected
infinite graph, for every finite `K` and every `b`, some function harmonic on `K` agrees with `b`
off `K`. -/
theorem exists_harmonicOn_eq_off (hG : G.Connected) [Infinite V] {c : V → V → ℝ}
    (hc : IsCond G c) (K : Finset V) (b : V → ℝ) :
    ∃ u : V → ℝ, (∀ x ∈ K, netLaplacian G c u x = 0) ∧ ∀ x, x ∉ K → u x = b x := by
  set b' : V → ℝ := fun v => if v ∈ K then 0 else b v with hb'
  obtain ⟨φ, hφ⟩ := LinearMap.surjective_of_injective (bvpMap_injective hG hc K)
    (fun x : K => -netLaplacian G c b' x)
  refine ⟨extC K φ + b', fun x hx => ?_, fun x hx => ?_⟩
  · have h1 : netLaplacian G c (extC K φ) x = -netLaplacian G c b' x := by
      have := congrFun hφ ⟨x, hx⟩
      rw [bvpMap_apply] at this
      exact this
    rw [netLaplacian_add, h1, neg_add_cancel]
  · simp [extC_eq_zero_of_not_mem K φ hx, hb', hx]

/-- The effective conductance between `x₁` and `x₂` of the network formed by a finite set `K`
and the edges joining it to the rest of the graph: the current entering `K` at `x₁` for a voltage
harmonic on `K`, equal to one at `x₂` and to zero at every other vertex outside `K`. It is zero
when no such voltage exists. -/
noncomputable def effCond (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (K : Finset V)
    (x₁ x₂ : V) : ℝ :=
  if h : ∃ u : V → ℝ, (∀ x ∈ K, netLaplacian G c u x = 0) ∧
      ∀ x, x ∉ K → u x = if x = x₂ then 1 else 0 then inflow c K h.choose x₁ else 0

/-- **Kirchhoff's law for a finite set with two exits.** If `f` is harmonic on `K` and every edge
leaving `K` ends at `x₁` or at `x₂`, the currents entering `K` at `x₁` and at `x₂` cancel. -/
theorem inflow_add_inflow_eq_zero {c : V → V → ℝ} (hc : IsCond G c) (K : Finset V) {x₁ x₂ : V}
    (h₁ : x₁ ∉ K) (h₂ : x₂ ∉ K) (hne : x₁ ≠ x₂)
    (hcut : ∀ x ∈ K, ∀ y, G.Adj x y → y ∉ K → y = x₁ ∨ y = x₂)
    {f : V → ℝ} (hf : ∀ x ∈ K, netLaplacian G c f x = 0) :
    inflow c K f x₁ + inflow c K f x₂ = 0 := by
  have hsum : ∑ x ∈ K, netLaplacian G c f x = 0 := Finset.sum_eq_zero hf
  have hdisj : Disjoint K {x₁, x₂} := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    rcases Finset.mem_insert.mp hy' with rfl | hy''
    · exact h₁ hy
    · rw [Finset.mem_singleton] at hy''
      subst hy''
      exact h₂ hy
  have hsplit : ∀ x ∈ K, netLaplacian G c f x
      = ∑ y ∈ K, c x y * (f y - f x) + (c x x₁ * (f x₁ - f x) + c x x₂ * (f x₂ - f x)) := by
    intro x hx
    have hT : G.neighborFinset x ⊆ K ∪ {x₁, x₂} := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      by_cases hyK : y ∈ K
      · exact Finset.mem_union_left _ hyK
      · rcases hcut x hx y hy hyK with rfl | rfl <;> simp
    rw [netLaplacian_eq_sum_of_subset (fun y hy => hc.zero_of_not_adj hy) f hT,
      Finset.sum_union hdisj, Finset.sum_pair hne]
  have hint : ∑ x ∈ K, ∑ y ∈ K, c x y * (f y - f x) = 0 := by
    have h1 : ∑ x ∈ K, ∑ y ∈ K, c x y * (f y - f x)
        = ∑ x ∈ K, ∑ y ∈ K, c y x * (f x - f y) := Finset.sum_comm
    have h2 : ∑ x ∈ K, ∑ y ∈ K, c y x * (f x - f y)
        = -∑ x ∈ K, ∑ y ∈ K, c x y * (f y - f x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hc.symm y x]
      ring
    linarith
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hint, zero_add,
    Finset.sum_add_distrib] at hsum
  have e1 : ∑ x ∈ K, c x x₁ * (f x₁ - f x) = -inflow c K f x₁ := by
    rw [inflow, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hc.symm y x₁]
    ring
  have e2 : ∑ x ∈ K, c x x₂ * (f x₂ - f x) = -inflow c K f x₂ := by
    rw [inflow, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hc.symm y x₂]
    ring
  linarith

/-- **The effective conductance of a two-edge cut.** If every edge leaving the finite set `K` ends
at `x₁` or at `x₂ ≠ x₁`, then for every function harmonic on `K` the current entering `K` at `x₁`
is `effCond G c K x₁ x₂ (f x₂ - f x₁)`, and the current entering at `x₂` is its negative. -/
theorem inflow_eq_effCond (hG : G.Connected) [Infinite V] {c : V → V → ℝ} (hc : IsCond G c)
    (K : Finset V) {x₁ x₂ : V} (h₁ : x₁ ∉ K) (h₂ : x₂ ∉ K) (hne : x₁ ≠ x₂)
    (hcut : ∀ x ∈ K, ∀ y, G.Adj x y → y ∉ K → y = x₁ ∨ y = x₂)
    {f : V → ℝ} (hf : ∀ x ∈ K, netLaplacian G c f x = 0) :
    inflow c K f x₁ = effCond G c K x₁ x₂ * (f x₂ - f x₁) ∧
      inflow c K f x₂ = effCond G c K x₁ x₂ * (f x₁ - f x₂) := by
  have hex : ∃ u : V → ℝ, (∀ x ∈ K, netLaplacian G c u x = 0) ∧
      ∀ x, x ∉ K → u x = if x = x₂ then 1 else 0 := exists_harmonicOn_eq_off hG hc K _
  have hceff : effCond G c K x₁ x₂ = inflow c K hex.choose x₁ := by rw [effCond, dif_pos hex]
  obtain ⟨hu1, hu2⟩ := hex.choose_spec
  set u : V → ℝ := hex.choose with hu
  have hux₁ : u x₁ = 0 := by rw [hu2 x₁ h₁, if_neg hne]
  have hux₂ : u x₂ = 1 := by rw [hu2 x₂ h₂, if_pos rfl]
  set g : V → ℝ := fun v => f x₁ + (f x₂ - f x₁) * u v with hg
  have hgK : ∀ x ∈ K, netLaplacian G c g x = 0 := by
    intro x hx
    have hshift : netLaplacian G c g x = netLaplacian G c (fun v => (f x₂ - f x₁) * u v) x := by
      simp only [netLaplacian, hg]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hshift, netLaplacian_smul, hu1 x hx, mul_zero]
  have hfg : ∀ x ∈ K, f x = g x := by
    refine eqOn_of_harmonicOn_of_boundary hG hc K h₁ hf hgK ?_
    intro x hx y hxy hy
    rcases hcut x hx y hxy hy with hy' | hy'
    · rw [hy']
      simp only [hg, hux₁]
      ring
    · rw [hy']
      simp only [hg, hux₂]
      ring
  have hin₁ : inflow c K f x₁ = (f x₂ - f x₁) * inflow c K u x₁ := by
    rw [inflow, inflow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hfg y hy, hg]
    simp only
    rw [hux₁]
    ring
  have hin₂ : inflow c K f x₂ = (f x₂ - f x₁) * inflow c K u x₂ := by
    rw [inflow, inflow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hfg y hy, hg]
    simp only
    rw [hux₂]
    ring
  have hcons := inflow_add_inflow_eq_zero hc K h₁ h₂ hne hcut hu1
  constructor
  · rw [hin₁, hceff]
    ring
  · rw [hin₂, hceff, show inflow c K u x₂ = -inflow c K u x₁ by linarith]
    ring

/-- At a vertex where a nonnegative function vanishes and is harmonic, it vanishes at every
neighbour. -/
theorem eq_zero_of_adj_of_harmonic_of_nonneg {c : V → V → ℝ} (hc : IsCond G c) {u : V → ℝ}
    (hu0 : ∀ v, 0 ≤ u v) {a : V} (ha : netLaplacian G c u a = 0) (hua : u a = 0) {d : V}
    (had : G.Adj a d) : u d = 0 := by
  rw [netLaplacian] at ha
  have hnn : ∀ w ∈ G.neighborFinset a, 0 ≤ c a w * (u w - u a) := fun w _ => by
    rw [hua, sub_zero]
    exact mul_nonneg (hc.nonneg a w) (hu0 w)
  have hd := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp ha d
    ((SimpleGraph.mem_neighborFinset _ _ _).mpr had)
  rw [hua, sub_zero] at hd
  rcases mul_eq_zero.mp hd with h | h
  · exact absurd h (hc.pos had).ne'
  · exact h

/-- **The effective conductance of a connected two-edge cut is positive.** If moreover the edge
`x₁ a₁` enters `K`, the edge `a₂ x₂` leaves it, and a walk inside `K` joins `a₁` to `a₂`, then
`effCond G c K x₁ x₂` is positive. -/
theorem effCond_pos (hG : G.Connected) [Infinite V] {c : V → V → ℝ} (hc : IsCond G c)
    (K : Finset V) {x₁ x₂ : V} (h₁ : x₁ ∉ K) (h₂ : x₂ ∉ K) (hne : x₁ ≠ x₂)
    {a₁ a₂ : V} (ha₁ : a₁ ∈ K) (hxa₁ : G.Adj x₁ a₁) (hxa₂ : G.Adj a₂ x₂) (p : G.Walk a₁ a₂)
    (hp : ∀ z ∈ p.support, z ∈ K) : 0 < effCond G c K x₁ x₂ := by
  have hex : ∃ u : V → ℝ, (∀ x ∈ K, netLaplacian G c u x = 0) ∧
      ∀ x, x ∉ K → u x = if x = x₂ then 1 else 0 := exists_harmonicOn_eq_off hG hc K _
  have hceff : effCond G c K x₁ x₂ = inflow c K hex.choose x₁ := by rw [effCond, dif_pos hex]
  obtain ⟨hu1, hu2⟩ := hex.choose_spec
  set u : V → ℝ := hex.choose with hu
  have hux₁ : u x₁ = 0 := by rw [hu2 x₁ h₁, if_neg hne]
  have hux₂ : u x₂ = 1 := by rw [hu2 x₂ h₂, if_pos rfl]
  have hu0 : ∀ v, 0 ≤ u v := by
    have hmin := le_of_harmonicOn hG hc K ∅ (fun v => -u v) 0 h₁
      (fun x hx _ => by rw [netLaplacian_neg, hu1 x hx, neg_zero])
      (fun x hx => by
        show -u x ≤ 0
        rw [hu2 x hx]
        split_ifs <;> norm_num)
      (fun x hx => absurd hx (Set.notMem_empty x))
    intro v
    have := hmin v
    linarith
  have hterm : ∀ y ∈ K, 0 ≤ c x₁ y * (u y - u x₁) := fun y _ => by
    rw [hux₁, sub_zero]
    exact mul_nonneg (hc.nonneg x₁ y) (hu0 y)
  rw [hceff]
  by_contra hle
  have hzero : inflow c K u x₁ = 0 :=
    le_antisymm (not_lt.mp hle) (Finset.sum_nonneg hterm)
  have hua₁ : u a₁ = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero a₁ ha₁
    rw [hux₁, sub_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (hc.pos hxa₁).ne'
    · exact h'
  have hwalk : ∀ {a b : V} (q : G.Walk a b), (∀ z ∈ q.support, z ∈ K) → u a = 0 → u b = 0 := by
    intro a b q
    induction q with
    | nil => exact fun _ h => h
    | @cons a d e had q ih =>
      intro hq hua
      have haK : a ∈ K := hq a (by simp)
      exact ih (fun z hz => hq z (by simp [hz]))
        (eq_zero_of_adj_of_harmonic_of_nonneg hc hu0 (hu1 a haK) hua had)
  have hua₂ : u a₂ = 0 := hwalk p hp hua₁
  have hux₂' : u x₂ = 0 := eq_zero_of_adj_of_harmonic_of_nonneg hc hu0
    (hu1 a₂ (hp a₂ (SimpleGraph.Walk.end_mem_support p))) hua₂ hxa₂
  rw [hux₂] at hux₂'
  exact one_ne_zero hux₂'

/-! ### The network with the finite side of a cut replaced by one edge -/

/-- The pair `{a, b}` is the new edge `{x₁, x₂}`. -/
def IsNewEdge (x₁ x₂ a b : V) : Prop := a ≠ b ∧ (a = x₁ ∧ b = x₂ ∨ a = x₂ ∧ b = x₁)

/-- The graph on the vertices outside `K` that keeps the edges of `G` between them and joins
`x₁` to `x₂`. When `x₁ = x₂` no edge is added and this is `G` with `K` deleted. -/
def cutGraph (G : SimpleGraph V) (K : Finset V) (x₁ x₂ : V) : SimpleGraph {v // v ∉ K} :=
  SimpleGraph.fromRel fun u w => G.Adj u.1 w.1 ∨ (u.1 = x₁ ∧ w.1 = x₂)

omit [G.LocallyFinite] in
/-- Adjacency in `cutGraph`: an edge of `G` between vertices outside `K`, or the new edge. -/
theorem cutGraph_adj {K : Finset V} {x₁ x₂ : V} {u w : {v // v ∉ K}} :
    (cutGraph G K x₁ x₂).Adj u w ↔ G.Adj u.1 w.1 ∨ IsNewEdge x₁ x₂ u.1 w.1 := by
  rw [cutGraph, SimpleGraph.fromRel_adj, IsNewEdge]
  constructor
  · rintro ⟨hne, (h | h) | (h | h)⟩
    · exact Or.inl h
    · exact Or.inr ⟨fun e => hne (Subtype.ext e), Or.inl h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨fun e => hne (Subtype.ext e), Or.inr ⟨h.2, h.1⟩⟩
  · rintro (h | ⟨hne, h | h⟩)
    · exact ⟨fun e => G.ne_of_adj h (congrArg Subtype.val e), Or.inl (Or.inl h)⟩
    · exact ⟨fun e => hne (congrArg Subtype.val e), Or.inl (Or.inr h)⟩
    · exact ⟨fun e => hne (congrArg Subtype.val e), Or.inr (Or.inr ⟨h.2, h.1⟩)⟩

/-- The candidate neighbours of `u` in `cutGraph`: its neighbours in `G` and the two endpoints,
outside `K`. -/
noncomputable def cutNbr (G : SimpleGraph V) [G.LocallyFinite] (K : Finset V) (x₁ x₂ : V)
    (u : {v // v ∉ K}) : Finset {v // v ∉ K} :=
  (G.neighborFinset u.1 ∪ {x₁, x₂}).subtype (· ∉ K)

theorem adj_cutGraph_mem_cutNbr {K : Finset V} {x₁ x₂ : V} {u w : {v // v ∉ K}}
    (h : (cutGraph G K x₁ x₂).Adj u w) : w ∈ cutNbr G K x₁ x₂ u := by
  rw [cutNbr, Finset.mem_subtype]
  rcases cutGraph_adj.mp h with h' | ⟨-, h' | h'⟩
  · exact Finset.mem_union_left _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr h')
  · simp [h'.2]
  · simp [h'.2]

noncomputable instance cutGraph.instLocallyFinite (K : Finset V) (x₁ x₂ : V) :
    (cutGraph G K x₁ x₂).LocallyFinite := fun u =>
  Fintype.ofFinset ((cutNbr G K x₁ x₂ u).filter fun w => (cutGraph G K x₁ x₂).Adj u w)
    fun w => by
      rw [Finset.mem_filter, SimpleGraph.mem_neighborSet]
      exact ⟨fun h => h.2, fun h => ⟨adj_cutGraph_mem_cutNbr h, h⟩⟩

/-- The conductance of `cutGraph`: that of `G` on the kept edges, increased by `ceff` on the new
edge `{x₁, x₂}`. -/
noncomputable def cutCond (c : V → V → ℝ) (K : Finset V) (x₁ x₂ : V) (ceff : ℝ) :
    {v // v ∉ K} → {v // v ∉ K} → ℝ :=
  fun u w => c u.1 w.1 + if IsNewEdge x₁ x₂ u.1 w.1 then ceff else 0

theorem isNewEdge_comm {x₁ x₂ a b : V} : IsNewEdge x₁ x₂ a b ↔ IsNewEdge x₁ x₂ b a := by
  unfold IsNewEdge
  constructor <;> rintro ⟨hne, h | h⟩ <;>
    exact ⟨Ne.symm hne, by tauto⟩

omit [G.LocallyFinite] in
/-- `cutCond` is a conductance of `cutGraph` when `ceff ≥ 0` and `ceff > 0` in case the new edge is
not already an edge of `G`. -/
theorem isCond_cutCond {c : V → V → ℝ} (hc : IsCond G c) (K : Finset V) {x₁ x₂ : V} {ceff : ℝ}
    (hceff : 0 ≤ ceff) (hpos : x₁ ≠ x₂ → ¬ G.Adj x₁ x₂ → 0 < ceff) :
    IsCond (cutGraph G K x₁ x₂) (cutCond c K x₁ x₂ ceff) where
  symm := by
    intro u w
    rw [cutCond, cutCond, hc.symm u.1 w.1]
    by_cases h : IsNewEdge x₁ x₂ u.1 w.1
    · rw [if_pos h, if_pos (isNewEdge_comm.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (isNewEdge_comm.mp h'))]
  pos := by
    intro u w h
    rw [cutCond]
    rcases cutGraph_adj.mp h with h' | h'
    · have := hc.pos h'
      split_ifs <;> linarith
    · rw [if_pos h']
      by_cases hadj : G.Adj u.1 w.1
      · linarith [hc.pos hadj]
      · have hne : x₁ ≠ x₂ := by
          obtain ⟨hab, h'' | h''⟩ := h'
          · rw [← h''.1, ← h''.2]; exact hab
          · rw [← h''.1, ← h''.2]; exact hab.symm
        have hnadj : ¬ G.Adj x₁ x₂ := by
          obtain ⟨-, h'' | h''⟩ := h'
          · rw [← h''.1, ← h''.2]; exact hadj
          · rw [← h''.1, ← h''.2]; exact fun e => hadj e.symm
        linarith [hc.nonneg u.1 w.1, hpos hne hnadj]
  zero_of_not_adj := by
    intro u w h
    rw [cutCond, hc.zero_of_not_adj (fun h' => h (cutGraph_adj.mpr (Or.inl h'))),
      if_neg (fun h' => h (cutGraph_adj.mpr (Or.inr h'))), add_zero]

/-- **The Laplacian of the reduced network.** At a vertex `u` outside `K`, the Laplacian of `f` in
`cutGraph` with `cutCond` is that in `G`, minus the current entering `K` at `u`, plus the current
along the new edge. -/
theorem netLaplacian_cutGraph {c : V → V → ℝ} (hc : IsCond G c) (K : Finset V) {x₁ x₂ : V}
    (h₁ : x₁ ∉ K) (h₂ : x₂ ∉ K) (ceff : ℝ) (f : V → ℝ) (u : {v // v ∉ K}) :
    netLaplacian (cutGraph G K x₁ x₂) (cutCond c K x₁ x₂ ceff) (fun v => f v.1) u
      = netLaplacian G c f u.1 - inflow c K f u.1
        + ∑ y ∈ ({x₁, x₂} : Finset V),
            (if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1) := by
  have hzero' : ∀ w, ¬ (cutGraph G K x₁ x₂).Adj u w → cutCond c K x₁ x₂ ceff u w = 0 := by
    intro w h
    rw [cutCond, hc.zero_of_not_adj (fun h' => h (cutGraph_adj.mpr (Or.inl h'))),
      if_neg (fun h' => h (cutGraph_adj.mpr (Or.inr h'))), add_zero]
  have hsub' : (cutGraph G K x₁ x₂).neighborFinset u ⊆ cutNbr G K x₁ x₂ u := fun w hw =>
    adj_cutGraph_mem_cutNbr ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)
  rw [netLaplacian_eq_sum_of_subset hzero' _ hsub', cutNbr]
  have hsubt : ∑ w ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).subtype (· ∉ K),
      cutCond c K x₁ x₂ ceff u w * (f w.1 - f u.1)
      = ∑ y ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).filter (· ∉ K),
          (c u.1 y + if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1) :=
    Finset.sum_subtype_eq_sum_filter
      (fun y => (c u.1 y + if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1))
  rw [hsubt]
  have hG : netLaplacian G c f u.1
      = ∑ y ∈ G.neighborFinset u.1 ∪ {x₁, x₂}, c u.1 y * (f y - f u.1) :=
    netLaplacian_eq_sum_of_subset (fun y hy => hc.zero_of_not_adj hy) f Finset.subset_union_left
  have hsplit := Finset.sum_filter_add_sum_filter_not (G.neighborFinset u.1 ∪ {x₁, x₂})
    (fun y => y ∉ K) (fun y => c u.1 y * (f y - f u.1))
  have hin : ∑ y ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).filter (fun y => ¬ y ∉ K),
      c u.1 y * (f y - f u.1) = inflow c K f u.1 := by
    rw [inflow]
    refine Finset.sum_subset (fun y hy => by simpa using (Finset.mem_filter.mp hy).2) ?_
    intro y hyK hy
    have hny : ¬ G.Adj u.1 y := by
      intro h
      exact hy (Finset.mem_filter.mpr ⟨Finset.mem_union_left _
        ((SimpleGraph.mem_neighborFinset _ _ _).mpr h), by simpa using hyK⟩)
    rw [hc.zero_of_not_adj hny, zero_mul]
  have hnew : ∑ y ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).filter (fun y => y ∉ K),
      (if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1)
      = ∑ y ∈ ({x₁, x₂} : Finset V),
          (if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro y hy
      refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hy, ?_⟩
      rcases Finset.mem_insert.mp hy with hy' | hy'
      · rw [hy']
        exact h₁
      · rw [Finset.mem_singleton] at hy'
        rw [hy']
        exact h₂
    · intro y _ hy
      have hnot : ¬ IsNewEdge x₁ x₂ u.1 y := by
        rintro ⟨-, h | h⟩
        · exact hy (by simp [h.2])
        · exact hy (by simp [h.2])
      rw [if_neg hnot, zero_mul]
  have hFsplit : ∑ y ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).filter (fun y => y ∉ K),
      (c u.1 y + if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1)
      = ∑ y ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).filter (fun y => y ∉ K),
          c u.1 y * (f y - f u.1)
        + ∑ y ∈ (G.neighborFinset u.1 ∪ {x₁, x₂}).filter (fun y => y ∉ K),
            (if IsNewEdge x₁ x₂ u.1 y then ceff else 0) * (f y - f u.1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hFsplit, hnew, hG, ← hsplit, hin]
  ring

/-- **Deleting a finite piece attached at one vertex.** If every edge leaving `K` ends at `t` and
`f` is harmonic on `K`, the Laplacian of `f` at every vertex outside `K` is unchanged when `K` is
deleted. -/
theorem netLaplacian_cutGraph_of_cutVertex (hG : G.Connected) {c : V → V → ℝ} (hc : IsCond G c)
    (K : Finset V) {t : V} (ht : t ∉ K) (hcut : ∀ x ∈ K, ∀ y, G.Adj x y → y ∉ K → y = t)
    {f : V → ℝ} (hf : ∀ x ∈ K, netLaplacian G c f x = 0) (u : {v // v ∉ K}) :
    netLaplacian (cutGraph G K t t) (cutCond c K t t 0) (fun v => f v.1) u
      = netLaplacian G c f u.1 := by
  rw [netLaplacian_cutGraph hc K ht ht 0 f u]
  have hconst := eq_of_harmonicOn_of_cutVertex hG hc K ht hcut hf
  have hin : inflow c K f u.1 = 0 := by
    refine Finset.sum_eq_zero fun y hy => ?_
    by_cases hu : u.1 = t
    · rw [hu, hconst y hy, sub_self, mul_zero]
    · have hny : ¬ G.Adj u.1 y := fun h => hu (hcut y hy u.1 h.symm u.2)
      rw [hc.zero_of_not_adj hny, zero_mul]
  rw [hin]
  simp

/-- **Replacing a finite piece with two exits by one edge.** If every edge leaving `K` ends at
`x₁` or at `x₂ ≠ x₁` and `f` is harmonic on `K`, the Laplacian of `f` at every vertex outside `K`
is unchanged when `K` is replaced by an edge from `x₁` to `x₂` of conductance
`effCond G c K x₁ x₂`. -/
theorem netLaplacian_cutGraph_of_twoExits (hG : G.Connected) [Infinite V] {c : V → V → ℝ}
    (hc : IsCond G c) (K : Finset V) {x₁ x₂ : V} (h₁ : x₁ ∉ K) (h₂ : x₂ ∉ K) (hne : x₁ ≠ x₂)
    (hcut : ∀ x ∈ K, ∀ y, G.Adj x y → y ∉ K → y = x₁ ∨ y = x₂)
    {f : V → ℝ} (hf : ∀ x ∈ K, netLaplacian G c f x = 0) (u : {v // v ∉ K}) :
    netLaplacian (cutGraph G K x₁ x₂) (cutCond c K x₁ x₂ (effCond G c K x₁ x₂)) (fun v => f v.1) u
      = netLaplacian G c f u.1 := by
  rw [netLaplacian_cutGraph hc K h₁ h₂ _ f u, Finset.sum_pair hne]
  obtain ⟨hi₁, hi₂⟩ := inflow_eq_effCond hG hc K h₁ h₂ hne hcut hf
  have hn11 : ¬ IsNewEdge x₁ x₂ x₁ x₁ := fun h => h.1 rfl
  have hn22 : ¬ IsNewEdge x₁ x₂ x₂ x₂ := fun h => h.1 rfl
  have hn12 : IsNewEdge x₁ x₂ x₁ x₂ := ⟨hne, Or.inl ⟨rfl, rfl⟩⟩
  have hn21 : IsNewEdge x₁ x₂ x₂ x₁ := ⟨hne.symm, Or.inr ⟨rfl, rfl⟩⟩
  by_cases hu₁ : u.1 = x₁
  · rw [hu₁, if_neg hn11, if_pos hn12, hi₁]
    ring
  by_cases hu₂ : u.1 = x₂
  · rw [hu₂, if_pos hn21, if_neg hn22, hi₂]
    ring
  have hin : inflow c K f u.1 = 0 := by
    refine Finset.sum_eq_zero fun y hy => ?_
    have hny : ¬ G.Adj u.1 y := by
      intro h
      rcases hcut y hy u.1 h.symm u.2 with h' | h'
      · exact hu₁ h'
      · exact hu₂ h'
    rw [hc.zero_of_not_adj hny, zero_mul]
  have hno : ∀ y, ¬ IsNewEdge x₁ x₂ u.1 y := by
    rintro y ⟨-, h | h⟩
    · exact hu₁ h.1
    · exact hu₂ h.1
  rw [hin, if_neg (hno x₁), if_neg (hno x₂)]
  ring

end UCPlanar.Support
