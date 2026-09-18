/-
The random walk of a conductance network, and recurrence of that walk.

The library's `LatticeProb.Graph.heat` is the walk of the unit conductance.  A
network with conductances `c` has its own walk, with transition probability
`c x y / weight G c x` from `x` to `y`; this file defines its heat kernel, its
Green function and recurrence, so that the Liouville theorem can be stated for
the network the paper uses rather than for the unit conductance.
-/
import LatticeProb.Network.Basic
import LatticeProb.Graph.Reach
import LatticeProb.Graph.Basic

open scoped Classical ENNReal

namespace UCPlanar.Support

open LatticeProb.Network LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The `k`-step transition probability of the walk of the conductance `c`:
`cHeat G c k x y = P_x(X_k = y)`. -/
noncomputable def cHeat (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) :
    ℕ → V → V → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | k + 1 => fun x y =>
      (∑ z ∈ G.neighborFinset x, c x z * cHeat G c k z y) / weight G c x

/-- The one-step energy of `f` at `u`: the `c`-weighted mean square deviation
of `f` from `f u` over the neighbours of `u`. -/
noncomputable def cEnergy (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (f : V → ℝ) (u : V) : ℝ :=
  ∑ w ∈ G.neighborFinset u, (c u w / weight G c u) * (f w - f u) ^ 2

/-- The Green function of the walk of the conductance `c`, valued in `[0,∞]`. -/
noncomputable def cGreen (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (x v : V) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (cHeat G c k x v)

/-- The network is recurrent at `o`: the walk of the conductance `c` returns to
`o` with probability one, equivalently its Green function diverges there. -/
def NetworkRecurrent (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (o : V) : Prop :=
  cGreen G c o o = ⊤

/-- The total conductance at a vertex of positive degree is positive. -/
theorem weight_pos {c : V → V → ℝ} (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    (x : V) : 0 < weight G c x := by
  classical
  have hcard : 0 < (G.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg x
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
  exact Finset.sum_pos' (fun z _ => hc.nonneg x z) ⟨y, hy,
    hc.pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)⟩

/-- The base clause of the transition probability. -/
theorem cHeat_zero (c : V → V → ℝ) (x y : V) :
    cHeat G c 0 x y = if x = y then 1 else 0 := rfl

/-- The successor clause of the transition probability, with the division
distributed over the sum. -/
theorem cHeat_succ (c : V → V → ℝ) (k : ℕ) (x y : V) :
    cHeat G c (k + 1) x y
      = ∑ z ∈ G.neighborFinset x, (c x z / weight G c x) * cHeat G c k z y := by
  simp only [cHeat]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun z _ => by ring

/-- The Green function is the sum of the transition probabilities. -/
theorem cGreen_eq_tsum (c : V → V → ℝ) (x v : V) :
    cGreen G c x v = ∑' k : ℕ, ENNReal.ofReal (cHeat G c k x v) := rfl

theorem cHeat_eq_zero_of_notMem_reach {c : V → V → ℝ} :
    ∀ (k : ℕ) (x y : V), y ∉ LatticeProb.Graph.reach G k x → cHeat G c k x y = 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro x y hy
      rw [LatticeProb.Graph.reach_zero, Finset.mem_singleton] at hy
      simp only [cHeat]
      rw [if_neg (fun h => hy h.symm)]
  | succ k ih =>
      intro x y hy
      rw [LatticeProb.Graph.reach_succ] at hy
      simp only [Finset.mem_biUnion, not_exists, not_and] at hy
      simp only [cHeat]
      rw [Finset.sum_eq_zero (fun w hw => by
            rw [mul_eq_zero]
            right
            exact ih w y (hy w hw)), zero_div]

theorem sum_cHeat_eq_one {c : V → V → ℝ} (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (k : ℕ) (x : V), ∑ y ∈ LatticeProb.Graph.reach G k x, cHeat G c k x y = 1 := by
  classical
  intro k
  induction k with
  | zero =>
      intro x
      rw [LatticeProb.Graph.reach_zero, Finset.sum_singleton]
      simp [cHeat]
  | succ k ih =>
      intro x
      have hsub : ∀ w ∈ G.neighborFinset x,
          LatticeProb.Graph.reach G k w ⊆ LatticeProb.Graph.reach G (k + 1) x := by
        intro w hw v hv
        simp only [LatticeProb.Graph.reach_succ, Finset.mem_biUnion]
        exact ⟨w, hw, hv⟩
      have hstep : ∀ w ∈ G.neighborFinset x,
          ∑ y ∈ LatticeProb.Graph.reach G (k + 1) x, cHeat G c k w y = 1 := by
        intro w hw
        rw [← ih w]
        exact (Finset.sum_subset (hsub w hw) (fun y _ hy =>
          cHeat_eq_zero_of_notMem_reach k w y hy)).symm
      rw [Finset.sum_congr rfl (fun y _ => cHeat_succ c k x y)]
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun w hw => by
        rw [← Finset.mul_sum, hstep w hw, mul_one])]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (weight_pos hc hdeg x))

/-- The mean value property iterated for the walk of a conductance `c`: a
`c`-harmonic function equals its `n`-step `c`-kernel average. -/
theorem eq_sum_cHeat_mul_of_harmonic {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ)
    (hharm : ∀ x, netLaplacian G c f x = 0) :
    ∀ (n : ℕ) (x : V), f x = ∑ v ∈ reach G n x, cHeat G c n x v * f v := by
  classical
  intro n
  induction n with
  | zero =>
    intro x
    simp [reach_zero, cHeat]
  | succ n ih =>
    intro x
    have hmv : f x = (∑ y ∈ G.neighborFinset x, c x y * f y) / weight G c x :=
      (harmonic_iff_mean f (ne_of_gt (weight_pos hc hdeg x))).mp (hharm x)
    rw [hmv]
    have hsub : ∀ y ∈ G.neighborFinset x,
        reach G n y ⊆ reach G (n + 1) x := by
      intro y hy v hv
      rw [reach_succ]
      exact Finset.mem_biUnion.mpr ⟨y, hy, hv⟩
    have hstep : ∀ y ∈ G.neighborFinset x,
        f y = ∑ v ∈ reach G (n + 1) x, cHeat G c n y v * f v := by
      intro y hy
      rw [ih y]
      exact Finset.sum_subset (hsub y hy) (fun v _ hv => by
        rw [cHeat_eq_zero_of_notMem_reach n y v hv, zero_mul])
    rw [Finset.sum_congr rfl (fun y hy => by rw [hstep y hy])]
    have hdist : ∀ y ∈ G.neighborFinset x,
        (c x y * (∑ v ∈ reach G (n + 1) x, cHeat G c n y v * f v)) / weight G c x
          = ∑ v ∈ reach G (n + 1) x,
              (c x y / weight G c x) * cHeat G c n y v * f v := by
      intro y hy
      rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [Finset.sum_div, Finset.sum_congr rfl hdist, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_mul, ← cHeat_succ c n x v]

/-- The Chapman--Kolmogorov identity for the walk of a conductance `c`. -/
theorem cHeat_add {c : V → V → ℝ} (_hc : IsCond G c) (_hdeg : ∀ v : V, 0 < G.degree v)
    (a b : ℕ) (u w : V) :
    cHeat G c (a + b) u w
      = ∑ z ∈ reach G a u, cHeat G c a u z * cHeat G c b z w := by
  classical
  induction a generalizing u with
  | zero =>
      rw [Nat.zero_add, reach_zero, Finset.sum_singleton, cHeat_zero, if_pos rfl, one_mul]
  | succ a ih =>
      rw [Nat.succ_add, cHeat_succ]
      have hsub : ∀ y ∈ G.neighborFinset u, reach G a y ⊆ reach G (a + 1) u := by
        intro y hy z hz
        rw [reach_succ]
        exact Finset.mem_biUnion.mpr ⟨y, hy, hz⟩
      have hext : ∀ y ∈ G.neighborFinset u,
          (∑ z ∈ reach G a y, (c u y / weight G c u) * cHeat G c a y z * cHeat G c b z w)
            = ∑ z ∈ reach G (a + 1) u,
                (c u y / weight G c u) * cHeat G c a y z * cHeat G c b z w := by
        intro y hy
        refine Finset.sum_subset (hsub y hy) fun z _ hz => ?_
        rw [cHeat_eq_zero_of_notMem_reach a y z hz]; ring
      have hstep : ∀ y ∈ G.neighborFinset u,
          cHeat G c (a + b) y w
            = ∑ z ∈ reach G a y, cHeat G c a y z * cHeat G c b z w := fun y _ => ih y
      rw [Finset.sum_congr rfl (fun y hy => by rw [hstep y hy])]
      have hdist : ∀ y ∈ G.neighborFinset u,
          c u y / weight G c u * (∑ z ∈ reach G a y, cHeat G c a y z * cHeat G c b z w)
            = ∑ z ∈ reach G a y,
                (c u y / weight G c u) * cHeat G c a y z * cHeat G c b z w := by
        intro y hy
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [Finset.sum_congr rfl (fun y hy => by rw [hdist y hy])]
      rw [Finset.sum_congr rfl (fun y hy => hext y hy)]
      rw [Finset.sum_comm]
      conv_rhs => rw [reach_succ]
      refine Finset.sum_congr rfl fun z hz => ?_
      rw [cHeat_succ c a u z, Finset.sum_mul]


/-- The transition probability of the `c`-walk is nonnegative. -/
theorem cHeat_nonneg {c : V → V → ℝ} (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (k : ℕ) (x y : V), 0 ≤ cHeat G c k x y := by
  classical
  intro k
  induction k with
  | zero =>
      intro x y
      rw [cHeat_zero]
      split <;> norm_num
  | succ k ih =>
      intro x y
      rw [cHeat_succ]
      exact Finset.sum_nonneg fun z _ =>
        mul_nonneg (div_nonneg (hc.nonneg x z) (le_of_lt (weight_pos hc hdeg x))) (ih z y)

theorem cHeat_pos_of_walk {c : V → V → ℝ} (hc : IsCond G c) (hdeg : ∀ v : V, 0 < G.degree v)
    {x y : V} (p : G.Walk x y) : 0 < cHeat G c p.length x y := by
  classical
  induction p with
  | nil => simp [cHeat]
  | @cons u w z h p ih =>
      rw [SimpleGraph.Walk.length_cons, cHeat_succ]
      have hw : w ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).mpr h
      have hle : (c u w / weight G c u) * cHeat G c p.length w z
          ≤ ∑ s ∈ G.neighborFinset u, (c u s / weight G c u) * cHeat G c p.length s z :=
        Finset.single_le_sum (f := fun s => (c u s / weight G c u) * cHeat G c p.length s z)
          (fun s _ => mul_nonneg (div_nonneg (hc.nonneg u s) (le_of_lt (weight_pos hc hdeg u)))
            (cHeat_nonneg hc hdeg p.length s z)) hw
      exact lt_of_lt_of_le (mul_pos (div_pos (hc.pos h) (weight_pos hc hdeg u)) ih) hle


/-- Every vertex reached by a walk lies in the corresponding `reach` set. -/
theorem mem_reach_of_walk {x y : V} (p : G.Walk x y) : y ∈ reach G p.length x := by
  induction p with
  | nil => rw [SimpleGraph.Walk.length_nil, reach_zero]; exact Finset.mem_singleton_self _
  | @cons u w z h p ih =>
      rw [SimpleGraph.Walk.length_cons, reach_succ]
      exact Finset.mem_biUnion.mpr ⟨w, (SimpleGraph.mem_neighborFinset _ _ _).mpr h, ih⟩

theorem cGreen_eq_top_of_recurrent {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (hG : G.Connected) {o : V}
    (hrec : NetworkRecurrent G c o) (v : V) : cGreen G c v o = ⊤ := by
  have hoo : (∑' k : ℕ, ENNReal.ofReal (cHeat G c k o o)) = ⊤ := hrec
  have hvo : (∑' k : ℕ, ENNReal.ofReal (cHeat G c k v o)) = ⊤ := by
    obtain ⟨p⟩ := hG.preconnected v o
    set r := p.length with hr
    have hcpos : 0 < cHeat G c r v o := cHeat_pos_of_walk hc hdeg p
    have hstep : ∀ k : ℕ,
        ENNReal.ofReal (cHeat G c r v o) * ENNReal.ofReal (cHeat G c k o o)
          ≤ ENNReal.ofReal (cHeat G c (r + k) v o) := by
      intro k
      rw [← ENNReal.ofReal_mul (cHeat_nonneg hc hdeg r v o)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [cHeat_add hc hdeg r k v o]
      have ho : o ∈ reach G r v := by
        rw [hr]
        exact mem_reach_of_walk p
      exact Finset.single_le_sum
        (f := fun z => cHeat G c r v z * cHeat G c k z o)
        (fun z _ => mul_nonneg (cHeat_nonneg hc hdeg r v z) (cHeat_nonneg hc hdeg k z o)) ho
    have hsum : ENNReal.ofReal (cHeat G c r v o) * (∑' k : ℕ, ENNReal.ofReal (cHeat G c k o o))
        ≤ ∑' k : ℕ, ENNReal.ofReal (cHeat G c (r + k) v o) := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum hstep
    have hle : (∑' k : ℕ, ENNReal.ofReal (cHeat G c (r + k) v o))
        ≤ ∑' k : ℕ, ENNReal.ofReal (cHeat G c k v o) :=
      ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective r)
        (fun k => ENNReal.ofReal (cHeat G c k v o))
    rw [hoo, ENNReal.mul_top (by simpa using (ENNReal.ofReal_pos.mpr hcpos).ne')] at hsum
    exact top_le_iff.mp (le_trans hsum hle)
  rw [cGreen_eq_tsum, hvo]


/-- The variance identity behind the energy argument. -/
theorem sum_mul_sq_sub_eq (s : Finset V) (a f : V → ℝ) (c : ℝ)
    (hsum : ∑ w ∈ s, a w = 1) (hc : c = ∑ w ∈ s, a w * f w) :
    ∑ w ∈ s, a w * (f w - c) ^ 2 = ∑ w ∈ s, a w * f w ^ 2 - c ^ 2 := by
  subst hc
  have h1 : ∑ w ∈ s, a w * (f w - ∑ v ∈ s, a v * f v) ^ 2
      = ∑ w ∈ s, (a w * f w ^ 2 - 2 * (a w * f w) * (∑ v ∈ s, a v * f v)
          + a w * (∑ v ∈ s, a v * f v) ^ 2) := by
    refine Finset.sum_congr rfl fun w _ => by ring
  rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [show (∑ x ∈ s, a x * (∑ v ∈ s, a v * f v) ^ 2)
      = (∑ x ∈ s, a x) * (∑ v ∈ s, a v * f v) ^ 2 from by rw [Finset.sum_mul]]
  rw [hsum]
  ring


/-- `reach G 1 u` is the neighbour set of `u`. -/
theorem reach_one (u : V) : reach G 1 u = G.neighborFinset u := by
  rw [reach_succ]
  simp only [reach_zero]
  ext v
  simp

theorem cHeat_one {c : V → V → ℝ} (hc : IsCond G c) (u v : V) :
    cHeat G c 1 u v = if G.Adj u v then c u v / weight G c u else 0 := by
  rw [cHeat_succ]
  simp only [cHeat_zero]
  rw [Finset.sum_eq_single v]
  · by_cases h : G.Adj u v
    · simp [h]
    · rw [if_neg h, hc.zero_of_not_adj h, zero_div, zero_mul]
  · intro w _ hwv
    rw [if_neg hwv, mul_zero]
  · intro hv
    rw [hc.zero_of_not_adj (fun h => hv ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)), zero_div,
      zero_mul]

theorem nbr_subset_reach_succ {u : V} {n : ℕ} {x : V} (hu : u ∈ reach G n x) :
    G.neighborFinset u ⊆ reach G (n + 1) x := by
  induction n generalizing u x with
  | zero =>
      rw [reach_zero, Finset.mem_singleton] at hu
      subst hu
      rw [Nat.zero_add, reach_one]
  | succ n ih =>
      rw [reach_succ] at hu
      obtain ⟨y, hy, huy⟩ := Finset.mem_biUnion.mp hu
      intro w hw
      rw [reach_succ]
      exact Finset.mem_biUnion.mpr ⟨y, hy, ih huy hw⟩

theorem cHeat_variance_telescope {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ)
    (hharm : HarmonicOn G c f Set.univ) (n : ℕ) (x : V) :
    ∑ v ∈ reach G (n + 1) x, cHeat G c (n + 1) x v * f v ^ 2
      = ∑ u ∈ reach G n x, cHeat G c n x u * f u ^ 2
        + ∑ u ∈ reach G n x, cHeat G c n x u
            * (∑ w ∈ G.neighborFinset u, (c u w / weight G c u) * (f w - f u) ^ 2) := by
  classical
  have hstep : ∀ u : V,
      (∑ w ∈ G.neighborFinset u, (c u w / weight G c u) * f w ^ 2)
        = f u ^ 2 + ∑ w ∈ G.neighborFinset u, (c u w / weight G c u) * (f w - f u) ^ 2 := by
    intro u
    have hsum : ∑ w ∈ G.neighborFinset u, c u w / weight G c u = 1 := by
      rw [← Finset.sum_div, weight]
      exact div_self (ne_of_gt (weight_pos hc hdeg u))
    have hmv : f u = ∑ w ∈ G.neighborFinset u, (c u w / weight G c u) * f w := by
      have h := (harmonic_iff_mean f (ne_of_gt (weight_pos hc hdeg u))).mp (hharm u (Set.mem_univ u))
      rw [h, Finset.sum_div]
      exact Finset.sum_congr rfl fun w _ => by ring
    have := sum_mul_sq_sub_eq (G.neighborFinset u) (fun w => c u w / weight G c u) f (f u) hsum hmv
    linarith [this]
  have hinner : ∀ u ∈ reach G n x,
      (∑ v ∈ reach G (n + 1) x, cHeat G c 1 u v * f v ^ 2)
        = ∑ w ∈ G.neighborFinset u, c u w / weight G c u * f w ^ 2 := by
    intro u hu
    have hsub : G.neighborFinset u ⊆ reach G (n + 1) x := nbr_subset_reach_succ hu
    rw [(Finset.sum_subset hsub (fun v _ hv => by
      rw [cHeat_one hc, if_neg (fun h => hv ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)),
        zero_mul])).symm]
    exact Finset.sum_congr rfl fun w hw => by
      rw [cHeat_one hc, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)]
  have hleft : ∑ v ∈ reach G (n + 1) x, cHeat G c (n + 1) x v * f v ^ 2
      = ∑ u ∈ reach G n x, cHeat G c n x u
          * (∑ w ∈ G.neighborFinset u, (c u w / weight G c u) * f w ^ 2) := by
    have h1 : ∀ v : V, cHeat G c (n + 1) x v
        = ∑ u ∈ reach G n x, cHeat G c n x u * cHeat G c 1 u v := by
      intro v
      rw [cHeat_add hc hdeg n 1 x v]
    rw [Finset.sum_congr rfl (fun v _ => by rw [h1 v, Finset.sum_mul])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [show (∑ v ∈ reach G (n + 1) x, cHeat G c n x u * cHeat G c 1 u v * f v ^ 2)
        = cHeat G c n x u * ∑ v ∈ reach G (n + 1) x, cHeat G c 1 u v * f v ^ 2 from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => by ring]
    rw [hinner u hu]
  rw [hleft]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hstep u, mul_add])]
  rw [Finset.sum_add_distrib]


/-- The weighted mean square of a bounded `f` is at most `M ^ 2`. -/
theorem cHeat_meanSq_le {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) {f : V → ℝ} {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (n : ℕ) (x : V) :
    ∑ v ∈ reach G n x, cHeat G c n x v * f v ^ 2 ≤ M ^ 2 := by
  calc ∑ v ∈ reach G n x, cHeat G c n x v * f v ^ 2
      ≤ ∑ v ∈ reach G n x, cHeat G c n x v * M ^ 2 := by
        refine Finset.sum_le_sum fun v _ => ?_
        exact mul_le_mul_of_nonneg_left (by nlinarith [abs_le.mp (hM v)]) (cHeat_nonneg hc hdeg n x v)
    _ = (∑ v ∈ reach G n x, cHeat G c n x v) * M ^ 2 := by rw [Finset.sum_mul]
    _ = M ^ 2 := by rw [sum_cHeat_eq_one hc hdeg n x, one_mul]


/-- The energy of the first `N` steps is bounded by the mean square. -/
theorem cHeat_energy_sum_le {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ)
    (hharm : HarmonicOn G c f Set.univ) (hbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    (N : ℕ) (x : V) :
    ∑ n ∈ Finset.range N, ∑ u ∈ reach G n x, cHeat G c n x u * cEnergy G c f u
      ≤ 2 * (Classical.choose hbdd) ^ 2 := by
  classical
  set M := Classical.choose hbdd with hMdef
  have hM : ∀ y, |f y| ≤ M := Classical.choose_spec hbdd
  have htel : ∀ n : ℕ,
      (∑ u ∈ reach G n x, cHeat G c n x u * cEnergy G c f u)
        = (∑ v ∈ reach G (n + 1) x, cHeat G c (n + 1) x v * f v ^ 2)
          - ∑ u ∈ reach G n x, cHeat G c n x u * f u ^ 2 := by
    intro n
    have h := cHeat_variance_telescope hc hdeg f hharm n x
    simp only [cEnergy] at h ⊢
    linarith [h]
  have hsum : ∑ n ∈ Finset.range N, ∑ u ∈ reach G n x, cHeat G c n x u * cEnergy G c f u
      = (∑ v ∈ reach G N x, cHeat G c N x v * f v ^ 2) - f x ^ 2 := by
    induction N with
    | zero =>
        rw [Finset.range_zero, Finset.sum_empty, reach_zero]
        simp [cHeat]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, htel N]
        ring
  rw [hsum]
  have hN := cHeat_meanSq_le hc hdeg hM N x
  have h0 : f x ^ 2 ≤ M ^ 2 := by nlinarith [abs_le.mp (hM x)]
  have h2 : (0:ℝ) ≤ M ^ 2 := sq_nonneg M
  have h3 : (0:ℝ) ≤ f x ^ 2 := sq_nonneg (f x)
  have : (∑ v ∈ reach G N x, cHeat G c N x v * f v ^ 2) - f x ^ 2 ≤ 2 * M ^ 2 := by linarith
  rwa [hMdef]


/-- A summable return series makes the Green function finite. -/
theorem cGreen_ne_top_of_summable {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) {u : V}
    (h : Summable fun n : ℕ => cHeat G c n u u) :
    cGreen G c u u ≠ ⊤ := by
  rw [cGreen_eq_tsum]
  have hnn : ∀ n : ℕ, 0 ≤ cHeat G c n u u := fun n => cHeat_nonneg hc hdeg n u u
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn h]
  exact ENNReal.ofReal_ne_top

/-- An infinite Green function forces the real return series to diverge. -/
theorem not_summable_cHeat_of_cGreen_eq_top {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) {x u : V} (h : cGreen G c x u = ⊤) :
    ¬ Summable fun n : ℕ => cHeat G c n x u := by
  intro hs
  have hnn : ∀ n : ℕ, 0 ≤ cHeat G c n x u := fun n => cHeat_nonneg hc hdeg n x u
  rw [cGreen_eq_tsum, ← ENNReal.ofReal_tsum_of_nonneg hnn hs] at h
  exact ENNReal.ofReal_ne_top h



/-- The energy is nonnegative. -/
theorem cEnergy_nonneg {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (f : V → ℝ) (u : V) :
    0 ≤ cEnergy G c f u := by
  rw [cEnergy]
  exact Finset.sum_nonneg fun w _ => mul_nonneg
    (div_nonneg (hc.nonneg u w) (le_of_lt (weight_pos hc hdeg u))) (sq_nonneg _)

/-- The two-step kernel dominates the product of its factors. -/
theorem cHeat_mul_le_add {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (a b : ℕ) (x y z : V) :
    cHeat G c a x y * cHeat G c b y z ≤ cHeat G c (a + b) x z := by
  rw [cHeat_add hc hdeg a b x z]
  by_cases hy : y ∈ reach G a x
  · exact Finset.single_le_sum
      (f := fun w => cHeat G c a x w * cHeat G c b w z)
      (fun w _ => mul_nonneg (cHeat_nonneg hc hdeg a x w) (cHeat_nonneg hc hdeg b w z)) hy
  · rw [cHeat_eq_zero_of_notMem_reach a x y hy, zero_mul]
    exact Finset.sum_nonneg fun w _ =>
      mul_nonneg (cHeat_nonneg hc hdeg a x w) (cHeat_nonneg hc hdeg b w z)

theorem cGreen_eq_top_of_recurrent' {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (hG : G.Connected) {o : V}
    (hrec : NetworkRecurrent G c o) (x u : V) : cGreen G c x u = ⊤ := by
  have hoo : (∑' k : ℕ, ENNReal.ofReal (cHeat G c k o o)) = ⊤ := hrec
  obtain ⟨p⟩ := hG.preconnected x o
  obtain ⟨q⟩ := hG.preconnected o u
  have hp : 0 < cHeat G c p.length x o := cHeat_pos_of_walk hc hdeg p
  have hq : 0 < cHeat G c q.length o u := cHeat_pos_of_walk hc hdeg q
  have hstep : ∀ k : ℕ,
      ENNReal.ofReal (cHeat G c p.length x o) * ENNReal.ofReal (cHeat G c k o o)
          * ENNReal.ofReal (cHeat G c q.length o u)
        ≤ ENNReal.ofReal (cHeat G c (p.length + k + q.length) x u) := by
    intro k
    have h1 : cHeat G c p.length x o * cHeat G c (k + q.length) o u
        ≤ cHeat G c (p.length + (k + q.length)) x u :=
      cHeat_mul_le_add hc hdeg p.length (k + q.length) x o u
    have h2 : cHeat G c k o o * cHeat G c q.length o u ≤ cHeat G c (k + q.length) o u :=
      cHeat_mul_le_add hc hdeg k q.length o o u
    have h3 : cHeat G c p.length x o * cHeat G c k o o * cHeat G c q.length o u
        ≤ cHeat G c (p.length + k + q.length) x u := by
      calc cHeat G c p.length x o * cHeat G c k o o * cHeat G c q.length o u
          = cHeat G c p.length x o * (cHeat G c k o o * cHeat G c q.length o u) := by ring
        _ ≤ cHeat G c p.length x o * cHeat G c (k + q.length) o u :=
            mul_le_mul_of_nonneg_left h2 (cHeat_nonneg hc hdeg p.length x o)
        _ ≤ cHeat G c (p.length + (k + q.length)) x u := h1
        _ = cHeat G c (p.length + k + q.length) x u := by
            rw [show p.length + (k + q.length) = p.length + k + q.length by omega]
    have h3e : ENNReal.ofReal (cHeat G c p.length x o * cHeat G c k o o * cHeat G c q.length o u)
        ≤ ENNReal.ofReal (cHeat G c (p.length + k + q.length) x u) :=
      ENNReal.ofReal_le_ofReal h3
    rw [← ENNReal.ofReal_mul (cHeat_nonneg hc hdeg p.length x o)]
    rw [← ENNReal.ofReal_mul (mul_nonneg (cHeat_nonneg hc hdeg p.length x o)
      (cHeat_nonneg hc hdeg k o o))]
    exact h3e
  have hsum : ENNReal.ofReal (cHeat G c p.length x o) * (∑' k : ℕ, ENNReal.ofReal (cHeat G c k o o))
        * ENNReal.ofReal (cHeat G c q.length o u)
      ≤ ∑' k : ℕ, ENNReal.ofReal (cHeat G c (p.length + k + q.length) x u) := by
    calc ENNReal.ofReal (cHeat G c p.length x o) * (∑' k : ℕ, ENNReal.ofReal (cHeat G c k o o))
          * ENNReal.ofReal (cHeat G c q.length o u)
        = (∑' k : ℕ, ENNReal.ofReal (cHeat G c p.length x o) * ENNReal.ofReal (cHeat G c k o o))
          * ENNReal.ofReal (cHeat G c q.length o u) := by rw [ENNReal.tsum_mul_left]
      _ = ∑' k : ℕ, ENNReal.ofReal (cHeat G c p.length x o) * ENNReal.ofReal (cHeat G c k o o)
            * ENNReal.ofReal (cHeat G c q.length o u) := by rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (cHeat G c (p.length + k + q.length) x u) :=
          ENNReal.tsum_le_tsum hstep
  have hle : (∑' k : ℕ, ENNReal.ofReal (cHeat G c (p.length + k + q.length) x u))
      ≤ ∑' k : ℕ, ENNReal.ofReal (cHeat G c k x u) := by
    have h := ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective (p.length + q.length))
      (fun k => ENNReal.ofReal (cHeat G c k x u))
    refine le_trans (le_of_eq ?_) h
    exact tsum_congr fun k => by rw [show p.length + q.length + k = p.length + k + q.length by omega]
  rw [hoo, ENNReal.mul_top (by simpa using (ENNReal.ofReal_pos.mpr hp).ne'),
      ENNReal.top_mul (by simpa using (ENNReal.ofReal_pos.mpr hq).ne')] at hsum
  rw [cGreen_eq_tsum]
  exact top_le_iff.mp (le_trans hsum hle)


/-- On a recurrent network the energy of a bounded harmonic function vanishes. -/
theorem cEnergy_eq_zero_of_recurrent {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (hG : G.Connected) {o : V}
    (hrec : NetworkRecurrent G c o) (f : V → ℝ)
    (hharm : HarmonicOn G c f Set.univ) (hbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (u : V) :
    cEnergy G c f u = 0 := by
  classical
  have hb : ∀ n : ℕ, 0 ≤ ∑ v ∈ reach G n o, cHeat G c n o v * cEnergy G c f v :=
    fun n => Finset.sum_nonneg fun v _ =>
      mul_nonneg (cHeat_nonneg hc hdeg n o v) (cEnergy_nonneg hc hdeg f v)
  have hsum : Summable fun n : ℕ => ∑ v ∈ reach G n o, cHeat G c n o v * cEnergy G c f v :=
    summable_of_sum_range_le hb (fun N => cHeat_energy_sum_le hc hdeg f hharm hbdd N o)
  have hdiv : ¬ Summable fun n : ℕ => cHeat G c n o u :=
    not_summable_cHeat_of_cGreen_eq_top hc hdeg (cGreen_eq_top_of_recurrent' hc hdeg hG hrec o u)
  by_contra hne
  have hle : ∀ n : ℕ, cHeat G c n o u * cEnergy G c f u
      ≤ ∑ v ∈ reach G n o, cHeat G c n o v * cEnergy G c f v := by
    intro n
    by_cases hu : u ∈ reach G n o
    · exact Finset.single_le_sum (fun v _ =>
        mul_nonneg (cHeat_nonneg hc hdeg n o v) (cEnergy_nonneg hc hdeg f v)) hu
    · rw [cHeat_eq_zero_of_notMem_reach n o u hu, zero_mul]
      exact hb n
  have hsum2 : Summable fun n : ℕ => cHeat G c n o u * cEnergy G c f u :=
    Summable.of_nonneg_of_le (fun n =>
      mul_nonneg (cHeat_nonneg hc hdeg n o u) (cEnergy_nonneg hc hdeg f u)) hle hsum
  have : Summable fun n : ℕ => cHeat G c n o u := by
    have h := hsum2.mul_right (cEnergy G c f u)⁻¹
    refine h.congr fun n => ?_
    field_simp
  exact hdiv this


/-- A neighbour of a vertex where the energy vanishes has the same value. -/
theorem eq_of_adj_of_cEnergy_eq_zero {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) {f : V → ℝ} {x : V}
    (h : cEnergy G c f x = 0) {w : V} (hw : G.Adj x w) : f w = f x := by
  rw [cEnergy] at h
  have hnn : ∀ z ∈ G.neighborFinset x,
      0 ≤ (c x z / weight G c x) * (f z - f x) ^ 2 := fun z _ =>
    mul_nonneg (div_nonneg (hc.nonneg x z) (le_of_lt (weight_pos hc hdeg x))) (sq_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h w ((SimpleGraph.mem_neighborFinset G x w).mpr hw)
  have hcpos : 0 < c x w / weight G c x :=
    div_pos (hc.pos hw) (weight_pos hc hdeg x)
  have : (f w - f x) ^ 2 = 0 := by
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact absurd h1 (ne_of_gt hcpos)
    · exact h2
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

theorem eq_const_of_recurrent {c : V → V → ℝ} (hc : IsCond G c)
    (hdeg : ∀ v : V, 0 < G.degree v) (hG : G.Connected) {o : V}
    (hrec : NetworkRecurrent G c o) (f : V → ℝ)
    (hharm : HarmonicOn G c f Set.univ) (hbdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    ∃ a : ℝ, ∀ x, f x = a := by
  refine ⟨f o, fun x => ?_⟩
  have key : ∀ y, G.Reachable x y → f x = f y := by
    intro y hxy
    obtain ⟨p⟩ := hxy
    induction p with
    | nil => rfl
    | cons hab tail ih =>
        rename_i a b c
        have hz := cEnergy_eq_zero_of_recurrent hc hdeg hG hrec f hharm hbdd a
        have h1 : f b = f a := eq_of_adj_of_cEnergy_eq_zero hc hdeg hz hab
        rw [← h1]
        exact ih
  exact key o (hG.preconnected x o)


end UCPlanar.Support
