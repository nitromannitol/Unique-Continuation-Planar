/-
Recurrence of a periodic network, and the bounded Liouville theorem.

A connected, locally finite graph with a rank-two periodic coordinate
realization and periodic conductances is recurrent: the boxes of lattice
coordinates have boundary cuts whose total conductance grows at most linearly
in the radius, so the reciprocal conductance sum diverges and the
Nash-Williams criterion applies.  On a recurrent network every bounded
harmonic function is constant.
-/
import UCPlanar.Support.LiouKilled
import UCPlanar.Support.Periodic
import LatticeProb.Network.Series
import Mathlib.Analysis.Normed.Group.Constructions

open scoped Classical ENNReal

namespace UCPlanar.Support

open LatticeProb.Network LatticeProb.Graph

variable {V : Type*}

/-- The harmonic series over the shifted naturals is unbounded. -/
theorem harmonic_unbounded (B : ℝ) :
    ∃ T : ℕ, B ≤ ∑ t ∈ Finset.range T, (1 : ℝ) / (t + 1) := by
  have h1 : ¬ Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 : ℝ) :=
    Real.summable_one_div_nat_rpow.not.mpr (by norm_num)
  simp only [Real.rpow_one] at h1
  have h2 : ¬ Summable fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) :=
    (summable_nat_add_iff 1).not.mpr h1
  have h3 : (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      = (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := by
    funext n
    push_cast
    ring
  rw [h3] at h2
  have hnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := fun n => by positivity
  have hT := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp h2
  obtain ⟨T, hT⟩ := (hT.eventually (Filter.eventually_ge_atTop B)).exists
  exact ⟨T, hT⟩

/-- A walk that starts inside a set and ends outside it crosses its boundary. -/
theorem _root_.SimpleGraph.Walk.exists_cut_edge {G : SimpleGraph V} {S : Finset V} {u v : V}
    (p : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  induction p with
  | nil => exact absurd hu hv
  | @cons a b w hab p ih =>
    by_cases hb : b ∈ S
    · exact ih hb hv
    · exact ⟨a, b, hu, hb, hab⟩

end UCPlanar.Support

namespace UCPlanar.PeriodicGraph

open LatticeProb.Network LatticeProb.Graph UCPlanar.Support

variable {V : Type*} (P : UCPlanar.PeriodicGraph V)

/-- Representatives together with a chosen basepoint. -/
noncomputable def baseReps (o : V) : Finset V :=
  insert o P.representatives

theorem covers_baseReps (o : V) (x : V) :
    ∃ v ∈ P.baseReps o, ∃ a, P.shift a v = x := by
  obtain ⟨v, hv, a, ha⟩ := P.covers x
  exact ⟨v, Finset.mem_insert_of_mem hv, a, ha⟩

/-- The shift orbit of a vertex is a faithful copy of the lattice. -/
theorem shift_injective_at (v : V) :
    Function.Injective (fun a : LatticeProb.Site 2 => P.shift a v) := by
  intro a b hab
  have hpos := congrArg P.pos hab
  rw [P.pos_shift, P.pos_shift] at hpos
  replace hpos := P.period.injective (add_left_cancel hpos)
  funext i
  exact Int.cast_injective (congrFun hpos i)

theorem shift_injective (a : LatticeProb.Site 2) : Function.Injective (P.shift a) := by
  have h : Function.LeftInverse (P.shift (-a)) (P.shift a) := fun x => by
    rw [← P.shift_add, neg_add_cancel, P.shift_zero]
  exact h.injective

/-- The constant-coordinate embedding of `ℤ` into the lattice. -/
theorem constSite_injective :
    Function.Injective (fun n : ℤ => fun _ : Fin 2 => n) :=
  fun _ _ h => congrFun h 0

include P in
/-- A periodic graph on a nonempty vertex type is infinite. -/
theorem infinite (v : V) : Infinite V :=
  Infinite.of_injective _ ((P.shift_injective_at v).comp constSite_injective)

/-- The box of lattice coordinates of sup-norm at most `k`. -/
noncomputable def coordBox (k : ℕ) : Finset (LatticeProb.Site 2) :=
  Fintype.piFinset fun _ : Fin 2 => Finset.Icc (-(k : ℤ)) (k : ℤ)

theorem mem_coordBox {k : ℕ} {a : LatticeProb.Site 2} :
    a ∈ coordBox k ↔ ∀ i, |a i| ≤ (k : ℤ) := by
  simp only [coordBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem coordBox_mono {k k' : ℕ} (h : k ≤ k') : coordBox k ⊆ coordBox k' := by
  intro a ha
  rw [mem_coordBox] at ha ⊢
  intro i
  exact le_trans (ha i) (by exact_mod_cast h)

theorem card_coordBox (k : ℕ) : (coordBox k).card = (2 * k + 1) ^ 2 := by
  rw [coordBox, Fintype.piFinset, Finset.card_map, Finset.card_pi, Fin.prod_univ_two,
    Int.card_Icc]
  have e : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
  rw [e]
  ring

/-- The vertices whose lattice coordinate lies in the box of radius `k`. -/
noncomputable def boxSet (o : V) (k : ℕ) : Finset V :=
  (P.baseReps o).biUnion fun v => (coordBox k).image fun a => P.shift a v

theorem mem_boxSet {o : V} {k : ℕ} {y : V} :
    y ∈ P.boxSet o k ↔ ∃ v ∈ P.baseReps o, ∃ a ∈ coordBox k, P.shift a v = y := by
  simp only [boxSet, Finset.mem_biUnion, Finset.mem_image]

theorem mem_boxSet_self (o : V) (k : ℕ) : o ∈ P.boxSet o k := by
  rw [mem_boxSet]
  refine ⟨o, Finset.mem_insert_self o _, 0, ?_, P.shift_zero o⟩
  rw [mem_coordBox]
  intro i
  simp

theorem boxSet_mono {o : V} {k k' : ℕ} (h : k ≤ k') : P.boxSet o k ⊆ P.boxSet o k' := by
  intro x hx
  rw [mem_boxSet] at hx ⊢
  obtain ⟨v, hv, a, ha, rfl⟩ := hx
  exact ⟨v, hv, a, coordBox_mono h ha, rfl⟩

theorem card_boxSet_le (o : V) (k : ℕ) :
    (P.boxSet o k).card ≤ (P.baseReps o).card * (2 * k + 1) ^ 2 := by
  rw [boxSet]
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum fun v _ => Finset.card_image_le).trans ?_
  rw [card_coordBox, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]

/-! ### The constants of the periodic structure -/

/-- The largest positional length of an edge leaving a representative. -/
noncomputable def edgeSpan (o : V) : ℝ :=
  (((P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
    ‖P.pos z - P.pos v‖₊) : NNReal)

theorem norm_pos_sub_le_edgeSpan {o v z : V}
    (hv : v ∈ P.baseReps o) (hz : P.graph.Adj v z) :
    ‖P.pos z - P.pos v‖ ≤ P.edgeSpan o := by
  have hz' : z ∈ P.graph.neighborFinset v :=
    (SimpleGraph.mem_neighborFinset _ _ _).mpr hz
  have h1 : ‖P.pos z - P.pos v‖₊
      ≤ (P.graph.neighborFinset v).sup fun z => ‖P.pos z - P.pos v‖₊ :=
    Finset.le_sup (f := fun z => ‖P.pos z - P.pos v‖₊) hz'
  have h2 : ((P.graph.neighborFinset v).sup fun z => ‖P.pos z - P.pos v‖₊)
      ≤ (P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
        ‖P.pos z - P.pos v‖₊ :=
    Finset.le_sup (f := fun v => (P.graph.neighborFinset v).sup fun z =>
      ‖P.pos z - P.pos v‖₊) hv
  show (‖P.pos z - P.pos v‖₊ : ℝ) ≤
    (((P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
      ‖P.pos z - P.pos v‖₊) : NNReal)
  exact_mod_cast le_trans h1 h2

/-- The largest positional norm of a representative. -/
noncomputable def repPos (o : V) : ℝ :=
  (((P.baseReps o).sup fun v => ‖P.pos v‖₊) : NNReal)

theorem norm_pos_le_repPos {o v : V} (hv : v ∈ P.baseReps o) :
    ‖P.pos v‖ ≤ P.repPos o := by
  show (‖P.pos v‖₊ : ℝ) ≤ (((P.baseReps o).sup fun v => ‖P.pos v‖₊) : NNReal)
  exact_mod_cast Finset.le_sup (f := fun v => ‖P.pos v‖₊) hv

/-- The matrix entries of the inverse period in the standard basis. -/
noncomputable def periodInvEntry (j i : Fin 2) : ℝ :=
  P.period.symm (Pi.single i (1 : ℝ)) j

/-- A bound on the operator norm of the inverse period. -/
noncomputable def periodInvBound : ℝ :=
  ∑ j : Fin 2, ∑ i : Fin 2, |P.periodInvEntry j i|

theorem periodInvBound_nonneg : 0 ≤ P.periodInvBound :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_periodInvEntry_le (j i : Fin 2) :
    |P.periodInvEntry j i| ≤ P.periodInvBound :=
  le_trans
    (Finset.single_le_sum (f := fun i' => |P.periodInvEntry j i'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    (Finset.single_le_sum (f := fun j' => ∑ i' : Fin 2, |P.periodInvEntry j' i'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j))

theorem plane_eq_sum_single (u : UCPlanar.Plane) :
    u = u 0 • Pi.single (0 : Fin 2) (1 : ℝ) + u 1 • Pi.single (1 : Fin 2) (1 : ℝ) := by
  funext i
  fin_cases i <;> simp

theorem abs_periodInv_apply_le (u : UCPlanar.Plane) (j : Fin 2) :
    |(P.period.symm u) j| ≤ P.periodInvBound * (|u 0| + |u 1|) := by
  have key : (P.period.symm u) j
      = u 0 * P.periodInvEntry j 0 + u 1 * P.periodInvEntry j 1 := by
    have hdecomp : P.period.symm u = u 0 • P.period.symm (Pi.single (0 : Fin 2) (1 : ℝ))
        + u 1 • P.period.symm (Pi.single (1 : Fin 2) (1 : ℝ)) := by
      conv_lhs => rw [plane_eq_sum_single u]
      rw [map_add, map_smul, map_smul]
    rw [hdecomp]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, periodInvEntry]
  rw [key]
  have h0 : |u 0 * P.periodInvEntry j 0| ≤ P.periodInvBound * |u 0| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (P.abs_periodInvEntry_le j 0)
      (abs_nonneg _)).trans_eq (mul_comm _ _)
  have h1 : |u 1 * P.periodInvEntry j 1| ≤ P.periodInvBound * |u 1| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (P.abs_periodInvEntry_le j 1)
      (abs_nonneg _)).trans_eq (mul_comm _ _)
  calc |u 0 * P.periodInvEntry j 0 + u 1 * P.periodInvEntry j 1|
      ≤ |u 0 * P.periodInvEntry j 0| + |u 1 * P.periodInvEntry j 1| :=
        abs_add_le _ _
    _ ≤ P.periodInvBound * |u 0| + P.periodInvBound * |u 1| := add_le_add h0 h1
    _ = P.periodInvBound * (|u 0| + |u 1|) := by ring

/-- The largest jump of the lattice coordinate along an edge. -/
noncomputable def jumpBound (o : V) : ℝ :=
  P.periodInvBound * (2 * (P.edgeSpan o + 2 * P.repPos o))

theorem jumpBound_nonneg (o : V) : 0 ≤ P.jumpBound o :=
  mul_nonneg P.periodInvBound_nonneg
    (mul_nonneg (by norm_num) (add_nonneg (NNReal.coe_nonneg _)
      (mul_nonneg (by norm_num) (NNReal.coe_nonneg _))))

/-- The spacing between successive cutsets: strictly positive, and at least
the coordinate jump of a single edge. -/
noncomputable def spacing (o : V) : ℕ := max 1 ⌈P.jumpBound o⌉₊

theorem jumpBound_le_spacing (o : V) : P.jumpBound o ≤ (P.spacing o : ℝ) :=
  le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 1 _)

theorem one_le_spacing (o : V) : 1 ≤ P.spacing o := le_max_left _ _

/-- The lattice coordinates of the endpoints of an edge differ by at most the
jump bound. -/
theorem abs_coord_sub_le_jumpBound {o v w : V}
    (hv : v ∈ P.baseReps o) (hw : w ∈ P.baseReps o)
    {a b : LatticeProb.Site 2} (h : P.graph.Adj (P.shift a v) (P.shift b w))
    (j : Fin 2) :
    |((b - a) j : ℝ)| ≤ P.jumpBound o := by
  have hbg : P.shift b w = P.shift a (P.shift (b - a) w) := by
    rw [← P.shift_add, add_sub_cancel]
  rw [hbg] at h
  have hadj : P.graph.Adj v (P.shift (b - a) w) := (P.shift_adj a v _).mp h
  have hposz : P.pos (P.shift (b - a) w) = P.pos w + P.period (fun i => ((b - a) i : ℝ)) :=
    P.pos_shift (b - a) w
  have hper : P.period (fun i => ((b - a) i : ℝ))
      = P.pos (P.shift (b - a) w) - P.pos w := by
    rw [hposz]; abel
  have hnorm : ‖P.period (fun i => ((b - a) i : ℝ))‖ ≤ P.edgeSpan o + 2 * P.repPos o := by
    rw [hper]
    calc ‖P.pos (P.shift (b - a) w) - P.pos w‖
        ≤ ‖P.pos (P.shift (b - a) w) - P.pos v‖ + ‖P.pos v - P.pos w‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ P.edgeSpan o + (P.repPos o + P.repPos o) := by
          refine add_le_add (P.norm_pos_sub_le_edgeSpan hv hadj) ?_
          exact (norm_sub_le _ _).trans
            (add_le_add (P.norm_pos_le_repPos hv) (P.norm_pos_le_repPos hw))
      _ = P.edgeSpan o + 2 * P.repPos o := by ring
  have hcomp : ∀ i, |(P.period (fun i => ((b - a) i : ℝ))) i|
      ≤ P.edgeSpan o + 2 * P.repPos o :=
    fun i => le_trans
      (by simpa using norm_le_pi_norm (P.period fun i => ((b - a) i : ℝ)) i) hnorm
  have hbound := P.abs_periodInv_apply_le (P.period fun i => ((b - a) i : ℝ)) j
  rw [LinearEquiv.symm_apply_apply] at hbound
  have hsum : |(P.period (fun i => ((b - a) i : ℝ))) 0|
        + |(P.period (fun i => ((b - a) i : ℝ))) 1|
      ≤ 2 * (P.edgeSpan o + 2 * P.repPos o) := by
    rw [show (2 * (P.edgeSpan o + 2 * P.repPos o))
        = (P.edgeSpan o + 2 * P.repPos o) + (P.edgeSpan o + 2 * P.repPos o) from by ring]
    exact add_le_add (hcomp 0) (hcomp 1)
  exact le_trans hbound (mul_le_mul_of_nonneg_left hsum P.periodInvBound_nonneg)

/-- One step across an edge moves the lattice coordinate by less than one
spacing, so the boxes absorb their outer neighbour shell. -/
theorem shift_mem_boxSet_add_spacing {o x y : V} {k : ℕ}
    (hx : x ∈ P.boxSet o k) (hxy : P.graph.Adj x y) :
    y ∈ P.boxSet o (k + P.spacing o) := by
  rw [mem_boxSet] at hx
  obtain ⟨v, hv, a, ha, rfl⟩ := hx
  obtain ⟨w, hw, b, rfl⟩ := P.covers_baseReps o y
  rw [mem_boxSet]
  refine ⟨w, hw, b, ?_, rfl⟩
  rw [mem_coordBox] at ha ⊢
  intro j
  have hjump := P.abs_coord_sub_le_jumpBound hv hw hxy j
  have hb : |(b j : ℝ)| ≤ (k : ℝ) + P.spacing o := by
    have h1 : (b j : ℝ) = (a j : ℝ) + ((b - a) j : ℝ) := by
      rw [Pi.sub_apply, Int.cast_sub]
      ring
    rw [h1]
    refine (abs_add_le _ _).trans (add_le_add ?_ (le_trans hjump (P.jumpBound_le_spacing o)))
    rw [← Int.cast_abs]
    exact_mod_cast ha j
  rw [abs_le] at hb ⊢
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

/-! ### Degrees and conductances are bounded -/

/-- The largest degree of a representative. -/
noncomputable def maxDegree (o : V) : ℕ :=
  (P.baseReps o).sup fun v => P.graph.degree v

theorem neighborFinset_shift (a : LatticeProb.Site 2) (v : V) :
    P.graph.neighborFinset (P.shift a v) = (P.graph.neighborFinset v).image (P.shift a) := by
  ext y
  constructor
  · intro h
    rw [SimpleGraph.mem_neighborFinset] at h
    rw [Finset.mem_image]
    have hya : P.shift a (P.shift (-a) y) = y := by
      rw [← P.shift_add, add_neg_cancel, P.shift_zero]
    rw [← hya] at h
    exact ⟨P.shift (-a) y, (SimpleGraph.mem_neighborFinset _ _ _).mpr
      ((P.shift_adj a _ _).mp h), hya⟩
  · intro h
    rw [Finset.mem_image] at h
    obtain ⟨z, hz, rfl⟩ := h
    rw [SimpleGraph.mem_neighborFinset] at hz ⊢
    exact (P.shift_adj a _ _).mpr hz

theorem degree_shift (a : LatticeProb.Site 2) (v : V) :
    P.graph.degree (P.shift a v) = P.graph.degree v := by
  simp only [SimpleGraph.degree]
  rw [P.neighborFinset_shift]
  exact Finset.card_image_of_injective _ (P.shift_injective a)

theorem degree_le_maxDegree (o : V) (x : V) :
    P.graph.degree x ≤ P.maxDegree o := by
  obtain ⟨v, hv, a, rfl⟩ := P.covers_baseReps o x
  rw [P.degree_shift]
  exact Finset.le_sup (f := fun v => P.graph.degree v) hv

theorem maxDegree_pos (o : V) [Infinite V] : 1 ≤ P.maxDegree o :=
  le_trans (LatticeProb.Graph.degree_pos P.connected o)
    (Finset.le_sup (f := fun v => P.graph.degree v) (Finset.mem_insert_self o _))

/-- The largest conductance of an edge leaving a representative. -/
noncomputable def maxCond (o : V) (c : V → V → ℝ) : ℝ :=
  (((P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
    (c v z).toNNReal) : NNReal)

theorem cond_le_maxCond {o : V} {c : V → V → ℝ}
    (hc : IsCond P.graph c) (hp : P.PeriodicConductance c) {x y : V}
    (hxy : P.graph.Adj x y) :
    c x y ≤ P.maxCond o c := by
  obtain ⟨v, hv, a, rfl⟩ := P.covers_baseReps o x
  have hya : P.shift a (P.shift (-a) y) = y := by
    rw [← P.shift_add, add_neg_cancel, P.shift_zero]
  have e1 : c (P.shift a v) y = c v (P.shift (-a) y) := by
    have h1 := hp (-a) (P.shift a v) y
    rw [← P.shift_add, neg_add_cancel, P.shift_zero] at h1
    exact h1.symm
  rw [e1]
  have hz : P.shift (-a) y ∈ P.graph.neighborFinset v := by
    rw [SimpleGraph.mem_neighborFinset]
    have hxy' : P.graph.Adj (P.shift a v) (P.shift a (P.shift (-a) y)) := by
      rw [hya]; exact hxy
    exact (P.shift_adj a _ _).mp hxy'
  have hpos : 0 ≤ c v (P.shift (-a) y) :=
    le_of_lt (hc.pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hz))
  have h1 : (c v (P.shift (-a) y)).toNNReal
      ≤ (P.graph.neighborFinset v).sup fun z => (c v z).toNNReal :=
    Finset.le_sup (f := fun z => (c v z).toNNReal) hz
  have h2 : ((P.graph.neighborFinset v).sup fun z => (c v z).toNNReal)
      ≤ (P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
        (c v z).toNNReal :=
    Finset.le_sup (f := fun v => (P.graph.neighborFinset v).sup fun z =>
      (c v z).toNNReal) hv
  show c v (P.shift (-a) y) ≤
    (((P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
      (c v z).toNNReal) : NNReal)
  rw [show c v (P.shift (-a) y) = ((c v (P.shift (-a) y)).toNNReal : ℝ) from
    (Real.coe_toNNReal _ hpos).symm]
  exact_mod_cast le_trans h1 h2

theorem maxCond_pos (o : V) [Infinite V] {c : V → V → ℝ} (hc : IsCond P.graph c) :
    0 < P.maxCond o c := by
  have h1 : 0 < P.graph.degree o := LatticeProb.Graph.degree_pos P.connected o
  obtain ⟨w, hw⟩ := (P.graph.degree_pos_iff_exists_adj o).mp h1
  have hz : w ∈ P.graph.neighborFinset o := (SimpleGraph.mem_neighborFinset _ _ _).mpr hw
  have hpos : 0 < c o w := hc.pos hw
  have hle1 : (c o w).toNNReal ≤ (P.graph.neighborFinset o).sup fun z => (c o z).toNNReal :=
    Finset.le_sup (f := fun z => (c o z).toNNReal) hz
  have hle2 : ((P.graph.neighborFinset o).sup fun z => (c o z).toNNReal)
      ≤ (P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
        (c v z).toNNReal :=
    Finset.le_sup (f := fun v => (P.graph.neighborFinset v).sup fun z =>
      (c v z).toNNReal) (Finset.mem_insert_self o _)
  have h3 := lt_of_lt_of_le (Real.toNNReal_pos.mpr hpos) (le_trans hle1 hle2)
  show (0 : ℝ) < (((P.baseReps o).sup fun v => (P.graph.neighborFinset v).sup fun z =>
    (c v z).toNNReal) : NNReal)
  exact_mod_cast h3

/-! ### Boundary cuts of the coordinate boxes -/

/-- The inside endpoint of a boundary edge of a box lies in the outer shell of
width one spacing. -/
theorem cutPairs_mem_shell {o : V} {k : ℕ} (hk : P.spacing o ≤ k)
    {p : V × V} (hp : p ∈ cutPairs P.graph (P.boxSet o k)) :
    p.1 ∈ P.boxSet o k \ P.boxSet o (k - P.spacing o) := by
  obtain ⟨h1, h2, h3⟩ := mem_cutPairs.mp hp
  rw [Finset.mem_sdiff]
  refine ⟨h1, fun h => ?_⟩
  have h4 := P.shift_mem_boxSet_add_spacing h h3
  rw [Nat.sub_add_cancel hk] at h4
  exact h2 h4

/-- The boundary cut of a coordinate box has cardinality at most the maximal
degree times the area of the outer shell. -/
theorem card_cutPairs_le {o : V} {k : ℕ} (hk : P.spacing o ≤ k) :
    (cutPairs P.graph (P.boxSet o k)).card
      ≤ P.maxDegree o * ((P.baseReps o).card *
          ((2 * k + 1) ^ 2 - (2 * (k - P.spacing o) + 1) ^ 2)) := by
  classical
  set shell := P.boxSet o k \ P.boxSet o (k - P.spacing o) with hshell
  have hsub : cutPairs P.graph (P.boxSet o k)
      ⊆ shell.biUnion fun x => (P.graph.neighborFinset x).image fun y => (x, y) := by
    intro p hp
    obtain ⟨-, -, h3⟩ := mem_cutPairs.mp hp
    rw [Finset.mem_biUnion]
    refine ⟨p.1, P.cutPairs_mem_shell hk hp, ?_⟩
    rw [Finset.mem_image]
    exact ⟨p.2, (SimpleGraph.mem_neighborFinset _ _ _).mpr h3, rfl⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  have hcard : ∀ x ∈ shell,
      ((P.graph.neighborFinset x).image fun y => (x, y)).card = P.graph.degree x := by
    intro x _
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
    rfl
  refine (Finset.sum_le_sum fun x hx => le_of_eq (hcard x hx)).trans ?_
  refine (Finset.sum_le_sum fun x _ => P.degree_le_maxDegree o x).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hshell_card : shell.card
      ≤ (P.baseReps o).card * ((2 * k + 1) ^ 2 - (2 * (k - P.spacing o) + 1) ^ 2) := by
    have hsub2 : shell ⊆ (P.baseReps o).biUnion fun v =>
        (coordBox k \ coordBox (k - P.spacing o)).image fun a => P.shift a v := by
      intro x hx
      rw [hshell, Finset.mem_sdiff] at hx
      obtain ⟨hxk, hxks⟩ := hx
      rw [mem_boxSet] at hxk
      obtain ⟨v, hv, a, ha, rfl⟩ := hxk
      rw [Finset.mem_biUnion]
      refine ⟨v, hv, ?_⟩
      rw [Finset.mem_image]
      refine ⟨a, ?_, rfl⟩
      rw [Finset.mem_sdiff]
      refine ⟨ha, fun haks => hxks (P.mem_boxSet.mpr ⟨v, hv, a, haks, rfl⟩)⟩
    refine (Finset.card_le_card hsub2).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun v _ => Finset.card_image_le).trans ?_
    rw [Finset.card_sdiff_of_subset (coordBox_mono (Nat.sub_le _ _)), card_coordBox,
      card_coordBox, Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  rw [Nat.cast_id, mul_comm]
  exact mul_le_mul_right hshell_card (P.maxDegree o)

/-- The total conductance of the boundary cut of a coordinate box grows at most
linearly in the radius, with an explicit constant. -/
theorem sum_cond_cutPairs_le {o : V} {c : V → V → ℝ} (hc : IsCond P.graph c)
    (hp : P.PeriodicConductance c) {k : ℕ} (hk : P.spacing o ≤ k) :
    ∑ p ∈ cutPairs P.graph (P.boxSet o k), c p.1 p.2
      ≤ P.maxCond o c * (((P.maxDegree o * ((P.baseReps o).card *
          ((2 * k + 1) ^ 2 - (2 * (k - P.spacing o) + 1) ^ 2))) : ℕ) : ℝ) := by
  refine (Finset.sum_le_sum (g := fun _ => P.maxCond o c) fun p hp' =>
    P.cond_le_maxCond (o := o) hc hp (mem_cutPairs.mp hp').2.2).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul,
    mul_comm ((cutPairs P.graph (P.boxSet o k)).card : ℝ) (P.maxCond o c)]
  refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
  exact_mod_cast P.card_cutPairs_le hk

/-- The boundary cut of a coordinate box has positive total conductance. -/
theorem sum_cond_cutPairs_pos {o : V} {c : V → V → ℝ} (hc : IsCond P.graph c) (k : ℕ) :
    0 < ∑ p ∈ cutPairs P.graph (P.boxSet o k), c p.1 p.2 := by
  haveI := P.infinite o
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (P.boxSet o k)
  obtain ⟨w⟩ := P.connected.preconnected o z
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    w.exists_cut_edge (P.mem_boxSet_self o k) hz
  have hp : (x, y) ∈ cutPairs P.graph (P.boxSet o k) := mem_cutPairs.mpr ⟨hx, hy, hxy⟩
  refine lt_of_lt_of_le (hc.pos hxy) ?_
  exact Finset.single_le_sum (f := fun p => c p.1 p.2)
    (fun q hq => le_of_lt (hc.pos (mem_cutPairs.mp hq).2.2)) hp

/-- Boundary cuts of boxes at distinct spacing multiples are disjoint: an edge
leaving the inner box lands inside the next box. -/
theorem disjoint_cutPairs {o : V} {t t' : ℕ} (h : t < t') :
    Disjoint (cutPairs P.graph (P.boxSet o (P.spacing o * (t + 1))))
      (cutPairs P.graph (P.boxSet o (P.spacing o * (t' + 1)))) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  obtain ⟨h1a, -, h1c⟩ := mem_cutPairs.mp hp1
  obtain ⟨-, h2b, -⟩ := mem_cutPairs.mp hp2
  have h3 : p.2 ∈ P.boxSet o (P.spacing o * (t + 1) + P.spacing o) :=
    P.shift_mem_boxSet_add_spacing h1a h1c
  have e : P.spacing o * (t + 1) + P.spacing o = P.spacing o * (t + 2) := by ring
  rw [e] at h3
  have hle : P.spacing o * (t + 2) ≤ P.spacing o * (t' + 1) :=
    mul_le_mul_right (by omega : t + 2 ≤ t' + 1) _
  exact h2b (P.boxSet_mono hle h3)

/-- Each boundary cut at a spacing multiple carries a unit of the Dirichlet
current. -/
theorem one_le_sum_current_cutPairs {o : V} {c : V → V → ℝ} (hc : IsCond P.graph c)
    [Infinite V] (C : Finset V) (ho : o ∈ C) {k : ℕ} (hkC : P.boxSet o k ⊆ C) :
    1 ≤ ∑ p ∈ cutPairs P.graph (P.boxSet o k),
      current P.graph c (bvpGreen P.graph P.connected hc C o ho) p.1 p.2 := by
  rw [← flux_eq_sum_cutPairs]
  refine le_of_eq (flux_eq_one hc _ _ (P.mem_boxSet_self o k) ?_).symm
  intro x hx
  rw [bvpGreen_laplacian P.connected hc C ho (hkC hx)]
  by_cases hxo : x = o <;> simp [hxo]

/-! ### Recurrence by Nash-Williams -/

/-- A periodic network is recurrent: the boundary cuts at multiples of the
spacing are disjoint, each carries a unit of the Dirichlet current, and their
total conductance grows at most linearly, so the reciprocal sum diverges. -/
theorem networkRecurrent (o : V) {c : V → V → ℝ} (hc : IsCond P.graph c)
    (hp : P.PeriodicConductance c) : NetworkRecurrent P.graph c o := by
  haveI := P.infinite o
  have hdeg : ∀ v : V, 0 < P.graph.degree v :=
    fun v => LatticeProb.Graph.degree_pos P.connected v
  set s := P.spacing o with hs
  have hs1 : 1 ≤ s := P.one_le_spacing o
  have hs0 : 0 < s := hs1
  have hs2 : s ≤ s ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_of_pos_right s hs0
  refine networkRecurrent_of_forall_exists P.connected hc hdeg o fun B => ?_
  set A' : ℝ := P.maxCond o c * ((P.maxDegree o : ℝ) * ((P.baseReps o).card : ℝ)
    * (8 * (s : ℝ) ^ 2)) with hA'
  have hA'pos : 0 < A' := by
    rw [hA']
    exact mul_pos (P.maxCond_pos o hc)
      (mul_pos
        (mul_pos (Nat.cast_pos.mpr (P.maxDegree_pos o))
          (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨o, Finset.mem_insert_self o _⟩)))
        (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hs0) 2)))
  have hW : 0 < weight P.graph c o := weight_pos hc hdeg o
  have hΔ : ∀ t : ℕ, (2 * (s * (t + 1)) + 1) ^ 2 - (2 * (s * (t + 1) - s) + 1) ^ 2
      ≤ 8 * s ^ 2 * (t + 1) := by
    intro t
    have e1 : s * (t + 1) - s = s * t := by rw [Nat.mul_succ, Nat.add_sub_cancel]
    have e2 : 2 * (s * (t + 1)) + 1 = (2 * (s * t) + 1) + 2 * s := by
      rw [Nat.mul_succ]; ring
    rw [e1, e2]
    have e3 : (2 * (s * t) + 1 + 2 * s) ^ 2
        = (2 * (s * t) + 1) ^ 2 + (4 * s * (2 * (s * t) + 1) + 4 * s ^ 2) := by ring
    rw [e3, Nat.add_sub_cancel_left]
    calc 4 * s * (2 * (s * t) + 1) + 4 * s ^ 2
        = (8 * s ^ 2 * t + 4 * s ^ 2) + 4 * s := by ring
      _ ≤ (8 * s ^ 2 * t + 4 * s ^ 2) + 4 * s ^ 2 :=
          add_le_add_right (mul_le_mul_right hs2 4) _
      _ = 8 * s ^ 2 * (t + 1) := by ring
  have hCsum : ∀ t : ℕ, ∑ p ∈ cutPairs P.graph (P.boxSet o (s * (t + 1))), c p.1 p.2
      ≤ A' * ((t : ℝ) + 1) := by
    intro t
    calc ∑ p ∈ cutPairs P.graph (P.boxSet o (s * (t + 1))), c p.1 p.2
        ≤ P.maxCond o c * (((P.maxDegree o * ((P.baseReps o).card *
            ((2 * (s * (t + 1)) + 1) ^ 2 - (2 * (s * (t + 1) - s) + 1) ^ 2))) : ℕ) : ℝ) :=
          P.sum_cond_cutPairs_le hc hp (Nat.le_mul_of_pos_right s (Nat.succ_pos t))
      _ ≤ P.maxCond o c * (((P.maxDegree o * ((P.baseReps o).card *
            (8 * s ^ 2 * (t + 1)))) : ℕ) : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
          exact Nat.cast_le.mpr (mul_le_mul (le_refl _)
            (mul_le_mul (le_refl _) (hΔ t) (Nat.zero_le _) (Nat.zero_le _))
            (Nat.zero_le _) (Nat.zero_le _))
      _ = A' * ((t : ℝ) + 1) := by rw [hA']; push_cast; ring
  obtain ⟨T, hT⟩ := harmonic_unbounded (B * (2 * A') / weight P.graph c o)
  refine ⟨P.boxSet o (s * T), P.mem_boxSet_self o _, ?_⟩
  set g := bvpGreen P.graph P.connected hc (P.boxSet o (s * T)) o
    (P.mem_boxSet_self o _) with hg
  have hkC : ∀ t ∈ Finset.range T, P.boxSet o (s * (t + 1)) ⊆ P.boxSet o (s * T) := by
    intro t ht
    have htT : t + 1 ≤ T := by have h := Finset.mem_range.mp ht; omega
    exact P.boxSet_mono (mul_le_mul_right htT s)
  have hsub : ∀ t ∈ Finset.range T, cutPairs P.graph (P.boxSet o (s * (t + 1)))
      ⊆ pairs P.graph (nbhd P.graph (P.boxSet o (s * T))) := fun t ht =>
    cutPairs_subset_pairs (hkC t ht)
  have hdisj : ((Finset.range T : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun t => cutPairs P.graph (P.boxSet o (s * (t + 1))) := by
    intro t _ t' _ htt'
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne htt' with h | h
    · exact P.disjoint_cutPairs h
    · exact (P.disjoint_cutPairs h).symm
  have hcut : ∀ t ∈ Finset.range T,
      1 ≤ ∑ p ∈ cutPairs P.graph (P.boxSet o (s * (t + 1))), current P.graph c g p.1 p.2 :=
    fun t ht => P.one_le_sum_current_cutPairs hc (P.boxSet o (s * T))
      (P.mem_boxSet_self o _) (hkC t ht)
  have hnw := cutset_sum_le_two_mul_bvpGreen P.connected hc (P.boxSet o (s * T))
    (P.mem_boxSet_self o _) (Finset.range T)
    (fun t => cutPairs P.graph (P.boxSet o (s * (t + 1)))) hsub hdisj hcut
  have hrecip : ∀ t : ℕ, (1 / A') * (1 / ((t : ℝ) + 1))
      ≤ 1 / (∑ p ∈ cutPairs P.graph (P.boxSet o (s * (t + 1))), c p.1 p.2) := by
    intro t
    have hpos := P.sum_cond_cutPairs_pos (o := o) hc (s * (t + 1))
    rw [div_mul_div_comm, one_mul]
    exact one_div_le_one_div_of_le hpos (hCsum t)
  have hsum : (1 / A') * (∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1)) ≤ 2 * g o := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum fun t _ => hrecip t).trans hnw
  have h2 : (∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1)) ≤ A' * (2 * g o) := by
    have h3 := mul_le_mul_of_nonneg_left hsum (le_of_lt hA'pos)
    rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hA'pos), one_mul] at h3
    exact h3
  have hchain : B * (2 * A') / weight P.graph c o ≤ 2 * A' * g o :=
    le_trans hT (le_trans h2 (le_of_eq (by ring)))
  have hBW : B * (2 * A') ≤ (2 * A' * g o) * weight P.graph c o :=
    (div_le_iff₀ hW).mp hchain
  refine (mul_le_mul_iff_left₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hA'pos)).mp ?_
  calc B * (2 * A') ≤ 2 * A' * g o * weight P.graph c o := hBW
    _ = (weight P.graph c o * g o) * (2 * A') := by ring

end UCPlanar.PeriodicGraph

namespace UCPlanar.Support

open LatticeProb.Network LatticeProb.Graph

/-- The bounded Liouville theorem for a periodic network: a harmonic function
bounded on the whole graph is constant.  The network is recurrent (Nash-Williams
applied to the boundary cuts of the coordinate boxes), and on a recurrent network
every bounded harmonic function is constant. -/
theorem boundedLiouville_periodic {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : IsCond P.graph c) (hp : P.PeriodicConductance c) :
    ∀ f : V → ℝ, HarmonicOn P.graph c f Set.univ →
      (∃ M : ℝ, ∀ x, |f x| ≤ M) → ∃ a : ℝ, ∀ x, f x = a := by
  intro f hf hbdd
  by_cases hV : Nonempty V
  · obtain ⟨o⟩ := hV
    haveI := P.infinite o
    exact eq_const_of_recurrent hc (fun v => LatticeProb.Graph.degree_pos P.connected v)
      P.connected (P.networkRecurrent o hc hp) f hf hbdd
  · exact ⟨0, fun x => absurd ⟨x⟩ hV⟩

end UCPlanar.Support
