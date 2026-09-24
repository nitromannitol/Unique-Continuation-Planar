/- Periodic geometry: translations move vertices a bounded distance, so balls grow quadratically. -/
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.ZeroMax
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **A translation carries walks to walks of the same length.** -/
theorem exists_walk_shift {V : Type*} (P : UCPlanar.PeriodicGraph V) (a : LatticeProb.Site 2)
    {x y : V} (p : P.graph.Walk x y) :
    ∃ q : P.graph.Walk (P.shift a x) (P.shift a y), q.length = p.length := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | @cons u v w h q ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨SimpleGraph.Walk.cons ((P.shift_adj a u v).mpr h) r, ?_⟩
      simp [SimpleGraph.Walk.length_cons, hr]

/-- A translation does not increase the graph distance. -/
theorem dist_shift_le_dist {V : Type*} (P : UCPlanar.PeriodicGraph V) (a : LatticeProb.Site 2)
    (x y : V) : P.graph.dist (P.shift a x) (P.shift a y) ≤ P.graph.dist x y := by
  obtain ⟨p, hp⟩ := P.connected.exists_walk_length_eq_dist x y
  obtain ⟨q, hq⟩ := exists_walk_shift P a p
  calc P.graph.dist (P.shift a x) (P.shift a y) ≤ q.length := SimpleGraph.dist_le q
    _ = p.length := hq
    _ = P.graph.dist x y := hp

/-- **A uniform bound on the distance moved by a generating translation**, from the finitely
many vertex orbits. -/
theorem exists_step_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ K : ℕ, 0 < K ∧ ∀ (w : V) (i : Fin 2),
      P.graph.dist w (P.shift (LatticeProb.unit i) w) ≤ K := by
  classical
  refine ⟨1 + ∑ u ∈ P.representatives, ∑ i : Fin 2,
    P.graph.dist u (P.shift (LatticeProb.unit i) u), by omega, ?_⟩
  intro w i
  obtain ⟨u, hu, b, hbu⟩ := P.covers w
  have hstep : P.shift (LatticeProb.unit i) w = P.shift b (P.shift (LatticeProb.unit i) u) := by
    rw [← hbu, ← P.shift_add, ← P.shift_add, add_comm]
  have hle : P.graph.dist w (P.shift (LatticeProb.unit i) w)
      ≤ P.graph.dist u (P.shift (LatticeProb.unit i) u) := by
    rw [hstep, ← hbu]
    exact dist_shift_le_dist P b u (P.shift (LatticeProb.unit i) u)
  have hinner : P.graph.dist u (P.shift (LatticeProb.unit i) u)
      ≤ ∑ j : Fin 2, P.graph.dist u (P.shift (LatticeProb.unit j) u) :=
    Finset.single_le_sum
      (f := fun j : Fin 2 => P.graph.dist u (P.shift (LatticeProb.unit j) u))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have houter : (∑ j : Fin 2, P.graph.dist u (P.shift (LatticeProb.unit j) u))
      ≤ ∑ v ∈ P.representatives, ∑ j : Fin 2,
        P.graph.dist v (P.shift (LatticeProb.unit j) v) :=
    Finset.single_le_sum
      (f := fun v : V => ∑ j : Fin 2, P.graph.dist v (P.shift (LatticeProb.unit j) v))
      (fun v _ => Nat.zero_le _) hu
  omega

/-- The distance moved by a power of a generating translation grows at most linearly. -/
theorem dist_shift_single {V : Type*} (P : UCPlanar.PeriodicGraph V) (K : ℕ)
    (hK : ∀ (w : V) (i : Fin 2), P.graph.dist w (P.shift (LatticeProb.unit i) w) ≤ K)
    (i : Fin 2) (k : ℤ) (v : V) :
    P.graph.dist v (P.shift (Pi.single i k) v) ≤ K * k.natAbs := by
  classical
  have hback : ∀ (w : V), P.graph.dist w (P.shift (-(LatticeProb.unit i)) w) ≤ K := by
    intro w
    have h1 : P.shift (LatticeProb.unit i) (P.shift (-(LatticeProb.unit i)) w) = w := by
      rw [← P.shift_add, add_neg_cancel, P.shift_zero]
    have h2 := hK (P.shift (-(LatticeProb.unit i)) w) i
    rw [h1] at h2
    rw [SimpleGraph.dist_comm]
    exact h2
  induction k using Int.induction_on with
  | zero => simp [Pi.single_zero, P.shift_zero]
  | succ k ih =>
      have hsplit : (Pi.single i ((k : ℤ) + 1) : LatticeProb.Site 2)
          = LatticeProb.unit i + Pi.single i (k : ℤ) := by
        rw [add_comm ((k : ℤ)) 1, Pi.single_add]
        rfl
      rw [hsplit, P.shift_add]
      have htri := P.connected.dist_triangle (u := v) (v := P.shift (Pi.single i (k:ℤ)) v)
        (w := P.shift (LatticeProb.unit i) (P.shift (Pi.single i (k:ℤ)) v))
      have hlast := hK (P.shift (Pi.single i (k:ℤ)) v) i
      have hnat : ((k : ℤ) + 1).natAbs = (k : ℤ).natAbs + 1 := by omega
      rw [hnat]
      have : K * ((k:ℤ).natAbs + 1) = K * (k:ℤ).natAbs + K := by ring
      omega
  | pred k ih =>
      have hsplit : (Pi.single i (-(k : ℤ) - 1) : LatticeProb.Site 2)
          = -(LatticeProb.unit i) + Pi.single i (-(k : ℤ)) := by
        have h1 : (-(k : ℤ) - 1) = (-1) + (-(k : ℤ)) := by ring
        rw [h1, Pi.single_add]
        congr 1
        funext j
        by_cases hj : j = i <;> simp [Pi.single, Function.update, LatticeProb.unit, hj]
      rw [hsplit, P.shift_add]
      have htri := P.connected.dist_triangle (u := v) (v := P.shift (Pi.single i (-(k:ℤ))) v)
        (w := P.shift (-(LatticeProb.unit i)) (P.shift (Pi.single i (-(k:ℤ))) v))
      have hlast := hback (P.shift (Pi.single i (-(k:ℤ))) v)
      have hnat : ((-(k : ℤ)) - 1).natAbs = (-(k : ℤ)).natAbs + 1 := by omega
      rw [hnat]
      have : K * ((-(k:ℤ)).natAbs + 1) = K * (-(k:ℤ)).natAbs + K := by ring
      omega

/-- The translation action is free. -/
theorem shift_left_injective {V : Type*} (P : UCPlanar.PeriodicGraph V) (x : V) :
    Function.Injective (fun a : LatticeProb.Site 2 => P.shift a x) := by
  intro a b hab
  have h1 : P.pos (P.shift a x) = P.pos (P.shift b x) := congrArg P.pos hab
  rw [P.pos_shift, P.pos_shift] at h1
  have h2 : P.period (fun i => (a i : ℝ)) = P.period (fun i => (b i : ℝ)) := add_left_cancel h1
  have h3 : (fun i => (a i : ℝ)) = (fun i => (b i : ℝ)) := P.period.injective h2
  funext i
  have h4 : ((a i : ℝ)) = ((b i : ℝ)) := congrFun h3 i
  exact_mod_cast h4

/-- The distance moved by an arbitrary translation is at most linear in its coordinates. -/
theorem dist_shift_le_sum {V : Type*} (P : UCPlanar.PeriodicGraph V) (K : ℕ)
    (hK : ∀ (w : V) (i : Fin 2), P.graph.dist w (P.shift (LatticeProb.unit i) w) ≤ K)
    (v : V) (a : LatticeProb.Site 2) :
    P.graph.dist v (P.shift a v) ≤ K * ((a 0).natAbs + (a 1).natAbs) := by
  classical
  have ha : a = Pi.single (1 : Fin 2) (a 1) + Pi.single (0 : Fin 2) (a 0) := by
    funext j
    fin_cases j <;> simp [Pi.single, Function.update]
  have hshift : P.shift a v
      = P.shift (Pi.single (1 : Fin 2) (a 1)) (P.shift (Pi.single (0 : Fin 2) (a 0)) v) := by
    rw [← P.shift_add, ← ha]
  rw [hshift]
  have htri := P.connected.dist_triangle (u := v)
    (v := P.shift (Pi.single (0 : Fin 2) (a 0)) v)
    (w := P.shift (Pi.single (1 : Fin 2) (a 1)) (P.shift (Pi.single (0 : Fin 2) (a 0)) v))
  have h0 := dist_shift_single P K hK 0 (a 0) v
  have h1 := dist_shift_single P K hK 1 (a 1) (P.shift (Pi.single (0 : Fin 2) (a 0)) v)
  have hexp : K * ((a 0).natAbs + (a 1).natAbs) = K * (a 0).natAbs + K * (a 1).natAbs := by ring
  omega

/-- **Quadratic volume growth from below.**  The orbit of the centre under the translations of
bounded coordinates sits inside the ball, so a periodic graph has metric balls of at least
quadratic cardinality, uniformly in the centre. -/
theorem exists_ball_card_lower {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : V) (n : ℕ), c * ((n : ℝ) + 1)^2 ≤ ((P.ball v n).card : ℝ) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_step_bound P
  refine ⟨1 / (4 * (K : ℝ)^2), by positivity, ?_⟩
  intro v n
  set t : ℕ := n / (2*K) with ht
  have hmod : 2*K * t + n % (2*K) = n := by rw [ht]; exact Nat.div_add_mod n (2*K)
  have hlt : n % (2*K) < 2*K := Nat.mod_lt _ (by omega)
  set Box : Finset (LatticeProb.Site 2) :=
    Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(t : ℤ)) (t : ℤ)) with hBox
  have hmem : ∀ a ∈ Box, P.shift a v ∈ P.ball v n := by
    intro a hA
    rw [hBox] at hA
    have hA' := Fintype.mem_piFinset.mp hA
    have hb0 : (a 0).natAbs ≤ t := by
      have := Finset.mem_Icc.mp (hA' 0); omega
    have hb1 : (a 1).natAbs ≤ t := by
      have := Finset.mem_Icc.mp (hA' 1); omega
    have hdist : P.graph.dist v (P.shift a v) ≤ n := by
      have := dist_shift_le_sum P K hK v a
      have hKt : K * ((a 0).natAbs + (a 1).natAbs) ≤ K * (2*t) := by
        exact Nat.mul_le_mul_left K (by omega)
      have hKt2 : K * (2*t) = 2*K*t := by ring
      omega
    rw [mem_ball_iff]
    obtain ⟨p, hp⟩ := P.connected.exists_walk_length_eq_dist v (P.shift a v)
    have hed : P.graph.edist (P.shift a v) v ≤ ((p.reverse.length : ℕ) : ℕ∞) :=
      SimpleGraph.edist_le p.reverse
    have hlen : p.reverse.length ≤ n := by
      rw [SimpleGraph.Walk.length_reverse, hp]; exact hdist
    exact le_trans hed (by exact_mod_cast Nat.cast_le.mpr hlen)
  have hinj : Set.InjOn (fun a : LatticeProb.Site 2 => P.shift a v) (Box : Set (LatticeProb.Site 2)) :=
    fun a _ b _ h => shift_left_injective P v h
  have hcard : Box.card ≤ (P.ball v n).card := by
    have := Finset.card_le_card_of_injOn (fun a : LatticeProb.Site 2 => P.shift a v) hmem
      (fun a ha b hb h => shift_left_injective P v h)
    exact this
  have hIcc : (Finset.Icc (-(t : ℤ)) (t : ℤ)).card = 2 * t + 1 := by
    rw [Int.card_Icc]; omega
  have hBoxCard : Box.card = (2 * t + 1)^2 := by
    rw [hBox, Fintype.card_piFinset]
    simp [hIcc]
  have hexp : 2 * K * (2 * t + 1) = 2 * (2 * K * t) + 2 * K := by ring
  have hkey : n + 1 ≤ 2 * K * (2 * t + 1) := by omega
  have hkeyR : ((n : ℝ) + 1) ≤ 2 * (K : ℝ) * (2 * (t : ℝ) + 1) := by exact_mod_cast hkey
  have hballR : ((2 * (t : ℝ) + 1)^2) ≤ ((P.ball v n).card : ℝ) := by
    have h1 : ((2 * t + 1)^2 : ℕ) ≤ (P.ball v n).card := by rw [← hBoxCard]; exact hcard
    have h2 : (((2 * t + 1)^2 : ℕ) : ℝ) = (2 * (t : ℝ) + 1)^2 := by push_cast; ring
    calc ((2 * (t:ℝ) + 1)^2) = (((2 * t + 1)^2 : ℕ) : ℝ) := h2.symm
      _ ≤ ((P.ball v n).card : ℝ) := by exact_mod_cast h1
  have hK0R : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK0
  have hnn : (0:ℝ) ≤ (n:ℝ) + 1 := by positivity
  have hsq : ((n:ℝ) + 1)^2 ≤ (2 * (K:ℝ))^2 * (2 * (t:ℝ) + 1)^2 := by
    have h3 : ((n:ℝ)+1)^2 ≤ (2 * (K:ℝ) * (2 * (t:ℝ) + 1))^2 := by
      apply sq_le_sq' <;> nlinarith [hkeyR, hnn, hK0R]
    nlinarith [h3]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 4 * (K:ℝ)^2)]
  nlinarith [hballR, hsq, hK0R]

end UCPlanar.Support
