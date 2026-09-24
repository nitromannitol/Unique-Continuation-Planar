/- Periodic geometry: edges are short, walks move the drawing slowly, vertices are infinite. -/
import UCPlanar.Support.Periodic
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **Edges are geometrically short.** Finitely many vertex orbits and local finiteness give a
uniform bound on the displacement across an edge. -/
theorem exists_edge_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, P.graph.Adj x y → ‖P.pos x - P.pos y‖ ≤ D := by
  classical
  set A : Finset (V × V) :=
    P.representatives.biUnion (fun v => (P.graph.neighborFinset v).image (fun w => (v, w))) with hA
  refine ⟨∑ p ∈ A, ‖P.pos p.1 - P.pos p.2‖, Finset.sum_nonneg (fun p _ => norm_nonneg _), ?_⟩
  intro x y hxy
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
  have hpos : P.pos x - P.pos y = P.pos v - P.pos w := by
    rw [← hav, ← hyw, P.pos_shift, P.pos_shift]
    abel
  rw [hpos]
  exact Finset.single_le_sum (f := fun p : V × V => ‖P.pos p.1 - P.pos p.2‖)
    (fun p _ => norm_nonneg _) hmem

/-- **A walk moves the drawing by at most its length times the edge bound.** -/
theorem norm_pos_sub_le_walk {V : Type*} (P : UCPlanar.PeriodicGraph V) (D : ℝ)
    (hD : ∀ x y, P.graph.Adj x y → ‖P.pos x - P.pos y‖ ≤ D) {x y : V}
    (p : P.graph.Walk x y) : ‖P.pos x - P.pos y‖ ≤ D * p.length := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
      have h1 : ‖P.pos u - P.pos w‖ ≤ ‖P.pos u - P.pos v‖ + ‖P.pos v - P.pos w‖ := by
        have := dist_triangle (P.pos u) (P.pos v) (P.pos w)
        simpa [dist_eq_norm] using this
      have h2 := hD u v h
      have h3 : (0 : ℝ) ≤ D := le_trans (norm_nonneg _) h2
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith [ih, h1, h2, h3]

/-- **A periodic graph has infinitely many vertices**, because the translation action is free. -/
theorem infinite_of_periodic {V : Type*} (P : UCPlanar.PeriodicGraph V) : Infinite V := by
  classical
  haveI : Nonempty V := P.connected.nonempty
  obtain ⟨x⟩ : Nonempty V := inferInstance
  have hinj : Function.Injective (fun a : LatticeProb.Site 2 => P.shift a x) := by
    intro a b hab
    have h1 : P.pos (P.shift a x) = P.pos (P.shift b x) := congrArg P.pos hab
    rw [P.pos_shift, P.pos_shift] at h1
    have h2 : P.period (fun i => (a i : ℝ)) = P.period (fun i => (b i : ℝ)) :=
      add_left_cancel h1
    have h3 : (fun i => (a i : ℝ)) = (fun i => (b i : ℝ)) := P.period.injective h2
    funext i
    have h4 : ((a i : ℝ)) = ((b i : ℝ)) := congrFun h3 i
    exact_mod_cast h4
  exact Infinite.of_injective _ hinj

/-- **A linear equivalence of the plane distorts the integer lattice boundedly.** -/
theorem exists_lattice_count (T : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : Fin 2 → ℤ) (M : ℝ), ‖T (fun j => (a j : ℝ))‖ ≤ M →
      ∀ j, |(a j : ℝ)| ≤ K * M := by
  classical
  set A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    LinearMap.toContinuousLinearMap (T.symm : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) with hA
  refine ⟨‖A‖, norm_nonneg _, ?_⟩
  intro a M hM j
  set v : Fin 2 → ℝ := fun j => (a j : ℝ) with hv
  have hAv : A (T v) = v := by
    simp [hA, LinearMap.coe_toContinuousLinearMap']
  have h1 : ‖v‖ ≤ ‖A‖ * ‖T v‖ := by
    have hop := A.le_opNorm (T v)
    rwa [hAv] at hop
  have h2 : ‖A‖ * ‖T v‖ ≤ ‖A‖ * M := mul_le_mul_of_nonneg_left hM (norm_nonneg A)
  have h3 : |(a j : ℝ)| ≤ ‖v‖ := by
    have := norm_le_pi_norm v j
    simpa [hv, Real.norm_eq_abs] using this
  linarith

/-- **Counting the integer points of a square box.** -/
theorem card_int_box_le (B : ℝ) (hB : 0 ≤ B) :
    (({a : Fin 2 → ℤ | ∀ j, |(a j : ℝ)| ≤ B}).ncard : ℝ) ≤ (2*B+1)^2 := by
  classical
  set N : ℕ := ⌊B⌋₊ with hN
  set F : Finset (Fin 2 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(N : ℤ)) (N : ℤ)) with hF
  have hsub : {a : Fin 2 → ℤ | ∀ j, |(a j : ℝ)| ≤ B} ⊆ (F : Set (Fin 2 → ℤ)) := by
    intro a ha
    simp only [hF, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have h1 : |(a j : ℝ)| ≤ B := ha j
    have habs : (0 : ℤ) ≤ |a j| := abs_nonneg _
    have h4 : (((|a j|).toNat : ℕ) : ℝ) ≤ B := by
      have hcast : ((|a j|).toNat : ℤ) = |a j| := Int.toNat_of_nonneg habs
      have h5 : (((|a j|).toNat : ℕ) : ℝ) = ((|a j| : ℤ) : ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hcast
      rw [h5, Int.cast_abs]
      exact h1
    have h6 : (|a j|).toNat ≤ N := Nat.le_floor h4
    have h7 : |a j| ≤ (N : ℤ) := by omega
    exact abs_le.mp h7
  have hIcc : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    rw [Int.card_Icc]; omega
  have hcardN : F.card = (2 * N + 1) ^ 2 := by
    rw [hF, Fintype.card_piFinset]
    simp [hIcc]
  have hle : (({a : Fin 2 → ℤ | ∀ j, |(a j : ℝ)| ≤ B}).ncard : ℝ) ≤ (F.card : ℝ) := by
    have h := Set.ncard_le_ncard hsub F.finite_toSet
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  have hNB : (N : ℝ) ≤ B := Nat.floor_le hB
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  rw [hcardN] at hle
  push_cast at hle
  nlinarith [hle, hNB, hN0]

/-- **A vertex of a metric ball is joined to the centre by a short walk.** -/
theorem exists_short_walk {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V) (n : ℕ)
    {x : V} (hx : x ∈ P.ball o n) : ∃ p : P.graph.Walk x o, p.length ≤ n := by
  classical
  have hx' : P.graph.edist x o ≤ (n : ℕ∞) := by
    have h := (Set.Finite.mem_toFinset _).mp hx
    simpa [LatticeProb.Graph.closedBall] using h
  obtain ⟨p, hp⟩ := P.connected.exists_walk_length_eq_edist x o
  refine ⟨p, ?_⟩
  have h2 : ((p.length : ℕ∞)) ≤ (n : ℕ∞) := by rw [hp]; exact hx'
  exact_mod_cast h2

/-- **The period map is additive on integer differences.** -/
theorem period_sub {V : Type*} (P : UCPlanar.PeriodicGraph V) (a b : LatticeProb.Site 2) :
    P.period (fun j => (((a - b) j : ℤ) : ℝ))
      = P.period (fun j => (a j : ℝ)) - P.period (fun j => (b j : ℝ)) := by
  have hfun : (fun j => (((a - b) j : ℤ) : ℝ))
      = (fun j => (a j : ℝ)) - (fun j => (b j : ℝ)) := by
    funext j
    simp [Pi.sub_apply]
  rw [hfun, map_sub]

/-- **Quadratic volume growth.**  A periodic graph has metric balls of at most quadratic
cardinality, uniformly in the centre.  This is the volume bound behind Step 2 of Section 3. -/
theorem exists_ball_card_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (o : V) (n : ℕ), ((P.ball o n).card : ℝ) ≤ C * (n + 1)^2 := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_edge_bound P
  obtain ⟨K, hK0, hK⟩ := exists_lattice_count P.period
  set R₀ : ℝ := ∑ v ∈ P.representatives, ‖P.pos v‖ with hR₀def
  have hR₀0 : 0 ≤ R₀ := Finset.sum_nonneg (fun v _ => norm_nonneg _)
  have hR₀ : ∀ v ∈ P.representatives, ‖P.pos v‖ ≤ R₀ :=
    fun v hv => Finset.single_le_sum (f := fun v => ‖P.pos v‖) (fun v _ => norm_nonneg _) hv
  have hb : (0:ℝ) < 2*K*(D + 2*R₀) + 3 := by nlinarith
  have hc : (0:ℝ) < ((P.representatives.card : ℝ) + 1) := by positivity
  refine ⟨((P.representatives.card : ℝ) + 1) * (2*K*(D + 2*R₀) + 3)^2,
    mul_pos hc (pow_pos hb 2), ?_⟩
  intro o n
  obtain ⟨v₀, hv₀, a₀, ha₀⟩ := P.covers o
  set N : ℕ := ⌈K * (D * n + 2*R₀)⌉₊ with hN
  set Box : Finset (LatticeProb.Site 2) :=
    Fintype.piFinset (fun j => Finset.Icc (a₀ j - (N:ℤ)) (a₀ j + (N:ℤ))) with hBox
  set E : Finset V :=
    P.representatives.biUnion (fun v => Box.image (fun a => P.shift a v)) with hE
  have hsub : P.ball o n ⊆ E := by
    intro x hx
    obtain ⟨p, hp⟩ := exists_short_walk P o n hx
    obtain ⟨v, hv, a, hav⟩ := P.covers x
    have hwalk : ‖P.pos x - P.pos o‖ ≤ D * n := by
      have h1 := norm_pos_sub_le_walk P D hD p
      have h2 : (p.length : ℝ) ≤ n := by exact_mod_cast hp
      nlinarith [h1, h2, hD0, norm_nonneg (P.pos x - P.pos o)]
    have hpx : P.period (fun j => (a j : ℝ)) = P.pos x - P.pos v := by
      have := P.pos_shift a v
      rw [hav] at this
      linear_combination (norm := abel) -this
    have hpo : P.period (fun j => (a₀ j : ℝ)) = P.pos o - P.pos v₀ := by
      have := P.pos_shift a₀ v₀
      rw [ha₀] at this
      linear_combination (norm := abel) -this
    have hdiff : P.period (fun j => (((a - a₀) j : ℤ) : ℝ))
        = (P.pos x - P.pos o) + (P.pos v₀ - P.pos v) := by
      rw [period_sub, hpx, hpo]
      abel
    have hnorm : ‖P.period (fun j => (((a - a₀) j : ℤ) : ℝ))‖ ≤ D * n + 2*R₀ := by
      rw [hdiff]
      have h3 : ‖(P.pos x - P.pos o) + (P.pos v₀ - P.pos v)‖
          ≤ ‖P.pos x - P.pos o‖ + ‖P.pos v₀ - P.pos v‖ := norm_add_le _ _
      have h4 : ‖P.pos v₀ - P.pos v‖ ≤ ‖P.pos v₀‖ + ‖P.pos v‖ := norm_sub_le _ _
      have h5 := hR₀ v₀ hv₀
      have h6 := hR₀ v hv
      linarith
    have hbox : a ∈ Box := by
      rw [hBox]
      refine Fintype.mem_piFinset.mpr ?_
      intro j
      have h7 := hK (a - a₀) (D * n + 2*R₀) hnorm j
      have h8 : |((a j - a₀ j : ℤ) : ℝ)| ≤ K * (D * n + 2*R₀) := by
        have : ((a - a₀) j : ℤ) = a j - a₀ j := by simp [Pi.sub_apply]
        rw [this] at h7
        exact h7
      have h9 : ((|a j - a₀ j| : ℤ) : ℝ) ≤ K * (D * n + 2*R₀) := by
        rw [Int.cast_abs]
        exact h8
      have h10 : ((|a j - a₀ j| : ℤ) : ℝ) ≤ (N : ℝ) := le_trans h9 (Nat.le_ceil _)
      have h11 : |a j - a₀ j| ≤ (N : ℤ) := by exact_mod_cast h10
      have h12 := abs_le.mp h11
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [hE]
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨a, hbox, hav⟩⟩
  have hIcc : ∀ j : Fin 2, (Finset.Icc (a₀ j - (N:ℤ)) (a₀ j + (N:ℤ))).card = 2 * N + 1 := by
    intro j
    rw [Int.card_Icc]
    omega
  have hBoxCard : Box.card = (2 * N + 1)^2 := by
    rw [hBox, Fintype.card_piFinset]
    simp [hIcc]
  have hEcard : E.card ≤ P.representatives.card * (2 * N + 1)^2 := by
    calc E.card ≤ ∑ v ∈ P.representatives, (Box.image (fun a => P.shift a v)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ P.representatives, Box.card :=
          Finset.sum_le_sum (fun v _ => Finset.card_image_le)
      _ = P.representatives.card * Box.card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = P.representatives.card * (2 * N + 1)^2 := by rw [hBoxCard]
  have hballcard : (P.ball o n).card ≤ P.representatives.card * (2 * N + 1)^2 :=
    le_trans (Finset.card_le_card hsub) hEcard
  have hNle : (N : ℝ) ≤ K * (D * n + 2*R₀) + 1 := by
    have := Nat.ceil_lt_add_one (a := K * (D * n + 2*R₀)) (by positivity)
    linarith
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have haux : K * (D * n + 2*R₀) ≤ K * ((D + 2*R₀) * (n+1)) := by
    apply mul_le_mul_of_nonneg_left _ hK0
    nlinarith [hn0, hD0, hR₀0]
  have hkey : (2 * (N:ℝ) + 1) ≤ (2*K*(D + 2*R₀) + 3) * (n + 1) := by
    nlinarith [hNle, haux, hn0]
  have hpos1 : (0:ℝ) ≤ 2 * (N:ℝ) + 1 := by positivity
  have hfinal : ((P.ball o n).card : ℝ)
      ≤ (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := by
    have := hballcard
    have hc2 : (((P.representatives.card * (2 * N + 1)^2 : ℕ)) : ℝ)
        = (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := by push_cast; ring
    calc ((P.ball o n).card : ℝ) ≤ ((P.representatives.card * (2 * N + 1)^2 : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := hc2
  have hsq : (2 * (N:ℝ) + 1)^2 ≤ ((2*K*(D + 2*R₀) + 3) * (n + 1))^2 := by
    apply sq_le_sq' <;> nlinarith [hkey, hpos1]
  have hrep0 : (0:ℝ) ≤ (P.representatives.card : ℝ) := Nat.cast_nonneg _
  calc ((P.ball o n).card : ℝ)
      ≤ (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := hfinal
    _ ≤ (P.representatives.card : ℝ) * ((2*K*(D + 2*R₀) + 3) * (n + 1))^2 := by
        exact mul_le_mul_of_nonneg_left hsq hrep0
    _ ≤ ((P.representatives.card : ℝ) + 1) * (2*K*(D + 2*R₀) + 3)^2 * (n + 1)^2 := by
        have : ((2*K*(D + 2*R₀) + 3) * ((n:ℝ) + 1))^2
            = (2*K*(D + 2*R₀) + 3)^2 * ((n:ℝ) + 1)^2 := by ring
        rw [this]
        nlinarith [hrep0, sq_nonneg ((2*K*(D + 2*R₀) + 3)), sq_nonneg ((n:ℝ)+1),
          mul_nonneg (sq_nonneg ((2*K*(D + 2*R₀) + 3))) (sq_nonneg ((n:ℝ)+1))]

end UCPlanar.Support
