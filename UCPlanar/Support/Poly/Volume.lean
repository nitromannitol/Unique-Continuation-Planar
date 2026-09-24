/-
Quadratic volume growth of the geometric squares of a periodic graph, the conversion from the
`ℓ²` norm on a square to the supremum norm.
-/
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.Poly.Square

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- **Quadratic volume growth of squares.**  Finitely many vertex orbits and the bounded
distortion of the period map give a uniform quadratic bound on the number of vertices of a
geometric square. -/
theorem exists_square_card_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ((P.square R).card : ℝ) ≤ C * R ^ 2 := by
  classical
  obtain ⟨K, hK0, hK⟩ := UCPlanar.Support.exists_lattice_count P.period
  set R₀ : ℝ := ∑ v ∈ P.representatives, ‖P.pos v‖ with hR₀def
  have hR₀0 : 0 ≤ R₀ := Finset.sum_nonneg (fun v _ => norm_nonneg _)
  have hR₀ : ∀ v ∈ P.representatives, ‖P.pos v‖ ≤ R₀ :=
    fun v hv => Finset.single_le_sum (f := fun v => ‖P.pos v‖) (fun v _ => norm_nonneg _) hv
  have hb : (0:ℝ) < 2*K*(1 + R₀) + 3 := by nlinarith
  have hc : (0:ℝ) < ((P.representatives.card : ℝ) + 1) := by positivity
  refine ⟨((P.representatives.card : ℝ) + 1) * (2*K*(1 + R₀) + 3)^2,
    mul_pos hc (pow_pos hb 2), ?_⟩
  intro R hR
  have hR0 : (0:ℝ) ≤ R := by linarith
  set N : ℕ := ⌈K * (R + R₀)⌉₊ with hN
  set Box : Finset (LatticeProb.Site 2) :=
    Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(N:ℤ)) (N:ℤ)) with hBox
  set E : Finset V :=
    P.representatives.biUnion (fun v => Box.image (fun a => P.shift a v)) with hE
  have hsub : P.square R ⊆ E := by
    intro x hx
    obtain ⟨v, hv, a, hav⟩ := P.covers x
    have hposx : ‖P.pos x‖ ≤ R := by
      refine (pi_norm_le_iff_of_nonneg hR0).mpr ?_
      intro i
      simpa [Real.norm_eq_abs] using (UCPlanar.Support.mem_square_iff P R x).mp hx i
    have hpx : P.period (fun j => (a j : ℝ)) = P.pos x - P.pos v := by
      have := P.pos_shift a v
      rw [hav] at this
      linear_combination (norm := abel) -this
    have hnorm : ‖P.period (fun j => (a j : ℝ))‖ ≤ R + R₀ := by
      rw [hpx]
      have h3 : ‖P.pos x - P.pos v‖ ≤ ‖P.pos x‖ + ‖P.pos v‖ := norm_sub_le _ _
      have h4 := hR₀ v hv
      linarith
    have hbox : a ∈ Box := by
      rw [hBox]
      refine Fintype.mem_piFinset.mpr ?_
      intro j
      have h7 := hK a (R + R₀) hnorm j
      have h9 : ((|a j| : ℤ) : ℝ) ≤ K * (R + R₀) := by
        rw [Int.cast_abs]
        exact h7
      have h10 : ((|a j| : ℤ) : ℝ) ≤ (N : ℝ) := le_trans h9 (Nat.le_ceil _)
      have h11 : |a j| ≤ (N : ℤ) := by exact_mod_cast h10
      have h12 := abs_le.mp h11
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [hE]
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨a, hbox, hav⟩⟩
  have hIcc : (Finset.Icc (-(N:ℤ)) (N:ℤ)).card = 2 * N + 1 := by
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
  have hcard : (P.square R).card ≤ P.representatives.card * (2 * N + 1)^2 :=
    le_trans (Finset.card_le_card hsub) hEcard
  have hNle : (N : ℝ) ≤ K * (R + R₀) + 1 := by
    have := Nat.ceil_lt_add_one (a := K * (R + R₀)) (by positivity)
    linarith
  have hstep : (2 * (N:ℝ) + 1) ≤ (2*K*(1 + R₀) + 3) * R := by
    have hprod : (0:ℝ) ≤ 2 * K * R₀ * (R - 1) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [hNle, hprod, hR, hK0, hR₀0]
  have hcast : ((P.square R).card : ℝ)
      ≤ (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := by
    have h := hcard
    have h2 : (((P.representatives.card * (2 * N + 1)^2 : ℕ)) : ℝ)
        = (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := by push_cast; ring
    calc ((P.square R).card : ℝ) ≤ ((P.representatives.card * (2 * N + 1)^2 : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = (P.representatives.card : ℝ) * (2 * (N:ℝ) + 1)^2 := h2
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hsq : (2 * (N:ℝ) + 1)^2 ≤ ((2*K*(1 + R₀) + 3) * R)^2 := by
    have h1 : (0:ℝ) ≤ 2 * (N:ℝ) + 1 := by linarith
    exact pow_le_pow_left₀ h1 hstep 2
  have hrepnn : (0:ℝ) ≤ (P.representatives.card : ℝ) := Nat.cast_nonneg _
  nlinarith [hcast, hsq, hrepnn, sq_nonneg ((2*K*(1 + R₀) + 3) * R)]

/-- The `ℓ²` norm on a finite set is at most the square root of its cardinality times the
supremum norm. -/
theorem sum_sq_le_card_mul_supNorm_sq {V : Type*} (S : Finset V) (f : V → ℝ) :
    ∑ x ∈ S, f x ^ 2 ≤ (S.card : ℝ) * UCPlanar.supNorm S f ^ 2 := by
  have hbound : ∀ x ∈ S, f x ^ 2 ≤ UCPlanar.supNorm S f ^ 2 := by
    intro x hx
    have h : (‖f x‖₊ : NNReal) ≤ (S.sup (fun y => ‖f y‖₊) : NNReal) := Finset.le_sup (f := fun y => ‖f y‖₊) hx
    have h' : |f x| ≤ UCPlanar.supNorm S f := by
      rw [UCPlanar.supNorm]
      have hcast : (‖f x‖₊ : ℝ) ≤ ((S.sup (fun y => ‖f y‖₊) : NNReal) : ℝ) := by exact_mod_cast h
      simpa [Real.norm_eq_abs] using hcast
    have habs : f x ^ 2 = |f x| ^ 2 := (sq_abs (f x)).symm
    rw [habs]
    exact pow_le_pow_left₀ (abs_nonneg _) h' 2
  calc ∑ x ∈ S, f x ^ 2 ≤ ∑ _x ∈ S, UCPlanar.supNorm S f ^ 2 := Finset.sum_le_sum hbound
    _ = (S.card : ℝ) * UCPlanar.supNorm S f ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

end UCPlanar.Support
