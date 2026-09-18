/-
The comparison of geometric squares with graph metric balls.

Every vertex of the square of radius `R` is a lattice translate of one of the finitely many
vertices of the square of radius `ρ`, the translation has coordinates at most a constant times
`R + ρ`, and a translation by one lattice generator moves a vertex a bounded graph distance.  So
the square of radius `R` lies in the ball of radius `C R + c`, where `C` depends only on the
graph and only the additive constant depends on the centre of the ball.
-/
import UCPlanar.Support.ZeroLower
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.ZeroAssemble
import UCPlanar.Support.LowerVolume

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace UCPlanar.Support.LiouFinal

/-- **Squares sit inside balls, with a multiplicative constant independent of the centre.**  The
additive constant is the graph distance from the centre to the finitely many vertices of a
fundamental square. -/
theorem exists_square_ball_uniform {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ o : V, ∃ c₂ : ℝ, 0 ≤ c₂ ∧ ∀ R : ℝ, 0 ≤ R →
      ∃ n : ℕ, (n:ℝ) ≤ Cg*R + c₂ ∧ (P.square R : Set V) ⊆ (P.ball o n : Set V) := by
  classical
  obtain ⟨Kd, hKd0, hKd⟩ := UCPlanar.Support.exists_step_bound P
  obtain ⟨Kl, hKl0, hKl⟩ := UCPlanar.Support.exists_lattice_count P.period
  obtain ⟨ρ, hρ0, hcentre⟩ := UCPlanar.Support.Lower.exists_centre P
  have hKdR : (0:ℝ) < (Kd:ℝ) := by exact_mod_cast hKd0
  set Cg : ℝ := 2*(Kd:ℝ)*(Kl+1) with hCgdef
  have hCg0 : 0 < Cg := by rw [hCgdef]; positivity
  refine ⟨Cg, hCg0, ?_⟩
  intro o
  set d₀ : ℕ := (P.square ρ).sup (fun u => P.graph.dist o u) with hd₀def
  refine ⟨Cg*ρ + (d₀:ℝ) + 1, by positivity, ?_⟩
  intro R hR
  have hbase : (0:ℝ) ≤ Cg*R + Cg*ρ + (d₀:ℝ) := by positivity
  refine ⟨⌈Cg*R + Cg*ρ + (d₀:ℝ)⌉₊, ?_, ?_⟩
  · have h1 : ((⌈Cg*R + Cg*ρ + (d₀:ℝ)⌉₊ : ℕ) : ℝ) < Cg*R + Cg*ρ + (d₀:ℝ) + 1 :=
      Nat.ceil_lt_add_one hbase
    linarith
  · intro y hy
    have hyF : y ∈ P.square R := hy
    obtain ⟨a, ha⟩ := hcentre y
    have huF : P.shift (-a) y ∈ P.square ρ :=
      (UCPlanar.Support.Lower.mem_squareAt P a ρ y).mp ha
    set u : V := P.shift (-a) y with hudef
    have hyu : P.shift a u = y := by
      rw [hudef, ← P.shift_add, add_neg_cancel, P.shift_zero]
    -- the two drawings are inside their squares
    have hposy : ‖P.pos y‖ ≤ R := by
      rw [pi_norm_le_iff_of_nonneg hR]
      intro i
      rw [Real.norm_eq_abs]
      exact (UCPlanar.Support.mem_square_iff P R y).mp hyF i
    have hposu : ‖P.pos u‖ ≤ ρ := by
      rw [pi_norm_le_iff_of_nonneg hρ0]
      intro i
      rw [Real.norm_eq_abs]
      exact (UCPlanar.Support.mem_square_iff P ρ u).mp huF i
    -- the lattice vector is short
    have hpery : P.pos y = P.pos u + P.period (fun i => ((a i : ℤ) : ℝ)) := by
      rw [← hyu]; exact P.pos_shift a u
    have hpernorm : ‖P.period (fun i => ((a i : ℤ) : ℝ))‖ ≤ R + ρ := by
      have heq : P.period (fun i => ((a i : ℤ) : ℝ)) = P.pos y - P.pos u := by
        rw [hpery]; ring
      rw [heq]
      calc ‖P.pos y - P.pos u‖ ≤ ‖P.pos y‖ + ‖P.pos u‖ := norm_sub_le _ _
        _ ≤ R + ρ := by linarith
    have hcoord : ∀ j, |((a j : ℤ) : ℝ)| ≤ Kl*(R+ρ) := hKl a (R+ρ) hpernorm
    have habs : ∀ j, (((a j).natAbs : ℕ) : ℝ) = |((a j : ℤ) : ℝ)| := by
      intro j
      rw [Nat.cast_natAbs, Int.cast_abs]
    have hnat : ∀ j, (((a j).natAbs : ℕ) : ℝ) ≤ Kl*(R+ρ) := by
      intro j; rw [habs j]; exact hcoord j
    -- the graph distance from the fundamental vertex
    have hdist_uy : P.graph.dist u y ≤ Kd * ((a 0).natAbs + (a 1).natAbs) := by
      rw [← hyu]
      exact UCPlanar.Support.dist_shift_le_sum P Kd hKd u a
    have hdist_uyR : ((P.graph.dist u y : ℕ) : ℝ) ≤ (Kd:ℝ) * (2*(Kl*(R+ρ))) := by
      have h1 : ((P.graph.dist u y : ℕ) : ℝ)
          ≤ ((Kd * ((a 0).natAbs + (a 1).natAbs) : ℕ) : ℝ) := by exact_mod_cast hdist_uy
      have h2 : ((Kd * ((a 0).natAbs + (a 1).natAbs) : ℕ) : ℝ)
          = (Kd:ℝ) * ((((a 0).natAbs : ℕ):ℝ) + (((a 1).natAbs : ℕ):ℝ)) := by push_cast; ring
      have h3 : (Kd:ℝ) * ((((a 0).natAbs : ℕ):ℝ) + (((a 1).natAbs : ℕ):ℝ))
          ≤ (Kd:ℝ) * (2*(Kl*(R+ρ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hKdR.le
        linarith [hnat 0, hnat 1]
      linarith [h1, h2 ▸ h1]
    -- the triangle inequality from the centre
    have hdist_ou : P.graph.dist o u ≤ d₀ := by
      rw [hd₀def]
      exact Finset.le_sup (f := fun w => P.graph.dist o w) huF
    have htri : P.graph.dist o y ≤ P.graph.dist o u + P.graph.dist u y :=
      P.connected.dist_triangle
    have hfin : ((P.graph.dist o y : ℕ) : ℝ) ≤ Cg*R + Cg*ρ + (d₀:ℝ) := by
      have h1 : ((P.graph.dist o y : ℕ) : ℝ)
          ≤ ((P.graph.dist o u : ℕ):ℝ) + ((P.graph.dist u y : ℕ):ℝ) := by exact_mod_cast htri
      have h2 : ((P.graph.dist o u : ℕ):ℝ) ≤ (d₀:ℝ) := by exact_mod_cast hdist_ou
      have h3 : (Kd:ℝ) * (2*(Kl*(R+ρ))) ≤ Cg*(R+ρ) := by
        rw [hCgdef]
        nlinarith [hKdR, hKl0, hR, hρ0]
      have h4 : Cg*(R+ρ) = Cg*R + Cg*ρ := by ring
      linarith [h1, h2, hdist_uyR, h3, h4]
    have hle : P.graph.dist o y ≤ ⌈Cg*R + Cg*ρ + (d₀:ℝ)⌉₊ := by
      have h1 : Cg*R + Cg*ρ + (d₀:ℝ) ≤ ((⌈Cg*R + Cg*ρ + (d₀:ℝ)⌉₊ : ℕ):ℝ) := Nat.le_ceil _
      have h2 : ((P.graph.dist o y : ℕ) : ℝ) ≤ ((⌈Cg*R + Cg*ρ + (d₀:ℝ)⌉₊ : ℕ):ℝ) := by
        linarith
      exact_mod_cast h2
    have : y ∈ P.ball o ⌈Cg*R + Cg*ρ + (d₀:ℝ)⌉₊ :=
      (UCPlanar.Support.mem_ball_iff_dist P o y _).mpr hle
    exact this

end UCPlanar.Support.LiouFinal
