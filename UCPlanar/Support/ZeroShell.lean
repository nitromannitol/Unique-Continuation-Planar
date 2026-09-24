/- Step 2 of Section 3: a radius whose neighbourhood carries few nonzero vertices. -/
import UCPlanar.Support.ZeroVolume
import UCPlanar.Support.ZeroCount
import UCPlanar.Basic
import Mathlib

open scoped BigOperators Classical

namespace UCPlanar.Support

/-- **Step 2 of Section 3: a sparse boundary radius.**  If `f` vanishes off an `ε`-fraction of
`B_{2n}`, some radius `m` with `3n/2 ≤ m` and `m + r ≤ 2n` carries at most `C ε n` vertices where `f` exceeds
the threshold within graph distance `r` of the sphere of radius `m`.  Keeping the whole buffer
inside `B_{2n}` is what makes the count one of vertices the density hypothesis controls;
quadratic volume growth turns the average over the admissible radii into a bound linear in
`n`. -/
theorem exists_sparse_shell {V : Type*} (P : UCPlanar.PeriodicGraph V) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (o : V) (n : ℕ), 0 < n → 4 * r ≤ n → ∀ (thr ε : ℝ), 0 ≤ ε →
      ∀ f : V → ℝ,
      ((UCPlanar.exceptionalCount (P.ball o (2*n)) f thr : ℕ) : ℝ)
          ≤ ε * (P.ball o (2*n)).card →
      ∃ m : ℕ, 3*n ≤ 2*m ∧ m + r ≤ 2*n ∧
        ((((P.ball o (2*n)).filter (fun x => thr < |f x| ∧
            m ≤ P.graph.dist o x + r ∧ P.graph.dist o x ≤ m + r)).card : ℝ) ≤ C * ε * n) := by
  classical
  obtain ⟨C₀, hC₀, hball⟩ := exists_ball_card_bound P
  refine ⟨36 * (2*r+1) * C₀, by positivity, ?_⟩
  intro o n hn hr thr ε hε f hcount
  set m₀ : ℕ := (3*n+1)/2 with hm₀
  set M : ℕ := 2*n + 1 - r - m₀ with hM
  have hM0 : 0 < M := by omega
  have hnM : n ≤ 4 * M := by omega
  set S : Finset V := (P.ball o (2*n)).filter (fun x => thr < |f x|) with hS
  set T : ℕ → Finset V := fun k => S.filter (fun x =>
    m₀ + k ≤ P.graph.dist o x + r ∧ P.graph.dist o x ≤ m₀ + k + r) with hT
  have hsub : ∀ k, k < M → T k ⊆ S := fun k _ => Finset.filter_subset _ _
  have hmult : ∀ x ∈ S, ((Finset.range M).filter (fun k => x ∈ T k)).card ≤ 2*r+1 := by
    intro x hx
    have hsubI : (Finset.range M).filter (fun k => x ∈ T k)
        ⊆ Finset.Icc (P.graph.dist o x - r - m₀) (P.graph.dist o x + r - m₀) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      have hk2 := hk.2
      rw [hT] at hk2
      simp only [Finset.mem_filter] at hk2
      obtain ⟨-, h1, h2⟩ := hk2
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hcard := Finset.card_le_card hsubI
    have hIcc : (Finset.Icc (P.graph.dist o x - r - m₀) (P.graph.dist o x + r - m₀)).card
        ≤ 2*r+1 := by
      rw [Nat.card_Icc]; omega
    omega
  obtain ⟨k, hk, hle⟩ := exists_sparse_index S T M (2*r+1) hM0 hsub hmult
  refine ⟨m₀ + k, by omega, by omega, ?_⟩
  have hfilter : (P.ball o (2*n)).filter (fun x => thr < |f x| ∧
      m₀ + k ≤ P.graph.dist o x + r ∧ P.graph.dist o x ≤ m₀ + k + r) = T k := by
    ext x
    simp only [hT, hS, Finset.mem_filter]
    tauto
  rw [hfilter]
  have hScard : (S.card : ℝ) ≤ ε * ((P.ball o (2*n)).card : ℝ) := by
    have : (S.card : ℝ) = ((UCPlanar.exceptionalCount (P.ball o (2*n)) f thr : ℕ) : ℝ) := by
      rw [hS, UCPlanar.exceptionalCount]
    rw [this]; exact hcount
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hballn : ((P.ball o (2*n)).card : ℝ) ≤ C₀ * ((2*n : ℕ) + 1)^2 := hball o (2*n)
  have hcast : ((2*n : ℕ) : ℝ) = 2 * (n:ℝ) := by push_cast; ring
  rw [hcast] at hballn
  have hS9 : (S.card : ℝ) ≤ 9 * C₀ * ε * (n:ℝ)^2 := by
    have h1 : ε * ((P.ball o (2*n)).card : ℝ) ≤ ε * (C₀ * (2*(n:ℝ) + 1)^2) :=
      mul_le_mul_of_nonneg_left hballn hε
    have hsq : (2*(n:ℝ)+1)^2 ≤ 9*(n:ℝ)^2 := by nlinarith [hn1]
    have h2 : ε * (C₀ * (2*(n:ℝ)+1)^2) ≤ ε * (C₀ * (9*(n:ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hC₀.le) hε
    have h3 : ε * (C₀ * (9*(n:ℝ)^2)) = 9*C₀*ε*(n:ℝ)^2 := by ring
    linarith [hScard, h1, h2, h3.le, h3.ge]
  have hM0r : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM0
  have hMreal : (n:ℝ) ≤ 4*(M:ℝ) := by exact_mod_cast hnM
  refine le_trans hle ?_
  rw [div_le_iff₀ hM0r]
  have hnn : (0:ℝ) ≤ 9*C₀*ε*(n:ℝ) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hMreal hnn
  have hprod : 9*C₀*ε*(n:ℝ)^2 ≤ 36*C₀*ε*(n:ℝ)*(M:ℝ) := by nlinarith [hstep]
  have hρ0 : (0:ℝ) ≤ 2*(r:ℝ)+1 := by positivity
  have hcastρ : (((2*r+1 : ℕ)) : ℝ) = 2*(r:ℝ)+1 := by push_cast; ring
  rw [hcastρ]
  calc (2*(r:ℝ)+1) * (S.card:ℝ)
      ≤ (2*(r:ℝ)+1) * (9*C₀*ε*(n:ℝ)^2) := mul_le_mul_of_nonneg_left hS9 hρ0
    _ ≤ (2*(r:ℝ)+1) * (36*C₀*ε*(n:ℝ)*(M:ℝ)) := mul_le_mul_of_nonneg_left hprod hρ0
    _ = 36 * (2*(r:ℝ)+1) * C₀ * ε * (n:ℝ) * (M:ℝ) := by ring

end UCPlanar.Support
