/-
Metric balls are contained in geometric squares and conversely.
-/
import UCPlanar.Support.Periodic
import UCPlanar.Support.FiniteDomains

open scoped Classical

-- FROZEN-STATEMENT-BEGIN
/-- A graph metric ball is contained in a geometric square of comparable radius. -/
theorem UCPlanar.Support.ball_subset_square {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (o : V) (n : ℕ) :
    ∃ R : ℝ, (P.ball o n : Set V) ⊆ (P.square R : Set V)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨(P.ball o n).sum (fun x => ∑ i : Fin 2, |P.pos x i|) + 1, ?_⟩
  intro x hx
  rw [Finset.mem_coe] at hx
  rw [Finset.mem_coe, UCPlanar.PeriodicGraph.square, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro i
  have h1 : |P.pos x i| ≤ ∑ j : Fin 2, |P.pos x j| := by
    simpa using Finset.single_le_sum (s := Finset.univ) (f := fun j => |P.pos x j|) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : ∑ j : Fin 2, |P.pos x j| ≤ (P.ball o n).sum (fun y => ∑ j : Fin 2, |P.pos y j|) := by
    simpa using Finset.single_le_sum (s := P.ball o n) (f := fun y => ∑ j : Fin 2, |P.pos y j|) (fun y _ => by positivity) hx
  linarith
