/-
A geometric square is contained in a graph metric ball of comparable radius.
-/
import UCPlanar.Support.LiouBallSquare

open scoped Classical

namespace UCPlanar.Support

/-- A geometric square is contained in a graph metric ball of comparable radius. -/
theorem square_subset_ball {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V) (R : ℝ) :
    ∃ n : ℕ, (P.square R : Set V) ⊆ (P.ball o n : Set V) := by
  refine ⟨(P.square R).sup (fun x => SimpleGraph.dist P.graph x o), ?_⟩
  intro x hx
  rw [Finset.mem_coe, UCPlanar.PeriodicGraph.ball, Set.Finite.mem_toFinset,
    LatticeProb.Graph.closedBall, Set.mem_setOf_eq]
  have h1 : SimpleGraph.dist P.graph x o ≤
      (P.square R).sup (fun x => SimpleGraph.dist P.graph x o) :=
    Finset.le_sup (f := fun x => SimpleGraph.dist P.graph x o) hx
  rw [← (P.connected x o).coe_dist_eq_edist]
  exact ENat.coe_le_coe.mpr h1

end UCPlanar.Support
