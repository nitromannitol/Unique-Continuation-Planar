/- The finite domains agree with their defining geometric and graph sets. -/
import UCPlanar.Support.Periodic

/-- The finite ball `P.ball o n`, as a set, coincides with the graph's closed metric
ball of radius `n` about `o`. -/
theorem UCPlanar.Support.coe_ball {V : Type*} (P : UCPlanar.PeriodicGraph V) (o : V) (n : ℕ) :
    (P.ball o n : Set V) = LatticeProb.Graph.closedBall P.graph o n := by
  simp [UCPlanar.PeriodicGraph.ball]

/-- The finite square `P.square R`, as a set, is exactly the vertices whose drawing lies
in the sup-norm ball of radius `R`. -/
theorem UCPlanar.Support.coe_square {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) :
    (P.square R : Set V) = {x | ∀ i, |P.pos x i| ≤ R} := by
  simp [UCPlanar.PeriodicGraph.square]
