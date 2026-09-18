import UCPlanar.External.EdgeSplitting
import UCPlanar.External.Unicoherence
import UCPlanar.External.MoserEstimate
import UCPlanar.Support.Growth
import UCPlanar.Support.LiouBridge
import UCPlanar.Support.LiouPeriodic

-- FROZEN-STATEMENT-BEGIN
/-- “There is some ε > 0 ... then f is constant.”
`ucplanar.tex:161-167 (theorem:liouville)`.
The conductances are periodic, and the bounded-value density has a limit.
The proof runs the exponential upper bound against the exponential lower bound, so it carries the
cited inputs of both: the edge splitting
of the plane and the unicoherence of the sphere, and the discrete Moser estimate.  The discrete
Remez inequality is proved in `UCPlanar.Support.RemezDiscrete`, and the bounded Liouville theorem
for the periodic network is proved from the recurrence of the network in
`UCPlanar.Support.LiouPeriodic`. -/
theorem UCPlanar.Frozen.liouville {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P.toPeriodicGraph c)
    (hES : UCPlanar.External.EdgeSplitting P.embedding)
    (hU : UCPlanar.External.Unicoherence P.embedding) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a
-- FROZEN-STATEMENT-END
:= by
  refine UCPlanar.Support.liouville_of_bounds P c hc hp
    (UCPlanar.Support.uniformUpperBound_of_frozen P
      (UCPlanar.Frozen.uniformlyBounded P hES hU))
    (UCPlanar.Support.periodicLowerBound_of_frozen P.toPeriodicGraph c
      (UCPlanar.Frozen.periodicLowerBound P.toPeriodicGraph c hc hp hMos))
    (UCPlanar.Support.boundedLiouville_periodic P.toPeriodicGraph c hc hp)
