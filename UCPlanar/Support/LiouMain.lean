/-
Assembly of the Liouville theorem from the uniform upper bound, the periodic
exponential lower bound, and the classical bounded-Liouville fact.
-/
import UCPlanar.Support.LiouAssembly
import UCPlanar.Support.LiouUnbounded
import UCPlanar.Support.LiouExpCompare
import UCPlanar.Support.LiouRatio
import UCPlanar.Support.LiouFinalContra
import UCPlanar.Support.LiouSquareDensity

open scoped Classical

namespace UCPlanar.Support

/-- The Liouville theorem, assembled from the uniform upper bound, the periodic
exponential lower bound, the classical bounded-Liouville fact.  The density hypothesis is transferred from
the metric balls to the geometric squares, and the ellipticity ratio of the
conductance comes from its periodicity. -/
theorem liouville_of_bounds {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hUB : UniformUpperBound P) (hLB : PeriodicLowerBound P.toPeriodicGraph c)
    (hBL : BoundedLiouville P.toPeriodicGraph c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a := by
  obtain ⟨lam, Θ, hlam, hΘ, hell⟩ := uniformlyElliptic_ratio P.toPeriodicGraph c hc hp
  exact LiouFinal.liouville_final_of_density P c hc lam Θ hlam hΘ hell hUB hLB hBL
    (exists_density_transfer P.toPeriodicGraph)

end UCPlanar.Support
