import UCPlanar.MainTheorems
import UCPlanar.Proved.Unicoherence
import UCPlanar.Proved.EdgeSplitting

/-!
# The main theorems with the plane-topology inputs proved

The theorems of `UCPlanar.MainTheorems` assume the two cited plane-topology statements
`UCPlanar.External.EdgeSplitting` and `UCPlanar.External.Unicoherence` for the drawing of the
periodic plane graph.  Both are proved for every periodic plane graph in
`UCPlanar.Proved.EdgeSplitting` and `UCPlanar.Proved.Unicoherence`, so the theorems below restate
the main theorems without them.  The Liouville theorem keeps its remaining cited input, the
Moser estimate `UCPlanar.External.MoserEstimate`, as a hypothesis; the exponential upper bound
and the zero case have no cited input left.
-/

/-- **Theorem 1.1** (`theorem:liouville`), assuming only the Moser estimate: for periodic
conductances on a periodic plane graph there is `ε > 0` such that a harmonic function whose set
`{|f| ≤ 1}` has density at least `1 - ε` in the graph balls is constant. -/
theorem UCPlanar.Proved.liouville {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P.toPeriodicGraph c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a :=
  UCPlanar.liouville P c hc hp hMos (UCPlanar.Support.edgeSplitting_holds P.embedding)
    (UCPlanar.Support.unicoherence_holds P)

/-- **Theorem 1.2** (`theorem:uniformly-bounded`), with no cited input: for uniformly elliptic
conductances, a function harmonic on `B_{2n}` with `|f| > 1` on at most `ε |B_{2n}|` vertices
satisfies `max_{B_n} |f| ≤ exp(A √ε n)`. -/
theorem UCPlanar.Proved.uniformlyBounded {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n) :=
  UCPlanar.uniformlyBounded P (UCPlanar.Support.edgeSplitting_holds P.embedding)
    (UCPlanar.Support.unicoherence_holds P)

/-- **Theorem 1.3** (`theorem:zero-case`), with no cited input: for arbitrary positive
conductances, a function harmonic on `B_{2n}` that is nonzero on at most `ε |B_{2n}|` vertices
vanishes on `B_n`. -/
theorem UCPlanar.Proved.zeroCase {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0 :=
  UCPlanar.zeroCase P (UCPlanar.Support.edgeSplitting_holds P.embedding)
    (UCPlanar.Support.unicoherence_holds P)
