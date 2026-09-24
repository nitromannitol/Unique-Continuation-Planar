import UCPlanar.Frozen.Liouville
import UCPlanar.Frozen.UniformlyBounded
import UCPlanar.Frozen.ZeroCase
import UCPlanar.Frozen.Counterexample

/-!
# Main results

The main theorems of the formalization of *Unique continuation on planar graphs*
(Bou-Rabee, Cooperman and Ganguly, Discrete Analysis 2025:16), stated here in full: the
Liouville theorem (`theorem:liouville`), the exponential upper bound
(`theorem:uniformly-bounded`), the zero case (`theorem:zero-case`), and the non-planar
counterexample (`theorem:counterexample`).

Each theorem below restates its certified counterpart in `UCPlanar/Frozen/` and is proved by
`exact` of it, so the statements displayed in this file are the certified ones.  The
hypotheses named `External.*` are results the paper cites without proof; they are assumed, not
proved, and are listed with their statements in `ASSUMPTIONS.md`.

* `UCPlanar.liouville`: for periodic conductances on a periodic plane graph there is `ε > 0`
  such that a harmonic function whose set `{|f| ≤ 1}` has density at least `1 - ε` in the
  graph balls is constant.
* `UCPlanar.uniformlyBounded`: for uniformly elliptic conductances, a function harmonic on
  `B_{2n}` with `|f| > 1` on at most `ε |B_{2n}|` vertices satisfies
  `max_{B_n} |f| ≤ exp(A √ε n)`.
* `UCPlanar.zeroCase`: for arbitrary positive conductances, a function harmonic on `B_{2n}`
  that is nonzero on at most `ε |B_{2n}|` vertices vanishes on `B_n`.
* `UCPlanar.counterexample`: on the square lattice with crossing diagonal edges there are
  periodic conductances with a harmonic function supported exactly on the diagonal.

All four reduce to the standard axioms (`propext`, `Classical.choice`, `Quot.sound`); see
`UCPlanar/Meta/AxiomsAudit.lean`.
-/

/-- **Theorem 1.1** (`theorem:liouville`).  The certified statement is
`UCPlanar.Frozen.liouville`. -/
theorem UCPlanar.liouville {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P.toPeriodicGraph c)
    (hES : UCPlanar.External.EdgeSplitting P.embedding)
    (hU : UCPlanar.External.Unicoherence P.embedding) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a := by
  exact UCPlanar.Frozen.liouville P c hc hp hMos hES hU

/-- **Theorem 1.2** (`theorem:uniformly-bounded`).  The certified statement is
`UCPlanar.Frozen.uniformlyBounded`. -/
theorem UCPlanar.uniformlyBounded {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting P.embedding)
    (hU : UCPlanar.External.Unicoherence P.embedding) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ Θ : ℝ, 1 < Θ →
      ∃ ε₀ A : ℝ, 0 < ε₀ ∧ 0 < A ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (c : V → V → ℝ),
      LatticeProb.Network.IsCond P.graph c → UCPlanar.UniformlyElliptic P.graph c lam (Θ*lam) →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 1 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, |f x| ≤ Real.exp (A * Real.sqrt ε * n) := by
  exact UCPlanar.Frozen.uniformlyBounded P hES hU

/-- **Theorem 1.3** (`theorem:zero-case`).  The certified statement is
`UCPlanar.Frozen.zeroCase`. -/
theorem UCPlanar.zeroCase {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (hES : UCPlanar.External.EdgeSplitting P.embedding)
    (hU : UCPlanar.External.Unicoherence P.embedding) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε < ε₀ →
      ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f (LatticeProb.Graph.closedBall P.graph o (2*n)) →
        (UCPlanar.exceptionalCount (P.toPeriodicGraph.ball o (2*n)) f 0 : ℝ) ≤
          ε * (P.toPeriodicGraph.ball o (2*n)).card →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0 := by
  exact UCPlanar.Frozen.zeroCase P hES hU

/-- **Theorem 5.1** (`theorem:counterexample`).  The certified statement is
`UCPlanar.Frozen.counterexample`. -/
theorem UCPlanar.counterexample (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (ht : 2*a^2*b^2 / ((a-b)^2*(a+b)) < t) :
    ∃ d : ℝ, 0 < d ∧ ∃ lf : UCPlanar.crossingGraph.LocallyFinite,
      LatticeProb.Network.IsCond UCPlanar.crossingGraph (UCPlanar.crossingConductance a b t d) ∧
      ∃ f : LatticeProb.Site 2 → ℝ,
        @LatticeProb.Network.HarmonicOn _ UCPlanar.crossingGraph lf
          (UCPlanar.crossingConductance a b t d) f Set.univ ∧
        f 0 = 1 ∧ ∀ x, f x ≠ 0 ↔ x 0 = x 1 := by
  exact UCPlanar.Frozen.counterexample a b t ha hb hab ht
