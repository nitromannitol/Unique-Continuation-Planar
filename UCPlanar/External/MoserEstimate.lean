import UCPlanar.Support.Poly.Difference

/-!
# Cited input: the discrete Moser estimate

Records, as a `Prop`-valued hypothesis, Delmotte's discrete Moser estimate on a periodic
network with a periodic conductance: for nested squares `Q_r ⊆ Q_s`, a function harmonic on `Q_s` has supremum on `Q_r`
controlled by `C / (s - r)` times its `ℓ²` norm on `Q_s`, with `C` independent of the two
scales. Cited from Delmotte, *Parabolic Harnack inequality and estimates of Markov chains on
graphs*, Rev. Mat. Iberoamericana 15 (1999), Prop. 5.3.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The discrete Moser estimate on a periodic network, in the form the derivative bound
consumes.  For a conductance `c` on the graph (symmetric, positive on edges, zero off edges)
that is invariant under the translation lattice, nested squares `Q_r ⊆ Q_s` and a function
harmonic on `Q_s`, the supremum of `f` over `Q_r` is at most `C / (s - r)` times the `ℓ²`
norm of `f` over `Q_s`, with a constant that depends on the network but not on the two
scales.  The two conditions on `c` are those of Delmotte's setting (uniformly elliptic
conductances on a graph of polynomial growth).  Delmotte, *Parabolic
Harnack inequality and estimates of Markov chains on graphs*, Rev. Mat. Iberoamericana 15
(1999) 181-232, Proposition 5.3; cited at `ucplanar.tex:441-446`. -/
def UCPlanar.External.MoserEstimate {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) : Prop :=
  LatticeProb.Network.IsCond P.graph c → P.PeriodicConductance c →
  ∃ C : ℝ, 0 < C ∧
    ∀ r s : ℝ, 0 < r → r < s → ∀ f : V → ℝ,
      (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) →
      ∀ x ∈ P.square r,
        |f x| ≤ (C / (s - r)) * Real.sqrt (∑ y ∈ P.square s, f y ^ 2)
-- FROZEN-STATEMENT-END
