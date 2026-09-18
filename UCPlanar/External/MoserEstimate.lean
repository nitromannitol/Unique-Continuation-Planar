import UCPlanar.Support.Poly.Difference

-- FROZEN-STATEMENT-BEGIN
/-- The discrete Moser estimate on a periodic network, in the form the derivative bound
consumes.  For nested squares `Q_r ⊆ Q_s` and a function harmonic on `Q_s`, the supremum of
`f` over `Q_r` is at most `C / (s - r)` times the `ℓ²` norm of `f` over `Q_s`, with a
constant that depends on the network but not on the two scales.  Delmotte, *Parabolic
Harnack inequality and estimates of Markov chains on graphs*, Rev. Mat. Iberoamericana 15
(1999) 181-232, Proposition 5.3; cited at `ucplanar.tex:452-457`. -/
def UCPlanar.External.MoserEstimate {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ r s : ℝ, 0 < r → r < s → ∀ f : V → ℝ,
      (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) →
      ∀ x ∈ P.square r,
        |f x| ≤ (C / (s - r)) * Real.sqrt (∑ y ∈ P.square s, f y ^ 2)
-- FROZEN-STATEMENT-END
