import UCPlanar.Basic
import UCPlanar.Support.Periodic
import UCPlanar.External.MoserEstimate
import UCPlanar.Support.ThreeAssembly

-- FROZEN-STATEMENT-BEGIN
/-- “max on Q₂ₙ |f| ≤ CM^{1/2} + C exp(-cN) M.”
`ucplanar.tex:468-480 (prop:three-ball)`.
The function is harmonic and bounded by M on Q_{kN} in the fixed periodic network, for an
outer radius k ≥ 4 determined by the network.  The proof applies the discrete Remez inequality
(proved in `UCPlanar.Support.RemezDiscrete`) to the approximating polynomial, and the
polynomial approximation lemma to the function; the discrete Moser estimate remains a cited
input. -/
theorem UCPlanar.Frozen.threeBall {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : V → V → ℝ,
      LatticeProb.Network.IsCond P.graph c → P.PeriodicConductance c →
      UCPlanar.External.MoserEstimate P c →
      ∃ (k : ℕ) (c₀ C : ℝ), 4 ≤ k ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ (f : V → ℝ) (M : ℝ), 0 ≤ M →
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (k*N) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (P.square N) f 1 →
        (∀ x ∈ P.square (k*N), |f x| ≤ M) →
        ∀ x ∈ P.square (2*N), |f x| ≤ C*Real.sqrt M + C*Real.exp (-c₀*N)*M
-- FROZEN-STATEMENT-END
:= UCPlanar.Support.Three.threeBall_assembled P
