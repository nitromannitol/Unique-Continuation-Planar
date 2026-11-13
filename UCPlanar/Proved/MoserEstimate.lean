import UCPlanar.Support.Moser.Estimate
import UCPlanar.Proved.Main
import UCPlanar.Frozen.PolynomialApproximation
import UCPlanar.Frozen.ThreeBall
import UCPlanar.Frozen.PeriodicLowerBound

/-!
# The Moser estimate proved, and the theorems that cited it

The discrete Moser estimate `UCPlanar.External.MoserEstimate` holds for every periodic graph and
every conductance on it (`UCPlanar.Support.moserEstimate_holds`): a discrete Sobolev bound
along lattice orbits, together with the iterated discrete Caccioppoli inequality, bounds the
supremum of a harmonic function on `Q_r` by `C / (s - r)` times its `ℓ²` norm on `Q_s`.

The polynomial approximation lemma, the three-ball bound and the periodic exponential lower
bound are restated below without the Moser hypothesis. Theorem 1.1 is restated with no cited
input left: the plane-topology inputs are proved in `UCPlanar.Proved.Main`, and the Moser
estimate here.
-/

/-- **The discrete Moser estimate**, for every periodic graph and every conductance: for a
conductance that is invariant under the translation lattice, a function harmonic on `Q_s` has
supremum on `Q_r` at most `C / (s - r)` times its `ℓ²` norm on `Q_s`. -/
theorem UCPlanar.Proved.moserEstimate {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) : UCPlanar.External.MoserEstimate P c :=
  UCPlanar.Support.moserEstimate_holds P c

/-- **Theorem 1.1** (`theorem:liouville`), with no cited input: for periodic conductances on a
periodic plane graph there is `ε > 0` such that a harmonic function whose set `{|f| ≤ 1}` has
density at least `1 - ε` in the graph balls is constant. -/
theorem UCPlanar.Proved.liouville_of_periodic {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a :=
  UCPlanar.Proved.liouville P c hc hp (UCPlanar.Proved.moserEstimate P.toPeriodicGraph c)

/-- **Polynomial approximation** (`lemma:poly-approx`), with no cited input: on scales large
enough relative to `α`, a function harmonic on `Q_{3R}` is approximated on each lattice orbit by a
low-degree polynomial to within `α ^ m` times the outer supremum norm. -/
theorem UCPlanar.Proved.polynomialApproximation {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c) :
    ∀ α : ℝ, 0 < α → ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ m : ℕ, (m : ℝ) ≤ δ*R →
      ∀ (v : V) (f : V → ℝ),
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (3*R) : Set V) →
        P.PolynomialApproximation R m v f α δ :=
  UCPlanar.Frozen.polynomialApproximation P c hc hp (UCPlanar.Proved.moserEstimate P c)

/-- **The three-ball bound** (`prop:three-ball`), with no cited input: a function harmonic and
bounded by `M` on `Q_{kN}`, with density at least `1 - ε` on `Q_N`, satisfies
`|f| ≤ C √M + C exp(-c₀ N) M` on `Q_{2N}`. -/
theorem UCPlanar.Proved.threeBall {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : V → V → ℝ,
      LatticeProb.Network.IsCond P.graph c → P.PeriodicConductance c →
      ∃ (k : ℕ) (c₀ C : ℝ), 4 ≤ k ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ (f : V → ℝ) (M : ℝ), 0 ≤ M →
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (k*N) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (P.square N) f 1 →
        (∀ x ∈ P.square (k*N), |f x| ≤ M) →
        ∀ x ∈ P.square (2*N), |f x| ≤ C*Real.sqrt M + C*Real.exp (-c₀*N)*M := by
  obtain ⟨ε, hε, h⟩ := UCPlanar.Frozen.threeBall P
  exact ⟨ε, hε, fun c hc hp => h c hc hp (UCPlanar.Proved.moserEstimate P c)⟩

/-- **The periodic exponential lower bound** (`theorem:lower-bound`), with no cited input: a
harmonic function with density at least `1 - ε` on every scale from `√N` to `2N` and with a
value at least `2` in `Q_{√N}` has supremum at least `exp(bN)` on `Q_N`. -/
theorem UCPlanar.Proved.periodicLowerBound {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (c : V → V → ℝ) (hc : LatticeProb.Network.IsCond P.graph c)
    (hp : P.PeriodicConductance c) :
    ∃ b : ℝ, 0 < b ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ N : ℕ, N₀ ≤ N → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∃ x ∈ P.square (Nat.sqrt N), 2 ≤ f x) →
        (∀ K : ℕ, Real.sqrt N ≤ K → K ≤ 2*N →
          1 - ε ≤ UCPlanar.boundedDensity (P.square K) f 1) →
        Real.exp (b*N) ≤ UCPlanar.supNorm (P.square N) f :=
  UCPlanar.Frozen.periodicLowerBound P c hc hp (UCPlanar.Proved.moserEstimate P c)
