import UCPlanar.Support.ZeroRemark
import UCPlanar.Support.SurroundExists
import UCPlanar.Proved.Unicoherence
import UCPlanar.Proved.EdgeSplitting

/-!
# The remark after Theorem 1.3

The remark following `theorem:zero-case` (`ucplanar.tex:306-309`) observes that the argument
uses the density hypothesis only through Step 2: a bound `c n` on the number of nonzero vertices
near the sphere of one radius `m ∈ [3n/2, 2n - 2C]` already forces `f ≡ 0` on `B_n`, and a
globally harmonic function with such a bound for arbitrarily large `n` vanishes identically.

The vertices counted are those of `B_{2n}` within `R` of the sphere of radius `m`, where `R` is a
constant of the periodic plane graph playing the role of the paper's buffer `C_𝓕`. Harmonicity
is asked on the ball `B_{K n}` for a graph constant `K ≥ 2`, as in `zeroCase_of_surrounding`:
the cycle of Step 3 is confined to the buffer of the sphere of radius `m`, and the region it
encloses is controlled only up to a constant factor of its radius. For a globally harmonic
function this is no restriction.
-/

/-- **The remark after Theorem 1.3, first sentence.** On a periodic plane graph there are
constants `K`, `R`, `c₀ > 0` and `n₀`, depending only on the graph, such that a function
harmonic on `B_{K n}` for arbitrary positive conductances, with at most `c₀ n` nonzero vertices
of `B_{2n}` within `R` of the sphere of one radius `m` with `3n ≤ 2m` and `m + R ≤ 2n`,
vanishes on `B_n`. -/
theorem UCPlanar.Proved.zeroCase_of_sparseShell {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ K R : ℕ, 2 ≤ K ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond P.graph c →
      ∀ (o : V) (n : ℕ), n₀ ≤ n → ∀ f : V → ℝ,
        LatticeProb.Network.HarmonicOn P.graph c f
          (LatticeProb.Graph.closedBall P.graph o (K*n)) →
        ∀ m : ℕ, 3 * n ≤ 2 * m → m + R ≤ 2 * n →
        ((((P.toPeriodicGraph.ball o (2*n)).filter (fun x => f x ≠ 0 ∧
            m ≤ P.graph.dist o x + R ∧ P.graph.dist o x ≤ m + R)).card : ℝ) ≤ c₀ * n) →
        ∀ x ∈ P.toPeriodicGraph.ball o n, f x = 0 := by
  obtain ⟨K, r, hK, hsur⟩ := UCPlanar.Support.exists_hasSurroundingCycles P
    (UCPlanar.Support.edgeSplitting_holds P.embedding) (UCPlanar.Support.unicoherence_holds P)
  obtain ⟨c₀, hc₀, n₀, hn₀, hmain⟩ := UCPlanar.Support.zeroCase_of_sparseShell_core P K r hsur
  exact ⟨K, 2 * r, hK, c₀, hc₀, n₀, hn₀, hmain⟩

/-- **The remark after Theorem 1.3, second sentence.** On a periodic plane graph there are
constants `R` and `c₀ > 0`, depending only on the graph, such that a function harmonic on the
whole graph for arbitrary positive conductances, which for arbitrarily large `n` has at most
`c₀ n` nonzero vertices of `B_{2n}` within `R` of the sphere of some radius `m` with `3n ≤ 2m`
and `m + R ≤ 2n`, is identically zero. -/
theorem UCPlanar.Proved.eq_zero_of_sparseShells {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    ∃ R : ℕ, ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (c : V → V → ℝ), LatticeProb.Network.IsCond P.graph c →
      ∀ (o : V) (f : V → ℝ), LatticeProb.Network.HarmonicOn P.graph c f Set.univ →
        (∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ m : ℕ, 3 * n ≤ 2 * m ∧ m + R ≤ 2 * n ∧
          ((((P.toPeriodicGraph.ball o (2*n)).filter (fun x => f x ≠ 0 ∧
            m ≤ P.graph.dist o x + R ∧ P.graph.dist o x ≤ m + R)).card : ℝ) ≤ c₀ * n)) →
        ∀ x, f x = 0 := by
  obtain ⟨K, R, -, c₀, hc₀, n₀, -, hmain⟩ := UCPlanar.Proved.zeroCase_of_sparseShell P
  refine ⟨R, c₀, hc₀, ?_⟩
  intro c hc o f hharm hshell x
  obtain ⟨n, hn, m, hm1, hm2, hcount⟩ := hshell (max n₀ (P.graph.dist o x))
  refine hmain c hc o n (le_trans (le_max_left _ _) hn) f (fun z _ => hharm z (Set.mem_univ z))
    m hm1 hm2 hcount x ?_
  exact (UCPlanar.Support.mem_ball_iff_dist P.toPeriodicGraph o x n).mpr
    (le_trans (le_max_right _ _) hn)
