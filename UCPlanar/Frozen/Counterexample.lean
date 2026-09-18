import UCPlanar.Support.CrossingHarmonic
import UCPlanar.Support.CrossingThreshold

-- FROZEN-STATEMENT-BEGIN
/-- “For each choice of positive A₁ ≠ A₂ and A₃ > ... there is a choice of A₄ > 0”
with a harmonic function supported on the diagonal.
`ucplanar.tex:380-391 (theorem:counterexample)`.
The function is normalized by h(0,0)=1 and is nonzero at every diagonal site. -/
theorem UCPlanar.Frozen.counterexample (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) (ht : 2*a^2*b^2 / ((a-b)^2*(a+b)) < t) :
    ∃ d : ℝ, 0 < d ∧ ∃ lf : UCPlanar.crossingGraph.LocallyFinite,
      LatticeProb.Network.IsCond UCPlanar.crossingGraph (UCPlanar.crossingConductance a b t d) ∧
      ∃ f : LatticeProb.Site 2 → ℝ,
        @LatticeProb.Network.HarmonicOn _ UCPlanar.crossingGraph lf
          (UCPlanar.crossingConductance a b t d) f Set.univ ∧
        f 0 = 1 ∧ ∀ x, f x ≠ 0 ↔ x 0 = x 1
-- FROZEN-STATEMENT-END
:= by
  let d : ℝ := t*(a-b)^2/(a*b)-2*a*b/(a+b)
  have hd : 0 < d := UCPlanar.Support.fourth_positive a b t ha hb hab ht
  have htpos := UCPlanar.Support.third_positive a b t ha hb hab ht
  refine ⟨d, hd, UCPlanar.crossingLocallyFinite,
    UCPlanar.Support.crossing_isCond a b t d ha hb htpos hd,
    UCPlanar.diagonalFunction a b, ?_, ?_, ?_⟩
  · intro x _
    exact UCPlanar.Support.diagonal_laplacian a b t d ha hb htpos hd
      (UCPlanar.Support.diagonal_balance a b t (ne_of_gt ha) (ne_of_gt hb)
        (ne_of_gt (add_pos ha hb))) x
  · simp [UCPlanar.diagonalFunction]
  · intro x
    have hq := UCPlanar.Support.ratio_nonzero a b ha hb
    by_cases hx : x 0 = x 1
    · simp only [UCPlanar.diagonalFunction, hx, iff_true]
      exact zpow_ne_zero _ hq
    · simp [UCPlanar.diagonalFunction, hx]
