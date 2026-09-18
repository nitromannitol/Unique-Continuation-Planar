import UCPlanar.Support.Approximation
import UCPlanar.Support.Poly.Assembly
import UCPlanar.External.MoserEstimate

-- FROZEN-STATEMENT-BEGIN
/-- “For any α > 0, there is a constant c(α) > 0 ... there exists a polynomial p”
with error at most α^m times the outer supremum norm on each lattice orbit.
The proof of the derivative bound cites a discrete Moser estimate, which enters as the
hypothesis `hMos`; the discrete Caccioppoli inequality it iterates is proved here.
`ucplanar.tex:438-445 (lemma:poly-approx)`. -/
theorem UCPlanar.Frozen.polynomialApproximation {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c) :
    ∀ α : ℝ, 0 < α → ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → ∀ m : ℕ, (m : ℝ) ≤ δ*R →
      ∀ (v : V) (f : V → ℝ),
        LatticeProb.Network.HarmonicOn P.graph c f (P.square (3*R) : Set V) →
        P.PolynomialApproximation R m v f α δ
-- FROZEN-STATEMENT-END
:= by
  intro α hα
  have hα2 : (0:ℝ) < min α 2 := lt_min hα (by norm_num)
  obtain ⟨δ, R₀, hδ, hR₀, h⟩ :=
    UCPlanar.Support.polynomialApproximation_aux P c hc hp hMos (min α 2) hα2
      (min_le_right _ _)
  refine ⟨δ, R₀, hδ, hR₀, ?_⟩
  intro R hR m hm v f hf
  obtain ⟨p, hdeg, hbound⟩ := h R hR m hm v f hf
  refine ⟨p, hdeg, ?_⟩
  intro x hx hox
  refine le_trans (hbound x hx hox) ?_
  have hs0 : (0:ℝ) ≤ UCPlanar.supNorm (P.square (3 * R)) f := by
    rw [UCPlanar.supNorm]
    exact NNReal.coe_nonneg _
  have hpow : (min α 2) ^ m ≤ α ^ m :=
    pow_le_pow_left₀ (le_of_lt hα2) (min_le_left _ _) m
  exact mul_le_mul_of_nonneg_right hpow hs0
