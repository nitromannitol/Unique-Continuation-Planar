import UCPlanar.Support.Periodic
import UCPlanar.Support.PlanarCycle
import UCPlanar.Support.PlanarTopological
import UCPlanar.Support.TopoInterleave

/-!
# The topological lemma on a cycle

Proves `ucplanar.tex`'s `lemma:topological-lemma` outright: for a cycle `γ` in a periodic plane
graph of bounded degree and face size, and disjoint sign classes `P`, `M` on the cycle's inner
region each reaching the boundary through every uncovered arc, some exceptional set `Z` of at
most an `α`-fraction of `γ` absorbs every arc where the two signs fail to reach the boundary.
The proof (`Support.topological_of_crosscuts`) reduces this to a common vertex among interleaved
face-boundary walks.
-/

open scoped Classical

-- FROZEN-STATEMENT-BEGIN
/-- “Let γ be a cycle ... let sets Z, P, M be disjoint” with face paths to
both signs and each sign component meeting γ ∖ Z; “|Z| ≤ α |γ|”.
`ucplanar.tex:222-231 (lemma:topological-lemma)`.
The constant depends on the uniform degree and face-size bounds. -/
theorem UCPlanar.Frozen.topological {V : Type*} :
    ∀ d L : ℕ, ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ Q : UCPlanar.PeriodicPlaneGraph V,
      (∀ x, Q.graph.degree x ≤ d) → Q.embedding.FaceBound L →
      ∀ (o : V) (γ : Q.graph.Walk o o), γ.IsCycle →
      ∀ (Z : Finset V) (P M : Set V),
        Disjoint (Z : Set V) P → Disjoint (Z : Set V) M → Disjoint P M →
        Z ⊆ γ.support.toFinset →
        P ⊆ Q.embedding.cycleRegion γ → M ⊆ Q.embedding.cycleRegion γ →
        (∀ z ∈ Z, Q.embedding.FacePathToSigns P M z) →
        UCPlanar.ComponentsMeetBoundary Q.graph P ((γ.support.toFinset : Set V) \ Z) →
        UCPlanar.ComponentsMeetBoundary Q.graph M ((γ.support.toFinset : Set V) \ Z) →
        (Z.card : ℝ) ≤ α * γ.support.toFinset.card
-- FROZEN-STATEMENT-END
:= by
  intro d L
  obtain ⟨α, hα0, hα1, hmain⟩ := UCPlanar.Support.topological_of_crosscuts d L
  refine ⟨α, hα0, hα1, ?_⟩
  intro Q hd hL o γ hγ
  refine hmain Q hd hL o γ hγ ?_
  intro i j k l hij hjk hkl hl p q hp hq
  exact UCPlanar.Support.exists_common_vertex_of_interleaved Q.embedding γ hγ
    (p.length + q.length) i j k l hij hjk hkl hl p q le_rfl hp hq
