/-
Weighted graph and finite-domain density vocabulary.
Graph balls, conductances and harmonicity are provided by the shared library.
-/
import LatticeProb.Network.Basic
import LatticeProb.Site

open scoped Classical

/-- The fraction of a finite set on which `|f| ≤ a`, with value zero on the empty set. -/
noncomputable def UCPlanar.boundedDensity {V : Type*} (S : Finset V) (f : V → ℝ)
    (a : ℝ) : ℝ :=
  ((S.filter (fun x => |f x| ≤ a)).card : ℝ) / S.card

/-- The number of vertices of a finite set on which `|f| > a`. -/
noncomputable def UCPlanar.exceptionalCount {V : Type*} (S : Finset V) (f : V → ℝ)
    (a : ℝ) : ℕ :=
  (S.filter (fun x => a < |f x|)).card

/-- Strict uniform bounds on the edge conductances, as in `ucplanar.tex:176`. -/
def UCPlanar.UniformlyElliptic {V : Type*} (G : SimpleGraph V) (c : V → V → ℝ)
    (lam big : ℝ) : Prop :=
  0 < lam ∧ lam < big ∧ ∀ x y, G.Adj x y → lam < c x y ∧ c x y < big
