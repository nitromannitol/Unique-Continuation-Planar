/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Topology/PlaneTopology.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `LatticeProb.Topology` is renamed `UCPlanar.Vendored.Topology`, and the module
   paths of local imports are changed. -/
import Mathlib

/-!
# Plane topology: simple loops, local connectedness, cut points, rectangles and dyadic squares

Definitions only; this module states and proves no theorem.

* `IsSimpleLoop`: a simple loop (Jordan curve) in `ℂ`.
* `IsLocallyConnectedSet`: a locally connected subset of `ℂ`.
* `IsCutPoint`: a cut point of a subset of `ℂ`.
* `connectedComponentsIn`: the set of connected components of a set.
* `IsClosedRectangle`, `closedDyadicSquare`, `IsClosedDyadicSquare`: closed axis-parallel rectangles and closed
  dyadic squares.
* `IsSmoothBoundedOpen`: a bounded open set with `C^∞` boundary.
* `TorhorstSimpleLoop`: Torhorst's conclusion for locally connected plane continua without cut points.

Sources. Simple loops, local connectedness and cut points: Bou-Rabee and Gwynne, *Harmonic balls in Liouville
quantum gravity* (arXiv:2208.11795), Definitions 10.2-10.4. Smooth bounded open sets: Gilbarg and Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Section 6.2. Torhorst's theorem: Torhorst (1931), in the
form of Jolivet, Loridant and Luo, *A numerical scale for non-locally connected planar continua*
(arXiv:1411.6776v1), Theorem 3.1.
-/

namespace UCPlanar.Vendored.Topology

open Set

/-- A *simple loop* (Jordan curve) in `ℂ` is the image `Γ` of a continuous injective map `φ` from the unit circle
`Circle`, i.e. `Γ = range φ` (Bou-Rabee and Gwynne, Definition 10.2). -/
def IsSimpleLoop (Γ : Set ℂ) : Prop :=
  ∃ φ : Circle → ℂ, Continuous φ ∧ Function.Injective φ ∧ range φ = Γ

/-- A set `X ⊆ ℂ` is *locally connected* if every neighbourhood of each `x ∈ X` with respect to `X` contains a
connected neighbourhood of `x` with respect to `X` (Bou-Rabee and Gwynne, Definition 10.3). -/
def IsLocallyConnectedSet (X : Set ℂ) : Prop :=
  ∀ x ∈ X, ∀ N ∈ nhdsWithin x X, ∃ V ∈ nhdsWithin x X, V ⊆ N ∩ X ∧ IsConnected V

/-- A point `a` of a set `A ⊆ ℂ` is a *cut point* of `A` if `a ∈ A` and `A \ {a}` is not connected
(Bou-Rabee and Gwynne, Definition 10.4). The standing hypotheses on `A` (compact, connected, locally connected)
are carried by the statements that use the notion. -/
def IsCutPoint (A : Set ℂ) (a : ℂ) : Prop :=
  a ∈ A ∧ ¬ IsPreconnected (A \ {a})

/-- The set of connected components of a set `F` in a topological space: `connectedComponentIn F x` for `x ∈ F`. -/
def connectedComponentsIn {α : Type*} [TopologicalSpace α] (F : Set α) : Set (Set α) :=
  connectedComponentIn F '' F

/-- A closed axis-parallel rectangle `[a₁, a₂] × [b₁, b₂] ⊆ ℂ` with `a₁ < a₂` and `b₁ < b₂`. -/
def IsClosedRectangle (R : Set ℂ) : Prop :=
  ∃ a₁ a₂ b₁ b₂ : ℝ, a₁ < a₂ ∧ b₁ < b₂ ∧ R = Icc a₁ a₂ ×ℂ Icc b₁ b₂

/-- The closed dyadic square `[j 2⁻ⁿ, (j+1) 2⁻ⁿ] × [k 2⁻ⁿ, (k+1) 2⁻ⁿ]` of side length `2⁻ⁿ`, for `n, j, k ∈ ℤ`. -/
def closedDyadicSquare (n j k : ℤ) : Set ℂ :=
  Icc ((j : ℝ) * 2 ^ (-n)) ((j + 1) * 2 ^ (-n)) ×ℂ Icc ((k : ℝ) * 2 ^ (-n)) ((k + 1) * 2 ^ (-n))

/-- A *closed dyadic square*: a set `closedDyadicSquare n j k` for some `n, j, k ∈ ℤ`. -/
def IsClosedDyadicSquare (S : Set ℂ) : Prop :=
  ∃ n j k : ℤ, S = closedDyadicSquare n j k

open scoped ContDiff in
/-- A *smooth bounded open set*: `O` is bounded and has a `C^∞` defining function, i.e. `O = {ρ < 0}` for some
`ρ ∈ C^∞(ℂ, ℝ)` whose differential does not vanish on `{ρ = 0}` (so that `{ρ = 0} = ∂O`). This is the usual notion of
a bounded open set with `C^∞` boundary (equivalently, `∂O` is locally the graph of a `C^∞` function with `O` on one
side; Gilbarg and Trudinger, Section 6.2). `O` need not be connected. -/
def IsSmoothBoundedOpen (O : Set ℂ) : Prop :=
  Bornology.IsBounded O ∧
    ∃ ρ : ℂ → ℝ, ContDiff ℝ ∞ ρ ∧ O = {z | ρ z < 0} ∧ ∀ z, ρ z = 0 → fderiv ℝ ρ z ≠ 0

/-- Torhorst's conclusion for plane continua: for a nondegenerate compact connected locally connected set `K ⊆ ℂ`
without cut points, the frontier of every connected component of `ℂ \ K` is a simple loop (Torhorst (1931), in the
form of Jolivet, Loridant and Luo, arXiv:1411.6776v1, Theorem 3.1, printed p. 6). -/
def TorhorstSimpleLoop : Prop :=
  ∀ K : Set ℂ, IsCompact K → IsConnected K → K.Nontrivial → IsLocallyConnectedSet K →
    (∀ a : ℂ, ¬ IsCutPoint K a) → ∀ C ∈ connectedComponentsIn Kᶜ, IsSimpleLoop (frontier C)

end UCPlanar.Vendored.Topology
