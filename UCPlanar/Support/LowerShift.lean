/-
The three-ball inequality at a square centred at a lattice point.

The chain of three-ball inequalities that produces the exponential lower bound is run at squares
centred at the successive maximum points of the function, not at the origin.  A lattice
translation is an automorphism of the graph which preserves the conductance and translates the
coordinate realization, so the translated inequality is the frozen one applied to the translated
function.
-/
import UCPlanar.Frozen.ThreeBall
import UCPlanar.Support.Poly.Elliptic
import UCPlanar.Support.Poly.Square

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Lower

/-- The vertices of the geometric square of radius `R` centred at the drawing of the lattice
vector `a`. -/
noncomputable def squareAt {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (a : LatticeProb.Site 2) (R : ℝ) : Finset V :=
  (P.square R).image (P.shift a)

theorem mem_squareAt {V : Type*} (P : UCPlanar.PeriodicGraph V) (a : LatticeProb.Site 2)
    (R : ℝ) (x : V) : x ∈ squareAt P a R ↔ P.shift (-a) x ∈ P.square R := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx, ← P.shift_add, neg_add_cancel, P.shift_zero]
    exact hy
  · intro hx
    refine Finset.mem_image.mpr ⟨P.shift (-a) x, hx, ?_⟩
    rw [← P.shift_add, add_neg_cancel, P.shift_zero]

theorem shift_mem_squareAt {V : Type*} (P : UCPlanar.PeriodicGraph V) (a : LatticeProb.Site 2)
    (R : ℝ) (y : V) (hy : y ∈ P.square R) : P.shift a y ∈ squareAt P a R :=
  Finset.mem_image.mpr ⟨y, hy, rfl⟩

theorem card_squareAt {V : Type*} (P : UCPlanar.PeriodicGraph V) (a : LatticeProb.Site 2)
    (R : ℝ) : (squareAt P a R).card = (P.square R).card :=
  Finset.card_image_of_injective _ (UCPlanar.Support.shift_injective P a)

theorem squareAt_mono {V : Type*} (P : UCPlanar.PeriodicGraph V) (a : LatticeProb.Site 2)
    {r s : ℝ} (hrs : r ≤ s) : squareAt P a r ⊆ squareAt P a s := by
  intro x hx
  rw [mem_squareAt] at hx ⊢
  exact UCPlanar.Support.square_mono P hrs hx

/-- Harmonicity transports along a lattice translation. -/
theorem harmonicOn_shift {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : P.PeriodicConductance c) (f : V → ℝ) (a : LatticeProb.Site 2) (R : ℝ)
    (hf : LatticeProb.Network.HarmonicOn P.graph c f (squareAt P a R : Set V)) :
    LatticeProb.Network.HarmonicOn P.graph c (fun y => f (P.shift a y)) (P.square R : Set V) := by
  intro x hx
  rw [UCPlanar.Support.netLaplacian_shift P c hc f a x]
  exact hf (P.shift a x) (by
    simp only [Finset.mem_coe]
    exact shift_mem_squareAt P a R x (by simpa using hx))

/-- The density transports along a lattice translation. -/
theorem boundedDensity_shift {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (a : LatticeProb.Site 2) (R t : ℝ) :
    UCPlanar.boundedDensity (P.square R) (fun y => f (P.shift a y)) t
      = UCPlanar.boundedDensity (squareAt P a R) f t := by
  classical
  have hfil : (squareAt P a R).filter (fun x => |f x| ≤ t)
      = ((P.square R).filter (fun y => |f (P.shift a y)| ≤ t)).image (P.shift a) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, squareAt]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hval⟩
      exact ⟨y, ⟨hy, hval⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hval⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, hval⟩
  simp only [UCPlanar.boundedDensity, hfil,
    Finset.card_image_of_injective _ (UCPlanar.Support.shift_injective P a), card_squareAt]

/-- **The three-ball inequality at a square centred at a lattice point.**  This is the frozen
proposition applied to the translated function; the outer radius, the exponential rate and the
constant are the ones the frozen statement supplies, and none of them depends on the centre. -/
theorem threeBall_shift {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : V → V → ℝ,
      LatticeProb.Network.IsCond P.graph c → P.PeriodicConductance c →
      UCPlanar.External.MoserEstimate P c →
      ∃ (k : ℕ) (c₀ C : ℝ), 4 ≤ k ∧ 0 < c₀ ∧ 0 < C ∧
      ∀ N : ℕ, 0 < N → ∀ (f : V → ℝ) (M : ℝ), 0 ≤ M → ∀ a : LatticeProb.Site 2,
        LatticeProb.Network.HarmonicOn P.graph c f (squareAt P a ((k:ℝ)*(N:ℝ)) : Set V) →
        1 - ε ≤ UCPlanar.boundedDensity (squareAt P a (N : ℝ)) f 1 →
        (∀ x ∈ squareAt P a ((k:ℝ)*(N:ℝ)), |f x| ≤ M) →
        ∀ x ∈ squareAt P a (2*(N:ℝ)), |f x| ≤ C*Real.sqrt M + C*Real.exp (-c₀*N)*M := by
  obtain ⟨ε, hε, hmain⟩ := UCPlanar.Frozen.threeBall P
  refine ⟨ε, hε, ?_⟩
  intro c hc hp hM
  obtain ⟨k, c₀, C, hk, hc₀, hC, hbody⟩ := hmain c hc hp hM
  refine ⟨k, c₀, C, hk, hc₀, hC, ?_⟩
  intro N hN f M hM0 a hharm hdens hbound x hx
  have hkey := hbody N hN (fun y => f (P.shift a y)) M hM0
    (harmonicOn_shift P c hp f a ((k:ℝ)*(N:ℝ)) hharm)
    (by rw [boundedDensity_shift]; exact hdens)
    (fun y hy => hbound (P.shift a y) (shift_mem_squareAt P a _ y hy))
  have hx' : P.shift (-a) x ∈ P.square (2*(N:ℝ)) := (mem_squareAt P a _ x).mp hx
  have := hkey (P.shift (-a) x) hx'
  rwa [← P.shift_add, add_neg_cancel, P.shift_zero] at this

end UCPlanar.Support.Lower
