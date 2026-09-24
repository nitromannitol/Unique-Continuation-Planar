/-
The lattice coordinates of an orbit: the two generators span the period lattice, and the period
map distorts lengths boundedly in the forward direction.
-/
import UCPlanar.Support.Poly.Bridge
import UCPlanar.Support.ZeroVolume

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- **The two generators span the period lattice.**  Every lattice vector is the combination of
`e₁` and `e₂` with its own coordinates. -/
theorem site_eq_smul (k : LatticeProb.Site 2) :
    k = (k 0) • UCPlanar.Support.e₁ + (k 1) • UCPlanar.Support.e₂ := by
  funext i
  fin_cases i <;> simp [UCPlanar.Support.e₁, UCPlanar.Support.e₂]

/-- **The period map distorts lengths boundedly.**  The forward companion of
`exists_lattice_count`: the drawing of a lattice vector is at most a fixed multiple of its
length. -/
theorem exists_period_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖ := by
  classical
  set A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    LinearMap.toContinuousLinearMap (P.period : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) with hA
  refine ⟨‖A‖, norm_nonneg _, ?_⟩
  intro u
  have h := A.le_opNorm u
  simpa [hA, LinearMap.coe_toContinuousLinearMap'] using h

/-- **Re-basing an orbit at a corner of the square.**  Given a square `Q_ρ` and a vertex `v`,
there are a point `v'` of the orbit of `v` and a natural number `N` of size `2Kρ + 1` such that
every orbit point of `Q_ρ` is reached from `v'` by a lattice translation whose two coordinates
are non-negative and at most `2N`.  This is what replaces the paper's choice of the orbit point
closest to the origin, and it is what puts the Newton interpolation in the lattice quadrant. -/
theorem exists_rebase {V : Type*} (P : UCPlanar.PeriodicGraph V) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ (a : Fin 2 → ℤ) (M : ℝ), ‖P.period (fun j => (a j : ℝ))‖ ≤ M →
      ∀ j, |(a j : ℝ)| ≤ K * M)
    (v : V) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ (v' : V) (N : ℕ), (N : ℝ) ≤ 2 * K * ρ + 1 ∧ P.OnOrbit v v' ∧
      ∀ x ∈ P.square ρ, P.OnOrbit v x →
        ∃ a b : ℕ, a ≤ 2*N ∧ b ≤ 2*N ∧
          P.shift ((a : ℤ) • UCPlanar.Support.e₁ + (b : ℤ) • UCPlanar.Support.e₂) v' = x := by
  classical
  set N : ℕ := ⌈2 * K * ρ⌉₊ with hNdef
  have hN : (N : ℝ) ≤ 2 * K * ρ + 1 := by
    have h := Nat.ceil_lt_add_one (a := 2*K*ρ) (by positivity)
    rw [hNdef]
    linarith
  by_cases hS : ∃ x, x ∈ P.square ρ ∧ P.OnOrbit v x
  · obtain ⟨x₀, hx₀, k₀, hk₀⟩ := hS
    refine ⟨P.shift (k₀ + (-(N:ℤ)) • UCPlanar.Support.e₁ + (-(N:ℤ)) • UCPlanar.Support.e₂) v, N,
      hN, ⟨_, rfl⟩, ?_⟩
    intro x hx hox
    obtain ⟨k, hk⟩ := hox
    have hnormle : ∀ y ∈ P.square ρ, ‖P.pos y‖ ≤ ρ := by
      intro y hy
      refine (pi_norm_le_iff_of_nonneg hρ).mpr ?_
      intro i
      simpa [Real.norm_eq_abs] using (UCPlanar.Support.mem_square_iff P ρ y).mp hy i
    have h1 : P.period (fun j => (k j : ℝ)) = P.pos x - P.pos v := by
      have h := P.pos_shift k v
      rw [hk] at h
      linear_combination (norm := abel) -h
    have h2 : P.period (fun j => (k₀ j : ℝ)) = P.pos x₀ - P.pos v := by
      have h := P.pos_shift k₀ v
      rw [hk₀] at h
      linear_combination (norm := abel) -h
    have hdiff : P.period (fun j => (((k - k₀) j : ℤ) : ℝ)) = P.pos x - P.pos x₀ := by
      rw [UCPlanar.Support.period_sub, h1, h2]
      abel
    have hnorm : ‖P.period (fun j => (((k - k₀) j : ℤ) : ℝ))‖ ≤ 2 * ρ := by
      rw [hdiff]
      have h3 : ‖P.pos x - P.pos x₀‖ ≤ ‖P.pos x‖ + ‖P.pos x₀‖ := norm_sub_le _ _
      have h4 := hnormle x hx
      have h5 := hnormle x₀ hx₀
      linarith
    have hbound : ∀ j, |(k - k₀) j| ≤ (N:ℤ) := by
      intro j
      have h6 := hK (k - k₀) (2*ρ) hnorm j
      have h7 : (((k - k₀) j : ℤ) : ℝ) = ((k - k₀) j : ℝ) := rfl
      have h8 : ((|(k - k₀) j| : ℤ) : ℝ) ≤ K * (2*ρ) := by
        rw [Int.cast_abs]
        exact h6
      have h9 : ((|(k - k₀) j| : ℤ) : ℝ) ≤ (N : ℝ) := by
        refine le_trans h8 ?_
        rw [hNdef]
        have : K * (2*ρ) = 2*K*ρ := by ring
        rw [this]
        exact Nat.le_ceil _
      exact_mod_cast h9
    have hb0 := abs_le.mp (hbound 0)
    have hb1 := abs_le.mp (hbound 1)
    refine ⟨((k - k₀) 0 + (N:ℤ)).toNat, ((k - k₀) 1 + (N:ℤ)).toNat, ?_, ?_, ?_⟩
    · omega
    · omega
    · have hca : (((k - k₀) 0 + (N:ℤ)).toNat : ℤ) = (k - k₀) 0 + (N:ℤ) := by omega
      have hcb : (((k - k₀) 1 + (N:ℤ)).toNat : ℤ) = (k - k₀) 1 + (N:ℤ) := by omega
      rw [hca, hcb, ← P.shift_add]
      have hkey : ((k - k₀) 0 + (N:ℤ)) • UCPlanar.Support.e₁
            + ((k - k₀) 1 + (N:ℤ)) • UCPlanar.Support.e₂
            + (k₀ + (-(N:ℤ)) • UCPlanar.Support.e₁ + (-(N:ℤ)) • UCPlanar.Support.e₂) = k := by
        have hkk : k - k₀ = ((k - k₀) 0) • UCPlanar.Support.e₁
            + ((k - k₀) 1) • UCPlanar.Support.e₂ := UCPlanar.Support.site_eq_smul (k - k₀)
        have hexp : ((k - k₀) 0 + (N:ℤ)) • UCPlanar.Support.e₁
              + ((k - k₀) 1 + (N:ℤ)) • UCPlanar.Support.e₂
              + (k₀ + (-(N:ℤ)) • UCPlanar.Support.e₁ + (-(N:ℤ)) • UCPlanar.Support.e₂)
            = (((k - k₀) 0) • UCPlanar.Support.e₁ + ((k - k₀) 1) • UCPlanar.Support.e₂) + k₀ := by
          module
        rw [hexp, ← hkk]
        abel
      rw [hkey, hk]
  · refine ⟨v, N, hN, ⟨0, P.shift_zero v⟩, ?_⟩
    intro x hx hox
    exact absurd ⟨x, hx, hox⟩ hS

end UCPlanar.Support
