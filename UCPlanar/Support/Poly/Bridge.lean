/-
The bridge between the mixed forward differences of the orbit data of a function and the word
differences along the two lattice generators, and the resulting bound on the mixed differences
of order `m+1` supplied by the derivative bound.
-/
import UCPlanar.Support.Poly.Orbit
import UCPlanar.Support.Poly.DerivBound

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support

/-- The orbit data of a function, as a function on the lattice quadrant. -/
noncomputable def orb {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V) :
    ℕ × ℕ → ℝ :=
  fun ab => UCPlanar.Support.orbitCoord P f v ab.1 ab.2

theorem orb_apply {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V) (t y : ℕ) :
    orb P f v (t, y) = f (P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v) :=
  rfl

theorem orb_fwdDiff_fst {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V) :
    fwdDiff ((1, 0) : ℕ × ℕ) (orb P f v) = orb P (P.diff UCPlanar.Support.e₁ f) v := by
  funext ab
  obtain ⟨t, y⟩ := ab
  show UCPlanar.Support.orbitCoord P f v (t + 1) y - UCPlanar.Support.orbitCoord P f v t y
    = f (P.shift UCPlanar.Support.e₁
          (P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v))
      - f (P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v)
  rw [UCPlanar.Support.orbitCoord, UCPlanar.Support.orbitCoord]
  congr 2
  rw [← P.shift_add]
  congr 1
  push_cast
  module

theorem orb_fwdDiff_snd {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V) :
    fwdDiff ((0, 1) : ℕ × ℕ) (orb P f v) = orb P (P.diff UCPlanar.Support.e₂ f) v := by
  funext ab
  obtain ⟨t, y⟩ := ab
  show UCPlanar.Support.orbitCoord P f v t (y + 1) - UCPlanar.Support.orbitCoord P f v t y
    = f (P.shift UCPlanar.Support.e₂
          (P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v))
      - f (P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v)
  rw [UCPlanar.Support.orbitCoord, UCPlanar.Support.orbitCoord]
  congr 2
  rw [← P.shift_add]
  congr 1
  push_cast
  module

theorem orb_fwdDiff_fst_iter {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (i : ℕ) :
    ∀ f : V → ℝ, (fwdDiff ((1, 0) : ℕ × ℕ))^[i] (orb P f v)
      = orb P ((P.diff UCPlanar.Support.e₁)^[i] f) v := by
  induction i with
  | zero => intro f; rfl
  | succ i ih =>
    intro f
    rw [Function.iterate_succ_apply, orb_fwdDiff_fst, ih, Function.iterate_succ_apply]

theorem orb_fwdDiff_snd_iter {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (j : ℕ) :
    ∀ f : V → ℝ, (fwdDiff ((0, 1) : ℕ × ℕ))^[j] (orb P f v)
      = orb P ((P.diff UCPlanar.Support.e₂)^[j] f) v := by
  induction j with
  | zero => intro f; rfl
  | succ j ih =>
    intro f
    rw [Function.iterate_succ_apply, orb_fwdDiff_snd, ih, Function.iterate_succ_apply]

theorem diffWord_append {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (u w : List (LatticeProb.Site 2)) (f : V → ℝ) :
    P.diffWord (u ++ w) f = P.diffWord u (P.diffWord w f) := by
  simp [UCPlanar.PeriodicGraph.diffWord, List.foldr_append]

theorem diffWord_replicate {V : Type*} (P : UCPlanar.PeriodicGraph V)
    (a : LatticeProb.Site 2) (i : ℕ) (f : V → ℝ) :
    P.diffWord (List.replicate i a) f = (P.diff a)^[i] f := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.replicate_succ, UCPlanar.PeriodicGraph.diffWord_cons, ih,
      Function.iterate_succ_apply']

/-- The mixed forward difference of the orbit data is the word difference along `i` copies of
the first generator followed by `j` copies of the second. -/
theorem orb_mixedDiff {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V)
    (i j : ℕ) (t y : ℕ) :
    ((fwdDiff ((1, 0) : ℕ × ℕ))^[i] ((fwdDiff ((0, 1) : ℕ × ℕ))^[j] (orb P f v))) (t, y)
      = P.diffWord (List.replicate i UCPlanar.Support.e₁ ++ List.replicate j UCPlanar.Support.e₂) f
          (P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v) := by
  rw [orb_fwdDiff_snd_iter, orb_fwdDiff_fst_iter, orb_apply, diffWord_append,
    diffWord_replicate, diffWord_replicate]

/-- The order-`(m+1)` mixed differences of the orbit data of a harmonic function, at the orbit
points of `Q_R`, are bounded by the derivative bound. -/
theorem exists_mixedDiff_bound {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hc : LatticeProb.Network.IsCond P.graph c) (hp : P.PeriodicConductance c)
    (hMos : UCPlanar.External.MoserEstimate P c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ R : ℝ, 1 ≤ R → ∀ m : ℕ, ((m : ℝ) + 1) * C₁ ≤ R →
      ∀ (f : V → ℝ),
        (∀ x ∈ P.square (3*R), LatticeProb.Network.netLaplacian P.graph c f x = 0) →
        ∀ (v : V) (i j : ℕ), i + j = m + 1 → ∀ t y : ℕ,
          P.shift ((t : ℤ) • UCPlanar.Support.e₁ + (y : ℤ) • UCPlanar.Support.e₂) v
            ∈ P.square R →
          |((fwdDiff ((1, 0) : ℕ × ℕ))^[i]
              ((fwdDiff ((0, 1) : ℕ × ℕ))^[j] (orb P f v))) (t, y)|
            ≤ ((C₁ * ((m : ℝ) + 1)) / R) ^ (m + 1)
                * UCPlanar.supNorm (P.square (3*R)) f := by
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    UCPlanar.Support.exists_derivative_bound P c hc hp hMos
      UCPlanar.Support.e₁ UCPlanar.Support.e₂
  refine ⟨C₁, hC₁0, ?_⟩
  intro R hR m hm f hf v i j hij t y hxy
  set w : List (LatticeProb.Site 2) :=
    List.replicate i UCPlanar.Support.e₁ ++ List.replicate j UCPlanar.Support.e₂ with hwdef
  have hlen : w.length = m + 1 := by
    rw [hwdef, List.length_append, List.length_replicate, List.length_replicate, hij]
  have hletters : ∀ a ∈ w, a = UCPlanar.Support.e₁ ∨ a = UCPlanar.Support.e₂ := by
    intro a ha
    rw [hwdef, List.mem_append] at ha
    rcases ha with h | h
    · exact Or.inl (List.eq_of_mem_replicate h)
    · exact Or.inr (List.eq_of_mem_replicate h)
  have hpos : 0 < w.length := by rw [hlen]; omega
  have hsmall : (w.length : ℝ) * C₁ ≤ R := by
    rw [hlen]; push_cast; linarith [hm]
  have h := hC₁ R hR w hletters hpos hsmall f hf _ hxy
  rw [orb_mixedDiff]
  rw [hlen] at h
  push_cast at h ⊢
  exact h

end UCPlanar.Support
