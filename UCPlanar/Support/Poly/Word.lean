/-
Iterated forward differences along a word of lattice vectors: their harmonicity on a square
shrunk by the length of the word, and the iteration of the discrete Caccioppoli inequality
across a chain of equally spaced nested squares.
-/
import UCPlanar.Support.Poly.Square

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar

/-- The forward difference of `f` along a word of lattice vectors, read right to left. -/
noncomputable def PeriodicGraph.diffWord {V : Type*} (P : PeriodicGraph V)
    (w : List (LatticeProb.Site 2)) (f : V → ℝ) : V → ℝ :=
  w.foldr (fun a g => P.diff a g) f

theorem PeriodicGraph.diffWord_nil {V : Type*} (P : PeriodicGraph V) (f : V → ℝ) :
    P.diffWord [] f = f := rfl

theorem PeriodicGraph.diffWord_cons {V : Type*} (P : PeriodicGraph V)
    (a : LatticeProb.Site 2) (w : List (LatticeProb.Site 2)) (f : V → ℝ) :
    P.diffWord (a :: w) f = P.diff a (P.diffWord w f) := rfl

end UCPlanar

namespace UCPlanar.Support

/-- A word difference of a function harmonic on a square is harmonic on the square shrunk by
the length of the word times a bound on the displacement of a single letter. -/
theorem diffWord_harmonic {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hp : P.PeriodicConductance c) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (w : List (LatticeProb.Site 2))
    (hw : ∀ a ∈ w, ∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ C₀)
    (f : V → ℝ) (s : ℝ)
    (hf : ∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c f x = 0) :
    ∀ x ∈ P.square (s - (w.length : ℝ) * C₀),
      LatticeProb.Network.netLaplacian P.graph c (P.diffWord w f) x = 0 := by
  induction w with
  | nil => intro x hx; simpa [UCPlanar.PeriodicGraph.diffWord_nil] using hf x (by simpa using hx)
  | cons a w ih =>
    intro x hx
    have hwmem : ∀ b ∈ w, ∀ i, |P.period (fun j => (b j : ℝ)) i| ≤ C₀ :=
      fun b hb => hw b (List.mem_cons_of_mem a hb)
    have hIH := ih hwmem
    have hlen : ((a :: w).length : ℝ) = (w.length : ℝ) + 1 := by
      simp [List.length_cons]
    have hsub : P.square (s - ((a :: w).length : ℝ) * C₀) ⊆ P.square (s - (w.length : ℝ) * C₀) := by
      refine UCPlanar.Support.square_mono P ?_
      rw [hlen]
      nlinarith [hC₀]
    have hx1 : x ∈ P.square (s - (w.length : ℝ) * C₀) := hsub hx
    have hx2 : P.shift a x ∈ P.square (s - (w.length : ℝ) * C₀) := by
      have h := UCPlanar.Support.shift_mem_square P a C₀ (hw a List.mem_cons_self)
        (s - ((a :: w).length : ℝ) * C₀) x hx
      have heq : s - ((a :: w).length : ℝ) * C₀ + C₀ = s - (w.length : ℝ) * C₀ := by
        rw [hlen]; ring
      rwa [heq] at h
    rw [UCPlanar.PeriodicGraph.diffWord_cons]
    show LatticeProb.Network.netLaplacian P.graph c
      (fun y => P.diffWord w f (P.shift a y) - P.diffWord w f y) x = 0
    have hgeq : (fun y => P.diffWord w f (P.shift a y) - P.diffWord w f y)
        = (fun y => P.diffWord w f (P.shift a y)) + (fun y => (-1 : ℝ) * P.diffWord w f y) := by
      funext y; simp [sub_eq_add_neg]
    rw [hgeq, LatticeProb.Network.netLaplacian_add,
      UCPlanar.Support.netLaplacian_shift P c hp (P.diffWord w f) a x,
      LatticeProb.Network.netLaplacian_smul, hIH (P.shift a x) hx2, hIH x hx1]
    ring

/-- Iterating the discrete Caccioppoli inequality across the chain of squares
`Q_r ⊂ Q_{r+gap} ⊂ … ⊂ Q_{r + n·gap}`, one letter of the word at each step. -/
theorem diffWord_l2_iterate {V : Type*} (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ)
    (hp : P.PeriodicConductance c) (C C₀ gap : ℝ) (hC : 0 < C) (hC₀ : 0 ≤ C₀)
    (hgap : 0 < gap) (hC₀gap : C₀ ≤ gap) (hCgap : C ≤ gap)
    (w : List (LatticeProb.Site 2))
    (hw : ∀ a ∈ w, ∀ i, |P.period (fun j => (a j : ℝ)) i| ≤ C₀)
    (hcac : ∀ a ∈ w, ∀ r s : ℝ, 0 < r → r + C ≤ s → ∀ g : V → ℝ,
      (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c g x = 0) →
      ∑ x ∈ P.square r, P.diff a g x ^ 2 ≤ (C / (s - r)) ^ 2 * ∑ x ∈ P.square s, g x ^ 2)
    (f : V → ℝ) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x ∈ P.square (r + (w.length : ℝ) * gap),
      LatticeProb.Network.netLaplacian P.graph c f x = 0) :
    ∑ x ∈ P.square r, P.diffWord w f x ^ 2
      ≤ ((C / gap) ^ w.length) ^ 2 * ∑ x ∈ P.square (r + (w.length : ℝ) * gap), f x ^ 2 := by
  induction w generalizing r with
  | nil => simp [UCPlanar.PeriodicGraph.diffWord_nil]
  | cons a w ih =>
    have hlen : (((a :: w).length : ℕ) : ℝ) = (w.length : ℝ) + 1 := by simp
    have hwmem : ∀ b ∈ w, ∀ i, |P.period (fun j => (b j : ℝ)) i| ≤ C₀ :=
      fun b hb => hw b (List.mem_cons_of_mem a hb)
    have hcacmem : ∀ b ∈ w, ∀ r s : ℝ, 0 < r → r + C ≤ s → ∀ g : V → ℝ,
        (∀ x ∈ P.square s, LatticeProb.Network.netLaplacian P.graph c g x = 0) →
        ∑ x ∈ P.square r, P.diff b g x ^ 2 ≤ (C / (s - r)) ^ 2 * ∑ x ∈ P.square s, g x ^ 2 :=
      fun b hb => hcac b (List.mem_cons_of_mem a hb)
    have hharm : ∀ x ∈ P.square (r + gap),
        LatticeProb.Network.netLaplacian P.graph c (P.diffWord w f) x = 0 := by
      intro x hx
      refine UCPlanar.Support.diffWord_harmonic P c hp C₀ hC₀ w hwmem f
        (r + (((a :: w).length : ℕ) : ℝ) * gap) hf x ?_
      refine UCPlanar.Support.square_mono P ?_ hx
      rw [hlen]
      nlinarith [hC₀gap, hgap]
    have hstep := hcac a List.mem_cons_self r (r + gap) hr (by linarith) (P.diffWord w f) hharm
    have hIH := ih hwmem hcacmem (r + gap) (by linarith) (by
      intro x hx
      refine hf x ?_
      refine UCPlanar.Support.square_mono P ?_ hx
      rw [hlen]
      nlinarith [hgap])
    have hgapne : C / (r + gap - r) = C / gap := by ring_nf
    rw [UCPlanar.PeriodicGraph.diffWord_cons]
    rw [hgapne] at hstep
    have hscale : r + gap + (w.length : ℝ) * gap = r + (((a :: w).length : ℕ) : ℝ) * gap := by
      rw [hlen]; ring
    rw [hscale] at hIH
    have hnn : (0:ℝ) ≤ (C / gap) ^ 2 := by positivity
    calc ∑ x ∈ P.square r, P.diff a (P.diffWord w f) x ^ 2
        ≤ (C / gap) ^ 2 * ∑ x ∈ P.square (r + gap), P.diffWord w f x ^ 2 := hstep
      _ ≤ (C / gap) ^ 2 * (((C / gap) ^ w.length) ^ 2 *
            ∑ x ∈ P.square (r + (((a :: w).length : ℕ) : ℝ) * gap), f x ^ 2) :=
          mul_le_mul_of_nonneg_left hIH hnn
      _ = ((C / gap) ^ ((a :: w).length)) ^ 2 *
            ∑ x ∈ P.square (r + (((a :: w).length : ℕ) : ℝ) * gap), f x ^ 2 := by
          rw [List.length_cons, pow_succ]
          ring

end UCPlanar.Support
