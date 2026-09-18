/-
Counting for the local density hypothesis.

The chain of three-ball inequalities needs the density hypothesis at every small square centred
at a lattice point inside a large square.  It follows from the density at the large square by
counting, because the exceptional vertices of the small square are exceptional vertices of the
large one, the number of vertices of a square is quadratic in its radius from both sides, and a
lattice translation preserves cardinalities.
-/
import UCPlanar.Support.LowerShift
import UCPlanar.Support.Poly.Volume
import UCPlanar.Support.Poly.Rebase

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Lower

/-- **Every vertex lies in a square of a fixed radius centred at a lattice point.**  The radius
depends only on the drawing of the finitely many vertex orbits. -/
theorem exists_centre {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x : V, ∃ a : LatticeProb.Site 2, x ∈ squareAt P a ρ := by
  classical
  refine ⟨∑ v ∈ P.representatives, ‖P.pos v‖, Finset.sum_nonneg (fun v _ => norm_nonneg _), ?_⟩
  intro x
  obtain ⟨v, hv, a, hax⟩ := P.covers x
  refine ⟨a, ?_⟩
  rw [mem_squareAt, ← hax, ← P.shift_add, neg_add_cancel, P.shift_zero]
  rw [UCPlanar.Support.mem_square_iff]
  intro i
  calc |P.pos v i| = ‖P.pos v i‖ := rfl
    _ ≤ ‖P.pos v‖ := norm_le_pi_norm _ i
    _ ≤ ∑ w ∈ P.representatives, ‖P.pos w‖ :=
        Finset.single_le_sum (f := fun w => ‖P.pos w‖) (fun w _ => norm_nonneg _) hv

/-- **A quadratic lower bound for the number of vertices of a geometric square.**  The orbit of
one representative under the lattice vectors of length at most `t` already has `(2t+1)²`
vertices, and the drawing of such a vector has length at most `B t`. -/
theorem exists_square_card_lower {V : Type*} (P : UCPlanar.PeriodicGraph V) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
      κ * R ^ 2 ≤ ((P.square R).card : ℝ) := by
  classical
  obtain ⟨B, hB0, hB⟩ := UCPlanar.Support.exists_period_bound P
  obtain ⟨ρ, hρ0, hρ⟩ := exists_centre P
  obtain ⟨x₀⟩ := P.connected.nonempty
  obtain ⟨a₀, ha₀⟩ := hρ x₀
  set v₀ : V := P.shift (-a₀) x₀ with hv₀
  have hv₀mem : v₀ ∈ P.square ρ := (mem_squareAt P a₀ ρ x₀).mp ha₀
  have hv₀i : ∀ i, |P.pos v₀ i| ≤ ρ := (UCPlanar.Support.mem_square_iff P ρ v₀).mp hv₀mem
  set b : ℝ := B + 1 with hbdef
  have hb0 : (0:ℝ) < b := by simp [hbdef]; linarith
  refine ⟨1/(4*b^2), by positivity, max (2*ρ) (4*b) + 1, by positivity, ?_⟩
  intro R hR
  have hRρ : 2*ρ ≤ R := le_trans (le_trans (le_max_left _ _) (by linarith)) hR
  have hRb : 4*b ≤ R := le_trans (le_trans (le_max_right _ _) (by linarith)) hR
  have hR0 : 0 < R := by linarith
  -- the integer half-side of the lattice box
  set t : ℕ := ⌊(R - ρ)/b⌋₊ with htdef
  have hfloor : ((t:ℝ)) ≥ (R - ρ)/b - 1 := by
    have := Nat.sub_one_lt_floor ((R - ρ)/b)
    linarith [Nat.lt_floor_add_one ((R - ρ)/b)]
  have hbtR : (R - ρ) - b ≤ b * (t:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hfloor (le_of_lt hb0)
    have heq : b * ((R - ρ)/b - 1) = (R - ρ) - b := by field_simp
    linarith [h, heq.le, heq.ge]
  have hbig : R ≤ 4*b*(t:ℝ) := by linarith [hbtR, hRρ, hRb]
  -- the box of lattice vectors injects into the square
  set Box : Finset (LatticeProb.Site 2) :=
    Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-(t : ℤ)) (t : ℤ)) with hBox
  have hmem : ∀ a ∈ Box, P.shift a v₀ ∈ P.square R := by
    intro a hA
    have hA' := Fintype.mem_piFinset.mp (by rwa [hBox] at hA)
    have hnorm : ‖(fun j => ((a j : ℤ) : ℝ))‖ ≤ (t:ℝ) := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      have := Finset.mem_Icc.mp (hA' j)
      have h1 : |((a j : ℤ) : ℝ)| ≤ (t:ℝ) := by
        rw [abs_le]
        constructor
        · exact_mod_cast this.1
        · exact_mod_cast this.2
      simpa [Real.norm_eq_abs] using h1
    have hper : ‖P.period (fun j => ((a j : ℤ) : ℝ))‖ ≤ B * (t:ℝ) :=
      le_trans (hB _) (by nlinarith [hnorm, hB0])
    rw [UCPlanar.Support.mem_square_iff]
    intro i
    rw [P.pos_shift]
    have hi : |P.period (fun j => ((a j : ℤ) : ℝ)) i| ≤ B * (t:ℝ) := by
      have hn := norm_le_pi_norm (P.period (fun j => ((a j : ℤ) : ℝ))) i
      rw [Real.norm_eq_abs] at hn
      exact le_trans hn hper
    have hbt : B * (t:ℝ) ≤ R - ρ := by
      have h1 : (t:ℝ) ≤ (R - ρ)/b := Nat.floor_le (by
        have : 0 ≤ R - ρ := by linarith
        positivity)
      have h2 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
      have h3 : B * (t:ℝ) ≤ b * ((R-ρ)/b) := by nlinarith [h1, hB0]
      rw [mul_div_cancel₀ _ (ne_of_gt hb0)] at h3
      exact h3
    calc |P.pos v₀ i + P.period (fun j => ((a j : ℤ) : ℝ)) i|
        ≤ |P.pos v₀ i| + |P.period (fun j => ((a j : ℤ) : ℝ)) i| := abs_add_le _ _
      _ ≤ ρ + (R - ρ) := add_le_add (hv₀i i) (le_trans hi hbt)
      _ = R := by ring
  have hcard : Box.card ≤ (P.square R).card :=
    Finset.card_le_card_of_injOn (fun a : LatticeProb.Site 2 => P.shift a v₀) hmem
      (fun a _ b _ h => UCPlanar.Support.shift_site_injective P v₀ h)
  have hIcc : (Finset.Icc (-(t : ℤ)) (t : ℤ)).card = 2 * t + 1 := by
    rw [Int.card_Icc]; omega
  have hBoxCard : Box.card = (2 * t + 1)^2 := by
    rw [hBox, Fintype.card_piFinset]
    simp [hIcc]
  have hlow : ((2 * (t:ℝ) + 1)^2) ≤ ((P.square R).card : ℝ) := by
    have h1 : ((2 * t + 1)^2 : ℕ) ≤ (P.square R).card := by rw [← hBoxCard]; exact hcard
    have h2 : (((2 * t + 1)^2 : ℕ) : ℝ) = (2 * (t : ℝ) + 1)^2 := by push_cast; ring
    calc ((2 * (t:ℝ) + 1)^2) = (((2 * t + 1)^2 : ℕ) : ℝ) := h2.symm
      _ ≤ ((P.square R).card : ℝ) := by exact_mod_cast h1
  have hfin : 1/(4*b^2) * R^2 ≤ (2 * (t:ℝ) + 1)^2 := by
    have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
    have hsq : R^2 ≤ (4*b*(t:ℝ))^2 := by nlinarith [hbig, hR0]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [hsq, ht0, hb0]
  linarith [hlow, hfin]

/-- **The density passes to a small square centred at a lattice point.**  The exceptional
vertices of the small square are exceptional vertices of the large one. -/
theorem density_squareAt {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ)
    (a : LatticeProb.Site 2) (L Rad ε ε₀ : ℝ)
    (hsub : squareAt P a L ⊆ P.square Rad)
    (hne : (P.square L).Nonempty)
    (hdens : 1 - ε ≤ UCPlanar.boundedDensity (P.square Rad) f 1)
    (hcount : ε * (((P.square Rad).card : ℕ) : ℝ) ≤ ε₀ * (((P.square L).card : ℕ) : ℝ)) :
    1 - ε₀ ≤ UCPlanar.boundedDensity (squareAt P a L) f 1 := by
  classical
  set S := P.square Rad with hS
  set T := squareAt P a L with hT
  have hTcard : T.card = (P.square L).card := card_squareAt P a L
  have hTne : T.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨P.shift a y, shift_mem_squareAt P a L y hy⟩
  have hTpos : (0:ℝ) < (T.card : ℝ) := by
    have : 0 < T.card := Finset.card_pos.mpr hTne
    exact_mod_cast this
  have hSne : S.Nonempty := ⟨_, hsub hTne.choose_spec⟩
  have hSpos : (0:ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hSne
    exact_mod_cast this
  have hgood : (1 - ε) * (S.card : ℝ) ≤ ((S.filter (fun x => |f x| ≤ 1)).card : ℝ) := by
    have h := hdens
    simp only [UCPlanar.boundedDensity] at h
    rw [le_div_iff₀ hSpos] at h
    linarith
  have hsplit : ((S.filter (fun x => |f x| ≤ 1)).card : ℝ)
      + ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) = (S.card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => |f x| ≤ 1)
    exact_mod_cast this
  have hbadS : ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) ≤ ε * (S.card : ℝ) := by linarith
  have hbadT : ((T.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ)
      ≤ ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) := by
    have : T.filter (fun x => ¬ (|f x| ≤ 1)) ⊆ S.filter (fun x => ¬ (|f x| ≤ 1)) :=
      Finset.filter_subset_filter _ hsub
    exact_mod_cast Finset.card_le_card this
  have hsplitT : ((T.filter (fun x => |f x| ≤ 1)).card : ℝ)
      + ((T.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) = (T.card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not (s := T) (p := fun x => |f x| ≤ 1)
    exact_mod_cast this
  have hcount' : ε * (S.card : ℝ) ≤ ε₀ * (T.card : ℝ) := by rw [hTcard]; exact hcount
  simp only [UCPlanar.boundedDensity]
  rw [le_div_iff₀ hTpos]
  linarith
