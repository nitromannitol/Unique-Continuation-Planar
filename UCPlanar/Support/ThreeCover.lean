/-
The geometry between the lattice three-ball inequality and the proposition: the line data of a
whole lattice line at reach `2^J`, and the transfer of the density hypothesis from the geometric
square to one coset of the period lattice.
-/
import UCPlanar.Basic
import UCPlanar.Support.ThreeReach
import UCPlanar.Support.Poly.Volume

open scoped BigOperators Classical
set_option autoImplicit false

namespace UCPlanar.Support.Three

open UCPlanar.Support

/-- **The bridge at reach `2^J`, horizontal lines.** -/
theorem polyReach_horizontal {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m J N : ℕ)
    (v : V) (f : V → ℝ) (α δ : ℝ) (t : ℤ)
    (happ : P.PolynomialApproximation R m v f α δ)
    (hin : ∀ s : ℤ, |s| ≤ 2^J*(N : ℤ) →
      P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v ∈ P.square (δ * R)) :
    PolyReach J N m (fun s => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  obtain ⟨p, hdeg, hbound⟩ := happ
  refine ⟨lineRestrict (latVar P v p) (t : ℝ), ?_, ?_⟩
  · exact le_trans (lineRestrict_natDegree_le _ _)
      (le_trans (latVar_totalDegree_le P v p) hdeg)
  · intro s hs
    have hor : P.OnOrbit v
        (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v) := ⟨_, rfl⟩
    have h := hbound _ (hin s hs) hor
    have heval : (lineRestrict (latVar P v p) (t : ℝ)).eval (s : ℝ)
        = MvPolynomial.eval
            (P.pos (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v)) p := by
      rw [lineRestrict_eval, ← latVar_eval_orbit P v p s t]
    simp only [orbLine]
    rw [heval]
    exact h

/-- **The bridge at reach `2^J`, vertical lines.** -/
theorem polyReach_vertical {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ) (m J N : ℕ)
    (v : V) (f : V → ℝ) (α δ : ℝ) (s : ℤ)
    (happ : P.PolynomialApproximation R m v f α δ)
    (hin : ∀ t : ℤ, |t| ≤ 2^J*(N : ℤ) →
      P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v ∈ P.square (δ * R)) :
    PolyReach J N m (fun t => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  obtain ⟨p, hdeg, hbound⟩ := happ
  refine ⟨lineRestrictSnd (latVar P v p) (s : ℝ), ?_, ?_⟩
  · exact le_trans (lineRestrictSnd_natDegree_le _ _)
      (le_trans (latVar_totalDegree_le P v p) hdeg)
  · intro t ht
    have hor : P.OnOrbit v
        (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v) := ⟨_, rfl⟩
    have h := hbound _ (hin t ht) hor
    have heval : (lineRestrictSnd (latVar P v p) (s : ℝ)).eval (t : ℝ)
        = MvPolynomial.eval
            (P.pos (P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v)) p := by
      rw [lineRestrictSnd_eval, ← latVar_eval_orbit P v p s t]
    simp only [orbLine]
    rw [heval]
    exact h

/-- An orbit point of the box of radius `L` lies in the square of radius `ρ + BL`. -/
theorem orbit_mem_square {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (s t : ℤ)
    (ρ B L : ℝ) (hB0 : 0 ≤ B) (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖)
    (hv : ‖P.pos v‖ ≤ ρ) (hs : |(s:ℝ)| ≤ L) (ht : |(t:ℝ)| ≤ L) (S : ℝ) (hS : ρ + B * L ≤ S) :
    P.shift (s • UCPlanar.Support.e₁ + t • UCPlanar.Support.e₂) v ∈ P.square S :=
  UCPlanar.Support.square_mono P hS
    (shift_mem_square P v s t ρ B L hB0 hL hρ hB hv hs ht)

/-- The integer bound `|s| ≤ 2^J N` in the real numbers. -/
theorem reach_cast (J N : ℕ) (s : ℤ) (hs : |s| ≤ 2^J*(N:ℤ)) : |(s:ℝ)| ≤ 2^J*(N:ℝ) := by
  rw [← Int.cast_abs]
  exact_mod_cast hs

/-- **The line data of every lattice line at reach `2^J`, horizontal.** -/
theorem polyReach_horizontal_of_fit {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ)
    (m J N : ℕ) (v : V) (f : V → ℝ) (α δ ρ B : ℝ) (hB0 : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖) (hv : ‖P.pos v‖ ≤ ρ)
    (hfit : ρ + B * (2^J*(N:ℝ)) ≤ δ * R)
    (happ : P.PolynomialApproximation R m v f α δ) (t : ℤ) (ht : |t| ≤ 2^J*(N:ℤ)) :
    PolyReach J N m (fun s => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  refine polyReach_horizontal P R m J N v f α δ t happ ?_
  intro s hs
  exact orbit_mem_square P v s t ρ B (2^J*(N:ℝ)) hB0 (by positivity) hρ hB hv
    (reach_cast J N s hs) (reach_cast J N t ht) (δ*R) hfit

/-- **The line data of every lattice line at reach `2^J`, vertical.** -/
theorem polyReach_vertical_of_fit {V : Type*} (P : UCPlanar.PeriodicGraph V) (R : ℝ)
    (m J N : ℕ) (v : V) (f : V → ℝ) (α δ ρ B : ℝ) (hB0 : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hB : ∀ u : UCPlanar.Plane, ‖P.period u‖ ≤ B * ‖u‖) (hv : ‖P.pos v‖ ≤ ρ)
    (hfit : ρ + B * (2^J*(N:ℝ)) ≤ δ * R)
    (happ : P.PolynomialApproximation R m v f α δ) (s : ℤ) (hs : |s| ≤ 2^J*(N:ℤ)) :
    PolyReach J N m (fun t => orbLine P f v s t)
      (α ^ m * UCPlanar.supNorm (P.square (3*R)) f) := by
  refine polyReach_vertical P R m J N v f α δ s happ ?_
  intro t ht
  exact orbit_mem_square P v s t ρ B (2^J*(N:ℝ)) hB0 (by positivity) hρ hB hv
    (reach_cast J N s hs) (reach_cast J N t ht) (δ*R) hfit

/-- The orbit point of `v` with lattice coordinates `x`. -/
noncomputable def orbPt {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) (x : ℤ × ℤ) : V :=
  P.shift (x.1 • UCPlanar.Support.e₁ + x.2 • UCPlanar.Support.e₂) v

theorem orbLine_eq_orbPt {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V)
    (x : ℤ × ℤ) : orbLine P f v x.1 x.2 = f (orbPt P v x) := rfl

/-- The two coordinates of a lattice vector written in the two generators. -/
theorem site_coord (a b : ℤ) (i : Fin 2) :
    ((a • UCPlanar.Support.e₁ + b • UCPlanar.Support.e₂ : LatticeProb.Site 2)) i
      = if i = 0 then a else b := by
  fin_cases i <;> simp [UCPlanar.Support.e₁, UCPlanar.Support.e₂]

/-- Distinct lattice coordinates give distinct orbit points. -/
theorem orbPt_injective {V : Type*} (P : UCPlanar.PeriodicGraph V) (v : V) :
    Function.Injective (orbPt P v) := by
  intro x y hxy
  have h := UCPlanar.Support.shift_site_injective P v hxy
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [site_coord x.1 x.2 0, site_coord y.1 y.2 0] at h0
  rw [site_coord x.1 x.2 1, site_coord y.1 y.2 1] at h1
  simp only [show ((1 : Fin 2) = 0) = False by simp, if_false] at h1
  exact Prod.ext h0 h1

/-- The lattice box has `(2n+1)^2` points. -/
theorem box_card (n : ℕ) : (box n).card = (2*n+1)^2 := by
  have hseg : (seg n).card = 2*n+1 := by
    rw [seg, Int.card_Icc]
    omega
  rw [box, show (seg n).product (seg n) = seg n ×ˢ seg n from rfl,
    Finset.card_product, hseg]
  ring

theorem zero_mem_box (n : ℕ) : ((0 : ℤ), (0 : ℤ)) ∈ box n := by
  rw [box, show (seg n).product (seg n) = seg n ×ˢ seg n from rfl, Finset.mem_product,
    seg, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp

/-- **The density hypothesis passes to one coset of the period lattice.**  The lattice box of
radius `n` embeds in the geometric square, so its exceptional points are exceptional points of
the square; if the square's exceptional count is at most a quarter of the box, the box carries
the density the lattice three-ball inequality asks for.  This is the step "by choosing ε
sufficiently small, it suffices to prove this statement only for vertices in the translated
lattice `v + L`" of `ucplanar.tex:488`. -/
theorem coset_density {V : Type*} (P : UCPlanar.PeriodicGraph V) (f : V → ℝ) (v : V) (n : ℕ)
    (Rad ε : ℝ) (_hε0 : 0 ≤ ε)
    (hmaps : ∀ x ∈ box n, orbPt P v x ∈ P.square Rad)
    (hdens : 1 - ε ≤ UCPlanar.boundedDensity (P.square Rad) f 1)
    (hcount : ε * (((P.square Rad).card : ℕ) : ℝ) ≤ (1/4) * (((box n).card : ℕ) : ℝ)) :
    (1 - (1/4:ℝ)) * (((box n).card : ℕ) : ℝ) ≤
      ((((box n).filter (fun x => |orbLine P f v x.1 x.2| ≤ 1)).card : ℕ) : ℝ) := by
  classical
  set S := P.square Rad with hS
  have hSne : S.Nonempty := ⟨orbPt P v (0, 0), hmaps _ (zero_mem_box n)⟩
  have hScard : (0:ℝ) < (S.card : ℝ) := by
    have : 0 < S.card := Finset.card_pos.mpr hSne
    exact_mod_cast this
  -- the density hypothesis in counting form
  have hgood : (1 - ε) * (S.card : ℝ) ≤ ((S.filter (fun x => |f x| ≤ 1)).card : ℝ) := by
    have h := hdens
    simp only [UCPlanar.boundedDensity] at h
    rw [le_div_iff₀ hScard] at h
    linarith
  have hsplit : ((S.filter (fun x => |f x| ≤ 1)).card : ℝ)
      + ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) = (S.card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not
      (s := S) (p := fun x => |f x| ≤ 1)
    exact_mod_cast this
  have hbadS : ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) ≤ ε * (S.card : ℝ) := by
    linarith
  -- the bad points of the box inject into the bad points of the square
  have hinj : ((box n).filter (fun x => ¬ (|orbLine P f v x.1 x.2| ≤ 1))).card
      ≤ (S.filter (fun x => ¬ (|f x| ≤ 1))).card := by
    refine Finset.card_le_card_of_injOn (orbPt P v) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨hmaps x hx.1, hx.2⟩
    · intro x _ y _ h
      exact orbPt_injective P v h
  have hinj' : (((box n).filter (fun x => ¬ (|orbLine P f v x.1 x.2| ≤ 1))).card : ℝ)
      ≤ ((S.filter (fun x => ¬ (|f x| ≤ 1))).card : ℝ) := by exact_mod_cast hinj
  have hsplitB : (((box n).filter (fun x => |orbLine P f v x.1 x.2| ≤ 1)).card : ℝ)
      + (((box n).filter (fun x => ¬ (|orbLine P f v x.1 x.2| ≤ 1))).card : ℝ)
      = ((box n).card : ℝ) := by
    have := Finset.card_filter_add_card_filter_not
      (s := box n) (p := fun x => |orbLine P f v x.1 x.2| ≤ 1)
    exact_mod_cast this
  linarith

end UCPlanar.Support.Three
