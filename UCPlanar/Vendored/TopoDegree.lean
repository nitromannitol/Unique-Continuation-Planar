/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Bonanno/QuantumZipper/Proofs/Complex/TopoDegree.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `QuantumZipper.CA.Topo` is renamed `UCPlanar.Vendored.Topo`, the module paths of
   local imports are changed, and `Set.domRestrict`, `continuousOn_iff_continuous_domRestrict` and
   `dite_eq_left` are replaced by `Set.restrict`, `continuousOn_iff_continuous_restrict` and
   `dif_pos`, their counterparts in the Mathlib version this repository uses. -/
/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.TopoDegree at commit 31e7483; only the module paths of local imports are changed.
   v4.35 port: replace deprecated dif_pos with dite_eq_left. -/
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Degree of loops in `ℂ \ {0}` (EXT-CA node T1)

For a continuous nonvanishing `γ : C(unitInterval, ℂ)` we construct a continuous logarithm
(`exists_lift_exp`), show that two continuous logarithms differ by a constant
(`lift_sub_eq_sub_zero`), and define the degree `loopDeg γ h` of a loop as
`(L 1 - L 0) / (2πi)` for any continuous logarithm `L` of `γ`.

Main results: `loopDeg_eq_of_lift`, `loopDeg_mul`, `loopDeg_const`, `loopDeg_circle`,
`loopDeg_eq_zero_iff`, `loopDeg_homotopy` (free homotopy invariance through loops),
`loopDeg_eq_of_norm_sub_lt` (Rouché/dog-on-a-leash), and `hasLogOn_of_arc`
(a continuous nonvanishing function on an arc has a continuous logarithm, T4(a)).

**Source.** R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021),
Chapter 4: Definition 4.2 and Corollary 4.3 (printed p. 189, PDF p. 214): the index of a loop is
`[φ(b) − φ(a)]/2πi` for a continuous logarithm `φ` of the loop; it is well defined because two
continuous logarithms differ by a constant on the connected interval, and it is an integer because
the loop closes. Existence of continuous logarithms (Burckel Thm 4.0/4.1) is replaced here by the
path lifting property of the covering map `exp : ℂ → ℂ \ {0}` (mathlib `Complex.isCoveringMap_exp`,
`IsCoveringMap.liftPath`, `IsCoveringMap.liftHomotopy`), and the "constant integer-valued
function" step by the uniqueness of path lifts. Homotopy invariance follows Burckel's use of a
lift of the whole homotopy (cf. the proof on PDF p. 214, top). The Rouché-type lemma
uses the principal logarithm of `γ/δ` on the right half plane (Burckel 3.19 style).
-/

open Complex Set Real

namespace UCPlanar.Vendored.Topo

/-- `g` has a continuous logarithm on `J`. -/
def HasLogOn (g : ℂ → ℂ) (J : Set ℂ) : Prop :=
  ∃ L : ℂ → ℂ, ContinuousOn L J ∧ ∀ z ∈ J, Complex.exp (L z) = g z

/-- The nonvanishing loop as a map into `{z // z ≠ 0}`. -/
noncomputable def toNeZero (γ : C(unitInterval, ℂ)) (h : ∀ t, γ t ≠ 0) : C(unitInterval, {z : ℂ // z ≠ 0}) :=
  ⟨fun t => ⟨γ t, h t⟩, by fun_prop⟩

/-- Existence of a continuous logarithm along a nonvanishing path. -/
theorem exists_lift_exp (γ : C(unitInterval, ℂ)) (h : ∀ t, γ t ≠ 0) :
    ∃ L : C(unitInterval, ℂ), ∀ t, Complex.exp (L t) = γ t := by
  have h0 : toNeZero γ h 0 = ⟨Complex.exp (Complex.log (γ 0)), Complex.exp_ne_zero _⟩ := by
    ext; simp [toNeZero, Complex.exp_log (h 0)]
  refine ⟨isCoveringMap_exp.liftPath (toNeZero γ h) (Complex.log (γ 0)) h0, fun t => ?_⟩
  have := congrArg Subtype.val
    (congr_fun (isCoveringMap_exp.liftPath_lifts (toNeZero γ h) (Complex.log (γ 0)) h0) t)
  simpa [toNeZero] using this

/-- Two continuous logarithms of the same nonvanishing path differ by a constant. -/
theorem lift_sub_eq_sub_zero (γ : C(unitInterval, ℂ)) (h : ∀ t, γ t ≠ 0) {L L' : unitInterval → ℂ}
    (hL : Continuous L) (hL' : Continuous L') (hexp : ∀ t, Complex.exp (L t) = γ t)
    (hexp' : ∀ t, Complex.exp (L' t) = γ t) (t : unitInterval) : L' t - L t = L' 0 - L 0 := by
  have hc : Complex.exp (L' 0 - L 0) = 1 := by
    rw [Complex.exp_sub, hexp, hexp', div_self (h 0)]
  have h0 : toNeZero γ h 0 = ⟨Complex.exp (L' 0), Complex.exp_ne_zero _⟩ := by
    ext; simp [toNeZero, hexp']
  have e1 : L' = isCoveringMap_exp.liftPath (toNeZero γ h) (L' 0) h0 := by
    rw [IsCoveringMap.eq_liftPath_iff]
    refine ⟨hL', ?_, rfl⟩
    funext s; ext; simp [toNeZero, hexp']
  have e2 : (fun s => L s + (L' 0 - L 0)) =
      isCoveringMap_exp.liftPath (toNeZero γ h) (L' 0) h0 := by
    rw [IsCoveringMap.eq_liftPath_iff]
    refine ⟨by fun_prop, ?_, by simp⟩
    funext s; ext; simp [toNeZero, Complex.exp_add, hexp, hc]
  have := congr_fun (e1.trans e2.symm) t
  rw [this]; ring

/-- The degree of a nonvanishing path `γ`: `round (re ((L 1 - L 0)/(2πi)))` for the chosen
continuous logarithm `L`. For a loop (`γ 0 = γ 1`) this equals `(L 1 - L 0)/(2πi)` for every
continuous logarithm, see `loopDeg_eq_of_lift`. -/
noncomputable def loopDeg (γ : C(unitInterval, ℂ)) (h : ∀ t, γ t ≠ 0) : ℤ :=
  let L := (exists_lift_exp γ h).choose
  round (((L 1 - L 0) / (2 * π * I)).re)

lemma two_pi_I_ne_zero' : (2 * π * I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- The degree of a loop computed from any continuous logarithm. -/
theorem loopDeg_eq_of_lift (γ : C(unitInterval, ℂ)) (h : ∀ t, γ t ≠ 0) (hc : γ 0 = γ 1) {L : unitInterval → ℂ}
    (hL : Continuous L) (hexp : ∀ t, Complex.exp (L t) = γ t) :
    L 1 - L 0 = (loopDeg γ h : ℂ) * (2 * π * I) := by
  set L₀ := (exists_lift_exp γ h).choose with hL₀
  have hL₀exp := (exists_lift_exp γ h).choose_spec
  have hsame : L 1 - L 0 = L₀ 1 - L₀ 0 := by
    have := lift_sub_eq_sub_zero γ h L₀.continuous hL hL₀exp hexp 1
    linear_combination this
  have hone : Complex.exp (L₀ 1 - L₀ 0) = 1 := by
    rw [Complex.exp_sub, hL₀exp, hL₀exp, ← hc, div_self (h 0)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone
  have hdeg : loopDeg γ h = n := by
    simp only [loopDeg]
    rw [← hL₀, hn, mul_div_assoc, div_self two_pi_I_ne_zero', mul_one]
    simp
  rw [hsame, hn, hdeg]

lemma loopDeg_unique (γ : C(unitInterval, ℂ)) (h : ∀ t, γ t ≠ 0) (hc : γ 0 = γ 1) {L : unitInterval → ℂ}
    (hL : Continuous L) (hexp : ∀ t, Complex.exp (L t) = γ t) {n : ℤ}
    (hn : L 1 - L 0 = (n : ℂ) * (2 * π * I)) : loopDeg γ h = n := by
  have := loopDeg_eq_of_lift γ h hc hL hexp
  rw [hn] at this
  exact_mod_cast (mul_right_cancel₀ two_pi_I_ne_zero' this).symm

/-- Degree is additive under pointwise products. -/
theorem loopDeg_mul (γ δ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0)
    (hγc : γ 0 = γ 1) (hδc : δ 0 = δ 1) :
    loopDeg (γ * δ) (fun t => by simpa using mul_ne_zero (hγ t) (hδ t)) =
      loopDeg γ hγ + loopDeg δ hδ := by
  obtain ⟨L, hL⟩ := exists_lift_exp γ hγ
  obtain ⟨M, hM⟩ := exists_lift_exp δ hδ
  apply loopDeg_unique _ _ (by simp [hγc, hδc]) (L := fun t => L t + M t) (by fun_prop)
    (fun t => by simp [Complex.exp_add, hL, hM])
  have e1 := loopDeg_eq_of_lift γ hγ hγc L.continuous hL
  have e2 := loopDeg_eq_of_lift δ hδ hδc M.continuous hM
  push_cast
  linear_combination e1 + e2

/-- A constant loop has degree `0`. -/
theorem loopDeg_const (c : ℂ) (hc : c ≠ 0) :
    loopDeg (ContinuousMap.const unitInterval c) (fun _ => hc) = 0 := by
  apply loopDeg_unique _ _ rfl (L := fun _ => Complex.log c) continuous_const
    (fun t => by simp [Complex.exp_log hc])
  simp

/-- The loop `t ↦ circleMap 0 r (2π t)`. -/
noncomputable def circleLoop (r : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => circleMap 0 r (2 * π * (t : ℝ)), by unfold circleMap; fun_prop⟩

lemma circleLoop_ne_zero {r : ℝ} (hr : r ≠ 0) (t : unitInterval) : circleLoop r t ≠ 0 :=
  circleMap_ne_center hr

/-- The standard circle has degree `1`. -/
theorem loopDeg_circle {r : ℝ} (hr : r ≠ 0) : loopDeg (circleLoop r) (circleLoop_ne_zero hr) = 1 := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  apply loopDeg_unique _ _ ?_ (L := fun t => Complex.log r + (2 * π * (t : ℝ) : ℝ) * I)
    (by fun_prop) (fun t => ?_)
  · simp
  · simp only [circleLoop, ContinuousMap.coe_mk, Set.Icc.coe_zero, Set.Icc.coe_one]
    simpa using (periodic_circleMap 0 r 0).symm
  · simp [circleLoop, circleMap, Complex.exp_add, Complex.exp_log hr']

/-- The slice `t ↦ H (t, s)` of a map on the square. -/
noncomputable def slice (H : C(unitInterval × unitInterval, ℂ)) (s : unitInterval) : C(unitInterval, ℂ) := ⟨fun t => H (t, s), by fun_prop⟩

/-- Free homotopy invariance of the degree through loops in `ℂ \ {0}`. -/
theorem loopDeg_homotopy (H : C(unitInterval × unitInterval, ℂ)) (h0 : ∀ p, H p ≠ 0) (hc : ∀ s, H (0, s) = H (1, s)) :
    loopDeg (slice H 0) (fun _ => h0 _) = loopDeg (slice H 1) (fun _ => h0 _) := by
  -- a continuous log of the side `s ↦ H (0, s)`
  let side : C(unitInterval, ℂ) := ⟨fun s => H (0, s), by fun_prop⟩
  obtain ⟨f, hf⟩ := exists_lift_exp side (fun _ => h0 _)
  let H' : C(unitInterval × unitInterval, {z : ℂ // z ≠ 0}) := ⟨fun p => ⟨H p, h0 p⟩, by fun_prop⟩
  have H_0 : ∀ a, H' (0, a) = ⟨Complex.exp (f a), Complex.exp_ne_zero _⟩ := fun a => by
    ext; simp [H', hf, side]
  set Λ := isCoveringMap_exp.liftHomotopy H' f H_0
  have hΛ : ∀ p, Complex.exp (Λ p) = H p := fun p => by
    exact congrArg Subtype.val (congr_fun (isCoveringMap_exp.liftHomotopy_lifts H' f H_0) p)
  -- the jump `Λ (1, s) - Λ (0, s)` is independent of `s`
  have hjump : ∀ s, Λ (1, s) - Λ (0, s) = Λ (1, 0) - Λ (0, 0) := by
    intro s
    have := lift_sub_eq_sub_zero side (fun _ => h0 _) (L := fun s => Λ (0, s))
      (L' := fun s => Λ (1, s)) (by fun_prop) (by fun_prop) (fun s => by simp [side, hΛ])
      (fun s => by simp [side, hΛ, hc]) s
    exact this
  have hdeg : ∀ s, (loopDeg (slice H s) (fun _ => h0 _) : ℂ) * (2 * π * I) =
      Λ (1, s) - Λ (0, s) := fun s =>
    (loopDeg_eq_of_lift (slice H s) (fun _ => h0 _) (by simp [slice, hc])
      (L := fun t => Λ (t, s)) (by fun_prop) (fun t => by simp [slice, hΛ])).symm
  have := (hdeg 0).trans ((hjump 1).symm.trans (hdeg 1).symm)
  exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero' this

/-- Dog-on-a-leash / Rouché: if `‖γ t - δ t‖ < ‖δ t‖` for all `t`, the loops `γ`, `δ` have the
same degree. -/
theorem loopDeg_eq_of_norm_sub_lt (γ δ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) (hδ : ∀ t, δ t ≠ 0)
    (hγc : γ 0 = γ 1) (hδc : δ 0 = δ 1) (h : ∀ t, ‖γ t - δ t‖ < ‖δ t‖) :
    loopDeg γ hγ = loopDeg δ hδ := by
  obtain ⟨M, hM⟩ := exists_lift_exp δ hδ
  have hq : ∀ t, γ t / δ t ∈ slitPlane := by
    intro t
    have e : γ t / δ t = 1 + (γ t - δ t) / δ t := by field_simp [hδ t]; ring
    rw [e]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr (hδ t))).mpr (by simpa using h t)
  have hqc : Continuous fun t => Complex.log (γ t / δ t) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (continuousAt_clog (hq t)).comp (f := fun t => γ t / δ t)
      (γ.continuous.div δ.continuous hδ).continuousAt
  apply loopDeg_unique γ hγ hγc (L := fun t => M t + Complex.log (γ t / δ t)) (by fun_prop)
    (fun t => by
      rw [Complex.exp_add, hM, Complex.exp_log (div_ne_zero (hγ t) (hδ t))]
      field_simp [hδ t])
  have e := loopDeg_eq_of_lift δ hδ hδc M.continuous hM
  rw [hγc, hδc]
  linear_combination e

/-- T4(a): a continuous nonvanishing function on an arc has a continuous logarithm. -/
theorem hasLogOn_of_arc {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hinj : InjOn γ (Icc 0 1))
    {g : ℂ → ℂ} (hg : ContinuousOn g (γ '' Icc 0 1)) (hg0 : ∀ z ∈ γ '' Icc 0 1, g z ≠ 0) :
    HasLogOn g (γ '' Icc 0 1) := by
  classical
  set A := γ '' Icc (0 : ℝ) 1
  -- the parametrization as a homeomorphism `unitInterval ≃ₜ A`
  let e : unitInterval ≃ A := Equiv.ofBijective (fun t => ⟨γ t, mem_image_of_mem γ t.2⟩)
    ⟨fun s t hst => Subtype.ext (hinj s.2 t.2 (congrArg Subtype.val hst)),
     fun ⟨z, hz⟩ => by obtain ⟨t, ht, rfl⟩ := hz; exact ⟨⟨t, ht⟩, rfl⟩⟩
  have he : Continuous e := by
    refine Continuous.subtype_mk ?_ _
    exact hγ.comp_continuous continuous_subtype_val (fun t => t.2)
  let φ : unitInterval ≃ₜ A := he.homeoOfEquivCompactToT2
  let G : C(unitInterval, ℂ) := ⟨fun t => g (φ t), by
    refine hg.comp_continuous (continuous_subtype_val.comp φ.continuous) (fun t => (φ t).2)⟩
  obtain ⟨L, hL⟩ := exists_lift_exp G (fun t => hg0 _ (φ t).2)
  refine ⟨fun z => if hz : z ∈ A then L (φ.symm ⟨z, hz⟩) else 0, ?_, fun z hz => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : A.restrict (fun z => if hz : z ∈ A then L (φ.symm ⟨z, hz⟩) else 0) =
        fun z => L (φ.symm z) := by
      funext z; exact dif_pos z.2
    rw [this]; fun_prop
  · dsimp only
    rw [dif_pos hz, hL]
    simp [G]

end UCPlanar.Vendored.Topo
