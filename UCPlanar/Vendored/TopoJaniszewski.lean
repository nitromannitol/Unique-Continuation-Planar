/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Bonanno/QuantumZipper/Proofs/Complex/TopoJaniszewski.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `QuantumZipper.CA.Topo` is renamed `UCPlanar.Vendored.Topo`, and the module paths
   of local imports are changed. -/
/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.TopoJaniszewski at commit 31e7483; only the module paths of local imports are changed. -/
import UCPlanar.Vendored.TopoEilenberg

/-!
# Janiszewski's theorem and non-separation by arcs (EXT-CA nodes T3, T4(b))

* `janiszewski` (T3): if the compact sets `A`, `B` do not separate `a, b ∉ A ∪ B` and `A ∩ B`
  is preconnected (e.g. empty or connected), then `A ∪ B` does not separate `a` and `b`:
  ```
  theorem janiszewski {A B : Set ℂ} {a b : ℂ} (hA : IsCompact A) (hB : IsCompact B)
      (hAB : IsPreconnected (A ∩ B)) (ha : a ∉ A ∪ B) (hb : b ∉ A ∪ B)
      (h₁ : b ∈ connectedComponentIn Aᶜ a) (h₂ : b ∈ connectedComponentIn Bᶜ a) :
      b ∈ connectedComponentIn (A ∪ B)ᶜ a
  ```
* `IsArcSet`, `mem_connectedComponentIn_compl_arc`, `not_sep_arc` (T4(b)): an arc does not
  separate the plane.

**Source.** R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021),
Exercise 4.37(ii) (Z. Janiszewski 1913) and its hint, printed p. 215, PDF p. 240: by 4.37(i)
(Eilenberg, node T2) `f z = (z - a)/(z - b)` has continuous logarithms `L_A` on `A`, `L_B` on `B`;
on `A ∩ B` their difference is continuous with values in `2πiℤ`, hence constant (preconnected);
shifting `L_B` by this constant and pasting gives a continuous logarithm on `A ∪ B`, and the other
direction of 4.37(i) concludes. We follow this proof verbatim (Burckel's hypothesis "void or
connected" is the preconnectedness of `A ∩ B`).
T4(b) is Burckel's route as well: an arc carries a continuous logarithm of every zero-free
continuous function (node T1, `hasLogOn_of_arc`), then 4.37(i).
-/

open Complex Set Metric Real

namespace UCPlanar.Vendored.Topo

/-- **T3 (Janiszewski's theorem**; Burckel Ex. 4.37(ii)). If neither of the compact sets `A`, `B`
separates `a, b ∉ A ∪ B` and `A ∩ B` is preconnected, then `A ∪ B` does not separate `a`, `b`. -/
theorem janiszewski {A B : Set ℂ} {a b : ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : IsPreconnected (A ∩ B)) (ha : a ∉ A ∪ B) (hb : b ∉ A ∪ B)
    (h₁ : b ∈ connectedComponentIn Aᶜ a) (h₂ : b ∈ connectedComponentIn Bᶜ a) :
    b ∈ connectedComponentIn (A ∪ B)ᶜ a := by
  obtain ⟨LA, hLAc, hLA⟩ := hasLogOn_of_not_separates hA h₁
  obtain ⟨LB, hLBc, hLB⟩ := hasLogOn_of_not_separates hB h₂
  have hf0 : ∀ z ∈ A ∪ B, (z - a) / (z - b) ≠ 0 := fun z hz =>
    div_ne_zero (sub_ne_zero.2 fun h => ha (h ▸ hz)) (sub_ne_zero.2 fun h => hb (h ▸ hz))
  have hexp : ∀ z ∈ A ∩ B, exp (LA z - LB z) = 1 := fun z hz => by
    rw [Complex.exp_sub, hLA z hz.1, hLB z hz.2, div_self (hf0 z (Or.inl hz.1))]
  -- the two logarithms differ by a constant `c ∈ 2πiℤ` on the preconnected set `A ∩ B`
  have hconst : ∃ c : ℂ, exp c = 1 ∧ ∀ z ∈ A ∩ B, LA z = LB z + c := by
    rcases (A ∩ B).eq_empty_or_nonempty with h | ⟨z₀, hz₀⟩
    · exact ⟨0, exp_zero, by simp [h]⟩
    refine ⟨LA z₀ - LB z₀, hexp z₀ hz₀, fun z hz => ?_⟩
    have h2 := two_pi_I_ne_zero'
    have hmaps : MapsTo (fun z => (LA z - LB z) / (2 * π * I)) (A ∩ B)
        (range ((↑) : ℤ → ℂ)) := by
      intro z hz
      obtain ⟨n, hn⟩ := exp_eq_one_iff.1 (hexp z hz)
      exact ⟨n, by simp only [hn, mul_div_cancel_right₀ _ h2]⟩
    have hc : (LA z - LB z) / (2 * π * I) = (LA z₀ - LB z₀) / (2 * π * I) :=
      hAB.constant_of_mapsTo Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range
        (((hLAc.mono inter_subset_left).sub (hLBc.mono inter_subset_right)).div_const _)
        hmaps hz hz₀
    have := (div_left_inj' h2).1 hc
    linear_combination this
  obtain ⟨c, hc1, hc⟩ := hconst
  classical
  refine not_separates_of_hasLogOn (hA.union hB) ha hb
    ⟨fun z => if z ∈ A then LA z else LB z + c, ?_, fun z hz => ?_⟩
  · refine ContinuousOn.union_of_isClosed ?_ ?_ hA.isClosed hB.isClosed
    · exact hLAc.congr fun z hz => ite_eq_left_iff.2 fun h => absurd hz h
    · refine (hLBc.add (continuousOn_const (c := c))).congr fun z hz => ?_
      by_cases hzA : z ∈ A
      · simp [hzA, hc z ⟨hzA, hz⟩]
      · simp [hzA]
  · dsimp only
    split_ifs with hzA
    · exact hLA z hzA
    · rw [Complex.exp_add, hLB z (hz.resolve_left hzA), hc1, mul_one]

/-- An arc: the image of `[0,1]` under a continuous injective map. -/
def IsArcSet (A : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1) ∧ A = γ '' Icc 0 1

/-- An arc is compact. -/
theorem IsArcSet.isCompact {A : Set ℂ} (hA : IsArcSet A) : IsCompact A := by
  obtain ⟨γ, hγ, -, rfl⟩ := hA
  exact isCompact_Icc.image_of_continuousOn hγ

end UCPlanar.Vendored.Topo
