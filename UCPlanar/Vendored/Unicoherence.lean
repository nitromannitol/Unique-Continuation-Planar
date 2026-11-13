/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Topology/Unicoherence.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `LatticeProb.Topology` is renamed `UCPlanar.Vendored.Topology`, and the module
   paths of local imports are changed. -/
import UCPlanar.Vendored.ComplementComponents
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Instances.ZMultiples
import Mathlib.Topology.UrysohnsLemma

/-!
# Unicoherence of the plane

* `exists_continuous_exp_eq`: a continuous nonvanishing function on `ℂ` has a continuous logarithm (lift through
  the covering map `exp : ℂ → ℂ \ {0}`; the plane is simply connected);
* `isPreconnected_inter_of_union_eq_univ`: **the plane is unicoherent** (Eilenberg; Kuratowski, *Topology II*,
  §57): if `ℂ = A ∪ B` with `A` and `B` closed and connected, then `A ∩ B` is connected. If `A ∩ B = P ∪ Q` were a
  separation, an Urysohn function `φ` (`0` on `P`, `1` on `Q`) gives the continuous function equal to
  `exp (iπφ)` on `A` and to `exp (-iπφ)` on `B`; a continuous logarithm `F` of it has `Im F - πφ` constant on `A`
  and `Im F + πφ` constant on `B` (both take values in `2πℤ`), which is impossible at a point of `P` and a point
  of `Q`;
* `isPreconnected_compl_of_mem_connectedComponentsIn_compl`: the complement of a connected component `W` of
  `ℂ \ X`, for `X` closed, connected and nonempty, is connected: it is the union of `X` and of the sets
  `closure W' = W' ∪ frontier W'` over the other components `W'`, each of which meets `X`;
* `isConnected_frontier_of_mem_connectedComponentsIn_compl`: the frontier of a connected component of the
  complement of a closed connected plane set is connected.
-/

namespace UCPlanar.Vendored.Topology

open Set Complex

/-- **Continuous logarithm on the plane.** A continuous nonvanishing function `f : ℂ → ℂ` is `exp ∘ F` for a
continuous `F : ℂ → ℂ`. -/
theorem exists_continuous_exp_eq {f : ℂ → ℂ} (hf : Continuous f) (hf0 : ∀ z, f z ≠ 0) :
    ∃ F : ℂ → ℂ, Continuous F ∧ ∀ z, exp (F z) = f z := by
  let g : C(ℂ, {w : ℂ // w ≠ 0}) := ⟨fun z => ⟨f z, hf0 z⟩, hf.subtype_mk _⟩
  obtain ⟨F, -, hF⟩ := (isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 (log (f 0))
    (Subtype.ext (exp_log (hf0 0)))).exists
  exact ⟨F, F.continuous, fun z => congrArg Subtype.val (congrFun hF z)⟩

/-- If `exp w = exp (t i)` with `t` real, then `Im w - t ∈ 2πℤ`. -/
theorem im_sub_mem_zmultiples_of_exp_eq {w : ℂ} {t : ℝ} (h : exp w = exp (t * I)) :
    w.im - t ∈ AddSubgroup.zmultiples (2 * Real.pi) := by
  have h1 : exp (w - t * I) = 1 := by rw [exp_sub, h, div_self (exp_ne_zero _)]
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 h1
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  rw [zsmul_eq_mul]
  linarith

/-- **The plane is unicoherent** (Eilenberg). If `ℂ = A ∪ B` with `A` and `B` closed and connected, then `A ∩ B`
is connected. -/
theorem isPreconnected_inter_of_union_eq_univ {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B)
    (hAc : IsPreconnected A) (hBc : IsPreconnected B) (hAB : A ∪ B = univ) : IsPreconnected (A ∩ B) := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsub hne
  by_contra hcon
  obtain ⟨hnu, hnv⟩ := not_or.1 hcon
  obtain ⟨q, hqAB, hqu⟩ := not_subset.1 hnu
  obtain ⟨p, hpAB, hpv⟩ := not_subset.1 hnv
  have hqv : q ∈ v := (hsub hqAB).resolve_left hqu
  have hpu : p ∈ u := (hsub hpAB).resolve_right hpv
  have hPQ : Disjoint (A ∩ B ∩ u) (A ∩ B ∩ v) := disjoint_left.2 fun z hzP hzQ => by
    have : z ∈ A ∩ B ∩ (u ∩ v) := ⟨hzP.1, hzP.2, hzQ.2⟩
    rw [hne] at this
    exact this
  obtain ⟨φ, hφP, hφQ, -⟩ :=
    exists_continuous_zero_one_of_isClosed ((hA.inter hB).inter hu) ((hA.inter hB).inter hv) hPQ
  have hφp : φ p = 0 := hφP ⟨hpAB, hpu⟩
  have hφq : φ q = 1 := hφQ ⟨hqAB, hqv⟩
  have hagree : ∀ z ∈ A ∩ B,
      exp (((Real.pi * φ z : ℝ) : ℂ) * I) = exp (((-(Real.pi * φ z) : ℝ) : ℂ) * I) := by
    intro z hz
    rcases hsub hz with h | h
    · rw [show φ z = 0 from hφP ⟨hz, h⟩]
      simp
    · rw [show φ z = 1 from hφQ ⟨hz, h⟩]
      simp [neg_mul, exp_neg]
  let e : ℂ → ℂ := fun z =>
    if z ∈ A then exp (((Real.pi * φ z : ℝ) : ℂ) * I) else exp (((-(Real.pi * φ z) : ℝ) : ℂ) * I)
  have hecont : Continuous e := by
    refine continuous_if (fun z hz => ?_) ?_ ?_
    · have hz' : z ∈ frontier A := hz
      have hzA : z ∈ A := hA.frontier_subset hz'
      have hzB : z ∈ B := by
        rw [← frontier_compl] at hz'
        refine closure_minimal (fun y hy => ?_) hB (frontier_subset_closure hz')
        have : y ∈ A ∪ B := hAB ▸ mem_univ y
        exact this.resolve_left hy
      exact hagree z ⟨hzA, hzB⟩
    · exact Continuous.continuousOn (by fun_prop)
    · exact Continuous.continuousOn (by fun_prop)
  have he0 : ∀ z, e z ≠ 0 := fun z => by
    simp only [e]
    split_ifs <;> exact exp_ne_zero _
  obtain ⟨F, hFc, hF⟩ := exists_continuous_exp_eq hecont he0
  have hmA : MapsTo (fun z => (F z).im - Real.pi * φ z) A (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) :=
    fun z hz => im_sub_mem_zmultiples_of_exp_eq (by rw [hF z]; simp only [e, hz, ↓reduceIte])
  have hmB : MapsTo (fun z => (F z).im - (-(Real.pi * φ z))) B
      (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) := by
    intro z hz
    refine im_sub_mem_zmultiples_of_exp_eq ?_
    rw [hF z]
    simp only [e]
    split_ifs with hzA
    · exact hagree z ⟨hzA, hz⟩
    · rfl
  have hT : IsDiscrete (AddSubgroup.zmultiples (2 * Real.pi) : Set ℝ) :=
    SetLike.isDiscrete_iff_discreteTopology.2 inferInstance
  have hc1 : Continuous fun z => (F z).im - Real.pi * φ z := by fun_prop
  have hc2 : Continuous fun z => (F z).im - (-(Real.pi * φ z)) := by fun_prop
  have h1 := hAc.constant_of_mapsTo hT hc1.continuousOn hmA hpAB.1 hqAB.1
  have h2 := hBc.constant_of_mapsTo hT hc2.continuousOn hmB hpAB.2 hqAB.2
  simp only [hφp, hφq] at h1 h2
  linarith [Real.pi_pos]

/-- **Complements of complementary components are connected.** If `X ⊆ ℂ` is closed, connected and nonempty and
`W` is a connected component of `ℂ \ X`, then `ℂ \ W` is connected. -/
theorem isPreconnected_compl_of_mem_connectedComponentsIn_compl {X W : Set ℂ} (hX : IsClosed X)
    (hXc : IsPreconnected X) (hXne : X.Nonempty) (hW : W ∈ connectedComponentsIn Xᶜ) : IsPreconnected Wᶜ := by
  obtain ⟨x, hx⟩ := hXne
  have hXW : X ⊆ Wᶜ := fun z hz hzW => subset_of_mem_connectedComponentsIn hW hzW hz
  obtain ⟨w₀, -, rfl⟩ := hW
  refine isPreconnected_of_forall x fun y hy => ?_
  by_cases hyX : y ∈ X
  · exact ⟨X, hXW, hx, hyX, hXc⟩
  have hmem : connectedComponentIn Xᶜ y ∈ connectedComponentsIn Xᶜ := ⟨y, hyX, rfl⟩
  have hfr : frontier (connectedComponentIn Xᶜ y) ⊆ X :=
    frontier_subset_of_mem_connectedComponentsIn_compl hX hmem
  have hyW' : y ∈ connectedComponentIn Xᶜ y := mem_connectedComponentIn hyX
  have hfrne : (frontier (connectedComponentIn Xᶜ y)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at h
    rcases isClopen_iff.1 h with h' | h'
    · rw [h'] at hyW'
      exact hyW'
    · have hxW' : x ∈ connectedComponentIn Xᶜ y := h' ▸ mem_univ x
      exact connectedComponentIn_subset _ _ hxW' hx
  obtain ⟨w, hw⟩ := hfrne
  have hunion : IsPreconnected (closure (connectedComponentIn Xᶜ y) ∪ X) :=
    IsPreconnected.union' ⟨w, frontier_subset_closure hw, hfr hw⟩ isPreconnected_connectedComponentIn.closure hXc
  have heq : closure (connectedComponentIn Xᶜ y) ∪ X = connectedComponentIn Xᶜ y ∪ X := by
    rw [closure_eq_self_union_frontier]
    ext z
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hfr h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  refine ⟨connectedComponentIn Xᶜ y ∪ X, ?_, Or.inr hx, Or.inl hyW', heq ▸ hunion⟩
  rintro z (hz | hz)
  · intro hzW
    apply hy
    rw [connectedComponentIn_eq hzW, ← connectedComponentIn_eq hz]
    exact hyW'
  · exact hXW hz

/-- **The frontier of a complementary component is connected.** If `K ⊆ ℂ` is closed and connected, the frontier
of every connected component of `ℂ \ K` is connected. -/
theorem isConnected_frontier_of_mem_connectedComponentsIn_compl {K C : Set ℂ} (hK : IsClosed K)
    (hKc : IsConnected K) (hC : C ∈ connectedComponentsIn Kᶜ) : IsConnected (frontier C) := by
  have hCo := isOpen_of_mem_connectedComponentsIn_compl hK hC
  have hCc := isConnected_of_mem_connectedComponentsIn hC
  have hCK : C ⊆ Kᶜ := subset_of_mem_connectedComponentsIn hC
  have hcompl :=
    isPreconnected_compl_of_mem_connectedComponentsIn_compl hK hKc.isPreconnected hKc.nonempty hC
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at h
    rcases isClopen_iff.1 h with h' | h'
    · exact hCc.nonempty.ne_empty h'
    · obtain ⟨k, hk⟩ := hKc.nonempty
      exact hCK (h' ▸ mem_univ k) hk
  · rw [hCo.frontier_eq, sdiff_eq]
    refine isPreconnected_inter_of_union_eq_univ isClosed_closure hCo.isClosed_compl
      hCc.isPreconnected.closure hcompl (eq_univ_of_forall fun z => ?_)
    by_cases hz : z ∈ C
    · exact Or.inl (subset_closure hz)
    · exact Or.inr hz

end UCPlanar.Vendored.Topology
