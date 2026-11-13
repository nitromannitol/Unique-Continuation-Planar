/- Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability, Apache-2.0),
   file LatticeProb/Topology/ComplementComponents.lean at commit c7e340ba2ea76157e90224e9dc3bc6a07083fe0f.
   The namespace `LatticeProb.Topology` is renamed `UCPlanar.Vendored.Topology`, and the module
   paths of local imports are changed. -/
import UCPlanar.Vendored.PlaneTopology

/-!
# Complementary components of closed plane sets, cut points and simple loops

Elementary facts behind Torhorst's theorem on the boundaries of the complementary domains of a locally connected
plane continuum (Torhorst (1921); Whyburn, *Analytic Topology*, Chapter VI). For a closed set `K ⊆ ℂ` and a
connected component `C` of `ℂ \ K`:

* `C` is open and connected (`isOpen_of_mem_connectedComponentsIn_compl`,
  `isConnected_of_mem_connectedComponentsIn`);
* the frontier of `C` lies in `K` (`frontier_subset_of_mem_connectedComponentsIn_compl`) and is compact when `K`
  is compact (`isCompact_frontier_of_mem_connectedComponentsIn_compl`);
* the frontier of `C` has two points when `K` has two points
  (`frontier_nontrivial_of_mem_connectedComponentsIn_compl`): otherwise `C` would be closed and open in the plane
  punctured at one point.

Two reformulations of the hypotheses and of the conclusion of Torhorst's theorem:

* `isSimpleLoop_iff_nonempty_homeomorph`: a subset of `ℂ` is a simple loop iff it is homeomorphic to the circle;
* `forall_not_isCutPoint_iff`: a set with two points has no cut point iff `A \ {a}` is connected for every
  `a ∈ A`.
-/

namespace UCPlanar.Vendored.Topology

open Set
open scoped _root_.Topology

/-- A member of `connectedComponentsIn F` is connected. -/
theorem isConnected_of_mem_connectedComponentsIn {α : Type*} [TopologicalSpace α] {F S : Set α}
    (hS : S ∈ connectedComponentsIn F) : IsConnected S := by
  obtain ⟨x, hx, rfl⟩ := hS
  exact isConnected_connectedComponentIn_iff.2 hx

/-- A member of `connectedComponentsIn F` is contained in `F`. -/
theorem subset_of_mem_connectedComponentsIn {α : Type*} [TopologicalSpace α] {F S : Set α}
    (hS : S ∈ connectedComponentsIn F) : S ⊆ F := by
  obtain ⟨x, -, rfl⟩ := hS
  exact connectedComponentIn_subset F x

variable {K C : Set ℂ}

/-- A connected component of the complement of a closed plane set is open. -/
theorem isOpen_of_mem_connectedComponentsIn_compl (hK : IsClosed K)
    (hC : C ∈ connectedComponentsIn Kᶜ) : IsOpen C := by
  obtain ⟨x, -, rfl⟩ := hC
  exact hK.isOpen_compl.connectedComponentIn

/-- The frontier of a connected component of the complement of a closed plane set `K` lies in `K`. -/
theorem frontier_subset_of_mem_connectedComponentsIn_compl (hK : IsClosed K)
    (hC : C ∈ connectedComponentsIn Kᶜ) : frontier C ⊆ K := by
  have hCo := isOpen_of_mem_connectedComponentsIn_compl hK hC
  obtain ⟨x, -, rfl⟩ := hC
  intro z hz
  by_contra hzK
  have hzK' : z ∈ Kᶜ := hzK
  have hnhds : connectedComponentIn Kᶜ z ∈ 𝓝 z :=
    hK.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hzK')
  obtain ⟨y, hyz, hyx⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hz) _ hnhds
  have hzx : z ∈ connectedComponentIn Kᶜ x := by
    rw [connectedComponentIn_eq hyx, ← connectedComponentIn_eq hyz]
    exact mem_connectedComponentIn hzK'
  rw [hCo.frontier_eq] at hz
  exact hz.2 hzx

/-- The frontier of a connected component of the complement of a compact plane set is compact. -/
theorem isCompact_frontier_of_mem_connectedComponentsIn_compl (hK : IsCompact K)
    (hC : C ∈ connectedComponentsIn Kᶜ) : IsCompact (frontier C) :=
  hK.of_isClosed_subset isClosed_frontier
    (frontier_subset_of_mem_connectedComponentsIn_compl hK.isClosed hC)

/-- If the frontier of a connected component `C` of `ℂ \ K` (with `K` closed) lies in `{p}`, then `K ⊆ {p}`:
`C` is closed and open in the connected set `ℂ \ {p}`. -/
theorem subset_singleton_of_frontier_subset_singleton (hK : IsClosed K)
    (hC : C ∈ connectedComponentsIn Kᶜ) {p : ℂ} (hp : frontier C ⊆ {p}) : K ⊆ {p} := by
  have hCo := isOpen_of_mem_connectedComponentsIn_compl hK hC
  have hCK := subset_of_mem_connectedComponentsIn hC
  obtain ⟨c₀, hc₀⟩ := (isConnected_of_mem_connectedComponentsIn hC).nonempty
  have hne : ∃ c ∈ C, c ≠ p := by
    by_contra h
    push Not at h
    have hCp : C = {p} :=
      eq_singleton_iff_unique_mem.2 ⟨h c₀ hc₀ ▸ hc₀, fun c hc => h c hc⟩
    exact not_isOpen_singleton p (hCp ▸ hCo)
  obtain ⟨c, hc, hcp⟩ := hne
  have hpre : IsPreconnected ({p}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) p).isPreconnected
  have hsub : ({p}ᶜ : Set ℂ) ⊆ C := by
    refine hpre.subset_of_closure_inter_subset hCo ⟨c, hcp, hc⟩ ?_
    rintro z ⟨hzc, hzp⟩
    by_contra hzC
    have hzf : z ∈ frontier C := by
      rw [hCo.frontier_eq]
      exact ⟨hzc, hzC⟩
    exact hzp (hp hzf)
  intro k hk
  by_contra hkp
  exact hCK (hsub hkp) hk

/-- The frontier of a connected component of the complement of a closed plane set with two points has two
points. -/
theorem frontier_nontrivial_of_mem_connectedComponentsIn_compl (hK : IsClosed K) (hKn : K.Nontrivial)
    (hC : C ∈ connectedComponentsIn Kᶜ) : (frontier C).Nontrivial := by
  by_contra h
  rw [not_nontrivial_iff] at h
  obtain ⟨p, hp⟩ : ∃ p : ℂ, frontier C ⊆ {p} := by
    rcases h.eq_empty_or_singleton with h0 | ⟨p, hp⟩
    · exact ⟨0, h0 ▸ empty_subset _⟩
    · exact ⟨p, hp.le⟩
  exact hKn.not_subset_singleton (subset_singleton_of_frontier_subset_singleton hK hC hp)

/-- A subset of `ℂ` is a simple loop iff it is homeomorphic to the unit circle. -/
theorem isSimpleLoop_iff_nonempty_homeomorph {Γ : Set ℂ} : IsSimpleLoop Γ ↔ Nonempty (Circle ≃ₜ Γ) := by
  constructor
  · rintro ⟨φ, hφc, hφi, rfl⟩
    exact ⟨(hφc.isClosedEmbedding hφi).isEmbedding.toHomeomorph⟩
  · rintro ⟨e⟩
    refine ⟨fun z => (e z : ℂ), continuous_subtype_val.comp e.continuous, ?_, ?_⟩
    · intro a b hab
      exact e.injective (Subtype.ext hab)
    · ext w
      constructor
      · rintro ⟨z, rfl⟩
        exact (e z).2
      · intro hw
        exact ⟨e.symm ⟨w, hw⟩, by simp⟩

/-- A subset of `ℂ` with two points has no cut point iff removing any one of its points leaves a connected set. -/
theorem forall_not_isCutPoint_iff {A : Set ℂ} (hA : A.Nontrivial) :
    (∀ a, ¬ IsCutPoint A a) ↔ ∀ a ∈ A, IsConnected (A \ {a}) := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, hba⟩ := hA.exists_ne a
    exact ⟨⟨b, hb, hba⟩, not_not.1 fun hp => h a ⟨ha, hp⟩⟩
  · rintro h a ⟨ha, hp⟩
    exact hp (h a ha).isPreconnected

end UCPlanar.Vendored.Topology
