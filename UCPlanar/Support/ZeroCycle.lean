/- Step 3 of Section 3: the cycle around the filled cluster of faces meeting the set where the
harmonic function is large, and the linear lower bound it forces on the number of such vertices
near the chosen sphere. -/
import UCPlanar.Support.ZeroGeom
import UCPlanar.Support.PlanarMetric
import UCPlanar.Frozen.Topological
import Mathlib

open scoped BigOperators Classical

/-- A vertex within the buffer `r` of the sphere of radius `m` which lies outside `W`. -/
def UCPlanar.NearBoundaryOutside {V : Type*} (G : SimpleGraph V) (W : Set V) (o : V) (m r : ℕ)
    (z : V) : Prop :=
  ∃ y, G.dist z y ≤ r ∧ y ∉ W ∧ m ≤ G.dist o y + r ∧ G.dist o y ≤ m + r

/-- **The cycle produced by Step 3 of Section 3.**  The connected cluster of faces of `G[B_m]`
meeting the complement of `W`, with the bounded components of its complement filled in, has a
boundary cycle `γ` with the following properties: `x₀` lies in the plane region it bounds, that
region reaches the sphere of radius `m`, every vertex on it either sits within the buffer of that
sphere next to a vertex outside `W` or lies in `W` itself, every such vertex of `W` carries a
face path to both sign sets inside the region, and every component of a sign set inside the
region reaches a vertex of `γ` within the buffer.  The finite set `D` is discarded: its
vertices carry no face path, and the sign components may reach them instead. -/
def UCPlanar.PeriodicPlaneGraph.SurroundedBy {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V)
    (r : ℕ) (W Pos Neg : Set V) (D : Finset V) (o : V) (m : ℕ) (x₀ : V) : Prop :=
  ∃ (b : V) (γ : Q.graph.Walk b b), γ.IsCycle ∧
    x₀ ∈ Q.embedding.cycleRegion γ ∧
    (∃ u ∈ Q.embedding.cycleRegion γ, m ≤ Q.graph.dist o u + r) ∧
    (∀ z ∈ γ.support, ¬ UCPlanar.NearBoundaryOutside Q.graph W o m r z → z ∈ W) ∧
    (∀ z ∈ γ.support, ¬ UCPlanar.NearBoundaryOutside Q.graph W o m r z → z ∉ D →
      Q.embedding.FacePathToSigns {x | x ∈ Q.embedding.cycleRegion γ ∧ x ∈ Pos}
        {x | x ∈ Q.embedding.cycleRegion γ ∧ x ∈ Neg} z) ∧
    UCPlanar.ComponentsMeetBoundary Q.graph
      {x | x ∈ Q.embedding.cycleRegion γ ∧ x ∈ Pos}
      {z | z ∈ γ.support ∧ (UCPlanar.NearBoundaryOutside Q.graph W o m r z ∨ z ∈ D)} ∧
    UCPlanar.ComponentsMeetBoundary Q.graph
      {x | x ∈ Q.embedding.cycleRegion γ ∧ x ∈ Neg}
      {z | z ∈ γ.support ∧ (UCPlanar.NearBoundaryOutside Q.graph W o m r z ∨ z ∈ D)}

namespace UCPlanar.Support

/-- **Step 3 of Section 3.**  Granting the boundary cycle of the filled cluster, the topological
lemma forces linearly many vertices outside `W` within the buffer of the sphere of radius `m`:
a fixed fraction of the cycle lies in that buffer, the cycle is long because the region it
bounds contains both `x₀` and a vertex at distance `m` from the centre, and each buffer vertex
of the cycle is charged to a vertex outside `W` with bounded multiplicity.  The discarded set
enters only through its cardinality. -/
theorem surround_step3 {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (d L r : ℕ)
    (hd : ∀ x, Q.graph.degree x ≤ d) (hL : Q.embedding.FaceBound L) :
    ∃ κ C₀ : ℝ, 0 < κ ∧ 0 ≤ C₀ ∧ ∀ (o : V) (m n : ℕ) (W Pos Neg : Set V) (D : Finset V)
      (x₀ : V) (S : Finset V),
      Disjoint W Pos → Disjoint W Neg → Disjoint Pos Neg →
      Q.graph.dist o x₀ ≤ n → 3 * n ≤ 2 * m →
      (∀ y, y ∉ W → m ≤ Q.graph.dist o y + r → Q.graph.dist o y ≤ m + r → y ∈ S) →
      Q.SurroundedBy r W Pos Neg D o m x₀ →
      κ * (n : ℝ) ≤ (S.card : ℝ) * (((r + 1) * (d + 1) ^ r : ℕ) : ℝ) + (D.card : ℝ) + C₀ := by
  classical
  obtain ⟨α, hα0, hα1, htop⟩ := UCPlanar.Frozen.topological (V := V) d L
  obtain ⟨C, hC0, hC⟩ := cycleRegion_dist_le Q
  refine ⟨(1 - α) / (2 * C), (1 - α) * ((r : ℝ) / C + 1), by positivity, by positivity, ?_⟩
  intro o m n W Pos Neg D x₀ S hWP hWN hPN hx₀ hmn hS hsur
  obtain ⟨b, γ, hcyc, hin, ⟨u, hux, hfar⟩, hzero, hface, hpos, hneg⟩ := hsur
  set Near : V → Prop := fun z => UCPlanar.NearBoundaryOutside Q.graph W o m r z with hNear
  set Z : Finset V := γ.support.toFinset.filter (fun z => ¬ Near z ∧ z ∉ D) with hZ
  set Pset : Set V := {x | x ∈ Q.embedding.cycleRegion γ ∧ x ∈ Pos} with hP
  set Mset : Set V := {x | x ∈ Q.embedding.cycleRegion γ ∧ x ∈ Neg} with hM
  have hZsupp : Z ⊆ γ.support.toFinset := Finset.filter_subset _ _
  have hZW : ∀ z ∈ Z, z ∈ W := by
    intro z hz
    rw [hZ, Finset.mem_filter, List.mem_toFinset] at hz
    exact hzero z hz.1 hz.2.1
  have hbdry : ((γ.support.toFinset : Set V) \ (Z : Set V))
      = {z | z ∈ γ.support ∧ (Near z ∨ z ∈ D)} := by
    ext z
    simp only [Set.mem_sdiff, Finset.mem_coe, List.mem_toFinset, hZ, Finset.mem_filter,
      Set.mem_setOf_eq]
    tauto
  have hkey : (Z.card : ℝ) ≤ α * γ.support.toFinset.card := by
    refine htop Q hd hL b γ hcyc Z Pset Mset ?_ ?_ ?_ hZsupp ?_ ?_ ?_ ?_ ?_
    · refine Set.disjoint_left.mpr ?_
      intro z hz hzP
      simp only [hP, Set.mem_setOf_eq] at hzP
      exact Set.disjoint_left.mp hWP (hZW z (Finset.mem_coe.mp hz)) hzP.2
    · refine Set.disjoint_left.mpr ?_
      intro z hz hzM
      simp only [hM, Set.mem_setOf_eq] at hzM
      exact Set.disjoint_left.mp hWN (hZW z (Finset.mem_coe.mp hz)) hzM.2
    · refine Set.disjoint_left.mpr ?_
      intro z hzP hzM
      simp only [hP, Set.mem_setOf_eq] at hzP
      simp only [hM, Set.mem_setOf_eq] at hzM
      exact Set.disjoint_left.mp hPN hzP.2 hzM.2
    · intro x hx; exact hx.1
    · intro x hx; exact hx.1
    · intro z hz
      rw [hZ, Finset.mem_filter, List.mem_toFinset] at hz
      exact hface z hz.1 hz.2.1 hz.2.2
    · rw [hbdry]; exact hpos
    · rw [hbdry]; exact hneg
  -- the cycle is long, because it surrounds both `x₀` and a vertex near the sphere
  have hdist := hC b γ x₀ u hin hux
  have htri := Q.connected.dist_triangle (u := o) (v := x₀) (w := u)
  have hlow : m ≤ n + r + Q.graph.dist x₀ u := by omega
  have hlowR : (m : ℝ) ≤ (n : ℝ) + r + (Q.graph.dist x₀ u : ℝ) := by exact_mod_cast hlow
  have hmnR : 3 * (n : ℝ) ≤ 2 * m := by exact_mod_cast hmn
  have hlen : (n : ℝ) / 2 - r ≤ C * ((γ.length : ℝ) + 1) := by linarith
  have hcardlen : (γ.length : ℝ) ≤ (γ.support.toFinset.card : ℝ) := by
    exact_mod_cast length_le_card_support γ hcyc
  have hgamma : (n : ℝ) / (2 * C) - (r : ℝ) / C - 1 ≤ (γ.support.toFinset.card : ℝ) := by
    have h1 : (n : ℝ) / 2 - r ≤ C * (γ.support.toFinset.card + 1) := by nlinarith [hlen, hcardlen]
    have h2 : ((n : ℝ) / 2 - r) / C ≤ (γ.support.toFinset.card : ℝ) + 1 :=
      (div_le_iff₀ hC0).mpr (by linarith [h1])
    have h3 : ((n : ℝ) / 2 - r) / C = (n : ℝ) / (2 * C) - (r : ℝ) / C := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  -- the part of the cycle outside `Z` is charged to the vertices outside `W` near the sphere
  have hcharge : ((γ.support.toFinset.filter (fun z => Near z)).card : ℝ)
      ≤ (S.card : ℝ) * (((r + 1) * (d + 1) ^ r : ℕ) : ℝ) := by
    have hsub : γ.support.toFinset.filter (fun z => Near z)
        ⊆ γ.support.toFinset.filter (fun z => ∃ y ∈ S, Q.graph.dist z y ≤ r) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      obtain ⟨y, hzy, hfy, h1, h2⟩ := hz.2
      exact ⟨hz.1, y, hS y hfy h1 h2, hzy⟩
    have hmain := UCPlanar.Support.card_near_boundary_le Q.connected γ.support.toFinset S d r hd
    have := (Finset.card_le_card hsub).trans hmain
    exact_mod_cast this
  have hsplitN : γ.support.toFinset
      ⊆ Z ∪ (γ.support.toFinset.filter (fun z => Near z)) ∪ D := by
    intro z hz
    by_cases hn : Near z
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hz, hn⟩))
    · by_cases hdz : z ∈ D
      · exact Finset.mem_union_right _ hdz
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (by rw [hZ, Finset.mem_filter]; exact ⟨hz, hn, hdz⟩))
  have hsplit : (γ.support.toFinset.card : ℝ)
      ≤ (Z.card : ℝ) + ((γ.support.toFinset.filter (fun z => Near z)).card : ℝ)
        + (D.card : ℝ) := by
    have h1 := Finset.card_le_card hsplitN
    have h2 := Finset.card_union_le (Z ∪ (γ.support.toFinset.filter (fun z => Near z))) D
    have h3 := Finset.card_union_le Z (γ.support.toFinset.filter (fun z => Near z))
    have : γ.support.toFinset.card ≤ Z.card
        + (γ.support.toFinset.filter (fun z => Near z)).card + D.card := by omega
    exact_mod_cast this
  have hfinal : (1 - α) * (γ.support.toFinset.card : ℝ)
      ≤ ((γ.support.toFinset.filter (fun z => Near z)).card : ℝ) + (D.card : ℝ) := by
    linarith [hkey, hsplit]
  have hαpos : 0 < 1 - α := by linarith
  have hstep : (1 - α) * ((n : ℝ) / (2 * C) - (r : ℝ) / C - 1)
      ≤ (1 - α) * (γ.support.toFinset.card : ℝ) :=
    mul_le_mul_of_nonneg_left hgamma (le_of_lt hαpos)
  have hexp : (1 - α) * ((n : ℝ) / (2 * C) - (r : ℝ) / C - 1)
      = (1 - α) / (2 * C) * (n : ℝ) - (1 - α) * ((r : ℝ) / C + 1) := by
    field_simp
    ring
  linarith [hstep, hfinal, hcharge, hexp.le, hexp.ge]

end UCPlanar.Support
