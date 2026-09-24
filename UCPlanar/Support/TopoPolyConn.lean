/- Two connectedness of the finite plane graph drawn by an edge set with a second edge at every
vertex and no splitting vertex. -/
import UCPlanar.Support.TopoPolyWalk
import Mathlib

open Set
open scoped Classical
open scoped Graph

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **An edge set with no splitting vertex stays connected when one vertex is deleted.**  The
two parts are the edges the walks from a fixed vertex reach without passing through `v` and the
edges they do not; a vertex other than `v` lying on both would be reached as well, so the parts
share only `v` and the hypothesis empties the second one. -/
theorem reachable_avoiding_of_no_split {T : Finset (Sym2 V)}
    (hT : ↑T ⊆ G.edgeSet)
    (hsplit : ∀ T₁ T₂ : Finset (Sym2 V), T₁ ⊆ T → T₂ ⊆ T → (∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) →
      Disjoint T₁ T₂ → ∀ v : V,
      (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) → T₁ = ∅ ∨ T₂ = ∅)
    (v : V) {a : V} {e₀ : Sym2 V} (he₀ : e₀ ∈ T) (ha : a ∈ e₀) (hav : a ≠ v) :
    ∀ f ∈ T, ∀ y : V, y ∈ f → y ≠ v →
      ∃ w : G.Walk a y, (∀ g ∈ w.edges, g ∈ T) ∧ ∀ z ∈ w.support, z ≠ v := by
  classical
  have hpair : ∀ (g : Sym2 V) (y y' : V), y ∈ g → y' ∈ g → y ≠ y' → g = s(y, y') := by
    refine Sym2.ind ?_
    intro p q y y' hy hy' hne
    rw [Sym2.mem_iff] at hy hy'
    rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact absurd rfl hne
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hne
  set R : Set V := {y | ∃ w : G.Walk a y, (∀ g ∈ w.edges, g ∈ T) ∧ ∀ z ∈ w.support, z ≠ v}
    with hRdef
  have haR : a ∈ R := ⟨SimpleGraph.Walk.nil, by simp, by simpa using hav⟩
  have hstep : ∀ g ∈ T, ∀ y : V, y ∈ g → y ∈ R → ∀ y' : V, y' ∈ g → y' ≠ v → y' ∈ R := by
    intro g hg y hy hyR y' hy' hy'v
    by_cases hyy : y' = y
    · exact hyy ▸ hyR
    · have hgs : g = s(y, y') := hpair g y y' hy hy' (fun hc => hyy hc.symm)
      have hadj : G.Adj y y' := by
        have hge : g ∈ G.edgeSet := hT hg
        rw [hgs] at hge
        exact hge
      obtain ⟨w, hw, hsup⟩ := hyR
      refine ⟨w.concat hadj, ?_, ?_⟩
      · intro q hq
        rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append, List.mem_append] at hq
        rcases hq with h1 | h1
        · exact hw q h1
        · rw [List.mem_singleton] at h1
          rw [h1, ← hgs]
          exact hg
      · intro z hz
        rw [SimpleGraph.Walk.support_concat, List.mem_append] at hz
        rcases hz with h1 | h1
        · exact hsup z h1
        · rw [List.mem_singleton] at h1
          rw [h1]
          exact hy'v
  have h1 : T.filter (fun g => ∃ y ∈ g, y ∈ R) ⊆ T := Finset.filter_subset _ _
  have h2 : T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R) ⊆ T := Finset.filter_subset _ _
  have hcover : ∀ g ∈ T, g ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R) ∨
      g ∈ T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R) := by
    intro g hg
    by_cases hc : ∃ y ∈ g, y ∈ R
    · exact Or.inl (Finset.mem_filter.mpr ⟨hg, hc⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hg, hc⟩)
  have hdisj : Disjoint (T.filter (fun g => ∃ y ∈ g, y ∈ R))
      (T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R)) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    exact (Finset.mem_filter.mp hg2).2 (Finset.mem_filter.mp hg1).2
  have hmeet : ∀ w : V, (∃ g ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R), w ∈ g) →
      (∃ h ∈ T.filter (fun g => ¬ ∃ y ∈ g, y ∈ R), w ∈ h) → w = v := by
    rintro w ⟨g, hg, hwg⟩ ⟨h, hh, hwh⟩
    by_contra hwv
    obtain ⟨hgT, y, hyg, hyR⟩ := Finset.mem_filter.mp hg
    exact (Finset.mem_filter.mp hh).2 ⟨w, hwh, hstep g hgT y hyg hyR w hwg hwv⟩
  rcases hsplit _ _ h1 h2 hcover hdisj v hmeet with hE | hE
  · exfalso
    have hmem : e₀ ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R) :=
      Finset.mem_filter.mpr ⟨he₀, ⟨a, ha, haR⟩⟩
    rw [hE] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · intro f hf y hy hyv
    have hfT : f ∈ T.filter (fun g => ∃ y ∈ g, y ∈ R) := by
      rcases hcover f hf with h | h
      · exact h
      · rw [hE] at h
        exact absurd h (Finset.notMem_empty _)
    obtain ⟨-, y', hy', hy'R⟩ := Finset.mem_filter.mp hfT
    exact hstep f hf y' hy' hy'R y hy hyv

/-- Three distinct drawn vertices, from an edge and a second edge at one of its ends. -/
theorem hasThreeVertices_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Finset (Sym2 V)}
    (hT : ↑T ⊆ G.edgeSet)
    (hdeg : ∀ e ∈ T, ∀ z : V, z ∈ e → ∃ f ∈ T, f ≠ e ∧ z ∈ f)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ T) :
    (edgeGraph E ↑T).HasThreeVertices := by
  have he₀G : e₀ ∈ G.edgeSet := hT he₀
  set a := e₀.out.1 with hadef
  set b := e₀.out.2 with hbdef
  have hab : G.Adj a b := adj_out he₀G
  have hae : a ∈ e₀ := Sym2.out_fst_mem e₀
  have hbe : b ∈ e₀ := Sym2.out_snd_mem e₀
  obtain ⟨f, hf, hfe, haf⟩ := hdeg e₀ he₀ a hae
  obtain ⟨c, hfc⟩ := exists_mk_of_mem haf
  have hfG : f ∈ G.edgeSet := hT hf
  have hac : G.Adj a c := by rw [← SimpleGraph.mem_edgeSet, ← hfc]; exact hfG
  have hcb : c ≠ b := by
    rintro rfl
    exact hfe (by rw [hfc, hadef, hbdef, mk_out])
  refine ⟨planeHomeo (E.pos a), mem_vertexSet_edgeGraph E he₀ he₀G hae,
    planeHomeo (E.pos b), mem_vertexSet_edgeGraph E he₀ he₀G hbe,
    planeHomeo (E.pos c), mem_vertexSet_edgeGraph E hf hfG (by rw [hfc]; simp),
    ?_, ?_, ?_⟩
  · exact fun h => hab.ne (posHomeo_injective E h)
  · exact fun h => hac.ne (posHomeo_injective E h)
  · exact fun h => hcb (posHomeo_injective E h).symm

/-- **The drawn plane graph of a connected edge set is connected.** -/
theorem connected_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Finset (Sym2 V)}
    (hT : ↑T ⊆ G.edgeSet)
    (hsplit : ∀ T₁ T₂ : Finset (Sym2 V), T₁ ⊆ T → T₂ ⊆ T → (∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) →
      Disjoint T₁ T₂ → ∀ v : V,
      (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) → T₁ = ∅ ∨ T₂ = ∅)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ T) :
    (edgeGraph E ↑T).Connected := by
  have he₀G : e₀ ∈ G.edgeSet := hT he₀
  have hae : e₀.out.1 ∈ e₀ := Sym2.out_fst_mem e₀
  refine Graph.Connected.of_hub (mem_vertexSet_edgeGraph E he₀ he₀G hae) ?_
  rintro q ⟨z, ⟨g, hg, hgG, hz⟩, rfl⟩
  obtain ⟨w, hw⟩ := reachable_of_no_split hT hsplit he₀ hae g (by exact_mod_cast hg) z hz
  exact ⟨w.edges, isWalk_of_walk E w (fun e he => by exact_mod_cast hw e he)
    (mem_vertexSet_edgeGraph E he₀ he₀G hae)⟩

/-- **The drawn plane graph stays connected when a vertex is deleted.** -/
theorem deleteVerts_connected_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Finset (Sym2 V)}
    (hT : ↑T ⊆ G.edgeSet)
    (hdeg : ∀ e ∈ T, ∀ z : V, z ∈ e → ∃ f ∈ T, f ≠ e ∧ z ∈ f)
    (hsplit : ∀ T₁ T₂ : Finset (Sym2 V), T₁ ⊆ T → T₂ ⊆ T → (∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) →
      Disjoint T₁ T₂ → ∀ v : V,
      (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) → T₁ = ∅ ∨ T₂ = ∅)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ T) {x : Schoenflies.Plane} (hx : x ∈ V(edgeGraph E ↑T)) :
    ((edgeGraph E ↑T).deleteVerts {x}).Connected := by
  obtain ⟨v₀, -, rfl⟩ := hx
  -- a vertex of the drawing other than the deleted one
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := hasThreeVertices_edgeGraph E hT hdeg he₀
  have hex : ∃ s ∈ V(edgeGraph E ↑T), s ≠ planeHomeo (E.pos v₀) := by
    by_cases h1 : p = planeHomeo (E.pos v₀)
    · exact ⟨q, hq, fun h2 => hpq (h1.trans h2.symm)⟩
    · exact ⟨p, hp, h1⟩
  obtain ⟨s, ⟨a₁, ⟨e₁, he₁, he₁G, ha₁⟩, rfl⟩, hsx⟩ := hex
  have ha₁v : a₁ ≠ v₀ := fun h => hsx (by rw [h])
  have hmemdel : planeHomeo (E.pos a₁) ∈ V((edgeGraph E ↑T).deleteVerts {planeHomeo (E.pos v₀)}) := by
    rw [Graph.vertexSet_deleteVerts]
    exact ⟨mem_vertexSet_edgeGraph E (by exact_mod_cast he₁) he₁G ha₁, by simpa using hsx⟩
  refine Graph.Connected.of_hub hmemdel ?_
  intro t ht
  rw [Graph.vertexSet_deleteVerts] at ht
  obtain ⟨⟨z, ⟨g, hg, hgG, hz⟩, rfl⟩, hzx⟩ := ht
  have hzv : z ≠ v₀ := by
    intro h
    exact hzx (by simp [h])
  obtain ⟨w, hwT, hwsup⟩ := reachable_avoiding_of_no_split hT hsplit v₀
    (by exact_mod_cast he₁) ha₁ ha₁v g (by exact_mod_cast hg) z hz hzv
  refine ⟨w.edges, Graph.IsWalk.anti Graph.deleteVerts_le
    (isWalk_of_walk E w (fun e he => by exact_mod_cast hwT e he)
      (mem_vertexSet_edgeGraph E (by exact_mod_cast he₁) he₁G ha₁)) hmemdel ?_⟩
  intro e he
  have heT : e ∈ (↑T : Set (Sym2 V)) := by exact_mod_cast hwT e he
  have heG : e ∈ G.edgeSet := hT (by exact_mod_cast heT)
  have hout : s(e.out.1, e.out.2) ∈ w.edges := by rw [mk_out]; exact he
  have h1 : e.out.1 ∈ w.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges w hout
  have h2 : e.out.2 ∈ w.support := SimpleGraph.Walk.snd_mem_support_of_mem_edges w hout
  rw [Graph.edgeSet_deleteVerts]
  refine ⟨planeHomeo (E.pos e.out.1), planeHomeo (E.pos e.out.2),
    ⟨heT, heG, e.out.1, e.out.2, (mk_out e).symm, rfl, rfl⟩, ?_, ?_⟩
  · simpa using fun hc => hwsup _ h1 (posHomeo_injective E hc)
  · simpa using fun hc => hwsup _ h2 (posHomeo_injective E hc)

/-- **The drawn plane graph of an edge set with a second edge at every vertex and no splitting
vertex is two connected.** -/
theorem isTwoConnected_edgeGraph (E : UCPlanar.PlaneEmbedding G) {T : Finset (Sym2 V)}
    (hT : ↑T ⊆ G.edgeSet)
    (hdeg : ∀ e ∈ T, ∀ z : V, z ∈ e → ∃ f ∈ T, f ≠ e ∧ z ∈ f)
    (hsplit : ∀ T₁ T₂ : Finset (Sym2 V), T₁ ⊆ T → T₂ ⊆ T → (∀ e ∈ T, e ∈ T₁ ∨ e ∈ T₂) →
      Disjoint T₁ T₂ → ∀ v : V,
      (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) → T₁ = ∅ ∨ T₂ = ∅)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ T) :
    (edgeGraph E ↑T).IsTwoConnected where
  hasThreeVertices := hasThreeVertices_edgeGraph E hT hdeg he₀
  connected := connected_edgeGraph E hT hsplit he₀
  deleteVerts_connected := fun _ hx => deleteVerts_connected_edgeGraph E hT hdeg hsplit he₀ hx

end UCPlanar.Support
