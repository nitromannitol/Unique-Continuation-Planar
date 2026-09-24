/- The two arcs a pair of vertices cuts a drawn cycle into. -/
import UCPlanar.Support.TopoChord

open Set SimpleGraph

open scoped Classical

namespace UCPlanar.Support

/-- Recopying a walk does not move its drawing. -/
theorem walkTrace_copy {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y x' y' : V} (w : G.Walk x y) (hx : x = x') (hy : y = y') :
    E.walkTrace (w.copy hx hy) = E.walkTrace w := by
  subst hx; subst hy; rfl

/-- **A cycle is cut by two of its vertices into two internally disjoint paths.** -/
theorem exists_cycle_arcs {V : Type*} {G : SimpleGraph V} {o : V}
    (E : UCPlanar.PlaneEmbedding G) (γ : G.Walk o o) (hγ : γ.IsCycle) {i k : ℕ}
    (hik : i < k) (hk : k < γ.length) :
    ∃ (σ₁ : G.Walk (γ.getVert i) (γ.getVert k)) (σ₂ : G.Walk (γ.getVert k) (γ.getVert i)),
      σ₁.IsPath ∧ σ₂.IsPath ∧ σ₁.length ≠ 0 ∧ σ₂.length ≠ 0 ∧
      (∀ m, i ≤ m → m ≤ k → γ.getVert m ∈ σ₁.support) ∧
      (∀ v ∈ σ₁.support, ∃ m, i ≤ m ∧ m ≤ k ∧ γ.getVert m = v) ∧
      (∀ m, m ≤ i → γ.getVert m ∈ σ₂.support) ∧
      (∀ m, k ≤ m → m ≤ γ.length → γ.getVert m ∈ σ₂.support) ∧
      (∀ v ∈ σ₂.support, ∃ m, m ≤ γ.length ∧ (m ≤ i ∨ k ≤ m) ∧ γ.getVert m = v) ∧
      (∀ e ∈ σ₁.edges, e ∉ σ₂.edges) ∧
      E.walkTrace γ = E.walkTrace σ₁ ∪ E.walkTrace σ₂ := by
  have hkl : k ≤ γ.length - 1 := by omega
  have hτ : (γ.take k).IsPath := SimpleGraph.Walk.IsPath.take_of_take hγ.isPath_dropLast hkl
  have hstart : (γ.take k).getVert i = γ.getVert i := by
    rw [γ.take_getVert k i]; congr 1; omega
  refine ⟨((γ.take k).drop i).copy hstart rfl, (γ.drop k).append (γ.take i), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_copy]; exact hτ.drop i
  · -- the complementary walk is a path
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
      γ.drop_support_eq_support_drop_min k, γ.support_take i]
    have hnd : γ.support.tail.Nodup := hγ.support_nodup
    have h1 : γ.support.drop (k ⊓ γ.length) = γ.support.tail.drop (k - 1) := by
      rw [List.drop_tail]
      congr 1
      omega
    have h2 : (γ.support.take (i + 1)).tail = γ.support.tail.take i := by
      simp [← List.drop_one, List.drop_take]
    rw [h1, h2]
    exact List.Nodup.append (hnd.drop) (hnd.take)
      (List.Disjoint.symm (List.disjoint_take_drop hnd (by omega)))
  · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.take_length]
    omega
  · rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.drop_length]
    omega
  · -- the vertices between the two indices lie on the first arc
    intro m him hmk
    have h : ((γ.take k).drop i).getVert (m - i) = γ.getVert m := by
      rw [SimpleGraph.Walk.drop_getVert, γ.take_getVert k]
      congr 1
      omega
    rw [SimpleGraph.Walk.support_copy, ← h]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  · -- the first arc has no other vertices
    intro v hv
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.mem_support_iff_exists_getVert] at hv
    obtain ⟨n, hn, hnle⟩ := hv
    rw [SimpleGraph.Walk.drop_length, SimpleGraph.Walk.take_length] at hnle
    refine ⟨i + n, by omega, by omega, ?_⟩
    rw [← hn, SimpleGraph.Walk.drop_getVert, γ.take_getVert k]
    congr 1
    omega
  · -- the vertices before the first index lie on the second arc
    intro m hmi
    refine (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inr ?_)
    have h : (γ.take i).getVert m = γ.getVert m := by
      rw [γ.take_getVert i m]; congr 1; omega
    rw [← h]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  · -- the vertices after the second index lie on the second arc
    intro m hkm hml
    refine (SimpleGraph.Walk.mem_support_append_iff _ _).mpr (Or.inl ?_)
    have h : (γ.drop k).getVert (m - k) = γ.getVert m := by
      rw [SimpleGraph.Walk.drop_getVert]; congr 1; omega
    rw [← h]
    exact SimpleGraph.Walk.getVert_mem_support _ _
  · -- the second arc has no other vertices
    intro v hv
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
    · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hv
      obtain ⟨n, hn, hnle⟩ := hv
      rw [SimpleGraph.Walk.drop_length] at hnle
      refine ⟨k + n, by omega, Or.inr (by omega), ?_⟩
      rw [← hn, SimpleGraph.Walk.drop_getVert]
    · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hv
      obtain ⟨n, hn, hnle⟩ := hv
      rw [SimpleGraph.Walk.take_length] at hnle
      refine ⟨n, by omega, Or.inl (by omega), ?_⟩
      rw [← hn, γ.take_getVert i n]
      congr 1
      omega
  · -- the two arcs share no edge
    intro e he he2
    have hnd : γ.edges.Nodup := hγ.edges_nodup
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_drop,
      SimpleGraph.Walk.edges_take] at he
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_drop,
      SimpleGraph.Walk.edges_take, List.mem_append] at he2
    have hetk : e ∈ γ.edges.take k := List.mem_of_mem_drop he
    have hedi : e ∈ γ.edges.drop i := by
      rw [List.drop_take] at he
      exact List.mem_of_mem_take he
    rcases he2 with he2 | he2
    · exact List.disjoint_take_drop hnd (le_refl k) hetk he2
    · exact List.disjoint_take_drop hnd (le_refl i) he2 hedi
  · -- the two arcs cover the drawing of the cycle
    have e1 : E.walkTrace γ
        = E.walkTrace (γ.take k) ∪ E.walkTrace (γ.drop k) := by
      conv_lhs => rw [← γ.append_take_drop_eq k]
      exact E.walkTrace_append _ _
    have e2 : E.walkTrace (γ.take k)
        = E.walkTrace ((γ.take k).take i) ∪ E.walkTrace ((γ.take k).drop i) := by
      conv_lhs => rw [← (γ.take k).append_take_drop_eq i]
      exact E.walkTrace_append _ _
    have e3 : E.walkTrace ((γ.take k).take i) = E.walkTrace (γ.take i) := by
      rw [SimpleGraph.Walk.take_take, walkTrace_copy, min_eq_right hik.le]
    rw [e1, e2, e3, walkTrace_copy, E.walkTrace_append]
    ac_rfl

/-- Two drawn walks with no common edge meet only in their common drawn vertices. -/
theorem walkTrace_inter_subset {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {a b c d : V} {S : Set UCPlanar.Plane}
    (w₁ : G.Walk a b) (w₂ : G.Walk c d)
    (hsup : ∀ v ∈ w₁.support, v ∈ w₂.support → E.pos v ∈ S)
    (hedge : ∀ e ∈ w₁.edges, e ∉ w₂.edges) :
    E.walkTrace w₁ ∩ E.walkTrace w₂ ⊆ S := by
  intro t ht
  by_cases htv : t ∈ Set.range E.pos
  · obtain ⟨v, rfl⟩ := htv
    exact hsup v ((E.pos_mem_walkTrace_iff w₁ v).mp ht.1)
      ((E.pos_mem_walkTrace_iff w₂ v).mp ht.2)
  · obtain ⟨u₁, v₁, h₁, ht₁, -, -, he₁⟩ := exists_edge_of_mem_walkTrace_edges E w₁ ht.1 htv
    obtain ⟨u₂, v₂, h₂, ht₂, -, -, he₂⟩ := exists_edge_of_mem_walkTrace_edges E w₂ ht.2 htv
    rcases edge_range_inter_or_eq E h₁ h₂ with hsub | hcase
    · rcases hsub ⟨ht₁, ht₂⟩ with h | h
      · exact absurd ⟨u₁, h.symm⟩ htv
      · exact absurd ⟨v₁, h.symm⟩ htv
    · exact absurd (by
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he₂
        · rwa [Sym2.eq_swap] at he₂) (hedge _ he₁)

/-- **A drawn cycle is cut by two of its vertices into two arcs**, and the vertices strictly
between them on one side lie on one arc only. -/
theorem exists_cutPair_cycle {V : Type*} {G : SimpleGraph V} {o : V}
    (E : UCPlanar.PlaneEmbedding G) (γ : G.Walk o o) (hγ : γ.IsCycle) {i j k l : ℕ}
    (hij : i < j) (hjk : j < k) (hkl : k < l) (hl : l < γ.length) :
    ∃ A₁ A₂ : Set Schoenflies.Plane,
      Schoenflies.IsCutPair (topoTrace E γ) (planeHomeo (E.pos (γ.getVert i)))
        (planeHomeo (E.pos (γ.getVert k))) A₁ A₂ ∧
      planeHomeo (E.pos (γ.getVert j)) ∈ A₁ ∧ planeHomeo (E.pos (γ.getVert j)) ∉ A₂ ∧
      planeHomeo (E.pos (γ.getVert l)) ∈ A₂ ∧ planeHomeo (E.pos (γ.getVert l)) ∉ A₁ := by
  have hk : k < γ.length := by omega
  obtain ⟨σ₁, σ₂, hp₁, hp₂, hn₁, hn₂, hm₁, hs₁, hm₂a, hm₂b, hs₂, hedge, htr⟩ :=
    exists_cycle_arcs E γ hγ (show i < k by omega) hk
  -- indices below the length are told apart by the cycle
  have hinj : ∀ m m' : ℕ, m ≤ γ.length - 1 → m' ≤ γ.length - 1 →
      γ.getVert m = γ.getVert m' → m = m' :=
    fun m m' hm hm' h => hγ.getVert_injOn' (by simpa using hm) (by simpa using hm') h
  have hzero : γ.getVert γ.length = γ.getVert 0 := by
    rw [SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
  -- the two supports meet exactly in the two chosen vertices
  have hmeet : ∀ v ∈ σ₁.support, v ∈ σ₂.support →
      E.pos v ∈ ({E.pos (γ.getVert i), E.pos (γ.getVert k)} : Set UCPlanar.Plane) := by
    intro v hv₁ hv₂
    obtain ⟨m, him, hmk, rfl⟩ := hs₁ v hv₁
    obtain ⟨m', hm'l, hm'c, hm'⟩ := hs₂ _ hv₂
    have hm2 : m = i ∨ m = k := by
      by_cases hml : m' = γ.length
      · subst hml
        rw [hzero] at hm'
        have := hinj m 0 (by omega) (by omega) hm'.symm
        omega
      · have := hinj m m' (by omega) (by omega) hm'.symm
        omega
    rcases hm2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨topoTrace E σ₁, topoTrace E σ₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨isArcBetween_topoTrace_of_isPath E σ₁ hp₁ hn₁,
      (isArcBetween_topoTrace_of_isPath E σ₂ hp₂ hn₂).reverse, ?_, ?_⟩
    · rw [topoTrace, topoTrace, topoTrace, ← Set.image_union, ← htr]
    · rw [topoTrace, topoTrace, ← Set.image_inter planeHomeo.injective]
      apply subset_antisymm
      · refine (Set.image_mono (walkTrace_inter_subset E σ₁ σ₂ hmeet hedge)).trans ?_
        rw [Set.image_insert_eq, Set.image_singleton]
      · refine Set.insert_subset ?_ (Set.singleton_subset_iff.mpr ?_)
        · exact Set.mem_image_of_mem _
            ⟨(E.pos_mem_walkTrace_iff σ₁ _).mpr σ₁.start_mem_support,
             (E.pos_mem_walkTrace_iff σ₂ _).mpr σ₂.end_mem_support⟩
        · exact Set.mem_image_of_mem _
            ⟨(E.pos_mem_walkTrace_iff σ₁ _).mpr σ₁.end_mem_support,
             (E.pos_mem_walkTrace_iff σ₂ _).mpr σ₂.start_mem_support⟩
  · exact Set.mem_image_of_mem _ ((E.pos_mem_walkTrace_iff σ₁ _).mpr (hm₁ j (by omega) (by omega)))
  · intro hmem
    have hv : γ.getVert j ∈ σ₂.support :=
      (E.pos_mem_walkTrace_iff σ₂ _).mp (planeHomeo.injective.mem_set_image.mp hmem)
    have := hmeet _ (hm₁ j (by omega) (by omega)) hv
    rcases this with h | h
    · exact absurd (hinj j i (by omega) (by omega) (E.pos_injective h)) (by omega)
    · exact absurd (hinj j k (by omega) (by omega) (E.pos_injective h)) (by omega)
  · exact Set.mem_image_of_mem _
      ((E.pos_mem_walkTrace_iff σ₂ _).mpr (hm₂b l (by omega) (by omega)))
  · intro hmem
    have hv : γ.getVert l ∈ σ₁.support :=
      (E.pos_mem_walkTrace_iff σ₁ _).mp (planeHomeo.injective.mem_set_image.mp hmem)
    have := hmeet _ hv (hm₂b l (by omega) (by omega))
    rcases this with h | h
    · exact absurd (hinj l i (by omega) (by omega) (E.pos_injective h)) (by omega)
    · exact absurd (hinj l k (by omega) (by omega) (E.pos_injective h)) (by omega)

end UCPlanar.Support
