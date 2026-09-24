/- Ordering and counting finite families of boundary contacts. -/
import UCPlanar.Support.PlanarBoundary
import UCPlanar.Support.PlanarLabels
import Mathlib.Data.Finset.Sort

open scoped Classical

/-- Every vertex of a cycle occurs before its repeated final endpoint. -/
theorem UCPlanar.Support.exists_cycle_vertex_index {V : Type*} {G : SimpleGraph V}
    {o z : V} (γ : G.Walk o o) (hγ : γ.IsCycle) (hz : z ∈ γ.support) :
    ∃ i < γ.length, γ.getVert i = z := by
  obtain ⟨i, hi, hil⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  by_cases hlt : i < γ.length
  · exact ⟨i, hlt, hi⟩
  · have he : i = γ.length := by omega
    have hz' : o = z := by simpa only [he, SimpleGraph.Walk.getVert_length] using hi
    exact ⟨0, by have := hγ.three_le_length; omega, by simpa only [SimpleGraph.Walk.getVert_zero] using hz'⟩

/-- Distinct contacts on a cycle admit an enumeration in strict cyclic order. -/
theorem UCPlanar.Support.exists_ordered_cycle_contacts {V I : Type*} {G : SimpleGraph V}
    {o : V} (γ : G.Walk o o) (hγ : γ.IsCycle) (T : Finset I) (c : I → V)
    (hc : Set.InjOn c (T : Set I)) (hmem : ∀ t ∈ T, c t ∈ γ.support) :
    ∃ e : Fin T.card ≃ T, ∃ k : Fin T.card → ℕ, StrictMono k ∧
      ∀ i, k i < γ.length ∧ γ.getVert (k i) = c (e i).val := by
  classical
  choose j hj using fun t : T => UCPlanar.Support.exists_cycle_vertex_index γ hγ
    (hmem t.val t.property)
  have hjinj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply hc x.property y.property
    exact (hj x).2.symm.trans ((congrArg γ.getVert he).trans (hj y).2)
  letI : LinearOrder T := LinearOrder.lift' j hjinj
  let e : Fin T.card ≃o T := Fintype.orderIsoFinOfCardEq T (by simp)
  refine ⟨e.toEquiv, fun i => j (e i), ?_, fun i => hj (e i)⟩
  intro i k hik
  exact e.strictMono hik

/-- The nonalternating boundary count for finite-indexed label families. -/
theorem UCPlanar.Support.boundary_count_fin_nonalternating {V : Type*} [DecidableEq V]
    {n : ℕ} (p m : Fin n → V) (B : Finset V)
    (hp : ∀ i, p i ∈ B) (hm : ∀ i, m i ∈ B)
    (hPM : ∀ i j, p i ≠ m j)
    (hcross : ∀ k a b c : Fin n, k < a → a < b → b < c → p k = p b → m a ≠ m c) :
    n ≤ 2 * B.card := by
  classical
  by_cases hn : n = 0
  · omega
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  let pp : ℕ → V := fun i => if hi : i < n then p ⟨i, hi⟩ else p ⟨0, hn'⟩
  let mm : ℕ → V := fun i => if hi : i < n then m ⟨i, hi⟩ else m ⟨0, hn'⟩
  apply UCPlanar.Support.boundary_count_of_nonalternating pp mm
    (Finset.univ.image p) (Finset.univ.image m) B n
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hp i
  · intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact hm i
  · apply Finset.disjoint_left.mpr
    intro z hpz hmz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hpz
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hmz
    exact hPM i j he.symm
  · intro i hi
    simpa only [pp, dif_pos hi] using Finset.mem_image_of_mem p (Finset.mem_univ ⟨i, hi⟩)
  · intro i hi
    simpa only [mm, dif_pos hi] using Finset.mem_image_of_mem m (Finset.mem_univ ⟨i, hi⟩)
  · intro k a b c hka hab hbc hcn he hm'
    have hkn : k < n := by omega
    have han : a < n := by omega
    have hbn : b < n := by omega
    have he' : p ⟨k, hkn⟩ = p ⟨b, hbn⟩ := by
      simpa only [pp, dif_pos hkn, dif_pos hbn] using he
    exact hcross ⟨k, hkn⟩ ⟨a, han⟩ ⟨b, hbn⟩ ⟨c, hcn⟩ hka hab hbc he'
      (by simpa only [mm, dif_pos han, dif_pos hcn] using hm')

