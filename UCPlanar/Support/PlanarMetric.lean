/- Metric bounds for the face paths and their sign neighbors. -/
import UCPlanar.Support.PlanarFaces
import UCPlanar.Support.PlanarPacking
import LatticeProb.Graph.Reach

open scoped Classical

/-- Every support vertex is at distance at most the length of the walk. -/
theorem UCPlanar.Support.dist_le_length_of_mem_support {V : Type*}
    {G : SimpleGraph V} {x y z : V} (p : G.Walk x y) (hz : z ∈ p.support) :
    G.dist x z ≤ p.length := by
  exact (SimpleGraph.dist_le (p.takeUntil z hz)).trans (p.length_takeUntil_le_length hz)

/-- A neighbor of the end of a simple face path is within the face-size bound. -/
theorem UCPlanar.PlaneEmbedding.dist_sign_le_faceBound {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x w y : V}
    (p : G.Walk x w) (hp : p.IsPath) (F : Set UCPlanar.Plane)
    (hF : E.IsFace F) (L : ℕ) (hL : E.FaceBound L)
    (htrace : E.walkTrace p ⊆ frontier F) (hwy : G.Adj w y) :
    G.dist x y ≤ L := by
  have hlen := E.length_lt_faceBound p hp F hF L hL htrace
  have hd := SimpleGraph.dist_le (p.concat hwy)
  simp only [SimpleGraph.Walk.length_concat] at hd
  omega

/-- Bounded degree supplies a quantitatively large set with disjoint radius-`r` balls. -/
theorem UCPlanar.Support.exists_metric_separated {V : Type*}
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (S : Finset V) (d r : ℕ) (hd : ∀ x, G.degree x ≤ d) :
    ∃ T ⊆ S, (∀ x ∈ T, ∀ y ∈ T, x ≠ y → 2 * r < G.dist x y) ∧
      S.card ≤ T.card * ((2 * r + 1) * (d + 1) ^ (2 * r)) := by
  classical
  obtain ⟨T, hTS, hsep, hcard⟩ := UCPlanar.Support.exists_separated_card S
    (fun x y => G.dist x y ≤ 2 * r) (by intros; rwa [G.dist_comm])
    ((2 * r + 1) * (d + 1) ^ (2 * r)) (by
      intro y _
      have hs : S.filter (fun x => x = y ∨ G.dist x y ≤ 2 * r) ⊆
          LatticeProb.Graph.ballFinset G y (2 * r) := by
        intro x hx
        apply LatticeProb.Graph.mem_ballFinset_of_dist_le hG
        rcases (Finset.mem_filter.mp hx).2 with rfl | hxy
        · simp
        · rwa [G.dist_comm]
      convert (Finset.card_le_card hs).trans
        (LatticeProb.Graph.card_ballFinset_le (d := d + 1) (by omega)
          (fun x => (hd x).trans (by omega)) y _) using 1
      · rfl
      · congr 1
        ext x
        simp)
  exact ⟨T, hTS, fun x hx y hy hxy => Nat.lt_of_not_ge (hsep x hx y hy hxy), hcard⟩

/-- Short walks from sufficiently distant starting vertices have disjoint supports. -/
theorem UCPlanar.Support.disjoint_support_of_dist {V : Type*}
    {G : SimpleGraph V} (hG : G.Connected) {x y u v : V}
    (p : G.Walk x u) (q : G.Walk y v) (r : ℕ)
    (hp : p.length ≤ r) (hq : q.length ≤ r) (hxy : 2 * r < G.dist x y) :
    ∀ z ∈ p.support, z ∉ q.support := by
  intro z hz hqz
  have hxz := UCPlanar.Support.dist_le_length_of_mem_support p hz
  have hyz := UCPlanar.Support.dist_le_length_of_mem_support q hqz
  have ht := hG.dist_triangle (u := x) (v := z) (w := y)
  rw [G.dist_comm (u := z) (v := y)] at ht
  omega

/-- Face paths supply short attachments to both signs. -/
theorem UCPlanar.PlaneEmbedding.facePathToSigns_metric {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {P M : Set V} {z : V}
    (h : E.FacePathToSigns P M z) (L : ℕ) (hL : E.FaceBound L) :
    ∃ w, ∃ β : G.Walk z w, β.IsPath ∧ β.length < L ∧
      (∀ x ∈ β.support, x ∉ P ∪ M) ∧
      (∃ p ∈ P, G.Adj w p ∧ G.dist z p ≤ L) ∧
      (∃ m ∈ M, G.Adj w m ∧ G.dist z m ≤ L) := by
  obtain ⟨F, hF, _, w, β, hβ, ht, ha, ⟨p, hp, hwp⟩, ⟨m, hm, hwm⟩⟩ := h
  exact ⟨w, β, hβ, E.length_lt_faceBound β hβ F hF L hL ht, ha,
    ⟨p, hp, hwp, E.dist_sign_le_faceBound β hβ F hF L hL ht hwp⟩,
    ⟨m, hm, hwm, E.dist_sign_le_faceBound β hβ F hF L hL ht hwm⟩⟩

/-- A fixed-width neighborhood of the boundary has cardinality linear in its size. -/
theorem UCPlanar.Support.card_near_boundary_le {V : Type*}
    {G : SimpleGraph V} [G.LocallyFinite] (hG : G.Connected)
    (S B : Finset V) (d r : ℕ) (hd : ∀ x, G.degree x ≤ d) :
    (S.filter (fun z => ∃ b ∈ B, G.dist z b ≤ r)).card ≤
      B.card * ((r + 1) * (d + 1) ^ r) := by
  classical
  apply UCPlanar.Support.card_le_of_cover _ B
    (fun b => LatticeProb.Graph.ballFinset G b r)
  · intro z hz
    obtain ⟨b, hb, hzb⟩ := (Finset.mem_filter.mp hz).2
    refine ⟨b, hb, LatticeProb.Graph.mem_ballFinset_of_dist_le hG ?_⟩
    rwa [G.dist_comm]
  · intro b _
    exact LatticeProb.Graph.card_ballFinset_le (d := d + 1) (by omega)
      (fun x => (hd x).trans (by omega)) b r

/-- Nearby endpoints of separated starting vertices are distinct. -/
theorem UCPlanar.Support.injective_endpoints_of_separated {V : Type*}
    {G : SimpleGraph V} (hG : G.Connected) (T : Finset V) (r : ℕ) (f : V → V)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 2 * r < G.dist x y)
    (hf : ∀ x ∈ T, G.dist x (f x) ≤ r) : Set.InjOn f (T : Set V) := by
  intro x hx y hy he
  by_contra hne
  have hxy := hsep x hx y hy hne
  have hx' := hf x hx
  have hy' := hf y hy
  have ht := hG.dist_triangle (u := x) (v := f x) (w := y)
  rw [he] at hx'
  rw [he, G.dist_comm (u := f y) (v := y)] at ht
  omega

/-- A bounded discard and a separated boundary charge combine into a uniform density charge. -/
theorem UCPlanar.Support.card_bound_of_discard_packing {V : Type*} [DecidableEq V]
    (Z E T B : Finset V) (K C : ℕ)
    (hpack : (Z \ E).card ≤ T.card * K)
    (hcharge : T.card ≤ 2 * B.card) (hdiscard : E.card ≤ B.card * C) :
    Z.card ≤ 2 * (K + C) * B.card := by
  have hz := Finset.card_le_card_sdiff_add_card (s := Z) (t := E)
  have ht := Nat.mul_le_mul_right K hcharge
  nlinarith

/-- The packing and discard constants give a density coefficient strictly between zero and one. -/
theorem UCPlanar.Support.density_bound_of_discard_packing {V : Type*} [DecidableEq V]
    (S Z E T : Finset V) (hZS : Z ⊆ S) (K C : ℕ) (hK : 0 < K + C)
    (hpack : (Z \ E).card ≤ T.card * K)
    (hcharge : T.card ≤ 2 * (S \ Z).card)
    (hdiscard : E.card ≤ (S \ Z).card * C) :
    0 < 2 * ((K + C : ℕ) : ℝ) / (2 * (K + C : ℕ) + 1) ∧
    2 * ((K + C : ℕ) : ℝ) / (2 * (K + C : ℕ) + 1) < 1 ∧
    (Z.card : ℝ) ≤ (2 * ((K + C : ℕ) : ℝ) / (2 * (K + C : ℕ) + 1)) * S.card := by
  have hk : 0 < ((K + C : ℕ) : ℝ) := by exact_mod_cast hK
  have hd : 0 < 2 * ((K + C : ℕ) : ℝ) + 1 := by positivity
  refine ⟨div_pos (by positivity) hd, (div_lt_one hd).mpr (by linarith), ?_⟩
  have hz : (Z.card : ℝ) ≤ 2 * ((K + C : ℕ) : ℝ) * (S \ Z).card := by
    exact_mod_cast UCPlanar.Support.card_bound_of_discard_packing Z E T (S \ Z) K C
      hpack hcharge hdiscard
  have hsum : (Z.card : ℝ) + (S \ Z).card = S.card := by
    exact_mod_cast (by simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hZS)
  simpa only [hsum] using UCPlanar.Support.packing_ratio
    (Z.card : ℝ) (S \ Z).card (K + C : ℕ) hk hz
