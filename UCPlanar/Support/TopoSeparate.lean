/- Separation of a point of the plane from infinity, and the splitting of a separator at a
single common point. -/
import UCPlanar.Support.TopoRegion
import Mathlib

open Set

namespace UCPlanar.Support

/-- In the coordinate plane the complement of a bounded set is unbounded. -/
theorem not_isBounded_compl {A : Set UCPlanar.Plane} (hA : Bornology.IsBounded A) :
    ¬ Bornology.IsBounded Aᶜ := by
  intro h
  have hu : Bornology.IsBounded (Set.univ : Set UCPlanar.Plane) := by
    have h2 := hA.union h
    rwa [Set.union_compl_self] at h2
  exact NormedSpace.unbounded_univ ℝ UCPlanar.Plane hu

/-- The coordinate plane is two dimensional, so the complement of a countable subset of it is
connected. -/
theorem one_lt_rank_plane : 1 < Module.rank ℝ UCPlanar.Plane := by
  have h2 : Module.rank ℝ UCPlanar.Plane = 2 := by
    simp [rank_fin_fun (R := ℝ) 2]
  rw [h2]
  norm_num

/-- **A bounded countable set separates nothing from infinity.**  Its complement is connected,
hence is the single unbounded component. -/
theorem insideOf_eq_empty_of_countable {S : Set UCPlanar.Plane} (hc : S.Countable)
    (hb : Bornology.IsBounded S) : insideOf S = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hz, hbd⟩
  have hconn : IsConnected (Sᶜ : Set UCPlanar.Plane) :=
    hc.isConnected_compl_of_one_lt_rank one_lt_rank_plane
  rw [hconn.isPreconnected.connectedComponentIn hz] at hbd
  exact not_isBounded_compl hb hbd

/-- **A set whose drawing is a simple arc separates nothing from infinity.** -/
theorem insideOf_eq_empty_of_image_isArc {A : Set UCPlanar.Plane}
    (hA : Schoenflies.IsArc (planeHomeo '' A)) : insideOf A = ∅ := by
  have himg : planeHomeo '' insideOf A = ∅ := by
    rw [image_insideOf planeHomeo A, insideOf_eq_inside]
    exact inside_eq_empty_of_isArc hA
  exact Set.image_eq_empty.mp himg

/-- **Enlarging a separator keeps a point separated from infinity.** -/
theorem insideOf_mono {S T : Set UCPlanar.Plane} (h : T ⊆ S) {p : UCPlanar.Plane}
    (hp : p ∉ S) (hin : p ∈ insideOf T) : p ∈ insideOf S :=
  insideOf_sdiff_subset h ⟨hin, hp⟩

/-- **Janiszewski's theorem at a single point.**  Two closed subsets of the plane whose
intersection is at most one point, neither of which separates a given point from infinity, have
a union which does not separate it either.

This is the classical unicoherence statement in the only form the boundary cycle theorem needs:
in the two places it is applied the two sets are the drawings of two edge sets of a plane graph
which share a single vertex, or which are disjoint. -/
def JaniszewskiPoint : Prop :=
  ∀ A B : Set UCPlanar.Plane, IsClosed A → IsClosed B →
    ∀ v : UCPlanar.Plane, A ∩ B ⊆ {v} →
    ∀ p : UCPlanar.Plane, p ∉ A → p ∉ B → p ∉ insideOf A → p ∉ insideOf B →
      p ∉ insideOf (A ∪ B)

/-- **The splitting form of Janiszewski's theorem.**  A point separated from infinity by the
union of two closed sets meeting in at most one point is separated by one of them. -/
theorem insideOf_union_split (hJ : JaniszewskiPoint) {A B : Set UCPlanar.Plane}
    (hA : IsClosed A) (hB : IsClosed B) {v : UCPlanar.Plane} (hAB : A ∩ B ⊆ {v})
    {p : UCPlanar.Plane} (hp : p ∈ insideOf (A ∪ B)) :
    p ∈ insideOf A ∨ p ∈ insideOf B := by
  classical
  rcases em (p ∈ insideOf A) with h | h
  · exact Or.inl h
  rcases em (p ∈ insideOf B) with h' | h'
  · exact Or.inr h'
  exact absurd hp (hJ A B hA hB v hAB p (fun hx => hp.1 (Or.inl hx))
    (fun hx => hp.1 (Or.inr hx)) h h')

/-- Janiszewski's theorem transports from the Euclidean plane of the Jordan curve development to
the coordinate plane. -/
theorem janiszewskiPoint_of_euclidean
    (h : ∀ A B : Set Schoenflies.Plane, IsClosed A → IsClosed B →
      ∀ v : Schoenflies.Plane, A ∩ B ⊆ {v} →
      ∀ p : Schoenflies.Plane, p ∉ A → p ∉ B →
        p ∉ Schoenflies.inside A → p ∉ Schoenflies.inside B →
          p ∉ Schoenflies.inside (A ∪ B)) :
    JaniszewskiPoint := by
  intro A B hA hB v hAB p hpA hpB hiA hiB hmem
  have himg : ∀ S : Set UCPlanar.Plane, ∀ q : UCPlanar.Plane,
      q ∈ insideOf S → planeHomeo q ∈ Schoenflies.inside (planeHomeo '' S) := by
    intro S q hq
    rw [← insideOf_eq_inside, ← image_insideOf planeHomeo S]
    exact Set.mem_image_of_mem _ hq
  have hpull : ∀ S : Set UCPlanar.Plane, ∀ q : UCPlanar.Plane,
      planeHomeo q ∈ Schoenflies.inside (planeHomeo '' S) → q ∈ insideOf S := by
    intro S q hq
    rw [← insideOf_eq_inside, ← image_insideOf planeHomeo S] at hq
    obtain ⟨y, hy, hyq⟩ := hq
    rwa [planeHomeo.injective hyq] at hy
  refine h (planeHomeo '' A) (planeHomeo '' B) (planeHomeo.isClosedMap A hA)
    (planeHomeo.isClosedMap B hB) (planeHomeo v) ?_ (planeHomeo p)
    (fun hx => hpA ((planeHomeo.injective).mem_set_image.mp hx))
    (fun hx => hpB ((planeHomeo.injective).mem_set_image.mp hx))
    (fun hx => hiA (hpull A p hx)) (fun hx => hiB (hpull B p hx)) ?_
  · rintro z ⟨⟨a, ha, rfl⟩, hzB⟩
    have haB : a ∈ B := (planeHomeo.injective).mem_set_image.mp hzB
    have : a ∈ ({v} : Set UCPlanar.Plane) := hAB ⟨ha, haB⟩
    simp only [Set.mem_singleton_iff] at this ⊢
    rw [this]
  · rw [← Set.image_union]
    exact himg (A ∪ B) p hmem

end UCPlanar.Support
