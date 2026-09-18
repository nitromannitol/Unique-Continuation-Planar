/- The face path of Step 3: a walk drawn on the frontier of a face from a vertex where the
harmonic function is small to a vertex next to both signs, obtained by stopping the walk along
the face at the first vertex carrying a large value and completing the sign by harmonicity. -/
import UCPlanar.Support.TopoChord
import UCPlanar.Support.TopoRegion
import UCPlanar.Support.ZeroSign
import UCPlanar.Support.ZeroMax
import UCPlanar.Support.PlanarCycle
import Mathlib

open Set
open scoped Classical

/-- **The vertices incident to a face are joined along its frontier.**  For a bounded face of a
locally finite plane graph this is the statement that the frontier of the face is the drawing of
a closed walk of the graph. -/
def UCPlanar.PlaneEmbedding.FaceWalks {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  ∀ F, E.IsFace F → ∀ u v, E.Incident F u → E.Incident F v →
    ∃ β : G.Walk u v, E.walkTrace β ⊆ frontier F

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **A walk from outside a set to inside it has a prefix avoiding the set whose end is adjacent
to the set.**  The prefix is drawn inside the walk. -/
theorem exists_prefix_avoiding (E : UCPlanar.PlaneEmbedding G) {S : Set V} {x y : V}
    (p : G.Walk x y) (hx : x ∉ S) (hy : y ∈ S) :
    ∃ (a b : V) (q : G.Walk x a), (∀ z ∈ q.support, z ∉ S) ∧ G.Adj a b ∧ b ∈ S ∧
      E.walkTrace q ⊆ E.walkTrace p := by
  revert hx
  induction p with
  | nil => intro hx; exact absurd hy hx
  | @cons u v w hadj tail ih =>
    intro hx
    by_cases hvS : v ∈ S
    · refine ⟨u, v, SimpleGraph.Walk.nil, ?_, hadj, hvS, ?_⟩
      · intro z hz
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        subst hz
        exact hx
      · intro t ht
        rw [UCPlanar.PlaneEmbedding.walkTrace] at ht
        rw [UCPlanar.PlaneEmbedding.walkTrace]
        have htu : t = E.pos u := ht
        subst htu
        exact Or.inl ⟨0, (E.edge hadj).source⟩
    · obtain ⟨a, b, q, hq, hab, hbS, hqt⟩ := ih hy hvS
      refine ⟨a, b, SimpleGraph.Walk.cons hadj q, ?_, hab, hbS, ?_⟩
      · intro z hz
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hx
        · exact hq z hz
      · intro t ht
        rw [UCPlanar.PlaneEmbedding.walkTrace] at ht
        rw [UCPlanar.PlaneEmbedding.walkTrace]
        rcases ht with ht | ht
        · exact Or.inl ht
        · exact Or.inr (hqt ht)

/-- **The face path of Step 3.**  Walk along the frontier of a face from a vertex carrying no
sign to a vertex that does, stop at the last vertex before the first sign, and complete the two
signs there.  The walk is made simple without leaving the frontier. -/
theorem facePathToSigns_of_faceWalks (E : UCPlanar.PlaneEmbedding G)
    (hFW : E.FaceWalks) {P M : Set V} {F : Set UCPlanar.Plane} (hF : E.IsFace F) {z w : V}
    (hz : E.Incident F z) (hzPM : z ∉ P ∪ M) (hw : E.Incident F w) (hwPM : w ∈ P ∪ M)
    (hsign : ∀ a b : V, G.Adj a b → a ∉ P ∪ M → b ∈ P ∪ M →
      (∃ p ∈ P, G.Adj a p) ∧ (∃ m ∈ M, G.Adj a m)) :
    E.FacePathToSigns P M z := by
  obtain ⟨β₀, hβ₀⟩ := hFW F hF z w hz hw
  obtain ⟨a, b, q, hqS, hab, hbS, hqt⟩ := exists_prefix_avoiding E β₀ hzPM hwPM
  obtain ⟨hp, hm⟩ := hsign a b hab (hqS a q.end_mem_support) hbS
  refine ⟨F, hF, hz, a, q.bypass, q.bypass_isPath, ?_, ?_, hp, hm⟩
  · exact (walkTrace_bypass_subset E q).trans (hqt.trans hβ₀)
  · intro t ht
    exact hqS t (q.support_bypass_subset_support ht)

/-- **A neighbour of an interior vertex of the region a cycle bounds lies in that region.** -/
theorem adj_mem_cycleRegion (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) {a y : V}
    (ha : a ∈ E.cycleRegion γ) (hanot : a ∉ γ.support) (hay : G.Adj a y) :
    y ∈ E.cycleRegion γ := by
  by_contra hy
  obtain ⟨t, ht, htγ⟩ :=
    exists_mem_support_of_cycleRegion E (SimpleGraph.Walk.cons hay SimpleGraph.Walk.nil) γ ha hy
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
    List.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact hanot htγ
  · exact hy (Or.inl htγ)

/-- **A vanishing vertex with a positive neighbour has a negative one.**  This is the harmonicity
step of Step 3. -/
theorem exists_neg_adj_of_harmonic [G.LocallyFinite] {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond G c) (f : V → ℝ) {a y : V}
    (hharm : LatticeProb.Network.netLaplacian G c f a = 0) (hfa : f a = 0)
    (hay : G.Adj a y) (hfy : 0 < f y) : ∃ z, G.Adj a z ∧ f z < 0 := by
  by_contra hcon
  push Not at hcon
  have hnn : ∀ z ∈ G.neighborFinset a, 0 ≤ c a z * (f z - f a) := by
    intro z hz
    have hadj : G.Adj a z := (SimpleGraph.mem_neighborFinset G a z).mp hz
    have h0 : 0 ≤ f z := hcon z hadj
    rw [hfa]
    exact mul_nonneg (hc.nonneg a z) (by linarith)
  have hymem : y ∈ G.neighborFinset a := (SimpleGraph.mem_neighborFinset G a y).mpr hay
  have hpos : 0 < c a y * (f y - f a) := by
    rw [hfa]
    exact mul_pos (hc.pos hay) (by linarith)
  have hsum : 0 < ∑ z ∈ G.neighborFinset a, c a z * (f z - f a) :=
    Finset.sum_pos' hnn ⟨y, hymem, hpos⟩
  rw [LatticeProb.Network.netLaplacian] at hharm
  linarith

/-- **The sign completion of Step 3.**  A vertex of the region where the function vanishes, all
of whose neighbours stay in the region, and which is adjacent to a vertex of one sign, is
adjacent to a vertex of each sign. -/
theorem sign_pair_of_harmonic [G.LocallyFinite] {c : V → V → ℝ}
    (hc : LatticeProb.Network.IsCond G c) (E : UCPlanar.PlaneEmbedding G) (f : V → ℝ)
    {o : V} (γ : G.Walk o o) {a b : V} (hab : G.Adj a b)
    (hharm : LatticeProb.Network.netLaplacian G c f a = 0)
    (hnb : ∀ y, G.Adj a y → y ∈ E.cycleRegion γ)
    (ha : a ∈ E.cycleRegion γ)
    (haPM : a ∉ {x | x ∈ E.cycleRegion γ ∧ 0 < f x} ∪ {x | x ∈ E.cycleRegion γ ∧ f x < 0})
    (hb : b ∈ {x | x ∈ E.cycleRegion γ ∧ 0 < f x} ∪ {x | x ∈ E.cycleRegion γ ∧ f x < 0}) :
    (∃ p ∈ {x | x ∈ E.cycleRegion γ ∧ 0 < f x}, G.Adj a p) ∧
      (∃ m ∈ {x | x ∈ E.cycleRegion γ ∧ f x < 0}, G.Adj a m) := by
  have hfa : f a = 0 := by
    rcases lt_trichotomy (f a) 0 with h | h | h
    · exact absurd (Or.inr ⟨ha, h⟩) haPM
    · exact h
    · exact absurd (Or.inl ⟨ha, h⟩) haPM
  rcases hb with hb | hb
  · obtain ⟨m, ham, hfm⟩ := exists_neg_adj_of_harmonic hc f hharm hfa hab hb.2
    exact ⟨⟨b, ⟨hb.1, hb.2⟩, hab⟩, ⟨m, ⟨hnb m ham, hfm⟩, ham⟩⟩
  · have hharm' : LatticeProb.Network.netLaplacian G c (fun z => -f z) a = 0 := by
      rw [netLaplacian_neg, hharm, neg_zero]
    obtain ⟨p, hap, hfp⟩ :=
      exists_neg_adj_of_harmonic hc (fun z => -f z) hharm' (by simp [hfa]) hab (by simpa using hb.2)
    exact ⟨⟨p, ⟨hnb p hap, by simpa using hfp⟩, hap⟩, ⟨b, ⟨hb.1, hb.2⟩, hab⟩⟩

/-- **The third hypothesis of the topological lemma, from the face walks.**  If the vertices
incident to a face are joined along its frontier, the face and the neighbours of its vertices lie
in the region a cycle bounds, the function is harmonic at every vertex of the face and vanishes
at one of them which shares the face with a vertex where it does not vanish, then that vertex
carries a face path to both signs. -/
theorem facePathToSigns_step3 [G.LocallyFinite] (E : UCPlanar.PlaneEmbedding G)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c) (hFW : E.FaceWalks) (f : V → ℝ)
    {o : V} (γ : G.Walk o o) {F : Set UCPlanar.Plane} (hF : E.IsFace F)
    (hharm : ∀ y, E.Incident F y → LatticeProb.Network.netLaplacian G c f y = 0)
    (hFreg : ∀ y, E.Incident F y → y ∈ E.cycleRegion γ)
    (hFnb : ∀ y, E.Incident F y → ∀ u, G.Adj y u → u ∈ E.cycleRegion γ)
    {z : V} (hzF : E.Incident F z) (hz0 : f z = 0)
    {w : V} (hwF : E.Incident F w) (hw0 : f w ≠ 0) :
    E.FacePathToSigns {x | x ∈ E.cycleRegion γ ∧ 0 < f x}
      {x | x ∈ E.cycleRegion γ ∧ f x < 0} z := by
  have hzPM : z ∉ {x | x ∈ E.cycleRegion γ ∧ 0 < f x} ∪ {x | x ∈ E.cycleRegion γ ∧ f x < 0} := by
    intro hcon
    rcases hcon with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hz0] at h <;> exact absurd h (lt_irrefl 0)
  have hwPM : w ∈ {x | x ∈ E.cycleRegion γ ∧ 0 < f x} ∪ {x | x ∈ E.cycleRegion γ ∧ f x < 0} := by
    rcases lt_trichotomy (f w) 0 with h | h | h
    · exact Or.inr ⟨hFreg w hwF, h⟩
    · exact absurd h hw0
    · exact Or.inl ⟨hFreg w hwF, h⟩
  obtain ⟨β₀, hβ₀⟩ := hFW F hF z w hzF hwF
  obtain ⟨a, b, q, hqS, hab, hbS, hqt⟩ := exists_prefix_avoiding E β₀ hzPM hwPM
  have haF : E.Incident F a :=
    hβ₀ (hqt ((E.pos_mem_walkTrace_iff q a).mpr q.end_mem_support))
  obtain ⟨hp, hm⟩ := sign_pair_of_harmonic hc E f γ hab (hharm a haF) (hFnb a haF)
    (hFreg a haF) (hqS a q.end_mem_support) hbS
  refine ⟨F, hF, hzF, a, q.bypass, q.bypass_isPath, ?_, ?_, hp, hm⟩
  · exact (walkTrace_bypass_subset E q).trans (hqt.trans hβ₀)
  · intro t ht
    exact hqS t (q.support_bypass_subset_support ht)

/-- **A walk one of whose vertices is adjacent to a set has a prefix avoiding the set whose end
is adjacent to it.**  Stopping at the FIRST vertex with a neighbour in the set keeps the whole
prefix out of the set, because a vertex of the set on the prefix would give its predecessor a
neighbour in the set earlier. -/
theorem exists_prefix_adj_avoiding (E : UCPlanar.PlaneEmbedding G) {S : Set V} {x y : V}
    (p : G.Walk x y) (hx : x ∉ S) (hex : ∃ t ∈ p.support, ∃ b, G.Adj t b ∧ b ∈ S) :
    ∃ (a b : V) (q : G.Walk x a), (∀ z ∈ q.support, z ∉ S) ∧ G.Adj a b ∧ b ∈ S ∧
      E.walkTrace q ⊆ E.walkTrace p := by
  classical
  revert hx
  induction p with
  | @nil u =>
    intro hx
    obtain ⟨t, ht, b, hab, hbS⟩ := hex
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at ht
    subst ht
    exact ⟨t, b, SimpleGraph.Walk.nil, by
      intro z hz
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst hz
      exact hx, hab, hbS, fun t ht => ht⟩
  | @cons u v w hadj tail ih =>
    intro hx
    by_cases hu : ∃ b, G.Adj u b ∧ b ∈ S
    · obtain ⟨b, hab, hbS⟩ := hu
      refine ⟨u, b, SimpleGraph.Walk.nil, ?_, hab, hbS, ?_⟩
      · intro z hz
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        subst hz
        exact hx
      · intro t ht
        rw [UCPlanar.PlaneEmbedding.walkTrace] at ht
        rw [UCPlanar.PlaneEmbedding.walkTrace]
        have htu : t = E.pos u := ht
        subst htu
        exact Or.inl ⟨0, (E.edge hadj).source⟩
    · have hvS : v ∉ S := fun hc => hu ⟨v, hadj, hc⟩
      have hex' : ∃ t ∈ tail.support, ∃ b, G.Adj t b ∧ b ∈ S := by
        obtain ⟨t, ht, b, hab, hbS⟩ := hex
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact absurd ⟨b, hab, hbS⟩ hu
        · exact ⟨t, ht, b, hab, hbS⟩
      obtain ⟨a, b, q, hq, hab, hbS, hqt⟩ := ih hex' hvS
      refine ⟨a, b, SimpleGraph.Walk.cons hadj q, ?_, hab, hbS, ?_⟩
      · intro z hz
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hx
        · exact hq z hz
      · intro t ht
        rw [UCPlanar.PlaneEmbedding.walkTrace] at ht
        rw [UCPlanar.PlaneEmbedding.walkTrace]
        rcases ht with ht | ht
        · exact Or.inl ht
        · exact Or.inr (hqt ht)

/-- **The third hypothesis of the topological lemma, with the neighbours of the stopping vertex
only.**  The walk along the face is stopped at a vertex with a neighbour of nonzero value, and
only there are the neighbours required to stay inside the cycle.  The far vertex of the face may
itself vanish, provided one of ITS neighbours does not; that is the case the neighbour-buffered
cluster produces. -/
theorem facePathToSigns_step3_stop [G.LocallyFinite] (E : UCPlanar.PlaneEmbedding G)
    {c : V → V → ℝ} (hc : LatticeProb.Network.IsCond G c) (hFW : E.FaceWalks) (f : V → ℝ)
    {o : V} (γ : G.Walk o o) {F : Set UCPlanar.Plane} (hF : E.IsFace F)
    (hharm : ∀ y, E.Incident F y → LatticeProb.Network.netLaplacian G c f y = 0)
    (hFreg : ∀ y, E.Incident F y → y ∈ E.cycleRegion γ)
    (hstop : ∀ y, E.Incident F y → (∃ u, G.Adj y u ∧ f u ≠ 0) →
      ∀ u, G.Adj y u → u ∈ E.cycleRegion γ)
    {z : V} (hzF : E.Incident F z) (hz0 : f z = 0)
    {w : V} (hwF : E.Incident F w) (hw : ∃ u, (u = w ∨ G.Adj w u) ∧ f u ≠ 0) :
    E.FacePathToSigns {x | x ∈ E.cycleRegion γ ∧ 0 < f x}
      {x | x ∈ E.cycleRegion γ ∧ f x < 0} z := by
  classical
  set P : Set V := {x | x ∈ E.cycleRegion γ ∧ 0 < f x} with hPdef
  set M : Set V := {x | x ∈ E.cycleRegion γ ∧ f x < 0} with hMdef
  have hzPM : z ∉ P ∪ M := by
    intro hcon
    rcases hcon with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hz0] at h <;> exact absurd h (lt_irrefl 0)
  have hmemPM : ∀ x, x ∈ E.cycleRegion γ → f x ≠ 0 → x ∈ P ∪ M := by
    intro x hx hfx
    rcases lt_trichotomy (f x) 0 with h | h | h
    · exact Or.inr ⟨hx, h⟩
    · exact absurd h hfx
    · exact Or.inl ⟨hx, h⟩
  have hnzPM : ∀ x, x ∈ P ∪ M → f x ≠ 0 := by
    rintro x (⟨-, h⟩ | ⟨-, h⟩)
    · exact ne_of_gt h
    · exact ne_of_lt h
  obtain ⟨β₀, hβ₀⟩ := hFW F hF z w hzF hwF
  obtain ⟨u, hu, hfu⟩ := hw
  obtain ⟨a, b, q, hqS, hab, hbS, hqt⟩ :
      ∃ (a b : V) (q : G.Walk z a), (∀ t ∈ q.support, t ∉ P ∪ M) ∧ G.Adj a b ∧ b ∈ P ∪ M ∧
        E.walkTrace q ⊆ E.walkTrace β₀ := by
    rcases hu with rfl | huw
    · exact exists_prefix_avoiding E β₀ hzPM (hmemPM u (hFreg u hwF) hfu)
    · refine exists_prefix_adj_avoiding E β₀ hzPM ⟨w, β₀.end_mem_support, u, huw, ?_⟩
      exact hmemPM u (hstop w hwF ⟨u, huw, hfu⟩ u huw) hfu
  have haF : E.Incident F a :=
    hβ₀ (hqt ((E.pos_mem_walkTrace_iff q a).mpr q.end_mem_support))
  obtain ⟨hp, hm⟩ := sign_pair_of_harmonic hc E f γ hab (hharm a haF)
    (hstop a haF ⟨b, hab, hnzPM b hbS⟩) (hFreg a haF) (hqS a q.end_mem_support) hbS
  refine ⟨F, hF, hzF, a, q.bypass, q.bypass_isPath, ?_, ?_, hp, hm⟩
  · exact (walkTrace_bypass_subset E q).trans (hqt.trans hβ₀)
  · intro t ht
    exact hqS t (q.support_bypass_subset_support ht)

end UCPlanar.Support
