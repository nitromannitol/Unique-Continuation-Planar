/- The banded sign step of Section 4: at a positive threshold a vertex of small value which is
adjacent to a value beyond the band is adjacent to a value beyond the band of the opposite sign,
and the face path of Step 3 either reaches both signs or stops inside the band. -/
import UCPlanar.Support.TopoFacePath
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **The sign completion of Section 4.**  At a vertex all of whose neighbours stay in the
region, a neighbour whose value is at least `B` in absolute value gives a neighbour above `A` and
a neighbour below `-A`, granted the observation that opens Section 4 at that vertex. -/
theorem sign_pair_of_band (E : UCPlanar.PlaneEmbedding G) (f : V → ℝ) {A B : ℝ} (hAB : A < B)
    {o : V} (γ : G.Walk o o) {a b : V} (hab : G.Adj a b)
    (hup : ∀ w, G.Adj a w → B ≤ f w → ∃ y, G.Adj a y ∧ f y < -A)
    (hdn : ∀ w, G.Adj a w → f w ≤ -B → ∃ y, G.Adj a y ∧ A < f y)
    (hnb : ∀ y, G.Adj a y → y ∈ E.cycleRegion γ)
    (hbig : B ≤ |f b|) :
    (∃ p ∈ {x | x ∈ E.cycleRegion γ ∧ A < f x}, G.Adj a p) ∧
      (∃ m ∈ {x | x ∈ E.cycleRegion γ ∧ f x < -A}, G.Adj a m) := by
  rcases le_abs.mp hbig with hb | hb
  · obtain ⟨y, hay, hfy⟩ := hup b hab hb
    exact ⟨⟨b, ⟨hnb b hab, by linarith⟩, hab⟩, ⟨y, ⟨hnb y hay, hfy⟩, hay⟩⟩
  · have hb' : f b ≤ -B := by linarith
    obtain ⟨y, hay, hfy⟩ := hdn b hab hb'
    exact ⟨⟨y, ⟨hnb y hay, hfy⟩, hay⟩, ⟨b, ⟨hnb b hab, by linarith⟩, hab⟩⟩

/-- **The third hypothesis of the topological lemma at a positive threshold.**  Walking along the
frontier of a face from a vertex of small value to a vertex of large value and stopping at the
last small vertex, either the first large value met lies beyond the band, in which case the
vertex carries a face path to both sign sets, or it lies inside the band, in which case the
vertex is discarded and the witness is exhibited together with the path reaching it. -/
theorem facePathToSigns_band (E : UCPlanar.PlaneEmbedding G) (hFW : E.FaceWalks)
    (f : V → ℝ) {A B : ℝ} (hAB : A < B)
    {o : V} (γ : G.Walk o o) {F : Set UCPlanar.Plane} (hF : E.IsFace F)
    (hup : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → B ≤ f u →
      ∃ v, G.Adj y v ∧ f v < -A)
    (hdn : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → f u ≤ -B →
      ∃ v, G.Adj y v ∧ A < f v)
    (hFreg : ∀ y, E.Incident F y → y ∈ E.cycleRegion γ)
    (hFnb : ∀ y, E.Incident F y → ∀ u, G.Adj y u → u ∈ E.cycleRegion γ)
    {z : V} (hzF : E.Incident F z) (hz0 : |f z| ≤ A)
    {w : V} (hwF : E.Incident F w) (hwA : A < |f w|) :
    E.FacePathToSigns {x | x ∈ E.cycleRegion γ ∧ A < f x}
        {x | x ∈ E.cycleRegion γ ∧ f x < -A} z ∨
      ∃ (a b : V) (q : G.Walk z a), q.IsPath ∧ (∀ t ∈ q.support, E.Incident F t) ∧
        G.Adj a b ∧ A < |f b| ∧ |f b| < B := by
  set P : Set V := {x | x ∈ E.cycleRegion γ ∧ A < f x} with hP
  set M : Set V := {x | x ∈ E.cycleRegion γ ∧ f x < -A} with hM
  have hzPM : z ∉ P ∪ M := by
    have h1 : f z ≤ A := le_trans (le_abs_self _) hz0
    have h2 : -A ≤ f z := neg_le_of_abs_le hz0
    rintro (⟨-, h⟩ | ⟨-, h⟩) <;> linarith
  have hwPM : w ∈ P ∪ M := by
    rcases lt_abs.mp hwA with h | h
    · exact Or.inl ⟨hFreg w hwF, h⟩
    · exact Or.inr ⟨hFreg w hwF, by linarith⟩
  obtain ⟨β₀, hβ₀⟩ := hFW F hF z w hzF hwF
  obtain ⟨a, b, q, hqS, hab, hbS, hqt⟩ := exists_prefix_avoiding E β₀ hzPM hwPM
  have hinc : ∀ t ∈ q.support, E.Incident F t := by
    intro t ht
    exact hβ₀ (hqt ((E.pos_mem_walkTrace_iff q t).mpr ht))
  have haF : E.Incident F a := hinc a q.end_mem_support
  have hbA : A < |f b| := by
    rcases hbS with ⟨-, h⟩ | ⟨-, h⟩
    · exact lt_of_lt_of_le h (le_abs_self _)
    · have : A < -f b := by linarith
      exact lt_of_lt_of_le this (neg_le_abs _)
  by_cases hbig : B ≤ |f b|
  · left
    have ha0 : |f a| ≤ A := by
      have haPM := hqS a q.end_mem_support
      have hareg : a ∈ E.cycleRegion γ := hFreg a haF
      refine abs_le.mpr ⟨?_, ?_⟩
      · by_contra hcon
        exact haPM (Or.inr ⟨hareg, not_le.mp hcon⟩)
      · by_contra hcon
        exact haPM (Or.inl ⟨hareg, not_le.mp hcon⟩)
    obtain ⟨hp, hm⟩ := sign_pair_of_band E f hAB γ hab (hup a haF ha0) (hdn a haF ha0)
      (hFnb a haF) hbig
    exact ⟨F, hF, hzF, a, q.bypass, q.bypass_isPath,
      (walkTrace_bypass_subset E q).trans (hqt.trans hβ₀),
      (fun t ht => hqS t (q.support_bypass_subset_support ht)), hp, hm⟩
  · right
    exact ⟨a, b, q.bypass, q.bypass_isPath,
      (fun t ht => hinc t (q.support_bypass_subset_support ht)), hab, hbA, lt_of_not_ge hbig⟩


/-- **A path drawn along one face is short.**  Its vertices are distinct and all incident to the
face, so its length is below the face bound. -/
theorem length_lt_faceBound (E : UCPlanar.PlaneEmbedding G) {L : ℕ} (hL : E.FaceBound L)
    {F : Set UCPlanar.Plane} (hF : E.IsFace F) {z a : V} (q : G.Walk z a) (hq : q.IsPath)
    (hinc : ∀ t ∈ q.support, E.Incident F t) : q.length + 1 ≤ L := by
  classical
  obtain ⟨hfin, hcard⟩ := hL F hF
  have hsub : q.support.toFinset ⊆ hfin.toFinset := by
    intro t ht
    exact (Set.Finite.mem_toFinset hfin).mpr (hinc t (List.mem_toFinset.mp ht))
  have h1 : q.support.toFinset.card ≤ hfin.toFinset.card := Finset.card_le_card hsub
  have h2 : q.support.toFinset.card = q.support.length :=
    List.toFinset_card_of_nodup hq.support_nodup
  have h3 : q.support.length = q.length + 1 := SimpleGraph.Walk.length_support q
  have h4 : hfin.toFinset.card = {x | E.Incident F x}.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
  omega

/-- **The banded face path with the discarded vertex located.**  Either the vertex carries a face
path to both sign sets, or it is within the face bound of a vertex whose value lies inside the
band. -/
theorem facePathToSigns_band_dist (E : UCPlanar.PlaneEmbedding G) (hFW : E.FaceWalks)
    {L : ℕ} (hL : E.FaceBound L) (f : V → ℝ) {A B : ℝ} (hAB : A < B)
    {o : V} (γ : G.Walk o o) {F : Set UCPlanar.Plane} (hF : E.IsFace F)
    (hup : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → B ≤ f u →
      ∃ v, G.Adj y v ∧ f v < -A)
    (hdn : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → f u ≤ -B →
      ∃ v, G.Adj y v ∧ A < f v)
    (hFreg : ∀ y, E.Incident F y → y ∈ E.cycleRegion γ)
    (hFnb : ∀ y, E.Incident F y → ∀ u, G.Adj y u → u ∈ E.cycleRegion γ)
    {z : V} (hzF : E.Incident F z) (hz0 : |f z| ≤ A)
    {w : V} (hwF : E.Incident F w) (hwA : A < |f w|) :
    E.FacePathToSigns {x | x ∈ E.cycleRegion γ ∧ A < f x}
        {x | x ∈ E.cycleRegion γ ∧ f x < -A} z ∨
      ∃ y, G.dist z y ≤ L ∧ A < |f y| ∧ |f y| < B := by
  rcases facePathToSigns_band E hFW f hAB γ hF hup hdn hFreg hFnb hzF hz0 hwF hwA with h | h
  · exact Or.inl h
  · obtain ⟨a, b, q, hq, hinc, hab, hbA, hbB⟩ := h
    refine Or.inr ⟨b, ?_, hbA, hbB⟩
    have hlen : q.length + 1 ≤ L := length_lt_faceBound E hL hF q hq hinc
    have hdist : G.dist z b ≤ (q.concat hab).length := SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.length_concat] at hdist
    omega

/-- **The banded face path with the neighbours asked only at the stopping vertex.**  The far
vertex of the face may itself lie inside the small values, provided one of its neighbours does
not; that is the case the neighbour-buffered cluster produces. -/
theorem facePathToSigns_band_stop (E : UCPlanar.PlaneEmbedding G) (hFW : E.FaceWalks)
    (f : V → ℝ) {A B : ℝ} (hAB : A < B)
    {o : V} (γ : G.Walk o o) {F : Set UCPlanar.Plane} (hF : E.IsFace F)
    (hup : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → B ≤ f u →
      ∃ v, G.Adj y v ∧ f v < -A)
    (hdn : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → f u ≤ -B →
      ∃ v, G.Adj y v ∧ A < f v)
    (hFreg : ∀ y, E.Incident F y → y ∈ E.cycleRegion γ)
    (hstop : ∀ y, E.Incident F y → (∃ u, G.Adj y u ∧ A < |f u|) →
      ∀ u, G.Adj y u → u ∈ E.cycleRegion γ)
    {z : V} (hzF : E.Incident F z) (hz0 : |f z| ≤ A)
    {w : V} (hwF : E.Incident F w) (hw : ∃ u, (u = w ∨ G.Adj w u) ∧ A < |f u|) :
    E.FacePathToSigns {x | x ∈ E.cycleRegion γ ∧ A < f x}
        {x | x ∈ E.cycleRegion γ ∧ f x < -A} z ∨
      ∃ (a b : V) (q : G.Walk z a), q.IsPath ∧ (∀ t ∈ q.support, E.Incident F t) ∧
        G.Adj a b ∧ A < |f b| ∧ |f b| < B := by
  classical
  set P : Set V := {x | x ∈ E.cycleRegion γ ∧ A < f x} with hP
  set M : Set V := {x | x ∈ E.cycleRegion γ ∧ f x < -A} with hM
  have hzPM : z ∉ P ∪ M := by
    have h1 : f z ≤ A := le_trans (le_abs_self _) hz0
    have h2 : -A ≤ f z := neg_le_of_abs_le hz0
    rintro (⟨-, h⟩ | ⟨-, h⟩) <;> linarith
  have hmemPM : ∀ x, x ∈ E.cycleRegion γ → A < |f x| → x ∈ P ∪ M := by
    intro x hx hfx
    rcases lt_abs.mp hfx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, by linarith⟩
  have hPMabs : ∀ x, x ∈ P ∪ M → A < |f x| := by
    rintro x (⟨-, h⟩ | ⟨-, h⟩)
    · exact lt_of_lt_of_le h (le_abs_self _)
    · exact lt_of_lt_of_le (show A < -f x by linarith) (neg_le_abs _)
  obtain ⟨β₀, hβ₀⟩ := hFW F hF z w hzF hwF
  obtain ⟨u, hu, hfu⟩ := hw
  obtain ⟨a, b, q, hqS, hab, hbS, hqt⟩ :
      ∃ (a b : V) (q : G.Walk z a), (∀ t ∈ q.support, t ∉ P ∪ M) ∧ G.Adj a b ∧ b ∈ P ∪ M ∧
        E.walkTrace q ⊆ E.walkTrace β₀ := by
    rcases hu with rfl | huw
    · exact exists_prefix_avoiding E β₀ hzPM (hmemPM u (hFreg u hwF) hfu)
    · refine exists_prefix_adj_avoiding E β₀ hzPM ⟨w, β₀.end_mem_support, u, huw, ?_⟩
      exact hmemPM u (hstop w hwF ⟨u, huw, hfu⟩ u huw) hfu
  have hinc : ∀ t ∈ q.support, E.Incident F t := by
    intro t ht
    exact hβ₀ (hqt ((E.pos_mem_walkTrace_iff q t).mpr ht))
  have haF : E.Incident F a := hinc a q.end_mem_support
  have hbA : A < |f b| := hPMabs b hbS
  by_cases hbig : B ≤ |f b|
  · left
    have ha0 : |f a| ≤ A := by
      have haPM := hqS a q.end_mem_support
      have hareg : a ∈ E.cycleRegion γ := hFreg a haF
      refine abs_le.mpr ⟨?_, ?_⟩
      · by_contra hcon
        exact haPM (Or.inr ⟨hareg, not_le.mp hcon⟩)
      · by_contra hcon
        exact haPM (Or.inl ⟨hareg, not_le.mp hcon⟩)
    obtain ⟨hp, hm⟩ := sign_pair_of_band E f hAB γ hab (hup a haF ha0) (hdn a haF ha0)
      (hstop a haF ⟨b, hab, hbA⟩) hbig
    exact ⟨F, hF, hzF, a, q.bypass, q.bypass_isPath,
      (walkTrace_bypass_subset E q).trans (hqt.trans hβ₀),
      (fun t ht => hqS t (q.support_bypass_subset_support ht)), hp, hm⟩
  · right
    exact ⟨a, b, q.bypass, q.bypass_isPath,
      (fun t ht => hinc t (q.support_bypass_subset_support ht)), hab, hbA, lt_of_not_ge hbig⟩

/-- **The banded face path with the discarded vertex located**, with the neighbours asked only at
the stopping vertex. -/
theorem facePathToSigns_band_dist_stop (E : UCPlanar.PlaneEmbedding G) (hFW : E.FaceWalks)
    {L : ℕ} (hL : E.FaceBound L) (f : V → ℝ) {A B : ℝ} (hAB : A < B)
    {o : V} (γ : G.Walk o o) {F : Set UCPlanar.Plane} (hF : E.IsFace F)
    (hup : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → B ≤ f u →
      ∃ v, G.Adj y v ∧ f v < -A)
    (hdn : ∀ y, E.Incident F y → |f y| ≤ A → ∀ u, G.Adj y u → f u ≤ -B →
      ∃ v, G.Adj y v ∧ A < f v)
    (hFreg : ∀ y, E.Incident F y → y ∈ E.cycleRegion γ)
    (hstop : ∀ y, E.Incident F y → (∃ u, G.Adj y u ∧ A < |f u|) →
      ∀ u, G.Adj y u → u ∈ E.cycleRegion γ)
    {z : V} (hzF : E.Incident F z) (hz0 : |f z| ≤ A)
    {w : V} (hwF : E.Incident F w) (hw : ∃ u, (u = w ∨ G.Adj w u) ∧ A < |f u|) :
    E.FacePathToSigns {x | x ∈ E.cycleRegion γ ∧ A < f x}
        {x | x ∈ E.cycleRegion γ ∧ f x < -A} z ∨
      ∃ y, G.dist z y ≤ L ∧ A < |f y| ∧ |f y| < B := by
  rcases facePathToSigns_band_stop E hFW f hAB γ hF hup hdn hFreg hstop hzF hz0 hwF hw with h | h
  · exact Or.inl h
  · obtain ⟨a, b, q, hq, hinc, hab, hbA, hbB⟩ := h
    refine Or.inr ⟨b, ?_, hbA, hbB⟩
    have hlen : q.length + 1 ≤ L := length_lt_faceBound E hL hF q hq hinc
    have hdist : G.dist z b ≤ (q.concat hab).length := SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.length_concat] at hdist
    omega

end UCPlanar.Support
