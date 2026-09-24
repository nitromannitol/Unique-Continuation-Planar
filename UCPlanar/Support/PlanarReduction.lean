/- Boundary counting from alternating-path intersection. -/
import UCPlanar.Support.PlanarDomain
import UCPlanar.Support.PlanarOrder

open scoped Classical

/-- Alternating-path intersection yields the boundary charge for disjoint sign attachments. -/
theorem UCPlanar.PlaneEmbedding.boundary_charge_of_alternating_paths {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) (D : Set UCPlanar.Plane)
    (H : SimpleGraph V) (hHG : H ≤ G)
    (hH : ∀ x y, H.Adj x y ↔ ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ D)
    (P M : Set V) (B : Finset V) (hPM : Disjoint P M)
    (hBP : UCPlanar.ComponentsMeetBoundary H P (B : Set V))
    (hBM : UCPlanar.ComponentsMeetBoundary H M (B : Set V))
    {n : ℕ} (v w p m : Fin n → V) (β : ∀ i, G.Walk (v i) (w i))
    (hp : ∀ i, p i ∈ P) (hm : ∀ i, m i ∈ M)
    (hwp : ∀ i, G.Adj (w i) (p i)) (hwm : ∀ i, G.Adj (w i) (m i))
    (ha : ∀ i, ∀ t ∈ (β i).support, t ∉ P ∪ M)
    (hdis : ∀ i j, i ≠ j → ∀ t ∈ (β i).support, t ∉ (β j).support)
    (htp : ∀ i, E.walkTrace ((β i).concat (hwp i)) ⊆ D)
    (htm : ∀ i, E.walkTrace ((β i).concat (hwm i)) ⊆ D)
    (hcross : ∀ k a b c : Fin n, k < a → a < b → b < c →
      ∀ ξ : G.Walk (v k) (v b), ∀ ζ : G.Walk (v a) (v c),
      E.walkTrace ξ ⊆ D → E.walkTrace ζ ⊆ D → ∃ t ∈ ξ.support, t ∈ ζ.support) :
    n ≤ 2 * B.card := by
  classical
  let pp : Fin n → P := fun i => UCPlanar.Support.componentBoundaryVertex H P (B : Set V) hBP
    ((H.induce P).connectedComponentMk ⟨p i, hp i⟩)
  let mm : Fin n → M := fun i => UCPlanar.Support.componentBoundaryVertex H M (B : Set V) hBM
    ((H.induce M).connectedComponentMk ⟨m i, hm i⟩)
  apply UCPlanar.Support.boundary_count_fin_nonalternating (fun i => (pp i).val)
    (fun i => (mm i).val) B
  · intro i
    exact (UCPlanar.Support.componentBoundaryVertex_spec H P (B : Set V) hBP
      ((H.induce P).connectedComponentMk ⟨p i, hp i⟩)).1
  · intro i
    exact (UCPlanar.Support.componentBoundaryVertex_spec H M (B : Set V) hBM
      ((H.induce M).connectedComponentMk ⟨m i, hm i⟩)).1
  · intro i j he
    have hx := (pp i).property
    rw [he] at hx
    exact Set.disjoint_left.mp hPM hx (mm j).property
  · intro k a b c hka hab hbc heP heM
    have hrP := (UCPlanar.Support.boundary_labels_eq_iff_reachable H P (B : Set V) hBP
      ⟨p k, hp k⟩ ⟨p b, hp b⟩).mp heP
    have hrM := (UCPlanar.Support.boundary_labels_eq_iff_reachable H M (B : Set V) hBM
      ⟨m a, hm a⟩ ⟨m c, hm c⟩).mp heM
    obtain ⟨ξ, hξ, hsξ⟩ := E.walk_between_attachments_in_domain D H hHG hH P
      (β k) (β b) (hp k) (hp b) (hwp k) (hwp b) (htp k) (htp b) hrP
    obtain ⟨ζ, hζ, hsζ⟩ := E.walk_between_attachments_in_domain D H hHG hH M
      (β a) (β c) (hm a) (hm c) (hwm a) (hwm c) (htm a) (htm c) hrM
    obtain ⟨t, htξ, htζ⟩ := hcross k a b c hka hab hbc ξ ζ hξ hζ
    rcases hsξ t htξ with htk | htb | htP
    · rcases hsζ t htζ with hta | htc | htM
      · exact hdis k a (ne_of_lt hka) t htk hta
      · exact hdis k c (ne_of_lt (hka.trans (hab.trans hbc))) t htk htc
      · exact ha k t htk (Or.inr htM)
    · rcases hsζ t htζ with hta | htc | htM
      · exact hdis b a (ne_of_gt hab) t htb hta
      · exact hdis b c (ne_of_lt hbc) t htb htc
      · exact ha b t htb (Or.inr htM)
    · rcases hsζ t htζ with hta | htc | htM
      · exact ha a t hta (Or.inl htP)
      · exact ha c t htc (Or.inl htP)
      · exact Set.disjoint_left.mp hPM htP htM

