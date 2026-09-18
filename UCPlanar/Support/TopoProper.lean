/- The drawing of a periodic plane graph is a closed set, so its faces are open. -/
import UCPlanar.Support.TopoFace
import UCPlanar.Support.Periodic

open Set

open scoped Classical

namespace UCPlanar.Support

/-- Inside a bounded square the drawing meets only the vertices of that square and the edges
at the finitely many vertices whose edges reach it. -/
theorem trace_inter_square_subset {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) (R : ℝ) :
    {s | s ∈ Q.embedding.trace ∧ ∀ i, |s i| ≤ R} ⊆
      (Q.pos '' (Q.square R : Set V)) ∪
        ⋃ x ∈ (Q.proper_edges R).toFinset, edgeStar Q.embedding x := by
  rintro s ⟨hs, hbound⟩
  rw [trace_eq_union_edgeStar] at hs
  rcases hs with ⟨v, hv⟩ | hs
  · refine Or.inl ⟨v, ?_, ?_⟩
    · show v ∈ (Q.square R : Set V)
      rw [Finset.mem_coe, UCPlanar.PeriodicGraph.square, Set.Finite.mem_toFinset]
      intro i
      rw [← Q.embedding_pos, hv]
      exact hbound i
    · rw [← Q.embedding_pos]; exact hv
  · obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hs
    obtain ⟨y, h, hmem⟩ := hx
    refine Or.inr (Set.mem_biUnion ?_ ⟨y, h, hmem⟩)
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨y, h, s, hmem, hbound⟩

/-- **The drawing of a periodic plane graph is closed.**  Only finitely many vertices and
finitely many drawn edges reach any bounded square, so the drawing is locally a finite union
of compact sets. -/
theorem isClosed_trace {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V) :
    IsClosed Q.embedding.trace := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro t ht
  set R : ℝ := ‖t‖ + 1 with hR
  set K : Set UCPlanar.Plane := (Q.pos '' (Q.square R : Set V)) ∪
    ⋃ x ∈ (Q.proper_edges R).toFinset, edgeStar Q.embedding x with hK
  have hKtrace : K ⊆ Q.embedding.trace := by
    rintro s (⟨v, -, rfl⟩ | hs)
    · exact Or.inl ⟨v, (congrFun Q.embedding_pos v)⟩
    · obtain ⟨x, -, hx⟩ := Set.mem_iUnion₂.mp hs
      exact edgeStar_subset_trace Q.embedding x hx
  have hKclosed : IsClosed K := by
    refine IsClosed.union ?_ ?_
    · exact (Set.Finite.image _ (Q.square R).finite_toSet).isClosed
    · exact ((Q.proper_edges R).toFinset.isCompact_biUnion
        (fun x _ => isCompact_edgeStar Q.embedding x)).isClosed
  have hball : ∀ s ∈ Metric.ball t 1, ∀ i, |s i| ≤ R := by
    intro s hs i
    have h1 : ‖s - t‖ < 1 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hs
    have h2 : ‖s i - t i‖ ≤ ‖s - t‖ := norm_le_pi_norm (s - t) i
    have h3 : ‖t i‖ ≤ ‖t‖ := norm_le_pi_norm t i
    rw [Real.norm_eq_abs] at h2 h3
    have h4 : |s i| - |t i| ≤ |s i - t i| := abs_sub_abs_le_abs_sub (s i) (t i)
    rw [hR]
    linarith
  refine ⟨Metric.ball t 1 ∩ Kᶜ, ?_, Metric.isOpen_ball.inter hKclosed.isOpen_compl, ?_⟩
  · rintro s ⟨hs1, hs2⟩ hstrace
    exact hs2 (trace_inter_square_subset Q R ⟨hstrace, hball s hs1⟩)
  · exact ⟨Metric.mem_ball_self one_pos, fun hc => ht (hKtrace hc)⟩



/-- The faces of a periodic plane graph are open. -/
theorem isOpen_isFace {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) : IsOpen F := by
  obtain ⟨p, hp, rfl⟩ := hF
  exact (isClosed_trace Q).isOpen_compl.connectedComponentIn

/-- **The frontier of a face is part of the drawing.**  A frontier point off the drawing would
lie in a face meeting the closure of the first, hence in the face itself, which is open. -/
theorem frontier_isFace_subset_trace {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) :
    frontier F ⊆ Q.embedding.trace := by
  intro z hz
  by_contra hzt
  have hH : Q.embedding.IsFace (connectedComponentIn Q.embedding.traceᶜ z) := ⟨z, hzt, rfl⟩
  have hzH : z ∈ connectedComponentIn Q.embedding.traceᶜ z := mem_connectedComponentIn hzt
  have hopen : IsOpen (connectedComponentIn Q.embedding.traceᶜ z) := isOpen_isFace Q hH
  have hmeet : (connectedComponentIn Q.embedding.traceᶜ z ∩ F).Nonempty := by
    have := hz.1
    exact mem_closure_iff.mp this _ hopen hzH
  obtain ⟨w, hw1, hw2⟩ := hmeet
  have heq := isFace_eq_of_mem Q.embedding hH hF hw1 hw2
  have hzF : z ∈ F := heq ▸ hzH
  have hint : z ∉ F := by
    have h2 := hz.2
    rwa [(isOpen_isFace Q hF).interior_eq] at h2
  exact hint hzF

end UCPlanar.Support
