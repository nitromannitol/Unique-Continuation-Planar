/- The positive undirected network of Section 5. -/
import UCPlanar.Support.CrossingWeights

theorem UCPlanar.Support.crossing_isCond (a b t d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) (hd : 0 < d) :
    LatticeProb.Network.IsCond UCPlanar.crossingGraph (UCPlanar.crossingConductance a b t d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact add_comm _ _
  · intro x y h
    change x ≠ y ∧ (UCPlanar.crossingRelation x y ∨ UCPlanar.crossingRelation y x) at h
    rcases h.2 with h | h
    · exact add_pos_of_pos_of_nonneg (UCPlanar.Support.outgoing_pos a b t d ha hb ht hd x y h)
        (UCPlanar.Support.outgoing_nonneg a b t d ha.le hb.le ht.le hd.le y x)
    · exact add_pos_of_nonneg_of_pos (UCPlanar.Support.outgoing_nonneg a b t d ha.le hb.le ht.le hd.le x y)
        (UCPlanar.Support.outgoing_pos a b t d ha hb ht hd y x h)
  · intro x y h
    have hxy : ¬UCPlanar.crossingRelation x y := by
      intro hr
      exact h ⟨UCPlanar.Support.relation_ne x y hr, Or.inl hr⟩
    have hyx : ¬UCPlanar.crossingRelation y x := by
      intro hr
      exact h ⟨(UCPlanar.Support.relation_ne y x hr).symm, Or.inr hr⟩
    unfold UCPlanar.crossingConductance
    rw [UCPlanar.Support.outgoing_zero a b t d x y hxy,
      UCPlanar.Support.outgoing_zero a b t d y x hyx, add_zero]
