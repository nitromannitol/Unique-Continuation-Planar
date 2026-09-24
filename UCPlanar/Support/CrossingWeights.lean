/- Positivity and edge support of the crossing conductances. -/
import UCPlanar.Support.CrossingGraph
import Mathlib.Tactic

theorem UCPlanar.Support.outgoing_nonneg (a b t d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (hd : 0 ≤ d) (x y : LatticeProb.Site 2) :
    0 ≤ UCPlanar.crossingOutgoing a b t d x y := by
  unfold UCPlanar.crossingOutgoing
  split_ifs <;> positivity

theorem UCPlanar.Support.outgoing_pos (a b t d : ℝ) (ha : 0<a) (hb : 0<b)
    (ht : 0<t) (hd : 0<d) (x y : LatticeProb.Site 2)
    (h : UCPlanar.crossingRelation x y) : 0<UCPlanar.crossingOutgoing a b t d x y := by
  unfold UCPlanar.crossingOutgoing
  rw [if_pos h.1]
  split_ifs with h1 h2 h3 h4
  · exact ha
  · exact hb
  · positivity
  · positivity
  · rcases h.2 with h | h | h | h | h | h | h | h
    all_goals tauto

theorem UCPlanar.Support.outgoing_zero (a b t d : ℝ) (x y : LatticeProb.Site 2)
    (h : ¬UCPlanar.crossingRelation x y) : UCPlanar.crossingOutgoing a b t d x y=0 := by
  unfold UCPlanar.crossingRelation at h
  unfold UCPlanar.crossingOutgoing
  split_ifs <;> tauto

theorem UCPlanar.Support.relation_ne (x y : LatticeProb.Site 2)
    (h : UCPlanar.crossingRelation x y) : x ≠ y := by
  intro heq
  rcases h.2 with h | h | h | h | h | h | h | h
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [heq, LatticeProb.unit, UCPlanar.diagonalStep] at h0 h1 <;> omega
