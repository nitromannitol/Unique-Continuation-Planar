/- Coordinate transport to the square-lattice contour and winding library. -/
import LatticeProb.Site
import LatticeProb.Lattice.Planar

/-- The coordinate identification of the two square-lattice site types. -/
def UCPlanar.Support.planarSiteEquiv :
    LatticeProb.Site 2 ≃ LatticeProb.Lattice.Planar.Site where
  toFun x := (x 0, x 1)
  invFun x := ![x.1, x.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := Prod.ext rfl rfl

/-- The coordinate identification preserves the square-lattice adjacency relation. -/
theorem UCPlanar.Support.planarSiteEquiv_adj (x y : LatticeProb.Site 2) :
    (LatticeProb.lattice 2).Adj x y ↔ LatticeProb.Lattice.Planar.squareGraph.Adj
      (UCPlanar.Support.planarSiteEquiv x) (UCPlanar.Support.planarSiteEquiv y) := by
  change (∃ i : Fin 2, y = x + LatticeProb.unit i ∨ x = y + LatticeProb.unit i) ↔
    |x 0 - y 0| + |x 1 - y 1| = 1
  constructor
  · rintro ⟨i, rfl | rfl⟩ <;> fin_cases i <;> simp [LatticeProb.unit]
  · intro h
    have hc : (y 0 = x 0 + 1 ∧ y 1 = x 1) ∨
        (x 0 = y 0 + 1 ∧ y 1 = x 1) ∨
        (y 1 = x 1 + 1 ∧ y 0 = x 0) ∨
        (x 1 = y 1 + 1 ∧ y 0 = x 0) := by
      rcases abs_cases (x 0 - y 0) with ⟨h0, h0'⟩ | ⟨h0, h0'⟩ <;>
      rcases abs_cases (x 1 - y 1) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rw [h0, h1] at h <;> omega
    rcases hc with h | h | h | h
    · refine ⟨0, Or.inl ?_⟩
      funext i; fin_cases i <;> simp [LatticeProb.unit] <;> omega
    · refine ⟨0, Or.inr ?_⟩
      funext i; fin_cases i <;> simp [LatticeProb.unit] <;> omega
    · refine ⟨1, Or.inl ?_⟩
      funext i; fin_cases i <;> simp [LatticeProb.unit] <;> omega
    · refine ⟨1, Or.inr ?_⟩
      funext i; fin_cases i <;> simp [LatticeProb.unit] <;> omega

/-- The two presentations of the square lattice are isomorphic. -/
def UCPlanar.Support.planarGraphIso :
    LatticeProb.lattice 2 ≃g LatticeProb.Lattice.Planar.squareGraph where
  toEquiv := UCPlanar.Support.planarSiteEquiv
  map_rel_iff' := (UCPlanar.Support.planarSiteEquiv_adj _ _).symm

/-- The support of a closed square-lattice graph walk is a closed unit-step list. -/
theorem UCPlanar.Support.isClosedWalk_support {o : LatticeProb.Lattice.Planar.Site}
    (p : LatticeProb.Lattice.Planar.squareGraph.Walk o o) :
    LatticeProb.Lattice.Planar.IsClosedWalk p.support := by
  refine ⟨p.support_ne_nil, ?_, ?_⟩
  · rw [List.head?_eq_some_head p.support_ne_nil,
      List.getLast?_eq_some_getLast p.support_ne_nil, p.head_support, p.getLast_support]
  · exact p.isChain_adj_support.imp (fun _ _ h => LatticeProb.Lattice.Planar.isUnit_of_adj h)

/-- Graph cycles provide the simple closed contours used by the winding theory. -/
theorem UCPlanar.Support.isSimpleClosed_support {o : LatticeProb.Lattice.Planar.Site}
    (p : LatticeProb.Lattice.Planar.squareGraph.Walk o o) (hp : p.IsCycle) :
    LatticeProb.Lattice.Planar.IsSimpleClosed p.support := by
  refine ⟨UCPlanar.Support.isClosedWalk_support p, hp.support_nodup, ?_⟩
  simpa only [List.length_tail, p.length_support, Nat.add_sub_cancel] using hp.three_le_length

/-- A square-lattice graph walk avoiding a contour is a path in its complement. -/
theorem UCPlanar.Support.offAdj_of_walk_support {x y : LatticeProb.Lattice.Planar.Site}
    (p : LatticeProb.Lattice.Planar.squareGraph.Walk x y)
    (c : List LatticeProb.Lattice.Planar.Site) (ha : ∀ z ∈ p.support, z ∉ c) :
    Relation.ReflTransGen (LatticeProb.Lattice.Planar.OffAdj c) x y := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | cons h p ih =>
    refine (Relation.ReflTransGen.single ⟨ha _ (by simp),
      ha _ (by simp [p.start_mem_support]), LatticeProb.Lattice.Planar.isUnit_of_adj h⟩).trans ?_
    exact ih (fun z hz => ha z (by simp [hz]))

/-- A walk whose vertices avoid a closed contour preserves its winding number. -/
theorem UCPlanar.Support.wind_eq_of_walk_avoiding {x y : LatticeProb.Lattice.Planar.Site}
    (p : LatticeProb.Lattice.Planar.squareGraph.Walk x y)
    (c : List LatticeProb.Lattice.Planar.Site) (hc : LatticeProb.Lattice.Planar.IsClosedWalk c)
    (ha : ∀ z ∈ p.support, z ∉ c) :
    LatticeProb.Lattice.Planar.wind c x = LatticeProb.Lattice.Planar.wind c y := by
  exact LatticeProb.Lattice.Planar.wind_eq_of_reflTransGen hc
    (UCPlanar.Support.offAdj_of_walk_support p c ha)

