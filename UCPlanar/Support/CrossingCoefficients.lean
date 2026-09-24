/- The eight conductances at a vertex of the crossing graph. -/
import UCPlanar.Support.CrossingGraph
import Mathlib.Tactic

theorem UCPlanar.Support.weight_plus_zero (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x + LatticeProb.unit 0) =
      if Even (x 0 + x 1) then b else a := by
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_minus_zero (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x - LatticeProb.unit 0) =
      if Even (x 0 + x 1) then a else b := by
  have hn : Even ((x - LatticeProb.unit 0 : LatticeProb.Site 2) 0 + (x - LatticeProb.unit 0 : LatticeProb.Site 2) 1) ↔
      ¬Even (x 0 + x 1) := by
    simp only [Int.even_iff, Pi.sub_apply, LatticeProb.unit, Pi.single_apply]
    norm_num
    omega
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_plus_one (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x + LatticeProb.unit 1) =
      if Even (x 0 + x 1) then b else a := by
  have hn : Even ((x + LatticeProb.unit 1 : LatticeProb.Site 2) 0 + (x + LatticeProb.unit 1 : LatticeProb.Site 2) 1) ↔
      ¬Even (x 0 + x 1) := by
    simp only [Int.even_iff, Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    norm_num
    omega
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_minus_one (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x - LatticeProb.unit 1) =
      if Even (x 0 + x 1) then a else b := by
  have hn : Even ((x - LatticeProb.unit 1 : LatticeProb.Site 2) 0 + (x - LatticeProb.unit 1 : LatticeProb.Site 2) 1) ↔
      ¬Even (x 0 + x 1) := by
    simp only [Int.even_iff, Pi.sub_apply, LatticeProb.unit, Pi.single_apply]
    norm_num
    omega
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_diag_plus (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x + UCPlanar.diagonalStep) =
      if Even (x 0 + x 1) then d else 0 := by
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_diag_minus (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x - UCPlanar.diagonalStep) =
      if Even (x 0 + x 1) then d else 0 := by
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_two_plus (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x + (2 : ℤ) • UCPlanar.diagonalStep) =
      if Even (x 0 + x 1) then t else 0 := by
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp_all [Int.even_iff] <;> omega

theorem UCPlanar.Support.weight_two_minus (a b t d : ℝ) (x : LatticeProb.Site 2) :
    UCPlanar.crossingConductance a b t d x (x - (2 : ℤ) • UCPlanar.diagonalStep) =
      if Even (x 0 + x 1) then t else 0 := by
  simp only [UCPlanar.crossingConductance, UCPlanar.crossingOutgoing,
    funext_iff, Fin.forall_fin_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    LatticeProb.unit, Pi.single_apply, UCPlanar.diagonalStep]
  norm_num
  split_ifs <;> simp only [Int.even_iff] at *
  all_goals first | omega | ring
