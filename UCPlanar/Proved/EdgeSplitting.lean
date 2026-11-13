import UCPlanar.Vendored.Janiszewski
import UCPlanar.Support.TopoMinimal
import UCPlanar.Support.TopoSeparate
import UCPlanar.External.EdgeSplitting

/-!
# Janiszewski's theorem at a point, and the splitting of edge sets

`UCPlanar.Support.JaniszewskiPoint` holds: if two closed sets of the plane meet in at most one
point and neither separates a point `p` from infinity, their union does not separate `p` from
infinity either.  The compact case is Janiszewski's theorem for compact plane sets
(`UCPlanar.Vendored.not_separates_union`, copied from Lattice-Probability).  The closed case
reduces to it: if the union separates `p`, the component of `p` in its complement is bounded, so
its closure lies in a closed ball `T`; the frontier of that component lies in the union, so the
component of `p` in the complement of `(A ∪ B) ∩ T` is the same bounded set, while `A ∩ T` and
`B ∩ T` are compact and separate `p` no more than `A` and `B` do.

Consequently the cited statement `UCPlanar.External.EdgeSplitting` holds for every plane
embedding (`UCPlanar.Support.edgeSplitting_of_janiszewskiPoint`).
-/

open Set Metric

namespace UCPlanar.Support

/-- Cutting a closed set down to a set `T` that contains the closure of the component of `p` in
its complement does not enlarge that component. -/
theorem connectedComponentIn_compl_inter_subset {S T : Set UCPlanar.Plane} (hS : IsClosed S)
    {p : UCPlanar.Plane} (hp : p ∉ S) (hT : closure (connectedComponentIn Sᶜ p) ⊆ T) :
    connectedComponentIn (S ∩ T)ᶜ p ⊆ connectedComponentIn Sᶜ p := by
  have hpST : p ∈ (S ∩ T)ᶜ := fun h => hp h.1
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    hS.isOpen_compl.connectedComponentIn
    ⟨p, mem_connectedComponentIn hpST, mem_connectedComponentIn hp⟩ ?_
  rintro x ⟨hxcl, hxW⟩
  have hxS : x ∉ S := fun h => connectedComponentIn_subset _ _ hxW ⟨h, hT hxcl⟩
  obtain ⟨y, hyx, hyp⟩ := mem_closure_iff.1 hxcl _ hS.isOpen_compl.connectedComponentIn
    (mem_connectedComponentIn hxS)
  rw [connectedComponentIn_eq hyp, ← connectedComponentIn_eq hyx]
  exact mem_connectedComponentIn hxS

/-- **Janiszewski's theorem at a point.**  Two closed sets of the plane meeting in at most one
point, neither of which separates `p` from infinity, have a union which does not separate `p`
from infinity either. -/
theorem janiszewskiPoint_holds : JaniszewskiPoint := by
  intro A B hA hB v hAB p hpA hpB hiA hiB hiAB
  have hpAB : p ∉ A ∪ B := hiAB.1
  have hb : Bornology.IsBounded (connectedComponentIn (A ∪ B)ᶜ p) := hiAB.2
  obtain ⟨R, hR⟩ := hb.closure.subset_closedBall (0 : UCPlanar.Plane)
  have hsub := connectedComponentIn_compl_inter_subset (hA.union hB) hpAB hR
  have hAc : IsCompact (A ∩ closedBall 0 R) := (isCompact_closedBall 0 R).inter_left hA
  have hBc : IsCompact (B ∩ closedBall 0 R) := (isCompact_closedBall 0 R).inter_left hB
  have hint : IsPreconnected ((A ∩ closedBall 0 R) ∩ (B ∩ closedBall 0 R)) :=
    (subsingleton_singleton.anti fun x hx => hAB ⟨hx.1.1, hx.2.1⟩).isPreconnected
  have hp : p ∉ (A ∩ closedBall 0 R) ∪ (B ∩ closedBall 0 R) :=
    fun h => h.elim (fun h => hpA h.1) (fun h => hpB h.1)
  have hnA : ¬ UCPlanar.Vendored.Separates (A ∩ closedBall 0 R) p := fun h =>
    hiA ⟨hpA, h.subset (connectedComponentIn_mono p (compl_subset_compl.2 inter_subset_left))⟩
  have hnB : ¬ UCPlanar.Vendored.Separates (B ∩ closedBall 0 R) p := fun h =>
    hiB ⟨hpB, h.subset (connectedComponentIn_mono p (compl_subset_compl.2 inter_subset_left))⟩
  refine UCPlanar.Vendored.not_separates_union hAc hBc hint hp hnA hnB ?_
  rw [UCPlanar.Vendored.Separates, ← union_inter_distrib_right]
  exact hb.subset hsub

/-- **The splitting of edge sets.**  The cited statement `UCPlanar.External.EdgeSplitting` holds
for every plane embedding. -/
theorem edgeSplitting_holds {V : Type*} {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) :
    UCPlanar.External.EdgeSplitting E :=
  edgeSplitting_of_janiszewskiPoint janiszewskiPoint_holds E

end UCPlanar.Support
