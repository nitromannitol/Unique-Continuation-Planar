import UCPlanar.Support.TopoMinimal

/-!
# Cited input: Janiszewski's theorem for edge-set drawings

Records, as a `Prop`-valued hypothesis rather than a proof, the point form of Janiszewski's
theorem for the drawings of two disjoint finite edge sets of a plane graph meeting in at most
one vertex: if the union of the two drawings does not separate two points, then already one of
the two edge sets' drawings alone does not separate them. Cited from Newman, *Elements of the
Topology of Plane Sets of Points*, and from Mohar-Thomassen; consumed as a hypothesis wherever
`UCPlanar.External.EdgeSplitting` appears.
-/

open scoped Classical

-- FROZEN-STATEMENT-BEGIN
/-- Janiszewski's theorem at a point, for the drawings of two finite edge sets of a plane
graph.  If two closed sets of the plane have a connected intersection and neither separates two
points, their union does not separate them either; when the two sets are the drawings of
disjoint finite edge sets meeting in at most one drawn vertex, the intersection is a point or
empty and the statement reads as below.  Newman, *Elements of the Topology of Plane Sets of
Points*, Chapter V, Theorem 9.3; Mohar and Thomassen, *Graphs on Surfaces*, Chapter 2;
Thomassen, *The Jordan-Schoenflies theorem and the classification of surfaces*, Amer. Math.
Monthly 99 (1992) 116-130. -/
def UCPlanar.External.EdgeSplitting {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  ∀ T₁ T₂ : Finset (Sym2 V), ↑T₁ ⊆ G.edgeSet → ↑T₂ ⊆ G.edgeSet → Disjoint T₁ T₂ →
    ∀ v : V, (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) →
    ∀ p : UCPlanar.Plane, p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑(T₁ ∪ T₂)) →
      p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑T₁) ∨
        p ∈ UCPlanar.Support.insideOf (E.edgesTrace ↑T₂)
-- FROZEN-STATEMENT-END

namespace UCPlanar.Support

/-- The cited input, in the vocabulary the boundary cycle theorem uses. -/
theorem edgeSplitting_of_external {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (h : UCPlanar.External.EdgeSplitting E) :
    E.EdgeSplitting := h

end UCPlanar.Support
