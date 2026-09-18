import UCPlanar.Support.TopoFaceWalks

-- FROZEN-STATEMENT-BEGIN
/-- Unicoherence of the sphere, in the form the face walks use.  The sphere is unicoherent, so
for a compact connected set of the plane whose complement has a bounded component the frontier
of that component is connected; applied to the drawing of a connected plane graph together with
the point at infinity, the frontier of every bounded face of the drawing is connected.  Newman,
*Elements of the Topology of Plane Sets of Points*, Chapter VI; Mohar and Thomassen, *Graphs on
Surfaces*, Chapter 2; Thomassen, *The Jordan-Schoenflies theorem and the classification of
surfaces*, Amer. Math. Monthly 99 (1992) 116-130. -/
def UCPlanar.External.Unicoherence {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Prop :=
  G.Connected → ∀ F, E.IsFace F → Bornology.IsBounded F → IsPreconnected (frontier F)
-- FROZEN-STATEMENT-END
