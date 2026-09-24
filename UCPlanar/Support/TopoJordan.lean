/- The Jordan domain of a drawn cycle, and the face a point off the drawing lies in. -/
import UCPlanar.Support.TopoProper

open Set

open scoped Classical

namespace UCPlanar.Support

/-- Every point off the drawing lies in a face. -/
theorem exists_isFace_of_notMem_trace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {z : UCPlanar.Plane} (hz : z ∉ E.trace) :
    ∃ F, E.IsFace F ∧ z ∈ F :=
  ⟨connectedComponentIn E.traceᶜ z, ⟨z, hz, rfl⟩, mem_connectedComponentIn hz⟩

/-- A drawn cycle encloses a nonempty region of the plane. -/
theorem inside_topoTrace_cycle_nonempty {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) (hγ : γ.IsCycle) :
    (Schoenflies.inside (topoTrace E γ)).Nonempty :=
  (isSeparating_topoTrace_cycle E γ hγ).isConnected_inside.nonempty

/-- The region a Jordan curve encloses is bounded. -/
theorem isBounded_inside_of_isSeparating {C : Set Schoenflies.Plane}
    (hC : Schoenflies.IsSeparating C) : Bornology.IsBounded (Schoenflies.inside C) := by
  obtain ⟨z, hz⟩ := hC.isConnected_inside.nonempty
  have h1 : Schoenflies.inside C ⊆ connectedComponentIn Cᶜ z :=
    hC.isConnected_inside.isPreconnected.subset_connectedComponentIn hz
      Schoenflies.inside_subset_compl
  exact hz.2.subset h1

/-- The vertex of the drawing at a frontier point of a face is incident to that face. -/
theorem incident_of_pos_mem_frontier {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (F : Set UCPlanar.Plane) (x : V)
    (hx : E.pos x ∈ frontier F) : E.Incident F x := hx

/-- A vertex incident to a face of a periodic plane graph is drawn on the graph. -/
theorem pos_mem_trace_of_incident {V : Type*} (Q : UCPlanar.PeriodicPlaneGraph V)
    {F : Set UCPlanar.Plane} (hF : Q.embedding.IsFace F) {x : V}
    (hx : Q.embedding.Incident F x) : Q.embedding.pos x ∈ Q.embedding.trace :=
  frontier_isFace_subset_trace Q hF hx

end UCPlanar.Support
