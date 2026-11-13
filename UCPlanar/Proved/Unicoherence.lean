import UCPlanar.Vendored.PlaneUnicoherence
import UCPlanar.Support.TopoUnicoherenceReduction
import UCPlanar.Support.TopoProper

/-!
# Unicoherence of the plane

`UCPlanar.Support.PlaneUnicoherence` holds: for a closed preconnected set `K` of the Euclidean
plane, the frontier of every bounded component of the complement of `K` is preconnected.  The
proof transports the unicoherence theorem for closed connected subsets of the coordinate plane
(`UCPlanar.Vendored.isPreconnected_frontier_connectedComponentIn_compl`, copied from
Lattice-Probability) along `UCPlanar.Support.planeHomeo`.  The boundedness of the component forces
`K` to be nonempty, hence connected.

Consequently the cited statement `UCPlanar.External.Unicoherence` holds for the drawing of every
periodic plane graph, whose trace is closed (`UCPlanar.Support.isClosed_trace`).
-/

open Set

namespace UCPlanar.Support

/-- **Unicoherence of the plane.**  For a closed preconnected set of the Euclidean plane, the
frontier of every bounded component of its complement is preconnected. -/
theorem planeUnicoherence_holds : PlaneUnicoherence := by
  intro K hK hKp p hp hb
  set e := planeHomeo
  have hne : K.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    rw [compl_empty, connectedComponentIn_univ,
      PreconnectedSpace.connectedComponent_eq_univ] at hb
    exact NormedSpace.unbounded_univ ℝ Schoenflies.Plane hb
  have hpre : e ⁻¹' K = e.symm '' K := (congrFun e.image_symm K).symm
  have hA : IsClosed (e ⁻¹' K) := hK.preimage e.continuous
  have hAc : IsConnected (e ⁻¹' K) := by
    rw [hpre]
    exact ⟨hne.image _, hKp.image _ e.symm.continuous.continuousOn⟩
  have hq : e.symm p ∉ e ⁻¹' K := by
    simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hp
  have hfr := UCPlanar.Vendored.isPreconnected_frontier_connectedComponentIn_compl hA hAc hq
  have himage : e '' connectedComponentIn (e ⁻¹' K)ᶜ (e.symm p) = connectedComponentIn Kᶜ p := by
    rw [e.image_connectedComponentIn (show e.symm p ∈ (e ⁻¹' K)ᶜ from hq),
      image_compl_eq e.bijective, e.image_preimage, e.apply_symm_apply]
  rw [← himage, ← e.image_frontier]
  exact hfr.image e e.continuous.continuousOn

/-- **Unicoherence for the drawing of a periodic plane graph.**  The cited statement
`UCPlanar.External.Unicoherence` holds for the embedding of every periodic plane graph. -/
theorem unicoherence_holds {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) :
    UCPlanar.External.Unicoherence P.embedding :=
  unicoherence_of_euclidean planeUnicoherence_holds P.embedding (isClosed_trace P)

end UCPlanar.Support
