/- A reduction of X-003 (`UCPlanar.External.Unicoherence`) to a clean classical statement about
`Schoenflies.Plane`, mirroring `janiszewskiPoint_of_euclidean` (`TopoSeparate.lean`): the
classical statement is transported along `planeHomeo` using `Homeomorph.image_connectedComponentIn`
and `Homeomorph.image_frontier`, exactly as that lemma transports Janiszewski's theorem.

Unlike Janiszewski's theorem, `Unicoherence` is stated for the *drawing* of a connected graph,
not for an arbitrary closed set, so half the work here is combinatorial rather than classical:
`isPreconnected_trace_of_connected` shows the drawing itself is a preconnected set, using
only `G.Connected` and the existing walk-trace machinery (`isPreconnected_walkTrace`), no
topological input at all.

The reduction also needs the drawing to be a *closed* set.  This holds for a periodic plane
graph (`UCPlanar.Support.isClosed_trace`, `TopoProper.lean`), which is the only case
`Unicoherence` is ever consumed at, but is not automatic for an arbitrary `PlaneEmbedding` of an
arbitrary (possibly infinite, non-locally-finite) graph, so it is carried as an explicit
hypothesis `hclosed` here rather than re-derived. -/
import UCPlanar.Support.TopoTransport
import UCPlanar.Support.PlanarInterior
import UCPlanar.Support.TopoFace
import UCPlanar.External.Unicoherence
import Mathlib

open Set

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **The drawing of a connected graph is preconnected.**  Fix a base vertex `x₀` and, for every
vertex `v`, a walk `x₀ ⟶ v` (using `G.Connected`); for every edge `x ⟶ y`, extend a walk
`x₀ ⟶ x` by that edge.  Each such walk's drawn trace is preconnected
(`isPreconnected_walkTrace`) and contains `E.pos x₀`, and together their drawn traces cover the
whole drawing, so `isPreconnected_iUnion` glues them into one preconnected set. -/
theorem isPreconnected_trace_of_connected (E : UCPlanar.PlaneEmbedding G)
    (hG : G.Connected) : IsPreconnected E.trace := by
  obtain ⟨x₀⟩ := hG.nonempty
  classical
  let walkTo : ∀ v : V, G.Walk x₀ v := fun v => (hG x₀ v).some
  let κ : Type _ := V ⊕ {e : V × V // G.Adj e.1 e.2}
  let t : κ → Set UCPlanar.Plane := fun k =>
    match k with
    | Sum.inl v => E.walkTrace (walkTo v)
    | Sum.inr e => E.walkTrace ((walkTo e.1.1).concat e.2)
  have hpre : ∀ k, IsPreconnected (t k) := by
    rintro (v | e)
    · exact E.isPreconnected_walkTrace (walkTo v)
    · exact E.isPreconnected_walkTrace ((walkTo e.1.1).concat e.2)
  have hmem : ∀ k, E.pos x₀ ∈ t k := by
    rintro (v | e)
    · exact (E.pos_mem_walkTrace_iff (walkTo v) x₀).mpr (walkTo v).start_mem_support
    · exact (E.pos_mem_walkTrace_iff ((walkTo e.1.1).concat e.2) x₀).mpr
        ((walkTo e.1.1).concat e.2).start_mem_support
  have hinter : (⋂ k, t k).Nonempty := ⟨E.pos x₀, Set.mem_iInter.mpr hmem⟩
  have hUnion : IsPreconnected (⋃ k, t k) := isPreconnected_iUnion hinter hpre
  have heq : E.trace = ⋃ k, t k := by
    apply Set.Subset.antisymm
    · rintro q (hq | ⟨x, y, h, hq⟩)
      · obtain ⟨v, rfl⟩ := hq
        exact Set.mem_iUnion.mpr ⟨Sum.inl v,
          (E.pos_mem_walkTrace_iff (walkTo v) v).mpr (walkTo v).end_mem_support⟩
      · refine Set.mem_iUnion.mpr ⟨Sum.inr ⟨(x, y), h⟩, ?_⟩
        show q ∈ E.walkTrace ((walkTo x).concat h)
        rw [SimpleGraph.Walk.concat_eq_append, E.walkTrace_append]
        exact Or.inr (Or.inl hq)
    · rintro q hq
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hq
      rcases k with v | e
      · exact walkTrace_subset_trace E (walkTo v) hk
      · exact walkTrace_subset_trace E ((walkTo e.1.1).concat e.2) hk
  rw [heq]
  exact hUnion

/-- **Unicoherence of the plane, in the form the face frontier needs.**  For a closed connected
set of the plane, the frontier of every bounded connected component of its complement is
connected.  This is the unicoherence of the sphere in the exact per-component form Newman's
development gives it (Newman, *Elements of the Topology of Plane Sets of Points*, Chapter VI;
Mohar and Thomassen, *Graphs on Surfaces*, Chapter 2). -/
def PlaneUnicoherence : Prop :=
  ∀ K : Set Schoenflies.Plane, IsClosed K → IsPreconnected K →
    ∀ p : Schoenflies.Plane, p ∉ K → Bornology.IsBounded (connectedComponentIn Kᶜ p) →
      IsPreconnected (frontier (connectedComponentIn Kᶜ p))

/-- **Unicoherence transports from the Euclidean plane of the Jordan curve development to the
coordinate plane**, for a plane embedding whose drawing is closed.  This is the reduction of
X-003 to a single classical statement, exactly as `janiszewskiPoint_of_euclidean` reduces X-002's
sibling `JaniszewskiPoint`. -/
theorem unicoherence_of_euclidean (h : PlaneUnicoherence) (E : UCPlanar.PlaneEmbedding G)
    (hclosed : IsClosed E.trace) : UCPlanar.External.Unicoherence E := by
  intro hG F hF hFbounded
  obtain ⟨p, hp, rfl⟩ := hF
  set Φ := UCPlanar.Support.planeHomeo
  set K : Set Schoenflies.Plane := Φ '' E.trace with hKdef
  have hcompl : Φ '' E.traceᶜ = Kᶜ := Φ.toEquiv.image_compl E.trace
  have hKclosed : IsClosed K := Φ.isClosedMap E.trace hclosed
  have hKconn : IsPreconnected K :=
    (isPreconnected_trace_of_connected E hG).image Φ Φ.continuous.continuousOn
  have hpK : Φ p ∉ K := by
    rw [hKdef]
    rintro ⟨y, hy, hxy⟩
    exact hp (Φ.injective hxy ▸ hy)
  have hcc : Φ '' connectedComponentIn E.traceᶜ p = connectedComponentIn Kᶜ (Φ p) := by
    have hc := Φ.image_connectedComponentIn (s := E.traceᶜ) hp
    rwa [hcompl] at hc
  have hbdd : Bornology.IsBounded (connectedComponentIn Kᶜ (Φ p)) := by
    rw [← hcc]
    exact (isBounded_image_homeo Φ _).mpr hFbounded
  have hres := h K hKclosed hKconn (Φ p) hpK hbdd
  rw [← hcc, ← Φ.image_frontier] at hres
  exact Φ.isPreconnected_image.mp hres

end UCPlanar.Support
