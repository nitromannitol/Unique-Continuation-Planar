import Mathlib
import UCPlanar.MainTheorems
import UCPlanarAudit.Liouville.SolutionBasic

/-!
# Bridge from the `Liouville` vocabulary to the repository

The vocabulary of `UCPlanarAudit/Liouville/Challenge.lean` (copied verbatim into
`UCPlanarAudit/Liouville/SolutionBasic.lean`, which imports only Mathlib; namespace
`UCPlanarAudit`) is a statement-level copy of the repository definitions and of the definitions
it uses from `Lattice-Probability` and the Schoenflies library.  Plain definitions over shared
Mathlib types (`closedBall`, `netLaplacian`, `HarmonicOn`, …) are definitionally equal to their
counterparts.  The structures (`IsCond`, `PlaneEmbedding`, `PeriodicGraph`,
`PeriodicPlaneGraph`) are new inductive types, so this file converts between them field by
field; the recursive `poly` is a new recursive definition, and `poly_eq` proves it equal to
`Schoenflies.poly` by induction.  From these, each cited-result proposition of the vocabulary
(`MoserEstimate`, `EdgeSplitting`, `Unicoherence`) implies the repository's.

It is imported by `UCPlanarAudit/Liouville/Solution.lean` only.  The `Challenge` and
`SolutionBasic` files must stay Mathlib-only: a repository import inside the vocabulary
changes instance elaboration there and breaks the comparator's constant-by-constant closure
check.
-/

namespace UCPlanarAudit.Bridge

/-- The vocabulary's polygonal carrier is the Schoenflies library's. -/
theorem poly_eq : ∀ vs : List EPlane, UCPlanarAudit.poly vs = Schoenflies.poly vs
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
    rw [UCPlanarAudit.poly, Schoenflies.poly_cons_cons, poly_eq (v :: rest)]

theorem isPolygonal_iff (A : Set EPlane) :
    UCPlanarAudit.IsPolygonal A ↔ Schoenflies.IsPolygonal A := by
  simp only [UCPlanarAudit.IsPolygonal, Schoenflies.IsPolygonal, poly_eq]

section Graph

variable {V : Type*}

theorem isCond_iff (G : SimpleGraph V) (c : V → V → ℝ) :
    UCPlanarAudit.IsCond G c ↔ LatticeProb.Network.IsCond G c :=
  ⟨fun h => ⟨h.symm, h.pos, h.zero_of_not_adj⟩, fun h => ⟨h.symm, h.pos, h.zero_of_not_adj⟩⟩

/-- A vocabulary plane embedding as a repository plane embedding. -/
def toPE {G : SimpleGraph V} (E : UCPlanarAudit.PlaneEmbedding G) :
    UCPlanar.PlaneEmbedding G where
  pos := E.pos
  pos_injective := E.pos_injective
  edge := E.edge
  edge_injective := E.edge_injective
  edge_symm := E.edge_symm
  vertex_on_edge := E.vertex_on_edge
  edge_inter := E.edge_inter
  edge_polygonal h := (isPolygonal_iff _).1 (E.edge_polygonal h)

/-- A vocabulary periodic graph as a repository periodic graph. -/
def toPG (P : UCPlanarAudit.PeriodicGraph V) : UCPlanar.PeriodicGraph V where
  graph := P.graph
  locallyFinite := P.locallyFinite
  connected := P.connected
  pos := P.pos
  pos_injective := P.pos_injective
  period := P.period
  shift := P.shift
  shift_zero := P.shift_zero
  shift_add := P.shift_add
  shift_adj := P.shift_adj
  pos_shift := P.pos_shift
  representatives := P.representatives
  covers := P.covers
  finite_squares := P.finite_squares
  finite_balls := P.finite_balls

/-- A vocabulary periodic plane graph as a repository periodic plane graph. -/
def toPPG (P : UCPlanarAudit.PeriodicPlaneGraph V) : UCPlanar.PeriodicPlaneGraph V where
  toPeriodicGraph := toPG P.toPeriodicGraph
  embedding := toPE P.embedding
  embedding_pos := P.embedding_pos
  edge_shift := P.edge_shift
  proper_edges := P.proper_edges
  bounded_faces := P.bounded_faces
  face_diameter := P.face_diameter

theorem edgeSplitting {G : SimpleGraph V} (E : UCPlanarAudit.PlaneEmbedding G)
    (h : UCPlanarAudit.External.EdgeSplitting E) : UCPlanar.External.EdgeSplitting (toPE E) :=
  h

theorem unicoherence {G : SimpleGraph V} (E : UCPlanarAudit.PlaneEmbedding G)
    (h : UCPlanarAudit.External.Unicoherence E) : UCPlanar.External.Unicoherence (toPE E) :=
  h

theorem moserEstimate (P : UCPlanarAudit.PeriodicGraph V) (c : V → V → ℝ)
    (h : UCPlanarAudit.External.MoserEstimate P c) :
    UCPlanar.External.MoserEstimate (toPG P) c :=
  h

end Graph

end UCPlanarAudit.Bridge
