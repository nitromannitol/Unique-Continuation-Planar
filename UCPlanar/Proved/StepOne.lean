import UCPlanar.Support.StepOne
import UCPlanar.Support.ZeroVolume

/-!
# Step 1 of the proof of Theorem 1.3

Step 1 of the proof of `theorem:zero-case` (`ucplanar.tex:270-278`) reduces to the case where the
dual multigraph is a graph. It rests on two facts about harmonic functions on the periodic
network `G`, proved here for arbitrary positive conductances:

* a finite set `K` all of whose outer edges end at one vertex `t` (the finite side of a bridge,
  or a finite piece of a two-edge cut whose two outside endpoints coincide) carries a harmonic
  function only as a constant, equal to its value at `t`; deleting `K` keeps the function
  harmonic on the rest of the graph;
* a finite set `K` all of whose outer edges end at `x₁` or at `x₂ ≠ x₁` may be replaced by a
  single edge from `x₁` to `x₂` whose conductance is the effective conductance of `K` together
  with its outer edges: the current entering `K` at `x₁` is `C_eff (f x₂ - f x₁)` for every
  function harmonic on `K`, and a function harmonic on `G` stays harmonic on the reduced
  network. When `K` is joined to `x₁` and `x₂` through a walk inside `K` the effective
  conductance is positive, so the reduced weights are again conductances.

The reduced network is `UCPlanar.Support.cutGraph` on the vertices outside `K`, with the
conductance `UCPlanar.Support.cutCond`; the effective conductance is
`UCPlanar.Support.effCond`. The proof of Theorem 1.3 in `UCPlanar.Proved.zeroCase` does not pass
through the reduced graph: Step 3 is carried out on the periodic plane graph itself.
-/

namespace UCPlanar.Proved

open LatticeProb.Network UCPlanar.Support

/-- **Step 1 of the proof of Theorem 1.3, a finite piece attached at one vertex.** On a periodic
plane graph with positive conductances, if every edge leaving the finite set `K` ends at the
vertex `t`, a function harmonic on `K` is constant on `K`, equal to its value at `t`; deleting `K`
leaves a network whose weights are conductances, and on which the function stays harmonic
wherever it was harmonic before. -/
theorem stepOne_cutVertex {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) (c : V → V → ℝ)
    (hc : IsCond P.graph c) (K : Finset V) (t : V) (ht : t ∉ K)
    (hcut : ∀ x ∈ K, ∀ y, P.graph.Adj x y → y ∉ K → y = t)
    (f : V → ℝ) (hf : HarmonicOn P.graph c f K) :
    (∀ x ∈ K, f x = f t) ∧ IsCond (cutGraph P.graph K t t) (cutCond c K t t 0) ∧
      ∀ S : Set V, HarmonicOn P.graph c f S →
        HarmonicOn (cutGraph P.graph K t t) (cutCond c K t t 0) (fun v => f v.1)
          {u | u.1 ∈ S} := by
  have hf' : ∀ x ∈ K, netLaplacian P.graph c f x = 0 := fun x hx => hf x hx
  refine ⟨eq_of_harmonicOn_of_cutVertex P.connected hc K ht hcut hf',
    isCond_cutCond hc K le_rfl (fun h => absurd rfl h), fun S hS u hu => ?_⟩
  rw [netLaplacian_cutGraph_of_cutVertex P.connected hc K ht hcut hf' u]
  exact hS u.1 hu

/-- **Step 1 of the proof of Theorem 1.3, a finite piece with two exits.** On a periodic plane
graph with positive conductances, let every edge leaving the finite set `K` end at `x₁` or at
`x₂ ≠ x₁`, and let the edges `x₁ a₁` and `a₂ x₂` and a walk inside `K` from `a₁` to `a₂` join
`x₁` to `x₂` through `K`. Then the effective conductance `C_eff` of `K` with its outer edges
between `x₁` and `x₂` is positive; the network in which `K` is replaced by an edge from `x₁` to
`x₂` of conductance `C_eff` has conductances as weights; and for every function harmonic on `K`
the currents entering `K` at `x₁` and `x₂` are `C_eff (f x₂ - f x₁)` and `C_eff (f x₁ - f x₂)`,
and the function stays harmonic on the reduced network wherever it was harmonic on `G`. -/
theorem stepOne_twoExits {V : Type*} (P : UCPlanar.PeriodicPlaneGraph V) (c : V → V → ℝ)
    (hc : IsCond P.graph c) (K : Finset V) (x₁ x₂ : V) (h₁ : x₁ ∉ K) (h₂ : x₂ ∉ K)
    (hne : x₁ ≠ x₂) (hcut : ∀ x ∈ K, ∀ y, P.graph.Adj x y → y ∉ K → y = x₁ ∨ y = x₂)
    (a₁ a₂ : V) (hxa₁ : P.graph.Adj x₁ a₁) (hxa₂ : P.graph.Adj a₂ x₂)
    (p : P.graph.Walk a₁ a₂) (hp : ∀ z ∈ p.support, z ∈ K) :
    0 < effCond P.graph c K x₁ x₂ ∧
      IsCond (cutGraph P.graph K x₁ x₂) (cutCond c K x₁ x₂ (effCond P.graph c K x₁ x₂)) ∧
      ∀ f : V → ℝ, HarmonicOn P.graph c f K →
        (inflow c K f x₁ = effCond P.graph c K x₁ x₂ * (f x₂ - f x₁) ∧
          inflow c K f x₂ = effCond P.graph c K x₁ x₂ * (f x₁ - f x₂)) ∧
        ∀ S : Set V, HarmonicOn P.graph c f S →
          HarmonicOn (cutGraph P.graph K x₁ x₂) (cutCond c K x₁ x₂ (effCond P.graph c K x₁ x₂))
            (fun v => f v.1) {u | u.1 ∈ S} := by
  haveI : Infinite V := infinite_of_periodic P.toPeriodicGraph
  have hpos : 0 < effCond P.graph c K x₁ x₂ :=
    effCond_pos P.connected hc K h₁ h₂ hne (hp a₁ p.start_mem_support) hxa₁ hxa₂ p hp
  refine ⟨hpos, isCond_cutCond hc K hpos.le (fun _ _ => hpos), fun f hf => ?_⟩
  have hf' : ∀ x ∈ K, netLaplacian P.graph c f x = 0 := fun x hx => hf x hx
  refine ⟨inflow_eq_effCond P.connected hc K h₁ h₂ hne hcut hf', fun S hS u hu => ?_⟩
  rw [netLaplacian_cutGraph_of_twoExits P.connected hc K h₁ h₂ hne hcut hf' u]
  exact hS u.1 hu

end UCPlanar.Proved
