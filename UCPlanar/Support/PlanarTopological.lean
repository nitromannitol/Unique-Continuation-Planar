/- Quantitative continuation on a cycle from alternating-crosscut intersection. -/
import UCPlanar.Support.Periodic
import UCPlanar.Support.PlanarReduction
import UCPlanar.Support.PlanarMetric

open scoped Classical

/-- The density bound follows from alternating-crosscut intersection in the closed domain. -/
theorem UCPlanar.Support.topological_of_crosscuts {V : Type*} :
    ∀ d L : ℕ, ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ Q : UCPlanar.PeriodicPlaneGraph V,
      (∀ x, Q.graph.degree x ≤ d) → Q.embedding.FaceBound L →
      ∀ (o : V) (γ : Q.graph.Walk o o), γ.IsCycle →
      (∀ i j k l : ℕ, i < j → j < k → k < l → l < γ.length →
        ∀ p : Q.graph.Walk (γ.getVert i) (γ.getVert k),
        ∀ q : Q.graph.Walk (γ.getVert j) (γ.getVert l),
        Q.embedding.walkTrace p ⊆ Q.embedding.closedCycleDomain γ →
        Q.embedding.walkTrace q ⊆ Q.embedding.closedCycleDomain γ →
        ∃ v ∈ p.support, v ∈ q.support) →
      ∀ (Z : Finset V) (P M : Set V),
        Disjoint (Z : Set V) P → Disjoint (Z : Set V) M → Disjoint P M →
        Z ⊆ γ.support.toFinset →
        P ⊆ Q.embedding.cycleRegion γ → M ⊆ Q.embedding.cycleRegion γ →
        (∀ z ∈ Z, Q.embedding.FacePathToSigns P M z) →
        UCPlanar.ComponentsMeetBoundary Q.graph P ((γ.support.toFinset : Set V) \ Z) →
        UCPlanar.ComponentsMeetBoundary Q.graph M ((γ.support.toFinset : Set V) \ Z) →
        (Z.card : ℝ) ≤ α * γ.support.toFinset.card
:= by
  intro d L
  let K := (2 * L + 1) * (d + 1) ^ (2 * L)
  let C := (L + 1) * (d + 1) ^ L
  have hKC : 0 < K + C := by dsimp [K, C]; positivity
  have hKC' : 0 < ((K + C : ℕ) : ℝ) := by exact_mod_cast hKC
  let α : ℝ := 2 * ((K + C : ℕ) : ℝ) / (2 * ((K + C : ℕ) : ℝ) + 1)
  refine ⟨α, by dsimp [α]; positivity, ?_, ?_⟩
  · exact (div_lt_one (by positivity)).mpr (by linarith)
  · intro Q hd hL o γ hγ hcross Z P M hZP hZM hPM hZS hP hM hface hBP hBM
    classical
    let S := γ.support.toFinset
    let B := S \ Z
    let A := Z.filter (fun z => ∃ b ∈ B, Q.graph.dist z b ≤ L)
    have hA : A.card ≤ B.card * C :=
      UCPlanar.Support.card_near_boundary_le Q.connected Z B d L hd
    obtain ⟨T, hTW, hsep, hpack⟩ := UCPlanar.Support.exists_metric_separated
      Q.connected (Z \ A) d L hd
    have hTZ : T ⊆ Z := fun z hz => (Finset.mem_sdiff.mp (hTW hz)).1
    have hremote : ∀ z : T, ∃ v ∈ Z, ∃ w p m, ∃ β : Q.graph.Walk v w,
        β.IsPath ∧ β.length < L ∧
        (∀ t ∈ β.support, t ∉ P ∪ M ∧ Q.graph.dist z.val t ≤ L) ∧
        p ∈ P ∧ m ∈ M ∧ Q.graph.dist z.val p ≤ L ∧ Q.graph.dist z.val m ≤ L ∧
        ∃ hwp : Q.graph.Adj w p, ∃ hwm : Q.graph.Adj w m,
          Q.embedding.walkTrace (β.concat hwp) ⊆ Q.embedding.closedCycleDomain γ ∧
          Q.embedding.walkTrace (β.concat hwm) ⊆ Q.embedding.closedCycleDomain γ := by
      intro z
      apply Q.embedding.remote_facePathToSigns_interior γ Z P M L hL (hTZ z.property)
        hZS hZP hZM hP hM (hface z.val (hTZ z.property))
      intro b hb
      by_contra hn
      apply (Finset.mem_sdiff.mp (hTW z.property)).2
      exact Finset.mem_filter.mpr ⟨hTZ z.property, ⟨b, hb, Nat.le_of_not_gt hn⟩⟩
    choose v hvZ w p m β hβ hlen ha hp hm hdp hdm hwp hwm htp htm using hremote
    have hvRad (z : T) : Q.graph.dist z.val (v z) ≤ L :=
      (ha z (v z) (β z).start_mem_support).2
    have hvInj : Function.Injective v := by
      intro z t he
      by_contra hn
      have hs := hsep z.val z.property t.val t.property (fun he => hn (Subtype.ext he))
      have hz := hvRad z
      have ht := hvRad t
      have htri := Q.connected.dist_triangle (u := z.val) (v := v z) (w := t.val)
      rw [he, Q.graph.dist_comm (u := v t) (v := t.val)] at htri
      rw [he] at hz
      omega
    obtain ⟨e, k, hk, hkv⟩ := UCPlanar.Support.exists_ordered_cycle_contacts γ hγ
      (Finset.univ : Finset T) v (fun _ _ _ _ he => hvInj he)
      (fun z _ => List.mem_toFinset.mp (hZS (hvZ z)))
    let u : Fin (Finset.univ : Finset T).card → T := fun i => (e i).val
    have hu : Function.Injective u := fun _ _ he => e.injective (Subtype.ext he)
    let D := Q.embedding.closedCycleDomain γ
    obtain ⟨H, hHG, hH⟩ := Q.embedding.exists_graph_with_edges_in D
    have hBPγ : UCPlanar.ComponentsMeetBoundary Q.graph P {v | v ∈ γ.support} := by
      intro x
      obtain ⟨y, hy, hr⟩ := hBP x
      exact ⟨y, List.mem_toFinset.mp hy.1, hr⟩
    have hBMγ : UCPlanar.ComponentsMeetBoundary Q.graph M {v | v ∈ γ.support} := by
      intro x
      obtain ⟨y, hy, hr⟩ := hBM x
      exact ⟨y, List.mem_toFinset.mp hy.1, hr⟩
    have hBP' : UCPlanar.ComponentsMeetBoundary H P (B : Set V) := by
      intro x
      obtain ⟨y, hy, hr⟩ := Q.embedding.componentsMeetBoundary_in_domain γ H hHG hH P hP hBPγ x
      exact ⟨y, Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hy,
        fun hz => Set.disjoint_left.mp hZP hz y.property⟩, hr⟩
    have hBM' : UCPlanar.ComponentsMeetBoundary H M (B : Set V) := by
      intro x
      obtain ⟨y, hy, hr⟩ := Q.embedding.componentsMeetBoundary_in_domain γ H hHG hH M hM hBMγ x
      exact ⟨y, Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hy,
        fun hz => Set.disjoint_left.mp hZM hz y.property⟩, hr⟩
    have hcopy {x y x' y' : V} (q : Q.graph.Walk x y) (hx : x = x') (hy : y = y') :
        Q.embedding.walkTrace (q.copy hx hy) = Q.embedding.walkTrace q := by
      subst x'; subst y'; rfl
    have hcharge' : (Finset.univ : Finset T).card ≤ 2 * B.card := by
      refine Q.embedding.boundary_charge_of_alternating_paths D H hHG hH P M B hPM hBP' hBM'
        (fun i => v (u i)) (fun i => w (u i)) (fun i => p (u i)) (fun i => m (u i))
        (fun i => β (u i)) (fun i => hp (u i)) (fun i => hm (u i))
        (fun i => hwp (u i)) (fun i => hwm (u i))
        (fun i t ht => (ha (u i) t ht).1) ?_
        (fun i => htp (u i)) (fun i => htm (u i)) ?_
      · intro i j hij t hti htj
        have hs := hsep (u i).val (u i).property (u j).val (u j).property
          (fun he => hij (hu (Subtype.ext he)))
        have hi := (ha (u i) t hti).2
        have hj := (ha (u j) t htj).2
        have ht := Q.connected.dist_triangle (u := (u i).val) (v := t) (w := (u j).val)
        rw [Q.graph.dist_comm (u := t) (v := (u j).val)] at ht
        omega
      · intro a b c d hab hbc hcd ξ ζ hξ hζ
        let ξ' := ξ.copy (hkv a).2.symm (hkv c).2.symm
        let ζ' := ζ.copy (hkv b).2.symm (hkv d).2.symm
        have hξ' : Q.embedding.walkTrace ξ' ⊆ Q.embedding.closedCycleDomain γ := by
          simpa only [ξ', hcopy] using hξ
        have hζ' : Q.embedding.walkTrace ζ' ⊆ Q.embedding.closedCycleDomain γ := by
          simpa only [ζ', hcopy] using hζ
        obtain ⟨t, htξ, htζ⟩ := hcross (k a) (k b) (k c) (k d)
          (hk hab) (hk hbc) (hk hcd) (hkv d).1 ξ' ζ' hξ' hζ'
        exact ⟨t, by simpa only [ξ', SimpleGraph.Walk.support_copy] using htξ,
          by simpa only [ζ', SimpleGraph.Walk.support_copy] using htζ⟩
    have hcharge : T.card ≤ 2 * (S \ Z).card := by simpa only [Finset.card_univ,
      Fintype.card_coe] using hcharge'
    exact (UCPlanar.Support.density_bound_of_discard_packing S Z A T hZS K C hKC
      hpack hcharge hA).2.2
