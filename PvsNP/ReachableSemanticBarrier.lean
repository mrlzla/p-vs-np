module

public import PvsNP.FormulaCircuit
public import PvsNP.AffineButterflyBarrier

@[expose] public section

open Filter

namespace PvsNP

section Reachability

/-- `GateUsesWire g u` holds when wire `u` is an input wire to gate `g`. -/
inductive GateUsesWire {w : Nat} : Gate w → Fin w → Prop
  | not (a : Fin w) : GateUsesWire (.not a) a
  | and_left (a b : Fin w) : GateUsesWire (.and a b) a
  | and_right (a b : Fin w) : GateUsesWire (.and a b) b
  | or_left (a b : Fin w) : GateUsesWire (.or a b) a
  | or_right (a b : Fin w) : GateUsesWire (.or a b) b

/-- Directed dependency edge `u → v` in a standard `Circuit`: `u` feeds directly
into the gate computing wire `v`. -/
def Circuit.DirectedEdge : {inputs wires : Nat} → Circuit inputs wires →
    Fin wires → Fin wires → Prop
  | _, _, .inputsOnly, _, _ => False
  | _, _, .snoc prev g, u, v =>
      (∃ u' v', u = u'.castSucc ∧ v = v'.castSucc ∧ prev.DirectedEdge u' v') ∨
      (v = Fin.last _ ∧ ∃ a, u = a.castSucc ∧ GateUsesWire g a)

/-- Directed reachability from wire `u` to wire `v` in a standard `Circuit`. -/
def Circuit.DirectedReach {inputs wires : Nat} (c : Circuit inputs wires)
    (u v : Fin wires) : Prop :=
  Relation.ReflTransGen c.DirectedEdge u v

lemma Circuit.directedEdge_snoc_castSucc {inputs wires : Nat}
    {prev : Circuit inputs wires} {g : Gate wires} {u v : Fin wires}
    (h : prev.DirectedEdge u v) :
    (prev.snoc g).DirectedEdge u.castSucc v.castSucc :=
  Or.inl ⟨u, v, rfl, rfl, h⟩

lemma Circuit.directedEdge_snoc_last {inputs wires : Nat}
    {prev : Circuit inputs wires} {g : Gate wires} {a : Fin wires}
    (h : GateUsesWire g a) :
    (prev.snoc g).DirectedEdge a.castSucc (Fin.last wires) :=
  Or.inr ⟨rfl, a, rfl, h⟩

lemma Circuit.directedReach_snoc_castSucc {inputs wires : Nat}
    {prev : Circuit inputs wires} {g : Gate wires} {u v : Fin wires}
    (h : prev.DirectedReach u v) :
    (prev.snoc g).DirectedReach u.castSucc v.castSucc := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hStep ih => exact ih.tail (Circuit.directedEdge_snoc_castSucc hStep)

lemma Circuit.evalWires_snoc_castSucc {inputs w : Nat}
    (prev : Circuit inputs w) (g : Gate w) (x : Fin inputs → Bool) (u : Fin w) :
    (prev.snoc g).evalWires x u.castSucc = prev.evalWires x u :=
  Fin.snoc_castSucc (α := fun _ => Bool) (g.eval (prev.evalWires x)) (prev.evalWires x) u

lemma Circuit.evalWires_snoc_last {inputs w : Nat}
    (prev : Circuit inputs w) (g : Gate w) (x : Fin inputs → Bool) :
    (prev.snoc g).evalWires x (Fin.last w) = g.eval (prev.evalWires x) :=
  Fin.snoc_last (α := fun _ => Bool) (g.eval (prev.evalWires x)) (prev.evalWires x)

lemma Circuit.wires_eq_inputs_add_gateCount :
    ∀ {inputs wires : Nat} (c : Circuit inputs wires), wires = inputs + c.gateCount
  | _, _, .inputsOnly => by simp [Circuit.gateCount]
  | _, _, .snoc prev _ => by
      simp [Circuit.gateCount, prev.wires_eq_inputs_add_gateCount, Nat.add_assoc]

lemma Circuit.directedEdge_to_circuitEdge :
    ∀ {inputs wires : Nat} {c : Circuit inputs wires} {u v : Fin wires},
      c.DirectedEdge u v → CircuitEdge c u v
  | _, _, .inputsOnly, _, _, h => by
      unfold Circuit.DirectedEdge at h
      exact False.elim h
  | _, _, .snoc _ _, u, v, h => by
      rcases h with ⟨u', v', hu, hv, hPrev⟩ | ⟨hv, a, hu, ha⟩
      · subst hu hv
        exact CircuitEdge.cast _ _ (Circuit.directedEdge_to_circuitEdge hPrev)
      · subst hu hv
        cases ha with
        | not => exact CircuitEdge.not_in _ _
        | and_left => exact CircuitEdge.and_left _ _ _
        | and_right => exact CircuitEdge.and_right _ _ _
        | or_left => exact CircuitEdge.or_left _ _ _
        | or_right => exact CircuitEdge.or_right _ _ _

lemma CircuitEdge.to_directedEdge_or {inputs wires : Nat} {c : Circuit inputs wires}
    {u v : Fin wires} (h : CircuitEdge c u v) :
    c.DirectedEdge u v ∨ c.DirectedEdge v u := by
  induction h with
  | cast _ _ _ ih =>
      rcases ih with h1 | h2
      · exact Or.inl (Circuit.directedEdge_snoc_castSucc h1)
      · exact Or.inr (Circuit.directedEdge_snoc_castSucc h2)
  | not_in _ a => exact Or.inl (Circuit.directedEdge_snoc_last (GateUsesWire.not a))
  | not_out _ a => exact Or.inr (Circuit.directedEdge_snoc_last (GateUsesWire.not a))
  | and_left _ a b => exact Or.inl (Circuit.directedEdge_snoc_last (GateUsesWire.and_left a b))
  | and_right _ a b => exact Or.inl (Circuit.directedEdge_snoc_last (GateUsesWire.and_right a b))
  | and_out_left _ a b => exact Or.inr (Circuit.directedEdge_snoc_last (GateUsesWire.and_left a b))
  | and_out_right _ a b => exact Or.inr (Circuit.directedEdge_snoc_last (GateUsesWire.and_right a b))
  | or_left _ a b => exact Or.inl (Circuit.directedEdge_snoc_last (GateUsesWire.or_left a b))
  | or_right _ a b => exact Or.inl (Circuit.directedEdge_snoc_last (GateUsesWire.or_right a b))
  | or_out_left _ a b => exact Or.inr (Circuit.directedEdge_snoc_last (GateUsesWire.or_left a b))
  | or_out_right _ a b => exact Or.inr (Circuit.directedEdge_snoc_last (GateUsesWire.or_right a b))

/-- `HybridGateUsesWire g u` holds when wire `u` is an input wire to hybrid gate `g`. -/
inductive HybridGateUsesWire {w : Nat} : HybridGate w → Fin w → Prop
  | not (a : Fin w) : HybridGateUsesWire (.not a) a
  | and_left (a b : Fin w) : HybridGateUsesWire (.and a b) a
  | and_right (a b : Fin w) : HybridGateUsesWire (.and a b) b
  | or_left (a b : Fin w) : HybridGateUsesWire (.or a b) a
  | or_right (a b : Fin w) : HybridGateUsesWire (.or a b) b
  | xor_left (a b : Fin w) : HybridGateUsesWire (.xor a b) a
  | xor_right (a b : Fin w) : HybridGateUsesWire (.xor a b) b

/-- Directed dependency edge `u → v` in a `HybridCircuit`. -/
def HybridCircuit.DirectedEdge : {inputs wires : Nat} → HybridCircuit inputs wires →
    Fin wires → Fin wires → Prop
  | _, _, .inputsOnly, _, _ => False
  | _, _, .snoc prev g, u, v =>
      (∃ u' v', u = u'.castSucc ∧ v = v'.castSucc ∧ prev.DirectedEdge u' v') ∨
      (v = Fin.last _ ∧ ∃ a, u = a.castSucc ∧ HybridGateUsesWire g a)

/-- Directed reachability from wire `u` to wire `v` in a `HybridCircuit`. -/
def HybridCircuit.DirectedReach {inputs wires : Nat} (c : HybridCircuit inputs wires)
    (u v : Fin wires) : Prop :=
  Relation.ReflTransGen c.DirectedEdge u v

lemma HybridCircuit.directedEdge_snoc_castSucc {inputs wires : Nat}
    {prev : HybridCircuit inputs wires} {g : HybridGate wires} {u v : Fin wires}
    (h : prev.DirectedEdge u v) :
    (prev.snoc g).DirectedEdge u.castSucc v.castSucc :=
  Or.inl ⟨u, v, rfl, rfl, h⟩

lemma HybridCircuit.directedEdge_snoc_last {inputs wires : Nat}
    {prev : HybridCircuit inputs wires} {g : HybridGate wires} {a : Fin wires}
    (h : HybridGateUsesWire g a) :
    (prev.snoc g).DirectedEdge a.castSucc (Fin.last wires) :=
  Or.inr ⟨rfl, a, rfl, h⟩

lemma HybridCircuit.directedReach_snoc_castSucc {inputs wires : Nat}
    {prev : HybridCircuit inputs wires} {g : HybridGate wires} {u v : Fin wires}
    (h : prev.DirectedReach u v) :
    (prev.snoc g).DirectedReach u.castSucc v.castSucc := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hStep ih => exact ih.tail (HybridCircuit.directedEdge_snoc_castSucc hStep)

lemma HybridCircuit.evalWires_snoc_castSucc {inputs w : Nat}
    (prev : HybridCircuit inputs w) (g : HybridGate w) (x : Fin inputs → Bool) (u : Fin w) :
    (prev.snoc g).evalWires x u.castSucc = prev.evalWires x u :=
  Fin.snoc_castSucc (α := fun _ => Bool) (g.eval (prev.evalWires x)) (prev.evalWires x) u

lemma HybridCircuit.evalWires_snoc_last {inputs w : Nat}
    (prev : HybridCircuit inputs w) (g : HybridGate w) (x : Fin inputs → Bool) :
    (prev.snoc g).evalWires x (Fin.last w) = g.eval (prev.evalWires x) :=
  Fin.snoc_last (α := fun _ => Bool) (g.eval (prev.evalWires x)) (prev.evalWires x)

lemma HybridCircuit.directedEdge_to_hybridCircuitEdge :
    ∀ {inputs wires : Nat} {c : HybridCircuit inputs wires} {u v : Fin wires},
      c.DirectedEdge u v → HybridCircuitEdge c u v
  | _, _, .inputsOnly, _, _, h => by
      unfold HybridCircuit.DirectedEdge at h
      exact False.elim h
  | _, _, .snoc _ _, u, v, h => by
      rcases h with ⟨u', v', hu, hv, hPrev⟩ | ⟨hv, a, hu, ha⟩
      · subst hu hv
        exact HybridCircuitEdge.cast _ _ (HybridCircuit.directedEdge_to_hybridCircuitEdge hPrev)
      · subst hu hv
        cases ha with
        | not => exact HybridCircuitEdge.not_in _ _
        | and_left => exact HybridCircuitEdge.and_left _ _ _
        | and_right => exact HybridCircuitEdge.and_right _ _ _
        | or_left => exact HybridCircuitEdge.or_left _ _ _
        | or_right => exact HybridCircuitEdge.or_right _ _ _
        | xor_left => exact HybridCircuitEdge.xor_left _ _ _
        | xor_right => exact HybridCircuitEdge.xor_right _ _ _

end Reachability

section SubgraphMonotonicity

/-- Restrict a decomposition tree along an injective wire embedding `f : α → β`. -/
noncomputable def DecompTree.restrict {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) : DecompTree β → DecompTree α
  | .node bag cs => .node (bag.preimage f hf.injOn) (restrictList cs)
where
  restrictList : List (DecompTree β) → List (DecompTree α)
    | [] => []
    | c :: cs => DecompTree.restrict f hf c :: restrictList cs

lemma DecompTree.mem_subtreeWires_restrict {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (u : α) :
    ∀ t : DecompTree β, u ∈ (t.restrict f hf).subtreeWires ↔ f u ∈ t.subtreeWires
  | .node bag cs => by
      simp only [DecompTree.restrict, DecompTree.subtreeWires, Finset.mem_union,
        Finset.mem_preimage]
      constructor
      · rintro (hBag | hCs)
        · exact Or.inl hBag
        · exact Or.inr ((mem_listWires_restrictList cs).mp hCs)
      · rintro (hBag | hCs)
        · exact Or.inl hBag
        · exact Or.inr ((mem_listWires_restrictList cs).mpr hCs)
where
  mem_listWires_restrictList :
      ∀ cs : List (DecompTree β),
        u ∈ DecompTree.listWires (DecompTree.restrict.restrictList f hf cs) ↔
          f u ∈ DecompTree.listWires cs
    | [] => by simp [DecompTree.restrict.restrictList, DecompTree.listWires]
    | c :: cs => by
        simp only [DecompTree.restrict.restrictList, DecompTree.listWires, Finset.mem_union]
        rw [DecompTree.mem_subtreeWires_restrict f hf u c, mem_listWires_restrictList cs]

lemma DecompTree.containsPair_restrict {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (u v : α) :
    ∀ t : DecompTree β,
      DecompTree.ContainsPair (f u) (f v) t →
        DecompTree.ContainsPair u v (t.restrict f hf)
  | .node bag cs, h => by
      simp only [DecompTree.restrict, DecompTree.ContainsPair, Finset.mem_preimage] at h ⊢
      rcases h with ⟨hu, hv⟩ | hList
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr (containsPair_restrictList cs hList)
where
  containsPair_restrictList :
      ∀ cs : List (DecompTree β),
        DecompTree.ListContainsPair (f u) (f v) cs →
          DecompTree.ListContainsPair u v (DecompTree.restrict.restrictList f hf cs)
    | [], h => False.elim h
    | c :: cs, h => by
        simp only [DecompTree.restrict.restrictList, DecompTree.ListContainsPair] at h ⊢
        rcases h with hC | hCs
        · exact Or.inl (DecompTree.containsPair_restrict f hf u v c hC)
        · exact Or.inr (containsPair_restrictList cs hCs)

lemma DecompTree.maxBagCard_restrict_le {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    ∀ t : DecompTree β, (t.restrict f hf).maxBagCard ≤ t.maxBagCard
  | .node bag cs => by
      simp only [DecompTree.restrict, DecompTree.maxBagCard]
      refine max_le_max ?_ (listMaxBagCard_restrict_le cs)
      exact Finset.card_le_card_of_injOn f (fun u hu => Finset.mem_preimage.mp hu)
        (fun x _ y _ h => hf h)
where
  listMaxBagCard_restrict_le :
      ∀ cs : List (DecompTree β),
        DecompTree.listMaxBagCard (DecompTree.restrict.restrictList f hf cs) ≤
          DecompTree.listMaxBagCard cs
    | [] => le_rfl
    | c :: cs => by
        simp only [DecompTree.restrict.restrictList, DecompTree.listMaxBagCard]
        exact max_le_max (DecompTree.maxBagCard_restrict_le f hf c) (listMaxBagCard_restrict_le cs)

mutual
lemma DecompTree.runningIntersection_restrict {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    ∀ (t : DecompTree β) (outside' : Finset α) (outside : Finset β),
      (∀ u, u ∈ outside' ↔ f u ∈ outside) →
      DecompTree.RunningIntersection outside t →
      DecompTree.RunningIntersection outside' (t.restrict f hf)
  | .node bag cs, outside', outside, hOut, ⟨hTop, hCs⟩ => by
      change (∀ u ∈ (DecompTree.node (bag.preimage f hf.injOn)
            (DecompTree.restrict.restrictList f hf cs)).subtreeWires,
          u ∈ outside' → u ∈ bag.preimage f hf.injOn) ∧
        DecompTree.ListRunningIntersection (outside' ∪ bag.preimage f hf.injOn)
          (bag.preimage f hf.injOn) (DecompTree.restrict.restrictList f hf cs)
      refine ⟨fun u huSub huOut => Finset.mem_preimage.mpr ?_, ?_⟩
      · have huSub' : u ∈ ((DecompTree.node bag cs).restrict f hf).subtreeWires := huSub
        rw [DecompTree.mem_subtreeWires_restrict f hf u (DecompTree.node bag cs)] at huSub'
        exact hTop (f u) huSub' ((hOut u).mp huOut)
      · refine DecompTree.listRunningIntersection_restrict f hf cs
          (outside' ∪ bag.preimage f hf.injOn) (outside ∪ bag)
          (bag.preimage f hf.injOn) bag ?_ (fun u => Finset.mem_preimage) hCs
        intro u
        simp only [Finset.mem_union, Finset.mem_preimage, hOut u]

lemma DecompTree.listRunningIntersection_restrict {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) :
    ∀ (cs : List (DecompTree β)) (outside' : Finset α) (outside : Finset β)
      (parentBag' : Finset α) (parentBag : Finset β),
      (∀ u, u ∈ outside' ↔ f u ∈ outside) →
      (∀ u, u ∈ parentBag' ↔ f u ∈ parentBag) →
      DecompTree.ListRunningIntersection outside parentBag cs →
      DecompTree.ListRunningIntersection outside' parentBag'
        (DecompTree.restrict.restrictList f hf cs)
  | [], _, _, _, _, _, _, _ => trivial
  | c :: cs, outside', outside, parentBag', parentBag, hOut, hPar, ⟨hPair, hC, hTail⟩ => by
      simp only [DecompTree.restrict.restrictList, DecompTree.ListRunningIntersection]
      refine ⟨fun u huC huCs => ?_, ?_, ?_⟩
      · rw [DecompTree.mem_subtreeWires_restrict f hf u c] at huC
        rw [DecompTree.mem_subtreeWires_restrict.mem_listWires_restrictList f hf u cs] at huCs
        exact (hPar u).mpr (hPair (f u) huC huCs)
      · refine DecompTree.runningIntersection_restrict f hf c
          (outside' ∪ DecompTree.listWires (DecompTree.restrict.restrictList f hf cs))
          (outside ∪ DecompTree.listWires cs) ?_ hC
        intro u
        simp only [Finset.mem_union, hOut u,
          DecompTree.mem_subtreeWires_restrict.mem_listWires_restrictList]
      · refine DecompTree.listRunningIntersection_restrict f hf cs
          (outside' ∪ (c.restrict f hf).subtreeWires)
          (outside ∪ c.subtreeWires) parentBag' parentBag ?_ hPar hTail
        intro u
        simp only [Finset.mem_union, hOut u, DecompTree.mem_subtreeWires_restrict]
end

/-- Restrict a valid tree decomposition along an injective edge-preserving wire embedding. -/
noncomputable def TreeDecomp.restrict {w₁ w₂ : Nat} {E₁ : Fin w₁ → Fin w₁ → Prop}
    {E₂ : Fin w₂ → Fin w₂ → Prop}
    (f : Fin w₁ → Fin w₂) (hf : Function.Injective f) (hEdge : ∀ u v, E₁ u v → E₂ (f u) (f v))
    (td : TreeDecomp E₂) : TreeDecomp E₁ where
  root := td.root.restrict f hf
  cover_wire u := (DecompTree.mem_subtreeWires_restrict f hf u td.root).mpr (td.cover_wire (f u))
  cover_edge u v huv :=
    DecompTree.containsPair_restrict f hf u v td.root (td.cover_edge (f u) (f v) (hEdge u v huv))
  running :=
    DecompTree.runningIntersection_restrict f hf td.root ∅ ∅ (by simp) td.running

theorem TreeDecomp.restrict_le {w₁ w₂ : Nat} {E₁ : Fin w₁ → Fin w₁ → Prop}
    {E₂ : Fin w₂ → Fin w₂ → Prop}
    (f : Fin w₁ → Fin w₂) (hf : Function.Injective f) (hEdge : ∀ u v, E₁ u v → E₂ (f u) (f v))
    (td : TreeDecomp E₂) :
    (td.restrict f hf hEdge).width ≤ td.width :=
  Nat.sub_le_sub_right (DecompTree.maxBagCard_restrict_le f hf td.root) 1

/-- Restrict a contraction tree along an injective wire embedding `f : Fin w₁ → Fin w₂`. -/
noncomputable def ContractionTree.restrict {w₁ w₂ : Nat} (f : Fin w₁ → Fin w₂)
    (hf : Function.Injective f) : ContractionTree w₂ → ContractionTree w₁
  | .leaf wires => .leaf (wires.preimage f hf.injOn)
  | .join l r => .join (l.restrict f hf) (r.restrict f hf)

lemma ContractionTree.scope_restrict {w₁ w₂ : Nat} (f : Fin w₁ → Fin w₂) (hf : Function.Injective f) :
    ∀ (t : ContractionTree w₂) (u : Fin w₁), u ∈ (t.restrict f hf).scope ↔ f u ∈ t.scope
  | .leaf wires, u => by simp [ContractionTree.restrict, ContractionTree.scope]
  | .join l r, u => by
      simp only [ContractionTree.restrict, ContractionTree.scope, Finset.mem_union]
      rw [scope_restrict f hf l u, scope_restrict f hf r u]

lemma ContractionTree.containsPair_restrict {w₁ w₂ : Nat} (f : Fin w₁ → Fin w₂)
    (hf : Function.Injective f) (u v : Fin w₁) :
    ∀ t : ContractionTree w₂,
      ContractionTree.ContainsPair (f u) (f v) t →
        ContractionTree.ContainsPair u v (t.restrict f hf)
  | .leaf wires, h => by
      simpa [ContractionTree.restrict, ContractionTree.ContainsPair] using h
  | .join l r, h => by
      simp only [ContractionTree.restrict, ContractionTree.ContainsPair] at h ⊢
      rcases h with hl | hr
      · exact Or.inl (containsPair_restrict f hf u v l hl)
      · exact Or.inr (containsPair_restrict f hf u v r hr)

lemma ContractionTree.allLeaves_restrict {w₁ w₂ : Nat} (f : Fin w₁ → Fin w₂)
    (hf : Function.Injective f) {P : Finset (Fin w₁) → Prop} {Q : Finset (Fin w₂) → Prop}
    (hPQ : ∀ s, Q s → P (s.preimage f hf.injOn)) :
    ∀ t : ContractionTree w₂, t.AllLeaves Q → (t.restrict f hf).AllLeaves P
  | .leaf wires, h => hPQ wires h
  | .join l r, ⟨hl, hr⟩ =>
      ⟨allLeaves_restrict f hf hPQ l hl, allLeaves_restrict f hf hPQ r hr⟩

lemma ContractionTree.maxBoundary_restrict_le {w₁ w₂ : Nat} (f : Fin w₁ → Fin w₂)
    (hf : Function.Injective f) :
    ∀ (t : ContractionTree w₂) (outside' : Finset (Fin w₁)) (outside : Finset (Fin w₂)),
      (∀ u ∈ outside', f u ∈ outside) →
      (t.restrict f hf).maxBoundary outside' ≤ t.maxBoundary outside
  | .leaf wires, outside', outside, hOut => by
      simp only [ContractionTree.restrict, ContractionTree.maxBoundary]
      refine Finset.card_le_card_of_injOn f ?_ (fun x _ y _ h => hf h)
      intro u hu
      simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_preimage] at hu ⊢
      exact ⟨hu.1, hOut u hu.2⟩
  | .join l r, outside', outside, hOut => by
      simp only [ContractionTree.restrict, ContractionTree.maxBoundary]
      refine max_le_max ?_ (max_le_max ?_ ?_)
      · refine Finset.card_le_card_of_injOn f ?_ (fun x _ y _ h => hf h)
        intro u hu
        simp only [Finset.mem_coe, Finset.mem_inter, Finset.mem_union] at hu ⊢
        refine ⟨?_, hOut u hu.2⟩
        rcases hu.1 with huL | huR
        · exact Or.inl ((ContractionTree.scope_restrict f hf l u).mp huL)
        · exact Or.inr ((ContractionTree.scope_restrict f hf r u).mp huR)
      · refine maxBoundary_restrict_le f hf l (outside' ∪ (r.restrict f hf).scope)
          (outside ∪ r.scope) ?_
        intro u hu
        simp only [Finset.mem_union] at hu ⊢
        rcases hu with hu1 | hu2
        · exact Or.inl (hOut u hu1)
        · exact Or.inr ((ContractionTree.scope_restrict f hf r u).mp hu2)
      · refine maxBoundary_restrict_le f hf r (outside' ∪ (l.restrict f hf).scope)
          (outside ∪ l.scope) ?_
        intro u hu
        simp only [Finset.mem_union] at hu ⊢
        rcases hu with hu1 | hu2
        · exact Or.inl (hOut u hu1)
        · exact Or.inr ((ContractionTree.scope_restrict f hf l u).mp hu2)

/-- Restrict a valid contraction tree along an injective edge-preserving wire embedding. -/
noncomputable def ValidContractionTree.restrict {w₁ w₂ : Nat} {E₁ : Fin w₁ → Fin w₁ → Prop}
    {E₂ : Fin w₂ → Fin w₂ → Prop}
    (f : Fin w₁ → Fin w₂) (hf : Function.Injective f) (hEdge : ∀ u v, E₁ u v → E₂ (f u) (f v))
    (ct : ValidContractionTree E₂) : ValidContractionTree E₁ where
  tree := ct.tree.restrict f hf
  cover_wire u := (ContractionTree.scope_restrict f hf ct.tree u).mpr (ct.cover_wire (f u))
  cover_edge u v huv :=
    ContractionTree.containsPair_restrict f hf u v ct.tree
      (ct.cover_edge (f u) (f v) (hEdge u v huv))

theorem ValidContractionTree.restrict_le {w₁ w₂ : Nat} {E₁ : Fin w₁ → Fin w₁ → Prop}
    {E₂ : Fin w₂ → Fin w₂ → Prop}
    (f : Fin w₁ → Fin w₂) (hf : Function.Injective f) (hEdge : ∀ u v, E₁ u v → E₂ (f u) (f v))
    (ct : ValidContractionTree E₂) :
    (ct.restrict f hf hEdge).contractionWidth ≤ ct.contractionWidth :=
  ContractionTree.maxBoundary_restrict_le f hf ct.tree ∅ ∅ (by simp)

end SubgraphMonotonicity

namespace ButterflyNet

private lemma testBit_two_pow_sub_one (ℓ b : Nat) :
    Nat.testBit (2 ^ ℓ - 1) b = decide (b < ℓ) := by
  by_cases hb : b < ℓ
  · have hPosB : 0 < 2 ^ b := Nat.two_pow_pos b
    have hPosL : 0 < 2 ^ (ℓ - b) := Nat.two_pow_pos (ℓ - b)
    have hSplit : 2 ^ ℓ = 2 ^ b * 2 ^ (ℓ - b) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hb.le]
    have hEq : 2 ^ ℓ - 1 = 2 ^ b * (2 ^ (ℓ - b) - 1) + (2 ^ b - 1) := by
      rw [hSplit, Nat.mul_sub_left_distrib, Nat.mul_one]
      have hMulGe : 2 ^ b ≤ 2 ^ b * 2 ^ (ℓ - b) := Nat.le_mul_of_pos_right _ hPosL
      omega
    have hMod : (2 ^ ℓ - 1) / 2 ^ b = 2 ^ (ℓ - b) - 1 := by
      rw [hEq, Nat.mul_add_div hPosB, Nat.div_eq_of_lt (Nat.sub_lt hPosB Nat.zero_lt_one), Nat.add_zero]
    have hPos : 0 < ℓ - b := Nat.sub_pos_of_lt hb
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hPos.ne'
    have hEven : 2 ^ (ℓ - b) = 2 * 2 ^ k := by rw [hk, Nat.pow_succ']
    have hPosK : 1 ≤ 2 ^ k := Nat.two_pow_pos k
    have hOdd : (2 ^ (ℓ - b) - 1) % 2 = 1 := by omega
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, hMod, hOdd]
    simp [hb]
  · have hGe : ℓ ≤ b := Nat.le_of_not_gt hb
    have hLt : 2 ^ ℓ - 1 < 2 ^ b := by
      have : 2 ^ ℓ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hGe
      have := Nat.two_pow_pos ℓ
      omega
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hLt, hb]

private lemma mod_two_pow_eq_sub_one_iff {j ℓ : Nat} :
    j % 2 ^ ℓ = 2 ^ ℓ - 1 ↔ ∀ b < ℓ, j.testBit b = true := by
  constructor
  · intro h b hb
    have hBit := congrArg (fun n => Nat.testBit n b) h
    rw [Nat.testBit_mod_two_pow, testBit_two_pow_sub_one] at hBit
    simpa [hb] using hBit
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_mod_two_pow, testBit_two_pow_sub_one]
    by_cases hb : b < ℓ
    · simp [hb, h b hb]
    · simp [hb]

private lemma add_two_pow_testBit_lt {n ℓ b : Nat} (hb : b < ℓ) :
    (n + 2 ^ ℓ).testBit b = n.testBit b := by
  have hPosB : 0 < 2 ^ b := Nat.two_pow_pos b
  have hSplit : 2 ^ ℓ = 2 ^ b * 2 ^ (ℓ - b) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hb.le]
  have hPos : 0 < ℓ - b := Nat.sub_pos_of_lt hb
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hPos.ne'
  have hEven : 2 ^ (ℓ - b) = 2 * 2 ^ k := by rw [hk, Nat.pow_succ']
  have hDiv : (n + 2 ^ ℓ) / 2 ^ b = n / 2 ^ b + 2 * 2 ^ k := by
    rw [hSplit, hEven, Nat.add_mul_div_left _ _ hPosB]
  have hModEq : (n / 2 ^ b + 2 * 2 ^ k) % 2 = (n / 2 ^ b) % 2 :=
    Nat.add_mul_mod_self_left (n / 2 ^ b) 2 (2 ^ k)
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, hDiv, hModEq]

private lemma add_two_pow_testBit_self {n ℓ : Nat} (hEven : n / 2 ^ ℓ % 2 = 0) :
    (n + 2 ^ ℓ).testBit ℓ = true ∧ n.testBit ℓ = false := by
  have hPosL : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have hDiv : (n + 2 ^ ℓ) / 2 ^ ℓ = n / 2 ^ ℓ + 1 := by
    simp [Nat.add_div_right n hPosL]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, hDiv]
  constructor
  · simp [Nat.add_mod, hEven]
  · simp [hEven]

private lemma add_two_pow_testBit_gt {n ℓ b : Nat} (hEven : n / 2 ^ ℓ % 2 = 0) (hb : ℓ < b) :
    (n + 2 ^ ℓ).testBit b = n.testBit b := by
  have hPosL : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have hSplit : 2 ^ b = 2 ^ ℓ * 2 ^ (b - ℓ) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hb.le]
  have hPos : 0 < b - ℓ := Nat.sub_pos_of_lt hb
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hPos.ne'
  have hTwo : 2 ^ (b - ℓ) = 2 * 2 ^ k := by rw [hk, Nat.pow_succ']
  have hAddDiv : (n + 2 ^ ℓ) / 2 ^ ℓ = n / 2 ^ ℓ + 1 := by
    simp [Nat.add_div_right n hPosL]
  have hStep : (n / 2 ^ ℓ + 1) / 2 = (n / 2 ^ ℓ) / 2 := by omega
  have hEqDiv : (n + 2 ^ ℓ) / 2 ^ b = n / 2 ^ b := by
    rw [hSplit, hTwo, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      hAddDiv, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul (n / 2 ^ ℓ), hStep]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hEqDiv]

lemma flipBit_testBit_lt {j ℓ b : Nat} (hb : b < ℓ) :
    (flipBit j ℓ).testBit b = j.testBit b := by
  unfold flipBit
  by_cases hEven : j / 2 ^ ℓ % 2 = 0
  · simp only [hEven, ↓reduceIte]
    exact add_two_pow_testBit_lt hb
  · simp only [hEven, ↓reduceIte]
    have hGe : 2 ^ ℓ ≤ j := by
      by_contra hLt
      push Not at hLt
      have : j / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hLt
      omega
    have hEq : (j - 2 ^ ℓ) + 2 ^ ℓ = j := Nat.sub_add_cancel hGe
    have hAdd := add_two_pow_testBit_lt (n := j - 2 ^ ℓ) hb
    rw [hEq] at hAdd
    exact hAdd.symm

lemma flipBit_div_two_pow_sub_one {j ℓ : Nat} (hGe : 2 ^ ℓ ≤ j) :
    (j - 2 ^ ℓ) / 2 ^ ℓ = j / 2 ^ ℓ - 1 := by
  have hPosL : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have hMod : j % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt j hPosL
  have hQ : 1 ≤ j / 2 ^ ℓ := Nat.div_pos hGe hPosL
  have hDM := Nat.div_add_mod j (2 ^ ℓ)
  set q := j / 2 ^ ℓ
  set r := j % 2 ^ ℓ
  have hDecomp : j - 2 ^ ℓ = 2 ^ ℓ * (q - 1) + r := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hMul : 2 ^ ℓ ≤ 2 ^ ℓ * q := Nat.le_mul_of_pos_right _ hQ
    omega
  rw [hDecomp, Nat.mul_add_div hPosL, Nat.div_eq_of_lt hMod, Nat.add_zero]

lemma flipBit_testBit_self (j ℓ : Nat) :
    (flipBit j ℓ).testBit ℓ = !(j.testBit ℓ) := by
  unfold flipBit
  by_cases hEven : j / 2 ^ ℓ % 2 = 0
  · simp only [hEven, ↓reduceIte]
    have h := add_two_pow_testBit_self hEven
    rw [h.1, h.2]
    rfl
  · simp only [hEven, ↓reduceIte]
    have hGe : 2 ^ ℓ ≤ j := by
      by_contra hLt
      push Not at hLt
      have : j / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hLt
      omega
    have hQ : 1 ≤ j / 2 ^ ℓ := Nat.div_pos hGe (Nat.two_pow_pos ℓ)
    have hDivSub : (j - 2 ^ ℓ) / 2 ^ ℓ % 2 = 0 := by
      rw [flipBit_div_two_pow_sub_one hGe]
      omega
    have h := add_two_pow_testBit_self hDivSub
    rw [Nat.sub_add_cancel hGe] at h
    rw [h.1, h.2]
    rfl

lemma flipBit_testBit_gt {j ℓ b : Nat} (hb : ℓ < b) :
    (flipBit j ℓ).testBit b = j.testBit b := by
  unfold flipBit
  by_cases hEven : j / 2 ^ ℓ % 2 = 0
  · simp only [hEven, ↓reduceIte]
    exact add_two_pow_testBit_gt hEven hb
  · simp only [hEven, ↓reduceIte]
    have hGe : 2 ^ ℓ ≤ j := by
      by_contra hLt
      push Not at hLt
      have : j / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hLt
      omega
    have hQ : 1 ≤ j / 2 ^ ℓ := Nat.div_pos hGe (Nat.two_pow_pos ℓ)
    have hDivSub : (j - 2 ^ ℓ) / 2 ^ ℓ % 2 = 0 := by
      rw [flipBit_div_two_pow_sub_one hGe]
      omega
    have h := add_two_pow_testBit_gt hDivSub hb
    rw [Nat.sub_add_cancel hGe] at h
    exact h.symm

lemma div_two_pow_flipBit_eq_of_lt {j ℓ m : Nat} (hm : ℓ < m) :
    flipBit j ℓ / 2 ^ m = j / 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  exact flipBit_testBit_gt (by omega)

/-- Step edge relation characterizing butterfly wires at layers `< D`. -/
def BflyStep (d D u v : Nat) : Prop :=
  ∃ ℓ j, ℓ < D ∧ j < 2 ^ d ∧ v = (ℓ + 1) * 2 ^ d + j ∧
    (u = ℓ * 2 ^ d + j ∨ u = ℓ * 2 ^ d + flipBit j ℓ)

private lemma bflyGate_uses_iff (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d)
    (a : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j)) :
    GateUsesWire (bflyGate d ℓ j hℓ hj) a ↔
      a.val = ℓ * 2 ^ d + j ∨ a.val = ℓ * 2 ^ d + flipBit j ℓ := by
  dsimp [bflyGate]
  split_ifs
  · constructor
    · intro h
      cases h <;> simp
    · rintro (h1 | h2)
      · exact (congrArg (GateUsesWire _) (Fin.ext h1.symm)).mp (GateUsesWire.and_left _ _)
      · exact (congrArg (GateUsesWire _) (Fin.ext h2.symm)).mp (GateUsesWire.and_right _ _)
  · constructor
    · intro h
      cases h <;> simp
    · rintro (h1 | h2)
      · exact (congrArg (GateUsesWire _) (Fin.ext h1.symm)).mp (GateUsesWire.or_left _ _)
      · exact (congrArg (GateUsesWire _) (Fin.ext h2.symm)).mp (GateUsesWire.or_right _ _)

private lemma appendBflyRow_directedEdge_iff (d ℓ : Nat) (hℓ : ℓ < d)
    (prev : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (hPrev : ∀ u v, prev.DirectedEdge u v ↔ BflyStep d ℓ u.val v.val)
    (m : Nat) (hm : m ≤ 2 ^ d) :
    ∀ u v : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m),
      (appendBflyRow d ℓ hℓ m hm prev).DirectedEdge u v ↔
        BflyStep d ℓ u.val v.val ∨
          (∃ j < m, v.val = (ℓ + 1) * 2 ^ d + j ∧
            (u.val = ℓ * 2 ^ d + j ∨ u.val = ℓ * 2 ^ d + flipBit j ℓ)) := by
  induction m with
  | zero =>
      intro u v
      simpa [appendBflyRow] using hPrev u v
  | succ m ih =>
      intro u v
      dsimp [appendBflyRow]
      have hm' : m ≤ 2 ^ d := Nat.le_of_lt hm
      have hBase : LayeredRing.ringWires (2 ^ d) ℓ = (ℓ + 1) * 2 ^ d :=
        LayeredRing.ringWires_eq (2 ^ d) ℓ
      constructor
      · intro h
        rcases h with ⟨u', v', hu, hv, hPrevE⟩ | ⟨hv, a, hu, ha⟩
        · subst hu hv
          have ihuv := (ih hm' u' v').mp hPrevE
          rcases ihuv with hB | ⟨j, hj, hv', hu'⟩
          · exact Or.inl hB
          · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hv', hu'⟩
        · subst hv hu
          refine Or.inr ⟨m, Nat.lt_succ_self m, ?_, (bflyGate_uses_iff d ℓ m hℓ hm a).mp ha⟩
          simp [hBase]
      · intro h
        rcases h with hB | ⟨j, hj, hv, hu⟩
        · have hVlt : v.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
            rcases hB with ⟨ℓ', j', hℓ', hj', hv', _⟩
            have h1 : (ℓ' + 1) * 2 ^ d ≤ ℓ * 2 ^ d := Nat.mul_le_mul_right _ hℓ'
            have h2 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            omega
          have hUlt : u.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
            rcases hB with ⟨ℓ', j', hℓ', hj', _, hu1 | hu2⟩
            · have : ℓ' * 2 ^ d ≤ ℓ * 2 ^ d := Nat.mul_le_mul_right _ hℓ'.le
              nlinarith
            · have : ℓ' * 2 ^ d ≤ ℓ * 2 ^ d := Nat.mul_le_mul_right _ hℓ'.le
              have : flipBit j' ℓ' < 2 ^ d := flipBit_lt hj' (Nat.lt_trans hℓ' hℓ)
              nlinarith
          let u' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨u.val, hUlt⟩
          let v' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨v.val, hVlt⟩
          have hEdge := (ih hm' u' v').mpr (Or.inl hB)
          exact Or.inl ⟨u', v', Fin.ext rfl, Fin.ext rfl, hEdge⟩
        · by_cases hjm : j < m
          · have hVlt : v.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by omega
            have hUlt : u.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
              have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
              rcases hu with hu1 | hu2
              · omega
              · have := flipBit_lt (Nat.lt_trans hjm hm) hℓ
                omega
            let u' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨u.val, hUlt⟩
            let v' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨v.val, hVlt⟩
            have hEdge := (ih hm' u' v').mpr (Or.inr ⟨j, hjm, hv, hu⟩)
            exact Or.inl ⟨u', v', Fin.ext rfl, Fin.ext rfl, hEdge⟩
          · have hEq : j = m := by omega
            subst j
            have hvLast : v = Fin.last _ := Fin.ext (by simp [hBase, hv])
            have hUlt : u.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
              have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
              rcases hu with hu1 | hu2
              · omega
              · have := flipBit_lt hm hℓ
                omega
            let a : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨u.val, hUlt⟩
            have ha : GateUsesWire (bflyGate d ℓ m hℓ hm) a :=
              (bflyGate_uses_iff d ℓ m hℓ hm a).mpr hu
            exact Or.inr ⟨hvLast, a, Fin.ext rfl, ha⟩

private lemma circuit_directedEdge_inputsOnly {inputs : Nat} (u v : Fin inputs) :
    (Circuit.inputsOnly : Circuit inputs inputs).DirectedEdge u v = False := by
  simp [Circuit.DirectedEdge]

private lemma buildBfly_directedEdge_iff (d : Nat) :
    ∀ D (hD : D ≤ d) (u v : Fin (LayeredRing.ringWires (2 ^ d) D)),
      (buildBfly d D hD).DirectedEdge u v ↔ BflyStep d D u.val v.val
  | 0, _, u, v => by
      have hW : LayeredRing.ringWires (2 ^ d) 0 = 2 ^ d := by
        simpa using LayeredRing.ringWires_eq (2 ^ d) 0
      simp only [buildBfly, BflyStep]
      exact ⟨fun h => by
        have h' : (Circuit.inputsOnly : Circuit (2 ^ d) (2 ^ d)).DirectedEdge
            ⟨u.val, lt_of_lt_of_eq u.isLt hW⟩ ⟨v.val, lt_of_lt_of_eq v.isLt hW⟩ := h
        rw [circuit_directedEdge_inputsOnly] at h'
        exact False.elim h',
        fun ⟨_, _, hℓ, _⟩ => by omega⟩
  | D + 1, hD, u, v => by
      dsimp [buildBfly]
      have hPrev := buildBfly_directedEdge_iff d D (Nat.le_of_lt hD)
      refine (appendBflyRow_directedEdge_iff d D hD (buildBfly d D _) hPrev (2 ^ d) le_rfl u v).trans ?_
      constructor
      · rintro (⟨ℓ, j, hℓ, hj, hv, hu⟩ | ⟨j, hj, hv, hu⟩)
        · exact ⟨ℓ, j, Nat.lt_succ_of_lt hℓ, hj, hv, hu⟩
        · exact ⟨D, j, Nat.lt_succ_self D, hj, hv, hu⟩
      · rintro ⟨ℓ, j, hℓ, hj, hv, hu⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with hLt | rfl
        · exact Or.inl ⟨ℓ, j, hLt, hj, hv, hu⟩
        · exact Or.inr ⟨j, hj, hv, hu⟩

theorem source_directedEdge_iff (d : Nat) (u v : Fin (source d).wires) :
    (source d).circuit.DirectedEdge u v ↔ BflyStep d d u.val v.val :=
  buildBfly_directedEdge_iff d d le_rfl u v

private lemma source_output_eq_bflyWire (d : Nat) :
    (source d).output =
      bflyWire d d (2 ^ d - 1) le_rfl (Nat.sub_lt (Nat.two_pow_pos d) Nat.zero_lt_one) := by
  apply Fin.ext
  have hW := LayeredRing.ringWires_eq (2 ^ d) d
  dsimp [source, bflyWire]
  rw [hW]
  have hPos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hMul : (d + 1) * 2 ^ d = d * 2 ^ d + 2 ^ d := by ring
  omega

/-- Exact reachability characterization for `ButterflyNet.source d`: a wire `(ℓ, j)` reaches
the single output wire `(d, 2^d - 1)` if and only if all low `ℓ` bits of `j` are `1`, i.e.,
`j % 2 ^ ℓ = 2 ^ ℓ - 1`. -/
theorem source_reachable_iff (d : Nat) (u : Fin (source d).wires) :
    (source d).circuit.DirectedReach u (source d).output ↔
      ∃ (ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d),
        u = bflyWire d ℓ j hℓ hj ∧ j % 2 ^ ℓ = 2 ^ ℓ - 1 := by
  constructor
  · intro hReach
    induction hReach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        refine ⟨d, 2 ^ d - 1, le_rfl, Nat.sub_lt (Nat.two_pow_pos d) Nat.zero_lt_one,
          source_output_eq_bflyWire d, ?_⟩
        exact Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos d) Nat.zero_lt_one)
    | head hEdge _ ih =>
        rcases ih with ⟨ℓ', j', hℓ', hj', hbEq, hj'Mod⟩
        rw [source_directedEdge_iff] at hEdge
        rcases hEdge with ⟨ℓ, k, hℓLt, hkLt, hbVal, haVal⟩
        have hbVal' : _ = ℓ' * 2 ^ d + j' := congrArg Fin.val hbEq
        rw [hbVal'] at hbVal
        have hLayer : ℓ + 1 = ℓ' ∧ k = j' := by
          have hEqMul : ℓ + 1 = ℓ' := by
            by_contra hNe
            rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
            · have hMul : (ℓ + 2) * 2 ^ d ≤ ℓ' * 2 ^ d := Nat.mul_le_mul_right _ hLt
              have : (ℓ + 1) * 2 ^ d + 2 ^ d = (ℓ + 2) * 2 ^ d := by ring
              omega
            · have hMul : (ℓ' + 1) * 2 ^ d ≤ (ℓ + 1) * 2 ^ d := Nat.mul_le_mul_right _ hGt
              have : ℓ' * 2 ^ d + 2 ^ d = (ℓ' + 1) * 2 ^ d := by ring
              omega
          subst hEqMul
          omega
        rcases hLayer with ⟨rfl, rfl⟩
        rcases haVal with ha1 | ha2
        · refine ⟨ℓ, k, hℓLt.le, hkLt, Fin.ext (by simp [bflyWire, ha1]), ?_⟩
          rw [mod_two_pow_eq_sub_one_iff] at hj'Mod ⊢
          intro t ht
          exact hj'Mod t (Nat.lt_succ_of_lt ht)
        · have hFlipLt : flipBit k ℓ < 2 ^ d := flipBit_lt hkLt hℓLt
          refine ⟨ℓ, flipBit k ℓ, hℓLt.le, hFlipLt, Fin.ext (by simp [bflyWire, ha2]), ?_⟩
          rw [mod_two_pow_eq_sub_one_iff] at hj'Mod ⊢
          intro t ht
          rw [flipBit_testBit_lt ht]
          exact hj'Mod t (Nat.lt_succ_of_lt ht)
  · rintro ⟨ℓ, j, hℓ, hj, rfl, hjMod⟩
    suffices ∀ m (ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d),
        m = d - ℓ → j % 2 ^ ℓ = 2 ^ ℓ - 1 →
        (source d).circuit.DirectedReach (bflyWire d ℓ j hℓ hj) (source d).output by
      exact this (d - ℓ) ℓ j hℓ hj rfl hjMod
    intro m
    induction m with
    | zero =>
        intro ℓ j hℓ hj hm hjMod
        have hEq : ℓ = d := by omega
        subst hEq
        have hjEq : j = 2 ^ ℓ - 1 := by
          rw [Nat.mod_eq_of_lt hj] at hjMod
          exact hjMod
        subst hjEq
        rw [source_output_eq_bflyWire]
        exact Relation.ReflTransGen.refl
    | succ m ih =>
        intro ℓ j hℓ hj hm hjMod
        have hℓLt : ℓ < d := by omega
        by_cases hBit : j.testBit ℓ = true
        · have hjMod' : j % 2 ^ (ℓ + 1) = 2 ^ (ℓ + 1) - 1 := by
            rw [mod_two_pow_eq_sub_one_iff] at hjMod ⊢
            intro t ht
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht with htLt | rfl
            · exact hjMod t htLt
            · exact hBit
          have hEdge : (source d).circuit.DirectedEdge
              (bflyWire d ℓ j hℓ hj) (bflyWire d (ℓ + 1) j hℓLt hj) := by
            rw [source_directedEdge_iff]
            exact ⟨ℓ, j, hℓLt, hj, rfl, Or.inl rfl⟩
          exact Relation.ReflTransGen.head hEdge
            (ih (ℓ + 1) j hℓLt hj (by omega) hjMod')
        · have hBitFalse : j.testBit ℓ = false := Bool.eq_false_iff.mpr hBit
          have hFlipLt : flipBit j ℓ < 2 ^ d := flipBit_lt hj hℓLt
          have hjMod' : (flipBit j ℓ) % 2 ^ (ℓ + 1) = 2 ^ (ℓ + 1) - 1 := by
            rw [mod_two_pow_eq_sub_one_iff] at hjMod ⊢
            intro t ht
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht with htLt | rfl
            · rw [flipBit_testBit_lt htLt]
              exact hjMod t htLt
            · rw [flipBit_testBit_self, hBitFalse]
              rfl
          have hEdge : (source d).circuit.DirectedEdge
              (bflyWire d ℓ j hℓ hj) (bflyWire d (ℓ + 1) (flipBit j ℓ) hℓLt hFlipLt) := by
            rw [source_directedEdge_iff]
            refine ⟨ℓ, flipBit j ℓ, hℓLt, hFlipLt, rfl, Or.inr ?_⟩
            dsimp [bflyWire]
            rw [flipBit_involutive j ℓ]
          exact Relation.ReflTransGen.head hEdge
            (ih (ℓ + 1) (flipBit j ℓ) hℓLt hFlipLt (by omega) hjMod')

private lemma sum_two_pow_range (d : Nat) :
    ∑ k ∈ Finset.range (d + 1), 2 ^ k = 2 * 2 ^ d - 1 := by
  induction d with
  | zero => decide
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
      rw [Nat.pow_succ']
      omega

/-- Exactly `2 * 2 ^ d - 1` wires out of `(d + 1) * 2 ^ d` total wires in `ButterflyNet.source d`
can reach the single output wire. -/
theorem source_reachable_card_eq (d : Nat) :
    open Classical in
    (Finset.univ.filter (fun u : Fin (source d).wires =>
      (source d).circuit.DirectedReach u (source d).output)).card = 2 * 2 ^ d - 1 := by
  classical
  let R := Finset.univ.filter (fun u : Fin (source d).wires =>
    (source d).circuit.DirectedReach u (source d).output)
  let Ix := Sigma (fun ℓ : Fin (d + 1) => Fin (2 ^ (d - ℓ.val)))
  let toWire : Ix → Fin (source d).wires := fun ⟨ℓ, q⟩ =>
    let j := q.val * 2 ^ ℓ.val + (2 ^ ℓ.val - 1)
    have hℓ : ℓ.val ≤ d := Nat.lt_succ_iff.mp ℓ.isLt
    have hj : j < 2 ^ d := by
      have hPowPos : 0 < 2 ^ ℓ.val := Nat.two_pow_pos ℓ.val
      have hMul : (q.val + 1) * 2 ^ ℓ.val ≤ 2 ^ (d - ℓ.val) * 2 ^ ℓ.val :=
        Nat.mul_le_mul_right _ q.isLt
      have hPowEq : 2 ^ (d - ℓ.val) * 2 ^ ℓ.val = 2 ^ d := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hℓ]
      rw [hPowEq] at hMul
      dsimp [j]
      rw [Nat.add_mul, Nat.one_mul] at hMul
      omega
    bflyWire d ℓ.val j hℓ hj
  have hToMem : ∀ p : Ix, toWire p ∈ R := by
    intro ⟨ℓ, q⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (source_reachable_iff d _).mpr ?_⟩
    have hℓ : ℓ.val ≤ d := Nat.lt_succ_iff.mp ℓ.isLt
    have hPowPos : 0 < 2 ^ ℓ.val := Nat.two_pow_pos ℓ.val
    have hMod : (q.val * 2 ^ ℓ.val + (2 ^ ℓ.val - 1)) % 2 ^ ℓ.val = 2 ^ ℓ.val - 1 := by
      rw [Nat.mul_comm, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (Nat.sub_lt hPowPos Nat.zero_lt_one)
    exact ⟨ℓ.val, _, hℓ, _, rfl, hMod⟩
  have hInj : Function.Injective toWire := by
    rintro ⟨ℓ₁, q₁⟩ ⟨ℓ₂, q₂⟩ hEq
    have hVal : (toWire ⟨ℓ₁, q₁⟩).val = (toWire ⟨ℓ₂, q₂⟩).val := congrArg Fin.val hEq
    dsimp [toWire, bflyWire] at hVal
    have hℓ1 : ℓ₁.val ≤ d := Nat.lt_succ_iff.mp ℓ₁.isLt
    have hℓ2 : ℓ₂.val ≤ d := Nat.lt_succ_iff.mp ℓ₂.isLt
    have hj1 : q₁.val * 2 ^ ℓ₁.val + (2 ^ ℓ₁.val - 1) < 2 ^ d := by
      have hPowPos : 0 < 2 ^ ℓ₁.val := Nat.two_pow_pos ℓ₁.val
      have hPowEq : 2 ^ (d - ℓ₁.val) * 2 ^ ℓ₁.val = 2 ^ d := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hℓ1]
      have hMul : (q₁.val + 1) * 2 ^ ℓ₁.val ≤ 2 ^ d := by
        calc (q₁.val + 1) * 2 ^ ℓ₁.val ≤ 2 ^ (d - ℓ₁.val) * 2 ^ ℓ₁.val :=
              Nat.mul_le_mul_right _ q₁.isLt
          _ = 2 ^ d := hPowEq
      rw [Nat.add_mul, Nat.one_mul] at hMul
      omega
    have hj2 : q₂.val * 2 ^ ℓ₂.val + (2 ^ ℓ₂.val - 1) < 2 ^ d := by
      have hPowPos : 0 < 2 ^ ℓ₂.val := Nat.two_pow_pos ℓ₂.val
      have hPowEq : 2 ^ (d - ℓ₂.val) * 2 ^ ℓ₂.val = 2 ^ d := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hℓ2]
      have hMul : (q₂.val + 1) * 2 ^ ℓ₂.val ≤ 2 ^ d := by
        calc (q₂.val + 1) * 2 ^ ℓ₂.val ≤ 2 ^ (d - ℓ₂.val) * 2 ^ ℓ₂.val :=
              Nat.mul_le_mul_right _ q₂.isLt
          _ = 2 ^ d := hPowEq
      rw [Nat.add_mul, Nat.one_mul] at hMul
      omega
    have hDiv1 : (ℓ₁.val * 2 ^ d + (q₁.val * 2 ^ ℓ₁.val + (2 ^ ℓ₁.val - 1))) / 2 ^ d = ℓ₁.val := by
      rw [Nat.mul_comm ℓ₁.val, Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt hj1, Nat.add_zero]
    have hDiv2 : (ℓ₂.val * 2 ^ d + (q₂.val * 2 ^ ℓ₂.val + (2 ^ ℓ₂.val - 1))) / 2 ^ d = ℓ₂.val := by
      rw [Nat.mul_comm ℓ₂.val, Nat.mul_add_div (Nat.two_pow_pos d), Nat.div_eq_of_lt hj2, Nat.add_zero]
    have hLEq : ℓ₁.val = ℓ₂.val := by rw [← hDiv1, ← hDiv2, hVal]
    have hLExt : ℓ₁ = ℓ₂ := Fin.ext hLEq
    subst hLExt
    have hJ : q₁.val * 2 ^ ℓ₁.val + (2 ^ ℓ₁.val - 1) = q₂.val * 2 ^ ℓ₁.val + (2 ^ ℓ₁.val - 1) := by
      omega
    have hPowPos : 0 < 2 ^ ℓ₁.val := Nat.two_pow_pos ℓ₁.val
    have hQEq : q₁.val = q₂.val := by
      have hMulEq : q₁.val * 2 ^ ℓ₁.val = q₂.val * 2 ^ ℓ₁.val := by omega
      exact Nat.eq_of_mul_eq_mul_right hPowPos hMulEq
    cases q₁; cases q₂
    simp only at hQEq
    subst hQEq
    rfl
  have hSurj : ∀ u ∈ R, ∃ p ∈ (Finset.univ : Finset Ix), toWire p = u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases (source_reachable_iff d u).mp hu.2 with ⟨ℓ, j, hℓ, hj, rfl, hjMod⟩
    have hPowPos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
    have hDivLt : j / 2 ^ ℓ < 2 ^ (d - ℓ) := by
      rw [Nat.div_lt_iff_lt_mul hPowPos, ← Nat.pow_add, Nat.sub_add_cancel hℓ]
      exact hj
    refine ⟨⟨⟨ℓ, Nat.lt_succ_of_le hℓ⟩, ⟨j / 2 ^ ℓ, hDivLt⟩⟩, Finset.mem_univ _, Fin.ext ?_⟩
    dsimp [toWire, bflyWire]
    have hDM := Nat.div_add_mod j (2 ^ ℓ)
    rw [hjMod] at hDM
    linarith [Nat.mul_comm (2 ^ ℓ) (j / 2 ^ ℓ)]
  have hCardEq : (Finset.univ : Finset Ix).card = R.card :=
    Finset.card_bij (fun p _ => toWire p) (fun p _ => hToMem p)
      (fun _ _ _ _ h => hInj h) (fun u hu =>
        let ⟨p, hp, hEq⟩ := hSurj u hu
        ⟨p, hp, hEq⟩)
  rw [Finset.card_univ] at hCardEq
  rw [← hCardEq]
  simp only [Ix, Fintype.card_sigma, Fintype.card_fin]
  have hReindex : ∑ ℓ : Fin (d + 1), 2 ^ (d - ℓ.val) = ∑ k ∈ Finset.range (d + 1), 2 ^ k := by
    rw [Fin.sum_univ_eq_sum_range (fun ℓ => 2 ^ (d - ℓ))]
    refine Finset.sum_bij (fun ℓ _ => d - ℓ) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro ℓ hℓ
      rw [Finset.mem_range] at hℓ ⊢
      omega
    · intro a ha b hb hEq
      rw [Finset.mem_range] at ha hb
      omega
    · intro k hk
      rw [Finset.mem_range] at hk
      exact ⟨d - k, Finset.mem_range.mpr (by omega), by omega⟩
  rw [hReindex, sum_two_pow_range]

/-- Tree formula extracting the unique reachable computation tree of `ButterflyNet.source d`. -/
def treeFormulaLayer (d ℓ q : Nat) (hℓ : ℓ ≤ d) (hq : q < 2 ^ (d - ℓ)) :
    BoolFormula (Fin (2 ^ d)) :=
  match ℓ with
  | 0 => .var ⟨q, by simpa using hq⟩
  | ℓ' + 1 =>
      have hPow : 2 ^ (d - ℓ') = 2 * 2 ^ (d - (ℓ' + 1)) := by
        have hSub : d - ℓ' = (d - (ℓ' + 1)) + 1 := by omega
        rw [hSub, Nat.pow_succ']
      have hq1 : 2 * q + 1 < 2 ^ (d - ℓ') := by rw [hPow]; omega
      have hq0 : 2 * q < 2 ^ (d - ℓ') := by rw [hPow]; omega
      let left := treeFormulaLayer d ℓ' (2 * q + 1) (Nat.le_of_lt hℓ) hq1
      let right := treeFormulaLayer d ℓ' (2 * q) (Nat.le_of_lt hℓ) hq0
      if ℓ' % 2 = 0 then .binary .and left right else .binary .or left right

/-- Canonical depth-`d` binary tree formula computed by `ButterflyNet.source d`. -/
def treeFormula (d : Nat) : BoolFormula (Fin (2 ^ d)) :=
  treeFormulaLayer d d 0 le_rfl (by simp)

/-- Linear-size tree circuit compressing `ButterflyNet.source d`. -/
def treeInstance (d : Nat) : CircuitInstance (2 ^ d) :=
  (treeFormula d).toCircuit id

private lemma treeFormulaLayer_gateCount (d ℓ q : Nat) (hℓ : ℓ ≤ d) (hq : q < 2 ^ (d - ℓ)) :
    (treeFormulaLayer d ℓ q hℓ hq).gateCount = 2 ^ ℓ - 1 := by
  induction ℓ generalizing q with
  | zero => simp [treeFormulaLayer, BoolFormula.gateCount]
  | succ ℓ' ih =>
      dsimp [treeFormulaLayer]
      split_ifs <;>
      · simp only [BoolFormula.gateCount, ih]
        have := Nat.two_pow_pos ℓ'
        rw [Nat.pow_succ']
        omega

private lemma bflyGate_eval_eq (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d)
    (v : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j) → Bool) :
    have hBase : LayeredRing.ringWires (2 ^ d) ℓ = (ℓ + 1) * 2 ^ d :=
      LayeredRing.ringWires_eq (2 ^ d) ℓ
    (bflyGate d ℓ j hℓ hj).eval v =
      if ℓ % 2 = 0 then
        v ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩ &&
          v ⟨ℓ * 2 ^ d + flipBit j ℓ, by
            rw [hBase]; have := flipBit_lt hj hℓ; nlinarith⟩
      else
        v ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩ ||
          v ⟨ℓ * 2 ^ d + flipBit j ℓ, by
            rw [hBase]; have := flipBit_lt hj hℓ; nlinarith⟩ := by
  dsimp [bflyGate]
  split_ifs <;> rfl

lemma flipBit_div_two_pow_pair (j ℓ : Nat) :
    (j / 2 ^ ℓ = 2 * (j / 2 ^ (ℓ + 1)) ∧ flipBit j ℓ / 2 ^ ℓ = 2 * (j / 2 ^ (ℓ + 1)) + 1) ∨
    (j / 2 ^ ℓ = 2 * (j / 2 ^ (ℓ + 1)) + 1 ∧ flipBit j ℓ / 2 ^ ℓ = 2 * (j / 2 ^ (ℓ + 1))) := by
  have hDivSucc : j / 2 ^ (ℓ + 1) = (j / 2 ^ ℓ) / 2 := by
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  by_cases hEven : j / 2 ^ ℓ % 2 = 0
  · refine Or.inl ⟨by omega, ?_⟩
    have hFlip : flipBit j ℓ = j + 2 ^ ℓ := by simp [flipBit, hEven]
    rw [hFlip, Nat.add_div_right _ (Nat.two_pow_pos ℓ)]
    omega
  · refine Or.inr ⟨by omega, ?_⟩
    have hFlip : flipBit j ℓ = j - 2 ^ ℓ := by simp [flipBit, hEven]
    have hGe : 2 ^ ℓ ≤ j := by
      by_contra hLt
      push Not at hLt
      have : j / 2 ^ ℓ = 0 := Nat.div_eq_of_lt hLt
      omega
    rw [hFlip, flipBit_div_two_pow_sub_one hGe]
    omega

private lemma appendBflyRow_evalWires_stable (d ℓ : Nat) (hℓ : ℓ < d)
    (prev : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (m : Nat) (hm : m ≤ 2 ^ d) (x : Fin (2 ^ d) → Bool)
    (u : Fin (LayeredRing.ringWires (2 ^ d) ℓ)) :
    (appendBflyRow d ℓ hℓ m hm prev).evalWires x ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ m)⟩ =
      prev.evalWires x u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [appendBflyRow]
      exact (Circuit.evalWires_snoc_castSucc _ _ x _).trans (ih (Nat.le_of_lt hm))

private lemma appendBflyRow_evalWires (d ℓ : Nat) (hℓ : ℓ < d)
    (prev : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (x : Fin (2 ^ d) → Bool)
    (hPrev : ∀ j (hj : j < 2 ^ d),
      prev.evalWires x ⟨ℓ * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
      (treeFormulaLayer d ℓ (j / 2 ^ ℓ) hℓ.le (by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ), ← Nat.pow_add, Nat.sub_add_cancel hℓ.le]
        exact hj)).eval x)
    (m : Nat) (hm : m ≤ 2 ^ d) :
    ∀ j (hj : j < m),
      (appendBflyRow d ℓ hℓ m hm prev).evalWires x ⟨(ℓ + 1) * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; omega⟩ =
      (treeFormulaLayer d (ℓ + 1) (j / 2 ^ (ℓ + 1)) hℓ (by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hℓ]
        exact Nat.lt_of_lt_of_le hj hm)).eval x := by
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
      intro j hj
      dsimp [appendBflyRow]
      have hBase := LayeredRing.ringWires_eq (2 ^ d) ℓ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
      · exact (Circuit.evalWires_snoc_castSucc _ _ x _).trans (ih (Nat.le_of_lt hm) j hjm)
      · have hLast : (⟨(ℓ + 1) * 2 ^ d + j, by rw [hBase]; omega⟩ :
            Fin (LayeredRing.ringWires (2 ^ d) ℓ + (j + 1))) = Fin.last _ := by
          apply Fin.ext; simp [hBase]
        rw [hLast]
        refine (Circuit.evalWires_snoc_last _ _ x).trans ?_
        rw [bflyGate_eval_eq]
        have hSt1 : (appendBflyRow d ℓ hℓ j (Nat.le_of_lt hm) prev).evalWires x
            ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩ =
            (treeFormulaLayer d ℓ (j / 2 ^ ℓ) hℓ.le (by
              rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ), ← Nat.pow_add, Nat.sub_add_cancel hℓ.le]
              exact hm)).eval x := by
          have hSt := appendBflyRow_evalWires_stable d ℓ hℓ prev j (Nat.le_of_lt hm) x
            ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩
          exact hSt.trans (hPrev j hm)
        have hFlipLt : flipBit j ℓ < 2 ^ d := flipBit_lt hm hℓ
        have hSt2 := appendBflyRow_evalWires_stable d ℓ hℓ prev j (Nat.le_of_lt hm) x
          ⟨ℓ * 2 ^ d + flipBit j ℓ, by rw [hBase]; nlinarith⟩
        have hSt2' : (appendBflyRow d ℓ hℓ j (Nat.le_of_lt hm) prev).evalWires x
            ⟨ℓ * 2 ^ d + flipBit j ℓ, by rw [hBase]; nlinarith⟩ =
            (treeFormulaLayer d ℓ (flipBit j ℓ / 2 ^ ℓ) hℓ.le (by
              rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos ℓ), ← Nat.pow_add, Nat.sub_add_cancel hℓ.le]
              exact hFlipLt)).eval x :=
          hSt2.trans (hPrev (flipBit j ℓ) hFlipLt)
        rw [hSt1, hSt2']
        dsimp [treeFormulaLayer, BoolFormula.eval]
        rcases flipBit_div_two_pow_pair j ℓ with ⟨hq1, hq2⟩ | ⟨hq1, hq2⟩
        · simp only [hq1, hq2]
          split_ifs
          · simp only [BoolFormula.eval, BinaryGate.eval]
            exact Bool.and_comm _ _
          · simp only [BoolFormula.eval, BinaryGate.eval]
            exact Bool.or_comm _ _
        · simp only [hq1, hq2]
          split_ifs <;> rfl

private lemma buildBfly_evalWires_layer (d : Nat) (x : Fin (2 ^ d) → Bool) :
    ∀ D (hD : D ≤ d) (j : Nat) (hj : j < 2 ^ d),
      (buildBfly d D hD).evalWires x ⟨D * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
      (treeFormulaLayer d D (j / 2 ^ D) hD (by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos D), ← Nat.pow_add, Nat.sub_add_cancel hD]
        exact hj)).eval x
  | 0, _, j, hj => by
      simp [buildBfly, Circuit.evalWires, treeFormulaLayer, BoolFormula.eval]
      rfl
  | D + 1, hD, j, hj => by
      dsimp [buildBfly]
      exact (appendBflyRow_evalWires d D hD (buildBfly d D (Nat.le_of_lt hD)) x
        (buildBfly_evalWires_layer d x D (Nat.le_of_lt hD)) (2 ^ d) le_rfl j hj)

theorem source_eval_eq_treeFormula (d : Nat) (x : Fin (2 ^ d) → Bool) :
    (source d).eval x = (treeFormula d).eval x := by
  change (buildBfly d d le_rfl).evalWires x (source d).output = _
  rw [source_output_eq_bflyWire]
  have hj : 2 ^ d - 1 < 2 ^ d := Nat.sub_lt (Nat.two_pow_pos d) Nat.zero_lt_one
  have hEval := buildBfly_evalWires_layer d x d le_rfl (2 ^ d - 1) hj
  have hDiv0 : (2 ^ d - 1) / 2 ^ d = 0 := Nat.div_eq_of_lt hj
  have hWireEq : bflyWire d d (2 ^ d - 1) le_rfl hj =
      ⟨d * 2 ^ d + (2 ^ d - 1), by
        change d * 2 ^ d + (2 ^ d - 1) < LayeredRing.ringWires (2 ^ d) d
        rw [LayeredRing.ringWires_eq]
        nlinarith⟩ := rfl
  refine (congrArg ((buildBfly d d le_rfl).evalWires x) hWireEq).trans (hEval.trans ?_)
  simp only [treeFormula, hDiv0]

/-- Because `ButterflyNet.source d` has only `2 * 2^d - 1` reachable wires arranged as a
tree formula with zero shared fanout, it compresses into `2 * 2^d - 1` wires and `O(2^d)`
CNF size. -/
theorem source_linear_compression :
    CircuitCompressionTask (fun d => 2 ^ d) source treeInstance where
  inputsGrow := Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun d hd =>
    le_trans hd (le_of_lt (Nat.lt_two_pow_self (n := d)))⟩
  sourceSize := by
    refine ⟨1, 1, by decide, by decide, fun d _ => ?_⟩
    have hGates : (source d).circuit.gateCount = d * 2 ^ d := by
      have hW := (source d).circuit.wires_eq_inputs_add_gateCount
      have hR : (source d).wires = (d + 1) * 2 ^ d := LayeredRing.ringWires_eq (2 ^ d) d
      have hEq : (d + 1) * 2 ^ d = 2 ^ d + (source d).circuit.gateCount := by
        simpa using hR.symm.trans hW
      have hMul : (d + 1) * 2 ^ d = d * 2 ^ d + 2 ^ d := by ring
      omega
    have hLog : (2 ^ d).log2 = d := Nat.log2_two_pow
    rw [hGates, hLog, Nat.one_mul, Nat.one_mul, Nat.mul_comm]
    exact ⟨le_rfl, le_rfl⟩
  equivalent d input := by
    dsimp [treeInstance]
    rw [BoolFormula.eval_toCircuit]
    exact (source_eval_eq_treeFormula d input).symm
  exactCount d := by
    refine ⟨?_⟩
    have hEqv : Models (treeInstance d).cnf ≃ (treeInstance d).Accepting :=
      (treeInstance d).circuit.acceptingAssignmentsEquiv (treeInstance d).output
    have hEqFun : ∀ x, (treeInstance d).eval x = (source d).eval x := fun x => by
      dsimp [treeInstance]; rw [BoolFormula.eval_toCircuit]; exact (source_eval_eq_treeFormula d x).symm
    exact hEqv.trans (Equiv.subtypeEquiv (Equiv.refl _) fun x => by
      change (treeInstance d).eval x = true ↔ (source d).eval x = true
      rw [hEqFun x])
  variableBound := by
    refine ⟨2, fun d => ?_⟩
    have hW : (treeInstance d).wires = 2 ^ d + (treeInstance d).circuit.gateCount :=
      (treeInstance d).circuit.wires_eq_inputs_add_gateCount
    have hG : (treeInstance d).circuit.gateCount = (treeFormula d).gateCount :=
      BoolFormula.gateCount_toCircuit (treeFormula d) id
    rw [hW, hG, treeFormula, treeFormulaLayer_gateCount]
    omega
  clauses := by
    refine ⟨3, fun d => ?_⟩
    have hEnc : (treeInstance d).cnf.clauses.size ≤ 3 * (treeInstance d).circuit.gateCount + 1 :=
      (treeInstance d).circuit.encode_size (treeInstance d).output
    have hG : (treeInstance d).circuit.gateCount = (treeFormula d).gateCount :=
      BoolFormula.gateCount_toCircuit (treeFormula d) id
    rw [hG, treeFormula, treeFormulaLayer_gateCount] at hEnc
    have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
    omega
  width d clause hClause :=
    (treeInstance d).circuit.encode_width (treeInstance d).output hClause
  subexponential C D := by
    refine logTimeBudget_isLittleO (Filter.tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun d hd => le_trans hd (le_of_lt (Nat.lt_two_pow_self (n := d)))⟩) ?_ 2 ?_ C D
    · intro d
      exact (treeInstance d).circuit.inputs_le_wires
    · intro d
      have hW : (treeInstance d).wires = 2 ^ d + (treeInstance d).circuit.gateCount :=
        (treeInstance d).circuit.wires_eq_inputs_add_gateCount
      have hG : (treeInstance d).circuit.gateCount = (treeFormula d).gateCount :=
        BoolFormula.gateCount_toCircuit (treeFormula d) id
      rw [hW, hG, treeFormula, treeFormulaLayer_gateCount]
      omega

/-- Exact satisfying-assignment count recurrence for `ButterflyNet.source d`:
`A(0) = 1`, `A(ℓ+1) = A(ℓ)^2` when `ℓ` is even (`AND`), and
`A(ℓ+1) = 2 * 2^(2^ℓ) * A(ℓ) - A(ℓ)^2` when `ℓ` is odd (`OR`). -/
def bflyTreeCount : Nat → Nat
  | 0 => 1
  | ℓ + 1 =>
      if ℓ % 2 = 0 then
        bflyTreeCount ℓ * bflyTreeCount ℓ
      else
        2 * 2 ^ (2 ^ ℓ) * bflyTreeCount ℓ - bflyTreeCount ℓ * bflyTreeCount ℓ

private lemma bflyTreeCount_le (ℓ : Nat) : bflyTreeCount ℓ ≤ 2 ^ (2 ^ ℓ) := by
  induction ℓ with
  | zero => decide
  | succ ℓ ih =>
      dsimp [bflyTreeCount]
      have hPow : 2 ^ (2 ^ (ℓ + 1)) = 2 ^ (2 ^ ℓ) * 2 ^ (2 ^ ℓ) := by
        rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
      rw [hPow]
      split_ifs
      · exact Nat.mul_le_mul ih ih
      · set N := 2 ^ (2 ^ ℓ)
        set A := bflyTreeCount ℓ
        have hSub : A * A ≤ 2 * N * A := by
          have : A ≤ 2 * N := le_trans ih (by omega)
          exact Nat.mul_le_mul_right A this
        have h1 : (N - A) * (N - A) + (2 * N * A - A * A) = N * N := by
          zify [ih, hSub]
          ring
        omega

private def mapFormula {α β : Type} (f : α → β) : BoolFormula α → BoolFormula β
  | .var a => .var (f a)
  | .not p => .not (mapFormula f p)
  | .binary g p q => .binary g (mapFormula f p) (mapFormula f q)

private lemma eval_mapFormula {α β : Type} (f : α → β) (v : β → Bool) (φ : BoolFormula α) :
    (mapFormula f φ).eval v = φ.eval (v ∘ f) := by
  induction φ with
  | var a => rfl
  | not p ih => simp [mapFormula, BoolFormula.eval, ih]
  | binary g p q ihp ihq => simp [mapFormula, BoolFormula.eval, ihp, ihq]

private def canonicalLayerFormula : (ℓ : Nat) → BoolFormula (Fin (2 ^ ℓ))
  | 0 => .var ⟨0, by decide⟩
  | ℓ + 1 =>
      let shiftHi : Fin (2 ^ ℓ) → Fin (2 ^ (ℓ + 1)) := fun k =>
        ⟨2 ^ ℓ + k.val, by rw [Nat.pow_succ, Nat.mul_two]; omega⟩
      let shiftLo : Fin (2 ^ ℓ) → Fin (2 ^ (ℓ + 1)) := fun k =>
        ⟨k.val, by rw [Nat.pow_succ, Nat.mul_two]; omega⟩
      let left := mapFormula shiftHi (canonicalLayerFormula ℓ)
      let right := mapFormula shiftLo (canonicalLayerFormula ℓ)
      if ℓ % 2 = 0 then .binary .and left right else .binary .or left right

private lemma treeFormulaLayer_eval_eq_canonical (d ℓ q : Nat) (hℓ : ℓ ≤ d) (hq : q < 2 ^ (d - ℓ))
    (x : Fin (2 ^ d) → Bool) :
    (treeFormulaLayer d ℓ q hℓ hq).eval x =
      (canonicalLayerFormula ℓ).eval (fun k : Fin (2 ^ ℓ) =>
        x ⟨q * 2 ^ ℓ + k.val, by
          have h1 : q * 2 ^ ℓ + k.val < (q + 1) * 2 ^ ℓ := by
            rw [Nat.add_mul, Nat.one_mul]; omega
          have h2 : (q + 1) * 2 ^ ℓ ≤ 2 ^ (d - ℓ) * 2 ^ ℓ :=
            Nat.mul_le_mul_right _ hq
          have h3 : 2 ^ (d - ℓ) * 2 ^ ℓ = 2 ^ d := by
            rw [← Nat.pow_add, Nat.sub_add_cancel hℓ]
          omega⟩) := by
  induction ℓ generalizing q with
  | zero =>
      simp [treeFormulaLayer, canonicalLayerFormula, BoolFormula.eval]
  | succ ℓ' ih =>
      dsimp [treeFormulaLayer, canonicalLayerFormula]
      split_ifs <;> simp only [BoolFormula.eval, eval_mapFormula, BinaryGate.eval]
      · congr 1
        · rw [ih (2 * q + 1) (Nat.le_of_lt hℓ) _]
          congr 1; funext k; congr 1; apply Fin.ext
          dsimp [Function.comp]; rw [Nat.pow_succ]; ring
        · rw [ih (2 * q) (Nat.le_of_lt hℓ) _]
          congr 1; funext k; congr 1; apply Fin.ext
          dsimp [Function.comp]; rw [Nat.pow_succ]; ring
      · congr 1
        · rw [ih (2 * q + 1) (Nat.le_of_lt hℓ) _]
          congr 1; funext k; congr 1; apply Fin.ext
          dsimp [Function.comp]; rw [Nat.pow_succ]; ring
        · rw [ih (2 * q) (Nat.le_of_lt hℓ) _]
          congr 1; funext k; congr 1; apply Fin.ext
          dsimp [Function.comp]; rw [Nat.pow_succ]; ring

private def splitVecEquiv (ℓ : Nat) :
    (Fin (2 ^ (ℓ + 1)) → Bool) ≃ (Fin (2 ^ ℓ) → Bool) × (Fin (2 ^ ℓ) → Bool) where
  toFun y :=
    (fun k => y ⟨2 ^ ℓ + k.val, by rw [Nat.pow_succ, Nat.mul_two]; omega⟩,
     fun k => y ⟨k.val, by rw [Nat.pow_succ, Nat.mul_two]; omega⟩)
  invFun p i :=
    if h : i.val < 2 ^ ℓ then p.2 ⟨i.val, h⟩
    else p.1 ⟨i.val - 2 ^ ℓ, by
      have hi : i.val < 2 ^ (ℓ + 1) := i.isLt
      have hMul : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := Nat.pow_succ'
      omega⟩
  left_inv y := by
    funext i
    by_cases h : i.val < 2 ^ ℓ
    · simp [h]
    · simp [h, Nat.add_sub_cancel' (Nat.le_of_not_gt h)]
  right_inv p := by
    ext k
    · have hNot : ¬ (2 ^ ℓ + k.val < 2 ^ ℓ) := by omega
      simp [hNot]
    · simp [k.isLt]

private lemma canonicalLayerFormula_count (ℓ : Nat) :
    open Classical in
    (Finset.univ.filter (fun y : Fin (2 ^ ℓ) → Bool =>
      (canonicalLayerFormula ℓ).eval y = true)).card = bflyTreeCount ℓ := by
  classical
  induction ℓ with
  | zero =>
      let e0 : (Fin (2 ^ 0) → Bool) ≃ Bool :=
        ⟨fun y => y ⟨0, by decide⟩, fun b _ => b,
         fun y => funext fun i => by fin_cases i; rfl, fun _ => rfl⟩
      have hCard : (Finset.univ.filter (fun y : Fin (2 ^ 0) → Bool =>
          (canonicalLayerFormula 0).eval y = true)).card =
          (Finset.univ.filter (fun b : Bool => b = true)).card := by
        refine Finset.card_bij (fun y _ => e0 y) ?_ ?_ ?_
        · intro y hy
          rw [Finset.mem_filter] at hy ⊢
          exact ⟨Finset.mem_univ _, by simpa [canonicalLayerFormula, BoolFormula.eval, e0] using hy.2⟩
        · intro a _ b _ h; exact e0.injective h
        · intro b hb
          rw [Finset.mem_filter] at hb
          refine ⟨e0.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e0.apply_symm_apply b⟩
          simpa [canonicalLayerFormula, BoolFormula.eval, e0] using hb.2
      rw [hCard]
      decide
  | succ ℓ ih =>
      let S : Finset (Fin (2 ^ ℓ) → Bool) :=
        Finset.univ.filter (fun y => (canonicalLayerFormula ℓ).eval y = true)
      have hCardS : S.card = bflyTreeCount ℓ := ih
      let P : Finset ((Fin (2 ^ ℓ) → Bool) × (Fin (2 ^ ℓ) → Bool)) :=
        Finset.univ.filter (fun p =>
          if ℓ % 2 = 0 then
            (canonicalLayerFormula ℓ).eval p.1 = true ∧ (canonicalLayerFormula ℓ).eval p.2 = true
          else
            (canonicalLayerFormula ℓ).eval p.1 = true ∨ (canonicalLayerFormula ℓ).eval p.2 = true)
      have hBij : (Finset.univ.filter (fun y : Fin (2 ^ (ℓ + 1)) → Bool =>
          (canonicalLayerFormula (ℓ + 1)).eval y = true)).card = P.card := by
        refine Finset.card_bij (fun y _ => splitVecEquiv ℓ y) ?_ ?_ ?_
        · intro y hy
          rw [Finset.mem_filter] at hy ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          dsimp [canonicalLayerFormula] at hy
          split_ifs at hy ⊢
          · simp only [BoolFormula.eval, eval_mapFormula, BinaryGate.eval, Bool.and_eq_true] at hy
            exact ⟨hy.2.1, hy.2.2⟩
          · simp only [BoolFormula.eval, eval_mapFormula, BinaryGate.eval, Bool.or_eq_true] at hy
            exact hy.2
        · intro a _ b _ h; exact (splitVecEquiv ℓ).injective h
        · intro p hp
          rw [Finset.mem_filter] at hp
          refine ⟨(splitVecEquiv ℓ).symm p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
            (splitVecEquiv ℓ).apply_symm_apply p⟩
          have hEq := (splitVecEquiv ℓ).apply_symm_apply p
          have hP1 : (splitVecEquiv ℓ ((splitVecEquiv ℓ).symm p)).1 = p.1 := congrArg Prod.fst hEq
          have hP2 : (splitVecEquiv ℓ ((splitVecEquiv ℓ).symm p)).2 = p.2 := congrArg Prod.snd hEq
          dsimp [canonicalLayerFormula]
          split_ifs at hp ⊢
          · simp only [BoolFormula.eval, eval_mapFormula, BinaryGate.eval, Bool.and_eq_true]
            change (canonicalLayerFormula ℓ).eval (splitVecEquiv ℓ ((splitVecEquiv ℓ).symm p)).1 = true ∧
              (canonicalLayerFormula ℓ).eval (splitVecEquiv ℓ ((splitVecEquiv ℓ).symm p)).2 = true
            rw [hP1, hP2]
            exact hp.2
          · simp only [BoolFormula.eval, eval_mapFormula, BinaryGate.eval, Bool.or_eq_true]
            change (canonicalLayerFormula ℓ).eval (splitVecEquiv ℓ ((splitVecEquiv ℓ).symm p)).1 = true ∨
              (canonicalLayerFormula ℓ).eval (splitVecEquiv ℓ ((splitVecEquiv ℓ).symm p)).2 = true
            rw [hP1, hP2]
            exact hp.2
      rw [hBij]
      dsimp [bflyTreeCount]
      split_ifs with hEven
      · have hProd : P = S ×ˢ S := by
          ext p
          simp [P, S, hEven]
        rw [hProd, Finset.card_product, hCardS]
      · let U : Finset (Fin (2 ^ ℓ) → Bool) := Finset.univ
        let Sc : Finset (Fin (2 ^ ℓ) → Bool) := U \ S
        have hScCard : Sc.card = 2 ^ (2 ^ ℓ) - bflyTreeCount ℓ := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), hCardS]
          simp
        have hComp : (U ×ˢ U) \ P = Sc ×ˢ Sc := by
          ext p
          simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_univ, true_and,
            P, S, Sc, U, Finset.mem_filter, hEven, ↓reduceIte]
          tauto
        have hPSub : P ⊆ U ×ˢ U := Finset.subset_univ P
        have hTotal : (U ×ˢ U).card = 2 ^ (2 ^ ℓ) * 2 ^ (2 ^ ℓ) := by
          rw [Finset.card_product]
          simp [U]
        have hSdiff : (U ×ˢ U).card - P.card = Sc.card * Sc.card := by
          rw [← Finset.card_sdiff_of_subset hPSub, hComp, Finset.card_product]
        have hBound := bflyTreeCount_le ℓ
        have hPcardLe : P.card ≤ (U ×ˢ U).card := Finset.card_le_card hPSub
        rw [hScCard, hTotal] at hSdiff
        set N := 2 ^ (2 ^ ℓ)
        set A := bflyTreeCount ℓ
        have hSub : A * A ≤ 2 * N * A := by
          have : A ≤ 2 * N := le_trans hBound (by omega)
          exact Nat.mul_le_mul_right A this
        have hId : (N - A) * (N - A) + (2 * N * A - A * A) = N * N := by
          zify [hBound, hSub]
          ring
        omega

/-- Exact closed-form count of accepting assignments for `ButterflyNet.source d`:
`Fintype.card (source d).Accepting = bflyTreeCount d`. -/
theorem source_acceptCount_eq_treeCount (d : Nat) :
    Fintype.card (source d).Accepting = bflyTreeCount d := by
  classical
  unfold CircuitInstance.Accepting
  rw [Fintype.card_subtype]
  have hEq : (Finset.univ.filter (fun x : Fin (2 ^ d) → Bool => (source d).eval x = true)) =
      Finset.univ.filter (fun x : Fin (2 ^ d) → Bool => (canonicalLayerFormula d).eval x = true) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hCan := treeFormulaLayer_eval_eq_canonical d d 0 le_rfl (by simp) x
    have hEqArg : (fun k : Fin (2 ^ d) => x ⟨0 * 2 ^ d + k.val,
        by rw [Nat.zero_mul, Nat.zero_add]; exact k.isLt⟩) = x :=
      funext fun k => congrArg x (Fin.ext (by simp))
    have hCan' : (treeFormulaLayer d d 0 le_rfl (by simp)).eval x =
        (canonicalLayerFormula d).eval x := by
      refine hCan.trans (congrArg (fun v => (canonicalLayerFormula d).eval v) ?_)
      funext k
      congr 1
      exact Fin.ext (by simp)
    rw [source_eval_eq_treeFormula, treeFormula, hCan']
  rw [hEq, canonicalLayerFormula_count d]

end ButterflyNet

namespace ClosedComparatorXor

/-- Total wires in the comparator butterfly stage `(d + 1) * 2 ^ d`. -/
def bflyWires (d : Nat) : Nat := (d + 1) * 2 ^ d

/-- Total wires in `ClosedComparatorXor.source d`: `(d + 2) * 2 ^ d - 1`. -/
def totalWires (d : Nat) : Nat := (d + 2) * 2 ^ d - 1

/-- Wire index for butterfly node `(ℓ, j)` (`ℓ ≤ d`, `j < 2^d`). -/
def compWire (d ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d) :
    Fin (LayeredRing.ringWires (2 ^ d) d) :=
  ⟨ℓ * 2 ^ d + j, by
    rw [LayeredRing.ringWires_eq]
    have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
    have h2 : (ℓ + 1) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (Nat.succ_le_succ hℓ)
    omega⟩

/-- Comparator cell gate at butterfly layer `ℓ`, wire `j`:
`AND` when bit `ℓ` of `j` is `0`, `OR` when bit `ℓ` of `j` is `1`. -/
def compGate (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    HybridGate (LayeredRing.ringWires (2 ^ d) ℓ + j) :=
  let N := 2 ^ d
  have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
  have hfLt : ButterflyNet.flipBit j ℓ < N := ButterflyNet.flipBit_lt hj hℓ
  let w1 : Fin (LayeredRing.ringWires N ℓ + j) :=
    ⟨ℓ * N + j, by rw [hBase]; nlinarith⟩
  let w2 : Fin (LayeredRing.ringWires N ℓ + j) :=
    ⟨ℓ * N + ButterflyNet.flipBit j ℓ, by rw [hBase]; nlinarith⟩
  if j.testBit ℓ = false then HybridGate.and w1 w2 else HybridGate.or w1 w2

/-- Appends `m` comparator gates for row `ℓ` (`0 ≤ m ≤ 2^d`). -/
def appendCompRow (d ℓ : Nat) (hℓ : ℓ < d)
    (m : Nat) (hm : m ≤ 2 ^ d)
    (prev : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) :
    HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ + m) :=
  match m with
  | 0 => prev
  | m' + 1 =>
      (appendCompRow d ℓ hℓ m' (Nat.le_of_lt hm) prev).snoc (compGate d ℓ m' hℓ hm)

/-- Builds the `D`-layer comparator butterfly (`0 ≤ D ≤ d`). -/
def buildCompBfly (d : Nat) :
    ∀ D, D ≤ d → HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) D)
  | 0, _ => HybridCircuit.inputsOnly
  | D + 1, hD =>
      appendCompRow d D hD (2 ^ d) le_rfl (buildCompBfly d D (Nat.le_of_lt hD))

/-- Wire index function in `totalWires d` for balanced XOR heap nodes `1 ≤ h < 2^(d+1)`:
for internal XOR nodes `1 ≤ h < 2^d`, maps `h ↦ (d + 2) * 2^d - 1 - h`;
for leaves `2^d ≤ h < 2^(d+1)`, maps `h ↦ d * 2^d + (h - 2^d)`. -/
def heapWireVal (d h : Nat) : Nat :=
  if h < 2 ^ d then (d + 2) * 2 ^ d - 1 - h
  else d * 2 ^ d + (h - 2 ^ d)

lemma heapWireVal_lt_xorStep (d m h : Nat) (hm : m < 2 ^ d - 1)
    (hh1 : h = 2 * (2 ^ d - 1 - m) ∨ h = 2 * (2 ^ d - 1 - m) + 1) :
    heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
  have hBase : LayeredRing.ringWires (2 ^ d) d = (d + 1) * 2 ^ d :=
    LayeredRing.ringWires_eq (2 ^ d) d
  rw [hBase]
  set p := 2 ^ d - 1 - m
  have hp1 : 1 ≤ p := by omega
  have hp2 : p ≤ 2 ^ d - 1 := by omega
  have hLt2 : h < 2 ^ (d + 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
    omega
  dsimp [heapWireVal]
  split_ifs with hSmall
  · have hP : p < h := by omega
    have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
    omega
  · have hMul : d * 2 ^ d + 2 ^ d = (d + 1) * 2 ^ d := by ring
    omega

/-- Appends `m` XOR reduction gates (`0 ≤ m ≤ 2^d - 1`) on top of the comparator butterfly,
wiring internal heap node `p = 2^d - 1 - m` to `2*p` and `2*p + 1`. -/
def appendXorGates (d : Nat) :
    ∀ m, m ≤ 2 ^ d - 1 → HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) d + m)
  | 0, _ => buildCompBfly d d le_rfl
  | m + 1, hm =>
      let prev := appendXorGates d m (Nat.le_of_lt hm)
      let p := 2 ^ d - 1 - m
      let g : HybridGate (LayeredRing.ringWires (2 ^ d) d + m) :=
        HybridGate.xor
          ⟨heapWireVal d (2 * p), heapWireVal_lt_xorStep d m (2 * p) hm (Or.inl rfl)⟩
          ⟨heapWireVal d (2 * p + 1), heapWireVal_lt_xorStep d m (2 * p + 1) hm (Or.inr rfl)⟩
      prev.snoc g

/-- Closed single-output comparator-XOR butterfly circuit instance on `2^d` inputs. -/
def source (d : Nat) : HybridCircuitInstance (2 ^ d) where
  wires := LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1)
  circuit := appendXorGates d (2 ^ d - 1) le_rfl
  output := ⟨LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) - 1, by
    have hBase := LayeredRing.ringWires_eq (2 ^ d) d
    have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
    have hWPos : 1 ≤ (d + 1) * 2 ^ d :=
      le_trans hPos (Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d))
    omega⟩

lemma source_wires_eq (d : Nat) : (source d).wires = totalWires d := by
  change LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) = (d + 2) * 2 ^ d - 1
  rw [LayeredRing.ringWires_eq]
  have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hMul : (d + 1) * 2 ^ d + 2 ^ d = (d + 2) * 2 ^ d := by ring
  omega

lemma source_output_val (d : Nat) : (source d).output.val = heapWireVal d 1 := by
  change LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) - 1 = heapWireVal d 1
  rw [LayeredRing.ringWires_eq]
  dsimp [heapWireVal]
  by_cases hd : d = 0
  · subst hd; decide
  · have hGt : 1 < 2 ^ d := Nat.one_lt_two_pow hd
    simp only [hGt, ↓reduceIte]
    have hMul : (d + 1) * 2 ^ d + 2 ^ d = (d + 2) * 2 ^ d := by ring
    omega

/-- Butterfly wire `(ℓ, j)` inside `ClosedComparatorXor.source d`. -/
def compWireInSource (d ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d) : Fin (source d).wires :=
  ⟨ℓ * 2 ^ d + j, by
    change _ < LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1)
    rw [LayeredRing.ringWires_eq]
    have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
    have h2 : (ℓ + 1) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (Nat.succ_le_succ hℓ)
    omega⟩

private lemma compGate_uses_iff (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d)
    (a : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j)) :
    HybridGateUsesWire (compGate d ℓ j hℓ hj) a ↔
      a.val = ℓ * 2 ^ d + j ∨ a.val = ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ := by
  dsimp [compGate]
  split_ifs
  · constructor
    · intro h
      cases h <;> simp
    · rintro (h1 | h2)
      · exact (congrArg (HybridGateUsesWire _) (Fin.ext h1.symm)).mp (HybridGateUsesWire.and_left _ _)
      · exact (congrArg (HybridGateUsesWire _) (Fin.ext h2.symm)).mp (HybridGateUsesWire.and_right _ _)
  · constructor
    · intro h
      cases h <;> simp
    · rintro (h1 | h2)
      · exact (congrArg (HybridGateUsesWire _) (Fin.ext h1.symm)).mp (HybridGateUsesWire.or_left _ _)
      · exact (congrArg (HybridGateUsesWire _) (Fin.ext h2.symm)).mp (HybridGateUsesWire.or_right _ _)

private lemma appendCompRow_directedEdge_of_bflyStep (d ℓ : Nat) (hℓ : ℓ < d)
    (prev : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (hPrev : ∀ u v : Fin (LayeredRing.ringWires (2 ^ d) ℓ),
      ButterflyNet.BflyStep d ℓ u.val v.val → prev.DirectedEdge u v)
    (m : Nat) (hm : m ≤ 2 ^ d) :
    ∀ u v : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m),
      (ButterflyNet.BflyStep d ℓ u.val v.val ∨
        (∃ j < m, v.val = (ℓ + 1) * 2 ^ d + j ∧
          (u.val = ℓ * 2 ^ d + j ∨ u.val = ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ))) →
      (appendCompRow d ℓ hℓ m hm prev).DirectedEdge u v := by
  induction m with
  | zero =>
      intro u v h
      rcases h with hB | ⟨j, hj, _⟩
      · exact hPrev u v hB
      · omega
  | succ m ih =>
      intro u v h
      dsimp [appendCompRow]
      have hm' : m ≤ 2 ^ d := Nat.le_of_lt hm
      have hBase : LayeredRing.ringWires (2 ^ d) ℓ = (ℓ + 1) * 2 ^ d :=
        LayeredRing.ringWires_eq (2 ^ d) ℓ
      rcases h with hB | ⟨j, hj, hv, hu⟩
      · have hVlt : v.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
          rcases hB with ⟨ℓ', j', hℓ', hj', hv', _⟩
          have h1 : (ℓ' + 1) * 2 ^ d ≤ ℓ * 2 ^ d := Nat.mul_le_mul_right _ hℓ'
          have h2 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
          omega
        have hUlt : u.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
          rcases hB with ⟨ℓ', j', hℓ', hj', _, hu1 | hu2⟩
          · have : ℓ' * 2 ^ d ≤ ℓ * 2 ^ d := Nat.mul_le_mul_right _ hℓ'.le
            nlinarith
          · have : ℓ' * 2 ^ d ≤ ℓ * 2 ^ d := Nat.mul_le_mul_right _ hℓ'.le
            have : ButterflyNet.flipBit j' ℓ' < 2 ^ d :=
              ButterflyNet.flipBit_lt hj' (Nat.lt_trans hℓ' hℓ)
            nlinarith
        let u' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨u.val, hUlt⟩
        let v' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨v.val, hVlt⟩
        exact HybridCircuit.directedEdge_snoc_castSucc (ih hm' u' v' (Or.inl hB))
      · by_cases hjm : j < m
        · have hVlt : v.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by omega
          have hUlt : u.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
            have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            rcases hu with hu1 | hu2
            · omega
            · have := ButterflyNet.flipBit_lt (Nat.lt_trans hjm hm) hℓ
              omega
          let u' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨u.val, hUlt⟩
          let v' : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨v.val, hVlt⟩
          exact HybridCircuit.directedEdge_snoc_castSucc (ih hm' u' v' (Or.inr ⟨j, hjm, hv, hu⟩))
        · have hEq : j = m := by omega
          subst j
          have hvLast : v = Fin.last _ := Fin.ext (by simp [hBase, hv])
          have hUlt : u.val < LayeredRing.ringWires (2 ^ d) ℓ + m := by
            have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            rcases hu with hu1 | hu2
            · omega
            · have := ButterflyNet.flipBit_lt hm hℓ
              omega
          let a : Fin (LayeredRing.ringWires (2 ^ d) ℓ + m) := ⟨u.val, hUlt⟩
          have ha : HybridGateUsesWire (compGate d ℓ m hℓ hm) a :=
            (compGate_uses_iff d ℓ m hℓ hm a).mpr hu
          subst hvLast
          exact HybridCircuit.directedEdge_snoc_last ha

lemma buildCompBfly_directedEdge_of_bflyStep (d : Nat) :
    ∀ D (hD : D ≤ d) (u v : Fin (LayeredRing.ringWires (2 ^ d) D)),
      ButterflyNet.BflyStep d D u.val v.val → (buildCompBfly d D hD).DirectedEdge u v
  | 0, _, _, _, ⟨_, _, hℓ, _⟩ => by omega
  | D + 1, hD, u, v, ⟨ℓ, j, hℓ, hj, hv, hu⟩ => by
      dsimp [buildCompBfly]
      refine appendCompRow_directedEdge_of_bflyStep d D hD _
        (buildCompBfly_directedEdge_of_bflyStep d D (Nat.le_of_lt hD)) (2 ^ d) le_rfl u v ?_
      rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with hLt | rfl
      · exact Or.inl ⟨ℓ, j, hLt, hj, hv, hu⟩
      · exact Or.inr ⟨j, hj, hv, hu⟩

private lemma appendXorGates_directedEdge_of_prev (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    {u v : Fin (LayeredRing.ringWires (2 ^ d) d)}
    (h : (buildCompBfly d d le_rfl).DirectedEdge u v) :
    (appendXorGates d m hm).DirectedEdge
      ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ m)⟩
      ⟨v.val, Nat.lt_of_lt_of_le v.isLt (Nat.le_add_right _ m)⟩ := by
  induction m with
  | zero => exact h
  | succ m ih =>
      dsimp [appendXorGates]
      exact HybridCircuit.directedEdge_snoc_castSucc (ih (Nat.le_of_lt hm))

private lemma appendXorGates_directedEdge_step (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    (h : Nat) (hh1 : 2 ≤ h) (hh2 : 2 ^ d - m ≤ h / 2) (hh3 : h < 2 ^ (d + 1)) :
    have hBase : LayeredRing.ringWires (2 ^ d) d = (d + 1) * 2 ^ d :=
      LayeredRing.ringWires_eq (2 ^ d) d
    have hU : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
      rw [hBase]
      dsimp [heapWireVal]
      have hMul1 : d * 2 ^ d + 2 ^ d = (d + 1) * 2 ^ d := by ring
      have hMul2 : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      split_ifs <;> omega
    have hV : heapWireVal d (h / 2) < LayeredRing.ringWires (2 ^ d) d + m := by
      rw [hBase]
      have hSub : h / 2 < 2 ^ d := by
        rw [Nat.pow_succ, Nat.mul_two] at hh3
        omega
      dsimp [heapWireVal]
      simp only [hSub, ↓reduceIte]
      have hMul2 : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      omega
    (appendXorGates d m hm).DirectedEdge ⟨heapWireVal d h, hU⟩ ⟨heapWireVal d (h / 2), hV⟩ := by
  induction m with
  | zero => omega
  | succ m ih =>
      intro hBase hU hV
      dsimp [appendXorGates]
      set p := 2 ^ d - 1 - m
      by_cases hEq : h / 2 = p
      · have hStep : heapWireVal d (h / 2) = LayeredRing.ringWires (2 ^ d) d + m := by
          rw [hBase, hEq]
          have hpLt : p < 2 ^ d := by
            have := Nat.two_pow_pos d
            omega
          dsimp [heapWireVal]
          simp only [hpLt, ↓reduceIte]
          have hMul2 : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
          omega
        have hvLast : (⟨heapWireVal d (h / 2), hV⟩ :
            Fin (LayeredRing.ringWires (2 ^ d) d + (m + 1))) = Fin.last _ :=
          Fin.ext (by simp [hStep])
        have hULT : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
          have : h = 2 * p ∨ h = 2 * p + 1 := by omega
          exact heapWireVal_lt_xorStep d m h hm this
        have hUses : HybridGateUsesWire
            (HybridGate.xor
              ⟨heapWireVal d (2 * p), heapWireVal_lt_xorStep d m (2 * p) hm (Or.inl rfl)⟩
              ⟨heapWireVal d (2 * p + 1), heapWireVal_lt_xorStep d m (2 * p + 1) hm (Or.inr rfl)⟩)
            ⟨heapWireVal d h, hULT⟩ := by
          rcases (show h = 2 * p ∨ h = 2 * p + 1 by omega) with hL | hR
          · exact (congrArg (HybridGateUsesWire _) (Fin.ext (by simp [hL]))).mpr
              (HybridGateUsesWire.xor_left _ _)
          · exact (congrArg (HybridGateUsesWire _) (Fin.ext (by simp [hR]))).mpr
              (HybridGateUsesWire.xor_right _ _)
        rw [hvLast]
        exact HybridCircuit.directedEdge_snoc_last hUses
      · have hh2' : 2 ^ d - m ≤ h / 2 := by omega
        exact HybridCircuit.directedEdge_snoc_castSucc (ih (Nat.le_of_lt hm) hh2')

/-- **100% Reachability**: every single wire in `ClosedComparatorXor.source d`
reaches the single output wire. -/
theorem all_wires_reachable (d : Nat) (u : Fin (source d).wires) :
    (source d).circuit.DirectedReach u (source d).output := by
  have hBase : LayeredRing.ringWires (2 ^ d) d = (d + 1) * 2 ^ d :=
    LayeredRing.ringWires_eq (2 ^ d) d
  have hHeapReach : ∀ h (hh1 : 1 ≤ h) (hh2 : h < 2 ^ (d + 1)),
      ∃ hu : heapWireVal d h < (source d).wires,
        (source d).circuit.DirectedReach ⟨heapWireVal d h, hu⟩ (source d).output := by
    intro h
    induction h using Nat.strong_induction_on with
    | h h ih =>
        intro hh1 hh2
        by_cases h1 : h = 1
        · subst h1
          refine ⟨by rw [← source_output_val]; exact (source d).output.isLt, ?_⟩
          have hOut : (⟨heapWireVal d 1, by rw [← source_output_val]; exact (source d).output.isLt⟩ :
              Fin (source d).wires) = (source d).output := Fin.ext (source_output_val d).symm
          rw [hOut]
          exact Relation.ReflTransGen.refl
        · have hhGe2 : 2 ≤ h := by omega
          have hp1 : 1 ≤ h / 2 := by omega
          have hp2 : h / 2 < 2 ^ (d + 1) := by omega
          have hpLt : h / 2 < h := Nat.div_lt_self (by omega) (by decide)
          obtain ⟨hpW, hpReach⟩ := ih (h / 2) hpLt hp1 hp2
          have hh2m : 2 ^ d - (2 ^ d - 1) ≤ h / 2 := by
            have := Nat.two_pow_pos d
            omega
          have hEdge := appendXorGates_directedEdge_step d (2 ^ d - 1) le_rfl h hhGe2 hh2m hh2
          exact ⟨_, Relation.ReflTransGen.head hEdge hpReach⟩
  have hBflyReach : ∀ m (ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d) (hm : m = d - ℓ),
      ∃ hu : ℓ * 2 ^ d + j < (source d).wires,
        (source d).circuit.DirectedReach ⟨ℓ * 2 ^ d + j, hu⟩ (source d).output := by
    intro m
    induction m with
    | zero =>
        intro ℓ j hℓ hj hm
        have hEq : ℓ = d := by omega
        subst hEq
        have hh1 : 1 ≤ 2 ^ ℓ + j := by
          have := Nat.two_pow_pos ℓ
          omega
        have hh2 : 2 ^ ℓ + j < 2 ^ (ℓ + 1) := by
          rw [Nat.pow_succ, Nat.mul_two]
          omega
        obtain ⟨hW, hReach⟩ := hHeapReach (2 ^ ℓ + j) hh1 hh2
        have hVal : heapWireVal ℓ (2 ^ ℓ + j) = ℓ * 2 ^ ℓ + j := by
          dsimp [heapWireVal]
          have hNot : ¬ (2 ^ ℓ + j < 2 ^ ℓ) := by omega
          simp only [hNot, ↓reduceIte, Nat.add_sub_cancel_left]
        refine ⟨by rw [← hVal]; exact hW, ?_⟩
        convert hReach using 1
        exact Fin.ext hVal.symm
    | succ m ih =>
        intro ℓ j hℓ hj hm
        have hℓLt : ℓ < d := by omega
        obtain ⟨hNextW, hNextReach⟩ := ih (ℓ + 1) j hℓLt hj (by omega)
        have hCurLt : ℓ * 2 ^ d + j < LayeredRing.ringWires (2 ^ d) d := by
          rw [hBase]
          have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
          have : (ℓ + 1) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
          omega
        have hNextLt : (ℓ + 1) * 2 ^ d + j < LayeredRing.ringWires (2 ^ d) d := by
          rw [hBase]
          have : (ℓ + 1) * 2 ^ d + 2 ^ d = (ℓ + 2) * 2 ^ d := by ring
          have : (ℓ + 2) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
          omega
        have hEdgeB := buildCompBfly_directedEdge_of_bflyStep d d le_rfl
          ⟨ℓ * 2 ^ d + j, hCurLt⟩ ⟨(ℓ + 1) * 2 ^ d + j, hNextLt⟩
          ⟨ℓ, j, hℓLt, hj, rfl, Or.inl rfl⟩
        have hEdgeS := appendXorGates_directedEdge_of_prev d (2 ^ d - 1) le_rfl hEdgeB
        exact ⟨_, Relation.ReflTransGen.head hEdgeS hNextReach⟩
  have hUlt : u.val < (d + 2) * 2 ^ d - 1 := by
    simpa [source_wires_eq, totalWires] using u.isLt
  by_cases hInBfly : u.val < (d + 1) * 2 ^ d
  · have hPos : 0 < 2 ^ d := Nat.two_pow_pos d
    have hℓ : u.val / 2 ^ d ≤ d := by
      have : u.val / 2 ^ d < d + 1 := Nat.div_lt_of_lt_mul (by linarith)
      omega
    have hj : u.val % 2 ^ d < 2 ^ d := Nat.mod_lt u.val hPos
    obtain ⟨hW, hReach⟩ := hBflyReach (d - u.val / 2 ^ d) (u.val / 2 ^ d) (u.val % 2 ^ d) hℓ hj rfl
    have hDM : (u.val / 2 ^ d) * 2 ^ d + u.val % 2 ^ d = u.val := by
      have := Nat.div_add_mod u.val (2 ^ d)
      linarith [Nat.mul_comm (u.val / 2 ^ d) (2 ^ d)]
    have hFinEq : (⟨(u.val / 2 ^ d) * 2 ^ d + u.val % 2 ^ d, hW⟩ : Fin (source d).wires) = u :=
      Fin.ext hDM
    rwa [hFinEq] at hReach
  · set h := (d + 2) * 2 ^ d - 1 - u.val
    have hh1 : 1 ≤ h := by omega
    have hh2 : h < 2 ^ (d + 1) := by
      have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      rw [Nat.pow_succ, Nat.mul_two]
      omega
    have hhSmall : h < 2 ^ d := by
      have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      omega
    obtain ⟨hW, hReach⟩ := hHeapReach h hh1 hh2
    have hVal : heapWireVal d h = u.val := by
      dsimp [heapWireVal]
      simp only [hhSmall, ↓reduceIte]
      omega
    have hFinEq : (⟨heapWireVal d h, hW⟩ : Fin (source d).wires) = u := Fin.ext hVal
    rwa [hFinEq] at hReach

private lemma compGate_nonlinearWeight (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    (compGate d ℓ j hℓ hj).nonlinearWeight = 1 := by
  dsimp [compGate]
  split_ifs <;> rfl

private lemma appendCompRow_nonlinearCount (d ℓ : Nat) (hℓ : ℓ < d) (m : Nat) (hm : m ≤ 2 ^ d)
    (prev : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) :
    (appendCompRow d ℓ hℓ m hm prev).nonlinearCount = prev.nonlinearCount + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [appendCompRow, HybridCircuit.nonlinearCount]
      rw [ih (Nat.le_of_lt hm), compGate_nonlinearWeight]
      omega

lemma buildCompBfly_nonlinearCount (d : Nat) :
    ∀ D (hD : D ≤ d), (buildCompBfly d D hD).nonlinearCount = D * 2 ^ d
  | 0, _ => by simp [buildCompBfly, HybridCircuit.nonlinearCount]
  | D + 1, hD => by
      dsimp [buildCompBfly]
      refine (appendCompRow_nonlinearCount d D hD (2 ^ d) le_rfl
        (buildCompBfly d D (Nat.le_of_lt hD))).trans ?_
      rw [buildCompBfly_nonlinearCount d D (Nat.le_of_lt hD)]
      ring

private lemma appendXorGates_nonlinearCount (d m : Nat) (hm : m ≤ 2 ^ d - 1) :
    (appendXorGates d m hm).nonlinearCount = d * 2 ^ d := by
  induction m with
  | zero => exact buildCompBfly_nonlinearCount d d le_rfl
  | succ m ih =>
      dsimp [appendXorGates, HybridCircuit.nonlinearCount]
      exact ih (Nat.le_of_lt hm)

/-- Exact nonlinear gate count of `ClosedComparatorXor.source d`:
all `d * 2 ^ d` comparator gates are nonlinear (`AND`/`OR`), while all `2 ^ d - 1`
reduction gates are linear (`XOR`). -/
theorem nonlinearCount_eq (d : Nat) :
    (source d).circuit.nonlinearCount = d * 2 ^ d :=
  appendXorGates_nonlinearCount d (2 ^ d - 1) le_rfl

/-- **Nonlinear-Count Lower Bound**: `ClosedComparatorXor.source (d i)` has
`d i * 2^(d i)` nonlinear gates, escaping every `o(2^(d i))` bound. -/
theorem escapes_sublinear_nonlinear (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (B : Nat → ℝ) (hB : B =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) :
    ¬ (∀ᶠ i in atTop, (((source (d i)).circuit.nonlinearCount : Nat) : ℝ) ≤ B i) := by
  intro hLe
  rw [Asymptotics.isLittleO_iff] at hB
  have hBound := hB (show (0 : ℝ) < 1 by norm_num)
  have hD2 : ∀ᶠ i in atTop, 2 ≤ d i := hd.eventually_ge_atTop 2
  obtain ⟨i, hiLe, hiB, hiD⟩ := (hLe.and (hBound.and hD2)).exists
  rw [nonlinearCount_eq (d i)] at hiLe
  have hPowPos : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by exact_mod_cast Nat.two_pow_pos (d i)
  have hNormB : B i ≤ ‖B i‖ := le_abs_self _
  have hNormPow : ‖((2 ^ d i : Nat) : ℝ)‖ = ((2 ^ d i : Nat) : ℝ) :=
    Real.norm_of_nonneg hPowPos.le
  rw [hNormPow, one_mul] at hiB
  have hCast : (((d i * 2 ^ d i : Nat) : ℝ)) = (d i : ℝ) * ((2 ^ d i : Nat) : ℝ) := by
    push_cast; rfl
  have hDReal : (2 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hiD
  nlinarith

private lemma source_embeds_butterfly (d : Nat) :
    let f : Fin (ButterflyNet.source d).wires → Fin (source d).wires :=
      fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩
    Function.Injective f ∧
      (∀ u v, CircuitEdge (ButterflyNet.source d).circuit u v →
        HybridCircuitEdge (source d).circuit (f u) (f v)) := by
  intro f
  refine ⟨fun a b h => Fin.ext (by simpa [f] using congrArg Fin.val h), fun u v huv => ?_⟩
  have hDirOr : (ButterflyNet.source d).circuit.DirectedEdge u v ∨
      (ButterflyNet.source d).circuit.DirectedEdge v u :=
    CircuitEdge.to_directedEdge_or huv
  rcases hDirOr with hDir | hDir
  · rw [ButterflyNet.source_directedEdge_iff] at hDir
    have hComp := buildCompBfly_directedEdge_of_bflyStep d d le_rfl u v hDir
    have hXor := appendXorGates_directedEdge_of_prev d (2 ^ d - 1) le_rfl hComp
    exact HybridCircuit.directedEdge_to_hybridCircuitEdge hXor
  · rw [ButterflyNet.source_directedEdge_iff] at hDir
    have hComp := buildCompBfly_directedEdge_of_bflyStep d d le_rfl v u hDir
    have hXor := appendXorGates_directedEdge_of_prev d (2 ^ d - 1) le_rfl hComp
    exact (HybridCircuit.directedEdge_to_hybridCircuitEdge hXor).symm

/-- **Linear Treewidth Wall**: via `TreeDecomp.restrict_le` on the comparator butterfly subgraph,
any tree decomposition of `ClosedComparatorXor.source d` has width `Ω(2^d)`. -/
theorem treewidth_linear (d : Nat) (td : TreeDecomp (HybridCircuitEdge (source d).circuit)) :
    2 ^ d ≤ 18 * (td.width + 1) := by
  let f : Fin (ButterflyNet.source d).wires → Fin (source d).wires :=
    fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩
  have hf : Function.Injective f := (source_embeds_butterfly d).1
  have hEdge := (source_embeds_butterfly d).2
  have hLin := ButterflyNet.butterfly_treewidth_linear d (td.restrict f hf hEdge)
  have hLe := td.restrict_le f hf hEdge
  omega

/-- **Linear Gate-Contraction-Width Wall**: via `ValidContractionTree.restrict_le` on the
comparator butterfly subgraph, any leaf-bounded contraction tree has width `Ω(2^d)`. -/
theorem gateContractionWidth_linear (d : Nat) (hd : 2 ≤ d)
    (ct : ValidContractionTree (HybridCircuitEdge (source d).circuit))
    (hLeaves : ContractionTree.AllLeaves (fun s => s.card ≤ 2) ct.tree) :
    2 ^ d ≤ 18 * ct.contractionWidth := by
  let f : Fin (ButterflyNet.source d).wires → Fin (source d).wires :=
    fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩
  have hf : Function.Injective f := (source_embeds_butterfly d).1
  have hEdge := (source_embeds_butterfly d).2
  have hLin : 2 ^ d ≤ 18 * (ct.restrict f hf hEdge).contractionWidth := by
    refine ButterflyNet.butterfly_gateContractionWidth_linear d hd (ct.restrict f hf hEdge) ?_
    refine ContractionTree.allLeaves_restrict f hf ?_ ct.tree hLeaves
    intro s hs
    have hPreLe : (s.preimage f hf.injOn).card ≤ s.card :=
      Finset.card_le_card_of_injOn f (fun u hu => Finset.mem_preimage.mp hu)
        (fun x _ y _ h => hf h)
    have hFiltLe : ({x : Fin (2 ^ d) | ⟨x.val, by
        change x.val < LayeredRing.ringWires (2 ^ d) d
        have hx := x.isLt
        have hWPos : 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d)
        rw [LayeredRing.ringWires_eq]
        exact lt_of_lt_of_le hx hWPos⟩ ∈ s.preimage f hf.injOn} : Finset _).card ≤
        (s.preimage f hf.injOn).card := by
      refine Finset.card_le_card_of_injOn
        (fun x : Fin (2 ^ d) => ⟨x.val, by
          change x.val < LayeredRing.ringWires (2 ^ d) d
          have hx := x.isLt
          have hWPos : 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d)
          rw [LayeredRing.ringWires_eq]
          exact lt_of_lt_of_le hx hWPos⟩)
        (fun x hx => by simpa using hx)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    exact hFiltLe.trans (hPreLe.trans hs)
  have hLe := ct.restrict_le f hf hEdge
  omega

/-- `ClosedComparatorXor.source` defeats all sublinear-treewidth algorithms. -/
theorem escapes_sublinear_treewidth (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (td : (i : Nat) → TreeDecomp (HybridCircuitEdge (source (d i)).circuit)) :
    ¬ ((fun i => ((td i).width : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) := by
  let td' : (i : Nat) → TreeDecomp (CircuitEdge (ButterflyNet.source (d i)).circuit) :=
    fun i => (td i).restrict _ (source_embeds_butterfly (d i)).1 (source_embeds_butterfly (d i)).2
  intro hSub
  have hSub' : (fun i => ((td' i).width : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ) := by
    refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
    filter_upwards [(Asymptotics.isLittleO_iff.mp hSub) hε] with i hi
    have hLe : ((td' i).width : ℝ) ≤ ((td i).width : ℝ) := by
      exact_mod_cast (td i).restrict_le _ (source_embeds_butterfly (d i)).1
        (source_embeds_butterfly (d i)).2
    have hNonneg : 0 ≤ ((td' i).width : ℝ) := Nat.cast_nonneg _
    have hNonneg2 : 0 ≤ ((td i).width : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg hNonneg]
    rw [Real.norm_of_nonneg hNonneg2] at hi
    exact hLe.trans hi
  exact ButterflyNet.butterfly_escapes_sublinear_treewidth d hd td' hSub'

/-- `ClosedComparatorXor.source` defeats all sublinear contraction-width algorithms. -/
theorem escapes_sublinear_contractionWidth (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (ct : (i : Nat) → ValidContractionTree (HybridCircuitEdge (source (d i)).circuit))
    (hLeaves : ∀ i, ContractionTree.AllLeaves (fun s => s.card ≤ 2) (ct i).tree) :
    ¬ ((fun i => ((ct i).contractionWidth : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) := by
  intro hSub
  rw [Asymptotics.isLittleO_iff] at hSub
  have hBound := hSub (show (0 : ℝ) < 1 / 36 by norm_num)
  have hD2 : ∀ᶠ i in atTop, 2 ≤ d i := hd.eventually_ge_atTop 2
  obtain ⟨i, hiB, hiD⟩ := (hBound.and hD2).exists
  have hLin : 2 ^ d i ≤ 18 * (ct i).contractionWidth :=
    gateContractionWidth_linear (d i) hiD (ct i) (hLeaves i)
  have hLinR : ((2 ^ d i : Nat) : ℝ) ≤ 18 * ((ct i).contractionWidth : ℝ) := by
    exact_mod_cast hLin
  have hNonneg : 0 ≤ ((ct i).contractionWidth : ℝ) := Nat.cast_nonneg _
  have hPowPos : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by exact_mod_cast Nat.two_pow_pos (d i)
  rw [Real.norm_of_nonneg hNonneg, Real.norm_of_nonneg hPowPos.le] at hiB
  nlinarith

private lemma appendCompRow_evalWires_stable (d ℓ : Nat) (hℓ : ℓ < d)
    (prev : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (m : Nat) (hm : m ≤ 2 ^ d) (x : Fin (2 ^ d) → Bool)
    (u : Fin (LayeredRing.ringWires (2 ^ d) ℓ)) :
    (appendCompRow d ℓ hℓ m hm prev).evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ m)⟩ =
      prev.evalWires x u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [appendCompRow]
      exact (HybridCircuit.evalWires_snoc_castSucc _ _ x _).trans (ih (Nat.le_of_lt hm))

lemma buildCompBfly_evalWires_stable (d : Nat) (x : Fin (2 ^ d) → Bool) :
    ∀ D₁ D₂ (h₁₂ : D₁ ≤ D₂) (h₂ : D₂ ≤ d) (u : Fin (LayeredRing.ringWires (2 ^ d) D₁)),
      (buildCompBfly d D₂ h₂).evalWires x
          ⟨u.val, by
            have hu : u.val < (D₁ + 1) * 2 ^ d := by
              have h1 := LayeredRing.ringWires_eq (2 ^ d) D₁
              have := u.isLt
              omega
            have hMul : (D₁ + 1) * 2 ^ d ≤ (D₂ + 1) * 2 ^ d :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ h₁₂)
            have h2 := LayeredRing.ringWires_eq (2 ^ d) D₂
            omega⟩ =
        (buildCompBfly d D₁ (le_trans h₁₂ h₂)).evalWires x u := by
  intro D₁ D₂ h₁₂
  induction D₂ with
  | zero =>
      intro h₂ u
      have hD1 : D₁ = 0 := by omega
      subst hD1
      rfl
  | succ D₂ ih =>
      intro h₂ u
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h₁₂) with hLt | rfl
      · have h12' : D₁ ≤ D₂ := Nat.lt_succ_iff.mp hLt
        dsimp [buildCompBfly]
        have hSt := appendCompRow_evalWires_stable d D₂ h₂ (buildCompBfly d D₂ (Nat.le_of_lt h₂))
          (2 ^ d) le_rfl x ⟨u.val, by
            have hu : u.val < (D₁ + 1) * 2 ^ d := by
              have h1 := LayeredRing.ringWires_eq (2 ^ d) D₁
              have := u.isLt
              omega
            have hMul : (D₁ + 1) * 2 ^ d ≤ (D₂ + 1) * 2 ^ d :=
              Nat.mul_le_mul_right _ (Nat.succ_le_succ h12')
            have h2' := LayeredRing.ringWires_eq (2 ^ d) D₂
            omega⟩
        exact hSt.trans (ih h12' (Nat.le_of_lt h₂) u)
      · rfl

private lemma compGate_eval_eq (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d)
    (v : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j) → Bool) :
    have hBase : LayeredRing.ringWires (2 ^ d) ℓ = (ℓ + 1) * 2 ^ d :=
      LayeredRing.ringWires_eq (2 ^ d) ℓ
    (compGate d ℓ j hℓ hj).eval v =
      if j.testBit ℓ = false then
        v ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩ &&
          v ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
            rw [hBase]; have := ButterflyNet.flipBit_lt hj hℓ; nlinarith⟩
      else
        v ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩ ||
          v ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
            rw [hBase]; have := ButterflyNet.flipBit_lt hj hℓ; nlinarith⟩ := by
  dsimp [compGate]
  split_ifs <;> rfl

private lemma appendCompRow_evalWires_step (d ℓ : Nat) (hℓ : ℓ < d)
    (prev : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (m : Nat) (hm : m ≤ 2 ^ d) (x : Fin (2 ^ d) → Bool) :
    ∀ j (hj : j < m),
      (appendCompRow d ℓ hℓ m hm prev).evalWires x ⟨(ℓ + 1) * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; omega⟩ =
      if j.testBit ℓ = false then
        prev.evalWires x ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩ &&
          prev.evalWires x ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
            rw [LayeredRing.ringWires_eq]; have := ButterflyNet.flipBit_lt (Nat.lt_of_lt_of_le hj hm) hℓ; nlinarith⟩
      else
        prev.evalWires x ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩ ||
          prev.evalWires x ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
            rw [LayeredRing.ringWires_eq]; have := ButterflyNet.flipBit_lt (Nat.lt_of_lt_of_le hj hm) hℓ; nlinarith⟩ := by
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
      intro j hj
      dsimp [appendCompRow]
      have hBase := LayeredRing.ringWires_eq (2 ^ d) ℓ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjm | rfl
      · exact (HybridCircuit.evalWires_snoc_castSucc _ _ x _).trans (ih (Nat.le_of_lt hm) j hjm)
      · have hLast : (⟨(ℓ + 1) * 2 ^ d + j, by rw [hBase]; omega⟩ :
            Fin (LayeredRing.ringWires (2 ^ d) ℓ + (j + 1))) = Fin.last _ :=
          Fin.ext (by simp [hBase])
        rw [hLast]
        refine (HybridCircuit.evalWires_snoc_last _ _ x).trans ?_
        rw [compGate_eval_eq]
        have hSt1 := appendCompRow_evalWires_stable d ℓ hℓ prev j (Nat.le_of_lt hm) x
          ⟨ℓ * 2 ^ d + j, by rw [hBase]; nlinarith⟩
        have hFlipLt := ButterflyNet.flipBit_lt hm hℓ
        have hSt2 := appendCompRow_evalWires_stable d ℓ hℓ prev j (Nat.le_of_lt hm) x
          ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by rw [hBase]; nlinarith⟩
        simp only at hSt1 hSt2 ⊢
        rw [hSt1, hSt2]

private lemma appendXorGates_evalWires_stable (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    (x : Fin (2 ^ d) → Bool) (u : Fin (LayeredRing.ringWires (2 ^ d) d)) :
    (appendXorGates d m hm).evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ m)⟩ =
      (buildCompBfly d d le_rfl).evalWires x u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [appendXorGates]
      exact (HybridCircuit.evalWires_snoc_castSucc _ _ x _).trans (ih (Nat.le_of_lt hm))

lemma source_evalWire_comp (d ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d)
    (x : Fin (2 ^ d) → Bool) :
    (source d).circuit.evalWires x (compWireInSource d ℓ j hℓ hj) =
      (buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]
        have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
        omega⟩ := by
  have hX := appendXorGates_evalWires_stable d (2 ^ d - 1) le_rfl x (compWire d ℓ j hℓ hj)
  have hB := buildCompBfly_evalWires_stable d x ℓ d hℓ le_rfl
    ⟨ℓ * 2 ^ d + j, by
      rw [LayeredRing.ringWires_eq]
      have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
      omega⟩
  exact hX.trans hB

lemma buildCompBfly_eval_succ (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d)
    (x : Fin (2 ^ d) → Bool) :
    (buildCompBfly d (ℓ + 1) hℓ).evalWires x ⟨(ℓ + 1) * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
      if j.testBit ℓ = false then
        (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x ⟨ℓ * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ &&
        (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
          rw [LayeredRing.ringWires_eq]; have := ButterflyNet.flipBit_lt hj hℓ; nlinarith⟩
      else
        (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x ⟨ℓ * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ ||
        (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
          rw [LayeredRing.ringWires_eq]; have := ButterflyNet.flipBit_lt hj hℓ; nlinarith⟩ := by
  dsimp [buildCompBfly]
  exact appendCompRow_evalWires_step d ℓ hℓ _ (2 ^ d) le_rfl x j hj

private lemma buildCompBfly_eval_ext (d ℓ : Nat) (hℓ : ℓ ≤ d) (j : Nat) (hj : j < 2 ^ d)
    (x y : Fin (2 ^ d) → Bool)
    (hAgree : ∀ k (hk : k < 2 ^ d), k / 2 ^ ℓ = j / 2 ^ ℓ → x ⟨k, hk⟩ = y ⟨k, hk⟩) :
    (buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
      (buildCompBfly d ℓ hℓ).evalWires y ⟨ℓ * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
  induction ℓ generalizing j with
  | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, buildCompBfly, HybridCircuit.evalWires]
      exact hAgree j hj rfl
  | succ ℓ ih =>
      rw [buildCompBfly_eval_succ d ℓ j hℓ hj x, buildCompBfly_eval_succ d ℓ j hℓ hj y]
      have hFlipLt := ButterflyNet.flipBit_lt hj hℓ
      have h1 := ih (Nat.le_of_lt hℓ) j hj (fun k hk hDiv =>
        hAgree k hk (by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hDiv]))
      have h2 := ih (Nat.le_of_lt hℓ) (ButterflyNet.flipBit j ℓ) hFlipLt (fun k hk hDiv =>
        hAgree k hk (by
          have hDivF : ButterflyNet.flipBit j ℓ / 2 ^ (ℓ + 1) = j / 2 ^ (ℓ + 1) :=
            ButterflyNet.div_two_pow_flipBit_eq_of_lt (Nat.lt_succ_self ℓ)
          rw [← hDivF, Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hDiv]))
      rw [h1, h2]

private lemma buildCompBfly_eval_const (d ℓ : Nat) (hℓ : ℓ ≤ d) (j : Nat) (hj : j < 2 ^ d)
    (b : Bool) (x : Fin (2 ^ d) → Bool)
    (hConst : ∀ k (hk : k < 2 ^ d), k / 2 ^ ℓ = j / 2 ^ ℓ → x ⟨k, hk⟩ = b) :
    (buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ = b := by
  induction ℓ generalizing j with
  | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, buildCompBfly, HybridCircuit.evalWires]
      exact hConst j hj rfl
  | succ ℓ ih =>
      rw [buildCompBfly_eval_succ d ℓ j hℓ hj x]
      have hFlipLt := ButterflyNet.flipBit_lt hj hℓ
      have h1 := ih (Nat.le_of_lt hℓ) j hj (fun k hk hDiv =>
        hConst k hk (by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hDiv]))
      have h2 := ih (Nat.le_of_lt hℓ) (ButterflyNet.flipBit j ℓ) hFlipLt (fun k hk hDiv =>
        hConst k hk (by
          have hDivF : ButterflyNet.flipBit j ℓ / 2 ^ (ℓ + 1) = j / 2 ^ (ℓ + 1) :=
            ButterflyNet.div_two_pow_flipBit_eq_of_lt (Nat.lt_succ_self ℓ)
          rw [← hDivF, Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hDiv]))
      rw [h1, h2]
      split_ifs <;> simp

private lemma buildCompBfly_eval_toggle (d ℓ : Nat) (hℓ : ℓ ≤ d) (j : Nat) (hj : j < 2 ^ d)
    (k : Nat) (hk : k < 2 ^ d) (hBlock : k / 2 ^ ℓ = j / 2 ^ ℓ) :
    ∃ x : Fin (2 ^ d) → Bool,
      (buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ ≠
        (buildCompBfly d ℓ hℓ).evalWires (Function.update x ⟨k, hk⟩ (!(x ⟨k, hk⟩)))
          ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
  induction ℓ generalizing j with
  | zero =>
      have hkEq : k = j := by simpa using hBlock
      subst hkEq
      refine ⟨fun _ => false, ?_⟩
      simp only [Nat.zero_mul, Nat.zero_add, buildCompBfly, HybridCircuit.evalWires]
      change false ≠ Function.update (fun _ : Fin (2 ^ d) => false) ⟨k, hk⟩ true ⟨k, hj⟩
      rw [show (⟨k, hj⟩ : Fin (2 ^ d)) = ⟨k, hk⟩ from Fin.ext rfl, Function.update_self]
      decide
  | succ ℓ ih =>
      have hFlipLt := ButterflyNet.flipBit_lt hj hℓ
      have hSideNe : ButterflyNet.flipBit j ℓ / 2 ^ ℓ ≠ j / 2 ^ ℓ := by
        rcases ButterflyNet.flipBit_div_two_pow_pair j ℓ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      have hKIn : k / 2 ^ ℓ = j / 2 ^ ℓ ∨ k / 2 ^ ℓ = ButterflyNet.flipBit j ℓ / 2 ^ ℓ := by
        have hKDiv : (k / 2 ^ ℓ) / 2 = (j / 2 ^ ℓ) / 2 := by
          rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← Nat.pow_succ, hBlock]
        rcases ButterflyNet.flipBit_div_two_pow_pair j ℓ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      let idVal : Bool := !(j.testBit ℓ)
      rcases hKIn with hLeft | hRight
      · obtain ⟨x₀, hx₀⟩ := ih (Nat.le_of_lt hℓ) j hj hLeft
        let x : Fin (2 ^ d) → Bool := fun i =>
          if i.val / 2 ^ ℓ = ButterflyNet.flipBit j ℓ / 2 ^ ℓ then idVal else x₀ i
        refine ⟨x, ?_⟩
        have hkNotSide : k / 2 ^ ℓ ≠ ButterflyNet.flipBit j ℓ / 2 ^ ℓ := by
          rw [hLeft]; exact hSideNe.symm
        have hMainX : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x ⟨ℓ * 2 ^ d + j, by
            rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x₀ ⟨ℓ * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
          refine buildCompBfly_eval_ext d ℓ (Nat.le_of_lt hℓ) j hj x x₀ fun i _ hi => ?_
          have hNe : i / 2 ^ ℓ ≠ ButterflyNet.flipBit j ℓ / 2 ^ ℓ := by
            rw [hi]; exact hSideNe.symm
          simp [x, hNe]
        have hMainUpd : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires
            (Function.update x ⟨k, hk⟩ (!(x ⟨k, hk⟩))) ⟨ℓ * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires
              (Function.update x₀ ⟨k, hk⟩ (!(x₀ ⟨k, hk⟩))) ⟨ℓ * 2 ^ d + j, by
                rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
          refine buildCompBfly_eval_ext d ℓ (Nat.le_of_lt hℓ) j hj _ _ fun i hi hDiv => ?_
          by_cases hik : (⟨i, hi⟩ : Fin (2 ^ d)) = ⟨k, hk⟩
          · rw [hik]
            simp [x, hkNotSide]
          · have hNe : i / 2 ^ ℓ ≠ ButterflyNet.flipBit j ℓ / 2 ^ ℓ := by
              rw [hDiv]; exact hSideNe.symm
            simp [Function.update_of_ne hik, x, hNe]
        have hSideX : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x
            ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ = idVal := by
          refine buildCompBfly_eval_const d ℓ (Nat.le_of_lt hℓ) _ hFlipLt idVal x fun i _ hi => ?_
          simp [x, hi]
        have hSideUpd : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires
            (Function.update x ⟨k, hk⟩ (!(x ⟨k, hk⟩)))
            ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ = idVal := by
          refine buildCompBfly_eval_const d ℓ (Nat.le_of_lt hℓ) _ hFlipLt idVal _ fun i hi hiDiv => ?_
          have hik : (⟨i, hi⟩ : Fin (2 ^ d)) ≠ ⟨k, hk⟩ := by
            intro hEq
            have := congrArg Fin.val hEq
            dsimp at this
            subst this
            exact hkNotSide hiDiv
          simp [Function.update_of_ne hik, x, hiDiv]
        rw [buildCompBfly_eval_succ d ℓ j hℓ hj, buildCompBfly_eval_succ d ℓ j hℓ hj,
          hMainX, hMainUpd, hSideX, hSideUpd]
        dsimp [idVal]
        cases hBit : j.testBit ℓ
        · simp [hx₀]
        · simp [hx₀]
      · obtain ⟨x₀, hx₀⟩ := ih (Nat.le_of_lt hℓ) (ButterflyNet.flipBit j ℓ) hFlipLt hRight
        let x : Fin (2 ^ d) → Bool := fun i =>
          if i.val / 2 ^ ℓ = j / 2 ^ ℓ then idVal else x₀ i
        refine ⟨x, ?_⟩
        have hkNotMain : k / 2 ^ ℓ ≠ j / 2 ^ ℓ := by
          rw [hRight]; exact hSideNe
        have hSideX : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x
            ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x₀
              ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
                rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
          refine buildCompBfly_eval_ext d ℓ (Nat.le_of_lt hℓ) _ hFlipLt x x₀ fun i _ hi => ?_
          have hNe : i / 2 ^ ℓ ≠ j / 2 ^ ℓ := by
            rw [hi]; exact hSideNe
          simp [x, hNe]
        have hSideUpd : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires
            (Function.update x ⟨k, hk⟩ (!(x ⟨k, hk⟩)))
            ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires
              (Function.update x₀ ⟨k, hk⟩ (!(x₀ ⟨k, hk⟩)))
              ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
                rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
          refine buildCompBfly_eval_ext d ℓ (Nat.le_of_lt hℓ) _ hFlipLt _ _ fun i hi hDiv => ?_
          by_cases hik : (⟨i, hi⟩ : Fin (2 ^ d)) = ⟨k, hk⟩
          · rw [hik]
            simp [x, hkNotMain]
          · have hNe : i / 2 ^ ℓ ≠ j / 2 ^ ℓ := by
              rw [hDiv]; exact hSideNe
            simp [Function.update_of_ne hik, x, hNe]
        have hMainX : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x ⟨ℓ * 2 ^ d + j, by
            rw [LayeredRing.ringWires_eq]; nlinarith⟩ = idVal := by
          refine buildCompBfly_eval_const d ℓ (Nat.le_of_lt hℓ) j hj idVal x fun i _ hi => ?_
          simp [x, hi]
        have hMainUpd : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires
            (Function.update x ⟨k, hk⟩ (!(x ⟨k, hk⟩))) ⟨ℓ * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ = idVal := by
          refine buildCompBfly_eval_const d ℓ (Nat.le_of_lt hℓ) j hj idVal _ fun i hi hiDiv => ?_
          have hik : (⟨i, hi⟩ : Fin (2 ^ d)) ≠ ⟨k, hk⟩ := by
            intro hEq
            have := congrArg Fin.val hEq
            dsimp at this
            subst this
            exact hkNotMain hiDiv
          simp [Function.update_of_ne hik, x, hiDiv]
        rw [buildCompBfly_eval_succ d ℓ j hℓ hj, buildCompBfly_eval_succ d ℓ j hℓ hj,
          hMainX, hMainUpd, hSideX, hSideUpd]
        dsimp [idVal]
        cases hBit : j.testBit ℓ
        · simp [hx₀]
        · simp [hx₀]

private lemma exists_highest_diff_bit :
    ∀ {ℓ j₁ j₂ : Nat}, j₁ / 2 ^ ℓ = j₂ / 2 ^ ℓ → j₁ ≠ j₂ →
      ∃ b < ℓ, j₁.testBit b ≠ j₂.testBit b ∧
        ∀ t, b < t → t < ℓ → j₁.testBit t = j₂.testBit t
  | 0, _, _, hDiv, hNe => by simp at hDiv; exact False.elim (hNe hDiv)
  | ℓ + 1, j₁, j₂, hDiv, hNe => by
      by_cases hBit : j₁.testBit ℓ ≠ j₂.testBit ℓ
      · exact ⟨ℓ, Nat.lt_succ_self ℓ, hBit, fun t ht1 ht2 => by omega⟩
      · have hEqBit : j₁.testBit ℓ = j₂.testBit ℓ := of_not_not hBit
        have hDivL : j₁ / 2 ^ ℓ = j₂ / 2 ^ ℓ := by
          apply Nat.eq_of_testBit_eq
          intro b
          rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
          by_cases hb : b = 0
          · subst hb; simpa using hEqBit
          · have h1 := congrArg (fun n => n.testBit (b - 1)) hDiv
            rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow] at h1
            have hSub : b - 1 + (ℓ + 1) = b + ℓ := by omega
            rwa [hSub] at h1
        obtain ⟨b, hbLt, hbNe, hbAbove⟩ := exists_highest_diff_bit hDivL hNe
        refine ⟨b, Nat.lt_succ_of_lt hbLt, hbNe, fun t ht1 ht2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht2 with htLt | rfl
        · exact hbAbove t ht1 htLt
        · exact hEqBit

private lemma eval_lift_above_branch (d b : Nat) (y₀ : Fin (2 ^ d) → Bool)
    (jRef : Nat) (_hjRef : jRef < 2 ^ d) :
    ∀ m (hm : b + 1 ≤ m) (hmd : m ≤ d),
      ∃ x : Fin (2 ^ d) → Bool,
        (∀ i (hi : i < 2 ^ d), i / 2 ^ (b + 1) = jRef / 2 ^ (b + 1) → x ⟨i, hi⟩ = y₀ ⟨i, hi⟩) ∧
        (∀ j (hj : j < 2 ^ d), j / 2 ^ (b + 1) = jRef / 2 ^ (b + 1) →
          (∀ t, b + 1 ≤ t → t < m → j.testBit t = jRef.testBit t) →
          (buildCompBfly d m hmd).evalWires x ⟨m * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d (b + 1) (by omega)).evalWires y₀ ⟨(b + 1) * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩) := by
  intro m hm hmd
  suffices ∀ k (m : Nat) (hk : k = m - (b + 1)) (hm : b + 1 ≤ m) (hmd : m ≤ d),
      ∃ x : Fin (2 ^ d) → Bool,
        (∀ i (hi : i < 2 ^ d), i / 2 ^ (b + 1) = jRef / 2 ^ (b + 1) → x ⟨i, hi⟩ = y₀ ⟨i, hi⟩) ∧
        (∀ j (hj : j < 2 ^ d), j / 2 ^ (b + 1) = jRef / 2 ^ (b + 1) →
          (∀ t, b + 1 ≤ t → t < m → j.testBit t = jRef.testBit t) →
          (buildCompBfly d m hmd).evalWires x ⟨m * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d (b + 1) (by omega)).evalWires y₀ ⟨(b + 1) * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩) by
    exact this (m - (b + 1)) m rfl hm hmd
  intro k
  induction k with
  | zero =>
      intro m hk hm hmd
      have hmEq : m = b + 1 := by omega
      subst hmEq
      exact ⟨y₀, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ k ih =>
      intro m hk hm hmd
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : b + 1 ≤ m' := by omega
      have hmd' : m' ≤ d := Nat.le_of_lt hmd
      obtain ⟨xPrev, hxPrevAgree, hxPrevEval⟩ := ih m' (by omega) hm' hmd'
      let sideVal : Bool := !(jRef.testBit m')
      let x : Fin (2 ^ d) → Bool := fun i =>
        if i.val / 2 ^ m' = ButterflyNet.flipBit jRef m' / 2 ^ m' then sideVal else xPrev i
      refine ⟨x, ?_, ?_⟩
      · intro i hi hiDiv
        have hiNe : i / 2 ^ m' ≠ ButterflyNet.flipBit jRef m' / 2 ^ m' := by
          intro hEq
          have h1 := congrArg (fun n => n.testBit (m' - (b + 1))) hiDiv
          have h2 := congrArg (fun n => n.testBit (m' - (b + 1))) hEq
          have h1' : (i / 2 ^ (b + 1)).testBit (m' - (b + 1)) = i.testBit m' := by
            rw [Nat.testBit_div_two_pow]
            congr 1; omega
          have h2' : (jRef / 2 ^ (b + 1)).testBit (m' - (b + 1)) = jRef.testBit m' := by
            rw [Nat.testBit_div_two_pow]
            congr 1; omega
          have h3 : i.testBit m' = jRef.testBit m' := by rw [← h1', ← h2', h1]
          have h4 := congrArg (fun n : Nat => n.testBit 0) hEq
          simp only [Nat.testBit_div_two_pow, Nat.zero_add, ButterflyNet.flipBit_testBit_self] at h4
          rw [h3] at h4
          cases jRef.testBit m' <;> simp at h4
        simp [x, hiNe, hxPrevAgree i hi hiDiv]
      · intro j hj hjDiv hjBits
        have hjMatch : j / 2 ^ m' = jRef / 2 ^ m' := by
          apply Nat.eq_of_testBit_eq
          intro t
          rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
          have hSplit : (t + m') = (t + (m' - (b + 1))) + (b + 1) := by omega
          have hDiv1 := congrArg (fun n => n.testBit (t + (m' - (b + 1)))) hjDiv
          rwa [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, ← hSplit] at hDiv1
        have hFlipMatch : ButterflyNet.flipBit j m' / 2 ^ m' =
            ButterflyNet.flipBit jRef m' / 2 ^ m' := by
          apply Nat.eq_of_testBit_eq
          intro t
          rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
          rcases eq_or_ne t 0 with rfl | ht
          · simp only [Nat.zero_add, ButterflyNet.flipBit_testBit_self,
              hjBits m' hm' (Nat.lt_succ_self m')]
          · rw [ButterflyNet.flipBit_testBit_gt (by omega),
              ButterflyNet.flipBit_testBit_gt (by omega)]
            have hT := congrArg (fun n => n.testBit t) hjMatch
            rwa [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow] at hT
        have hFlipLt := ButterflyNet.flipBit_lt hj hmd
        have hSideNe : j / 2 ^ m' ≠ ButterflyNet.flipBit jRef m' / 2 ^ m' := by
          rw [hjMatch]
          intro hEq
          have hSelf := congrArg (fun n : Nat => n.testBit 0) hEq
          rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.zero_add,
            ButterflyNet.flipBit_testBit_self] at hSelf
          cases hjBit : jRef.testBit m' <;> simp [hjBit] at hSelf
        have hMain : (buildCompBfly d m' hmd').evalWires x ⟨m' * 2 ^ d + j, by
            rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
            (buildCompBfly d (b + 1) (by omega)).evalWires y₀ ⟨(b + 1) * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
          have hExt : (buildCompBfly d m' hmd').evalWires x ⟨m' * 2 ^ d + j, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
              (buildCompBfly d m' hmd').evalWires xPrev ⟨m' * 2 ^ d + j, by
                rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
            refine buildCompBfly_eval_ext d m' hmd' j hj x xPrev fun i _ hi => ?_
            have hiNe : i / 2 ^ m' ≠ ButterflyNet.flipBit jRef m' / 2 ^ m' := by
              rw [hi]; exact hSideNe
            simp [x, hiNe]
          rw [hExt]
          exact hxPrevEval j hj hjDiv (fun t ht1 ht2 => hjBits t ht1 (Nat.lt_succ_of_lt ht2))
        have hSide : (buildCompBfly d m' hmd').evalWires x
            ⟨m' * 2 ^ d + ButterflyNet.flipBit j m', by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ = sideVal := by
          refine buildCompBfly_eval_const d m' hmd' _ hFlipLt sideVal x fun i _ hi => ?_
          rw [hFlipMatch] at hi
          simp [x, hi]
        rw [buildCompBfly_eval_succ d m' j hmd hj, hMain, hSide]
        have hBitEq : j.testBit m' = jRef.testBit m' := hjBits m' hm' (Nat.lt_succ_self m')
        rw [hBitEq]
        dsimp [sideVal]
        cases jRef.testBit m' <;> simp

/-- **100% Pairwise Semantic Distinctness**: any two distinct wires `(ℓ₁, j₁) ≠ (ℓ₂, j₂)`
in the comparator butterfly stage of `ClosedComparatorXor.source d` compute strictly distinct
Boolean functions on `Fin (2 ^ d) → Bool`. -/
theorem bfly_wires_pairwise_distinct (d : Nat)
    (ℓ₁ ℓ₂ j₁ j₂ : Nat) (hℓ₁ : ℓ₁ ≤ d) (hℓ₂ : ℓ₂ ≤ d) (hj₁ : j₁ < 2 ^ d) (hj₂ : j₂ < 2 ^ d)
    (hNe : (ℓ₁, j₁) ≠ (ℓ₂, j₂)) :
    ∃ x : Fin (2 ^ d) → Bool,
      (source d).circuit.evalWires x (compWireInSource d ℓ₁ j₁ hℓ₁ hj₁) ≠
        (source d).circuit.evalWires x (compWireInSource d ℓ₂ j₂ hℓ₂ hj₂) := by
  simp only [source_evalWire_comp]
  by_cases hBlockEq : (ℓ₁ = ℓ₂ ∧ j₁ / 2 ^ ℓ₁ = j₂ / 2 ^ ℓ₂)
  · rcases hBlockEq with ⟨rfl, hDiv⟩
    have hjNe : j₁ ≠ j₂ := fun h => hNe (by subst h; rfl)
    obtain ⟨b, hbLt, hbDiff, hbAbove⟩ := exists_highest_diff_bit hDiv hjNe
    have hSameB1 : ∀ (a₁ a₂ : Nat) (hb1 : a₁.testBit b = false) (hb2 : a₂.testBit b = true)
        (haDiv : a₁ / 2 ^ (b + 1) = a₂ / 2 ^ (b + 1))
        (haAbove : ∀ t, b + 1 ≤ t → t < ℓ₁ → a₁.testBit t = a₂.testBit t)
        (ha1Lt : a₁ < 2 ^ d) (ha2Lt : a₂ < 2 ^ d),
        ∃ x : Fin (2 ^ d) → Bool,
          (buildCompBfly d ℓ₁ hℓ₁).evalWires x ⟨ℓ₁ * 2 ^ d + a₁, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ ≠
            (buildCompBfly d ℓ₁ hℓ₁).evalWires x ⟨ℓ₁ * 2 ^ d + a₂, by
              rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
      intro a₁ a₂ ha1Bit ha2Bit haDiv haAbove ha1Lt ha2Lt
      let y₀ : Fin (2 ^ d) → Bool := fun i =>
        decide (i.val / 2 ^ b = a₁ / 2 ^ b)
      obtain ⟨x, hxAgree, hxEval⟩ := eval_lift_above_branch d b y₀ a₁ ha1Lt ℓ₁ (by omega) hℓ₁
      have hx1 := hxEval a₁ ha1Lt rfl (fun _ _ _ => rfl)
      have hx2 := hxEval a₂ ha2Lt haDiv.symm (fun t ht1 ht2 => (haAbove t ht1 ht2).symm)
      have hFlip1Lt := ButterflyNet.flipBit_lt ha1Lt (by omega : b < d)
      have hFlip2Lt := ButterflyNet.flipBit_lt ha2Lt (by omega : b < d)
      have ha1DivNe : ButterflyNet.flipBit a₁ b / 2 ^ b ≠ a₁ / 2 ^ b := by
        intro hEq
        have := congrArg (fun n => n.testBit 0) hEq
        simp only [Nat.testBit_div_two_pow, Nat.zero_add,
          ButterflyNet.flipBit_testBit_self] at this
        cases a₁.testBit b <;> simp at this
      have ha2Side : a₂ / 2 ^ b = ButterflyNet.flipBit a₁ b / 2 ^ b := by
        apply Nat.eq_of_testBit_eq
        intro t
        rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
        rcases eq_or_ne t 0 with rfl | ht
        · simp only [Nat.zero_add, ButterflyNet.flipBit_testBit_self, ha1Bit, ha2Bit]
          rfl
        · rw [ButterflyNet.flipBit_testBit_gt (by omega)]
          have hT := congrArg (fun n => n.testBit (t - 1)) haDiv
          rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow] at hT
          have hEqPow : t - 1 + (b + 1) = t + b := by omega
          rw [hEqPow] at hT
          exact hT.symm
      have ha2FlipMain : ButterflyNet.flipBit a₂ b / 2 ^ b = a₁ / 2 ^ b := by
        apply Nat.eq_of_testBit_eq
        intro t
        rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
        rcases eq_or_ne t 0 with rfl | ht
        · simp only [Nat.zero_add, ButterflyNet.flipBit_testBit_self, ha1Bit, ha2Bit]
          rfl
        · rw [ButterflyNet.flipBit_testBit_gt (by omega)]
          have hT := congrArg (fun n => n.testBit (t - 1)) haDiv
          rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow] at hT
          have hEqPow : t - 1 + (b + 1) = t + b := by omega
          exact (hEqPow ▸ hT).symm
      have hyA1 : (buildCompBfly d b (by omega)).evalWires y₀ ⟨b * 2 ^ d + a₁, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ = true := by
        refine buildCompBfly_eval_const d b (by omega) a₁ ha1Lt true y₀ fun i _ hi => ?_
        simp [y₀, hi]
      have hyF1 : (buildCompBfly d b (by omega)).evalWires y₀
          ⟨b * 2 ^ d + ButterflyNet.flipBit a₁ b, by
            rw [LayeredRing.ringWires_eq]; nlinarith⟩ = false := by
        refine buildCompBfly_eval_const d b (by omega) _ hFlip1Lt false y₀ fun i _ hi => ?_
        have hNe : i / 2 ^ b ≠ a₁ / 2 ^ b := by rw [hi]; exact ha1DivNe
        simp [y₀, hNe]
      have hyA2 : (buildCompBfly d b (by omega)).evalWires y₀ ⟨b * 2 ^ d + a₂, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ = false := by
        refine buildCompBfly_eval_const d b (by omega) a₂ ha2Lt false y₀ fun i _ hi => ?_
        have hNe : i / 2 ^ b ≠ a₁ / 2 ^ b := by rw [hi, ha2Side]; exact ha1DivNe
        simp [y₀, hNe]
      have hyF2 : (buildCompBfly d b (by omega)).evalWires y₀
          ⟨b * 2 ^ d + ButterflyNet.flipBit a₂ b, by
            rw [LayeredRing.ringWires_eq]; nlinarith⟩ = true := by
        refine buildCompBfly_eval_const d b (by omega) _ hFlip2Lt true y₀ fun i _ hi => ?_
        dsimp only [y₀]
        rw [hi, ha2FlipMain]
        simp
      have hB1Eq : (buildCompBfly d (b + 1) (by omega)).evalWires y₀ ⟨(b + 1) * 2 ^ d + a₁, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ = false := by
        rw [buildCompBfly_eval_succ d b a₁ (by omega) ha1Lt, ha1Bit, hyA1, hyF1]
        decide
      have hB2Eq : (buildCompBfly d (b + 1) (by omega)).evalWires y₀ ⟨(b + 1) * 2 ^ d + a₂, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ = true := by
        rw [buildCompBfly_eval_succ d b a₂ (by omega) ha2Lt, ha2Bit, hyA2, hyF2]
        decide
      refine ⟨x, ?_⟩
      rw [hx1, hx2, hB1Eq, hB2Eq]
      decide
    have hDivB1 : j₁ / 2 ^ (b + 1) = j₂ / 2 ^ (b + 1) := by
      apply Nat.eq_of_testBit_eq
      intro t
      rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
      by_cases hLt : t + (b + 1) < ℓ₁
      · exact hbAbove (t + (b + 1)) (by omega) hLt
      · have hT := congrArg (fun n => n.testBit (t + (b + 1) - ℓ₁)) hDiv
        rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow] at hT
        have hSum : t + (b + 1) - ℓ₁ + ℓ₁ = t + (b + 1) := by omega
        rwa [hSum] at hT
    cases hJ1b : j₁.testBit b <;> cases hJ2b : j₂.testBit b
    · exact False.elim (hbDiff (by rw [hJ1b, hJ2b]))
    · exact hSameB1 j₁ j₂ hJ1b hJ2b hDivB1 hbAbove hj₁ hj₂
    · obtain ⟨x, hx⟩ := hSameB1 j₂ j₁ hJ2b hJ1b hDivB1.symm
        (fun t ht1 ht2 => (hbAbove t ht1 ht2).symm) hj₂ hj₁
      exact ⟨x, hx.symm⟩
    · exact False.elim (hbDiff (by rw [hJ1b, hJ2b]))
  · have hWitness : ∃ (ℓA jA ℓB jB : Nat) (hℓA : ℓA ≤ d) (hℓB : ℓB ≤ d)
        (hjA : jA < 2 ^ d) (hjB : jB < 2 ^ d) (k : Nat) (hk : k < 2 ^ d),
        k / 2 ^ ℓA = jA / 2 ^ ℓA ∧ k / 2 ^ ℓB ≠ jB / 2 ^ ℓB ∧
        ((ℓA = ℓ₁ ∧ jA = j₁ ∧ ℓB = ℓ₂ ∧ jB = j₂) ∨
         (ℓA = ℓ₂ ∧ jA = j₂ ∧ ℓB = ℓ₁ ∧ jB = j₁)) := by
      by_cases hL : ℓ₁ = ℓ₂
      · subst hL
        have hDNe : j₁ / 2 ^ ℓ₁ ≠ j₂ / 2 ^ ℓ₁ := fun h => hBlockEq ⟨rfl, h⟩
        exact ⟨ℓ₁, j₁, ℓ₁, j₂, hℓ₁, hℓ₂, hj₁, hj₂, j₁, hj₁, rfl, hDNe,
          Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
      · rcases Nat.lt_or_gt_of_ne hL with h12 | h21
        · let k₁ := (j₂ / 2 ^ ℓ₂) * 2 ^ ℓ₂
          let k₂ := k₁ + 2 ^ ℓ₁
          have hk1Lt : k₁ < 2 ^ d := by
            have := Nat.div_mul_le_self j₂ (2 ^ ℓ₂)
            omega
          have hk2Lt : k₂ < 2 ^ d := by
            have hPowPos2 : 0 < 2 ^ ℓ₂ := Nat.two_pow_pos ℓ₂
            have hPow12 : 2 ^ ℓ₁ < 2 ^ ℓ₂ := Nat.pow_lt_pow_right (by decide) h12
            have hQ : j₂ / 2 ^ ℓ₂ + 1 ≤ 2 ^ (d - ℓ₂) := by
              rw [Nat.succ_le_iff, Nat.div_lt_iff_lt_mul hPowPos2, ← Nat.pow_add,
                Nat.sub_add_cancel hℓ₂]
              exact hj₂
            have hMul : (j₂ / 2 ^ ℓ₂ + 1) * 2 ^ ℓ₂ ≤ 2 ^ d := by
              calc (j₂ / 2 ^ ℓ₂ + 1) * 2 ^ ℓ₂ ≤ 2 ^ (d - ℓ₂) * 2 ^ ℓ₂ :=
                    Nat.mul_le_mul_right _ hQ
                _ = 2 ^ d := by rw [← Nat.pow_add, Nat.sub_add_cancel hℓ₂]
            dsimp [k₂, k₁]
            rw [Nat.add_mul, Nat.one_mul] at hMul
            omega
          have hk1Div2 : k₁ / 2 ^ ℓ₂ = j₂ / 2 ^ ℓ₂ := by
            dsimp [k₁]; rw [Nat.mul_div_left _ (Nat.two_pow_pos ℓ₂)]
          have hk2Div2 : k₂ / 2 ^ ℓ₂ = j₂ / 2 ^ ℓ₂ := by
            dsimp [k₂, k₁]
            have hPow12 : 2 ^ ℓ₁ < 2 ^ ℓ₂ := Nat.pow_lt_pow_right (by decide) h12
            rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos ℓ₂), Nat.div_eq_of_lt hPow12,
              Nat.add_zero]
          have hkNe : k₁ / 2 ^ ℓ₁ ≠ k₂ / 2 ^ ℓ₁ := by
            dsimp [k₂]
            rw [Nat.add_div_right _ (Nat.two_pow_pos ℓ₁)]
            omega
          by_cases h1 : k₁ / 2 ^ ℓ₁ = j₁ / 2 ^ ℓ₁
          · exact ⟨ℓ₂, j₂, ℓ₁, j₁, hℓ₂, hℓ₁, hj₂, hj₁, k₂, hk2Lt, hk2Div2,
              by rw [← h1]; exact hkNe.symm, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
          · exact ⟨ℓ₂, j₂, ℓ₁, j₁, hℓ₂, hℓ₁, hj₂, hj₁, k₁, hk1Lt, hk1Div2, h1,
              Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
        · let k₁ := (j₁ / 2 ^ ℓ₁) * 2 ^ ℓ₁
          let k₂ := k₁ + 2 ^ ℓ₂
          have hk1Lt : k₁ < 2 ^ d := by
            have := Nat.div_mul_le_self j₁ (2 ^ ℓ₁)
            omega
          have hk2Lt : k₂ < 2 ^ d := by
            have hPowPos1 : 0 < 2 ^ ℓ₁ := Nat.two_pow_pos ℓ₁
            have hPow21 : 2 ^ ℓ₂ < 2 ^ ℓ₁ := Nat.pow_lt_pow_right (by decide) h21
            have hQ : j₁ / 2 ^ ℓ₁ + 1 ≤ 2 ^ (d - ℓ₁) := by
              rw [Nat.succ_le_iff, Nat.div_lt_iff_lt_mul hPowPos1, ← Nat.pow_add,
                Nat.sub_add_cancel hℓ₁]
              exact hj₁
            have hMul : (j₁ / 2 ^ ℓ₁ + 1) * 2 ^ ℓ₁ ≤ 2 ^ d := by
              calc (j₁ / 2 ^ ℓ₁ + 1) * 2 ^ ℓ₁ ≤ 2 ^ (d - ℓ₁) * 2 ^ ℓ₁ :=
                    Nat.mul_le_mul_right _ hQ
                _ = 2 ^ d := by rw [← Nat.pow_add, Nat.sub_add_cancel hℓ₁]
            dsimp [k₂, k₁]
            rw [Nat.add_mul, Nat.one_mul] at hMul
            omega
          have hk1Div1 : k₁ / 2 ^ ℓ₁ = j₁ / 2 ^ ℓ₁ := by
            dsimp [k₁]; rw [Nat.mul_div_left _ (Nat.two_pow_pos ℓ₁)]
          have hk2Div1 : k₂ / 2 ^ ℓ₁ = j₁ / 2 ^ ℓ₁ := by
            dsimp [k₂, k₁]
            have hPow21 : 2 ^ ℓ₂ < 2 ^ ℓ₁ := Nat.pow_lt_pow_right (by decide) h21
            rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos ℓ₁), Nat.div_eq_of_lt hPow21,
              Nat.add_zero]
          have hkNe : k₁ / 2 ^ ℓ₂ ≠ k₂ / 2 ^ ℓ₂ := by
            dsimp [k₂]
            rw [Nat.add_div_right _ (Nat.two_pow_pos ℓ₂)]
            omega
          by_cases h2 : k₁ / 2 ^ ℓ₂ = j₂ / 2 ^ ℓ₂
          · exact ⟨ℓ₁, j₁, ℓ₂, j₂, hℓ₁, hℓ₂, hj₁, hj₂, k₂, hk2Lt, hk2Div1,
              by rw [← h2]; exact hkNe.symm, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
          · exact ⟨ℓ₁, j₁, ℓ₂, j₂, hℓ₁, hℓ₂, hj₁, hj₂, k₁, hk1Lt, hk1Div1, h2,
              Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    obtain ⟨ℓA, jA, ℓB, jB, hℓA, hℓB, hjA, hjB, k, hk, hkA, hkB, hCases⟩ := hWitness
    obtain ⟨x, hxTog⟩ := buildCompBfly_eval_toggle d ℓA hℓA jA hjA k hk hkA
    let x' := Function.update x ⟨k, hk⟩ (!(x ⟨k, hk⟩))
    have hBStay : (buildCompBfly d ℓB hℓB).evalWires x ⟨ℓB * 2 ^ d + jB, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
        (buildCompBfly d ℓB hℓB).evalWires x' ⟨ℓB * 2 ^ d + jB, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
      refine buildCompBfly_eval_ext d ℓB hℓB jB hjB x x' fun i hi hiDiv => ?_
      have hik : (⟨i, hi⟩ : Fin (2 ^ d)) ≠ ⟨k, hk⟩ := by
        intro hEq
        have := congrArg Fin.val hEq
        dsimp at this
        subst this
        exact hkB hiDiv
      exact (Function.update_of_ne hik _ x).symm
    by_cases hEqB : (buildCompBfly d ℓA hℓA).evalWires x ⟨ℓA * 2 ^ d + jA, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
        (buildCompBfly d ℓB hℓB).evalWires x ⟨ℓB * 2 ^ d + jB, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩
    · have hx'Ne : (buildCompBfly d ℓA hℓA).evalWires x' ⟨ℓA * 2 ^ d + jA, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ ≠
          (buildCompBfly d ℓB hℓB).evalWires x' ⟨ℓB * 2 ^ d + jB, by
            rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
        intro hEq'
        apply hxTog
        rw [hEqB, hBStay, ← hEq']
      rcases hCases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨x', hx'Ne⟩
      · exact ⟨x', hx'Ne.symm⟩
    · rcases hCases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨x, hEqB⟩
      · exact ⟨x, fun h => hEqB h.symm⟩

private lemma boolToZMod2_and_add_or (a b : Bool) :
    boolToZMod2 (a && b) + boolToZMod2 (a || b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

private lemma sum_pair_flipBit {d ℓ : Nat} (hℓ : ℓ < d) (f : Fin (2 ^ d) → ZMod 2) :
    ∑ j : Fin (2 ^ d), f j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ d) => j.val.testBit ℓ = false),
        (f j + f ⟨ButterflyNet.flipBit j.val ℓ, ButterflyNet.flipBit_lt j.isLt hℓ⟩) := by
  classical
  let S₀ := Finset.univ.filter (fun j : Fin (2 ^ d) => j.val.testBit ℓ = false)
  let S₁ := Finset.univ.filter (fun j : Fin (2 ^ d) => ¬ (j.val.testBit ℓ = false))
  have hSplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (2 ^ d)))
    (fun j : Fin (2 ^ d) => j.val.testBit ℓ = false) f
  have hPair : ∑ j ∈ S₁, f j =
      ∑ j ∈ S₀, f ⟨ButterflyNet.flipBit j.val ℓ, ButterflyNet.flipBit_lt j.isLt hℓ⟩ := by
    refine (Finset.sum_bij
      (fun j _ => ⟨ButterflyNet.flipBit j.val ℓ, ButterflyNet.flipBit_lt j.isLt hℓ⟩)
      ?_ ?_ ?_ (fun _ _ => rfl)).symm
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ButterflyNet.flipBit_testBit_self, hj.2]
      decide
    · intro a _ b _ hEq
      have hVal := congrArg Fin.val hEq
      dsimp at hVal
      have hInv := congrArg (fun z => ButterflyNet.flipBit z ℓ) hVal
      rw [ButterflyNet.flipBit_involutive, ButterflyNet.flipBit_involutive] at hInv
      exact Fin.ext hInv
    · intro y hy
      rw [Finset.mem_filter] at hy
      have hyT : y.val.testBit ℓ = true := Bool.eq_true_of_not_eq_false hy.2
      refine ⟨⟨ButterflyNet.flipBit y.val ℓ, ButterflyNet.flipBit_lt y.isLt hℓ⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [ButterflyNet.flipBit_testBit_self, hyT]; rfl⟩
      · exact Fin.ext (ButterflyNet.flipBit_involutive y.val ℓ)
  rw [← hSplit, hPair, ← Finset.sum_add_distrib]

/-- **Exact Parity Conservation (`ℤ/2ℤ`)**: at every layer `ℓ ≤ d` of the comparator
butterfly, the `ℤ/2ℤ` sum of all `2^d` wire values equals the input parity `∑ x_j`. -/
theorem layer_xor_invariant (d ℓ : Nat) (hℓ : ℓ ≤ d) (x : Fin (2 ^ d) → Bool) :
    ∑ j : Fin (2 ^ d), boolToZMod2
        ((source d).circuit.evalWires x (compWireInSource d ℓ j.val hℓ j.isLt)) =
      ∑ j : Fin (2 ^ d), boolToZMod2 (x j) := by
  simp only [source_evalWire_comp]
  induction ℓ with
  | zero =>
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [buildCompBfly, HybridCircuit.evalWires]
      congr 2
  | succ ℓ ih =>
      rw [sum_pair_flipBit hℓ]
      rw [← ih (Nat.le_of_lt hℓ), sum_pair_flipBit hℓ]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter] at hj
      have hjFalse : j.val.testBit ℓ = false := hj.2
      have hFlipLt := ButterflyNet.flipBit_lt j.isLt hℓ
      have hj'True : (ButterflyNet.flipBit j.val ℓ).testBit ℓ = true := by
        rw [ButterflyNet.flipBit_testBit_self, hjFalse]
        rfl
      rw [buildCompBfly_eval_succ d ℓ j.val hℓ j.isLt x,
        buildCompBfly_eval_succ d ℓ _ hℓ hFlipLt x]
      simp only [hjFalse, ↓reduceIte, hj'True, Bool.true_eq_false]
      have hInv : ButterflyNet.flipBit (ButterflyNet.flipBit j.val ℓ) ℓ = j.val :=
        ButterflyNet.flipBit_involutive j.val ℓ
      have hB : (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x
          ⟨ℓ * 2 ^ d + ButterflyNet.flipBit (ButterflyNet.flipBit j.val ℓ) ℓ, by
            rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ =
          (buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x
            ⟨ℓ * 2 ^ d + j.val, by rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ := by
        congr 1; exact Fin.ext (by simp [hInv])
      rw [hB, Bool.or_comm]
      exact boolToZMod2_and_add_or _ _

private lemma heapWireVal_lt_frontier (d m h : Nat) (_hm : m ≤ 2 ^ d - 1)
    (hh1 : 2 ^ d - m ≤ h) (hh2 : h < 2 * (2 ^ d - m)) :
    heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
  rw [LayeredRing.ringWires_eq]
  dsimp [heapWireVal]
  have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
  have hMul2 : d * 2 ^ d + 2 ^ d = (d + 1) * 2 ^ d := by ring
  split_ifs <;> omega

private def evalXorAt (d m : Nat) (hm : m ≤ 2 ^ d - 1) (x : Fin (2 ^ d) → Bool)
    (h : Nat) : ZMod 2 :=
  if hLt : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m then
    boolToZMod2 ((appendXorGates d m hm).evalWires x ⟨heapWireVal d h, hLt⟩)
  else 0

private lemma evalXorAt_eq_of_lt {d m : Nat} {hm : m ≤ 2 ^ d - 1}
    {x : Fin (2 ^ d) → Bool} {h : Nat}
    (hLt : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m) :
    evalXorAt d m hm x h =
      boolToZMod2 ((appendXorGates d m hm).evalWires x ⟨heapWireVal d h, hLt⟩) := by
  simp only [evalXorAt, hLt, ↓reduceDIte]

private lemma evalXorAt_step_old (d m : Nat) (hm : m < 2 ^ d - 1) (x : Fin (2 ^ d) → Bool)
    (h : Nat) (hh1 : 2 ^ d - m ≤ h) (hh2 : h < 2 * (2 ^ d - (m + 1))) :
    evalXorAt d (m + 1) hm x h = evalXorAt d m (Nat.le_of_lt hm) x h := by
  have hLt0 : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m :=
    heapWireVal_lt_frontier d m h (Nat.le_of_lt hm) hh1 (by omega)
  have hLt1 : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + (m + 1) :=
    Nat.lt_succ_of_lt hLt0
  rw [evalXorAt_eq_of_lt hLt1, evalXorAt_eq_of_lt hLt0]
  dsimp [appendXorGates]
  exact congrArg boolToZMod2
    (HybridCircuit.evalWires_snoc_castSucc (appendXorGates d m (Nat.le_of_lt hm)) _ x
      ⟨heapWireVal d h, hLt0⟩)

private lemma evalXorAt_step_new (d m : Nat) (hm : m < 2 ^ d - 1) (x : Fin (2 ^ d) → Bool) :
    let p := 2 ^ d - 1 - m
    evalXorAt d (m + 1) hm x p =
      evalXorAt d m (Nat.le_of_lt hm) x (2 * p) +
        evalXorAt d m (Nat.le_of_lt hm) x (2 * p + 1) := by
  intro p
  have hBase := LayeredRing.ringWires_eq (2 ^ d) d
  have hpLt : p < 2 ^ d := by
    have := Nat.two_pow_pos d
    dsimp [p]; omega
  have hValP : heapWireVal d p = LayeredRing.ringWires (2 ^ d) d + m := by
    rw [hBase]
    dsimp [heapWireVal]
    simp only [hpLt, ↓reduceIte]
    have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
    dsimp [p]; omega
  have hLtP : heapWireVal d p < LayeredRing.ringWires (2 ^ d) d + (m + 1) := by omega
  have hLt2P : heapWireVal d (2 * p) < LayeredRing.ringWires (2 ^ d) d + m :=
    heapWireVal_lt_xorStep d m (2 * p) hm (Or.inl rfl)
  have hLt2P1 : heapWireVal d (2 * p + 1) < LayeredRing.ringWires (2 ^ d) d + m :=
    heapWireVal_lt_xorStep d m (2 * p + 1) hm (Or.inr rfl)
  rw [evalXorAt_eq_of_lt hLtP, evalXorAt_eq_of_lt hLt2P, evalXorAt_eq_of_lt hLt2P1]
  have hFinLast : (⟨heapWireVal d p, hLtP⟩ :
      Fin (LayeredRing.ringWires (2 ^ d) d + (m + 1))) = Fin.last _ :=
    Fin.ext hValP
  rw [hFinLast]
  change boolToZMod2 (((appendXorGates d m (Nat.le_of_lt hm)).snoc _).evalWires x (Fin.last _)) = _
  rw [HybridCircuit.evalWires_snoc_last]
  dsimp [HybridGate.eval]
  exact boolToZMod2_xor _ _

private lemma appendXorGates_zmod2_frontier (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    (x : Fin (2 ^ d) → Bool) :
    ∑ h ∈ Finset.Ico (2 ^ d - m) (2 * (2 ^ d - m)), evalXorAt d m hm x h =
      ∑ j : Fin (2 ^ d), boolToZMod2 (x j) := by
  induction m with
  | zero =>
      simp only [Nat.sub_zero]
      have hInv := layer_xor_invariant d d le_rfl x
      simp only [source_evalWire_comp] at hInv
      rw [← hInv]
      refine (Finset.sum_bij (fun j _ => 2 ^ d + j.val) ?_ ?_ ?_ ?_).symm
      · intro j _
        rw [Finset.mem_Ico]
        exact ⟨Nat.le_add_right _ _, by rw [Nat.two_mul]; exact Nat.add_lt_add_left j.isLt _⟩
      · intro a _ b _ hEq
        exact Fin.ext (by omega)
      · intro h hh
        rw [Finset.mem_Ico, Nat.two_mul] at hh
        exact ⟨⟨h - 2 ^ d, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
      · intro j _
        have hNot : ¬ (2 ^ d + j.val < 2 ^ d) := by omega
        have hVal : heapWireVal d (2 ^ d + j.val) = d * 2 ^ d + j.val := by
          dsimp [heapWireVal]
          simp only [hNot, ↓reduceIte, Nat.add_sub_cancel_left]
        have hLt : heapWireVal d (2 ^ d + j.val) < LayeredRing.ringWires (2 ^ d) d + 0 := by
          rw [hVal, LayeredRing.ringWires_eq]
          nlinarith [j.isLt]
        rw [evalXorAt_eq_of_lt hLt]
        congr 2
        exact Fin.ext hVal.symm
  | succ m ih =>
      set p := 2 ^ d - 1 - m
      have hpPos : 1 ≤ p := by dsimp [p]; omega
      have hSub1 : 2 ^ d - (m + 1) = p := by dsimp [p]; omega
      have hSub0 : 2 ^ d - m = p + 1 := by dsimp [p]; omega
      rw [hSub1]
      have hLtP : p < 2 * p := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot hLtP]
      have hSumIco : ∑ h ∈ Finset.Ico (p + 1) (2 * p), evalXorAt d (m + 1) hm x h =
          ∑ h ∈ Finset.Ico (p + 1) (2 * p), evalXorAt d m (Nat.le_of_lt hm) x h := by
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [Finset.mem_Ico] at hh
        exact evalXorAt_step_old d m hm x h (by omega) (by omega)
      rw [hSumIco, evalXorAt_step_new d m hm x]
      have ih' := ih (Nat.le_of_lt hm)
      rw [hSub0] at ih'
      have hTop1 : p + 1 ≤ 2 * p := by omega
      have hTop2 : p + 1 ≤ 2 * p + 1 := by omega
      have hSplit : ∑ h ∈ Finset.Ico (p + 1) (2 * (p + 1)),
            evalXorAt d m (Nat.le_of_lt hm) x h =
          (∑ h ∈ Finset.Ico (p + 1) (2 * p), evalXorAt d m (Nat.le_of_lt hm) x h) +
            evalXorAt d m (Nat.le_of_lt hm) x (2 * p) +
            evalXorAt d m (Nat.le_of_lt hm) x (2 * p + 1) := by
        rw [show 2 * (p + 1) = (2 * p + 1) + 1 by ring]
        rw [Finset.sum_Ico_succ_top hTop2, Finset.sum_Ico_succ_top hTop1]
      dsimp [p] at hSplit
      rw [← ih', hSplit]
      ring

lemma source_eval_zmod2 (d : Nat) (x : Fin (2 ^ d) → Bool) :
    boolToZMod2 ((source d).eval x) = ∑ j : Fin (2 ^ d), boolToZMod2 (x j) := by
  have hF := appendXorGates_zmod2_frontier d (2 ^ d - 1) le_rfl x
  have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hSub : 2 ^ d - (2 ^ d - 1) = 1 := by omega
  rw [hSub, show 2 * 1 = 2 by decide] at hF
  have hIco : Finset.Ico 1 2 = {1} := by decide
  rw [hIco, Finset.sum_singleton] at hF
  have hLt : heapWireVal d 1 < LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) := by
    rw [← source_output_val]
    exact (source d).output.isLt
  rw [evalXorAt_eq_of_lt hLt] at hF
  have hOut : (⟨heapWireVal d 1, hLt⟩ : Fin (source d).wires) = (source d).output :=
    Fin.ext (source_output_val d).symm
  change boolToZMod2 ((source d).circuit.evalWires x (source d).output) = _
  rw [← hOut]
  exact hF

/-- **Closed-Form Exact Model Count (`#Circuit-SAT`)**: `ClosedComparatorXor.source d` accepts
exactly half of all Boolean inputs (`2 ^ (2 ^ d - 1)` out of `2 ^ (2 ^ d)`). -/
theorem acceptCount_eq (d : Nat) :
    Fintype.card { x : Fin (2 ^ d) → Bool // (source d).eval x = true } = 2 ^ (2 ^ d - 1) := by
  classical
  rw [Fintype.card_subtype]
  let S := Finset.univ.filter (fun x : Fin (2 ^ d) → Bool => (source d).eval x = true)
  let T := Finset.univ.filter (fun x : Fin (2 ^ d) → Bool => (source d).eval x = false)
  let i₀ : Fin (2 ^ d) := ⟨0, Nat.two_pow_pos d⟩
  let flip0 : (Fin (2 ^ d) → Bool) → (Fin (2 ^ d) → Bool) :=
    fun x => Function.update x i₀ (!(x i₀))
  have hFlipInv : ∀ x, flip0 (flip0 x) = x := by
    intro x
    funext j
    by_cases hj : j = i₀
    · subst hj; simp [flip0]
    · simp [flip0, Function.update_of_ne hj]
  have hFlipSum : ∀ x,
      (∑ j : Fin (2 ^ d), boolToZMod2 (flip0 x j)) =
        (∑ j : Fin (2 ^ d), boolToZMod2 (x j)) + 1 := by
    intro x
    have h1 := Finset.add_sum_erase Finset.univ (fun j => boolToZMod2 (flip0 x j)) (Finset.mem_univ i₀)
    have h2 := Finset.add_sum_erase Finset.univ (fun j => boolToZMod2 (x j)) (Finset.mem_univ i₀)
    have hErase : ∑ j ∈ Finset.univ.erase i₀, boolToZMod2 (flip0 x j) =
        ∑ j ∈ Finset.univ.erase i₀, boolToZMod2 (x j) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_erase] at hj
      simp [flip0, Function.update_of_ne hj.1]
    have hNot : boolToZMod2 (!(x i₀)) = boolToZMod2 (x i₀) + 1 := by
      cases x i₀ <;> decide
    have hFlip0 : flip0 x i₀ = !(x i₀) := by simp [flip0]
    rw [← h1, hFlip0, hNot, hErase]
    rw [← h2]
    ring
  have hEvalFlip : ∀ x, ((source d).eval x = true ↔ (source d).eval (flip0 x) = false) := by
    intro x
    have hx := source_eval_zmod2 d x
    have hfx := source_eval_zmod2 d (flip0 x)
    rw [hFlipSum] at hfx
    cases hxB : (source d).eval x <;> cases hfxB : (source d).eval (flip0 x)
    · have h0 : boolToZMod2 false = (0 : ZMod 2) := rfl
      rw [hxB] at hx; rw [hfxB] at hfx
      rw [h0] at hx hfx
      rw [← hx] at hfx
      exact absurd hfx (by decide)
    · simp
    · simp
    · have h1 : boolToZMod2 true = (1 : ZMod 2) := rfl
      rw [hxB] at hx; rw [hfxB] at hfx
      rw [h1] at hx hfx
      rw [← hx] at hfx
      exact absurd hfx (by decide)
  have hCardEq : S.card = T.card := by
    refine Finset.card_bij (fun x _ => flip0 x) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, (hEvalFlip x).mp hx.2⟩
    · intro a _ b _ h
      have := congrArg flip0 h
      rwa [hFlipInv, hFlipInv] at this
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨flip0 y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hFlipInv y⟩
      by_contra hFalse
      have hF : (source d).eval (flip0 y) = false := Bool.eq_false_iff.mpr hFalse
      have hT := (hEvalFlip y).mpr hF
      rw [hy.2] at hT
      exact absurd hT (by decide)
  have hDisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rw [Finset.mem_filter] at hxS hxT
    rw [hxS.2] at hxT
    exact absurd hxT.2 (by decide)
  have hUnion : S ∪ T = Finset.univ := by
    ext x
    simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases (source d).eval x <;> simp
  have hSum : S.card + T.card = 2 ^ (2 ^ d) := by
    rw [← Finset.card_union_of_disjoint hDisj, hUnion, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hPow : 2 ^ (2 ^ d) = 2 * 2 ^ (2 ^ d - 1) := by
    calc 2 ^ (2 ^ d) = 2 ^ ((2 ^ d - 1) + 1) := by rw [Nat.sub_add_cancel hPos]
      _ = 2 * 2 ^ (2 ^ d - 1) := Nat.pow_succ'
  linarith [hCardEq, hSum, hPow]

end ClosedComparatorXor

end PvsNP
