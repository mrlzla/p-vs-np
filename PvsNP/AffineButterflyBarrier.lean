module

public import PvsNP.SeparatorBarrier
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Treewidth, Tensor-Contraction Width, and the $\mathbb{F}_2$-Affine Butterfly Separation

Sharpens and breaks the `ButterflyNet` topological barrier from `SeparatorBarrier.lean`:

1. **Treewidth and tensor-contraction width lower bounds on `ButterflyNet`**:
   - `DecompTree`, `TreeDecomp`: arbitrary-degree rooted tree decompositions satisfying wire
     coverage, edge coverage, and the running-intersection property.
   - `ButterflyNet.butterfly_treewidth_linear` (`2 ^ d ≤ 18 * (td.width + 1)`) and
     `ButterflyNet.butterfly_escapes_sublinear_treewidth` (`¬ width = o(n)`).
   - `ContractionTree`, `ValidContractionTree`: binary tensor-contraction trees measuring maximum
     cut boundary size `contractionWidth` over all contraction steps.
   - `ButterflyNet.butterfly_contractionWidth_linear`,
     `ButterflyNet.butterfly_gateContractionWidth_linear` (`2 ^ d ≤ 18 * ct.contractionWidth` for
     every fan-in-2 gate contraction tree), and
     `ButterflyNet.butterfly_escapes_sublinear_contractionWidth` (`¬ contractionWidth = o(n)`).

2. **`HybridCircuit`, $\mathbb{F}_2$ affine subspace counting, and universal $3^q$ branching**:
   - `HybridGate` (`and`/`or`/`xor`/`not`), `HybridCircuit`, `HybridCircuitInstance`,
     `HybridCircuitEdge`, and embedding `HybridCircuit.ofCircuit`.
   - `AffineForm`, `LinearSystem`: exact `ZMod 2` linear-system cardinality
     `linearSystem_card_eq_of_nonempty` and `linearSystem_card_eq_zero_or_pow`
     (`0` or `2 ^ (n - finrank range)`).
   - `compileAffineBranches` and `HybridCircuitInstance.acceptCount_eq_sum_affine`: universal
     exact decomposition into `3 ^ q` disjoint affine systems (`q = nonlinearCount`), giving
     `2 ^ o(n)` `#Circuit-SAT` (`affineBranchLogTimeBudget_isLittleO`) whenever `q = o(n)`.

3. **Explicit `HybridButterflyNet` exponential separation**:
   - `HybridButterflyNet.source d q` preserves the exact undirected graph topology of
     `ButterflyNet.source d` (`hybridBfly_edge_iff`), keeping `Ω(n)` treewidth and contraction
     width (`hybridBfly_treewidth_linear`, `hybridBfly_gateContractionWidth_linear`) for every `q`.
   - At `q = 0`, `XorButterflyNet` collapses to exact closed-form `#Circuit-SAT` count
     `2 ^ (2 ^ d - 1)` (`xorBfly_acceptCount`).
   - For any `q i = o(2 ^ d i)`, `hybridBfly_subexponential_of_sublinear_nonlinear` puts exact
     `#Circuit-SAT` inside `2 ^ o(n)`, whereas all-nonlinear `ButterflyNet` (`q = d * 2 ^ d`)
     escapes `o(n)` (`butterfly_allNonlinear_escapes_sublinear_budget`).
-/

namespace PvsNP

open Asymptotics Filter

/-! ### 1. Generic Graph-Walk Helpers, Tree Decompositions, and Contraction Trees -/

/-- Undirected reachability avoiding `S` over any relation `E`. -/
inductive RelReachAvoiding {w : Nat} (E : Fin w → Fin w → Prop) (S : Finset (Fin w)) :
    Fin w → Fin w → Prop where
  | refl (u : Fin w) (hu : u ∉ S) : RelReachAvoiding E S u u
  | step {u v z : Fin w} (hu : u ∉ S) (hEdge : E u v)
      (hRest : RelReachAvoiding E S v z) : RelReachAvoiding E S u z

theorem RelReachAvoiding.trans {w : Nat} {E : Fin w → Fin w → Prop} {S : Finset (Fin w)}
    {u v z : Fin w} (h1 : RelReachAvoiding E S u v) (h2 : RelReachAvoiding E S v z) :
    RelReachAvoiding E S u z := by
  induction h1 with
  | refl _ _ => exact h2
  | step hu hEdge _ ih => exact .step hu hEdge (ih h2)

theorem RelReachAvoiding.map_rel {w : Nat} {E₁ E₂ : Fin w → Fin w → Prop} {S : Finset (Fin w)}
    (hMap : ∀ {u v}, E₁ u v → E₂ u v) {u v : Fin w} (hReach : RelReachAvoiding E₁ S u v) :
    RelReachAvoiding E₂ S u v := by
  induction hReach with
  | refl u hu => exact .refl u hu
  | step hu hEdge _ ih => exact .step hu (hMap hEdge) ih

theorem RelReachAvoiding.start_not_mem {w : Nat} {E : Fin w → Fin w → Prop}
    {S : Finset (Fin w)} {u v : Fin w} (h : RelReachAvoiding E S u v) : u ∉ S := by
  cases h with
  | refl _ hu => exact hu
  | step hu _ _ => exact hu

theorem RelReachAvoiding.preserves_pred {w : Nat} {E : Fin w → Fin w → Prop}
    {S : Finset (Fin w)} (P : Fin w → Prop)
    (hStep : ∀ {u v}, u ∉ S → v ∉ S → E u v → P u → P v)
    {u v : Fin w} (hReach : RelReachAvoiding E S u v) (hu : P u) : P v := by
  induction hReach with
  | refl _ _ => exact hu
  | step huS hEdge hRest ih => exact ih (hStep huS hRest.start_not_mem hEdge hu)

theorem undirectedReachAvoiding_iff_rel {n w : Nat} (c : Circuit n w) (S : Finset (Fin w))
    (u v : Fin w) :
    UndirectedReachAvoiding c S u v ↔ RelReachAvoiding (CircuitEdge c) S u v := by
  constructor
  · intro h
    induction h with
    | refl x hx => exact .refl x hx
    | step hx hEdge _ ih => exact .step hx hEdge ih
  · intro h
    induction h with
    | refl x hx => exact .refl x hx
    | step hx hEdge _ ih => exact .step hx hEdge ih

/-- Arbitrary-degree rooted tree for tree decompositions over vertex type `α`. -/
inductive DecompTree (α : Type) where
  | node (bag : Finset α) (children : List (DecompTree α))

namespace DecompTree

mutual
  def subtreeWires {α : Type} [DecidableEq α] : DecompTree α → Finset α
    | .node bag cs => bag ∪ listWires cs

  def listWires {α : Type} [DecidableEq α] : List (DecompTree α) → Finset α
    | [] => ∅
    | c :: cs => c.subtreeWires ∪ listWires cs
end

mutual
  def maxBagCard {α : Type} : DecompTree α → Nat
    | .node bag cs => max bag.card (listMaxBagCard cs)

  def listMaxBagCard {α : Type} : List (DecompTree α) → Nat
    | [] => 0
    | c :: cs => max c.maxBagCard (listMaxBagCard cs)
end

mutual
  def ContainsPair {α : Type} (u v : α) : DecompTree α → Prop
    | .node bag cs => (u ∈ bag ∧ v ∈ bag) ∨ ListContainsPair u v cs

  def ListContainsPair {α : Type} (u v : α) : List (DecompTree α) → Prop
    | [] => False
    | c :: cs => c.ContainsPair u v ∨ ListContainsPair u v cs
end

mutual
  def RunningIntersection {α : Type} [DecidableEq α] (outside : Finset α) : DecompTree α → Prop
    | .node bag cs =>
      (∀ u, u ∈ (DecompTree.node bag cs).subtreeWires → u ∈ outside → u ∈ bag) ∧
        ListRunningIntersection (outside ∪ bag) bag cs

  def ListRunningIntersection {α : Type} [DecidableEq α] (outside parentBag : Finset α) :
      List (DecompTree α) → Prop
    | [] => True
    | c :: cs =>
      (∀ u, u ∈ c.subtreeWires → u ∈ listWires cs → u ∈ parentBag) ∧
        c.RunningIntersection (outside ∪ listWires cs) ∧
        ListRunningIntersection (outside ∪ c.subtreeWires) parentBag cs
end

theorem listWires_subset_of_mem {α : Type} [DecidableEq α] {c : DecompTree α}
    {cs : List (DecompTree α)} (hc : c ∈ cs) : c.subtreeWires ⊆ listWires cs := by
  induction cs with
  | nil => simp at hc
  | cons a rest ih =>
    simp only [listWires]
    rcases List.mem_cons.mp hc with rfl | hMem
    · exact Finset.subset_union_left
    · exact (ih hMem).trans Finset.subset_union_right

theorem mem_listWires_iff_exists {α : Type} [DecidableEq α] {cs : List (DecompTree α)} {u : α} :
    u ∈ listWires cs ↔ ∃ i : Fin cs.length, u ∈ (cs[i]).subtreeWires := by
  induction cs with
  | nil =>
    simp [listWires]
  | cons c rest ih =>
    simp only [listWires, Finset.mem_union, ih]
    constructor
    · rintro (hc | ⟨i, hi⟩)
      · exact ⟨⟨0, Nat.succ_pos _⟩, hc⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact Or.inl hi
      | succ j => exact Or.inr ⟨j, hi⟩

mutual
  theorem containsPair_mem_subtreeWires {α : Type} [DecidableEq α] :
      ∀ {t : DecompTree α} {u v : α}, t.ContainsPair u v → u ∈ t.subtreeWires ∧ v ∈ t.subtreeWires
    | .node bag cs, u, v, h => by
      simp only [ContainsPair] at h
      simp only [subtreeWires, Finset.mem_union]
      rcases h with ⟨hu, hv⟩ | hList
      · exact ⟨Or.inl hu, Or.inl hv⟩
      · obtain ⟨hu, hv⟩ := listContainsPair_mem_listWires hList
        exact ⟨Or.inr hu, Or.inr hv⟩

  theorem listContainsPair_mem_listWires {α : Type} [DecidableEq α] :
      ∀ {cs : List (DecompTree α)} {u v : α},
        ListContainsPair u v cs → u ∈ listWires cs ∧ v ∈ listWires cs
    | [], _, _, h => False.elim h
    | c :: cs, u, v, h => by
      simp only [ListContainsPair] at h
      simp only [listWires, Finset.mem_union]
      rcases h with hC | hRest
      · obtain ⟨hu, hv⟩ := containsPair_mem_subtreeWires hC
        exact ⟨Or.inl hu, Or.inl hv⟩
      · obtain ⟨hu, hv⟩ := listContainsPair_mem_listWires hRest
        exact ⟨Or.inr hu, Or.inr hv⟩
end

theorem listContainsPair_iff_exists {α : Type} {cs : List (DecompTree α)} {u v : α} :
    ListContainsPair u v cs ↔ ∃ i : Fin cs.length, (cs[i]).ContainsPair u v := by
  induction cs with
  | nil =>
    simp [ListContainsPair]
  | cons c rest ih =>
    simp only [ListContainsPair, ih]
    constructor
    · rintro (hc | ⟨i, hi⟩)
      · exact ⟨⟨0, Nat.succ_pos _⟩, hc⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      cases i using Fin.cases with
      | zero => exact Or.inl hi
      | succ j => exact Or.inr ⟨j, hi⟩

theorem listWires_disjoint_of_running {α : Type} [DecidableEq α] (outside parentBag : Finset α) :
    ∀ {cs : List (DecompTree α)},
      ListRunningIntersection outside parentBag cs →
      ∀ (i j : Fin cs.length), i ≠ j →
        ∀ u, u ∈ (cs[i]).subtreeWires → u ∈ (cs[j]).subtreeWires → u ∈ parentBag
  | [], _, i, _, _, _, _, _ => i.elim0
  | c :: rest, hLRI, i, j, hNe, u, huI, huJ => by
    rcases hLRI with ⟨hHeadDisj, _, hTail⟩
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact absurd rfl hNe
      | succ j' =>
        exact hHeadDisj u huI (listWires_subset_of_mem (List.getElem_mem j'.isLt) huJ)
    | succ i' =>
      cases j using Fin.cases with
      | zero =>
        exact hHeadDisj u huJ (listWires_subset_of_mem (List.getElem_mem i'.isLt) huI)
      | succ j' =>
        have hNe' : i' ≠ j' := fun h => hNe (congrArg Fin.succ h)
        exact listWires_disjoint_of_running (outside ∪ c.subtreeWires) parentBag hTail i' j' hNe' u
          huI huJ

mutual
  theorem subtreeWires_one_le_maxBagCard {α : Type} [DecidableEq α] :
      ∀ {t : DecompTree α} {u : α}, u ∈ t.subtreeWires → 1 ≤ t.maxBagCard
    | .node bag cs, u, hu => by
      simp only [subtreeWires, Finset.mem_union] at hu
      rcases hu with huB | huL
      · exact Nat.le_trans (Finset.card_pos.mpr ⟨u, huB⟩) (le_max_left _ _)
      · exact (listWires_one_le_listMaxBagCard huL).trans (le_max_right _ _)

  theorem listWires_one_le_listMaxBagCard {α : Type} [DecidableEq α] :
      ∀ {cs : List (DecompTree α)} {u : α}, u ∈ listWires cs → 1 ≤ listMaxBagCard cs
    | [], _, hu => by simp [listWires] at hu
    | c :: rest, u, hu => by
      simp only [listWires, Finset.mem_union] at hu
      rcases hu with huC | huRest
      · exact (subtreeWires_one_le_maxBagCard huC).trans (le_max_left _ _)
      · exact (listWires_one_le_listMaxBagCard huRest).trans (le_max_right _ _)
end

theorem exists_centroid_bag {α : Type} [DecidableEq α] (E : α → α → Prop) (I : Finset α) :
    ∀ (t : DecompTree α) (outside : Finset α),
      t.RunningIntersection outside →
      (∀ u v, E u v → (u ∈ outside ∧ v ∈ outside) ∨ t.ContainsPair u v) →
      (∀ u, u ∈ outside ∪ t.subtreeWires) →
      I.card < 2 * (I ∩ t.subtreeWires).card →
      ∃ (bag : Finset α) (cs : List (DecompTree α)) (outside' : Finset α),
        bag.card ≤ t.maxBagCard ∧
        (DecompTree.node bag cs).RunningIntersection outside' ∧
        (∀ u v, E u v → (u ∈ outside' ∧ v ∈ outside') ∨ (DecompTree.node bag cs).ContainsPair u v) ∧
        (∀ u, u ∈ outside' ∪ (DecompTree.node bag cs).subtreeWires) ∧
        I.card < 2 * (I ∩ (DecompTree.node bag cs).subtreeWires).card ∧
        ∀ c ∈ cs, 2 * (I ∩ c.subtreeWires).card ≤ I.card
  | .node bag cs, outside, hRI, hPair, hCov, hHeavy => by
    by_cases hStop : ∀ c ∈ cs, 2 * (I ∩ c.subtreeWires).card ≤ I.card
    · refine ⟨bag, cs, outside, le_max_left _ _, hRI, hPair, hCov, hHeavy, hStop⟩
    · push Not at hStop
      rcases hRI with ⟨_, hLRI⟩
      have hEdgeList : ∀ u v, E u v →
          (u ∈ outside ∪ bag ∧ v ∈ outside ∪ bag) ∨ ListContainsPair u v cs := by
        intro u v huv
        rcases hPair u v huv with ⟨hu, hv⟩ | hP
        · exact Or.inl ⟨Finset.mem_union_left _ hu, Finset.mem_union_left _ hv⟩
        · rcases hP with ⟨hu, hv⟩ | hLP
          · exact Or.inl ⟨Finset.mem_union_right _ hu, Finset.mem_union_right _ hv⟩
          · exact Or.inr hLP
      have hCovList : ∀ u, u ∈ (outside ∪ bag) ∪ listWires cs := by
        intro u
        have hu := hCov u
        simp only [subtreeWires, Finset.mem_union] at hu ⊢
        tauto
      have hListDescent :
          ∀ (rest : List (DecompTree α)) (outside0 : Finset α),
            ListRunningIntersection outside0 bag rest →
            (∀ u v, E u v → (u ∈ outside0 ∧ v ∈ outside0) ∨ ListContainsPair u v rest) →
            (∀ u, u ∈ outside0 ∪ listWires rest) →
            (∃ c ∈ rest, I.card < 2 * (I ∩ c.subtreeWires).card) →
            (∀ c ∈ rest, ∀ (outsideC : Finset α),
              c.RunningIntersection outsideC →
              (∀ u v, E u v → (u ∈ outsideC ∧ v ∈ outsideC) ∨ c.ContainsPair u v) →
              (∀ u, u ∈ outsideC ∪ c.subtreeWires) →
              I.card < 2 * (I ∩ c.subtreeWires).card →
              ∃ (bag' : Finset α) (cs' : List (DecompTree α)) (outside' : Finset α),
                bag'.card ≤ c.maxBagCard ∧
                (DecompTree.node bag' cs').RunningIntersection outside' ∧
                (∀ u v, E u v →
                  (u ∈ outside' ∧ v ∈ outside') ∨ (DecompTree.node bag' cs').ContainsPair u v) ∧
                (∀ u, u ∈ outside' ∪ (DecompTree.node bag' cs').subtreeWires) ∧
                I.card < 2 * (I ∩ (DecompTree.node bag' cs').subtreeWires).card ∧
                ∀ c' ∈ cs', 2 * (I ∩ c'.subtreeWires).card ≤ I.card) →
            ∃ (bag' : Finset α) (cs' : List (DecompTree α)) (outside' : Finset α),
              bag'.card ≤ listMaxBagCard rest ∧
              (DecompTree.node bag' cs').RunningIntersection outside' ∧
              (∀ u v, E u v →
                (u ∈ outside' ∧ v ∈ outside') ∨ (DecompTree.node bag' cs').ContainsPair u v) ∧
              (∀ u, u ∈ outside' ∪ (DecompTree.node bag' cs').subtreeWires) ∧
              I.card < 2 * (I ∩ (DecompTree.node bag' cs').subtreeWires).card ∧
              ∀ c' ∈ cs', 2 * (I ∩ c'.subtreeWires).card ≤ I.card := by
        intro rest
        induction rest with
        | nil =>
          intro outside0 _ _ _ hEx _
          rcases hEx with ⟨c, hc, _⟩
          simp at hc
        | cons c tl ihRest =>
          intro outside0 hLRI_r hEdge_r hCov_r hEx ihChildren
          rcases hLRI_r with ⟨_, hCRI, hTlLRI⟩
          by_cases hcHeavy : I.card < 2 * (I ∩ c.subtreeWires).card
          · have hEdgeC : ∀ u v, E u v →
                (u ∈ outside0 ∪ listWires tl ∧ v ∈ outside0 ∪ listWires tl) ∨ c.ContainsPair u v := by
              intro u v huv
              rcases hEdge_r u v huv with ⟨hu, hv⟩ | hLP
              · exact Or.inl ⟨Finset.mem_union_left _ hu, Finset.mem_union_left _ hv⟩
              · rcases hLP with hCP | hTlP
                · exact Or.inr hCP
                · obtain ⟨hu, hv⟩ := listContainsPair_mem_listWires hTlP
                  exact Or.inl ⟨Finset.mem_union_right _ hu, Finset.mem_union_right _ hv⟩
            have hCovC : ∀ u, u ∈ (outside0 ∪ listWires tl) ∪ c.subtreeWires := by
              intro u
              have hu := hCov_r u
              simp only [listWires, Finset.mem_union] at hu ⊢
              tauto
            obtain ⟨bag', cs', outside', hBag, hRI', hPair', hCov', hHeavy', hStop'⟩ :=
              ihChildren c (List.mem_cons_self ..) (outside0 ∪ listWires tl) hCRI hEdgeC hCovC hcHeavy
            exact ⟨bag', cs', outside', hBag.trans (le_max_left _ _), hRI', hPair', hCov', hHeavy', hStop'⟩
          · have hExTl : ∃ c' ∈ tl, I.card < 2 * (I ∩ c'.subtreeWires).card := by
              rcases hEx with ⟨c', hc', hc'Heavy⟩
              rcases List.mem_cons.mp hc' with rfl | hMemTl
              · exact absurd hc'Heavy hcHeavy
              · exact ⟨c', hMemTl, hc'Heavy⟩
            have hEdgeTl : ∀ u v, E u v →
                (u ∈ outside0 ∪ c.subtreeWires ∧ v ∈ outside0 ∪ c.subtreeWires) ∨
                  ListContainsPair u v tl := by
              intro u v huv
              rcases hEdge_r u v huv with ⟨hu, hv⟩ | hLP
              · exact Or.inl ⟨Finset.mem_union_left _ hu, Finset.mem_union_left _ hv⟩
              · rcases hLP with hCP | hTlP
                · obtain ⟨hu, hv⟩ := containsPair_mem_subtreeWires hCP
                  exact Or.inl ⟨Finset.mem_union_right _ hu, Finset.mem_union_right _ hv⟩
                · exact Or.inr hTlP
            have hCovTl : ∀ u, u ∈ (outside0 ∪ c.subtreeWires) ∪ listWires tl := by
              intro u
              have hu := hCov_r u
              simp only [listWires, Finset.mem_union] at hu ⊢
              tauto
            have ihChildrenTl : ∀ c' ∈ tl, ∀ (outsideC : Finset α),
                c'.RunningIntersection outsideC →
                (∀ u v, E u v → (u ∈ outsideC ∧ v ∈ outsideC) ∨ c'.ContainsPair u v) →
                (∀ u, u ∈ outsideC ∪ c'.subtreeWires) →
                I.card < 2 * (I ∩ c'.subtreeWires).card →
                ∃ (bag' : Finset α) (cs' : List (DecompTree α)) (outside' : Finset α),
                  bag'.card ≤ c'.maxBagCard ∧
                  (DecompTree.node bag' cs').RunningIntersection outside' ∧
                  (∀ u v, E u v →
                    (u ∈ outside' ∧ v ∈ outside') ∨ (DecompTree.node bag' cs').ContainsPair u v) ∧
                  (∀ u, u ∈ outside' ∪ (DecompTree.node bag' cs').subtreeWires) ∧
                  I.card < 2 * (I ∩ (DecompTree.node bag' cs').subtreeWires).card ∧
                  ∀ c'' ∈ cs', 2 * (I ∩ c''.subtreeWires).card ≤ I.card :=
              fun c' hc' => ihChildren c' (List.mem_cons_of_mem c hc')
            obtain ⟨bag', cs', outside', hBag, hRI', hPair', hCov', hHeavy', hStop'⟩ :=
              ihRest (outside0 ∪ c.subtreeWires) hTlLRI hEdgeTl hCovTl hExTl ihChildrenTl
            exact ⟨bag', cs', outside', hBag.trans (le_max_right _ _), hRI', hPair', hCov', hHeavy', hStop'⟩
      have ihChildrenRoot : ∀ c ∈ cs, ∀ (outsideC : Finset α),
          c.RunningIntersection outsideC →
          (∀ u v, E u v → (u ∈ outsideC ∧ v ∈ outsideC) ∨ c.ContainsPair u v) →
          (∀ u, u ∈ outsideC ∪ c.subtreeWires) →
          I.card < 2 * (I ∩ c.subtreeWires).card →
          ∃ (bag' : Finset α) (cs' : List (DecompTree α)) (outside' : Finset α),
            bag'.card ≤ c.maxBagCard ∧
            (DecompTree.node bag' cs').RunningIntersection outside' ∧
            (∀ u v, E u v →
              (u ∈ outside' ∧ v ∈ outside') ∨ (DecompTree.node bag' cs').ContainsPair u v) ∧
            (∀ u, u ∈ outside' ∪ (DecompTree.node bag' cs').subtreeWires) ∧
            I.card < 2 * (I ∩ (DecompTree.node bag' cs').subtreeWires).card ∧
            ∀ c' ∈ cs', 2 * (I ∩ c'.subtreeWires).card ≤ I.card :=
        fun c _ => exists_centroid_bag E I c
      obtain ⟨bag', cs', outside', hBag, hRI', hPair', hCov', hHeavy', hStop'⟩ :=
        hListDescent cs (outside ∪ bag) hLRI hEdgeList hCovList hStop ihChildrenRoot
      exact ⟨bag', cs', outside', hBag.trans (le_max_right _ _), hRI', hPair', hCov', hHeavy', hStop'⟩
termination_by t => t

end DecompTree

/-- Valid tree decomposition of an undirected wire graph `E : Fin w → Fin w → Prop`. -/
structure TreeDecomp {w : Nat} (E : Fin w → Fin w → Prop) where
  root : DecompTree (Fin w)
  cover_wire : ∀ u : Fin w, u ∈ root.subtreeWires
  cover_edge : ∀ u v : Fin w, E u v → root.ContainsPair u v
  running : root.RunningIntersection ∅

def TreeDecomp.width {w : Nat} {E : Fin w → Fin w → Prop} (td : TreeDecomp E) : Nat :=
  td.root.maxBagCard - 1

/-- Binary tensor-contraction tree over wire indices `Fin w`. -/
inductive ContractionTree (w : Nat) where
  | leaf (wires : Finset (Fin w))
  | join (left right : ContractionTree w)

namespace ContractionTree

def scope {w : Nat} : ContractionTree w → Finset (Fin w)
  | .leaf s => s
  | .join l r => l.scope ∪ r.scope

def ContainsPair {w : Nat} (u v : Fin w) : ContractionTree w → Prop
  | .leaf s => u ∈ s ∧ v ∈ s
  | .join l r => l.ContainsPair u v ∨ r.ContainsPair u v

def maxBoundary {w : Nat} (outside : Finset (Fin w)) : ContractionTree w → Nat
  | .leaf s => (s ∩ outside).card
  | .join l r =>
    max ((l.scope ∪ r.scope) ∩ outside).card
      (max (l.maxBoundary (outside ∪ r.scope)) (r.maxBoundary (outside ∪ l.scope)))

def AllLeaves {w : Nat} (P : Finset (Fin w) → Prop) : ContractionTree w → Prop
  | .leaf s => P s
  | .join l r => l.AllLeaves P ∧ r.AllLeaves P

theorem containsPair_mem_scope {w : Nat} {t : ContractionTree w} {u v : Fin w}
    (h : t.ContainsPair u v) : u ∈ t.scope ∧ v ∈ t.scope := by
  induction t with
  | leaf s => exact h
  | join l r ihl ihr =>
    simp only [scope, Finset.mem_union]
    rcases h with hl | hr
    · obtain ⟨hu, hv⟩ := ihl hl
      exact ⟨Or.inl hu, Or.inl hv⟩
    · obtain ⟨hu, hv⟩ := ihr hr
      exact ⟨Or.inr hu, Or.inr hv⟩

theorem scope_inter_card_le_maxBoundary {w : Nat} (t : ContractionTree w)
    (outside : Finset (Fin w)) : (t.scope ∩ outside).card ≤ t.maxBoundary outside := by
  cases t with
  | leaf s => exact le_rfl
  | join l r => exact le_max_left _ _

end ContractionTree

/-- Valid tensor-contraction tree covering all wires and edges of `E`. -/
structure ValidContractionTree {w : Nat} (E : Fin w → Fin w → Prop) where
  tree : ContractionTree w
  cover_wire : ∀ u : Fin w, u ∈ tree.scope
  cover_edge : ∀ u v : Fin w, E u v → tree.ContainsPair u v

def ValidContractionTree.contractionWidth {w : Nat} {E : Fin w → Fin w → Prop}
    (ct : ValidContractionTree E) : Nat :=
  ct.tree.maxBoundary ∅

/-! ### 2. `ButterflyNet` Treewidth and Contraction-Width Linear Lower Bounds -/

namespace ButterflyNet

theorem butterfly_treewidth_maxBag_linear (d : Nat)
    (td : TreeDecomp (CircuitEdge (source d).circuit)) :
    2 ^ d ≤ 18 * td.root.maxBagCard := by
  by_cases hd : d = 0
  · subst hd
    have h0Mem : (⟨0, by rw [wires_eq]; norm_num⟩ : Fin (source 0).wires) ∈ td.root.subtreeWires :=
      td.cover_wire _
    have h1 := DecompTree.subtreeWires_one_le_maxBagCard h0Mem
    omega
  · have hdPos : 1 ≤ d := Nat.pos_of_ne_zero hd
    let emb : Fin (2 ^ d) → Fin (source d).wires :=
      fun x => ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩
    have hEmbInj : Function.Injective emb := fun _ _ hxy =>
      Fin.ext (congrArg (Fin.val : Fin (source d).wires → Nat) hxy)
    let I : Finset (Fin (source d).wires) := Finset.univ.image emb
    have hICard : I.card = 2 ^ d := by
      rw [Finset.card_image_of_injective _ hEmbInj, Finset.card_univ, Fintype.card_fin]
    have hIHeavy : I.card < 2 * (I ∩ td.root.subtreeWires).card := by
      have hSub : I ⊆ td.root.subtreeWires := fun u _ => td.cover_wire u
      rw [Finset.inter_eq_left.mpr hSub, hICard]
      have := Nat.two_pow_pos d
      omega
    have hPair0 : ∀ u v, CircuitEdge (source d).circuit u v →
        (u ∈ (∅ : Finset (Fin (source d).wires)) ∧ v ∈ (∅ : Finset (Fin (source d).wires))) ∨
          td.root.ContainsPair u v :=
      fun u v huv => Or.inr (td.cover_edge u v huv)
    have hCov0 : ∀ u : Fin (source d).wires,
        u ∈ (∅ : Finset (Fin (source d).wires)) ∪ td.root.subtreeWires :=
      fun u => Finset.mem_union_right _ (td.cover_wire u)
    obtain ⟨bag, cs, outside', hBagLe, hRI, hPair, hCov, hHeavy, hStop⟩ :=
      DecompTree.exists_centroid_bag (CircuitEdge (source d).circuit) I td.root ∅
        td.running hPair0 hCov0 hIHeavy
    rcases hRI with ⟨hRootRI, hLRI⟩
    let m : Nat := 1 + cs.length + 2 ^ d
    let C : Fin m → Finset (Fin (2 ^ d)) := fun idx =>
      if h0 : idx.val = 0 then
        Finset.univ.filter fun x => emb x ∈ outside' \ bag
      else if hC : idx.val - 1 < cs.length then
        Finset.univ.filter fun x => emb x ∈ (cs[idx.val - 1]'hC).subtreeWires \ bag
      else
        Finset.univ.filter fun x =>
          x.val = idx.val - (1 + cs.length) ∧ emb x ∈ bag
    have hCover : ∀ x : Fin (2 ^ d), ∃ i : Fin m, x ∈ C i := by
      intro x
      by_cases hxBag : emb x ∈ bag
      · refine ⟨⟨1 + cs.length + x.val, by dsimp [m]; omega⟩, ?_⟩
        have hNe0 : 1 + cs.length + x.val ≠ 0 := by omega
        have hGe : ¬ (1 + cs.length + x.val - 1 < cs.length) := by omega
        simp only [C, hNe0, ↓reduceDIte, hGe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by omega, hxBag⟩
      · have hxCov := hCov (emb x)
        simp only [DecompTree.subtreeWires, Finset.mem_union] at hxCov
        rcases hxCov with hxOut | (hxBag' | hxList)
        · refine ⟨⟨0, by dsimp [m]; omega⟩, ?_⟩
          simp [C, hxOut, hxBag]
        · exact absurd hxBag' hxBag
        · rw [DecompTree.mem_listWires_iff_exists] at hxList
          obtain ⟨k, hk⟩ := hxList
          refine ⟨⟨1 + k.val, by dsimp [m]; omega⟩, ?_⟩
          have hNe0 : 1 + k.val ≠ 0 := by omega
          have hkLt : 1 + k.val - 1 < cs.length := by simp
          simp only [C, hNe0, ↓reduceDIte, hkLt, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff]
          refine ⟨?_, hxBag⟩
          simpa [Nat.add_sub_cancel_left] using hk
    have hDisj : ∀ i j : Fin m, i ≠ j → Disjoint (C i) (C j) := by
      intro i j hNe
      rw [Finset.disjoint_left]
      intro x hxI hxJ
      by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
      · exact hNe (Fin.ext (by omega))
      · simp only [C, hi0, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff] at hxI
        by_cases hjC : j.val - 1 < cs.length
        · simp only [C, hj0, ↓reduceDIte, hjC, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hxJ
          have hSub : (cs[j.val - 1]'hjC).subtreeWires ⊆ (DecompTree.node bag cs).subtreeWires :=
            Finset.Subset.trans (DecompTree.listWires_subset_of_mem (List.getElem_mem hjC))
              Finset.subset_union_right
          exact hxI.2 (hRootRI (emb x) (hSub hxJ.1) hxI.1)
        · simp only [C, hj0, ↓reduceDIte, hjC, Finset.mem_filter, Finset.mem_univ, true_and] at hxJ
          exact hxI.2 hxJ.2
      · simp only [C, hj0, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff] at hxJ
        by_cases hiC : i.val - 1 < cs.length
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hxI
          have hSub : (cs[i.val - 1]'hiC).subtreeWires ⊆ (DecompTree.node bag cs).subtreeWires :=
            Finset.Subset.trans (DecompTree.listWires_subset_of_mem (List.getElem_mem hiC))
              Finset.subset_union_right
          exact hxJ.2 (hRootRI (emb x) (hSub hxI.1) hxJ.1)
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and] at hxI
          exact hxJ.2 hxI.2
      · by_cases hiC : i.val - 1 < cs.length <;> by_cases hjC : j.val - 1 < cs.length
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hxI
          simp only [C, hj0, ↓reduceDIte, hjC, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hxJ
          have hIdxNe : (⟨i.val - 1, hiC⟩ : Fin cs.length) ≠ ⟨j.val - 1, hjC⟩ := by
            intro hEq
            have hVal : i.val - 1 = j.val - 1 := congrArg Fin.val hEq
            exact hNe (Fin.ext (by omega))
          exact hxI.2 (DecompTree.listWires_disjoint_of_running (outside' ∪ bag) bag hLRI
            ⟨i.val - 1, hiC⟩ ⟨j.val - 1, hjC⟩ hIdxNe (emb x) hxI.1 hxJ.1)
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hxI
          simp only [C, hj0, ↓reduceDIte, hjC, Finset.mem_filter, Finset.mem_univ, true_and] at hxJ
          exact hxI.2 hxJ.2
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and] at hxI
          simp only [C, hj0, ↓reduceDIte, hjC, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hxJ
          exact hxJ.2 hxI.2
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and] at hxI
          simp only [C, hj0, ↓reduceDIte, hjC, Finset.mem_filter, Finset.mem_univ, true_and] at hxJ
          exact hNe (Fin.ext (by omega))
    have hComp : ∀ x y : Fin (2 ^ d),
        UndirectedReachAvoiding (source d).circuit bag (emb x) (emb y) →
        ∃ i : Fin m, x ∈ C i ∧ y ∈ C i := by
      intro x y hReach
      rw [undirectedReachAvoiding_iff_rel] at hReach
      have hxNotBag : emb x ∉ bag := hReach.start_not_mem
      obtain ⟨i, hxI⟩ := hCover x
      refine ⟨i, hxI, ?_⟩
      by_cases hi0 : i.val = 0
      · simp only [C, hi0, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and] at hxI ⊢
        refine hReach.preserves_pred (fun z => z ∈ outside' \ bag) (fun {u v} huB hvB hEdge huOut => ?_) hxI
        refine Finset.mem_sdiff.mpr ⟨?_, hvB⟩
        rcases hPair u v hEdge with ⟨_, hvOut⟩ | hP
        · exact hvOut
        · rcases hP with ⟨huIn, _⟩ | hLP
          · exact absurd huIn huB
          · rw [DecompTree.listContainsPair_iff_exists] at hLP
            obtain ⟨k, hk⟩ := hLP
            obtain ⟨huC, _⟩ := DecompTree.containsPair_mem_subtreeWires hk
            have huTree : u ∈ (DecompTree.node bag cs).subtreeWires :=
              Finset.mem_union_right _ (DecompTree.listWires_subset_of_mem (List.getElem_mem k.isLt) huC)
            exact absurd (hRootRI u huTree (Finset.mem_sdiff.mp huOut).1) huB
      · by_cases hiC : i.val - 1 < cs.length
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and] at hxI ⊢
          let k : Fin cs.length := ⟨i.val - 1, hiC⟩
          refine hReach.preserves_pred (fun z => z ∈ (cs[k]).subtreeWires \ bag)
            (fun {u v} huB hvB hEdge huK => ?_) hxI
          refine Finset.mem_sdiff.mpr ⟨?_, hvB⟩
          have huK' : u ∈ (cs[k]).subtreeWires := (Finset.mem_sdiff.mp huK).1
          rcases hPair u v hEdge with ⟨huOut, _⟩ | hP
          · have huTree : u ∈ (DecompTree.node bag cs).subtreeWires :=
              Finset.mem_union_right _ (DecompTree.listWires_subset_of_mem (List.getElem_mem k.isLt) huK')
            exact absurd (hRootRI u huTree huOut) huB
          · rcases hP with ⟨huIn, _⟩ | hLP
            · exact absurd huIn huB
            · rw [DecompTree.listContainsPair_iff_exists] at hLP
              obtain ⟨k', hk'⟩ := hLP
              obtain ⟨huC', hvC'⟩ := DecompTree.containsPair_mem_subtreeWires hk'
              by_cases hkk' : k = k'
              · subst hkk'; exact hvC'
              · exact absurd (DecompTree.listWires_disjoint_of_running (outside' ∪ bag) bag hLRI k k'
                  hkk' u huK' huC') huB
        · simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and] at hxI
          exact absurd hxI.2 hxNotBag
    have hSmall : ∀ i : Fin m, 3 * (C i).card ≤ 2 * 2 ^ d := by
      intro i
      by_cases hi0 : i.val = 0
      · have hMap : (C i).image emb ⊆ I \ (I ∩ (DecompTree.node bag cs).subtreeWires) := by
          intro u hu
          rw [Finset.mem_image] at hu
          obtain ⟨x, hx, rfl⟩ := hu
          simp only [C, hi0, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_sdiff] at hx
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
          intro hMemInter
          exact hx.2 (hRootRI (emb x) (Finset.mem_inter.mp hMemInter).2 hx.1)
        have hCardEq : ((C i).image emb).card = (C i).card :=
          Finset.card_image_of_injective _ hEmbInj
        have hSdiff : (I \ (I ∩ (DecompTree.node bag cs).subtreeWires)).card =
            I.card - (I ∩ (DecompTree.node bag cs).subtreeWires).card := by
          rw [Finset.card_sdiff]
          congr 1
          congr 1
          ext z
          simp [Finset.mem_inter, and_comm]
        have hLe := (Finset.card_le_card hMap).trans_eq hSdiff
        rw [hCardEq] at hLe
        rw [hICard] at hHeavy hLe
        omega
      · by_cases hiC : i.val - 1 < cs.length
        · have hMap : (C i).image emb ⊆ I ∩ (cs[i.val - 1]'hiC).subtreeWires := by
            intro u hu
            rw [Finset.mem_image] at hu
            obtain ⟨x, hx, rfl⟩ := hu
            simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_sdiff] at hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hx.1⟩
          have hLe : (C i).card ≤ (I ∩ (cs[i.val - 1]'hiC).subtreeWires).card := by
            rw [← Finset.card_image_of_injective (C i) hEmbInj]
            exact Finset.card_le_card hMap
          have hStopC := hStop (cs[i.val - 1]'hiC) (List.getElem_mem hiC)
          rw [hICard] at hStopC
          omega
        · have hCard1 : (C i).card ≤ 1 := by
            refine Finset.card_le_one.mpr fun x hx y hy => ?_
            simp only [C, hi0, ↓reduceDIte, hiC, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
            exact Fin.ext (by omega)
          have h2Pow : 2 ≤ 2 ^ d := by
            calc
              2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hdPos
          omega
    have hLin := butterfly_component_separator_linear d m bag C hCover hDisj hComp hSmall
    exact hLin.trans (Nat.mul_le_mul_left 18 hBagLe)

theorem butterfly_treewidth_linear (d : Nat)
    (td : TreeDecomp (CircuitEdge (source d).circuit)) :
    2 ^ d ≤ 18 * (td.width + 1) := by
  have hMax := butterfly_treewidth_maxBag_linear d td
  have h1 : td.root.maxBagCard ≤ td.width + 1 := by
    dsimp [TreeDecomp.width]
    omega
  exact hMax.trans (Nat.mul_le_mul_left 18 h1)

theorem butterfly_escapes_sublinear_treewidth (d : Nat → Nat) (_hd : Tendsto d atTop atTop)
    (td : ∀ i, TreeDecomp (CircuitEdge (source (d i)).circuit)) :
    ¬ ((fun i => ((td i).width : ℝ)) =o[atTop] (fun i => ((2 ^ d i : Nat) : ℝ))) := by
  intro hLittleO
  have hBound : ∀ᶠ i in atTop,
      ‖((td i).width : ℝ)‖ ≤ (1 / 36 : ℝ) * ‖((2 ^ d i : Nat) : ℝ)‖ :=
    hLittleO.bound (by norm_num : (0 : ℝ) < 1 / 36)
  have hD : ∀ᶠ i in atTop, 6 ≤ d i := _hd.eventually_ge_atTop 6
  obtain ⟨i, hi, hd6⟩ := (hBound.and hD).exists
  have hLin : ((2 ^ d i : Nat) : ℝ) ≤ 18 * (((td i).width : ℝ) + 1) := by
    exact_mod_cast butterfly_treewidth_linear (d i) (td i)
  have hPow64 : (64 : ℝ) ≤ ((2 ^ d i : Nat) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd6
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hi
  linarith

private theorem contraction_step_aux {d : Nat}
    (ch other : ContractionTree (source d).wires) (outside : Finset (Fin (source d).wires))
    (hC1 : 2 ^ d < 3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
      (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ ch.scope).card)
    (hC2 : 3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
      (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ ch.scope).card ≤
      2 * 2 ^ d)
    (hPairSplit : ∀ u v, CircuitEdge (source d).circuit u v →
      (u ∈ outside ∪ other.scope ∧ v ∈ outside ∪ other.scope) ∨ ch.ContainsPair u v) :
    ∃ (S : Finset (Fin (source d).wires)) (A B : Finset (Fin (2 ^ d))),
      S.card ≤ ch.maxBoundary (outside ∪ other.scope) ∧
      SeparatesInputs (source d).circuit S A B (inputs_le_wires d) ∧
      2 ^ d ≤ 3 * A.card ∧ 2 ^ d ≤ 3 * B.card := by
  let emb : Fin (2 ^ d) → Fin (source d).wires :=
    fun x => ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩
  let S : Finset (Fin (source d).wires) := ch.scope ∩ (outside ∪ other.scope)
  let A : Finset (Fin (2 ^ d)) := Finset.univ.filter fun x => emb x ∈ ch.scope
  let B : Finset (Fin (2 ^ d)) := Finset.univ \ A
  have hSCard : S.card ≤ ch.maxBoundary (outside ∪ other.scope) :=
    ContractionTree.scope_inter_card_le_maxBoundary ch (outside ∪ other.scope)
  have hALe : A.card ≤ 2 ^ d := by simpa using Finset.card_le_univ A
  have hBCard : 2 ^ d ≤ 3 * B.card := by
    have hSubEq : B.card = 2 ^ d - A.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hSubEq]
    change 3 * A.card ≤ 2 * 2 ^ d at hC2
    omega
  have hSep : SeparatesInputs (source d).circuit S A B (inputs_le_wires d) := by
    intro x hx y hy hReach
    rw [undirectedReachAvoiding_iff_rel] at hReach
    have hxScope : emb x ∈ ch.scope := (Finset.mem_filter.mp hx).2
    have hyNotScope : emb y ∉ ch.scope := by
      intro hyScope
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyScope⟩)
    have hPres : emb y ∈ ch.scope :=
      hReach.preserves_pred (fun u => u ∈ ch.scope) (fun {u v} huS _ hEdge hu => by
        rcases hPairSplit u v hEdge with ⟨huOut, _⟩ | hCh
        · exact absurd (Finset.mem_inter.mpr ⟨hu, huOut⟩) huS
        · exact (ContractionTree.containsPair_mem_scope hCh).2) hxScope
    exact hyNotScope hPres
  exact ⟨S, A, B, hSCard, hSep, le_of_lt hC1, hBCard⟩

private theorem contraction_find_balanced_cut {d : Nat}
    (t : ContractionTree (source d).wires) (outside : Finset (Fin (source d).wires))
    (hLeaf : t.AllLeaves fun s =>
      3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ s).card ≤ 2 * 2 ^ d)
    (hPair : ∀ u v, CircuitEdge (source d).circuit u v → (u ∈ outside ∧ v ∈ outside) ∨ t.ContainsPair u v)
    (hHeavy : 2 * 2 ^ d < 3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
      (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ t.scope).card) :
    ∃ (S : Finset (Fin (source d).wires)) (A B : Finset (Fin (2 ^ d))),
      S.card ≤ t.maxBoundary outside ∧
      SeparatesInputs (source d).circuit S A B (inputs_le_wires d) ∧
      2 ^ d ≤ 3 * A.card ∧ 2 ^ d ≤ 3 * B.card := by
  let emb : Fin (2 ^ d) → Fin (source d).wires :=
    fun x => ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩
  let inScope : ContractionTree (source d).wires → Finset (Fin (2 ^ d)) :=
    fun sub => Finset.univ.filter fun x => emb x ∈ sub.scope
  induction t generalizing outside with
  | leaf s =>
    exact absurd hHeavy (Nat.not_lt_of_ge hLeaf)
  | join l r ihl ihr =>
    rcases hLeaf with ⟨hLeafL, hLeafR⟩
    have hPairL : ∀ u v, CircuitEdge (source d).circuit u v →
        (u ∈ outside ∪ r.scope ∧ v ∈ outside ∪ r.scope) ∨ l.ContainsPair u v := by
      intro u v huv
      rcases hPair u v huv with ⟨hu, hv⟩ | (hl | hr)
      · exact Or.inl ⟨Finset.mem_union_left _ hu, Finset.mem_union_left _ hv⟩
      · exact Or.inr hl
      · obtain ⟨hu, hv⟩ := ContractionTree.containsPair_mem_scope hr
        exact Or.inl ⟨Finset.mem_union_right _ hu, Finset.mem_union_right _ hv⟩
    have hPairR : ∀ u v, CircuitEdge (source d).circuit u v →
        (u ∈ outside ∪ l.scope ∧ v ∈ outside ∪ l.scope) ∨ r.ContainsPair u v := by
      intro u v huv
      rcases hPair u v huv with ⟨hu, hv⟩ | (hl | hr)
      · exact Or.inl ⟨Finset.mem_union_left _ hu, Finset.mem_union_left _ hv⟩
      · obtain ⟨hu, hv⟩ := ContractionTree.containsPair_mem_scope hl
        exact Or.inl ⟨Finset.mem_union_right _ hu, Finset.mem_union_right _ hv⟩
      · exact Or.inr hr
    by_cases hL : 2 * 2 ^ d < 3 * (inScope l).card
    · obtain ⟨S, A, B, hS, hSep, hA, hB⟩ := ihl (outside ∪ r.scope) hLeafL hPairL hL
      have hMaxL : l.maxBoundary (outside ∪ r.scope) ≤ (ContractionTree.join l r).maxBoundary outside :=
        (le_max_left _ _).trans (le_max_right _ _)
      exact ⟨S, A, B, hS.trans hMaxL, hSep, hA, hB⟩
    · by_cases hR : 2 * 2 ^ d < 3 * (inScope r).card
      · obtain ⟨S, A, B, hS, hSep, hA, hB⟩ := ihr (outside ∪ l.scope) hLeafR hPairR hR
        have hMaxR : r.maxBoundary (outside ∪ l.scope) ≤ (ContractionTree.join l r).maxBoundary outside :=
          (le_max_right _ _).trans (le_max_right _ _)
        exact ⟨S, A, B, hS.trans hMaxR, hSep, hA, hB⟩
      · have hLSmall : 3 * (inScope l).card ≤ 2 * 2 ^ d := Nat.le_of_not_gt hL
        have hRSmall : 3 * (inScope r).card ≤ 2 * 2 ^ d := Nat.le_of_not_gt hR
        have hUnion : inScope (.join l r) = inScope l ∪ inScope r := by
          ext x
          simp [inScope, ContractionTree.scope]
        have hSumLe : (inScope (.join l r)).card ≤ (inScope l).card + (inScope r).card := by
          rw [hUnion]
          exact Finset.card_union_le _ _
        have hEither : 2 ^ d < 3 * (inScope l).card ∨ 2 ^ d < 3 * (inScope r).card := by
          change 2 * 2 ^ d < 3 * (inScope (.join l r)).card at hHeavy
          omega
        rcases hEither with hLBig | hRBig
        · obtain ⟨S, A, B, hS, hSep, hA, hB⟩ :=
            contraction_step_aux l r outside hLBig hLSmall hPairL
          have hMaxL : l.maxBoundary (outside ∪ r.scope) ≤ (ContractionTree.join l r).maxBoundary outside :=
            (le_max_left _ _).trans (le_max_right _ _)
          exact ⟨S, A, B, hS.trans hMaxL, hSep, hA, hB⟩
        · obtain ⟨S, A, B, hS, hSep, hA, hB⟩ :=
            contraction_step_aux r l outside hRBig hRSmall hPairR
          have hMaxR : r.maxBoundary (outside ∪ l.scope) ≤ (ContractionTree.join l r).maxBoundary outside :=
            (le_max_right _ _).trans (le_max_right _ _)
          exact ⟨S, A, B, hS.trans hMaxR, hSep, hA, hB⟩

theorem butterfly_contractionWidth_linear (d : Nat)
    (ct : ValidContractionTree (CircuitEdge (source d).circuit))
    (hLeaves : ct.tree.AllLeaves fun s =>
      3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ s).card ≤ 2 * 2 ^ d) :
    2 ^ d ≤ 18 * ct.contractionWidth := by
  have hPair0 : ∀ u v, CircuitEdge (source d).circuit u v →
      (u ∈ (∅ : Finset (Fin (source d).wires)) ∧ v ∈ (∅ : Finset (Fin (source d).wires))) ∨
        ct.tree.ContainsPair u v :=
    fun u v huv => Or.inr (ct.cover_edge u v huv)
  have hHeavy0 : 2 * 2 ^ d < 3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
      (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ ct.tree.scope).card := by
    have hEq : (Finset.univ.filter fun x : Fin (2 ^ d) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ ct.tree.scope) =
        Finset.univ := by
      ext x
      simp [ct.cover_wire]
    rw [hEq, Finset.card_univ, Fintype.card_fin]
    have := Nat.two_pow_pos d
    omega
  obtain ⟨S, A, B, hS, hSep, hA, hB⟩ := contraction_find_balanced_cut ct.tree ∅ hLeaves hPair0 hHeavy0
  exact (butterfly_balanced_separator_linear d S hSep hA hB).trans (Nat.mul_le_mul_left 18 hS)

theorem butterfly_gateContractionWidth_linear (d : Nat) (hd : 2 ≤ d)
    (ct : ValidContractionTree (CircuitEdge (source d).circuit))
    (hLeaves : ct.tree.AllLeaves fun s =>
      (Finset.univ.filter fun x : Fin (2 ^ d) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ s).card ≤ 2) :
    2 ^ d ≤ 18 * ct.contractionWidth := by
  refine butterfly_contractionWidth_linear d ct ?_
  have hPow : 4 ≤ 2 ^ d := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd
  have hMono : ∀ {t : ContractionTree (source d).wires},
      t.AllLeaves (fun s =>
        (Finset.univ.filter fun x : Fin (2 ^ d) =>
          (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ s).card ≤ 2) →
      t.AllLeaves (fun s =>
        3 * (Finset.univ.filter fun x : Fin (2 ^ d) =>
          (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ : Fin (source d).wires) ∈ s).card ≤ 2 * 2 ^ d) := by
    intro t ht
    induction t with
    | leaf s =>
      change 3 * _ ≤ 2 * 2 ^ d
      change _ ≤ 2 at ht
      omega
    | join l r ihl ihr =>
      exact ⟨ihl ht.1, ihr ht.2⟩
  exact hMono hLeaves

theorem butterfly_escapes_sublinear_contractionWidth (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (ct : ∀ i, ValidContractionTree (CircuitEdge (source (d i)).circuit))
    (hLeaves : ∀ i, (ct i).tree.AllLeaves fun s =>
      (Finset.univ.filter fun x : Fin (2 ^ d i) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires (d i))⟩ : Fin (source (d i)).wires) ∈ s).card ≤ 2) :
    ¬ ((fun i => ((ct i).contractionWidth : ℝ)) =o[atTop] (fun i => ((2 ^ d i : Nat) : ℝ))) := by
  intro hLittleO
  have hBound : ∀ᶠ i in atTop,
      ‖((ct i).contractionWidth : ℝ)‖ ≤ (1 / 36 : ℝ) * ‖((2 ^ d i : Nat) : ℝ)‖ :=
    hLittleO.bound (by norm_num : (0 : ℝ) < 1 / 36)
  have hD : ∀ᶠ i in atTop, 2 ≤ d i := hd.eventually_ge_atTop 2
  obtain ⟨i, hi, hd2⟩ := (hBound.and hD).exists
  have hLin : ((2 ^ d i : Nat) : ℝ) ≤ 18 * ((ct i).contractionWidth : ℝ) := by
    exact_mod_cast butterfly_gateContractionWidth_linear (d i) hd2 (ct i) (hLeaves i)
  have hPos : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by positivity
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hi
  linarith

end ButterflyNet

/-! ### 3. `HybridCircuit`, $\mathbb{F}_2$ Affine Systems, and Universal $3^q$ Nonlinear Branching -/

/-- Fan-in-2 gate over `{AND, OR, XOR, NOT}`. -/
inductive HybridGate (n : Nat) where
  | and (left right : Fin n)
  | or (left right : Fin n)
  | xor (left right : Fin n)
  | not (input : Fin n)

def HybridGate.eval {n : Nat} (gate : HybridGate n) (values : Fin n → Bool) : Bool :=
  match gate with
  | .and left right => values left && values right
  | .or left right => values left || values right
  | .xor left right => Bool.xor (values left) (values right)
  | .not input => !values input

def HybridGate.nonlinearWeight {n : Nat} : HybridGate n → Nat
  | .and _ _ => 1
  | .or _ _ => 1
  | .xor _ _ => 0
  | .not _ => 0

def HybridGate.ofGate {n : Nat} : Gate n → HybridGate n
  | .and a b => .and a b
  | .or a b => .or a b
  | .not a => .not a

theorem HybridGate.eval_ofGate {n : Nat} (g : Gate n) (values : Fin n → Bool) :
    (HybridGate.ofGate g).eval values = g.eval values := by
  cases g <;> rfl

/-- Topologically ordered fan-in-2 hybrid circuit over `{AND, OR, XOR, NOT}`. -/
inductive HybridCircuit (inputs : Nat) : Nat → Type where
  | inputsOnly : HybridCircuit inputs inputs
  | snoc {n : Nat} (earlier : HybridCircuit inputs n) (gate : HybridGate n) :
      HybridCircuit inputs (n + 1)

namespace HybridCircuit

def evalWires {inputs : Nat} : {w : Nat} → HybridCircuit inputs w → (Fin inputs → Bool) → (Fin w → Bool)
  | _, .inputsOnly, input => input
  | _, .snoc earlier gate, input =>
    let values := earlier.evalWires input
    Fin.snoc values (gate.eval values)

def gateCount {inputs : Nat} : {w : Nat} → HybridCircuit inputs w → Nat
  | _, .inputsOnly => 0
  | _, .snoc earlier _ => earlier.gateCount + 1

def nonlinearCount {inputs : Nat} : {w : Nat} → HybridCircuit inputs w → Nat
  | _, .inputsOnly => 0
  | _, .snoc earlier gate => earlier.nonlinearCount + gate.nonlinearWeight

def ofCircuit {inputs : Nat} : {w : Nat} → Circuit inputs w → HybridCircuit inputs w
  | _, .inputsOnly => .inputsOnly
  | _, .snoc earlier gate => .snoc (ofCircuit earlier) (HybridGate.ofGate gate)

theorem ofCircuit_evalWires {inputs : Nat} :
    ∀ {w : Nat} (c : Circuit inputs w) (x : Fin inputs → Bool),
      (ofCircuit c).evalWires x = c.evalWires x
  | _, .inputsOnly, _ => rfl
  | _, .snoc earlier gate, x => by
    simp only [ofCircuit, evalWires, Circuit.evalWires, ofCircuit_evalWires earlier x,
      HybridGate.eval_ofGate]

theorem ofCircuit_nonlinearCount_eq_binaryGateCount {inputs : Nat} :
    ∀ {w : Nat} (c : Circuit inputs w), (ofCircuit c).nonlinearCount = binaryGateCount c
  | _, .inputsOnly => rfl
  | _, .snoc earlier gate => by
    have ih := ofCircuit_nonlinearCount_eq_binaryGateCount earlier
    cases gate with
    | and u v =>
      change (ofCircuit earlier).nonlinearCount + 1 = unhitBinaryGates earlier (fun _ => none) + 1
      rw [ih]; rfl
    | or u v =>
      change (ofCircuit earlier).nonlinearCount + 1 = unhitBinaryGates earlier (fun _ => none) + 1
      rw [ih]; rfl
    | not u =>
      change (ofCircuit earlier).nonlinearCount + 0 = unhitBinaryGates earlier (fun _ => none)
      rw [Nat.add_zero, ih]; rfl

end HybridCircuit

/-- Undirected parent-child adjacency in a `HybridCircuit inputs w`. -/
inductive HybridCircuitEdge {inputs : Nat} : {w : Nat} → HybridCircuit inputs w → Fin w → Fin w → Prop where
  | cast {w : Nat} (earlier : HybridCircuit inputs w) (g : HybridGate w) {u v : Fin w} :
      HybridCircuitEdge earlier u v → HybridCircuitEdge (earlier.snoc g) u.castSucc v.castSucc
  | not_in {w : Nat} (earlier : HybridCircuit inputs w) (a : Fin w) :
      HybridCircuitEdge (earlier.snoc (.not a)) a.castSucc (Fin.last w)
  | not_out {w : Nat} (earlier : HybridCircuit inputs w) (a : Fin w) :
      HybridCircuitEdge (earlier.snoc (.not a)) (Fin.last w) a.castSucc
  | and_left {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.and a b)) a.castSucc (Fin.last w)
  | and_right {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.and a b)) b.castSucc (Fin.last w)
  | and_out_left {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.and a b)) (Fin.last w) a.castSucc
  | and_out_right {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.and a b)) (Fin.last w) b.castSucc
  | or_left {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.or a b)) a.castSucc (Fin.last w)
  | or_right {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.or a b)) b.castSucc (Fin.last w)
  | or_out_left {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.or a b)) (Fin.last w) a.castSucc
  | or_out_right {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.or a b)) (Fin.last w) b.castSucc
  | xor_left {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.xor a b)) a.castSucc (Fin.last w)
  | xor_right {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.xor a b)) b.castSucc (Fin.last w)
  | xor_out_left {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.xor a b)) (Fin.last w) a.castSucc
  | xor_out_right {w : Nat} (earlier : HybridCircuit inputs w) (a b : Fin w) :
      HybridCircuitEdge (earlier.snoc (.xor a b)) (Fin.last w) b.castSucc

theorem HybridCircuitEdge.symm {inputs w : Nat} {c : HybridCircuit inputs w} {u v : Fin w}
    (h : HybridCircuitEdge c u v) : HybridCircuitEdge c v u := by
  induction h with
  | cast earlier g _ ih => exact .cast earlier g ih
  | not_in earlier a => exact .not_out earlier a
  | not_out earlier a => exact .not_in earlier a
  | and_left earlier a b => exact .and_out_left earlier a b
  | and_right earlier a b => exact .and_out_right earlier a b
  | and_out_left earlier a b => exact .and_left earlier a b
  | and_out_right earlier a b => exact .and_right earlier a b
  | or_left earlier a b => exact .or_out_left earlier a b
  | or_right earlier a b => exact .or_out_right earlier a b
  | or_out_left earlier a b => exact .or_left earlier a b
  | or_out_right earlier a b => exact .or_right earlier a b
  | xor_left earlier a b => exact .xor_out_left earlier a b
  | xor_right earlier a b => exact .xor_out_right earlier a b
  | xor_out_left earlier a b => exact .xor_left earlier a b
  | xor_out_right earlier a b => exact .xor_right earlier a b

/-- Single-output hybrid Circuit-SAT instance. -/
structure HybridCircuitInstance (inputs : Nat) where
  wires : Nat
  circuit : HybridCircuit inputs wires
  output : Fin wires

def HybridCircuitInstance.eval {inputs : Nat} (c : HybridCircuitInstance inputs)
    (x : Fin inputs → Bool) : Bool :=
  c.circuit.evalWires x c.output

def HybridCircuitInstance.acceptCount {inputs : Nat} (c : HybridCircuitInstance inputs) : Nat :=
  (Finset.univ.filter fun x : Fin inputs → Bool => c.eval x = true).card

/-! #### $\mathbb{F}_2$ Affine Forms and Exact Linear-System Cardinality -/

def boolToZMod2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

def zmod2ToBool (z : ZMod 2) : Bool :=
  decide (z = 1)

def boolEquivZMod2 : Bool ≃ ZMod 2 where
  toFun := boolToZMod2
  invFun := zmod2ToBool
  left_inv b := by cases b <;> decide
  right_inv z := by
    fin_cases z <;> rfl

theorem boolToZMod2_zmod2ToBool (z : ZMod 2) : boolToZMod2 (zmod2ToBool z) = z :=
  boolEquivZMod2.right_inv z

theorem boolToZMod2_eq_one_iff (b : Bool) : boolToZMod2 b = 1 ↔ b = true := by
  cases b <;> decide

theorem boolToZMod2_xor (a b : Bool) :
    boolToZMod2 (Bool.xor a b) = boolToZMod2 a + boolToZMod2 b := by
  cases a <;> cases b <;> decide

theorem boolToZMod2_not (a : Bool) :
    boolToZMod2 (!a) = boolToZMod2 a + 1 := by
  cases a <;> decide

/-- An affine linear form `∑ i, coeff i * x i + bias` over `ZMod 2`. -/
structure AffineForm (n : Nat) where
  coeff : Fin n → ZMod 2
  bias : ZMod 2

namespace AffineForm

def evalZ2 {n : Nat} (f : AffineForm n) (x : Fin n → Bool) : ZMod 2 :=
  (∑ i : Fin n, f.coeff i * boolToZMod2 (x i)) + f.bias

def eval {n : Nat} (f : AffineForm n) (x : Fin n → Bool) : Bool :=
  decide (f.evalZ2 x = 1)

theorem boolToZMod2_eval {n : Nat} (f : AffineForm n) (x : Fin n → Bool) :
    boolToZMod2 (f.eval x) = f.evalZ2 x := by
  dsimp [eval]
  generalize f.evalZ2 x = hz
  fin_cases hz <;> rfl

def var {n : Nat} (i : Fin n) : AffineForm n where
  coeff j := if j = i then 1 else 0
  bias := 0

@[simp] theorem evalZ2_var {n : Nat} (i : Fin n) (x : Fin n → Bool) :
    (var i).evalZ2 x = boolToZMod2 (x i) := by
  simp [evalZ2, var]

@[simp] theorem eval_var {n : Nat} (i : Fin n) (x : Fin n → Bool) :
    (var i).eval x = x i := by
  simp [eval, evalZ2_var, boolToZMod2_eq_one_iff]

def const {n : Nat} (b : Bool) : AffineForm n where
  coeff _ := 0
  bias := boolToZMod2 b

@[simp] theorem evalZ2_const {n : Nat} (b : Bool) (x : Fin n → Bool) :
    (const b : AffineForm n).evalZ2 x = boolToZMod2 b := by
  simp [evalZ2, const]

@[simp] theorem eval_const {n : Nat} (b : Bool) (x : Fin n → Bool) :
    (const b : AffineForm n).eval x = b := by
  simp [eval, evalZ2_const, boolToZMod2_eq_one_iff]

def not {n : Nat} (f : AffineForm n) : AffineForm n where
  coeff := f.coeff
  bias := f.bias + 1

@[simp] theorem evalZ2_not {n : Nat} (f : AffineForm n) (x : Fin n → Bool) :
    f.not.evalZ2 x = f.evalZ2 x + 1 := by
  simp [evalZ2, not, add_assoc]

@[simp] theorem eval_not {n : Nat} (f : AffineForm n) (x : Fin n → Bool) :
    f.not.eval x = !(f.eval x) := by
  have h1 : boolToZMod2 (f.not.eval x) = boolToZMod2 (!(f.eval x)) := by
    rw [boolToZMod2_eval, evalZ2_not, boolToZMod2_not, boolToZMod2_eval]
  exact boolEquivZMod2.injective h1

theorem evalZ2_not_eq_zero_iff {n : Nat} (f : AffineForm n) (x : Fin n → Bool) :
    f.not.evalZ2 x = 0 ↔ f.eval x = true := by
  rw [evalZ2_not, ← f.boolToZMod2_eval, ← boolToZMod2_eq_one_iff]
  cases f.eval x <;> decide

theorem evalZ2_eq_zero_iff {n : Nat} (f : AffineForm n) (x : Fin n → Bool) :
    f.evalZ2 x = 0 ↔ f.eval x = false := by
  rw [← f.boolToZMod2_eval]
  cases f.eval x <;> decide

def xor {n : Nat} (f g : AffineForm n) : AffineForm n where
  coeff := f.coeff + g.coeff
  bias := f.bias + g.bias

@[simp] theorem evalZ2_xor {n : Nat} (f g : AffineForm n) (x : Fin n → Bool) :
    (f.xor g).evalZ2 x = f.evalZ2 x + g.evalZ2 x := by
  simp [evalZ2, xor, add_mul, Finset.sum_add_distrib]
  ring

@[simp] theorem eval_xor {n : Nat} (f g : AffineForm n) (x : Fin n → Bool) :
    (f.xor g).eval x = Bool.xor (f.eval x) (g.eval x) := by
  have h1 : boolToZMod2 ((f.xor g).eval x) = boolToZMod2 (Bool.xor (f.eval x) (g.eval x)) := by
    rw [boolToZMod2_eval, evalZ2_xor, boolToZMod2_xor, boolToZMod2_eval, boolToZMod2_eval]
  exact boolEquivZMod2.injective h1

end AffineForm

/-- List of affine linear equations `f x = 0` over `ZMod 2`. -/
abbrev LinearSystem (n : Nat) := List (AffineForm n)

namespace LinearSystem

def sat {n : Nat} (sys : LinearSystem n) (x : Fin n → Bool) : Prop :=
  ∀ f ∈ sys, f.evalZ2 x = 0

def satBool {n : Nat} (sys : LinearSystem n) (x : Fin n → Bool) : Bool :=
  sys.all fun f => decide (f.evalZ2 x = 0)

theorem satBool_eq_true {n : Nat} (sys : LinearSystem n) (x : Fin n → Bool) :
    sys.satBool x = true ↔ sys.sat x := by
  simp [satBool, sat, List.all_eq_true]

def solSet {n : Nat} (sys : LinearSystem n) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => sys.satBool x = true

theorem mem_solSet {n : Nat} (sys : LinearSystem n) (x : Fin n → Bool) :
    x ∈ sys.solSet ↔ sys.sat x := by
  simp [solSet, satBool_eq_true]

def matrixMap {n : Nat} (sys : LinearSystem n) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin sys.length → ZMod 2) where
  toFun v j := ∑ i : Fin n, (sys[j]).coeff i * v i
  map_add' u v := by
    ext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext j
    simp [Finset.mul_sum, mul_left_comm]

theorem linearSystem_card_eq_of_nonempty {n : Nat} (sys : LinearSystem n)
    {x₀ : Fin n → Bool} (hx₀ : sys.sat x₀) :
    sys.solSet.card = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker sys.matrixMap) ∧
      sys.solSet.card = 2 ^ (n - Module.finrank (ZMod 2) (LinearMap.range sys.matrixMap)) := by
  classical
  have hKernelEquiv : ∀ x : Fin n → Bool,
      sys.sat x ↔ (fun i => boolToZMod2 (x i) - boolToZMod2 (x₀ i)) ∈ LinearMap.ker sys.matrixMap := by
    intro x
    rw [LinearMap.mem_ker, funext_iff]
    constructor
    · intro hx j
      have hEvalX : (sys[j]).evalZ2 x = 0 := hx (sys[j]) (List.getElem_mem j.isLt)
      have hEvalX0 : (sys[j]).evalZ2 x₀ = 0 := hx₀ (sys[j]) (List.getElem_mem j.isLt)
      change ∑ i : Fin n, (sys[j]).coeff i * (boolToZMod2 (x i) - boolToZMod2 (x₀ i)) = 0
      simp only [mul_sub, Finset.sum_sub_distrib]
      dsimp [AffineForm.evalZ2] at hEvalX hEvalX0
      have hSumX : ∑ i : Fin n, (sys[j]).coeff i * boolToZMod2 (x i) = -(sys[j]).bias :=
        eq_neg_of_add_eq_zero_left hEvalX
      have hSumX0 : ∑ i : Fin n, (sys[j]).coeff i * boolToZMod2 (x₀ i) = -(sys[j]).bias :=
        eq_neg_of_add_eq_zero_left hEvalX0
      rw [hSumX, hSumX0, sub_self]
    · intro hKer f hfMem
      rw [List.mem_iff_getElem] at hfMem
      obtain ⟨idx, hIdxLt, rfl⟩ := hfMem
      have hJ : sys.matrixMap (fun i => boolToZMod2 (x i) - boolToZMod2 (x₀ i)) ⟨idx, hIdxLt⟩ = 0 :=
        hKer ⟨idx, hIdxLt⟩
      change ∑ i : Fin n, (sys[idx]).coeff i * (boolToZMod2 (x i) - boolToZMod2 (x₀ i)) = 0 at hJ
      simp only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] at hJ
      have hEvalX0 : (sys[idx]).evalZ2 x₀ = 0 := hx₀ (sys[idx]) (List.getElem_mem hIdxLt)
      dsimp [AffineForm.evalZ2] at hEvalX0 ⊢
      rw [hJ]
      exact hEvalX0
  let e : { x : Fin n → Bool // x ∈ sys.solSet } ≃ LinearMap.ker sys.matrixMap :=
    { toFun := fun x => ⟨fun i => boolToZMod2 (x.1 i) - boolToZMod2 (x₀ i),
        (hKernelEquiv x.1).mp ((mem_solSet sys x.1).mp x.2)⟩
      invFun := fun k => ⟨fun i => zmod2ToBool (k.1 i + boolToZMod2 (x₀ i)), by
        rw [mem_solSet, hKernelEquiv]
        convert k.2 using 1
        ext i
        rw [boolToZMod2_zmod2ToBool]
        ring⟩
      left_inv := fun x => by
        ext i
        change zmod2ToBool ((boolToZMod2 (x.1 i) - boolToZMod2 (x₀ i)) + boolToZMod2 (x₀ i)) = x.1 i
        have hSub : boolToZMod2 (x.1 i) - boolToZMod2 (x₀ i) + boolToZMod2 (x₀ i) =
            boolToZMod2 (x.1 i) := by ring
        rw [hSub]
        exact boolEquivZMod2.left_inv (x.1 i)
      right_inv := fun k => by
        ext i
        change boolToZMod2 (zmod2ToBool (k.1 i + boolToZMod2 (x₀ i))) - boolToZMod2 (x₀ i) = k.1 i
        rw [boolToZMod2_zmod2ToBool]
        ring }
  let _ : Fintype (LinearMap.ker sys.matrixMap) := Fintype.ofFinite _
  have hCardKer : sys.solSet.card = Fintype.card (LinearMap.ker sys.matrixMap) := by
    rw [← Fintype.card_coe sys.solSet]
    exact Fintype.card_congr e
  have hPowKer : Fintype.card (LinearMap.ker sys.matrixMap) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker sys.matrixMap) := by
    rw [@Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hRankNull := LinearMap.finrank_range_add_finrank_ker sys.matrixMap
  have hDimDom : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n :=
    Module.finrank_fin_fun (ZMod 2)
  rw [hDimDom] at hRankNull
  have hKerDim : Module.finrank (ZMod 2) (LinearMap.ker sys.matrixMap) =
      n - Module.finrank (ZMod 2) (LinearMap.range sys.matrixMap) := by
    omega
  exact ⟨hCardKer.trans hPowKer, (hCardKer.trans hPowKer).trans (congrArg (2 ^ ·) hKerDim)⟩

theorem linearSystem_card_eq_zero_or_pow {n : Nat} (sys : LinearSystem n) :
    sys.solSet.card = 0 ∨
      sys.solSet.card = 2 ^ (n - Module.finrank (ZMod 2) (LinearMap.range sys.matrixMap)) := by
  by_cases hNe : sys.solSet.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hNe
    exact Or.inr (linearSystem_card_eq_of_nonempty sys ((mem_solSet sys x₀).mp hx₀)).2
  · left
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hNe)

end LinearSystem

/-! #### Universal $3^q$-Branch Affine Decomposition -/

/-- One branch of the affine decomposition: a `ZMod 2` linear system plus affine forms
for every wire of the `HybridCircuit`. -/
structure AffineBranch (n w : Nat) where
  sys : LinearSystem n
  wireAff : Fin w → AffineForm n

def compileAffineStep {n w : Nat} (g : HybridGate w) (b : AffineBranch n w) :
    List (AffineBranch n (w + 1)) :=
  match g with
  | .not a =>
    [⟨b.sys, Fin.snoc b.wireAff (b.wireAff a).not⟩]
  | .xor a c =>
    [⟨b.sys, Fin.snoc b.wireAff ((b.wireAff a).xor (b.wireAff c))⟩]
  | .and a c =>
    let fa := b.wireAff a
    let fc := b.wireAff c
    [ ⟨fa :: b.sys, Fin.snoc b.wireAff (AffineForm.const false)⟩,
      ⟨fc :: fa.not :: b.sys, Fin.snoc b.wireAff (AffineForm.const false)⟩,
      ⟨fc.not :: fa.not :: b.sys, Fin.snoc b.wireAff (AffineForm.const true)⟩ ]
  | .or a c =>
    let fa := b.wireAff a
    let fc := b.wireAff c
    [ ⟨fa.not :: b.sys, Fin.snoc b.wireAff (AffineForm.const true)⟩,
      ⟨fc.not :: fa :: b.sys, Fin.snoc b.wireAff (AffineForm.const true)⟩,
      ⟨fc :: fa :: b.sys, Fin.snoc b.wireAff (AffineForm.const false)⟩ ]

def compileAffineBranches {n : Nat} : {w : Nat} → HybridCircuit n w → List (AffineBranch n w)
  | _, .inputsOnly => [⟨[], fun i => AffineForm.var i⟩]
  | _, .snoc earlier gate => (compileAffineBranches earlier).flatMap (compileAffineStep gate)

private theorem length_flatMap_const {α β : Type _} (l : List α) (f : α → List β) (k : Nat)
    (hk : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := hk a (List.mem_cons_self ..)
    have hRest := ih fun x hx => hk x (List.mem_cons_of_mem _ hx)
    rw [ha, hRest]
    ring

private theorem sum_map_flatMap {α β : Type _} (l : List α) (f : α → List β) (g : β → Nat) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem compileAffineBranches_length {n : Nat} :
    ∀ {w : Nat} (c : HybridCircuit n w), (compileAffineBranches c).length = 3 ^ c.nonlinearCount
  | _, .inputsOnly => by simp [compileAffineBranches, HybridCircuit.nonlinearCount]
  | _, .snoc earlier gate => by
    have ih := compileAffineBranches_length earlier
    cases gate with
    | not a =>
      have hStep : ∀ b ∈ compileAffineBranches earlier,
          (compileAffineStep (.not a) b).length = 1 := fun _ _ => rfl
      simp [compileAffineBranches, HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight,
        length_flatMap_const _ _ 1 hStep, ih]
    | xor a c =>
      have hStep : ∀ b ∈ compileAffineBranches earlier,
          (compileAffineStep (.xor a c) b).length = 1 := fun _ _ => rfl
      simp [compileAffineBranches, HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight,
        length_flatMap_const _ _ 1 hStep, ih]
    | and a c =>
      have hStep : ∀ b ∈ compileAffineBranches earlier,
          (compileAffineStep (.and a c) b).length = 3 := fun _ _ => rfl
      rw [compileAffineBranches, length_flatMap_const _ _ 3 hStep, ih]
      simp [HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight, pow_succ]
    | or a c =>
      have hStep : ∀ b ∈ compileAffineBranches earlier,
          (compileAffineStep (.or a c) b).length = 3 := fun _ _ => rfl
      rw [compileAffineBranches, length_flatMap_const _ _ 3 hStep, ih]
      simp [HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight, pow_succ]

theorem compileAffineBranches_sys_length_le {n : Nat} :
    ∀ {w : Nat} (c : HybridCircuit n w), ∀ b ∈ compileAffineBranches c,
      b.sys.length ≤ 2 * c.nonlinearCount
  | _, .inputsOnly, b, hb => by
    simp only [compileAffineBranches, List.mem_singleton] at hb
    subst hb
    simp [HybridCircuit.nonlinearCount]
  | _, .snoc earlier gate, b, hb => by
    simp only [compileAffineBranches, List.mem_flatMap] at hb
    obtain ⟨b0, hb0, hbStep⟩ := hb
    have ih := compileAffineBranches_sys_length_le earlier b0 hb0
    cases gate with
    | not a =>
      simp only [compileAffineStep, List.mem_singleton] at hbStep
      subst hbStep
      simpa [HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight] using ih
    | xor a c =>
      simp only [compileAffineStep, List.mem_singleton] at hbStep
      subst hbStep
      simpa [HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight] using ih
    | and a c =>
      simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
      rcases hbStep with rfl | rfl | rfl <;>
        simp [HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight] <;> omega
    | or a c =>
      simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
      rcases hbStep with rfl | rfl | rfl <;>
        simp [HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight] <;> omega

private theorem compileAffineStep_indicator_sum {n w : Nat} (g : HybridGate w)
    (b : AffineBranch n w) (x : Fin n → Bool) :
    ((compileAffineStep g b).map fun b' => if b'.sys.satBool x then 1 else 0).sum =
      if b.sys.satBool x then 1 else 0 := by
  by_cases hB : b.sys.sat x
  · have hBools : b.sys.satBool x = true := (LinearSystem.satBool_eq_true b.sys x).mpr hB
    have hSat1 : ∀ f : AffineForm n, LinearSystem.satBool (f :: b.sys) x = true ↔ f.evalZ2 x = 0 := by
      intro f
      rw [LinearSystem.satBool_eq_true]
      exact ⟨fun h => h f (List.mem_cons_self ..), fun hf g hg => by
        rcases List.mem_cons.mp hg with rfl | hgSys
        · exact hf
        · exact hB g hgSys⟩
    have hSat2 : ∀ f g : AffineForm n,
        LinearSystem.satBool (f :: g :: b.sys) x = true ↔ f.evalZ2 x = 0 ∧ g.evalZ2 x = 0 := by
      intro f g
      rw [LinearSystem.satBool_eq_true]
      refine ⟨fun h => ⟨h f (List.mem_cons_self ..), h g (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩,
        fun ⟨hf, hg⟩ k hk => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk1
      · exact hf
      · rcases List.mem_cons.mp hk1 with rfl | hk2
        · exact hg
        · exact hB k hk2
    cases g with
    | not a => simp [compileAffineStep, hBools]
    | xor a c => simp [compileAffineStep, hBools]
    | and a c =>
      have hAE : (b.wireAff a).evalZ2 x = 0 ↔ (b.wireAff a).eval x = false :=
        AffineForm.evalZ2_eq_zero_iff _ _
      have hCE : (b.wireAff c).evalZ2 x = 0 ↔ (b.wireAff c).eval x = false :=
        AffineForm.evalZ2_eq_zero_iff _ _
      have hANE : (b.wireAff a).not.evalZ2 x = 0 ↔ (b.wireAff a).eval x = true :=
        AffineForm.evalZ2_not_eq_zero_iff _ _
      have hCNE : (b.wireAff c).not.evalZ2 x = 0 ↔ (b.wireAff c).eval x = true :=
        AffineForm.evalZ2_not_eq_zero_iff _ _
      simp only [compileAffineStep, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      cases hA : (b.wireAff a).eval x <;> cases hC : (b.wireAff c).eval x <;>
        simp only [hBools, hSat1, hSat2, hAE, hCE, hANE, hCNE, hA, hC] <;> simp
    | or a c =>
      have hAE : (b.wireAff a).evalZ2 x = 0 ↔ (b.wireAff a).eval x = false :=
        AffineForm.evalZ2_eq_zero_iff _ _
      have hCE : (b.wireAff c).evalZ2 x = 0 ↔ (b.wireAff c).eval x = false :=
        AffineForm.evalZ2_eq_zero_iff _ _
      have hANE : (b.wireAff a).not.evalZ2 x = 0 ↔ (b.wireAff a).eval x = true :=
        AffineForm.evalZ2_not_eq_zero_iff _ _
      have hCNE : (b.wireAff c).not.evalZ2 x = 0 ↔ (b.wireAff c).eval x = true :=
        AffineForm.evalZ2_not_eq_zero_iff _ _
      simp only [compileAffineStep, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      cases hA : (b.wireAff a).eval x <;> cases hC : (b.wireAff c).eval x <;>
        simp only [hBools, hSat1, hSat2, hAE, hCE, hANE, hCNE, hA, hC] <;> simp
  · have hBools : b.sys.satBool x = false := by
      cases hEq : b.sys.satBool x
      · rfl
      · exact absurd ((LinearSystem.satBool_eq_true b.sys x).mp hEq) hB
    have hNo : ∀ {l : LinearSystem n}, (∀ f ∈ b.sys, f ∈ l) → l.satBool x = false := by
      intro l hSub
      cases hEq : l.satBool x
      · rfl
      · exact absurd (fun f hf => (LinearSystem.satBool_eq_true l x).mp hEq f (hSub f hf)) hB
    cases g with
    | not a => simp [compileAffineStep, hBools]
    | xor a c => simp [compileAffineStep, hBools]
    | and a c =>
      have h1 : LinearSystem.satBool (b.wireAff a :: b.sys) x = false :=
        hNo fun _ h => List.mem_cons_of_mem _ h
      have h2 : LinearSystem.satBool (b.wireAff c :: (b.wireAff a).not :: b.sys) x = false :=
        hNo fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      have h3 : LinearSystem.satBool ((b.wireAff c).not :: (b.wireAff a).not :: b.sys) x = false :=
        hNo fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      simp [compileAffineStep, hBools, h1, h2, h3]
    | or a c =>
      have h1 : LinearSystem.satBool ((b.wireAff a).not :: b.sys) x = false :=
        hNo fun _ h => List.mem_cons_of_mem _ h
      have h2 : LinearSystem.satBool ((b.wireAff c).not :: b.wireAff a :: b.sys) x = false :=
        hNo fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      have h3 : LinearSystem.satBool (b.wireAff c :: b.wireAff a :: b.sys) x = false :=
        hNo fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
      simp [compileAffineStep, hBools, h1, h2, h3]

theorem compileAffineBranches_indicator_sum {n : Nat} :
    ∀ {w : Nat} (c : HybridCircuit n w) (x : Fin n → Bool),
      ((compileAffineBranches c).map fun b => if b.sys.satBool x then 1 else 0).sum = 1
  | _, .inputsOnly, x => by
    simp [compileAffineBranches, LinearSystem.satBool]
  | _, .snoc earlier gate, x => by
    have ih := compileAffineBranches_indicator_sum earlier x
    rw [compileAffineBranches, sum_map_flatMap]
    have hEq : (compileAffineBranches earlier).map
        (fun b => ((compileAffineStep gate b).map fun b' => if b'.sys.satBool x then 1 else 0).sum) =
        (compileAffineBranches earlier).map (fun b => if b.sys.satBool x then 1 else 0) :=
      List.map_congr_left fun b _ => compileAffineStep_indicator_sum gate b x
    rw [hEq, ih]

theorem compileAffineBranches_wire_sound {n : Nat} :
    ∀ {w : Nat} (c : HybridCircuit n w), ∀ b ∈ compileAffineBranches c,
      ∀ x : Fin n → Bool, b.sys.sat x → ∀ u : Fin w, c.evalWires x u = (b.wireAff u).eval x
  | _, .inputsOnly, b, hb, x, _, u => by
    simp only [compileAffineBranches, List.mem_singleton] at hb
    subst hb
    simp [HybridCircuit.evalWires]
  | _, .snoc earlier gate, b, hb, x, hxSat, u => by
    simp only [compileAffineBranches, List.mem_flatMap] at hb
    obtain ⟨b0, hb0, hbStep⟩ := hb
    have hSat0 : b0.sys.sat x := by
      cases gate with
      | not a =>
        simp only [compileAffineStep, List.mem_singleton] at hbStep
        subst hbStep; exact hxSat
      | xor a c =>
        simp only [compileAffineStep, List.mem_singleton] at hbStep
        subst hbStep; exact hxSat
      | and a c =>
        simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
        rcases hbStep with rfl | rfl | rfl <;> intro f hf
        · exact hxSat f (List.mem_cons_of_mem _ hf)
        · exact hxSat f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
        · exact hxSat f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
      | or a c =>
        simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
        rcases hbStep with rfl | rfl | rfl <;> intro f hf
        · exact hxSat f (List.mem_cons_of_mem _ hf)
        · exact hxSat f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
        · exact hxSat f (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf))
    have ih := compileAffineBranches_wire_sound earlier b0 hb0 x hSat0
    cases u using Fin.lastCases with
    | cast q =>
      simp only [HybridCircuit.evalWires, Fin.snoc_castSucc]
      have hAffEq : b.wireAff q.castSucc = b0.wireAff q := by
        cases gate with
        | not a =>
          simp only [compileAffineStep, List.mem_singleton] at hbStep
          subst hbStep; simp [Fin.snoc_castSucc]
        | xor a c =>
          simp only [compileAffineStep, List.mem_singleton] at hbStep
          subst hbStep; simp [Fin.snoc_castSucc]
        | and a c =>
          simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
          rcases hbStep with rfl | rfl | rfl <;> simp [Fin.snoc_castSucc]
        | or a c =>
          simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
          rcases hbStep with rfl | rfl | rfl <;> simp [Fin.snoc_castSucc]
      rw [hAffEq]
      exact ih q
    | last =>
      simp only [HybridCircuit.evalWires, Fin.snoc_last]
      cases gate with
      | not a =>
        simp only [compileAffineStep, List.mem_singleton] at hbStep
        subst hbStep
        simp [HybridGate.eval, Fin.snoc_last, ih a]
      | xor a c =>
        simp only [compileAffineStep, List.mem_singleton] at hbStep
        subst hbStep
        simp [HybridGate.eval, Fin.snoc_last, ih a, ih c]
      | and a c =>
        simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
        rcases hbStep with rfl | rfl | rfl
        · have hA0 : (b0.wireAff a).eval x = false :=
            (AffineForm.evalZ2_eq_zero_iff _ _).mp (hxSat _ (List.mem_cons_self ..))
          simp [HybridGate.eval, Fin.snoc_last, ih a, hA0]
        · have hC0 : (b0.wireAff c).eval x = false :=
            (AffineForm.evalZ2_eq_zero_iff _ _).mp (hxSat _ (List.mem_cons_self ..))
          simp [HybridGate.eval, Fin.snoc_last, ih c, hC0]
        · have hC1 : (b0.wireAff c).eval x = true :=
            (AffineForm.evalZ2_not_eq_zero_iff _ _).mp (hxSat _ (List.mem_cons_self ..))
          have hA1 : (b0.wireAff a).eval x = true :=
            (AffineForm.evalZ2_not_eq_zero_iff _ _).mp
              (hxSat _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          simp [HybridGate.eval, Fin.snoc_last, ih a, ih c, hA1, hC1]
      | or a c =>
        simp only [compileAffineStep, List.mem_cons, List.not_mem_nil, or_false] at hbStep
        rcases hbStep with rfl | rfl | rfl
        · have hA1 : (b0.wireAff a).eval x = true :=
            (AffineForm.evalZ2_not_eq_zero_iff _ _).mp (hxSat _ (List.mem_cons_self ..))
          simp [HybridGate.eval, Fin.snoc_last, ih a, hA1]
        · have hC1 : (b0.wireAff c).eval x = true :=
            (AffineForm.evalZ2_not_eq_zero_iff _ _).mp (hxSat _ (List.mem_cons_self ..))
          simp [HybridGate.eval, Fin.snoc_last, ih c, hC1]
        · have hC0 : (b0.wireAff c).eval x = false :=
            (AffineForm.evalZ2_eq_zero_iff _ _).mp (hxSat _ (List.mem_cons_self ..))
          have hA0 : (b0.wireAff a).eval x = false :=
            (AffineForm.evalZ2_eq_zero_iff _ _).mp
              (hxSat _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
          simp [HybridGate.eval, Fin.snoc_last, ih a, ih c, hA0, hC0]

namespace HybridCircuitInstance

def acceptSystems {n : Nat} (c : HybridCircuitInstance n) : List (LinearSystem n) :=
  (compileAffineBranches c.circuit).map fun b => (b.wireAff c.output).not :: b.sys

theorem acceptSystems_length {n : Nat} (c : HybridCircuitInstance n) :
    c.acceptSystems.length = 3 ^ c.circuit.nonlinearCount := by
  simp [acceptSystems, compileAffineBranches_length]

theorem acceptSystems_eqs_le {n : Nat} (c : HybridCircuitInstance n) :
    ∀ s ∈ c.acceptSystems, s.length ≤ 2 * c.circuit.nonlinearCount + 1 := by
  intro s hs
  simp only [acceptSystems, List.mem_map] at hs
  obtain ⟨b, hb, rfl⟩ := hs
  have hLe := compileAffineBranches_sys_length_le c.circuit b hb
  simp [hLe]

private theorem list_sum_finset_sum {α β : Type _} [Fintype β] (l : List α) (g : α → β → Nat) :
    (l.map fun a => ∑ x : β, g a x).sum = ∑ x : β, (l.map fun a => g a x).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp [ih, Finset.sum_add_distrib]

theorem acceptCount_eq_sum_affine {n : Nat} (c : HybridCircuitInstance n) :
    c.acceptCount = (c.acceptSystems.map fun s => s.solSet.card).sum := by
  have hCardFin : ∀ s : LinearSystem n,
      s.solSet.card = ∑ x : Fin n → Bool, if s.satBool x then 1 else 0 := by
    intro s
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  have hSwap : (c.acceptSystems.map fun s => s.solSet.card).sum =
      ∑ x : Fin n → Bool, (c.acceptSystems.map fun s => if s.satBool x then 1 else 0).sum := by
    have hMap : c.acceptSystems.map (fun s => s.solSet.card) =
        c.acceptSystems.map (fun s => ∑ x : Fin n → Bool, if s.satBool x then 1 else 0) :=
      List.map_congr_left fun s _ => hCardFin s
    rw [hMap, list_sum_finset_sum]
  have hPointwise : ∀ x : Fin n → Bool,
      (c.acceptSystems.map fun s => if s.satBool x then 1 else 0).sum =
        if c.eval x = true then 1 else 0 := by
    intro x
    have hMapSys : (c.acceptSystems.map fun s => if s.satBool x then 1 else 0) =
        (compileAffineBranches c.circuit).map fun b =>
          if b.sys.satBool x && decide (c.eval x = true) then 1 else 0 := by
      simp only [acceptSystems, List.map_map]
      refine List.map_congr_left fun b hb => ?_
      have hSatCons : LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x = true ↔
          (b.wireAff c.output).not.evalZ2 x = 0 ∧ b.sys.sat x := by
        rw [LinearSystem.satBool_eq_true]
        simp [LinearSystem.sat]
      by_cases hbSat : b.sys.sat x
      · have hBools : b.sys.satBool x = true := (LinearSystem.satBool_eq_true b.sys x).mpr hbSat
        have hWire := compileAffineBranches_wire_sound c.circuit b hb x hbSat c.output
        have hEvalEq : c.eval x = (b.wireAff c.output).eval x := hWire
        rw [hEvalEq, hBools]
        cases hEv : (b.wireAff c.output).eval x
        · have hNot0 : ¬ LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x = true := by
            rw [hSatCons, AffineForm.evalZ2_not_eq_zero_iff, hEv]
            simp
          have hF : LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x = false := by
            cases hQ : LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x
            · rfl
            · exact absurd hQ hNot0
          simp [hF]
        · have hT : LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x = true := by
            rw [hSatCons, AffineForm.evalZ2_not_eq_zero_iff]
            exact ⟨hEv, hbSat⟩
          simp [hT]
      · have hBools : b.sys.satBool x = false := by
          cases hQ : b.sys.satBool x
          · rfl
          · exact absurd ((LinearSystem.satBool_eq_true b.sys x).mp hQ) hbSat
        have hNotSys : LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x = false := by
          cases hQ : LinearSystem.satBool ((b.wireAff c.output).not :: b.sys) x
          · rfl
          · exact absurd ((hSatCons.mp hQ).2) hbSat
        simp [hBools, hNotSys]
    rw [hMapSys]
    by_cases hEv : c.eval x = true
    · simp only [hEv, decide_true, Bool.and_true]
      exact compileAffineBranches_indicator_sum c.circuit x
    · simp [hEv]
  rw [hSwap]
  have hAcc : c.acceptCount = ∑ x : Fin n → Bool, if c.eval x = true then 1 else 0 := by
    dsimp [acceptCount]
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  rw [hAcc]
  exact Finset.sum_congr rfl fun x _ => (hPointwise x).symm

end HybridCircuitInstance

/-- Deterministic `O(3 ^ q * ((2q + 2)(n + 1)^3 + w + 2))` log-time budget for solving `3 ^ q`
`ZMod 2` Gaussian-elimination systems of `≤ 2q + 1` equations over `n` variables. -/
noncomputable def affineBranchLogTimeBudget (n w q : Nat) : ℝ :=
  Real.log ((3 : ℝ) ^ q + 1) + Real.log (((2 * q + 2) * (n + 1) ^ 3 + w + 2 : Nat) : ℝ)

theorem affineBranchLogTimeBudget_isLittleO {n w q : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hq : (fun i => (q i : ℝ)) =o[atTop] fun i => (n i : ℝ))
    (D : Nat) (hw : ∀ᶠ i in atTop, w i ≤ (n i + 2) ^ D) :
    (fun i => affineBranchLogTimeBudget (n i) (w i) (q i)) =o[atTop] fun i => (n i : ℝ) := by
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hOne : (fun _ : Nat => (1 : ℝ)) =o[atTop] fun i => (n i : ℝ) := by
    refine IsLittleO.of_bound fun ε hε => ?_
    filter_upwards [hnReal.eventually_ge_atTop (1 / ε)] with i hi
    rw [norm_one, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      1 = ε * (1 / ε) := by field_simp
      _ ≤ ε * (n i : ℝ) := mul_le_mul_of_nonneg_left hi hε.le
  have hBranches : (fun i => Real.log ((3 : ℝ) ^ q i + 1)) =o[atTop] fun i => (n i : ℝ) := by
    have hO : (fun i => Real.log ((3 : ℝ) ^ q i + 1)) =O[atTop] fun i => ((q i : ℝ) + 1) := by
      refine IsBigO.of_bound (Real.log 3 + 1) ?_
      refine Eventually.of_forall fun i => ?_
      have hGe1 : (1 : ℝ) ≤ (3 : ℝ) ^ q i + 1 := by linarith [show (0 : ℝ) ≤ (3 : ℝ) ^ q i by positivity]
      have hPow : (3 : ℝ) ^ q i + 1 ≤ (3 : ℝ) ^ (q i + 1) := by
        have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ q i := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        linarith
      have hLog : Real.log ((3 : ℝ) ^ q i + 1) ≤ ((q i : ℝ) + 1) * Real.log 3 := by
        calc
          Real.log ((3 : ℝ) ^ q i + 1) ≤ Real.log ((3 : ℝ) ^ (q i + 1)) :=
            Real.log_le_log (by positivity) hPow
          _ = ((q i + 1 : Nat) : ℝ) * Real.log 3 := Real.log_pow 3 (q i + 1)
          _ = ((q i : ℝ) + 1) * Real.log 3 := by push_cast; ring
      rw [Real.norm_of_nonneg (Real.log_nonneg hGe1), Real.norm_of_nonneg (by positivity)]
      nlinarith [show (0 : ℝ) ≤ (q i : ℝ) + 1 by positivity]
    exact hO.trans_isLittleO (hq.add hOne)
  have hPoly : (fun i => Real.log (((2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 : Nat) : ℝ)) =o[atTop]
      fun i => (n i : ℝ) := by
    have hnShift : Tendsto (fun i => (n i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
    have hShiftO : (fun i => (n i : ℝ) + 2) =O[atTop] fun i => (n i : ℝ) := by
      refine IsBigO.of_bound 3 ?_
      filter_upwards [hnReal.eventually_ge_atTop 1] with i hi
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      linarith
    have hLogN := (Real.isLittleO_log_id_atTop.comp_tendsto hnShift).trans_isBigO hShiftO
    have hQLeN : ∀ᶠ i in atTop, q i ≤ n i := by
      filter_upwards [hq.bound (by norm_num : (0 : ℝ) < 1)] with i hi
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hi
      exact_mod_cast (by linarith : (q i : ℝ) ≤ (n i : ℝ))
    have hDom : (fun i => Real.log (((2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 : Nat) : ℝ)) =O[atTop]
        fun i => Real.log ((n i : ℝ) + 2) := by
      let E : Nat := max D 4 + 1
      refine IsBigO.of_bound (E : ℝ) ?_
      filter_upwards [hw, hQLeN, hn.eventually_ge_atTop 2] with i hwi hqi hn2
      have hPolyNat : (2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 ≤ (n i + 2) ^ E := by
        have h2Q : 2 * q i + 2 ≤ 2 * (n i + 2) := by omega
        have hCub : (n i + 1) ^ 3 ≤ (n i + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        have hN4 : (n i + 2) ^ 4 ≤ (n i + 2) ^ (max D 4) :=
          Nat.pow_le_pow_right (by omega) (le_max_right _ _)
        have hWD : w i ≤ (n i + 2) ^ (max D 4) :=
          hwi.trans (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
        have hTerm1 : (2 * q i + 2) * (n i + 1) ^ 3 ≤ 2 * (n i + 2) ^ (max D 4) := by
          calc
            (2 * q i + 2) * (n i + 1) ^ 3 ≤ (2 * (n i + 2)) * (n i + 2) ^ 3 :=
              Nat.mul_le_mul h2Q hCub
            _ = 2 * (n i + 2) ^ 4 := by ring
            _ ≤ 2 * (n i + 2) ^ (max D 4) := Nat.mul_le_mul_left 2 hN4
        have h2Le : 2 ≤ (n i + 2) ^ (max D 4) := by
          calc
            2 ≤ n i + 2 := by omega
            _ = (n i + 2) ^ 1 := (pow_one _).symm
            _ ≤ (n i + 2) ^ (max D 4) := Nat.pow_le_pow_right (by omega) (by omega)
        have h4Pow : 4 * (n i + 2) ^ (max D 4) ≤ (n i + 2) ^ E := by
          dsimp [E]
          rw [pow_succ']
          exact Nat.mul_le_mul_right _ (by omega)
        omega
      have hPos1 : (1 : ℝ) ≤ (((2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 : Nat) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ (2 * q i + 2) * (n i + 1) ^ 3 + w i + 2)
      have hLogLe : Real.log (((2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 : Nat) : ℝ) ≤
          (E : ℝ) * Real.log ((n i : ℝ) + 2) := by
        have hCast : (((2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 : Nat) : ℝ) ≤
            ((n i : ℝ) + 2) ^ E := by
          exact_mod_cast hPolyNat
        calc
          Real.log (((2 * q i + 2) * (n i + 1) ^ 3 + w i + 2 : Nat) : ℝ)
            ≤ Real.log (((n i : ℝ) + 2) ^ E) := Real.log_le_log (by positivity) hCast
          _ = (E : ℝ) * Real.log ((n i : ℝ) + 2) := Real.log_pow _ _
      have hLogPos : 0 ≤ Real.log ((n i : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ n i by positivity])
      rw [Real.norm_of_nonneg (Real.log_nonneg hPos1), Real.norm_of_nonneg hLogPos]
      exact hLogLe
    exact hDom.trans_isLittleO hLogN
  exact hBranches.add hPoly

/-! ### 4. Explicit `HybridButterflyNet` Family: Topological Wall vs. $\mathbb{F}_2$-Affine Collapse -/

namespace HybridButterflyNet

/-- Hybrid butterfly gate at layer `ℓ`, column `j < 2 ^ d`. First `q` gates (in row-major order
`ℓ * 2 ^ d + j < q`) are nonlinear `AND`/`OR`; the remaining gates are linear `XOR`. -/
def hybridBflyGate (d q ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    HybridGate (LayeredRing.ringWires (2 ^ d) ℓ + j) :=
  let N := 2 ^ d
  have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
  let a : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + j, by
    rw [hBase]
    have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
    omega⟩
  let b : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + ButterflyNet.flipBit j ℓ, by
    have hf := ButterflyNet.flipBit_lt hj hℓ
    rw [hBase]
    have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
    omega⟩
  if ℓ * N + j < q then
    if ℓ % 2 = 0 then .and a b else .or a b
  else
    .xor a b

def appendHybridBflyRow (d q ℓ : Nat) (hℓ : ℓ < d) :
    (j : Nat) → j ≤ 2 ^ d → HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ) →
      HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ + j)
  | 0, _, c => c
  | j + 1, hj, c =>
    (appendHybridBflyRow d q ℓ hℓ j (by omega) c).snoc (hybridBflyGate d q ℓ j hℓ (by omega))

def buildHybridBfly (d q : Nat) :
    (ℓ : Nat) → ℓ ≤ d → HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)
  | 0, _ => .inputsOnly
  | ℓ + 1, hℓ =>
    appendHybridBflyRow d q ℓ (by omega) (2 ^ d) (le_rfl) (buildHybridBfly d q ℓ (by omega))

def source (d q : Nat) : HybridCircuitInstance (2 ^ d) where
  wires := LayeredRing.ringWires (2 ^ d) d
  circuit := buildHybridBfly d q d (le_rfl)
  output := ⟨LayeredRing.ringWires (2 ^ d) d - 1, by
    have hEq := LayeredRing.ringWires_eq (2 ^ d) d
    have hPos : 0 < (d + 1) * 2 ^ d := Nat.mul_pos (Nat.succ_pos d) (Nat.two_pow_pos d)
    omega⟩

theorem wires_eq (d q : Nat) : (source d q).wires = (d + 1) * 2 ^ d :=
  LayeredRing.ringWires_eq (2 ^ d) d

theorem inputs_le_wires (d q : Nat) : 2 ^ d ≤ (source d q).wires := by
  rw [wires_eq]
  exact Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d)

/-- Relation capturing exact same operand wiring between a `HybridGate` and a `Gate`. -/
inductive SameGateWiring {w : Nat} : HybridGate w → Gate w → Prop where
  | and_and (a b : Fin w) : SameGateWiring (.and a b) (.and a b)
  | and_or (a b : Fin w) : SameGateWiring (.and a b) (.or a b)
  | or_and (a b : Fin w) : SameGateWiring (.or a b) (.and a b)
  | or_or (a b : Fin w) : SameGateWiring (.or a b) (.or a b)
  | xor_and (a b : Fin w) : SameGateWiring (.xor a b) (.and a b)
  | xor_or (a b : Fin w) : SameGateWiring (.xor a b) (.or a b)
  | not_not (a : Fin w) : SameGateWiring (.not a) (.not a)

inductive SameWiring {n : Nat} : {w : Nat} → HybridCircuit n w → Circuit n w → Prop where
  | inputsOnly : SameWiring .inputsOnly .inputsOnly
  | snoc {w : Nat} {hc : HybridCircuit n w} {c : Circuit n w}
      {hg : HybridGate w} {g : Gate w} :
      SameWiring hc c → SameGateWiring hg g → SameWiring (.snoc hc hg) (.snoc c g)

private theorem hybridEdge_iff_of_sameWiring {n w : Nat} {hc : HybridCircuit n w} {c : Circuit n w}
    (hSW : SameWiring hc c) (u v : Fin w) :
    HybridCircuitEdge hc u v ↔ CircuitEdge c u v := by
  induction hSW with
  | inputsOnly =>
    constructor <;> (intro h; cases h)
  | @snoc w hc c hg g _ hGate ih =>
    constructor
    · intro h
      cases h with
      | cast _ _ hPrev => exact .cast _ _ ((ih _ _).mp hPrev)
      | not_in => cases hGate; exact .not_in _ _
      | not_out => cases hGate; exact .not_out _ _
      | and_left => cases hGate <;> [exact .and_left _ _ _; exact .or_left _ _ _]
      | and_right => cases hGate <;> [exact .and_right _ _ _; exact .or_right _ _ _]
      | and_out_left => cases hGate <;> [exact .and_out_left _ _ _; exact .or_out_left _ _ _]
      | and_out_right => cases hGate <;> [exact .and_out_right _ _ _; exact .or_out_right _ _ _]
      | or_left => cases hGate <;> [exact .and_left _ _ _; exact .or_left _ _ _]
      | or_right => cases hGate <;> [exact .and_right _ _ _; exact .or_right _ _ _]
      | or_out_left => cases hGate <;> [exact .and_out_left _ _ _; exact .or_out_left _ _ _]
      | or_out_right => cases hGate <;> [exact .and_out_right _ _ _; exact .or_out_right _ _ _]
      | xor_left => cases hGate <;> [exact .and_left _ _ _; exact .or_left _ _ _]
      | xor_right => cases hGate <;> [exact .and_right _ _ _; exact .or_right _ _ _]
      | xor_out_left => cases hGate <;> [exact .and_out_left _ _ _; exact .or_out_left _ _ _]
      | xor_out_right => cases hGate <;> [exact .and_out_right _ _ _; exact .or_out_right _ _ _]
    · intro h
      cases h with
      | cast _ _ hPrev => exact .cast _ _ ((ih _ _).mpr hPrev)
      | not_in => cases hGate; exact .not_in _ _
      | not_out => cases hGate; exact .not_out _ _
      | and_left => cases hGate <;> [exact .and_left _ _ _; exact .or_left _ _ _; exact .xor_left _ _ _]
      | and_right => cases hGate <;> [exact .and_right _ _ _; exact .or_right _ _ _; exact .xor_right _ _ _]
      | and_out_left => cases hGate <;> [exact .and_out_left _ _ _; exact .or_out_left _ _ _; exact .xor_out_left _ _ _]
      | and_out_right => cases hGate <;> [exact .and_out_right _ _ _; exact .or_out_right _ _ _; exact .xor_out_right _ _ _]
      | or_left => cases hGate <;> [exact .and_left _ _ _; exact .or_left _ _ _; exact .xor_left _ _ _]
      | or_right => cases hGate <;> [exact .and_right _ _ _; exact .or_right _ _ _; exact .xor_right _ _ _]
      | or_out_left => cases hGate <;> [exact .and_out_left _ _ _; exact .or_out_left _ _ _; exact .xor_out_left _ _ _]
      | or_out_right => cases hGate <;> [exact .and_out_right _ _ _; exact .or_out_right _ _ _; exact .xor_out_right _ _ _]

private theorem hybridBflyGate_sameWiring (d q ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    SameGateWiring (hybridBflyGate d q ℓ j hℓ hj) (ButterflyNet.bflyGate d ℓ j hℓ hj) := by
  dsimp [hybridBflyGate, ButterflyNet.bflyGate]
  split_ifs
  · exact .and_and _ _
  · exact .or_or _ _
  · exact .xor_and _ _
  · exact .xor_or _ _

private theorem buildHybridBfly_sameWiring (d q : Nat) :
    ∀ D (hD : D ≤ d), SameWiring (buildHybridBfly d q D hD) (ButterflyNet.buildBfly d D hD)
  | 0, _ => .inputsOnly
  | D + 1, hD => by
    have ih := buildHybridBfly_sameWiring d q D (by omega)
    have hRow : ∀ j (hj : j ≤ 2 ^ d),
        SameWiring (appendHybridBflyRow d q D (by omega) j hj (buildHybridBfly d q D (by omega)))
          (ButterflyNet.appendBflyRow d D (by omega) j hj (ButterflyNet.buildBfly d D (by omega))) := by
      intro j hj
      induction j with
      | zero => exact ih
      | succ j ihJ =>
        exact .snoc (ihJ (by omega)) (hybridBflyGate_sameWiring d q D j (by omega) (by omega))
    exact hRow (2 ^ d) le_rfl

theorem hybridBfly_edge_iff (d q : Nat) (u v : Fin (source d q).wires) :
    HybridCircuitEdge (source d q).circuit u v ↔
      CircuitEdge (ButterflyNet.source d).circuit u v :=
  hybridEdge_iff_of_sameWiring (buildHybridBfly_sameWiring d q d le_rfl) u v

theorem hybridBfly_treewidth_linear (d q : Nat)
    (td : TreeDecomp (HybridCircuitEdge (source d q).circuit)) :
    2 ^ d ≤ 18 * (td.width + 1) := by
  let td' : TreeDecomp (CircuitEdge (ButterflyNet.source d).circuit) :=
    { root := td.root
      cover_wire := td.cover_wire
      cover_edge := fun u v huv => td.cover_edge u v ((hybridBfly_edge_iff d q u v).mpr huv)
      running := td.running }
  exact ButterflyNet.butterfly_treewidth_linear d td'

theorem hybridBfly_gateContractionWidth_linear (d q : Nat) (hd : 2 ≤ d)
    (ct : ValidContractionTree (HybridCircuitEdge (source d q).circuit))
    (hLeaves : ct.tree.AllLeaves fun s =>
      (Finset.univ.filter fun x : Fin (2 ^ d) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d q)⟩ : Fin (source d q).wires) ∈ s).card ≤ 2) :
    2 ^ d ≤ 18 * ct.contractionWidth := by
  let ct' : ValidContractionTree (CircuitEdge (ButterflyNet.source d).circuit) :=
    { tree := ct.tree
      cover_wire := ct.cover_wire
      cover_edge := fun u v huv => ct.cover_edge u v ((hybridBfly_edge_iff d q u v).mpr huv) }
  exact ButterflyNet.butterfly_gateContractionWidth_linear d hd ct' hLeaves

theorem hybridBfly_escapes_sublinear_treewidth (d q : Nat → Nat) (hd : Tendsto d atTop atTop)
    (td : ∀ i, TreeDecomp (HybridCircuitEdge (source (d i) (q i)).circuit)) :
    ¬ ((fun i => ((td i).width : ℝ)) =o[atTop] (fun i => ((2 ^ d i : Nat) : ℝ))) := by
  let td' : ∀ i, TreeDecomp (CircuitEdge (ButterflyNet.source (d i)).circuit) := fun i =>
    { root := (td i).root
      cover_wire := (td i).cover_wire
      cover_edge := fun u v huv => (td i).cover_edge u v ((hybridBfly_edge_iff (d i) (q i) u v).mpr huv)
      running := (td i).running }
  exact ButterflyNet.butterfly_escapes_sublinear_treewidth d hd td'

theorem hybridBfly_escapes_sublinear_contractionWidth (d q : Nat → Nat) (hd : Tendsto d atTop atTop)
    (ct : ∀ i, ValidContractionTree (HybridCircuitEdge (source (d i) (q i)).circuit))
    (hLeaves : ∀ i, (ct i).tree.AllLeaves fun s =>
      (Finset.univ.filter fun x : Fin (2 ^ d i) =>
        (⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires (d i) (q i))⟩ :
          Fin (source (d i) (q i)).wires) ∈ s).card ≤ 2) :
    ¬ ((fun i => ((ct i).contractionWidth : ℝ)) =o[atTop] (fun i => ((2 ^ d i : Nat) : ℝ))) := by
  let ct' : ∀ i, ValidContractionTree (CircuitEdge (ButterflyNet.source (d i)).circuit) := fun i =>
    { tree := (ct i).tree
      cover_wire := (ct i).cover_wire
      cover_edge := fun u v huv => (ct i).cover_edge u v ((hybridBfly_edge_iff (d i) (q i) u v).mpr huv) }
  exact ButterflyNet.butterfly_escapes_sublinear_contractionWidth d hd ct' hLeaves

private theorem hybridBflyGate_weight (d q ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    (hybridBflyGate d q ℓ j hℓ hj).nonlinearWeight = if ℓ * 2 ^ d + j < q then 1 else 0 := by
  dsimp [hybridBflyGate]
  split_ifs <;> rfl

private theorem appendHybridBflyRow_nonlinearCount (d q ℓ : Nat) (hℓ : ℓ < d)
    (c : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) :
    ∀ j (hj : j ≤ 2 ^ d),
      (appendHybridBflyRow d q ℓ hℓ j hj c).nonlinearCount =
        c.nonlinearCount + (min q (ℓ * 2 ^ d + j) - min q (ℓ * 2 ^ d))
  | 0, _ => by simp [appendHybridBflyRow]
  | j + 1, hj => by
    have ih := appendHybridBflyRow_nonlinearCount d q ℓ hℓ c j (by omega)
    change (appendHybridBflyRow d q ℓ hℓ j (by omega) c).nonlinearCount +
        (hybridBflyGate d q ℓ j hℓ (by omega)).nonlinearWeight = _
    rw [ih, hybridBflyGate_weight]
    have hLe1 : min q (ℓ * 2 ^ d) ≤ min q (ℓ * 2 ^ d + j) :=
      min_le_min_left q (Nat.le_add_right _ _)
    have hLe2 : min q (ℓ * 2 ^ d + j) ≤ min q (ℓ * 2 ^ d + (j + 1)) :=
      min_le_min_left q (by omega)
    by_cases hLt : ℓ * 2 ^ d + j < q
    · simp only [hLt, ↓reduceIte]
      rw [min_eq_right (by omega : ℓ * 2 ^ d + j ≤ q),
        min_eq_right (by omega : ℓ * 2 ^ d + (j + 1) ≤ q)]
      omega
    · simp only [hLt, ↓reduceIte]
      rw [min_eq_left (by omega : q ≤ ℓ * 2 ^ d + j),
        min_eq_left (by omega : q ≤ ℓ * 2 ^ d + (j + 1))]
      omega

private theorem buildHybridBfly_nonlinearCount (d q : Nat) :
    ∀ D (hD : D ≤ d), (buildHybridBfly d q D hD).nonlinearCount = min q (D * 2 ^ d)
  | 0, _ => by simp [buildHybridBfly, HybridCircuit.nonlinearCount]
  | D + 1, hD => by
    have ih := buildHybridBfly_nonlinearCount d q D (by omega)
    change (appendHybridBflyRow d q D (by omega) (2 ^ d) le_rfl
        (buildHybridBfly d q D (by omega))).nonlinearCount = min q ((D + 1) * 2 ^ d)
    rw [appendHybridBflyRow_nonlinearCount, ih]
    have hMul : (D + 1) * 2 ^ d = D * 2 ^ d + 2 ^ d := by ring
    have hLe : min q (D * 2 ^ d) ≤ min q (D * 2 ^ d + 2 ^ d) :=
      min_le_min_left q (Nat.le_add_right _ _)
    rw [hMul]
    omega

theorem hybridBfly_nonlinearCount (d q : Nat) :
    (source d q).circuit.nonlinearCount = min q (d * 2 ^ d) :=
  buildHybridBfly_nonlinearCount d q d le_rfl

private theorem evalWires_snoc_lt {n w : Nat} (c : HybridCircuit n w) (g : HybridGate w)
    (x : Fin n → Bool) (u : Fin w) :
    (c.snoc g).evalWires x u.castSucc = c.evalWires x u := by
  simp [HybridCircuit.evalWires, Fin.snoc_castSucc]

private theorem evalWires_appendHybridBflyRow_lt (d q ℓ : Nat) (hℓ : ℓ < d)
    (c : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) (x : Fin (2 ^ d) → Bool) :
    ∀ j (hj : j ≤ 2 ^ d) (u : Fin (LayeredRing.ringWires (2 ^ d) ℓ)),
      (appendHybridBflyRow d q ℓ hℓ j hj c).evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩ = c.evalWires x u
  | 0, _, _ => rfl
  | j + 1, hj, u => by
    have ih := evalWires_appendHybridBflyRow_lt d q ℓ hℓ c x j (by omega) u
    change ((appendHybridBflyRow d q ℓ hℓ j (by omega) c).snoc _).evalWires x
        (Fin.castSucc ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩) = _
    rw [evalWires_snoc_lt]
    exact ih

private theorem evalWires_appendHybridBflyRow_zero_last (d ℓ : Nat) (hℓ : ℓ < d)
    (c : HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) (x : Fin (2 ^ d) → Bool) :
    ∀ j (hj : j ≤ 2 ^ d) (r : Nat) (hr : r < j),
      (appendHybridBflyRow d 0 ℓ hℓ j hj c).evalWires x
          ⟨LayeredRing.ringWires (2 ^ d) ℓ + r, by omega⟩ =
        Bool.xor
          (c.evalWires x ⟨ℓ * 2 ^ d + r, by
            rw [LayeredRing.ringWires_eq]
            have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            omega⟩)
          (c.evalWires x ⟨ℓ * 2 ^ d + ButterflyNet.flipBit r ℓ, by
            have hf := ButterflyNet.flipBit_lt (by omega : r < 2 ^ d) hℓ
            rw [LayeredRing.ringWires_eq]
            have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            omega⟩)
  | 0, _, _, hr => by omega
  | j + 1, hj, r, hr => by
    by_cases hrj : r < j
    · have ih := evalWires_appendHybridBflyRow_zero_last d ℓ hℓ c x j (by omega) r hrj
      change ((appendHybridBflyRow d 0 ℓ hℓ j (by omega) c).snoc _).evalWires x
          (Fin.castSucc ⟨LayeredRing.ringWires (2 ^ d) ℓ + r, by omega⟩) = _
      rw [evalWires_snoc_lt]
      exact ih
    · have hEq : r = j := by omega
      subst hEq
      change ((appendHybridBflyRow d 0 ℓ hℓ r (by omega) c).snoc
          (hybridBflyGate d 0 ℓ r hℓ (by omega))).evalWires x
          (Fin.last (LayeredRing.ringWires (2 ^ d) ℓ + r)) = _
      simp only [hybridBflyGate, HybridCircuit.evalWires, HybridGate.eval, Fin.snoc_last]
      have hOld := evalWires_appendHybridBflyRow_lt d 0 ℓ hℓ c x r (by omega)
      have hA := hOld ⟨ℓ * 2 ^ d + r, by
        rw [LayeredRing.ringWires_eq]
        have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
        omega⟩
      have hB := hOld ⟨ℓ * 2 ^ d + ButterflyNet.flipBit r ℓ, by
        have hf := ButterflyNet.flipBit_lt (by omega : r < 2 ^ d) hℓ
        rw [LayeredRing.ringWires_eq]
        have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
        omega⟩
      exact congrArg₂ Bool.xor hA hB

private theorem buildHybridBfly_zero_stable (d : Nat) (x : Fin (2 ^ d) → Bool) :
    ∀ D₁ D₂ ℓ j (h1 : ℓ ≤ D₁) (h2 : ℓ ≤ D₂) (hD1 : D₁ ≤ d) (hD2 : D₂ ≤ d) (hj : j < 2 ^ d),
      (buildHybridBfly d 0 D₁ hD1).evalWires x
          ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
        (buildHybridBfly d 0 D₂ hD2).evalWires x
          ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
  have hMono : ∀ D (hD : D ≤ d) ℓ j (h : ℓ ≤ D) (hj : j < 2 ^ d),
      (buildHybridBfly d 0 D hD).evalWires x ⟨ℓ * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
        (buildHybridBfly d 0 ℓ (h.trans hD)).evalWires x ⟨ℓ * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
    intro D
    induction D with
    | zero =>
      intro hD ℓ j h hj
      have h0 : ℓ = 0 := by omega
      subst h0
      rfl
    | succ D ih =>
      intro hD ℓ j h hj
      by_cases hEq : ℓ = D + 1
      · subst hEq; rfl
      · have hLe : ℓ ≤ D := by omega
        have hLt := evalWires_appendHybridBflyRow_lt d 0 D (by omega)
          (buildHybridBfly d 0 D (by omega)) x (2 ^ d) le_rfl
          ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩
        exact hLt.trans (ih (by omega) ℓ j hLe hj)
  intro D₁ D₂ ℓ j h1 h2 hD1 hD2 hj
  rw [hMono D₁ hD1 ℓ j h1 hj, hMono D₂ hD2 ℓ j h2 hj]

private theorem flipBit_div_pow_succ_and_xor (j ℓ : Nat) :
    ButterflyNet.flipBit j ℓ / 2 ^ (ℓ + 1) = j / 2 ^ (ℓ + 1) ∧
      (∀ a : Nat, a / 2 ^ (ℓ + 1) = j / 2 ^ (ℓ + 1) ↔
        (a / 2 ^ ℓ = j / 2 ^ ℓ ∧ a / 2 ^ ℓ ≠ ButterflyNet.flipBit j ℓ / 2 ^ ℓ) ∨
        (a / 2 ^ ℓ = ButterflyNet.flipBit j ℓ / 2 ^ ℓ ∧ a / 2 ^ ℓ ≠ j / 2 ^ ℓ)) := by
  let P := 2 ^ ℓ
  have hP : 0 < P := Nat.two_pow_pos ℓ
  have hP2 : 2 ^ (ℓ + 1) = P * 2 := Nat.pow_succ 2 ℓ
  have hDivSucc : ∀ z, z / (P * 2) = (z / P) / 2 := fun z => (Nat.div_div_eq_div_mul z P 2).symm
  have hFlipDiv : ButterflyNet.flipBit j ℓ / P =
      if (j / P) % 2 = 0 then j / P + 1 else j / P - 1 := by
    unfold ButterflyNet.flipBit
    change (if (j / P) % 2 = 0 then j + P else j - P) / P = _
    by_cases hBit : (j / P) % 2 = 0
    · simp only [hBit, ↓reduceIte]
      have h1 : j + P = j + 1 * P := by ring
      rw [h1, Nat.add_mul_div_right _ _ hP]
    · simp only [hBit, ↓reduceIte]
      have hBit1 : (j / P) % 2 = 1 := by
        have := Nat.mod_lt (j / P) (by decide : 0 < 2)
        omega
      have hQPos : 1 ≤ j / P := by
        by_contra h0
        have hEq0 : j / P = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h0)
        rw [hEq0] at hBit1
        simp at hBit1
      have hPLe : P ≤ j := by
        have h1 : 1 * P ≤ (j / P) * P := Nat.mul_le_mul_right P hQPos
        have h2 : P * (j / P) = (j / P) * P := Nat.mul_comm _ _
        have hDM := Nat.div_add_mod j P
        omega
      have h1 : j = (j - P) + 1 * P := by omega
      have h2 := congrArg (· / P) h1
      rw [Nat.add_mul_div_right _ _ hP] at h2
      omega
  have hDMj := Nat.div_add_mod (j / P) 2
  have hModj := Nat.mod_lt (j / P) (by decide : 0 < 2)
  have hFlipDiv2 : ButterflyNet.flipBit j ℓ / 2 ^ (ℓ + 1) = j / 2 ^ (ℓ + 1) := by
    rw [hP2, hDivSucc, hDivSucc, hFlipDiv]
    by_cases hBit : (j / P) % 2 = 0
    · simp only [hBit, ↓reduceIte]
      have hjEq : j / P + 1 = 2 * ((j / P) / 2) + 1 := by omega
      rw [hjEq]
      omega
    · simp only [hBit, ↓reduceIte]
      have hjEq : j / P - 1 = 2 * ((j / P) / 2) := by omega
      rw [hjEq]
      omega
  refine ⟨hFlipDiv2, fun a => ?_⟩
  rw [hP2, hDivSucc, hDivSucc]
  have hDMa := Nat.div_add_mod (a / P) 2
  have hModa := Nat.mod_lt (a / P) (by decide : 0 < 2)
  change (a / P) / 2 = (j / P) / 2 ↔
    (a / P = j / P ∧ a / P ≠ ButterflyNet.flipBit j ℓ / P) ∨
    (a / P = ButterflyNet.flipBit j ℓ / P ∧ a / P ≠ j / P)
  rw [hFlipDiv]
  by_cases hBit : (j / P) % 2 = 0
  · simp only [hBit, ↓reduceIte]
    omega
  · simp only [hBit, ↓reduceIte]
    omega

theorem xorBfly_wire_eval (d : Nat) (x : Fin (2 ^ d) → Bool) :
    ∀ ℓ (hℓ : ℓ ≤ d) (j : Nat) (hj : j < 2 ^ d),
      boolToZMod2 ((source d 0).circuit.evalWires x (ButterflyNet.bflyWire d ℓ j hℓ hj)) =
        ∑ i : Fin (2 ^ d), if i.val / 2 ^ ℓ = j / 2 ^ ℓ then boolToZMod2 (x i) else 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro h0 j hj
    have hSt := buildHybridBfly_zero_stable d x d 0 0 j h0 (le_rfl) le_rfl (Nat.zero_le d) hj
    change boolToZMod2 ((buildHybridBfly d 0 d le_rfl).evalWires x
      ⟨0 * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩) = _
    rw [hSt]
    simp only [buildHybridBfly, HybridCircuit.evalWires, Nat.zero_mul, Nat.zero_add]
    change boolToZMod2 (x ⟨j, hj⟩) = _
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro i _ hiNe
      have hNe : i.val ≠ j := fun h => hiNe (Fin.ext h)
      simp [hNe]
    · intro hMem
      exact absurd (Finset.mem_univ _) hMem
  | succ ℓ ih =>
    intro hSucc j hj
    have hStepSt := buildHybridBfly_zero_stable d x d (ℓ + 1) (ℓ + 1) j hSucc le_rfl le_rfl hSucc hj
    have hASt := buildHybridBfly_zero_stable d x d ℓ ℓ j (by omega) le_rfl (by omega) (by omega) hj
    have hBSt := buildHybridBfly_zero_stable d x d ℓ ℓ (ButterflyNet.flipBit j ℓ) (by omega)
      le_rfl (by omega) (by omega) (ButterflyNet.flipBit_lt hj (by omega))
    have hRow := evalWires_appendHybridBflyRow_zero_last d ℓ (by omega)
      (buildHybridBfly d 0 ℓ (by omega)) x (2 ^ d) le_rfl j hj
    have hLhs : (source d 0).circuit.evalWires x (ButterflyNet.bflyWire d (ℓ + 1) j hSucc hj) =
        Bool.xor
          ((source d 0).circuit.evalWires x (ButterflyNet.bflyWire d ℓ j (by omega) hj))
          ((source d 0).circuit.evalWires x
            (ButterflyNet.bflyWire d ℓ (ButterflyNet.flipBit j ℓ) (by omega)
              (ButterflyNet.flipBit_lt hj (by omega)))) := by
      change (buildHybridBfly d 0 d le_rfl).evalWires x
          ⟨(ℓ + 1) * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
        Bool.xor
          ((buildHybridBfly d 0 d le_rfl).evalWires x
            ⟨ℓ * 2 ^ d + j, by rw [LayeredRing.ringWires_eq]; nlinarith⟩)
          ((buildHybridBfly d 0 d le_rfl).evalWires x
            ⟨ℓ * 2 ^ d + ButterflyNet.flipBit j ℓ, by
              have hf := ButterflyNet.flipBit_lt hj (by omega : ℓ < d)
              rw [LayeredRing.ringWires_eq]; nlinarith⟩)
      rw [hStepSt, hASt, hBSt]
      have hW1 : (ℓ + 1) * 2 ^ d + j < LayeredRing.ringWires (2 ^ d) (ℓ + 1) := by
        rw [LayeredRing.ringWires_eq]
        have : (ℓ + 1) * 2 ^ d + 2 ^ d = ((ℓ + 1) + 1) * 2 ^ d := by ring
        omega
      have hW2 : LayeredRing.ringWires (2 ^ d) ℓ + j < LayeredRing.ringWires (2 ^ d) (ℓ + 1) := by
        rw [LayeredRing.ringWires_eq, LayeredRing.ringWires_eq]
        have : (ℓ + 1) * 2 ^ d + 2 ^ d = ((ℓ + 1) + 1) * 2 ^ d := by ring
        omega
      have hFinEq : (⟨(ℓ + 1) * 2 ^ d + j, by
            change _ < LayeredRing.ringWires (2 ^ d) (ℓ + 1)
            exact hW1⟩ : Fin (LayeredRing.ringWires (2 ^ d) ℓ + 2 ^ d)) =
          ⟨LayeredRing.ringWires (2 ^ d) ℓ + j, by omega⟩ := by
        apply Fin.ext
        dsimp only
        rw [LayeredRing.ringWires_eq]
      change (appendHybridBflyRow d 0 ℓ (by omega) (2 ^ d) le_rfl
          (buildHybridBfly d 0 ℓ (by omega))).evalWires x
            ⟨(ℓ + 1) * 2 ^ d + j, by change _ < LayeredRing.ringWires (2 ^ d) (ℓ + 1); exact hW1⟩ = _
      rw [hFinEq]
      exact hRow
    rw [hLhs, boolToZMod2_xor, ih (by omega) j hj,
      ih (by omega) (ButterflyNet.flipBit j ℓ) (ButterflyNet.flipBit_lt hj (by omega)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hPart := (flipBit_div_pow_succ_and_xor j ℓ).2 i.val
    by_cases hTop : i.val / 2 ^ (ℓ + 1) = j / 2 ^ (ℓ + 1)
    · simp only [hTop, ↓reduceIte]
      by_cases ha : i.val / 2 ^ ℓ = j / 2 ^ ℓ <;>
        by_cases hb : i.val / 2 ^ ℓ = ButterflyNet.flipBit j ℓ / 2 ^ ℓ
      · exfalso
        rcases hPart.mp hTop with ⟨_, hne⟩ | ⟨_, hne⟩
        · exact hne hb
        · exact hne ha
      · have hb' : j / 2 ^ ℓ ≠ ButterflyNet.flipBit j ℓ / 2 ^ ℓ := by rw [← ha]; exact hb
        simp [ha, hb']
      · have ha' : ButterflyNet.flipBit j ℓ / 2 ^ ℓ ≠ j / 2 ^ ℓ := by rw [← hb]; exact ha
        simp [hb, ha']
      · exfalso
        rcases hPart.mp hTop with ⟨heq, _⟩ | ⟨heq, _⟩
        · exact ha heq
        · exact hb heq
    · have hDivSucc : ∀ z, z / 2 ^ (ℓ + 1) = (z / 2 ^ ℓ) / 2 := fun z => by
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      have hNot1 : i.val / 2 ^ ℓ ≠ j / 2 ^ ℓ := fun hEq => by
        apply hTop
        rw [hDivSucc i.val, hDivSucc j, hEq]
      have hNot2 : i.val / 2 ^ ℓ ≠ ButterflyNet.flipBit j ℓ / 2 ^ ℓ := fun hEq => by
        apply hTop
        rw [← (flipBit_div_pow_succ_and_xor j ℓ).1, hDivSucc i.val, hDivSucc (ButterflyNet.flipBit j ℓ),
          hEq]
      simp [hTop, hNot1, hNot2]

/-- Exact closed-form `#Circuit-SAT` count on `XorButterflyNet` (`q = 0`), collapsing the
`Ω(n)`-treewidth butterfly into `2 ^ (n - 1)` accepting assignments. -/
theorem xorBfly_acceptCount (d : Nat) : (source d 0).acceptCount = 2 ^ (2 ^ d - 1) := by
  let sys : LinearSystem (2 ^ d) := [⟨fun _ => 1, 1⟩]
  have hSatIff : ∀ x : Fin (2 ^ d) → Bool, (source d 0).eval x = true ↔ sys.sat x := by
    intro x
    have hOutEq : (source d 0).output =
        ButterflyNet.bflyWire d d (2 ^ d - 1) le_rfl (by have := Nat.two_pow_pos d; omega) := by
      apply Fin.ext
      have hEq := LayeredRing.ringWires_eq (2 ^ d) d
      have hPos : 0 < 2 ^ d := Nat.two_pow_pos d
      change (LayeredRing.ringWires (2 ^ d) d - 1) = d * 2 ^ d + (2 ^ d - 1)
      rw [hEq, Nat.succ_mul]
      omega
    have hEval : boolToZMod2 ((source d 0).eval x) = ∑ i : Fin (2 ^ d), boolToZMod2 (x i) := by
      change boolToZMod2 ((source d 0).circuit.evalWires x (source d 0).output) = _
      rw [hOutEq, xorBfly_wire_eval d x d le_rfl (2 ^ d - 1) (by have := Nat.two_pow_pos d; omega)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : i.val / 2 ^ d = 0 := Nat.div_eq_of_lt i.isLt
      have hj : (2 ^ d - 1) / 2 ^ d = 0 := Nat.div_eq_of_lt (by have := Nat.two_pow_pos d; omega)
      simp [hi, hj]
    constructor
    · intro hT f hf
      simp only [sys, List.mem_singleton] at hf
      subst hf
      have h1 : boolToZMod2 ((source d 0).eval x) = 1 := (boolToZMod2_eq_one_iff _).mpr hT
      dsimp [AffineForm.evalZ2]
      simp only [one_mul]
      rw [← hEval, h1]
      decide
    · intro hSat
      have hEq0 := hSat ⟨fun _ => 1, 1⟩ (by simp [sys])
      dsimp [AffineForm.evalZ2] at hEq0
      simp only [one_mul] at hEq0
      rw [← hEval] at hEq0
      rw [← boolToZMod2_eq_one_iff]
      generalize boolToZMod2 ((source d 0).eval x) = hz at hEq0 ⊢
      fin_cases hz
      · exfalso
        revert hEq0
        decide
      · rfl
  have hCountEq : (source d 0).acceptCount = sys.solSet.card := by
    dsimp [HybridCircuitInstance.acceptCount]
    congr 1
    ext x
    simp [LinearSystem.mem_solSet, hSatIff x]
  let x₀ : Fin (2 ^ d) → Bool := fun i => decide (i.val = 0)
  have hx₀ : sys.sat x₀ := by
    intro f hf
    simp only [sys, List.mem_singleton] at hf
    subst hf
    dsimp [AffineForm.evalZ2]
    have hSum1 : ∑ i : Fin (2 ^ d), (1 : ZMod 2) * boolToZMod2 (x₀ i) = 1 := by
      let h0 : Fin (2 ^ d) := ⟨0, Nat.two_pow_pos d⟩
      rw [Finset.sum_eq_single h0]
      · simp [x₀, h0, boolToZMod2]
      · intro i _ hiNe
        have hNe0 : i ≠ 0 := fun h => hiNe (Fin.ext (by simp [h0, h]))
        simp [x₀, boolToZMod2, hNe0]
      · intro hMem
        exact absurd (Finset.mem_univ _) hMem
    rw [hSum1]
    decide
  have hRank1 : Module.finrank (ZMod 2) (LinearMap.range sys.matrixMap) = 1 := by
    have hTop : LinearMap.range sys.matrixMap = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      let h0 : Fin (2 ^ d) := ⟨0, Nat.two_pow_pos d⟩
      let j0 : Fin sys.length := ⟨0, by simp [sys]⟩
      let val : ZMod 2 := y j0
      refine ⟨(Pi.single h0 val : Fin (2 ^ d) → ZMod 2), ?_⟩
      ext j
      have hj0 : j = j0 := by
        apply Fin.ext
        have hJ := j.isLt
        simp only [sys, List.length_cons, List.length_nil, Nat.zero_add] at hJ
        simp only [j0]
        omega
      subst hj0
      dsimp [LinearSystem.matrixMap]
      simp [sys, val]
    rw [hTop, finrank_top, Module.finrank_fin_fun (ZMod 2)]
    simp [sys]
  rw [hCountEq, (LinearSystem.linearSystem_card_eq_of_nonempty sys hx₀).2, hRank1]

theorem hybridBfly_subexponential_of_sublinear_nonlinear (d q : Nat → Nat)
    (hd : Tendsto d atTop atTop)
    (hq : (fun i => (q i : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) :
    (fun i => affineBranchLogTimeBudget (2 ^ d i) (source (d i) (q i)).wires
        (source (d i) (q i)).circuit.nonlinearCount) =o[atTop]
      fun i => ((2 ^ d i : Nat) : ℝ) := by
  have hn : Tendsto (fun i => 2 ^ d i) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨i₀, hi₀⟩ := tendsto_atTop_atTop.mp hd b
    refine ⟨i₀, fun i hi => ?_⟩
    exact le_trans (hi₀ i hi) (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hqNL : (fun i => ((source (d i) (q i)).circuit.nonlinearCount : ℝ)) =o[atTop]
      fun i => ((2 ^ d i : Nat) : ℝ) := by
    refine IsBigO.trans_isLittleO ?_ hq
    refine IsBigO.of_bound 1 (Eventually.of_forall fun i => ?_)
    rw [hybridBfly_nonlinearCount, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    simp
  have hw : ∀ᶠ i in atTop, (source (d i) (q i)).wires ≤ (2 ^ d i + 2) ^ 2 := by
    filter_upwards [hd.eventually_ge_atTop 1] with i _
    rw [wires_eq]
    have hDLe : d i + 1 ≤ 2 ^ d i + 2 := by
      have := Nat.lt_two_pow_self (n := d i)
      omega
    have h1 : (d i + 1) * 2 ^ d i ≤ (2 ^ d i + 2) * (2 ^ d i + 2) :=
      Nat.mul_le_mul hDLe (by omega)
    simpa [pow_two] using h1
  exact affineBranchLogTimeBudget_isLittleO hn hqNL 2 hw

theorem butterfly_allNonlinear_escapes_sublinear_budget (d : Nat → Nat)
    (hd : Tendsto d atTop atTop) :
    ¬ ((fun i => ((HybridCircuit.ofCircuit (ButterflyNet.source (d i)).circuit).nonlinearCount : ℝ)) =o[atTop]
      fun i => ((2 ^ d i : Nat) : ℝ)) := by
  intro hLittleO
  have hBound : ∀ᶠ i in atTop,
      ‖((HybridCircuit.ofCircuit (ButterflyNet.source (d i)).circuit).nonlinearCount : ℝ)‖ ≤
        (1 : ℝ) * ‖((2 ^ d i : Nat) : ℝ)‖ :=
    hLittleO.bound (by norm_num : (0 : ℝ) < 1)
  have hD : ∀ᶠ i in atTop, 2 ≤ d i := hd.eventually_ge_atTop 2
  obtain ⟨i, hi, hd2⟩ := (hBound.and hD).exists
  have hEq : (HybridCircuit.ofCircuit (ButterflyNet.source (d i)).circuit).nonlinearCount =
      d i * 2 ^ d i := by
    rw [HybridCircuit.ofCircuit_nonlinearCount_eq_binaryGateCount,
      ButterflyNet.source_binaryGateCount]
  rw [hEq, Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hi
  have hCast : ((d i * 2 ^ d i : Nat) : ℝ) = (d i : ℝ) * ((2 ^ d i : Nat) : ℝ) := by
    push_cast; rfl
  have hPos : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by positivity
  have hdReal : (2 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hd2
  nlinarith

end HybridButterflyNet

end PvsNP
