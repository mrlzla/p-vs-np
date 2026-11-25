module

public import MCSPSecondBlockExits

/-! A two-input raw gate lets its block choose the first exit's controlling
polarity. Find the exit in the original wiring before committing the pins. -/

@[expose] public section

namespace PvsNP.Frontier.ConstantBlockExits

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest ForestBlockPinning ForestPinning RestrictionCharges
open FreshCharges NestedFaces QuadraticForest DownstreamBlockPinning
open IndependentBlockPinning MultiBlockPinning SecondBlockExits
open scoped Classical BigOperators

section Wiring

variable {n k g a d : ℕ}

private theorem binary_of_distinct_ports (op : Op)
    (i j : Fin (signature.Arity op)) (hne : i ≠ j) : op = .and ∨ op = .or := by
  cases op with
  | const b => exact Fin.elim0 i
  | not => exact (hne ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  | and => exact Or.inl rfl
  | or => exact Or.inr rfl

private theorem binary_same_value (op : Op) (i j : Fin (signature.Arity op))
    (hne : i ≠ j) (f : Fin (signature.Arity op) → Bool) (b : Bool)
    (hi : f i = b) (hj : f j = b) : interpretation op f = b := by
  have hb := binary_of_distinct_ports op i j hne
  rcases hb with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [interpretation]

private theorem gate_same_value (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (j : Fin g) (i r : Fin (signature.Arity (p.lines j).op)) (hne : i ≠ r) (b : Bool)
    (hi : restrictedWire p ρ ((p.lines j).wires i) = fun _ => b)
    (hr : restrictedWire p ρ ((p.lines j).wires r) = fun _ => b) :
    restrictedWire p ρ (.gate j) = fun _ => b := by
  funext z
  unfold restrictedWire
  rw [p.trace_gate]
  exact binary_same_value _ i r hne _ b (congrFun hi z) (congrFun hr z)

/-- A binary gate reading two original raw inputs in the same block. -/
def HasRawPair (p : Program signature (2^(a+d)) g) (s : BitString a) : Prop :=
  ∃ (j : Fin g) (i r : Fin (signature.Arity (p.lines j).op)), i ≠ r ∧
    ∃ u ∈ block (d := d) s, ∃ v ∈ block (d := d) s,
      (p.lines j).wires i = .input u ∧ (p.lines j).wires r = .input v

noncomputable def rawPairBlocks (p : Program signature (2^(a+d)) g)
    (E : Finset (BitString a)) : Finset E :=
  Finset.univ.filter fun s => HasRawPair p s.val

private theorem block_subset_blocks {E : Finset (BitString a)} {s : BitString a} (hs : s ∈ E) :
    block (d := d) s ⊆ blocks (d := d) E := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.symm ▸ hs⟩

/-- Paths through direct readers of a single block, before any pins are assigned. -/
inductive BlockReaderPath (p : Program signature (2^(a+d)) g) (s : BitString a) (j : Fin g) :
    Fin g → Prop where
  | start : s ∈ readerTags p j → BlockReaderPath p s j j
  | step {u v} : BlockReaderPath p s j u → s ∈ readerTags p v →
      (∃ i, (p.lines v).wires i = .gate u) → BlockReaderPath p s j v

private theorem BlockReaderPath.mem_tags {p : Program signature (2^(a+d)) g} {s : BitString a}
    {j u : Fin g} (h : BlockReaderPath p s j u) : s ∈ readerTags p u := by
  cases h with
  | start h => exact h
  | step _ h _ => exact h

private theorem BlockReaderPath.propagates {p : Program signature (2^(a+d)) g} {s : BitString a}
    {j u : Fin g} (h : BlockReaderPath p s j u) (E : Finset (BitString a)) (hs : s ∈ E)
    (x : BitString (2^(a+d))) (b : Bool)
    (hx : ∀ i ∈ block (d := d) s, x i = b)
    (hSeed : restrictedWire p (pinAt x (blocks (d := d) E)) (.gate j) = fun _ => b) :
    restrictedWire p (pinAt x (blocks (d := d) E)) (.gate u) = fun _ => b := by
  induction h with
  | start => exact hSeed
  | @step u v _ hTag hEdge ih =>
    obtain ⟨i, hi⟩ := hEdge
    obtain ⟨z, hz, k, hk⟩ := (Finset.mem_filter.mp (mem_readerTags.mp hTag)).2
    have hn : i ≠ k := by
      intro he
      rw [he, hk] at hi
      cases hi
    have hPin := pin_input_constant p x (block_subset_blocks hs hz)
    rw [hx z hz] at hPin
    exact gate_same_value p _ v i k hn b (hi ▸ ih) (hk ▸ hPin)

/-- An output that stays nonconstant for every assignment cannot directly
read one of these pins. -/
private theorem output_not_direct (p : Program signature n g) (P : Finset (Fin n))
    (root : Wire n g)
    (hNon : ∀ x : BitString n, ¬∃ b : Bool, restrictedWire p (pinAt x P) root = fun _ => b)
    {j : Fin g} (he : root = .gate j) : j ∉ directReaders p P := by
  intro h
  obtain ⟨i, hi, a, ha⟩ := (Finset.mem_filter.mp h).2
  obtain ⟨v, b, hv⟩ := op_can_force_constant (p.lines j).op a
  apply hNon (fun _ => v)
  refine ⟨b, funext fun z => ?_⟩
  rw [he]
  have hArg : restrictedWire p (pinAt (fun _ => v) P) ((p.lines j).wires a) = fun _ => v :=
    ha ▸ pin_input_constant p (fun _ => v) hi
  unfold restrictedWire
  rw [p.trace_gate]
  exact hv _ (congrFun hArg z)

/-- Locate the first exit in the original wiring, ahead of choosing the
block polarity. Separation confines the earlier readers to this block. -/
theorem exists_structural_exit (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (hSep : Separated p E)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hNon : ∀ x : BitString (2^(a+d)),
      ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b)
    (s : E) (j : Fin g) (hj : ResidualLive p Sum.inl root j) (hs : s.val ∈ readerTags p j) :
    ∃ u : Fin g, u ∉ directReaders p (blocks (d := d) E) ∧
      ∃ v : Fin g, BlockReaderPath p s.val j v ∧ ∃ i, (p.lines u).wires i = .gate v := by
  let P := blocks (d := d) E
  by_contra hNo
  have hAbsent {u : Fin g} (h : ResidualLive p Sum.inl root u) :
      ¬ BlockReaderPath p s.val j u := by
    induction h with
    | @output u hRep =>
      intro h
      have hu := mem_readerTags.mp h.mem_tags
      have hSub := block_subset_blocks (d := d) s.property
      obtain ⟨i, hi, b, hb⟩ := (Finset.mem_filter.mp hu).2
      exact output_not_direct p P root hNon (original_represents_gate hFresh hRep)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hSub hi, b, hb⟩)
    | @argument u v hU i hRep ih =>
      intro hv
      have he := original_represents_gate hFresh hRep
      have hsU := readerTags_subset_nearby_of_wire p he hv.mem_tags
      have hDirect : u ∈ directReaders p P := by
        by_contra h
        exact hNo ⟨u, h, v, hv, i, he⟩
      obtain ⟨z, hz, k, hk⟩ := (Finset.mem_filter.mp hDirect).2
      have hzE : tag z ∈ E := (Finset.mem_filter.mp hz).2
      have hzTag : tag z ∈ readerTags p u := mem_readerTags.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, k, hk⟩)
      have hzEq : s.val = tag z := by
        by_contra hn
        exact hSep s.val s.property _ hzE hn u hsU (readerTags_subset_nearby p u hzTag)
      exact ih (BlockReaderPath.step hv (hzEq ▸ hzTag) ⟨i, he⟩)
  exact hAbsent hj (.start hs)

end Wiring

section ChoosingPins

variable {a d g : ℕ}

/-- Every block containing both raw inputs of a gate can make its
matched first exit constant. Choices on different blocks are independent. -/
theorem choose_pins_for_rawPair_exits (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (hSep : Separated p E)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i)
    (hNon : ∀ x : BitString (2^(a+d)),
      ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    ∃ (x : BitString (2^(a+d))) (first : E ↪ downstreamReaders p (blocks (d := d) E) x),
      (∀ s : E, s.val ∈ nearbyTags p (first s).val) ∧
      rawPairBlocks p E ⊆ constantExitBlocks p E x first := by
  let P := blocks (d := d) E
  have oneBlock (s : E) : ∃ b : Bool, ∀ x : BitString (2^(a+d)),
      (∀ i ∈ block (d := d) s.val, x i = b) →
      ∃ j ∈ downstreamReaders p P x, s.val ∈ nearbyTags p j ∧
        (HasRawPair p s.val →
          ∃ v : Bool, restrictedWire p (pinAt x P) (.gate j) = fun _ => v) := by
    by_cases hPair : HasRawPair p s.val
    · obtain ⟨j, i, r, hne, u, hu, v, hv, hi, hr⟩ := hPair
      have hTag : s.val ∈ readerTags p j := mem_readerTags.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, i, hi⟩)
      obtain ⟨exit, hOutside, w, hPath, q, hq⟩ := exists_structural_exit p root E hSep hFresh hNon
        s j (mem_liveFresh_iff.mp (hLive.symm ▸ Finset.mem_univ j)) hTag
      obtain ⟨b, value, hForce⟩ := op_can_force_constant (p.lines exit).op q
      refine ⟨b, fun x hx => ?_⟩
      let ρ := pinAt x P
      have hU := pin_input_constant p x (block_subset_blocks s.property hu)
      have hV := pin_input_constant p x (block_subset_blocks s.property hv)
      rw [hx u hu] at hU
      rw [hx v hv] at hV
      have hSeed := gate_same_value p ρ j i r hne b (hi ▸ hU) (hr ▸ hV)
      have hArg : restrictedWire p ρ ((p.lines exit).wires q) = fun _ => b :=
        hq ▸ hPath.propagates E s.property x b hx hSeed
      refine ⟨exit, Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, b, hArg⟩, hOutside⟩,
        readerTags_subset_nearby_of_wire p hq hPath.mem_tags, fun _ => ⟨value, ?_⟩⟩
      funext z
      unfold restrictedWire
      rw [p.trace_gate]
      exact hForce _ (congrFun hArg z)
    · obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [card_block]; exact Nat.two_pow_pos _ :
        0 < (block (d := d) s.val).card)
      have hiP := block_subset_blocks s.property hi
      obtain ⟨j, q, hq⟩ := hRead i hiP
      obtain ⟨b, v, hv⟩ := op_can_force_constant (p.lines j).op q
      refine ⟨b, fun x hx => ?_⟩
      have hConst : restrictedWire p (pinAt x P) (.gate j) = fun _ => v := by
        funext z
        have hA : restrictedWire p (pinAt x P) ((p.lines j).wires q) = fun _ => b := by
          rw [hq, pin_input_constant p x hiP, hx i hi]
        unfold restrictedWire
        rw [p.trace_gate]
        exact hv _ (congrFun hA z)
      obtain ⟨u, hu, hs⟩ := has_exit_of_constant_reader p root E x hSep hFresh (hNon x)
        s.val s.property (mem_liveFresh_iff.mp (hLive.symm ▸ Finset.mem_univ j))
        (mem_readerTags.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, q, hq⟩)) ⟨v, hConst⟩
      exact ⟨u, hu, hs, fun h => (hPair h).elim⟩
  choose bit hBit using oneBlock
  let x (i : Fin (2^(a+d))) : Bool :=
    if h : tag i ∈ E then bit ⟨tag i, h⟩ else false
  have exits (s : E) := hBit s x (fun i hi => by
    have he : tag i = s.val := (Finset.mem_filter.mp hi).2
    simp only [x, he, s.property, dite_true])
  choose j hMem hTag hC using exits
  let toExit (s : E) : downstreamReaders p P x := ⟨j s, hMem s⟩
  have hInj : Function.Injective toExit := by
    intro s q h
    apply Subtype.ext
    by_contra hn
    have he : j s = j q := congrArg Subtype.val h
    exact hSep s.val s.property q.val q.property hn (j s) (hTag s) (he.symm ▸ hTag q)
  refine ⟨x, ⟨toExit, hInj⟩, hTag, ?_⟩
  intro s hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC s ((Finset.mem_filter.mp hs).2)⟩

/-- There is one second exit for every raw-pair block. The two-layer
matching pays for all first and second exits using distinct indices. -/
theorem rawPair_blocks_force_extra (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a))
    (hSep : SeparatedBy (extendedTags p) E) (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i)
    (hNon : ∀ x : BitString (2^(a+d)),
      ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    ∃ x : BitString (2^(a+d)),
      E.card+(rawPairBlocks p E).card ≤ (downstreamReaders p (blocks (d := d) E) x).card := by
  have hNear : Separated p E := by
    intro u hu v hv hne j huj hvj
    exact hSep u hu v hv hne j (nearbyTags_subset_extended p j huj) (nearbyTags_subset_extended p j hvj)
  obtain ⟨x, first, hFirst, hPair⟩ :=
    choose_pins_for_rawPair_exits p root E hNear hFresh hLive hRead hNon
  exact ⟨x, (Nat.add_le_add_left (Finset.card_le_card hPair) _).trans
    (first_and_second_exits p root E x first hFirst hSep hFresh hLive (hNon x))⟩

end ChoosingPins

section ExactMCSP

variable {a d B : ℕ}

/-- When every joint pin assignment keeps the probes and sparsity, the
raw-pair blocks contribute the second-layer charge to the full forest. -/
theorem exact_mcsp_rawPair_block_lower
    (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+d))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+d))))
    (hd : 1 ≤ d) (hFew : descriptionBitBound (a+d) < 2^(a+d)) (hB : B < 2^(a+d))
    (E : Finset (BitString a)) (hSep : SeparatedBy (extendedTags c.program) E)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin c.size, ∃ k, (c.program.lines j).wires k = .input i)
    (hSparse : ∀ x : BitString (2^(a+d)), (acceptingTables fun y => mcspSquare (a+d)
      (substitute (pinAt x (blocks (d := d) E)) y)).card ≤ 2^B)
    (hQuad : ∀ (x : BitString (2^(a+d))) (u : BitString (a+d)) (b : Bool) (v w : BitString (a+d)),
      mcspSquare (a+d) (substitute (pinAt x (blocks (d := d) E)) (MCSP.truthTable _ (quad u b v w))) =
        true) :
    280*(2*2^(a+d) + E.card*2^(d-1) + E.card + (rawPairBlocks c.program E).card) +
      2*2^(a+d) ≤ 280*(c.size+2*B+1) + 17*B := by
  let m := a+d
  let P := blocks (d := d) E
  have hInitNon := not_constant_of_sparse hFew (card_accepting_mcspSquare_le m)
    (mcspSquare_constant_table m (by omega) false)
  have hFresh := minimum_fresh_univ c hc hMin hInitNon
  have hLive := minimum_live_univ c hc hMin hInitNon
  have hNon (x : BitString (2^m)) :
      ¬∃ b : Bool, restrictedWire c.program (pinAt x P) (c.outputs 0) = fun _ => b := by
    rw [restricted_circuit_eq c hc]
    apply not_constant_of_sparse hB (hSparse x)
    have h := hQuad x (zeroVec m) false (zeroVec m) (zeroVec m)
    have he : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, SuperTwoN.affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  have hNear : Separated c.program E := by
    intro u hu v hv hn j hj hk
    exact hSep u hu v hv hn j (nearbyTags_subset_extended c.program j hj)
      (nearbyTags_subset_extended c.program j hk)
  obtain ⟨x, first, hFirst, hPair⟩ :=
    choose_pins_for_rawPair_exits c.program (c.outputs 0) E hNear hFresh hLive hRead hNon
  have h := preserved_forest_two_layers c hc hMin hd hFew hB E x first hFirst hSep hRead (hSparse x) (hQuad x)
  have hCount := Finset.card_le_card hPair
  omega

/-- Choose all the blocks from an eligible pool in the original minimum
circuit. With enough raw-pair prefixes the downstream charge grows to
two gates per selected block. -/
theorem exact_mcsp_many_rawPair_blocks {k l r K H reserve : ℕ}
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l)))))
    (hd : 1 ≤ k+l) (hFew : descriptionBitBound (a+(k+l)) < 2^(a+(k+l)))
    (pool : Finset (BitString a)) (hPool : ∀ s ∈ pool, HasRawPair (d := k+l) c.program s)
    (hCovered : blocks (d := k+l) pool ⊆ needInputs c.program (c.outputs 0) false)
    (hHeavy : 18*c.size < K*(H+1))
    (hRoom : r*(18*K+1)+H ≤ pool.card)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (hReserve : reserve ≤ descriptionBitBound (a+(k+l)))
    (hFactorial : 2^(r*2^(k+l)+reserve) ≤ ((a+(k+l))^2).factorial) :
    280*(2*2^(a+(k+l)) + r*2^(k+l-1) + 2*r) + 2*2^(a+(k+l)) ≤
      280*(c.size+2*(descriptionBitBound (a+(k+l))-reserve)+1) +
        17*(descriptionBitBound (a+(k+l))-reserve) := by
  let m := a+(k+l)
  let B := descriptionBitBound m
  obtain ⟨E, hE, hCard, hSep⟩ := exists_separated_subset_by (extendedTags (a := a) (d := k+l) c.program)
    (card_extendedTags_le c.program) pool r K H hHeavy hRoom
  let P := blocks (d := k+l) E
  have hP : P.card = r*2^(k+l) := (card_blocks E).trans (by rw [hCard])
  have h0 := mcspSquare_constant_table m (by omega) false
  have h1 := mcspSquare_constant_table m (by omega) true
  have hc0 : cornerValue c.program false (c.outputs 0) = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue c.program true (c.outputs 0) = true := (congrFun (hc _) 0).trans h1
  have hRead (i : Fin (2^m)) (hi : i ∈ P) : ∃ j : Fin c.size, ∃ b, (c.program.lines j).wires b = .input i := by
    have hp : i ∈ blocks (d := k+l) pool := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hE (Finset.mem_filter.mp hi).2⟩
    obtain ⟨j, _, b, hb⟩ := need_input_has_reader hc0 hc1 (hCovered hp)
    exact ⟨j, b, hb⟩
  have hAccept (x : BitString (2^m)) :
      (acceptingTables fun y => mcspSquare m (substitute (pinAt x P) y)).card ≤ 2^(B-reserve) :=
    padded_sparsity_of_factorial x P hReserve (by rwa [hP])
  have hQuad (x : BitString (2^m)) (u : BitString m) (v : Bool) (q s : BitString m) :
      mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad u v q s))) = true := by
    apply accepted_after_blocks_pin (k := k) (l := l)
    have hCost := QuadraticPinning.complexity_quad_shared_le u v q s
    dsimp only [m] at hCost
    rw [hCard]
    omega
  have hAll : rawPairBlocks c.program E = Finset.univ :=
    Finset.eq_univ_of_forall fun s => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPool s.val (hE s.property)⟩
  have h := exact_mcsp_rawPair_block_lower c hc hMin hd hFew ((Nat.sub_le B reserve).trans_lt hFew)
    E hSep hRead hAccept hQuad
  rw [hAll, Finset.card_univ, Fintype.card_coe, hCard] at h
  dsimp only [B, m] at h
  omega

end ExactMCSP

section Control

/-- A read-once control with a fully pinned OR and a subsequent AND exit. -/
def rawPairControlProgram : Program signature 4 3 :=
  let p0 : Program signature 4 0 := .empty
  let p1 := p0.gate ⟨.or, fun a => if a = 0 then .input 0 else .input 2⟩
  let p2 := p1.gate ⟨.and, fun a => if a = 0 then .gate 0 else .input 1⟩
  p2.gate ⟨.or, fun a => if a = 0 then .gate 1 else .input 3⟩

def rawPairControl : Circuit signature 4 1 := ⟨rawPairControlProgram, fun _ => .gate 2⟩

def rawPairControlFunction (x : BitString 4) : Bool := ((x 0 || x 2) && x 1) || x 3

theorem rawPair_control_computes : rawPairControl.Computes interpretation (single rawPairControlFunction) := by
  intro x
  rfl

theorem rawPair_control_minimum :
    rawPairControl.size = complexity interpretation (single rawPairControlFunction) := by
  let e : Equiv.Perm (Fin 4) := Equiv.swap 1 2
  have h := PermutedCut.complexity_comp_perm e SecondBlockExits.aliasFunction
  have he : (fun x => SecondBlockExits.aliasFunction (x ∘ e)) = rawPairControlFunction := by
    funext x
    have e0 : e 0 = 0 := by decide
    have e1 : e 1 = 2 := by decide
    have e2 : e 2 = 1 := by decide
    have e3 : e 3 = 3 := by decide
    simp only [SecondBlockExits.aliasFunction, Function.comp_apply, e0, e1, e2, e3, rawPairControlFunction]
  rw [he] at h
  exact SecondBlockExits.alias_circuit_minimum.trans h.symm

def rawPairControlBlocks : Finset (BitString 1) := {fun _ => false}

theorem rawPair_control_pins : blocks (d := 1) rawPairControlBlocks = ({0, 2} : Finset (Fin 4)) := by
  have hTag0 : tag (a := 1) (d := 1) (0 : Fin 4) = fun _ => false := by
    funext i
    rw [Fin.eq_zero i]
    decide
  have hTag2 : tag (a := 1) (d := 1) (2 : Fin 4) = fun _ => false := by
    funext i
    rw [Fin.eq_zero i]
    decide
  have hS : ({0, 2} : Finset (Fin 4)) ⊆ blocks (d := 1) rawPairControlBlocks := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hTag0]
      exact Finset.mem_singleton_self _
    · rw [Finset.mem_singleton.mp hi, hTag2]
      exact Finset.mem_singleton_self _
  apply (Finset.eq_of_subset_of_card_le hS ?_).symm
  rw [card_blocks]
  decide

/-- The pin rule produces two distinct original downstream deletions in
the minimum control. The default all-true pins would alias the first exit. -/
theorem rawPair_control_two_exits :
    ∃ x : BitString 4,
      2 ≤ (downstreamReaders rawPairControlProgram (blocks (d := 1) rawPairControlBlocks) x).card := by
  let E := rawPairControlBlocks
  let P := blocks (d := 1) E
  let p := rawPairControlProgram
  have hSep : SeparatedBy (extendedTags (a := 1) (d := 1) p) E := by
    intro u hu v hv hne
    exact (hne ((Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm)).elim
  have hRead : ∀ i ∈ P, ∃ j : Fin 3, ∃ q, (p.lines j).wires q = .input i := by
    intro i hi
    rw [show P = ({0, 2} : Finset (Fin 4)) from rawPair_control_pins] at hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨0, ⟨0, by decide⟩, rfl⟩
    · rw [Finset.mem_singleton.mp hi]
      exact ⟨0, ⟨1, by decide⟩, rfl⟩
  have hNon (x : BitString 4) :
      ¬∃ b : Bool, restrictedWire p (pinAt x P) (.gate 2) = fun _ => b := by
    rintro ⟨b, h⟩
    have h0 := congrFun h (![false,false,false,false] : BitString 4)
    have h1 := congrFun h (![false,false,false,true] : BitString 4)
    change rawPairControlFunction (substitute (pinAt x P) ![false,false,false,false]) = b at h0
    change rawPairControlFunction (substitute (pinAt x P) ![false,false,false,true]) = b at h1
    rw [show P = ({0,2} : Finset (Fin 4)) from rawPair_control_pins] at h0 h1
    simp [rawPairControlFunction, substitute, pinAt] at h0 h1
    cases h0.symm.trans h1
  have hInitialNon : ¬∃ b : Bool, rawPairControlFunction = fun _ => b := by
    rintro ⟨b, h⟩
    have h0 := congrFun h (![false,false,false,false] : BitString 4)
    have h1 := congrFun h (![false,false,false,true] : BitString 4)
    simp [rawPairControlFunction] at h0 h1
    cases h0.symm.trans h1
  have hFresh := minimum_fresh_univ rawPairControl rawPair_control_computes rawPair_control_minimum hInitialNon
  have hLive := minimum_live_univ rawPairControl rawPair_control_computes rawPair_control_minimum hInitialNon
  obtain ⟨x, hx⟩ := rawPair_blocks_force_extra (a := 1) (d := 1) p (.gate 2) E hSep hFresh hLive hRead hNon
  have hPair : (rawPairBlocks (a := 1) (d := 1) p E).card = E.card := by
    have he : rawPairBlocks (a := 1) (d := 1) p E = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro s
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, 0, ⟨0, by decide⟩, ⟨1, by decide⟩, by decide, 0, ?_, 2, ?_, rfl, rfl⟩
      · have h : (0 : Fin 4) ∈ P := by rw [show P = ({0, 2} : Finset (Fin 4)) from rawPair_control_pins]; decide
        have he : tag (a := 1) (d := 1) (0 : Fin 4) = s.val := by
          exact (Finset.mem_singleton.mp (Finset.mem_filter.mp h).2).trans
            (Finset.mem_singleton.mp s.property).symm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      · have h : (2 : Fin 4) ∈ P := by rw [show P = ({0, 2} : Finset (Fin 4)) from rawPair_control_pins]; decide
        have he : tag (a := 1) (d := 1) (2 : Fin 4) = s.val :=
          (Finset.mem_singleton.mp (Finset.mem_filter.mp h).2).trans
            (Finset.mem_singleton.mp s.property).symm
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    rw [he, Finset.card_univ, Fintype.card_coe]
  rw [hPair, show E.card = 1 by simp [E, rawPairControlBlocks]] at hx
  exact ⟨x, hx⟩

end Control

section Counting

/-- Keep the factorial of the earlier part of the product when bounding
a consecutive run of large factors. -/
private theorem pow_mul_factorial_le {q k : ℕ} (hk : 2^k ≤ q+1) (j : ℕ) :
    2^(k*j)*q.factorial ≤ (q+j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, pow_add, ← Nat.add_assoc, Nat.factorial_succ]
    calc
      _ = 2^k*(2^(k*j)*q.factorial) := by ring
      _ ≤ (q+j+1)*(q+j).factorial :=
        Nat.mul_le_mul (hk.trans (by omega)) ih

private def dyadicFactorialExponent : ℕ → ℕ
  | 0 => 0
  | n+1 => dyadicFactorialExponent n + n*2^n

private theorem dyadic_factorial_bound (j : ℕ) :
    2^dyadicFactorialExponent j ≤ (2^j-1).factorial := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hPos : 0 < (2:ℕ)^j := Nat.two_pow_pos j
    have hFactor := pow_mul_factorial_le (q := 2^j-1) (k := j) (by omega) (2^j)
    have hBound : 2^(j*2^j)*2^dyadicFactorialExponent j ≤ (2^j-1+2^j).factorial :=
      (Nat.mul_le_mul_left _ ih).trans hFactor
    have he : 2^(j+1)-1 = 2^j-1+2^j := by rw [pow_succ']; omega
    rw [he]
    simpa only [dyadicFactorialExponent, pow_add, Nat.mul_comm] using hBound

set_option exponentiation.threshold 16384 in
/-- A stronger finite factorial reserve, obtained by keeping every dyadic
range of factors instead of just the last range. -/
theorem factorial_room_32_dyadic : 2^8204 ≤ ((32:ℕ)^2).factorial := by
  have h := dyadic_factorial_bound 10
  change (2:ℕ)^8194 ≤ (1023:ℕ).factorial at h
  have hp : (2:ℕ)^8204 = 1024*(2:ℕ)^8194 := by
    rw [show (8204:ℕ) = 10+8194 by decide, pow_add, show (2:ℕ)^10 = 1024 by decide]
  have hf : ((32:ℕ)^2).factorial = 1024*(1023:ℕ).factorial := by
    rw [show (32:ℕ)^2 = 1023+1 by decide, Nat.factorial_succ]
  rw [hp, hf]
  exact Nat.mul_le_mul_left _ h

set_option exponentiation.threshold 16384 in
theorem padded_three_block_dyadic_sparsity (x : BitString (2^32)) (P : Finset (Fin (2^32)))
    (hP : P.card ≤ 768) :
    (acceptingTables fun y => mcspSquare 32 (substitute (pinAt x P) y)).card ≤ 2^20236 := by
  have h := padded_sparsity_of_factorial (b := 7436) x P (by decide)
    ((Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show P.card+7436 ≤ 8204 by omega)).trans
      factorial_room_32_dyadic)
  rwa [show descriptionBitBound 32 - 7436 = 20236 by decide] at h

/-- The improved unconditional finite bound from counting, independent
of how many first exits have a raw-pair seed. -/
theorem mcspSquare_32_dyadic_forest_floor :
    8620572811 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := padded_sparsity_of_factorial (m := 32) (b := 8204) (fun _ => false) ∅
    (by decide) (by rw [Finset.card_empty, Nat.zero_add]; exact factorial_room_32_dyadic)
  have he : (fun y => mcspSquare 32 (substitute (pinAt (fun _ => false) ∅) y)) = mcspSquare 32 := by
    funext y
    congr 1
  rw [he, show descriptionBitBound 32 - 8204 = 19468 by decide] at h
  have hForest := quad_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding h
    (fun a b c d => mcspSquare_accepts_quad 32 (by decide) a b c d)
  change 280*(2*4294967296)+2*4294967296 ≤
    280*(complexity interpretation (single (mcspSquare 32))+2*19468+1)+17*19468 at hForest
  omega

/-- The arity-32 certificate can choose the block signs and add one
distinct exit for each raw-pair block. -/
theorem three_block_rawPair_bound_32
    (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32)))
    (E : Finset (BitString 24)) (hE : E.card = 3)
    (hSep : SeparatedBy (extendedTags (a := 24) (d := 8) c.program) E)
    (hCover : blocks (d := 8) E ⊆ needInputs c.program (c.outputs 0) false) :
    8620571616 + (rawPairBlocks (a := 24) (d := 8) c.program E).card ≤ c.size := by
  let P := blocks (d := 8) E
  have hP : P.card = 768 := by
    rw [show P = blocks (d := 8) E from rfl, card_blocks, hE]
    decide
  have h0 : cornerValue c.program false (c.outputs 0) = true :=
    (congrFun (hc _) 0).trans (mcspSquare_constant_table 32 (by decide) false)
  have h1 : cornerValue c.program true (c.outputs 0) = true :=
    (congrFun (hc _) 0).trans (mcspSquare_constant_table 32 (by decide) true)
  have hRead (i : Fin (2^32)) (hi : i ∈ P) : ∃ j : Fin c.size, ∃ q, (c.program.lines j).wires q = .input i := by
    obtain ⟨j, _, q, hq⟩ := need_input_has_reader h0 h1 (hCover hi)
    exact ⟨j, q, hq⟩
  have hQ (x : BitString (2^32)) (a : BitString 32) (b : Bool) (u v : BitString 32) :
      mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 (quad a b u v))) = true := by
    apply accepted_after_blocks_pin (a := 24) (k := 2) (l := 6)
    have hCost := QuadraticPinning.complexity_quad_shared_le a b u v
    rw [hE]
    norm_num [lookupBankCost] at hCost ⊢
    omega
  have h := exact_mcsp_rawPair_block_lower (a := 24) (d := 8) (B := 20236) c hc hMin
    (by decide) (by decide) (by decide) E hSep hRead
    (fun x => padded_three_block_dyadic_sparsity x P hP.le) hQ
  rw [hE] at h
  norm_num at h
  omega

end Counting

#print axioms choose_pins_for_rawPair_exits
#print axioms rawPair_blocks_force_extra
#print axioms exact_mcsp_many_rawPair_blocks
#print axioms rawPair_control_two_exits
#print axioms factorial_room_32_dyadic
#print axioms mcspSquare_32_dyadic_forest_floor
#print axioms three_block_rawPair_bound_32

end PvsNP.Frontier.ConstantBlockExits
