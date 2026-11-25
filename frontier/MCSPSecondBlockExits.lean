module

public import MCSPIndependentBlockPinning

/-! Follow a matched exit through one more reader layer. A constant exit
forces another deletion, while an alias may stop the propagation. -/

@[expose] public section

namespace PvsNP.Frontier.SecondBlockExits

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates ForestBlockPinning ForestPinning RestrictionCharges
open FreshCharges NestedFaces QuadraticForest DownstreamBlockPinning
open IndependentBlockPinning MultiBlockPinning
open scoped Classical BigOperators

section Footprints

variable {a d g : ℕ}

/-- Include the raw block tags at distance at most two predecessor gates. -/
noncomputable def extendedTags (p : Program signature (2^(a+d)) g) (j : Fin g) :
    Finset (BitString a) :=
  nearbyTags p j ∪ Finset.univ.biUnion (fun i =>
    match (p.lines j).wires i with
    | .input _ => ∅
    | .gate u => nearbyTags p u)

theorem nearbyTags_subset_extended (p : Program signature (2^(a+d)) g) (j : Fin g) :
    nearbyTags p j ⊆ extendedTags p j := Finset.subset_union_left

theorem nearbyTags_subset_extended_of_wire (p : Program signature (2^(a+d)) g) {j u : Fin g}
    {b : Fin (signature.Arity (p.lines j).op)} (h : (p.lines j).wires b = .gate u) :
    nearbyTags p u ⊆ extendedTags p j := by
  intro s hs
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, by simpa only [h] using hs⟩

theorem card_extendedTags_le (p : Program signature (2^(a+d)) g) (j : Fin g) :
    (extendedTags p j).card ≤ 18 := by
  let f (b : Fin (signature.Arity (p.lines j).op)) :=
    match (p.lines j).wires b with | .input _ => ∅ | .gate u => nearbyTags p u
  have hEach (b) : (f b).card ≤ 6 := by
    cases he : (p.lines j).wires b with
    | input i => simp [f, he]
    | gate u => simpa only [f, he] using card_nearbyTags_le p u
  have hSum : (Finset.univ.biUnion f).card ≤ 12 := calc
    _ ≤ ∑ b, (f b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : Fin (signature.Arity (p.lines j).op), 6 :=
      Finset.sum_le_sum (fun b _ => hEach b)
    _ ≤ _ := by
      simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right 6 (Program.fanInAtMost_iff.mp p.fanInAtMost_two j)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (card_nearbyTags_le p j) hSum)

/-- The stronger separation is obtainable using the same greedy selection. -/
theorem exists_extended_separated_blocks (p : Program signature (2^(a+d)) g)
    (S : Finset (Fin (2^(a+d)))) (r K H : ℕ)
    (hHeavy : 18*g < K*(H+1))
    (hRoom : r*(18*K+1) + H + ((Finset.univ : Finset _) \ S).card ≤ 2^a) :
    ∃ E : Finset (BitString a), E.card = r ∧ SeparatedBy (extendedTags p) E ∧
      blocks (d := d) E ⊆ S :=
  exists_separated_covered_blocks_by (extendedTags p) (card_extendedTags_le p) S r K H hHeavy hRoom

/-- The stronger footprint budget still allows three fully covered
blocks at arity 32 in the relevant circuit-size range. -/
theorem exists_three_extended_blocks_32 {g : ℕ} (p : Program signature (2^32) g)
    (S : Finset (Fin (2^32))) (hg : g ≤ 3*2^32)
    (hS : ((Finset.univ : Finset _) \ S).card ≤ 27672) :
    ∃ E : Finset (BitString 24), E.card = 3 ∧
      SeparatedBy (extendedTags (a := 24) (d := 8) p) E ∧ blocks (d := 8) E ⊆ S := by
  apply exists_extended_separated_blocks (a := 24) (d := 8) p S 3 32768 8388608
  · norm_num at hg ⊢
    omega
  · norm_num
    omega

end Footprints

section Matching

variable {a d g : ℕ}

/-- A constant matched exit has a later downstream reader. If an immediate
reader is direct, its other argument is pinned and the constant keeps
propagating until it reaches a nondirect reader. -/
theorem later_exit_of_constant_exit (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (hSep : SeparatedBy (extendedTags p) E) (hFresh : fresh p Sum.inl = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b)
    (s : E) (j : Fin g) (hLive : ResidualLive p Sum.inl root j)
    (hTag : s.val ∈ nearbyTags p j)
    (hConst : ∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) (.gate j) = fun _ => b) :
    ∃ u ∈ downstreamReaders p (blocks (d := d) E) x, j < u ∧ s.val ∈ extendedTags p u := by
  let P := blocks (d := d) E
  let ρ := pinAt x P
  by_contra hNo
  have hAbsent {u : Fin g} (h : ResidualLive p Sum.inl root u) :
      (u = j ∨ (j < u ∧ s.val ∈ readerTags p u)) →
        ¬∃ b : Bool, restrictedWire p ρ (.gate u) = fun _ => b := by
    induction h with
    | @output u hRep =>
      intro _
      have he := original_represents_gate hFresh hRep
      simpa only [he] using hNon
    | @argument u v hU i hRep ih =>
      intro hv
      rintro ⟨b, hb⟩
      have he := original_represents_gate hFresh hRep
      have hlt : j < u := (hv.elim (fun h => h.symm.le) (fun h => h.1.le)).trans_lt
        (p.lt_of_lines_wires_eq_gate u i v he)
      have hsU : s.val ∈ extendedTags p u := by
        rcases hv with rfl | ⟨_, hv⟩
        · exact nearbyTags_subset_extended_of_wire p he hTag
        · exact nearbyTags_subset_extended p u (readerTags_subset_nearby_of_wire p he hv)
      have hArg : restrictedWire p ρ ((p.lines u).wires i) = fun _ => b := he ▸ hb
      have hDirect : u ∈ directReaders p P := by
        by_contra h
        exact hNo ⟨u, Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, b, hArg⟩, h⟩, hlt, hsU⟩
      obtain ⟨z, hz, k, hk⟩ := (Finset.mem_filter.mp hDirect).2
      have hzE : tag z ∈ E := (Finset.mem_filter.mp hz).2
      have hzTag : tag z ∈ readerTags p u := mem_readerTags.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, k, hk⟩)
      have hzEq : s.val = tag z := by
        by_contra hn
        exact hSep s.val s.property _ hzE hn u hsU
          (nearbyTags_subset_extended p u (readerTags_subset_nearby p u hzTag))
      have hn : i ≠ k := by
        intro e
        rw [e, hk] at he
        cases he
      exact ih (Or.inr ⟨hlt, hzEq ▸ hzTag⟩) (constant_of_two_arguments p ρ u i k hn b (x z)
        hArg (hk ▸ pin_input_constant p x hz))
  exact hAbsent hLive (Or.inl rfl) hConst

/-- The blocks whose matched first exit is constant after the joint pin. -/
noncomputable def constantExitBlocks (p : Program signature (2^(a+d)) g)
    (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (first : E ↪ downstreamReaders p (blocks (d := d) E) x) : Finset E :=
  Finset.univ.filter fun s => ∃ b : Bool,
    restrictedWire p (pinAt x (blocks (d := d) E)) (.gate (first s).val) = fun _ => b

/-- All first exits and one additional exit for each constant first exit
can be charged simultaneously, without sharing any original indices. -/
theorem first_and_second_exits (p : Program signature (2^(a+d)) g) (root : Wire (2^(a+d)) g)
    (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (first : E ↪ downstreamReaders p (blocks (d := d) E) x)
    (hFirst : ∀ s : E, s.val ∈ nearbyTags p (first s).val)
    (hSep : SeparatedBy (extendedTags p) E)
    (hFresh : fresh p Sum.inl = Finset.univ) (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    E.card + (constantExitBlocks p E x first).card ≤
      (downstreamReaders p (blocks (d := d) E) x).card := by
  let C := constantExitBlocks p E x first
  let D := downstreamReaders p (blocks (d := d) E) x
  have hex (s : C) : ∃ j ∈ D, (first s.val).val < j ∧ s.val.val ∈ extendedTags p j := by
    apply later_exit_of_constant_exit p root E x hSep hFresh hNon s.val (first s.val).val
      (mem_liveFresh_iff.mp (hLive.symm ▸ Finset.mem_univ _)) (hFirst s.val)
    exact (Finset.mem_filter.mp s.property).2
  choose second hMem hSecond using hex
  let into : E ⊕ C → D := Sum.elim first (fun s => ⟨second s, hMem s⟩)
  have hDistinct (u v : E) {j : Fin g}
      (hu : u.val ∈ extendedTags p j) (hv : v.val ∈ extendedTags p j) : u = v := by
    apply Subtype.ext
    by_contra hn
    exact hSep u.val u.property v.val v.property hn j hu hv
  have hNoCross (u : E) (v : C) : first u ≠ (⟨second v, hMem v⟩ : D) := by
    intro he
    have hEq : (first u).val = second v := congrArg Subtype.val he
    have ht := nearbyTags_subset_extended p (first u).val (hFirst u)
    have huv := hDistinct u v.val (hEq ▸ ht) (hSecond v).2
    have hlt := (hSecond v).1
    rw [← huv, hEq] at hlt
    exact (lt_irrefl _ hlt)
  have hInj : Function.Injective into := by
    intro u v he
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (first.injective he)
      | inr v => exact (hNoCross u v he).elim
    | inr u =>
      cases v with
      | inl v => exact (hNoCross v u he.symm).elim
      | inr v =>
        have hEq : second u = second v := congrArg Subtype.val he
        have huv := hDistinct u.val v.val (hEq ▸ (hSecond u).2) (hSecond v).2
        exact congrArg Sum.inr (Subtype.ext huv)
  simpa only [Fintype.card_sum, Fintype.card_coe] using Fintype.card_le_of_injective into hInj

/-- If every matched first exit is constant, the separated blocks
each account for two distinct original downstream gates. -/
theorem two_exits_per_constant_block (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (first : E ↪ downstreamReaders p (blocks (d := d) E) x)
    (hFirst : ∀ s : E, s.val ∈ nearbyTags p (first s).val)
    (hSep : SeparatedBy (extendedTags p) E)
    (hFresh : fresh p Sum.inl = Finset.univ) (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b)
    (hConst : ∀ s : E, ∃ b : Bool,
      restrictedWire p (pinAt x (blocks (d := d) E)) (.gate (first s).val) = fun _ => b) :
    2*E.card ≤ (downstreamReaders p (blocks (d := d) E) x).card := by
  have he : constantExitBlocks p E x first = Finset.univ := Finset.eq_univ_of_forall fun s =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hConst s⟩
  have h := first_and_second_exits p root E x first hFirst hSep hFresh hLive hNon
  rw [he, Finset.card_univ, Fintype.card_coe] at h
  omega

/-- If the first matching already uses every downstream reader, each
matched exit is an alias in the restriction. -/
theorem no_second_exit_implies_alias (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (first : E ↪ downstreamReaders p (blocks (d := d) E) x)
    (hFirst : ∀ s : E, s.val ∈ nearbyTags p (first s).val)
    (hSep : SeparatedBy (extendedTags p) E)
    (hFresh : fresh p Sum.inl = Finset.univ) (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b)
    (hSize : (downstreamReaders p (blocks (d := d) E) x).card = E.card)
    (s : E) :
    let ρ := pinAt x (blocks (d := d) E)
    let j := (first s).val
    (∃ i, restrictedWire p ρ (.gate j) = projection i) ∨
      ∃ u : Fin g, u < j ∧ restrictedWire p ρ (.gate j) = restrictedWire p ρ (.gate u) := by
  have h := first_and_second_exits p root E x first hFirst hSep hFresh hLive hNon
  have hEmpty : (constantExitBlocks p E x first).card = 0 := by omega
  have hn : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) (.gate (first s).val) =
      fun _ => b := by
    intro hC
    have hm : s ∈ constantExitBlocks p E x first := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩
    rw [Finset.card_eq_zero.mp hEmpty] at hm
    exact Finset.notMem_empty _ hm
  obtain ⟨b, v, hv⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (first s).property).1).2
  exact (disclosed_of_constant_argument p (pinAt x (blocks (d := d) E)) (first s).val b v hv).resolve_left hn

/-- Add the second exits once, alongside the direct-reader and dead gates. -/
theorem two_layer_residual_budget (p : Program signature (2^(a+d)) g) (root : Wire (2^(a+d)) g)
    (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (first : E ↪ downstreamReaders p (blocks (d := d) E) x)
    (hFirst : ∀ s : E, s.val ∈ nearbyTags p (first s).val)
    (hSep : SeparatedBy (extendedTags p) E)
    (hFresh : fresh p Sum.inl = Finset.univ) (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    let P := blocks (d := d) E
    complexity interpretation (single (restrictedWire p (pinAt x P) root)) +
      (directReaders p P).card + E.card + (constantExitBlocks p E x first).card +
      (deadFresh p (pinAt x P) root).card ≤ g := by
  have hExit := first_and_second_exits p root E x first hFirst hSep hFresh hLive hNon
  have hBudget := original_reader_and_dead_budget p root (blocks (d := d) E) x hNon
  dsimp only
  omega

end Matching

section MCSP

variable {a d B : ℕ}

/-- The full residual forest inequality can charge the second matching
alongside the direct readers. The improvement is the number of constant
matched exits. -/
theorem preserved_forest_two_layers
    (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+d))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+d))))
    (hd : 1 ≤ d) (hFew : descriptionBitBound (a+d) < 2^(a+d)) (hB : B < 2^(a+d))
    (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (first : E ↪ downstreamReaders c.program (blocks (d := d) E) x)
    (hFirst : ∀ s : E, s.val ∈ nearbyTags c.program (first s).val)
    (hSep : SeparatedBy (extendedTags c.program) E)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin c.size, ∃ k, (c.program.lines j).wires k = .input i)
    (hSparse : (acceptingTables fun y => mcspSquare (a+d)
      (substitute (pinAt x (blocks (d := d) E)) y)).card ≤ 2^B)
    (hQuad : ∀ (u : BitString (a+d)) (b : Bool) (v w : BitString (a+d)),
      mcspSquare (a+d) (substitute (pinAt x (blocks (d := d) E)) (MCSP.truthTable _ (quad u b v w))) =
        true) :
    280*(2*2^(a+d) + E.card*2^(d-1) + E.card + (constantExitBlocks c.program E x first).card) +
      2*2^(a+d) ≤ 280*(c.size+2*B+1) + 17*B := by
  let m := a+d
  let P := blocks (d := d) E
  let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
  have hInitNon := not_constant_of_sparse hFew (card_accepting_mcspSquare_le m)
    (mcspSquare_constant_table m (by omega) false)
  have hFresh := minimum_fresh_univ c hc hMin hInitNon
  have hLive := minimum_live_univ c hc hMin hInitNon
  have hYes : f (fun _ => false) = true := by
    have h := hQuad (zeroVec m) false (zeroVec m) (zeroVec m)
    have he : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, SuperTwoN.affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  have hEq : restrictedWire c.program (pinAt x P) (c.outputs 0) = f :=
    restricted_circuit_eq c hc (pinAt x P)
  have hNon : ¬∃ b : Bool, restrictedWire c.program (pinAt x P) (c.outputs 0) = fun _ => b := by
    rw [hEq]
    exact not_constant_of_sparse hB hSparse hYes
  have hD := directReader_charge_of_coverage c.program P P x (by rfl) hFresh hRead
  have hCard : P.card = 2*(E.card*2^(d-1)) := calc
    _ = E.card*2^d := card_blocks E
    _ = E.card*2^(d-1+1) := by rw [Nat.sub_add_cancel hd]
    _ = _ := by rw [pow_succ']; ring
  rw [hCard] at hD
  have hForest := quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding hSparse hQuad
  have hCost := two_layer_residual_budget c.program (c.outputs 0) E x first hFirst hSep hFresh hLive hNon
  dsimp only at hCost
  rw [hEq] at hCost
  dsimp only [m, P, f] at hD hCost hForest
  omega

/-- The three-block numerical certificate improves by exactly the
number of constant exits included in the second-layer matching. -/
theorem three_block_two_layer_bound_32
    (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32)))
    (E : Finset (BitString 24)) (hE : E.card = 3) (x : BitString (2^32))
    (first : E ↪ downstreamReaders c.program (blocks (d := 8) E) x)
    (hFirst : ∀ s : E, s.val ∈ nearbyTags (a := 24) (d := 8) c.program (first s).val)
    (hSep : SeparatedBy (extendedTags (a := 24) (d := 8) c.program) E)
    (hRead : ∀ i ∈ blocks (d := 8) E, ∃ j : Fin c.size, ∃ k, (c.program.lines j).wires k = .input i) :
    8620564205 + (constantExitBlocks (a := 24) (d := 8) c.program E x first).card ≤ c.size := by
  let P := blocks (d := 8) E
  have hP : P.card = 768 := by
    rw [show P = blocks (d := 8) E from rfl, card_blocks, hE]
    decide
  have hSparse : (acceptingTables fun y => mcspSquare 32 (substitute (pinAt x P) y)).card ≤ 2^23832 := by
    have h := padded_sparsity_of_factorial (b := 3840) x P (by decide) (by
      rw [hP, show (768:ℕ)+3840 = 4608 by decide]
      exact factorial_room_32)
    rwa [show descriptionBitBound 32 - 3840 = 23832 by decide] at h
  have hQ (a : BitString 32) (b : Bool) (u w : BitString 32) :
      mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 (quad a b u w))) = true := by
    apply accepted_after_blocks_pin (a := 24) (k := 2) (l := 6)
    have hCost := QuadraticPinning.complexity_quad_shared_le a b u w
    rw [hE]
    norm_num [lookupBankCost] at hCost ⊢
    omega
  have h := preserved_forest_two_layers (a := 24) (d := 8) c hc hMin
    (by decide) (by decide) (by decide) E x first hFirst hSep hRead hSparse hQ
  rw [hE] at h
  norm_num at h
  omega

end MCSP

section AliasControl

def aliasProgram : Program signature 4 3 :=
  let p0 : Program signature 4 0 := .empty
  let p1 := p0.gate ⟨.or, fun a => if a = 0 then .input 0 else .input 1⟩
  let p2 := p1.gate ⟨.and, fun a => if a = 0 then .gate 0 else .input 2⟩
  p2.gate ⟨.or, fun a => if a = 0 then .gate 1 else .input 3⟩

def aliasCircuit : Circuit signature 4 1 := ⟨aliasProgram, fun _ => .gate 2⟩

def aliasFunction (x : BitString 4) : Bool := ((x 0 || x 1) && x 2) || x 3

theorem alias_circuit_computes : aliasCircuit.Computes interpretation (single aliasFunction) := by
  intro x
  rfl

theorem alias_circuit_minimum :
    aliasCircuit.size = complexity interpretation (single aliasFunction) := by
  have hEss (i : Fin 4) : EssentialAt aliasFunction i := by
    fin_cases i
    · refine ⟨![false,false,true,false], ![true,false,true,false], ?_, by decide⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨![false,false,true,false], ![false,true,true,false], ?_, by decide⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨![true,false,false,false], ![true,false,true,false], ?_, by decide⟩
      intro j hj
      fin_cases j <;> simp_all
    · refine ⟨![false,false,false,false], ![false,false,false,true], ?_, by decide⟩
      intro j hj
      fin_cases j <;> simp_all
  apply le_antisymm _ (complexity_le_of_computes aliasCircuit alias_circuit_computes)
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single aliasFunction)
  rw [← hSize]
  have hRead : WireAccounting.inputs c.program (c.outputs 0) = Finset.univ :=
    Finset.eq_univ_of_forall fun i => WireAccounting.essential_mem_inputs hc (hEss i)
  have hh := WireAccounting.inputs_add_charges_le c.program (c.outputs 0)
  rw [hRead, Finset.card_univ, Fintype.card_fin] at hh
  change 3 ≤ c.size
  omega

def aliasPins : Finset (Fin 4) := {0}

def aliasBlock : Finset (BitString 2) := {tag (a := 2) (d := 0) (0 : Fin 4)}

theorem aliasBlock_pins : blocks (d := 0) aliasBlock = aliasPins := by
  have hSub : aliasPins ⊆ blocks (d := 0) aliasBlock := by
    intro i hi
    have he : i = 0 := Finset.mem_singleton.mp hi
    subst i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩
  apply (Finset.eq_of_subset_of_card_le hSub ?_).symm
  rw [card_blocks]
  decide

theorem alias_block_separated : SeparatedBy (extendedTags (a := 2) (d := 0) aliasProgram) aliasBlock := by
  intro u hu v hv hne
  exact (hne ((Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm)).elim

private theorem alias_not_pinned_const (x : BitString 4) {i : Fin 4} (hi : i ≠ 0) :
    ¬∃ b : Bool, restrictedWire aliasProgram (pinAt x aliasPins) (.input i) = fun _ => b := by
  rintro ⟨b, hb⟩
  have hIn : pinAt x aliasPins i = .inl i := by simp [pinAt, aliasPins, hi]
  have hfalse := congrFun hb (fun _ => false)
  have htrue := congrFun hb (fun _ => true)
  change substitute (pinAt x aliasPins) (fun _ => false) i = b at hfalse
  change substitute (pinAt x aliasPins) (fun _ => true) i = b at htrue
  rw [substitute_inl hIn] at hfalse htrue
  cases (hfalse.trans htrue.symm)

theorem alias_exit_nonconstant (x : BitString 4) :
    ¬∃ b : Bool, restrictedWire aliasProgram (pinAt x aliasPins) (.gate 1) = fun _ => b := by
  rintro ⟨b, h⟩
  have h0 := congrFun h (![false,true,false,false] : BitString 4)
  have h1 := congrFun h (![false,true,true,false] : BitString 4)
  change ((substitute (pinAt x aliasPins) ![false,true,false,false] 0 ||
    substitute (pinAt x aliasPins) ![false,true,false,false] 1) &&
    substitute (pinAt x aliasPins) ![false,true,false,false] 2) = b at h0
  change ((substitute (pinAt x aliasPins) ![false,true,true,false] 0 ||
    substitute (pinAt x aliasPins) ![false,true,true,false] 1) &&
    substitute (pinAt x aliasPins) ![false,true,true,false] 2) = b at h1
  simp [substitute, pinAt, aliasPins] at h0 h1
  cases (h0.symm.trans h1)

theorem alias_residual_nonconstant (x : BitString 4) :
    ¬∃ b : Bool, restrictedWire aliasProgram (pinAt x aliasPins) (.gate 2) = fun _ => b := by
  rintro ⟨b, h⟩
  have h0 := congrFun h (![false,false,false,false] : BitString 4)
  have h1 := congrFun h (![false,false,false,true] : BitString 4)
  change aliasFunction (substitute (pinAt x aliasPins) ![false,false,false,false]) = b at h0
  change aliasFunction (substitute (pinAt x aliasPins) ![false,false,false,true]) = b at h1
  simp [aliasFunction, substitute, pinAt, aliasPins] at h0 h1
  cases (h0.symm.trans h1)

/-- Even a minimum circuit with a nonconstant residual can have only one
downstream deletion for every assignment to a separated block. -/
theorem alias_control_at_most_one (x : BitString 4) :
    (downstreamReaders aliasProgram (blocks (d := 0) aliasBlock) x).card ≤ 1 := by
  rw [aliasBlock_pins]
  have hSub : downstreamReaders aliasProgram aliasPins x ⊆ ({1} : Finset (Fin 3)) := by
    intro j hj
    fin_cases j
    · exact ((Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, 0, Finset.mem_singleton_self _, ⟨0, by decide⟩, rfl⟩)).elim
    · exact Finset.mem_singleton_self _
    · obtain ⟨a, b, hb⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
      have ha := a.isLt
      change a.val < 2 at ha
      have hc : a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ :=
        (show a.val = 0 ∨ a.val = 1 from by omega).imp Fin.ext Fin.ext
      rcases hc with rfl | rfl
      · exact (alias_exit_nonconstant x ⟨b, hb⟩).elim
      · exact (alias_not_pinned_const x (i := 3) (by decide) ⟨b, hb⟩).elim
  exact (Finset.card_le_card hSub).trans (by simp)

/-- The first exit actually disappears in the forcing branch and is an
alias, while its original successor stays outside the downstream losses. -/
theorem alias_control_has_one_when_true :
    (downstreamReaders aliasProgram aliasPins (fun _ => true)).card = 1 ∧
    restrictedWire aliasProgram (pinAt (fun _ => true) aliasPins) (.gate 1) = projection 2 := by
  have hConst : restrictedWire aliasProgram (pinAt (fun _ => true) aliasPins) (.gate 0) =
      fun _ => true := by
    funext x
    change (substitute (pinAt (fun _ => true) aliasPins) x 0 ||
      substitute (pinAt (fun _ => true) aliasPins) x 1) = true
    simp [substitute, pinAt, aliasPins]
  have hMem : (1 : Fin 3) ∈ downstreamReaders aliasProgram aliasPins (fun _ => true) := by
    refine Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨0, by decide⟩, true, hConst⟩, ?_⟩
    intro h
    obtain ⟨i, hi, a, ha⟩ := (Finset.mem_filter.mp h).2
    have he : i = 0 := Finset.mem_singleton.mp hi
    subst i
    have hb := a.isLt
    change a.val < 2 at hb
    have hc : a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ :=
      (show a.val = 0 ∨ a.val = 1 from by omega).imp Fin.ext Fin.ext
    rcases hc with rfl | rfl <;> exact (by decide : ¬ _) ha
  have hUp := alias_control_at_most_one (fun _ => true)
  rw [aliasBlock_pins] at hUp
  refine ⟨le_antisymm hUp (Finset.card_pos.mpr ⟨_, hMem⟩), ?_⟩
  funext x
  change ((substitute (pinAt (fun _ => true) aliasPins) x 0 ||
    substitute (pinAt (fun _ => true) aliasPins) x 1) &&
    substitute (pinAt (fun _ => true) aliasPins) x 2) = x 2
  simp [substitute, pinAt, aliasPins]

private theorem alias_successor_eval (x y : BitString 4) :
    restrictedWire aliasProgram (pinAt x aliasPins) (.gate 2) y =
      (((x 0 || y 1) && y 2) || y 3) := by
  change aliasFunction (substitute (pinAt x aliasPins) y) = _
  simp [aliasFunction, substitute, pinAt, aliasPins]

private theorem alias_earlier_eval (x y : BitString 4) :
    restrictedWire aliasProgram (pinAt x aliasPins) (.gate 0) y = (x 0 || y 1) ∧
    restrictedWire aliasProgram (pinAt x aliasPins) (.gate 1) y = ((x 0 || y 1) && y 2) := by
  change (substitute (pinAt x aliasPins) y 0 || substitute (pinAt x aliasPins) y 1) = _ ∧
    ((substitute (pinAt x aliasPins) y 0 || substitute (pinAt x aliasPins) y 1) &&
      substitute (pinAt x aliasPins) y 2) = _
  simp [substitute, pinAt, aliasPins]

/-- The original reader of the alias remains necessary in the fresh,
live reconstruction for every pin value. -/
theorem alias_successor_stays_live (x : BitString 4) :
    (2 : Fin 3) ∈ liveFresh aliasProgram (pinAt x aliasPins) (.gate 2) := by
  let ρ := pinAt x aliasPins
  apply mem_liveFresh_iff.mpr
  apply ResidualLive.output
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  rintro (hConst | ⟨i, hi⟩ | ⟨j, hj, he⟩)
  · exact alias_residual_nonconstant x hConst
  · fin_cases i
    · have h := congrFun hi (![false,false,false,true] : BitString 4)
      rw [alias_successor_eval] at h
      simp [projection] at h
    · have h := congrFun hi (![false,false,false,true] : BitString 4)
      rw [alias_successor_eval] at h
      simp [projection] at h
    · have h := congrFun hi (![false,false,false,true] : BitString 4)
      rw [alias_successor_eval] at h
      simp [projection] at h
    · have h := congrFun hi (![false,true,true,false] : BitString 4)
      rw [alias_successor_eval] at h
      simp [projection] at h
  · have hj' : j.val < 2 := hj
    have hCases : j = 0 ∨ j = 1 := (show j.val = 0 ∨ j.val = 1 from by omega).imp Fin.ext Fin.ext
    rcases hCases with rfl | rfl
    · have h0 := congrFun he (![false,false,false,false] : BitString 4)
      have h1 := congrFun he (![false,false,false,true] : BitString 4)
      rw [alias_successor_eval, (alias_earlier_eval _ _).1] at h0 h1
      simp at h0 h1
      cases (h0.symm.trans h1)
    · have h := congrFun he (![false,false,false,true] : BitString 4)
      rw [alias_successor_eval, (alias_earlier_eval _ _).2] at h
      simp at h

/-- The counterexample bounds all omitted indices outside direct readers,
including aliases and dead gates, for every pin value. -/
theorem alias_control_all_extra_losses_le_one (x : BitString 4) :
    (((Finset.univ : Finset (Fin 3)) \ liveFresh aliasProgram (pinAt x aliasPins) (.gate 2)) \
      directReaders aliasProgram aliasPins).card ≤ 1 := by
  have hSub : ((Finset.univ : Finset (Fin 3)) \ liveFresh aliasProgram (pinAt x aliasPins) (.gate 2)) \
      directReaders aliasProgram aliasPins ⊆ {1} := by
    intro j hj
    fin_cases j
    · exact ((Finset.mem_sdiff.mp hj).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, 0, Finset.mem_singleton_self _, ⟨0, by decide⟩, rfl⟩)).elim
    · exact Finset.mem_singleton_self _
    · exact ((Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).2 (alias_successor_stays_live x)).elim
  exact (Finset.card_le_card hSub).trans (by simp)

end AliasControl

#print axioms exists_extended_separated_blocks
#print axioms later_exit_of_constant_exit
#print axioms first_and_second_exits
#print axioms two_layer_residual_budget
#print axioms preserved_forest_two_layers
#print axioms three_block_two_layer_bound_32
#print axioms alias_circuit_minimum
#print axioms alias_control_at_most_one
#print axioms alias_control_has_one_when_true
#print axioms alias_control_all_extra_losses_le_one
#print axioms two_exits_per_constant_block
#print axioms no_second_exit_implies_alias

end PvsNP.Frontier.SecondBlockExits
