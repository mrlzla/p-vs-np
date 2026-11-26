module

public import MCSPForestAbsorptionRank
public import MCSPAdjacentBlockRepair

/-! Choose absorbing pins from the clean forest of the original exact recognizer. -/

@[expose] public section

namespace PvsNP.Frontier.MinimumForestAbsorption

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest ForestBlockPinning
open MultiBlockPinning QuadraticForest ForestPinning JointSparseCompletion
open SuperTwoN AdjacentBlockRepair DownstreamBlockPinning RestrictionCharges
open ForestTraceQuotient ForestAbsorptionRank NestedFaces FreshCharges
open scoped Classical BigOperators

private theorem grounded_roots_near_floor (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hSize : c.size ≤ 8630810218) :
    3432426412 ≤ (groundedOrRoots c.program (c.outputs 0)).card +
      (groundedAndRoots c.program (c.outputs 0)).card := by
  let p := c.program
  let root := c.outputs 0
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  obtain ⟨x, P, hP, hMask, hx⟩ := exists_reindexed_quad_forest_mask_grounded
    (BitString.equivFin 32).symm.toEmbedding c hc (mcspSquare_accepts_quad 32 (by decide))
  have hAccept (y : BitString (2^32)) (hy : ∀ i ∈ P ∪ stopInputs p root, y i = x i) :
      mcspSquare 32 y = true := by
    have he := hMask.trace_eq hc0 hc1 (fun _ _ => rfl)
      (fun i hi => hy i (Finset.mem_union_left _ hi))
      (fun _ hk => Or.inl fun a i ha => hy i (Finset.mem_union_right _ (stopInput_mem_of_wire hk a ha)))
    exact (congrFun (hc y) 0).symm.trans (he.trans ((congrFun (hc x) 0).trans hx))
  have hMasked := card_masked_le mcsp32_tight_sparsity x _ hAccept
  have hUnion := Finset.card_union_le P (stopInputs p root)
  have hBudget := card_stopInputs_and_roots_le_ports c hc mcsp32_tight_sparsity h0 h1
  have hN0 := card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity false h0
  have hN1 := card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity true h1
  have hAcct := needInputs_add_slack_eq p root hc0 hc1
  have hOR : (groundedOrRoots p root).card ≤ (ORRoot p root).card := Finset.card_filter_le _ _
  have hAND : (groundedAndRoots p root).card ≤ (ANDRoot p root).card := Finset.card_filter_le _ _
  dsimp only [p, root] at hUnion hMasked hAcct hOR hAND
  norm_num at hMasked hN0 hN1
  omega

private theorem select_dense_covered_block {a d B t : ℕ} (T S : Finset (Fin (2^(a+d))))
    (ht : 0 < t) (hT : t * 2^a + B * 2^d < T.card) (hS : 2^(a+d) ≤ S.card + B) :
    ∃ q : BitString a, block (d := d) q ⊆ S ∧
      t ≤ (T ∩ block (d := d) q).card := by
  let head : Fin (2^(a+d)) → BitString a := tag (d := d)
  let bad := ((Finset.univ : Finset _) \ S).image head
  let good := T \ blocks (d := d) bad
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [Finset.card_univ, Fintype.card_fin] at hMiss
  have hBad : bad.card ≤ B := Finset.card_image_le.trans (by omega)
  have hBlockBad := card_blocks (d := d) bad
  have hPart := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left (s₁ := T) (s₂ := blocks (d := d) bad))
  have he : T \ (T ∩ blocks (d := d) bad) = good := by
    ext i
    by_cases hi : i ∈ T <;> simp [good, hi]
  rw [he] at hPart
  have hInter := Finset.card_le_card
    (Finset.inter_subset_right (s₁ := T) (s₂ := blocks (d := d) bad))
  have hMany : t * 2^a < good.card := by
    change good.card + _ = _ at hPart
    have hUpper := Nat.mul_le_mul_right (2^d) hBad
    omega
  have hSum : (∑ q : BitString a, (good.filter fun i => head i = q).card) = good.card := by
    simpa only [Finset.mem_univ, Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter good (Finset.univ : Finset (BitString a)) head
  obtain ⟨q, hq⟩ : ∃ q : BitString a, t ≤ (good.filter fun i => head i = q).card := by
    by_contra! hn
    have hLe : (∑ q : BitString a, (good.filter fun i => head i = q).card) ≤
        ∑ _q : BitString a, t := Finset.sum_le_sum fun q _ => (hn q).le
    rw [hSum, Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, Nat.mul_comm] at hLe
    omega
  have hNon : (good.filter fun i => head i = q).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hNon
  have hGood := (Finset.mem_filter.mp hi).1
  have hTag := (Finset.mem_filter.mp hi).2
  have hqGood : q ∉ bad := fun h => (Finset.mem_sdiff.mp hGood).2
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show head i ∈ bad from hTag.symm ▸ h⟩)
  refine ⟨q, ?_, hq.trans (Finset.card_le_card ?_)⟩
  · intro j hj
    by_contra hn
    exact hqGood (Finset.mem_image.mpr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩,
      (Finset.mem_filter.mp hj).2⟩)
  · intro j hj
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp hj).1).1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩⟩

private noncomputable def leavesFor {n g : ℕ} (p : Program signature n g) (root : Wire n g)
    (b : Bool) (r : Fin g) := if b then orInputs p root r else andInputs p root r

private theorem leavesFor_sound {n g : ℕ} (p : Program signature n g) (root : Wire n g)
    (b : Bool) (r : Fin g) (i : Fin n) (hi : i ∈ leavesFor p root b r)
    (y : BitString n) (hy : y i = b) : p.trace interpretation y (.gate r) = b := by
  cases b
  · exact andInputs_sound hi y hy
  · exact orInputs_sound hi y hy

/-- In an exact circuit within 10,000 gates of the direct-reader bound, one fully covered repairable block
has up to 400 distinct seeds for distinct original clean roots, all of the same polarity. -/
theorem covered_absorbing_roots (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hSize : c.size ≤ 8630810218)
    (t : ℕ) (ht : t ≤ 400) :
    ∃ (q : BitString 22) (Q : Finset (Fin (2^32))) (gate : Q ↪ Fin c.size) (b : Bool),
      Q.card = t ∧ Q ⊆ block (d := 10) q ∧
      block (d := 10) q ⊆ needInputs c.program (c.outputs 0) false ∧
      (∀ i : Q, gate i ∈ cleanGates c.program (c.outputs 0)) ∧
      ∀ (x : BitString (2^32)) (i : Q), x i = b →
        restrictedWire c.program (pinAt x (block (d := 10) q)) (.gate (gate i)) = fun _ => b := by
  let p := c.program
  let root := c.outputs 0
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hRoots : 3432426412 ≤ (groundedOrRoots p root).card + (groundedAndRoots p root).card :=
    grounded_roots_near_floor c hc hSize
  let roots (b : Bool) := if b then groundedOrRoots p root else groundedAndRoots p root
  let leaves := leavesFor p root
  obtain ⟨b,hb⟩ : ∃ b : Bool, 1716213206 ≤ (roots b).card := by
    by_cases h : 1716213206 ≤ (groundedOrRoots p root).card
    · exact ⟨true,h⟩
    · exact ⟨false, by change 1716213206 ≤ (groundedAndRoots p root).card; omega⟩
  have hNon (r : roots b) : ∃ i, i ∈ leaves b r := by
    have hr := r.property
    cases b
    · exact (Finset.mem_filter.mp (show r.val ∈ groundedAndRoots p root from hr)).2
    · exact (Finset.mem_filter.mp (show r.val ∈ groundedOrRoots p root from hr)).2
  choose leaf hLeaf using hNon
  have hInj : Function.Injective leaf := by
    intro r s he
    by_contra hn
    have hne : r.val ≠ s.val := fun h => hn (Subtype.ext h)
    have hd : Disjoint (leaves b r) (leaves b s) := by
      cases b
      · exact andInputs_disjoint hc1 hne
      · exact orInputs_disjoint hc0 hne
    exact Finset.disjoint_left.mp hd (hLeaf r) (he.symm ▸ hLeaf s)
  let T := (Finset.univ : Finset (roots b)).image leaf
  have hT : T.card = (roots b).card := by
    rw [show T = Finset.univ.image leaf from rfl, Finset.card_image_of_injective _ hInj,
      Finset.card_univ, Fintype.card_coe]
  have hNeed := card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity false h0
  have hDensity : 400 * 2^22 + 18903 * 2^10 < T.card :=
    (by decide : 400 * 2^22 + 18903 * 2^10 < 1716213206).trans_le (hT.symm ▸ hb)
  obtain ⟨q, hCover, hDense⟩ := select_dense_covered_block (a := 22) (d := 10)
    T (needInputs p root false) (by decide) hDensity hNeed
  obtain ⟨Q, hQ, hCard⟩ := Finset.exists_subset_card_eq (ht.trans hDense)
  have hSub := hQ.trans Finset.inter_subset_right
  have hPre (i : Q) : ∃ r : roots b, leaf r = i :=
    let ⟨r, _, hr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hQ i.property)).1
    ⟨r, hr⟩
  choose pick hPick using hPre
  let gate : Q ↪ Fin c.size := ⟨fun i => (pick i).val, fun i j hij => by
    apply Subtype.ext
    rw [← hPick i, ← hPick j, Subtype.ext hij]⟩
  refine ⟨q, Q, gate, b, hCard, hSub, hCover, ?_, ?_⟩
  · intro i
    have hr := (pick i).property
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases b
    · exact Or.inr ⟨_, ANDMember.self (Finset.mem_filter.mp
        (show (pick i).val ∈ groundedAndRoots p root from hr)).1⟩
    · exact Or.inl ⟨_, ORMember.self (Finset.mem_filter.mp
        (show (pick i).val ∈ groundedOrRoots p root from hr)).1⟩
  · intro x i hx
    have hi : i.val ∈ leaves b (pick i) := hPick i ▸ hLeaf (pick i)
    funext z
    let y := substitute (pinAt x (block (d := 10) q)) z
    have hy : y i.val = b := by
      change substitute (pinAt x (block (d := 10) q)) z i.val = b
      apply substitute_inr
      simp [pinAt, hSub i.property, hx]
    exact leavesFor_sound p root b (pick i).val i.val hi y hy

private theorem wire_port_budget {n g : ℕ} (p : Program signature n g)
    (W : Finset (Wire n g)) (J : Finset (Fin g))
    (h : ∀ w ∈ W, ∃ j ∈ J, ∃ a, (p.lines j).wires a = w) :
    W.card ≤ 2 * J.card := by
  let ports := J.sigma (fun j => (Finset.univ : Finset (Fin (signature.Arity (p.lines j).op))))
  have hRecord (w : W) : ∃ z ∈ ports, (p.lines z.1).wires z.2 = w.val := by
    obtain ⟨j,hj,a,ha⟩ := h w w.property
    exact ⟨⟨j,a⟩,Finset.mem_sigma.mpr ⟨hj,Finset.mem_univ _⟩,ha⟩
  let record (w : W) : ports := ⟨(hRecord w).choose, (hRecord w).choose_spec.1⟩
  have hInj : Function.Injective record := by
    intro u v he
    apply Subtype.ext
    exact (hRecord u).choose_spec.2.symm.trans
      ((congrArg (fun z : ports => (p.lines z.val.1).wires z.val.2) he).trans (hRecord v).choose_spec.2)
  have hCard := Fintype.card_le_of_injective record hInj
  simp only [Fintype.card_coe] at hCard
  refine hCard.trans ?_
  rw [show ports = J.sigma _ from rfl, Finset.card_sigma]
  calc
    _ ≤ ∑ _j ∈ J, (2 : ℕ) := Finset.sum_le_sum fun j _ => by
      simpa using (Program.fanInAtMost_iff.mp p.fanInAtMost_two j)
    _ = _ := by simp [Nat.mul_comm]

private theorem live_gate_has_port {n g : ℕ} (p : Program signature n g) (root : Wire n g)
    (hFresh : fresh p Sum.inl = Finset.univ) {j : Fin g}
    (hLive : ResidualLive p Sum.inl root j) (hj : .gate j ≠ root) :
    ∃ u : Fin g, ∃ a, (p.lines u).wires a = .gate j := by
  cases hLive with
  | output he => exact (hj (original_represents_gate hFresh he).symm).elim
  | argument _ a he => exact ⟨_, a, original_represents_gate hFresh he⟩

/-- Raw pins and distinct absorbed root wires all take argument ports of
constant readers. Raw and gate wires can share a reader, and its two ports
give the joint cap without counting the gate twice. -/
theorem constant_reader_budget {n g : ℕ} (p : Program signature n g) (root : Wire n g)
    (P : Finset (Fin n)) (R : Finset (Fin g)) (x : BitString n)
    (hFresh : fresh p Sum.inl = Finset.univ) (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ i ∈ P, ∃ j : Fin g, ∃ a, (p.lines j).wires a = .input i)
    (hConst : ∀ j ∈ R, ∃ b : Bool, restrictedWire p (pinAt x P) (.gate j) = fun _ => b) :
    P.card + R.card ≤ 2*(constantReaders p (pinAt x P)).card + 1 := by
  let raw : Finset (Wire n g) := P.image Wire.input
  let roots : Finset (Wire n g) := R.image Wire.gate
  let W := raw ∪ roots.erase root
  have hRaw : raw.card = P.card := Finset.card_image_of_injective _ (fun _ _ h => Wire.input.inj h)
  have hRoots : roots.card = R.card := Finset.card_image_of_injective _ (fun _ _ h => Wire.gate.inj h)
  have hDisj : Disjoint raw (roots.erase root) := Finset.disjoint_left.mpr (by
    intro w hw hr
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hr).2
    cases he)
  have hErase : roots.card ≤ (roots.erase root).card + 1 := by
    by_cases h : root ∈ roots
    · have := Finset.card_erase_add_one h
      omega
    · rw [Finset.erase_eq_of_notMem h]
      omega
  have hW : W.card = raw.card + (roots.erase root).card := Finset.card_union_of_disjoint hDisj
  have hPorts := wire_port_budget p W (constantReaders p (pinAt x P)) (by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨j,a,he⟩ := hRead i hi
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,x i,he ▸ pin_input_constant p x hi⟩,a,he⟩
    · obtain ⟨hne,hr⟩ := Finset.mem_erase.mp h
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨j,a,he⟩ := live_gate_has_port p root hFresh
        (mem_liveFresh_iff.mp (hLive.symm ▸ Finset.mem_univ k)) hne
      obtain ⟨b,hb⟩ := hConst k hk
      exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b,he ▸ hb⟩,a,he⟩)
  omega

set_option maxRecDepth 2500 in
set_option exponentiation.threshold 20000 in
/-- One restriction of a near-minimum exact circuit absorbs at least 200
distinct original clean roots while retaining the quadratic probes and
spending one bit in the sparsity bound. -/
theorem mcsp32_actual_forest_absorption (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hSize : c.size ≤ 8630810218) :
    ∃ (q : BitString 22) (x : BitString (2^32)) (R : Finset (Fin c.size)) (b : Bool),
      block (d := 10) q ⊆ needInputs c.program (c.outputs 0) false ∧
      (let pin := pinAt x (block (d := 10) q)
       let f : BooleanFunction (2^32) := fun z => mcspSquare 32 (substitute pin z)
       (acceptingTables f).card ≤ 2^(18904 : ℕ) ∧ 200 ≤ R.card ∧ R.card ≤ 400 ∧
       R ⊆ cleanGates c.program (c.outputs 0) ∧
       ∀ j ∈ R, restrictedWire c.program pin (.gate j) = fun _ => b) := by
  obtain ⟨q,Q,gate,b,hQ,hSub,hCover,hClean,hForce⟩ := covered_absorbing_roots c hc hSize 400 le_rfl
  obtain ⟨x,hMajor,hSparse⟩ := exists_sparse_majority_completion (mcspSquare 32)
    (block (d := 10) q) Q hSub b
  let A := Q.attach.filter fun i : Q => x i.val = b
  let R := A.image gate
  have hA : A.card = (Q.filter fun i => x i = b).card := by
    rw [← Finset.card_image_of_injective A Subtype.val_injective]
    congr 1
    ext i
    constructor
    · intro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨j.property,(Finset.mem_filter.mp hj).2⟩
    · intro h
      obtain ⟨hi,hb⟩ := Finset.mem_filter.mp h
      exact Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hb⟩,rfl⟩
  have hR : R.card = A.card := Finset.card_image_of_injective _ gate.injective
  have hLower : 200 ≤ R.card := by omega
  have hUpper : R.card ≤ 400 := by
    rw [hR,hA,← hQ]
    exact Finset.card_filter_le _ _
  have hCount : (acceptingTables fun z => mcspSquare 32
      (substitute (pinAt x (block (d := 10) q)) z)).card ≤ 2^(18904 : ℕ) := calc
    _ ≤ 2 * (acceptingTables (mcspSquare 32)).card := hSparse
    _ ≤ 2 * 2^(18903 : ℕ) := Nat.mul_le_mul_left 2 mcsp32_tight_sparsity
    _ = _ := (pow_succ' (2 : ℕ) 18903).symm
  refine ⟨q,x,R,b,hCover,hCount,hLower,hUpper,?_,?_⟩
  · intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact hClean i
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact hForce x i (Finset.mem_filter.mp hi).2

set_option maxRecDepth 2500 in
/-- Constant-reader losses and the restricted forest use disjoint original
gate indices. Absorbing the clean roots adds 98 gates to the port-based block bound. -/
theorem mcsp32_absorbing_block_floor_ports :
    8630800316 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c,hc,hMin⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  rw [← hMin]
  by_cases hSize : c.size ≤ 8630810218
  swap
  · omega
  obtain ⟨q,x,R,b,hCover,hSparse,hCard,_,_,hAbs⟩ := mcsp32_actual_forest_absorption c hc hSize
  let p := c.program
  let root := c.outputs 0
  let P := block (d := 10) q
  let pin := pinAt x P
  let f : BooleanFunction (2^32) := fun z => mcspSquare 32 (substitute pin z)
  have hP : P.card = 1024 := card_block q
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hNon := not_constant_of_sparse (by decide : 18903 < (2 : ℕ)^32) mcsp32_tight_sparsity h0
  have hFresh := minimum_fresh_univ c hc hMin hNon
  have hLive := minimum_live_univ c hc hMin hNon
  have hReaders := constant_reader_budget p root P R x hFresh hLive
    (fun i hi => by
      obtain ⟨j,_,a,ha⟩ := need_input_has_reader hc0 hc1 (hCover hi)
      exact ⟨j,a,ha⟩) (fun j hj => ⟨b,hAbs j hj⟩)
  have hQ (a : BitString 32) (v : Bool) (u w : BitString 32) :
      f (MCSP.truthTable 32 (quad a v u w)) = true :=
    accepted_after_1024_pin q x _ (QuadraticPinning.complexity_quad_shared_le a v u w)
  have hZero : f (fun _ => false) = true := by
    have h := hQ (zeroVec 32) false (zeroVec 32) (zeroVec 32)
    have he : MCSP.truthTable 32 (quad (zeroVec 32) false (zeroVec 32) (zeroVec 32)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  have hSparse' : (acceptingTables f).card ≤ 2^(18904 : ℕ) := hSparse
  have hForest := quad_reindexed_forest_size_ports (BitString.equivFin 32).symm.toEmbedding hSparse' hQ
  have hEq : restrictedWire p pin root = f := restricted_circuit_eq c hc pin
  have hRestNon : ¬ ∃ b, restrictedWire p pin root = fun _ => b := by
    rw [hEq]
    exact not_constant_of_sparse (by decide : 18904 < (2 : ℕ)^32) hSparse' hZero
  have hCombined := original_reader_and_dead_budget p root P x hRestNon
  have hReaderSplit := Finset.card_sdiff_add_card_eq_card (directReaders_subset_constantReaders p P x)
  change (downstreamReaders p P x).card + (directReaders p P).card = (constantReaders p pin).card at hReaderSplit
  change P.card + R.card ≤ 2*(constantReaders p pin).card + 1 at hReaders
  change complexity interpretation (single (restrictedWire p pin root)) + _ + _ + _ ≤ c.size at hCombined
  rw [hEq] at hCombined
  norm_num at hForest
  omega

theorem mcsp32_absorbing_block_floor :
    8620574586 ≤ complexity interpretation (single (mcspSquare 32)) :=
  (by decide : 8620574586 ≤ 8630800316).trans mcsp32_absorbing_block_floor_ports

/-- Counting up to 400 absorbed roots alone leaves too many named forest gates
to obtain a positive lower bound on the quotient rank from this cap. -/
theorem mcsp32_absorption_card_rank_gap (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hSize : c.size ≤ 8630810218)
    (R : Finset (Fin c.size)) (hR : R.card ≤ 400) :
    2^32 - (18904 + (cleanGates c.program (c.outputs 0) \ R).card + 1) = 0 := by
  let p := c.program
  let root := c.outputs 0
  let forest := cleanGates p root
  let stop := StopGate p root
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hForest : forest = Finset.univ \ stop := by
    ext j
    change j ∈ cleanGates p root ↔ j ∈ Finset.univ \ StopGate p root
    simp only [cleanGates,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro (⟨r,hr⟩ | ⟨r,hr⟩) hj
      · exact (stopGate_outside_forest hj).1 r hr
      · exact (stopGate_outside_forest hj).2 r hr
    · intro hj
      rcases non_stop_mem_forest hc0 hc1 hj with ⟨r,_,hr⟩ | ⟨r,_,hr⟩
      · exact Or.inl ⟨r,hr⟩
      · exact Or.inr ⟨r,hr⟩
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ stop)
  rw [← hForest,Finset.card_univ,Fintype.card_fin] at hPart
  have hRemoved := Finset.card_le_card (Finset.inter_subset_right (s₁ := forest) (s₂ := R))
  have hRest := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left (s₁ := forest) (s₂ := R))
  have he : forest \ (forest ∩ R) = forest \ R := by
    ext j
    by_cases hj : j ∈ forest <;> simp [hj]
  rw [he] at hRest
  have h0Size := card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity false h0
  have h1Size := card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity true h1
  have hSlack := needInputs_add_slack_eq p root hc0 hc1
  have hStop : stop.card ≤ 56 * slack p root := card_stopGate_le_56_slack p root hc0 hc1
  have hMin := mcsp32_adjacent_block_floor_ports.trans (complexity_le_of_computes c hc)
  dsimp only [p,root] at hSlack hStop
  change 4294967296 ≤ _ at h0Size h1Size
  change 4294967296 - (18904 + (forest \ R).card + 1) = 0
  omega

/-- Apply the quotient-rank estimate to the actual absorbed roots and an
accepted repaired probe. The cardinality estimate by itself adds zero. -/
theorem mcsp32_absorbing_block_rank (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hSize : c.size ≤ 8630810218) :
    ∃ (q : BitString 22) (x a : BitString (2^32)) (R : Finset (Fin c.size)),
      let p := c.program
      let out := c.outputs 0
      let paid := cleanGates p out
      let pin := pinAt x (block (d := 10) q)
      200 ≤ R.card ∧ R.card ≤ 400 ∧ R ⊆ paid ∧ restrictedWire p pin out a = true ∧
      (acceptingTables (restrictedWire p pin out)).card ≤ 2^(18904 : ℕ) ∧
      paidRank p pin a paid ≤ (paid \ R).card ∧
      2^32 ≤ 18904 + paidRank p pin a paid + remainingRank p pin a paid + 1 ∧
      remainingRank p pin a paid + (paid ∪ constantReaders p pin).card ≤ c.size ∧
      2^32 - (18904 + (paid \ R).card + 1) = 0 := by
  obtain ⟨q,x,R,b,_,hSparse,hCard,hUpper,hSub,hAbs⟩ := mcsp32_actual_forest_absorption c hc hSize
  let f := quad (zeroVec 32) false (zeroVec 32) (zeroVec 32)
  let a := MCSP.truthTable 32 f
  let pin := pinAt x (block (d := 10) q)
  let paid := cleanGates c.program (c.outputs 0)
  have hYes : restrictedWire c.program pin (c.outputs 0) a = true := by
    rw [restricted_circuit_eq c hc pin]
    exact accepted_after_1024_pin q x f (QuadraticPinning.complexity_quad_shared_le ..)
  have hConst j (hj : j ∈ R) : ∃ b : Bool,
      restrictedWire c.program pin (.gate j) = fun _ => b := ⟨b,hAbs j hj⟩
  have hSparse' : (acceptingTables (restrictedWire c.program pin (c.outputs 0))).card ≤
      2^(18904 : ℕ) := by
    rw [restricted_circuit_eq c hc pin]
    exact hSparse
  exact ⟨q,x,a,R,hCard,hUpper,hSub,hYes,hSparse',paidRank_le_unabsorbed c.program pin a paid R hConst,
    remainingRank_lower_of_sparse c.program pin a (c.outputs 0) paid 18904 hYes hSparse',
    remainingRank_with_paid_and_losses c.program pin a paid,
    mcsp32_absorption_card_rank_gap c hc hSize R hUpper⟩

#print axioms covered_absorbing_roots
#print axioms mcsp32_actual_forest_absorption
#print axioms mcsp32_absorbing_block_floor
#print axioms mcsp32_absorbing_block_floor_ports
#print axioms mcsp32_absorbing_block_rank

end PvsNP.Frontier.MinimumForestAbsorption
