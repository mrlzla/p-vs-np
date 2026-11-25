module

public import MCSPMultiBlockPinning
public import MCSPQuarterDeadFrontier

/-! Propagate constants from jointly pinned addresses and charge the original
indices, separately from direct readers and fresh but dead indices. -/

@[expose] public section

namespace PvsNP.Frontier.DownstreamBlockPinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest
open RestrictionCharges FreshCharges ForestPinning ForestBlockPinning
open NestedFaces MinorityResidual QuadraticForest QuadraticPinning SuperTwoN
open MultiBlockPinning
open scoped Classical BigOperators

section Sparsity

variable {n : ℕ}

/-- Padding can increase the acceptance count by at most one factor of two
per pinned position, for any choice of the fixed values. -/
theorem card_accepting_pin_le (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) :
    (acceptingTables fun y => f (substitute (pinAt x P) y)).card ≤
      2^P.card * (acceptingTables f).card := by
  induction P using Finset.induction_on with
  | empty =>
    have he : (fun y => f (substitute (pinAt x ∅) y)) = f := by
      funext y
      congr 1
    rw [he]
    simp
  | @insert i P hi ih =>
    let g : BooleanFunction n := fun y => f (substitute (pinAt x P) y)
    have hId : Function.update x i (x i) = x := Function.update_eq_self i x
    have hCompose := PairSeparation.branchPin_compose x P i (x i) hi
    simp only [PairSeparation.branchPin, hId] at hCompose
    have hOne (y : BitString n) : substitute (pinAt x {i}) y = Function.update y i (x i) := by
      funext j
      by_cases hj : j = i <;> simp [substitute, pinAt, hj]
    have he : (fun y => f (substitute (pinAt x (insert i P)) y)) =
        fun y => g (Function.update y i (x i)) := by
      funext y
      rw [hCompose, substitute_compose, hOne]
    rw [he, card_pinned_branch, Finset.card_insert_of_notMem hi, pow_succ']
    calc
      _ ≤ 2*(acceptingTables g).card :=
        Nat.mul_le_mul_left _ (Finset.card_filter_le _ _)
      _ ≤ 2*(2^P.card*(acceptingTables f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := Nat.mul_assoc .. |>.symm

theorem pow_le_factorial_of_large_factors {q k : ℕ} (hk : 2^k ≤ q+1) (d : ℕ) :
    2^(k*d) ≤ (q+d).factorial := by
  induction d with
  | zero =>
    have h := Nat.factorial_pos q
    simp only [Nat.mul_zero, pow_zero, Nat.add_zero]
    omega
  | succ d ih =>
    rw [Nat.mul_succ, pow_add, ← Nat.add_assoc, Nat.factorial_succ]
    rw [Nat.mul_comm (2^(k*d))]
    exact Nat.mul_le_mul (hk.trans (by omega)) ih

/-- Keep the unused factorial in the original description count. It pays
for a prescribed joint pin assignment and may leave a smaller description bound. -/
theorem padded_sparsity_of_factorial {m b : ℕ} (x : BitString (2^m))
    (P : Finset (Fin (2^m))) (hb : b ≤ descriptionBitBound m)
    (hRoom : 2^(P.card+b) ≤ (m^2).factorial) :
    (acceptingTables fun y => mcspSquare m (substitute (pinAt x P) y)).card ≤
      2^(descriptionBitBound m-b) := by
  apply (Nat.mul_le_mul_right_iff (Nat.two_pow_pos b)).mp
  calc
    _ ≤ (2^P.card*(acceptingTables (mcspSquare m)).card)*2^b :=
      Nat.mul_le_mul_right _ (card_accepting_pin_le (mcspSquare m) x P)
    _ = (acceptingTables (mcspSquare m)).card*2^(P.card+b) := by rw [pow_add]; ring
    _ ≤ (acceptingTables (mcspSquare m)).card*(m^2).factorial := Nat.mul_le_mul_left _ hRoom
    _ ≤ 2^descriptionBitBound m := card_accepting_mcspSquare_mul_factorial_le m
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hb]

end Sparsity

section Propagation

variable {n k g : ℕ}

/-- A path along which a controlling bit propagates unchanged. -/
inductive AbsorbingPath (p : Program signature n g) (b : Bool) (start : Wire n g) :
    Wire n g → Prop where
  | here : AbsorbingPath p b start start
  | step {j : Fin g} (a : Fin (signature.Arity (p.lines j).op))
      (op : (p.lines j).op = if b then .or else .and)
      (earlier : AbsorbingPath p b start ((p.lines j).wires a)) :
      AbsorbingPath p b start (.gate j)

private theorem absorbing_eval (op : Op) (b : Bool)
    (hOp : op = if b then .or else .and)
    (v : Fin (signature.Arity op) → Bool) (a : Fin (signature.Arity op)) (h : v a = b) :
    interpretation op v = b := by
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hOp
    subst op
    fin_cases a <;> simp_all [interpretation]
  · simp only [ite_true] at hOp
    subst op
    fin_cases a <;> simp_all [interpretation]

theorem AbsorbingPath.restricted_eq {p : Program signature n g} {b : Bool}
    {u v : Wire n g} (h : AbsorbingPath p b u v) (ρ : Fin n → Fin k ⊕ Bool)
    (hStart : restrictedWire p ρ u = fun _ => b) :
    restrictedWire p ρ v = fun _ => b := by
  induction h with
  | here => exact hStart
  | @step j a hop _ ih =>
    funext z
    change p.trace interpretation (substitute ρ z) (.gate j) = b
    rw [p.trace_gate]
    exact absorbing_eval _ _ hop _ a (congrFun ih z)

/-- Original gates with a direct pinned input argument. -/
noncomputable def directReaders (p : Program signature n g) (P : Finset (Fin n)) : Finset (Fin g) :=
  Finset.univ.filter fun j => ∃ i ∈ P, ∃ a, (p.lines j).wires a = .input i

/-- Original gates that read a signal constant on the joint restriction. -/
noncomputable def constantReaders (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) :
    Finset (Fin g) :=
  Finset.univ.filter fun j => ∃ a b, restrictedWire p ρ ((p.lines j).wires a) = fun _ => b

/-- Remove all direct readers from the downstream count. -/
noncomputable def downstreamReaders (p : Program signature n g) (P : Finset (Fin n))
    (x : BitString n) : Finset (Fin g) :=
  constantReaders p (pinAt x P) \ directReaders p P

theorem pin_input_constant (p : Program signature n g)
    (x : BitString n) {P : Finset (Fin n)} {i : Fin n} (hi : i ∈ P) :
    restrictedWire p (pinAt x P) (.input i) = fun _ => x i :=
  funext fun _ => substitute_inr (by simp [pinAt, hi])

theorem directReaders_subset_constantReaders (p : Program signature n g)
    (P : Finset (Fin n)) (x : BitString n) :
    directReaders p P ⊆ constantReaders p (pinAt x P) := by
  intro j hj
  obtain ⟨i, hi, a, ha⟩ := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, x i, ha ▸ pin_input_constant p x hi⟩

theorem constantReaders_subset_firstFreshLoss (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) :
    constantReaders p ρ ⊆ firstFreshLoss p ρ := by
  intro j hj
  obtain ⟨a, b, he⟩ := (Finset.mem_filter.mp hj).2
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
    (Finset.mem_filter.mp h).2 (disclosed_of_constant_argument p ρ j a b he)⟩

/-- All three charges use disjoint original indices. The first two lie
outside the final fresh set, and the third lies outside its live part. -/
theorem original_reader_and_dead_budget (p : Program signature n g)
    (root : Wire n g) (P : Finset (Fin n)) (x : BitString n)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x P) root = fun _ => b) :
    complexity interpretation (single (restrictedWire p (pinAt x P) root)) +
      (directReaders p P).card + (downstreamReaders p P x).card +
      (deadFresh p (pinAt x P) root).card ≤ g := by
  have hPair := Finset.card_sdiff_add_card_eq_card (directReaders_subset_constantReaders p P x)
  change (downstreamReaders p P x).card + (directReaders p P).card =
    (constantReaders p (pinAt x P)).card at hPair
  have hSub := Finset.card_le_card (constantReaders_subset_firstFreshLoss p (pinAt x P))
  have h := first_dead_and_residual_budget p (pinAt x P) root hNon
  omega

/-- Gates beyond the direct readers that read the end of a compatible path. -/
noncomputable def reachableReaders (p : Program signature n g)
    (P : Finset (Fin n)) (b : Bool) : Finset (Fin g) :=
  (Finset.univ.filter fun j => ∃ i ∈ P, ∃ a, AbsorbingPath p b (.input i) ((p.lines j).wires a)) \
    directReaders p P

theorem reachableReaders_subset_downstream (p : Program signature n g)
    (P : Finset (Fin n)) (x : BitString n) (b : Bool) (hPins : ∀ i ∈ P, x i = b) :
    reachableReaders p P b ⊆ downstreamReaders p P x := by
  intro j hj
  obtain ⟨hPath, hDirect⟩ := Finset.mem_sdiff.mp hj
  obtain ⟨i, hi, a, ha⟩ := (Finset.mem_filter.mp hPath).2
  have hConst := pin_input_constant p x hi
  rw [hPins i hi] at hConst
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, b, ha.restricted_eq (pinAt x P) hConst⟩, hDirect⟩

/-- One of the two uniform pin assignments charges at least half the
union of all possible compatible downstream readers. -/
theorem exists_uniform_downstream_charge (p : Program signature n g) (P : Finset (Fin n)) :
    ∃ b : Bool, ((reachableReaders p P false) ∪ reachableReaders p P true).card ≤
      2*(downstreamReaders p P (fun _ => b)).card := by
  have hU := Finset.card_union_le (reachableReaders p P false) (reachableReaders p P true)
  have h0 := Finset.card_le_card (reachableReaders_subset_downstream p P (fun _ => false) false (by simp))
  have h1 := Finset.card_le_card (reachableReaders_subset_downstream p P (fun _ => true) true (by simp))
  by_cases h : (reachableReaders p P false).card ≤ (reachableReaders p P true).card
  · exact ⟨true, by omega⟩
  · exact ⟨false, by omega⟩

/-- An accepted nonconstant output in a minimum circuit uses all original
indices freshly before restriction. -/
theorem minimum_fresh_univ {f : BooleanFunction n} (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (hNon : ¬∃ b : Bool, f = fun _ => b) :
    fresh c.program Sum.inl = Finset.univ := by
  have hEq : restrictedWire c.program Sum.inl (c.outputs 0) = f :=
    restricted_circuit_eq c hc (Sum.inl : Fin n → Fin n ⊕ Bool)
  have h := fresh_complexity_le_of_nonconstant c.program Sum.inl (c.outputs 0) (by
    rwa [hEq])
  rw [hEq, ← hMin] at h
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa using h

theorem directReader_charge_of_coverage (p : Program signature n g)
    (P Q : Finset (Fin n)) (x : BitString n) (hQP : Q ⊆ P)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hRead : ∀ i ∈ Q, ∃ j : Fin g, ∃ a, (p.lines j).wires a = .input i) :
    Q.card ≤ 2*(directReaders p P).card := by
  let J := directReaders p P
  have h := pins_charge_of_readers (p := p) x ∅ Q P J hQP (fun i hi => by
    obtain ⟨j, a, ha⟩ := hRead i hi
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hQP hi, a, ha⟩, a, ha⟩)
  have hId : pinAt x ∅ = Sum.inl := by funext i; simp [pinAt]
  have hEmpty : J \ fresh p Sum.inl = ∅ := by rw [hFresh]; simp
  rw [hId, hEmpty, Finset.card_empty, Nat.zero_add] at h
  exact h.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card Finset.inter_subset_left))

theorem minimum_live_univ {f : BooleanFunction n} (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (hNon : ¬∃ b : Bool, f = fun _ => b) :
    liveFresh c.program Sum.inl (c.outputs 0) = Finset.univ := by
  have hEq : restrictedWire c.program Sum.inl (c.outputs 0) = f :=
    restricted_circuit_eq c hc (Sum.inl : Fin n → Fin n ⊕ Bool)
  have h := live_fresh_complexity_le c.program Sum.inl (c.outputs 0) (by rwa [hEq])
  rw [hEq, ← hMin] at h
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa using h

theorem original_represents_gate {p : Program signature n g}
    (hFresh : fresh p Sum.inl = Finset.univ) {w : Wire n g} {j : Fin g}
    (h : Represents p Sum.inl w j) : w = .gate j := by
  cases w with
  | input i =>
    have he : restrictedWire p Sum.inl (.gate j) = projection i := h.2
    exact ((Finset.mem_filter.mp h.1).2 (Or.inr (Or.inl ⟨i, he⟩))).elim
  | gate i =>
    have hi : Represents p Sum.inl (.gate i) i := ⟨hFresh.symm ▸ Finset.mem_univ i, rfl⟩
    exact congrArg Wire.gate (represents_unique p Sum.inl hi h)

theorem constant_of_two_arguments (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (j : Fin g) (a b : Fin (signature.Arity (p.lines j).op)) (hne : a ≠ b)
    (va vb : Bool) (ha : restrictedWire p ρ ((p.lines j).wires a) = fun _ => va)
    (hb : restrictedWire p ρ ((p.lines j).wires b) = fun _ => vb) :
    ∃ v : Bool, restrictedWire p ρ (.gate j) = fun _ => v := by
  have hArity := (Program.fanInAtMost_iff.mp p.fanInAtMost_two) j
  have hPorts (i : Fin (signature.Arity (p.lines j).op)) : i = a ∨ i = b := by
    by_contra! h
    have hai : i.val ≠ a.val := fun e => h.1 (Fin.ext e)
    have hbi : i.val ≠ b.val := fun e => h.2 (Fin.ext e)
    have hab : a.val ≠ b.val := fun e => hne (Fin.ext e)
    have hIa := i.isLt
    have hAa := a.isLt
    have hBa := b.isLt
    omega
  refine ⟨restrictedWire p ρ (.gate j) (fun _ => false), funext fun z => ?_⟩
  unfold restrictedWire
  rw [p.trace_gate, p.trace_gate]
  congr 1
  funext i
  rcases hPorts i with rfl | rfl
  · exact (congrFun ha z).trans (congrFun ha (fun _ => false)).symm
  · exact (congrFun hb z).trans (congrFun hb (fun _ => false)).symm

theorem op_can_force_constant (op : Op) (a : Fin (signature.Arity op)) :
    ∃ b v : Bool, ∀ f : Fin (signature.Arity op) → Bool, f a = b → interpretation op f = v := by
  cases op with
  | const b => exact Fin.elim0 a
  | not =>
    refine ⟨false, true, fun f hf => ?_⟩
    have ha := Fin.eq_zero a
    rw [ha] at hf
    simp [interpretation, hf]
  | and => exact ⟨false, false, fun f h => absorbing_eval .and false rfl f a h⟩
  | or => exact ⟨true, true, fun f h => absorbing_eval .or true rfl f a h⟩

/-- A constant direct reader in an original live circuit must eventually
reach a gate outside the direct-reader set if the residual is nonconstant. -/
theorem downstream_nonempty_of_constant_live (p : Program signature n g)
    (root : Wire n g) (P : Finset (Fin n)) (x : BitString n)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x P) root = fun _ => b)
    {j : Fin g} (hj : j ∈ liveFresh p Sum.inl root)
    (hC : ∃ b : Bool, restrictedWire p (pinAt x P) (.gate j) = fun _ => b) :
    (downstreamReaders p P x).Nonempty := by
  let ρ := pinAt x P
  by_contra hNo
  have hAbsent {u : Fin g} (h : ResidualLive p Sum.inl root u) :
      ¬∃ b : Bool, restrictedWire p ρ (.gate u) = fun _ => b := by
    induction h with
    | @output u hRep =>
      have he := original_represents_gate hFresh hRep
      simpa only [he] using hNon
    | @argument u v hLive a hRep ih =>
      rintro ⟨b, hb⟩
      have he := original_represents_gate hFresh hRep
      have hA : restrictedWire p ρ ((p.lines u).wires a) = fun _ => b := he ▸ hb
      have hDirect : u ∈ directReaders p P := by
        by_contra hu
        apply hNo
        exact ⟨u, Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, b, hA⟩, hu⟩⟩
      obtain ⟨i, hi, ai, hri⟩ := (Finset.mem_filter.mp hDirect).2
      have han : a ≠ ai := by
        intro heq
        rw [heq, hri] at he
        cases he
      exact ih (constant_of_two_arguments p ρ u a ai han b (x i) hA
        (hri ▸ pin_input_constant p x hi))
  exact hAbsent (mem_liveFresh_iff.mp hj) hC

/-- With free choice of the uniform polarity, a nonempty direct-reader set
in a minimum circuit forces at least one strictly downstream deletion. -/
theorem exists_positive_downstream_charge (p : Program signature n g)
    (root : Wire n g) (P : Finset (Fin n))
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hDirect : (directReaders p P).Nonempty)
    (hNon : ∀ s : Bool, ¬∃ b : Bool, restrictedWire p (pinAt (fun _ => s) P) root = fun _ => b) :
    ∃ s : Bool, (downstreamReaders p P (fun _ => s)).Nonempty := by
  obtain ⟨j, hj⟩ := hDirect
  obtain ⟨i, hi, a, ha⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨s, b, hb⟩ := op_can_force_constant (p.lines j).op a
  let ρ := pinAt (fun _ => s) P
  have hA : restrictedWire p ρ ((p.lines j).wires a) = fun _ => s :=
    ha ▸ pin_input_constant p (fun _ => s) hi
  have hC : restrictedWire p ρ (.gate j) = fun _ => b := by
    funext z
    unfold restrictedWire
    rw [p.trace_gate]
    exact hb _ (congrFun hA z)
  exact ⟨s, downstream_nonempty_of_constant_live p root P _ hFresh (hNon s)
    (hLive.symm ▸ Finset.mem_univ j) ⟨b, hC⟩⟩

end Propagation

section ThreeBlocks

set_option exponentiation.threshold 8192 in
theorem factorial_room_32 : 2^4608 ≤ ((32:ℕ)^2).factorial := by
  have h := pow_le_factorial_of_large_factors (q := 512) (k := 9) (by decide) 512
  rw [show (32:ℕ)^2 = 1024 by decide]
  change (2:ℕ)^4608 ≤ (1024:ℕ).factorial at h
  exact h

/-- Three joint blocks retain the full quadratic forest bound with a smaller
description bound. Either uniform pin polarity is now available. -/
theorem original_downstream_charge_32 (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32))) :
    ∃ (E : Finset (BitString 24)) (b : Bool), E.card = 3 ∧
      let P := blocks (d := 8) E
      let x : BitString (2^32) := fun _ => b
      let p := c.program
      let root := c.outputs 0
      1 ≤ (downstreamReaders p P x).card ∧
      ((reachableReaders p P false) ∪ reachableReaders p P true).card ≤
        2*(downstreamReaders p P x).card ∧
      8620564202 + (downstreamReaders p P x).card + (deadFresh p (pinAt x P) root).card ≤ c.size := by
  let p := c.program
  let root := c.outputs 0
  let S := needInputs p root false
  have hSparse := card_accepting_mcspSquare_le 32
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hNeed : 2^32 ≤ S.card + 27672 := by
    simpa only [show descriptionBitBound 32 = 27672 by decide] using
      card_needInputs_ge_of_sparse c hc hSparse false h0
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hMiss
  obtain ⟨E, hE, hCover⟩ := exists_covered_blocks (a := 24) (d := 8) S 3 (by
    norm_num at hNeed hMiss ⊢
    omega)
  let P := blocks (d := 8) E
  have hP : P.card = 768 := by rw [show P = blocks (d := 8) E from rfl, card_blocks, hE]; decide
  let f (b : Bool) : BooleanFunction (2^32) :=
    fun y => mcspSquare 32 (substitute (pinAt (fun _ => b) P) y)
  have hResid (b : Bool) : (acceptingTables (f b)).card ≤ 2^23832 := by
    have h := padded_sparsity_of_factorial (b := 3840) (fun _ => b) P (by decide) (by
      rw [hP, show (768:ℕ)+3840 = 4608 by decide]
      exact factorial_room_32)
    rwa [show descriptionBitBound 32 - 3840 = 23832 by decide] at h
  have hQ (b : Bool) (a : BitString 32) (s : Bool) (u w : BitString 32) :
      f b (MCSP.truthTable 32 (quad a s u w)) = true := by
    apply accepted_after_blocks_pin (a := 24) (k := 2) (l := 6)
    have hCost := complexity_quad_shared_le a s u w
    rw [hE]
    norm_num [lookupBankCost] at hCost ⊢
    omega
  have hZero (b : Bool) : f b (fun _ => false) = true := by
    have h := hQ b (zeroVec 32) false (zeroVec 32) (zeroVec 32)
    have he : MCSP.truthTable 32 (quad (zeroVec 32) false (zeroVec 32) (zeroVec 32)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  have hInitNon := not_constant_of_sparse (by decide) hSparse h0
  have hFresh := minimum_fresh_univ c hc hMin hInitNon
  have hLive := minimum_live_univ c hc hMin hInitNon
  have hCount (x : BitString (2^32)) : 768 ≤ 2*(directReaders p P).card := by
    have h := directReader_charge_of_coverage p P P x (by rfl) hFresh (fun i hi => by
      obtain ⟨j, _, a, ha⟩ := need_input_has_reader hc0 hc1 (hCover hi)
      exact ⟨j, a, ha⟩)
    rwa [hP] at h
  have hDirect : (directReaders p P).Nonempty :=
    Finset.card_pos.mp (by have h := hCount (fun _ => false); omega)
  have hEq (b : Bool) : restrictedWire p (pinAt (fun _ => b) P) root = f b :=
    restricted_circuit_eq c hc (pinAt (fun _ => b) P)
  have hNon (b : Bool) : ¬∃ v : Bool, restrictedWire p (pinAt (fun _ => b) P) root = fun _ => v := by
    rw [hEq]
    exact not_constant_of_sparse (by decide) (hResid b) (hZero b)
  obtain ⟨u, hu⟩ := exists_positive_downstream_charge p root P hFresh hLive hDirect hNon
  obtain ⟨v, hv⟩ := exists_uniform_downstream_charge p P
  obtain ⟨b, hPositive, hReach⟩ : ∃ b : Bool, 1 ≤ (downstreamReaders p P (fun _ => b)).card ∧
      ((reachableReaders p P false) ∪ reachableReaders p P true).card ≤
        2*(downstreamReaders p P (fun _ => b)).card := by
    have hu' := Finset.card_pos.mpr hu
    by_cases h : (downstreamReaders p P (fun _ => u)).card ≤ (downstreamReaders p P (fun _ => v)).card
    · exact ⟨v, by omega, hv⟩
    · exact ⟨u, by omega, by omega⟩
  have hForest := quad_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding (hResid b) (hQ b)
  change 280*(2*4294967296)+2*4294967296 ≤
    280*(complexity interpretation (single (f b))+2*23832+1)+17*23832 at hForest
  have hBudget := original_reader_and_dead_budget p root P (fun _ => b) (hNon b)
  rw [hEq] at hBudget
  have hDirectCount := hCount (fun _ => b)
  refine ⟨E, b, hE, hPositive, hReach, ?_⟩
  change 8620564202 + (downstreamReaders p P (fun _ => b)).card +
    (deadFresh p (pinAt (fun _ => b) P) root).card ≤ c.size
  omega

theorem mcspSquare_32_downstream_floor :
    8620564203 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  obtain ⟨E, b, _, hPositive, _, hBudget⟩ := original_downstream_charge_32 c hc hSize
  omega

/-- The same factorial estimate also strengthens the unpinned forest
bound. This measures the gain in counting independently of propagation. -/
theorem mcspSquare_32_factorial_forest_floor :
    8620565401 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := padded_sparsity_of_factorial (m := 32) (b := 4608) (fun _ => false) ∅
    (by decide) (by
      rw [Finset.card_empty, Nat.zero_add]
      exact factorial_room_32)
  have he : (fun y => mcspSquare 32 (substitute (pinAt (fun _ => false) ∅) y)) = mcspSquare 32 := by
    funext y
    congr 1
  rw [he, show descriptionBitBound 32 - 4608 = 23064 by decide] at h
  have hForest := quad_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding h
    (fun a b c d => mcspSquare_accepts_quad 32 (by decide) a b c d)
  change 280*(2*4294967296)+2*4294967296 ≤
    280*(complexity interpretation (single (mcspSquare 32))+2*23064+1)+17*23064 at hForest
  omega

end ThreeBlocks

theorem growing_blocks_fit_factorial (t : ℕ) (ht : 8 ≤ t) :
    2^(2*multiBlockLoss t) ≤ ((multiBlockArity t)^2).factorial := by
  let m := multiBlockArity t
  let k := t.log2
  let l := 3*t-2
  let r := (2:ℕ)^t
  let q := (2:ℕ)^(4*t-1)
  have hK : 2^k ≤ t := Nat.log2_self_le (by omega : t ≠ 0)
  have hD : 1 ≤ k+l := by dsimp only [l]; omega
  have hScale : 2*multiBlockLoss t = (r*2^l)*2^k := calc
    _ = r*(2*2^(k+l-1)) := by unfold multiBlockLoss; dsimp only [k, l, r]; ring
    _ = r*2^(k+l) := by rw [← pow_succ', Nat.sub_add_cancel hD]
    _ = _ := by rw [pow_add]; ring
  have hHalf : q+q = m^2 := calc
    _ = 2*q := by omega
    _ = 2^(4*t) := by dsimp only [q]; rw [← pow_succ', Nat.sub_add_cancel (by omega)]
    _ = 2^((2*t)*2) := congrArg (fun j : ℕ => 2^j) (by omega)
    _ = _ := pow_mul _ _ _
  have hRows : 4*(r*2^l) = m^2 := multi_block_rows t ht
  have hRowLe : r*2^l ≤ q := by omega
  have hBound : 2*multiBlockLoss t ≤ (4*t-1)*q := calc
    _ ≤ (r*2^l)*2^k := hScale.le
    _ ≤ q*(4*t-1) := Nat.mul_le_mul hRowLe (hK.trans (by omega))
    _ = _ := Nat.mul_comm ..
  have hFac := pow_le_factorial_of_large_factors (q := q) (k := 4*t-1) (by
    change q ≤ q+1
    omega) q
  rw [hHalf] at hFac
  exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hBound).trans hFac

/-- The factorial room also permits either polarity on every joint block
of the growing schedule, with the original sparsity bound. -/
theorem growing_blocks_preserve_sparsity (t : ℕ) (ht : 8 ≤ t)
    (P : Finset (Fin (2^(multiBlockArity t)))) (hP : P.card ≤ 2*multiBlockLoss t)
    (x : BitString (2^(multiBlockArity t))) :
    (acceptingTables fun y => mcspSquare (multiBlockArity t) (substitute (pinAt x P) y)).card ≤
      2^descriptionBitBound (multiBlockArity t) := by
  have h := padded_sparsity_of_factorial (b := 0) x P (Nat.zero_le _) (by
    rw [Nat.add_zero]
    exact (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hP).trans
      (growing_blocks_fit_factorial t ht))
  simpa only [Nat.sub_zero] using h

section ChainControl

open QuarterDeadFrontier (chainedProgram)

def controlPins : Finset (Fin 4) := {0, 1}

private def controlPin : Fin 4 → Fin 4 ⊕ Bool := pinAt (fun _ => false) controlPins

private theorem chain_reader_mem {j : Fin 8} (a : Fin (signature.Arity (chainedProgram.lines j).op))
    (hConst : restrictedWire chainedProgram controlPin ((chainedProgram.lines j).wires a) = fun _ => false)
    (hNo : ∀ i ∈ controlPins, ∀ b, (chainedProgram.lines j).wires b ≠ .input i) :
    j ∈ downstreamReaders chainedProgram controlPins (fun _ => false) := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, false, hConst⟩, ?_⟩
  intro h
  obtain ⟨i, hi, b, hb⟩ := (Finset.mem_filter.mp h).2
  exact hNo i hi b hb

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- The minimum all-equal control has four additional original readers
when the two first entries are pinned false. -/
theorem chain_control_downstream :
    4 ≤ (downstreamReaders chainedProgram controlPins (fun _ => false)).card := by
  have h0 : restrictedWire chainedProgram controlPin (.gate 0) = fun _ => false := by
    funext x
    change (substitute controlPin x 0 || substitute controlPin x 1) = false
    simp [substitute, controlPin, pinAt, controlPins]
  have h3 : restrictedWire chainedProgram controlPin (.gate 3) = fun _ => false := by
    funext x
    change (substitute controlPin x 0 && substitute controlPin x 1) = false
    simp [substitute, controlPin, pinAt, controlPins]
  have h4 : restrictedWire chainedProgram controlPin (.gate 4) = fun _ => false := by
    funext x
    change (restrictedWire chainedProgram controlPin (.gate 3) x && substitute controlPin x 2) = false
    rw [h3]
    rfl
  have h5 : restrictedWire chainedProgram controlPin (.gate 5) = fun _ => false := by
    funext x
    change (restrictedWire chainedProgram controlPin (.gate 4) x && substitute controlPin x 3) = false
    rw [h4]
    rfl
  let S : Finset (Fin 8) := {1,4,5,7}
  have hSub : S ⊆ downstreamReaders chainedProgram controlPins (fun _ => false) := by
    intro j hj
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl
    · exact chain_reader_mem (j := 1) ⟨0, by decide⟩ h0 (by
        intro i hi a
        fin_cases i <;> fin_cases a <;> simp [controlPins] at hi <;> decide)
    · exact chain_reader_mem (j := 4) ⟨0, by decide⟩ h3 (by
        intro i hi a
        fin_cases i <;> fin_cases a <;> simp [controlPins] at hi <;> decide)
    · exact chain_reader_mem (j := 5) ⟨0, by decide⟩ h4 (by
        intro i hi a
        fin_cases i <;> fin_cases a <;> simp [controlPins] at hi <;> decide)
    · exact chain_reader_mem (j := 7) ⟨1, by decide⟩ h5 (by
        intro i hi a
        fin_cases i <;> fin_cases a <;> simp [controlPins] at hi <;> decide)
  exact (show 4 ≤ S.card by decide).trans (Finset.card_le_card hSub)

end ChainControl

#print axioms padded_sparsity_of_factorial
#print axioms reachableReaders_subset_downstream
#print axioms original_reader_and_dead_budget
#print axioms exists_positive_downstream_charge
#print axioms original_downstream_charge_32
#print axioms mcspSquare_32_downstream_floor
#print axioms mcspSquare_32_factorial_forest_floor
#print axioms chain_control_downstream
#print axioms growing_blocks_preserve_sparsity

end PvsNP.Frontier.DownstreamBlockPinning
