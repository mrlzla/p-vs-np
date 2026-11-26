module

public import MCSPQuadraticPinning
public import Complexity.Computability.Circuit.Boolean.ShannonSynthesis

/-! Pin an address subcube selected from the original two-corner wiring.
The correction is one small lookup on its free address coordinates. -/

@[expose] public section

namespace PvsNP.Frontier.ForestBlockPinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest
open ForestPinning RestrictionCharges FreshCharges NestedFaces
open MinorityResidual QuadraticForest QuadraticPinning SuperTwoN
open scoped Classical BigOperators

section AddressBlocks

variable {a d : ℕ}

def addressHead (d : ℕ) (z : BitString (a+d)) : BitString a := z ∘ Fin.castAdd d

def addressTail (a : ℕ) (z : BitString (a+d)) : BitString d := z ∘ Fin.natAdd a

theorem append_prefix_suffix (z : BitString (a+d)) :
    Fin.append (addressHead d z) (addressTail a z) = z := by
  funext i
  exact Fin.addCases (fun j => by simp [addressHead]) (fun j => by simp [addressTail]) i

def tag (i : Fin (2^(a+d))) : BitString a := addressHead d ((BitString.equivFin (a+d)).symm i)

/-- Pin all addresses with one specified prefix. -/
noncomputable def block (p : BitString a) : Finset (Fin (2^(a+d))) :=
  Finset.univ.filter fun i => tag i = p

theorem card_block (p : BitString a) : (block (d := d) p).card = 2^d := by
  let e (u : BitString d) := BitString.equivFin (a+d) (Fin.append p u)
  have he : (Finset.univ : Finset (BitString d)).image e = block p := by
    ext i
    constructor
    · intro hi
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simp [tag, e, addressHead, Function.comp_def]
    · intro hi
      let z := (BitString.equivFin (a+d)).symm i
      have hp : addressHead d z = p := (Finset.mem_filter.mp hi).2
      apply Finset.mem_image.mpr
      refine ⟨addressTail a z, Finset.mem_univ _, ?_⟩
      change BitString.equivFin (a+d) (Fin.append p (addressTail a z)) = i
      rw [← hp, append_prefix_suffix, Equiv.apply_symm_apply]
  have hInj : Function.Injective e := by
    intro u v h
    have hh := congrArg (addressTail a) ((BitString.equivFin (a+d)).injective h)
    simpa [addressTail, Function.comp_def] using hh
  rw [← he, Finset.card_image_of_injective _ hInj, Finset.card_univ, BitString.card]

/-- Some block sees at least the global density of any fixed set of wired inputs. -/
theorem exists_dense_block (S : Finset (Fin (2^(a+d)))) {k : ℕ}
    (hS : 2^(a+d) ≤ k*S.card) :
    ∃ p : BitString a, 2^d ≤ k*(S.filter fun i => tag i = p).card := by
  have hSum : (∑ p : BitString a, (S.filter fun i => tag i = p).card) = S.card := by
    simpa only [Finset.mem_univ, Finset.filter_true] using
      Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ : Finset (BitString a)) tag
  by_contra! h
  have hLt : (∑ p : BitString a, k*(S.filter fun i => tag i = p).card) <
      ∑ _p : BitString a, 2^d :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ => h p)
  rw [← Finset.mul_sum, hSum] at hLt
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, ← pow_add] at hLt
  exact (not_lt_of_ge hS) hLt

/-- If there are more address blocks than missing inputs, an entire block is covered. -/
theorem exists_covered_block (S : Finset (Fin (2^(a+d))))
    (hS : ((Finset.univ : Finset _) \ S).card < 2^a) :
    ∃ p : BitString a, block (d := d) p ⊆ S := by
  let bad := ((Finset.univ : Finset _) \ S).image tag
  have hBad : bad.card < 2^a := Finset.card_image_le.trans_lt hS
  obtain ⟨p, hp⟩ : ∃ p : BitString a, p ∉ bad := by
    by_contra! h
    rw [Finset.eq_univ_of_forall h, Finset.card_univ, BitString.card] at hBad
    omega
  refine ⟨p, ?_⟩
  intro i hi
  by_contra hn
  exact hp (Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩,
    (Finset.mem_filter.mp hi).2⟩)

private theorem complexity_comp_wiring_le {n m : ℕ} (w : Fin n → Fin m) (f : BooleanFunction n) :
    complexity interpretation (single (fun x => f (x ∘ w))) ≤ complexity interpretation (single f) := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single f)
  let C := c.comp (Circuit.wiring signature w)
  have hC : C.Computes interpretation (single (fun x => f (x ∘ w))) := by
    intro x
    change (c.comp (Circuit.wiring signature w)).eval interpretation x = _
    rw [Circuit.eval_comp, Circuit.eval_wiring]
    exact hc _
  exact (complexity_le_of_computes C hC).trans (by simpa [C, Circuit.size_comp] using hsize.le)

def prefixMatch (p : BitString a) (z : BitString (a+d)) : Bool :=
  decide (addressHead d z = p)

theorem synthesis_prefix_match (p : BitString a) :
    Synthesis interpretation (inputs (a+d)) {prefixMatch (d := d) p} (2*a+1) := by
  let lit (i : Fin a) (z : BitString (a+d)) := decide (z (Fin.castAdd d i) = p i)
  have hl (i : Fin a) : Synthesis interpretation (inputs (a+d)) {lit i} 1 :=
    Synthesis.literal (show (fun z : BitString (a+d) => z (Fin.castAdd d i)) ∈ inputs (a+d) from
      ⟨Fin.castAdd d i, rfl⟩) (p i)
  obtain ⟨w, hw, hs⟩ := Synthesis.exists_forall_mem (Finset.univ : Finset (Fin a)) lit
    (c := 1) (m := a) (by simp) (fun i _ => hl i)
  have hMatch := Synthesis.congr_iff hs (g := prefixMatch (d := d) p) (fun z => by
    rw [hw]
    simp only [lit, prefixMatch, Finset.mem_univ, true_implies, decide_eq_true_eq]
    exact ⟨funext, congrFun⟩)
  exact hMatch.mono Set.Subset.rfl Set.Subset.rfl (by omega)

theorem complexity_matches_le (p : BitString a) :
    complexity interpretation (single (prefixMatch (d := d) p)) ≤ 2*a+1 :=
  (synthesis_prefix_match p).complexity_le

private theorem tree_lookup_bound (f : BooleanFunction d) :
    complexity interpretation (single f) ≤ 5*2^d := by
  let t := OrderedTree.canonical d f
  have hCost := OrderedTree.Tree.cost t
  have hDepth := OrderedTree.canonical_depth_le_arity f
  have hPow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  change 2^t.depth ≤ 2^d at hPow
  rw [show t.eval = f from OrderedTree.canonical_eval f] at hCost
  omega

/-- The repair on a whole prefix block is any Boolean function of the remaining
address bits, masked by one equality check on the fixed prefix. -/
theorem accepted_after_block_pin {k : ℕ}
    (hLookup : ∀ g : BooleanFunction d, complexity interpretation (single g) ≤ k)
    (p : BitString a) (x : BitString (2^(a+d))) (f : BooleanFunction (a+d))
    (hBudget : complexity interpretation (single f) + 2*a + k + 6 ≤ (a+d)^2) :
    mcspSquare (a+d) (substitute (pinAt x (block p)) (MCSP.truthTable _ f)) = true := by
  let fix (u : BitString d) := f (Fin.append p u) ^^ x (BitString.equivFin (a+d) (Fin.append p u))
  let correction (z : BitString (a+d)) := prefixMatch p z && fix (addressTail a z)
  have hLift : complexity interpretation (single (fun z => fix (addressTail a z))) ≤ k :=
    (complexity_comp_wiring_le (Fin.natAdd a) fix).trans (hLookup fix)
  have hMask : complexity interpretation (single correction) ≤ (2*a+1) + k + 1 :=
    (complexity_and_le (prefixMatch (d := d) p) (fun z => fix (addressTail a z))).trans
      (Nat.add_le_add_right (Nat.add_le_add (complexity_matches_le p) hLift) 1)
  have hCorrect : MCSP.truthTable (a+d) (fun z => f z ^^ correction z) =
      substitute (pinAt x (block p)) (MCSP.truthTable (a+d) f) := by
    funext i
    let z := (BitString.equivFin (a+d)).symm i
    simp only [MCSP.truthTable_apply]
    change (f z ^^ correction z) = substitute (pinAt x (block p)) (MCSP.truthTable (a+d) f) i
    by_cases hi : i ∈ block p
    · have hp : addressHead d z = p := (Finset.mem_filter.mp hi).2
      have he : Fin.append p (addressTail a z) = z := hp ▸ append_prefix_suffix z
      rw [substitute_inr (show pinAt x (block p) i = .inr (x i) by simp [pinAt, hi])]
      simp only [correction, prefixMatch, hp, decide_true, Bool.true_and, fix, he, z, Equiv.apply_symm_apply]
      cases f ((BitString.equivFin (a+d)).symm i) <;> cases x i <;> rfl
    · have hp : addressHead d z ≠ p := fun he => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      rw [substitute_inl (show pinAt x (block p) i = .inl i by simp [pinAt, hi])]
      simp [correction, prefixMatch, hp, z, MCSP.truthTable_apply]
  rw [← hCorrect, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  have h := complexity_xor_le f correction
  exact h.trans (by omega)

end AddressBlocks

section ReaderAccounting

variable {n g : ℕ}

theorem exists_sparse_pins (f : BooleanFunction n) (P : Finset (Fin n)) :
    ∃ x : BitString n, (acceptingTables fun z => f (substitute (pinAt x P) z)).card ≤
      (acceptingTables f).card := by
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => false, ?_⟩
    have hId : (fun z => f (substitute (pinAt (fun _ => false) ∅) z)) = f := by
      funext z
      congr 1
    rw [hId]
  | @insert i P hi ih =>
    obtain ⟨x, hx⟩ := ih
    let F : BooleanFunction n := fun z => f (substitute (pinAt x P) z)
    obtain ⟨v, hv⟩ := exists_sparse_pin F i
    let y := Function.update x i v
    refine ⟨y, ?_⟩
    have he (z : BitString n) : substitute (pinAt y {i}) z = Function.update z i v := by
      funext j
      by_cases hj : j = i <;> simp [substitute, pinAt, y, hj]
    have hEq : (fun z => f (substitute (pinAt y (insert i P)) z)) =
        fun z => F (Function.update z i v) := by
      funext z
      rw [show pinAt y (insert i P) = PairSeparation.branchPin x P i v from rfl,
        PairSeparation.branchPin_compose x P i v hi, substitute_compose, he]
    rw [hEq]
    exact hv.trans hx

theorem not_constant_of_sparse {f : BooleanFunction n} {B : ℕ}
    (hFew : B < n) (hSparse : (acceptingTables f).card ≤ 2^B) (hYes : f (fun _ => false) = true) :
    ¬ ∃ b : Bool, f = fun _ => b := by
  rintro ⟨b, he⟩
  have hb : b = true := (congrFun he (fun _ => false)).symm.trans hYes
  rw [he, hb] at hSparse
  simp only [acceptingTables, Finset.filter_true, Finset.card_univ, BitString.card] at hSparse
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hFew)) hSparse

/-- Original gates belonging to the verified clean OR and AND trees. -/
noncomputable def cleanGates (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  Finset.univ.filter (fun j => (∃ r, ORMember p root r j) ∨ (∃ r, ANDMember p root r j))

/-- The reader pool adds the original stop gates to the clean trees. -/
noncomputable def readerGates (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  StopGate p root ∪ cleanGates p root

theorem need_input_has_clean_reader {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {i : Fin n} (hi : i ∈ needInputs p root false) (hs : i ∉ stopInputs p root) :
    ∃ j ∈ cleanGates p root, ∃ a, (p.lines j).wires a = .input i := by
  rcases need_input_in_stop_or_forest h0 h1 hi with h | ⟨r, _, hr⟩ | ⟨r, _, hr⟩
  · exact (hs h).elim
  · obtain ⟨j, hj, a, ha⟩ := (Finset.mem_filter.mp hr).2
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨r, hj⟩⟩, a, ha⟩
  · obtain ⟨j, hj, a, ha⟩ := (Finset.mem_filter.mp hr).2
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨r, hj⟩⟩, a, ha⟩

theorem need_input_has_reader {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {i : Fin n} (hi : i ∈ needInputs p root false) :
    ∃ j ∈ readerGates p root, ∃ a, (p.lines j).wires a = .input i := by
  by_cases hs : i ∈ stopInputs p root
  · obtain ⟨j, hj, ht⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hs).2
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp ht
    exact ⟨j, Finset.mem_union_left _ hj, a, ha⟩
  · obtain ⟨j, hj, a, ha⟩ := need_input_has_clean_reader h0 h1 hi hs
    exact ⟨j, Finset.mem_union_right _ hj, a, ha⟩

end ReaderAccounting

section BlockLowerBound

variable {a d : ℕ}

/-- Add the distinct original readers made redundant by one joint pin
assignment, provided it preserves all the quadratic probes. -/
theorem pin_losses_and_residual_with_count {m B : ℕ} (c : Circuit signature (2^m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (hMin : c.size = complexity interpretation (single (mcspSquare m)))
    (hm : 1 ≤ m) (hFew : B < 2^m)
    (hSparse : (acceptingTables (mcspSquare m)).card ≤ 2^B)
    (P Q : Finset (Fin (2^m))) (J : Finset (Fin c.size)) (hQP : Q ⊆ P)
    (hReader : ∀ i ∈ Q, ∃ j ∈ J, ∃ k, (c.program.lines j).wires k = .input i)
    (hRepair : ∀ (x : BitString (2^m)) (a : BitString m) (v : Bool) (u w : BitString m),
      mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad a v u w))) = true) :
    ∃ (x : BitString (2^m)),
      let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      Q.card ≤ 2*(J ∩ removed).card ∧
      (280*(2*2^m) + 2*2^m ≤
        280*(complexity interpretation (single f) + 2*B + 1) +
          17*B) ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  let root := c.outputs 0
  have h0 := mcspSquare_constant_table m hm false
  obtain ⟨x, hx⟩ := exists_sparse_pins (mcspSquare m) P
  let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
  have hSparse' : (acceptingTables f).card ≤ 2^B := hx.trans hSparse
  have hQ (u : BitString m) (v : Bool) (c₁ c₂ : BitString m) :
      f (MCSP.truthTable m (quad u v c₁ c₂)) = true :=
    hRepair x u v c₁ c₂
  have hZero : f (fun _ => false) = true := by
    have h := hQ (zeroVec m) false (zeroVec m) (zeroVec m)
    have hz : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [hz] at h
  have hForest := quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding hSparse' hQ
  have hIdEq : restrictedWire c.program Sum.inl root = mcspSquare m :=
    restricted_circuit_eq c hc Sum.inl
  have hInit := fresh_complexity_le_of_nonconstant c.program Sum.inl root (by
    rw [hIdEq]
    exact not_constant_of_sparse hFew hSparse h0)
  rw [hIdEq, ← hMin] at hInit
  have hAll : fresh c.program Sum.inl = Finset.univ := by
    have hCard : (Finset.univ : Finset (Fin c.size)).card ≤ (fresh c.program Sum.inl).card := by
      simpa using hInit
    exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hCard
  have hCount := pins_charge_of_readers (p := c.program) x ∅ Q P J hQP hReader
  have hEmpty : pinAt x ∅ = Sum.inl := by funext i; simp [pinAt]
  rw [hEmpty, show J \ fresh c.program Sum.inl = ∅ by rw [hAll]; simp] at hCount
  simp only [Finset.card_empty, Nat.zero_add, nextFreshLoss] at hCount
  change Q.card ≤ 2*(J ∩ (fresh c.program Sum.inl \ fresh c.program (pinAt x P))).card at hCount
  have hEq : restrictedWire c.program (pinAt x P) root = f :=
    restricted_circuit_eq c hc (pinAt x P)
  have hSynth := fresh_complexity_le_of_nonconstant c.program (pinAt x P) root (by
    rw [hEq]
    exact not_constant_of_sparse hFew hSparse' hZero)
  rw [hEq] at hSynth
  have hSub : fresh c.program (pinAt x P) ⊆ fresh c.program Sum.inl :=
    fresh_nested c.program Sum.inl (pinAt x P)
  have hPart := Finset.card_sdiff_add_card_eq_card hSub
  have hSize : (fresh c.program Sum.inl).card ≤ c.size :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin c.size)
  exact ⟨x, hCount, hForest, by
    change complexity interpretation (single f) + (fresh c.program Sum.inl \ fresh c.program (pinAt x P)).card ≤ c.size
    omega⟩

theorem pin_losses_and_residual_of_readers {m : ℕ} (c : Circuit signature (2^m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (hMin : c.size = complexity interpretation (single (mcspSquare m)))
    (hm : 1 ≤ m) (hFew : descriptionBitBound m < 2^m)
    (P Q : Finset (Fin (2^m))) (J : Finset (Fin c.size)) (hQP : Q ⊆ P)
    (hReader : ∀ i ∈ Q, ∃ j ∈ J, ∃ k, (c.program.lines j).wires k = .input i)
    (hRepair : ∀ (x : BitString (2^m)) (a : BitString m) (v : Bool) (u w : BitString m),
      mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad a v u w))) = true) :
    ∃ (x : BitString (2^m)),
      let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      Q.card ≤ 2*(J ∩ removed).card ∧
      (280*(2*2^m) + 2*2^m ≤
        280*(complexity interpretation (single f) + 2*descriptionBitBound m + 1) +
          17*descriptionBitBound m) ∧
      complexity interpretation (single f) + removed.card ≤ c.size :=
  pin_losses_and_residual_with_count c hc hMin hm hFew (card_accepting_mcspSquare_le m)
    P Q J hQP hReader hRepair

/-- For a chosen block, charge the original readers of any covered subset
and choose values that retain the residual acceptance-count bound. -/
theorem block_losses_and_residual_of_readers {k : ℕ}
    (hLookup : ∀ g : BooleanFunction d, complexity interpretation (single g) ≤ k) (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+d))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+d))))
    (hm : 5 ≤ a+d) (hFew : descriptionBitBound (a+d) < 2^(a+d))
    (hRepair : 6*(a+d) + k + 49 ≤ (a+d)^2)
    (p : BitString a) (Q : Finset (Fin (2^(a+d)))) (J : Finset (Fin c.size))
    (hQP : Q ⊆ block (d := d) p)
    (hReader : ∀ i ∈ Q, ∃ j ∈ J, ∃ k, (c.program.lines j).wires k = .input i) :
    ∃ (x : BitString (2^(a+d))),
      let P := block (d := d) p
      let f : BooleanFunction (2^(a+d)) := fun y => mcspSquare (a+d) (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      Q.card ≤ 2*(J ∩ removed).card ∧
      (280*(2*2^(a+d)) + 2*2^(a+d) ≤
        280*(complexity interpretation (single f) + 2*descriptionBitBound (a+d) + 1) +
          17*descriptionBitBound (a+d)) ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  apply pin_losses_and_residual_of_readers c hc hMin (by omega) hFew (block (d := d) p) Q J hQP hReader
  intro x u v c₁ c₂
  apply accepted_after_block_pin hLookup
  have hCost := complexity_quad_shared_le u v c₁ c₂
  omega

/-- Choose an entire address block from the raw inputs of the original
zero-corner certificate. Pinning makes its direct readers redundant
independently of the values chosen, so the sparse branch is available. -/
theorem original_block_losses_and_residual {k : ℕ}
    (hLookup : ∀ g : BooleanFunction d, complexity interpretation (single g) ≤ k) (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+d))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+d))))
    (hm : 5 ≤ a+d) (hDescription : descriptionBitBound (a+d) < 2^a)
    (hRepair : 6*(a+d) + k + 49 ≤ (a+d)^2) :
    ∃ (p : BitString a) (x : BitString (2^(a+d))),
      block (d := d) p ⊆ needInputs c.program (c.outputs 0) false ∧
      let P := block (d := d) p
      let f : BooleanFunction (2^(a+d)) := fun y => mcspSquare (a+d) (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      2^d ≤ 2*(readerGates c.program (c.outputs 0) ∩ removed).card ∧
      (280*(2*2^(a+d)) + 2*2^(a+d) ≤
        280*(complexity interpretation (single f) + 2*descriptionBitBound (a+d) + 1) +
          17*descriptionBitBound (a+d)) ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  let m := a+d
  let root := c.outputs 0
  have hFew : descriptionBitBound m < 2^m :=
    hDescription.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_add_right a d))
  have hSparse := card_accepting_mcspSquare_le m
  have h0 := mcspSquare_constant_table m (by omega) false
  have h1 := mcspSquare_constant_table m (by omega) true
  have hc0 : cornerValue c.program false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue c.program true root = true := (congrFun (hc _) 0).trans h1
  let S := needInputs c.program root false
  have hNeed : 2^m ≤ S.card + descriptionBitBound m := by
    simpa only [S, root, m, Nat.add_comm] using card_needInputs_ge_of_sparse c hc hSparse false h0
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hMiss
  obtain ⟨p, hp⟩ := exists_covered_block (a := a) (d := d) S (by
    dsimp only [m] at hNeed hMiss
    omega)
  let P := block (d := d) p
  obtain ⟨x, hCount, hForest, hBudget⟩ := block_losses_and_residual_of_readers hLookup c hc hMin hm hFew
    hRepair p P (readerGates c.program root) (by rfl)
    (fun i hi => need_input_has_reader hc0 hc1 (hp hi))
  have hCard : P.card = 2^d := card_block p
  rw [hCard] at hCount
  exact ⟨p, x, hp, hCount, hForest, hBudget⟩

/-- A circuit near the quadratic forest bound still has many clean readers
after excluding all raw stop inputs. This variant charges clean trees only. -/
theorem original_clean_block_losses_and_residual (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+d))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+d))))
    (ha : 13 ≤ a) (hd : 13 ≤ d) (hDescription : descriptionBitBound (a+d) < 2^a)
    (hRepair : 6*(a+d) + 5*2^d + 49 ≤ (a+d)^2)
    (hNear : 280*c.size ≤ 280*(2*2^(a+d) + 2^(d-1)) + 2*2^(a+d)) :
    ∃ (p : BitString a) (x : BitString (2^(a+d))),
      let P := block (d := d) p
      let f : BooleanFunction (2^(a+d)) := fun y => mcspSquare (a+d) (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      2^d ≤ 16*(cleanGates c.program (c.outputs 0) ∩ removed).card ∧
      (280*(2*2^(a+d)) + 2*2^(a+d) ≤
        280*(complexity interpretation (single f) + 2*descriptionBitBound (a+d) + 1) +
          17*descriptionBitBound (a+d)) ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  let root := c.outputs 0
  let S := needInputs c.program root false \ stopInputs c.program root
  have h0 := mcspSquare_constant_table (a+d) (by omega) false
  have h1 := mcspSquare_constant_table (a+d) (by omega) true
  have hSparse := card_accepting_mcspSquare_le (a+d)
  have hc0 := (congrFun (hc (fun _ => false)) 0).trans h0
  have hc1 := (congrFun (hc (fun _ => true)) 0).trans h1
  change cornerValue c.program false root = true at hc0
  change cornerValue c.program true root = true at hc1
  have h0N := card_needInputs_ge_of_sparse c hc hSparse false h0
  have h1N := card_needInputs_ge_of_sparse c hc hSparse true h1
  have hPart := needInputs_add_slack_eq c.program root hc0 hc1
  have hStop := card_stopInputs_and_roots_le_tight c hc hSparse h0 h1
  have hBase : (needInputs c.program root false).card ≤ S.card +
      (stopInputs c.program root).card := by
    apply le_trans (Finset.card_le_card (t := S ∪ stopInputs c.program root) ?_)
      (Finset.card_union_le _ _)
    intro i hi
    by_cases hs : i ∈ stopInputs c.program root
    · exact Finset.mem_union_right _ hs
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi, hs⟩)
  have hPow (k : ℕ) (hk : 13 ≤ k) : 8192 ≤ 2^k :=
    Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hk
  have hN : 8192 ≤ 2^(a+d) := hPow _ (by omega)
  have hB : 8192*descriptionBitBound (a+d) ≤ 2^(a+d) := calc
    _ ≤ 2^d*2^a := Nat.mul_le_mul (hPow d hd) hDescription.le
    _ = _ := by rw [Nat.mul_comm, ← pow_add]
  have hLoss : 8192*2^(d-1) ≤ 2^(a+d) := calc
    _ ≤ 2^a*2^d := Nat.mul_le_mul (hPow a ha) (Nat.pow_le_pow_right (by decide) (by omega))
    _ = _ := (pow_add ..).symm
  dsimp only [root] at hPart hBase
  have hDense : 2^(a+d) ≤ 8*S.card := by omega
  obtain ⟨p, hp⟩ := exists_dense_block S hDense
  let Q := S.filter (fun i => tag i = p)
  have hSubset : Q ⊆ block (d := d) p := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hReads (i) (hi : i ∈ Q) : ∃ j ∈ cleanGates c.program root,
      ∃ k, (c.program.lines j).wires k = .input i := by
    have hs := Finset.mem_sdiff.mp (Finset.mem_filter.mp hi).1
    exact need_input_has_clean_reader hc0 hc1 hs.1 hs.2
  have hFew : descriptionBitBound (a+d) < 2^(a+d) :=
    hDescription.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_add_right a d))
  obtain ⟨x, hCount, hForest, hBudget⟩ := block_losses_and_residual_of_readers tree_lookup_bound c hc hMin
    (by omega) hFew hRepair p Q (cleanGates c.program root) hSubset hReads
  have hp' : 2^d ≤ 8*Q.card := hp
  refine ⟨p, x, ?_, hForest, hBudget⟩
  change 2^d ≤ 16*(cleanGates c.program root ∩
    (fresh c.program Sum.inl \ fresh c.program (pinAt x (block (d := d) p)))).card
  omega

/-- The half-block charge is added to the original quadratic forest inequality. -/
theorem mcspSquare_block_pinning {k : ℕ}
    (hLookup : ∀ g : BooleanFunction d, complexity interpretation (single g) ≤ k) (hd : 1 ≤ d) (hm : 5 ≤ a+d)
    (hDescription : descriptionBitBound (a+d) < 2^a)
    (hRepair : 6*(a+d) + k + 49 ≤ (a+d)^2) :
    280*(2*2^(a+d) + 2^(d-1)) + 2*2^(a+d) ≤
      280*(complexity interpretation (single (mcspSquare (a+d))) +
        2*descriptionBitBound (a+d) + 1) + 17*descriptionBitBound (a+d) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare (a+d)))
  obtain ⟨p, x, _, hCount, hForest, hBudget⟩ :=
    original_block_losses_and_residual hLookup c hc hSize hm hDescription hRepair
  have hSub := Finset.card_le_card
    (Finset.inter_subset_right (s₁ := readerGates c.program (c.outputs 0))
      (s₂ := fresh c.program Sum.inl \ fresh c.program (pinAt x (block (d := d) p))))
  have hPow : 2^d = 2*2^(d-1) := calc
    _ = 2^(d-1+1) := congrArg (fun n : ℕ => 2^n) (by omega)
    _ = _ := pow_succ' _ _
  rw [hPow] at hCount
  omega

end BlockLowerBound

section Scaling

def blockDimension (m : ℕ) : ℕ := 2*m.log2-3

def blockLoss (m : ℕ) : ℕ := 2^(blockDimension m-1)

private theorem log_room (m : ℕ) (hm : 256 ≤ m) : 8 ≤ m.log2 ∧ 32*m.log2 ≤ m := by
  have hn : m ≠ 0 := by omega
  have hLog : 8 ≤ m.log2 := (Nat.le_log2 hn).mpr hm
  have hPow (k : ℕ) (hk : 8 ≤ k) : 32*k ≤ 2^k := by
    refine Nat.le_induction (m := 8) (P := fun j _ => 32*j ≤ 2^j) (by decide) ?_ k hk
    intro j hj ih
    rw [pow_succ']
    omega
  exact ⟨hLog, (hPow m.log2 hLog).trans (Nat.log2_self_le hn)⟩

private theorem description_lt_pow_of_half (m a : ℕ) (hm : 256 ≤ m) (h128 : 128 ≤ a)
    (hHalf : m ≤ 2*a) : descriptionBitBound m < 2^a := by
  calc
    _ ≤ (4*m+12)*m^2 := description_le_polynomial m (by omega)
    _ ≤ (5*m)*m^2 := Nat.mul_le_mul_right _ (by omega)
    _ = 5*m^3 := by ring
    _ ≤ 5*(2*a)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHalf 3)
    _ = 40*a^3 := by ring
    _ < a*a^3 := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega : 0 < a))
    _ = a^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp a (by omega)

private theorem block_schedule (m : ℕ) (hm : 256 ≤ m) :
    let d := blockDimension m
    1 ≤ d ∧ d ≤ m ∧ descriptionBitBound m < 2^(m-d) ∧
      6*m + 5*2^d + 49 ≤ m^2 := by
  let d := blockDimension m
  let a := m-d
  let h := m.log2
  change 1 ≤ d ∧ d ≤ m ∧ descriptionBitBound m < 2^a ∧ 6*m + 5*2^d + 49 ≤ m^2
  obtain ⟨h8, hRoom⟩ := log_room m hm
  have hd : d = 2*h-3 := rfl
  have h128 : 128 ≤ a := by dsimp only [a]; omega
  have hHalf : m ≤ 2*a := by dsimp only [a]; omega
  have hDesc := description_lt_pow_of_half m a hm h128 hHalf
  have hPow : 8*2^d ≤ m^2 := calc
    _ = 2^(d+3) := by rw [pow_add]; simp only [show (2:ℕ)^3 = 8 by decide, Nat.mul_comm]
    _ = 2^(h*2) := congrArg (fun j : ℕ => 2^j) (by omega)
    _ = (2^h)^2 := pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left (Nat.log2_self_le (by omega : m ≠ 0)) 2
  have hFixed : 80*m ≤ 3*m^2 := calc
    _ ≤ (3*m)*m := Nat.mul_le_mul_right m (by omega)
    _ = _ := by ring
  exact ⟨by omega, by omega, hDesc, by omega⟩

/-- The schedule gives a quadratic additive term in the represented arity. -/
theorem square_lt_sixtyfour_blockLoss {m : ℕ} (hm : 256 ≤ m) : m^2 < 64*blockLoss m := by
  have h := (log_room m hm).1
  calc
    _ < (2^(m.log2+1))^2 := Nat.pow_lt_pow_left (Nat.lt_log2_self (n := m)) (by decide)
    _ = 2^((m.log2+1)*2) := (pow_mul _ _ _).symm
    _ = 2^(blockDimension m-1+6) := congrArg (fun j : ℕ => 2^j) (by unfold blockDimension; omega)
    _ = _ := by rw [pow_add]; simp only [blockLoss, show (2:ℕ)^6 = 64 by decide, Nat.mul_comm]

theorem scaledPins_lt_blockLoss {m : ℕ} (hm : 256 ≤ m) :
    scaledPins m < blockLoss m := by
  have hScale : 2*scaledPins m ≤ m*m.log2 := by unfold scaledPins; omega
  have h : 64*scaledPins m ≤ m^2 := calc
    _ = 32*(2*scaledPins m) := by ring
    _ ≤ 32*(m*m.log2) := Nat.mul_le_mul_left _ hScale
    _ = (32*m.log2)*m := by ring
    _ ≤ m*m := Nat.mul_le_mul_right m (log_room m hm).2
    _ = _ := (pow_two m).symm
  have hh := square_lt_sixtyfour_blockLoss hm
  omega

/-- There is an address block of dimension `blockDimension m` contained
in the wired certificate, paying for the new losses outside the residual. -/
theorem mcspSquare_structured_pinning {m : ℕ} (hm : 256 ≤ m) :
    280*(2*2^m + blockLoss m) + 2*2^m ≤
      280*(complexity interpretation (single (mcspSquare m)) +
        2*descriptionBitBound m + 1) + 17*descriptionBitBound m := by
  obtain ⟨hd, hdM, hDesc, hRepair⟩ := block_schedule m hm
  let d := blockDimension m
  have he : m-d+d = m := Nat.sub_add_cancel hdM
  have h := mcspSquare_block_pinning (a := m-d) (d := d) tree_lookup_bound hd
    (by rw [he]; omega) (by rwa [he]) (by rwa [he])
  rw [he] at h
  exact h

/-- Shannon synthesis supports about `m² log₂ m` addresses on one block. -/
def shannonBlockDimension (m : ℕ) : ℕ := 2*m.log2 + m.log2.log2 - 5

def shannonBlockLoss (m : ℕ) : ℕ := 2^(shannonBlockDimension m-1)

private theorem shannon_lookup_bound {d : ℕ} (hd : 16 ≤ d) (f : BooleanFunction d) :
    complexity interpretation (single f) ≤ 27*2^d/d := by
  obtain ⟨c, hc, hSize⟩ := Boolean.ShannonSynthesis.exists_circuit hd f
  exact (complexity_le_of_computes c hc).trans hSize

private theorem shannon_block_schedule (m : ℕ) (hm : 1024 ≤ m) :
    let d := shannonBlockDimension m
    16 ≤ d ∧ d ≤ m ∧ descriptionBitBound m < 2^(m-d) ∧
      6*m + 27*2^d/d + 49 ≤ m^2 := by
  let h := m.log2
  let j := h.log2
  let d := shannonBlockDimension m
  let a := m-d
  change 16 ≤ d ∧ d ≤ m ∧ descriptionBitBound m < 2^a ∧ 6*m + 27*2^d/d + 49 ≤ m^2
  have h10 : 10 ≤ h := (Nat.le_log2 (by omega : m ≠ 0)).mpr hm
  have hj : j ≤ h := Nat.log2_le_self h
  have hj3 : 3 ≤ j := (Nat.le_log2 (by omega : h ≠ 0)).mpr (by omega)
  have hd : d = 2*h+j-5 := rfl
  have hRoom := (log_room m (by omega)).2
  change 32*h ≤ m at hRoom
  have h128 : 128 ≤ a := by dsimp only [a]; omega
  have hHalf : m ≤ 2*a := by dsimp only [a]; omega
  have hDesc := description_lt_pow_of_half m a (by omega) h128 hHalf
  have hPow : 32*2^d ≤ m^2*h := calc
    _ = 2^(d+5) := by rw [pow_add]; simp only [show (2:ℕ)^5 = 32 by decide, Nat.mul_comm]
    _ = 2^(h*2+j) := congrArg (fun k : ℕ => 2^k) (by omega)
    _ = (2^h)^2*2^j := by rw [pow_add, pow_mul]
    _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.log2_self_le (by omega : m ≠ 0)) 2)
      (Nat.log2_self_le (by omega : h ≠ 0))
  let lookup := 27*2^d/d
  have hLookup : 32*lookup ≤ 27*m^2 := by
    apply (Nat.mul_le_mul_right_iff (by omega : 0 < d)).mp
    calc
      (32*lookup)*d = 32*(lookup*d) := by ring
      _ ≤ 32*(27*2^d) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = 27*(32*2^d) := by ring
      _ ≤ 27*(m^2*h) := Nat.mul_le_mul_left _ hPow
      _ ≤ 27*(m^2*d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  have hFixed : 200*m ≤ 5*m^2 := calc
    _ ≤ (5*m)*m := Nat.mul_le_mul_right m (by omega)
    _ = _ := by ring
  have hBudget : 6*m + lookup + 49 ≤ m^2 := by omega
  exact ⟨by omega, by omega, hDesc, hBudget⟩

theorem arity_sq_log_lt_shannonBlockLoss {m : ℕ} (hm : 1024 ≤ m) :
    m^2*m.log2 < 512*shannonBlockLoss m := by
  let h := m.log2
  let j := h.log2
  have h8 : 8 ≤ h := (log_room m (by omega)).1
  have hPos : 0 < h := by omega
  have hDim : shannonBlockDimension m = 2*h+j-5 := rfl
  change m^2*h < 512*shannonBlockLoss m
  calc
    _ < (2^(h+1))^2*h := Nat.mul_lt_mul_of_pos_right
      (Nat.pow_lt_pow_left (Nat.lt_log2_self (n := m)) (by decide)) hPos
    _ ≤ (2^(h+1))^2*2^(j+1) := Nat.mul_le_mul_left _ (Nat.lt_log2_self (n := h)).le
    _ = 2^((h+1)*2+(j+1)) := by rw [pow_add 2 ((h+1)*2) (j+1), pow_mul 2 (h+1) 2]
    _ = 2^(shannonBlockDimension m-1+9) := congrArg (fun k : ℕ => 2^k) (by omega)
    _ = _ := by rw [pow_add]; simp only [shannonBlockLoss, show (2:ℕ)^9 = 512 by decide, Nat.mul_comm]

/-- The shared-column lookup yields an additive `Ω(m² log₂ m)` charge
over the full quadratic forest bound. -/
theorem mcspSquare_shannon_block_pinning {m : ℕ} (hm : 1024 ≤ m) :
    280*(2*2^m + shannonBlockLoss m) + 2*2^m ≤
      280*(complexity interpretation (single (mcspSquare m)) +
        2*descriptionBitBound m + 1) + 17*descriptionBitBound m := by
  obtain ⟨hd, hdM, hDesc, hRepair⟩ := shannon_block_schedule m hm
  let d := shannonBlockDimension m
  have he : m-d+d = m := Nat.sub_add_cancel hdM
  have h := mcspSquare_block_pinning (a := m-d) (d := d) (shannon_lookup_bound hd)
    (by omega) (by rw [he]; omega) (by rwa [he]) (by rwa [he])
  rw [he] at h
  exact h

end Scaling

theorem minterm_bank_size_le (n : ℕ) : (mintermCircuit n).size ≤ 3*2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    let e : Bool × BitString n ≃ Fin (2^(n+1)) :=
      (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).trans (BitString.equivFin (n+1))
    have hExt (p : Bool × BitString n) :
        (mintermExtension n (e p)).size = if p.1 then 1 else 2 := by
      rcases p with ⟨b, z⟩
      cases b <;> simp [e, mintermExtension, Formula.size_and, Formula.size_not, Formula.size_input]
    have hSum : (∑ a : Fin (2^(n+1)), (mintermExtension n a).size) = 3*2^n := calc
      _ = ∑ p : Bool × BitString n, (mintermExtension n (e p)).size :=
        (Equiv.sum_comp e (fun a => (mintermExtension n a).size)).symm
      _ = ∑ p : Bool × BitString n, (if p.1 then 1 else 2) :=
        Finset.sum_congr rfl (fun p _ => hExt p)
      _ = _ := by
        rw [Fintype.sum_prod_type, Fintype.sum_bool]
        simp only [Bool.false_eq_true, ite_false, ite_true, Finset.sum_const, smul_eq_mul,
          Finset.card_univ, BitString.card, Nat.mul_one]
        omega
    simp only [mintermCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
      Circuit.size_pi, Formula.size_toCircuit, Nat.add_zero]
    rw [hSum, pow_succ']
    omega

set_option maxRecDepth 4096 in
private theorem nine_bit_lookup_bound (f : BooleanFunction 9) :
    complexity interpretation (single f) ≤ 760 := by
  let C := ShannonSynthesis.circuit (k := 2) (d := 7) f
  have hc : C.Computes interpretation (single f) := by
    intro x
    funext i
    exact ShannonSynthesis.eval_circuit (k := 2) (d := 7) f x i
  have hData : (ShannonSynthesis.splitMinterms 2 7).size ≤ 440 := by
    simp only [ShannonSynthesis.splitMinterms, Circuit.size_append, Circuit.size_comp,
      Circuit.size_wiring]
    exact (Nat.add_le_add (minterm_bank_size_le 2) (minterm_bank_size_le 7)).trans (by decide)
  have hLib : (ShannonSynthesis.libraryAndData 2 7).size ≤ 64 := by
    simp only [ShannonSynthesis.libraryAndData, Circuit.size_append, Circuit.size_comp,
      Circuit.size_wiring, Nat.add_zero, Nat.zero_add]
    exact (ShannonSynthesis.size_columnLibrary_le 2).trans (by decide)
  have hOut : (ShannonSynthesis.outputFormula (k := 2) (d := 7) f).size ≤ 256 :=
    ShannonSynthesis.size_outputFormula_le (k := 2) (d := 7) f
  have hSize : C.size ≤ 760 := by
    simp only [C, ShannonSynthesis.circuit, Circuit.size_comp, Formula.size_toCircuit]
    omega
  exact (complexity_le_of_computes C hc).trans hSize

/-- At arity 32 a nine-bit block pays for 256 distinct original gates. -/
theorem mcspSquare_32_forest_block :
    8620556161 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := mcspSquare_block_pinning (a := 23) (d := 9) nine_bit_lookup_bound
    (by decide) (by decide) (by decide) (by decide)
  rw [show (23:ℕ)+9 = 32 by decide, show descriptionBitBound 32 = 27672 by decide] at h
  norm_num at h
  omega

/-- A fixed set supporting every assignment to its pins must fit the
description bound, even when only the zero probe is being repaired. -/
theorem fixed_pin_capacity {m : ℕ} (P : Finset (Fin (2^m)))
    (hRepair : ∀ x : BitString (2^m),
      mcspSquare m (substitute (pinAt x P) (fun _ => false)) = true) :
    P.card ≤ descriptionBitBound m := by
  let fill (u : P → Bool) (i : Fin (2^m)) := if hi : i ∈ P then u ⟨i, hi⟩ else false
  have hAccept (u : P → Bool) : mcspSquare m (fill u) = true := by
    have h := hRepair (fill u)
    have he : substitute (pinAt (fill u) P) (fun _ => false) = fill u := by
      funext i
      by_cases hi : i ∈ P <;> simp [pinAt, substitute, fill, hi]
    rwa [he] at h
  let into (u : P → Bool) : acceptingTables (mcspSquare m) :=
    ⟨fill u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAccept u⟩⟩
  have hInj : Function.Injective into := by
    intro u v h
    funext i
    have he := congrFun (congrArg Subtype.val h) i.val
    simpa only [into, fill, i.property, dite_true] using he
  have hCard := Fintype.card_le_of_injective into hInj
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_coe] at hCard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (hCard.trans (card_accepting_mcspSquare_le m))

#print axioms accepted_after_block_pin
#print axioms original_block_losses_and_residual
#print axioms original_clean_block_losses_and_residual
#print axioms square_lt_sixtyfour_blockLoss
#print axioms scaledPins_lt_blockLoss
#print axioms mcspSquare_structured_pinning
#print axioms arity_sq_log_lt_shannonBlockLoss
#print axioms mcspSquare_shannon_block_pinning
#print axioms mcspSquare_32_forest_block
#print axioms fixed_pin_capacity

end PvsNP.Frontier.ForestBlockPinning
