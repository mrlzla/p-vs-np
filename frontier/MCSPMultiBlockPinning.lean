module

public import MCSPForestBlockPinning

/-! Joint pinning of many address blocks with one shared column library.
The union of lost original indices is charged against one common residual. -/

@[expose] public section

namespace PvsNP.Frontier.MultiBlockPinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure ForestPinning ForestBlockPinning
open RestrictionCharges FreshCharges NestedFaces QuadraticForest QuadraticPinning
open scoped Classical BigOperators

section Blocks

variable {a d : ℕ}

/-- All addresses whose prefix belongs to the chosen set of blocks. -/
noncomputable def blocks (E : Finset (BitString a)) : Finset (Fin (2^(a+d))) :=
  Finset.univ.filter fun i => tag i ∈ E

theorem card_blocks (E : Finset (BitString a)) : (blocks (d := d) E).card = E.card*2^d := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin (2^(a+d)))) E tag
  change (∑ p ∈ E, (block (d := d) p).card) = (blocks (d := d) E).card at h
  simp only [card_block, Finset.sum_const, smul_eq_mul] at h
  exact h.symm

/-- A missing address can exclude only the block containing it. -/
theorem exists_covered_blocks (S : Finset (Fin (2^(a+d)))) (r : ℕ)
    (hS : r + ((Finset.univ : Finset _) \ S).card ≤ 2^a) :
    ∃ E : Finset (BitString a), E.card = r ∧ blocks (d := d) E ⊆ S := by
  let bad := ((Finset.univ : Finset _) \ S).image tag
  let good := Finset.univ \ bad
  have hb : bad.card ≤ ((Finset.univ : Finset _) \ S).card := Finset.card_image_le
  have hg := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  rw [Finset.card_univ, BitString.card] at hg
  have hr : r ≤ good.card := by
    dsimp only [good]
    omega
  obtain ⟨E, hE, hCard⟩ := Finset.exists_subset_card_eq hr
  refine ⟨E, hCard, ?_⟩
  intro i hi
  by_contra hmiss
  have he := hE ((Finset.mem_filter.mp hi).2)
  exact (Finset.mem_sdiff.mp he).2
    (Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hmiss⟩, rfl⟩)

end Blocks

section Capacity

/-- A single accepting padded residual is already a cube on its pinned coordinates.
The bound applies even if the pin values were selected adaptively. -/
theorem padded_pin_capacity {n B : ℕ} (f : BooleanFunction n) (P : Finset (Fin n))
    (x y : BitString n) (hYes : f (substitute (pinAt x P) y) = true)
    (hSparse : (acceptingTables fun z => f (substitute (pinAt x P) z)).card ≤ 2^B) :
    P.card ≤ B := by
  let g : BooleanFunction n := fun z => f (substitute (pinAt x P) z)
  let fill (u : P → Bool) (i : Fin n) := if h : i ∈ P then u ⟨i,h⟩ else y i
  have hFill (u : P → Bool) : substitute (pinAt x P) (fill u) = substitute (pinAt x P) y := by
    funext i
    by_cases hi : i ∈ P <;> simp [substitute, pinAt, fill, hi]
  let into (u : P → Bool) : acceptingTables g :=
    ⟨fill u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      change f (substitute (pinAt x P) (fill u)) = true
      rwa [hFill]⟩⟩
  have hInj : Function.Injective into := by
    intro u v he
    funext i
    have e := congrFun (congrArg Subtype.val he) i.val
    simpa only [into, fill, i.property, dite_true] using e
  have hCard := Fintype.card_le_of_injective into hInj
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_coe] at hCard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hCard.trans hSparse)

/-- Whole-block pinning with one nonempty sparse padded residual pays for
at most `B` addressed positions across all its blocks. -/
theorem padded_block_capacity {a d B : ℕ} (f : BooleanFunction (2^(a+d)))
    (E : Finset (BitString a)) (x y : BitString (2^(a+d)))
    (hYes : f (substitute (pinAt x (blocks (d := d) E)) y) = true)
    (hSparse : (acceptingTables fun z => f (substitute (pinAt x (blocks (d := d) E)) z)).card ≤ 2^B) :
    E.card*2^d ≤ B := by
  rw [← card_blocks]
  exact padded_pin_capacity f _ x y hYes hSparse

/-- A proof selecting one original reader per pin has at most `B` indices
to charge while using the nonempty sparse padded residual. -/
theorem selected_readers_le_padded_capacity {n g B : ℕ} (f : BooleanFunction n)
    (P : Finset (Fin n)) (reader : Fin n → Fin g) (x y : BitString n)
    (hYes : f (substitute (pinAt x P) y) = true)
    (hSparse : (acceptingTables fun z => f (substitute (pinAt x P) z)).card ≤ 2^B) :
    (P.image reader).card ≤ B :=
  Finset.card_image_le.trans (padded_pin_capacity f P x y hYes hSparse)

end Capacity

section SharedLookup

open ShannonSynthesis (libraryAndData splitMinterms outputFormula)

def lookupBankCost (k l : ℕ) : ℕ := 3*2^k + 3*2^l + 2^(2^k)*2^k

/-- Every suffix lookup uses the same minterms and column-library gates. -/
theorem synth_suffix_lookups {I : Type} [Fintype I] {a k l : ℕ}
    (f : I → BooleanFunction (k+l)) :
    Synthesis interpretation (inputs (a+(k+l)))
      (Set.range fun i : I => fun z => f i (addressTail a z))
      (lookupBankCost k l + Fintype.card I*(2*2^l)) := by
  let n := a+(k+l)
  let pre := (libraryAndData k l).comp (splitMinterms k l)
  let C := pre.comp (Circuit.wiring signature (Fin.natAdd a : Fin (k+l) → Fin n))
  let wire (j : Fin (2^(2^k)+2^l)) (z : BitString n) := C.eval interpretation z j
  let bank := Set.range wire
  have hMin : (splitMinterms k l).size ≤ 3*2^k + 3*2^l := by
    simp only [splitMinterms, Circuit.size_append, Circuit.size_comp, Circuit.size_wiring]
    rw [Nat.zero_add, Nat.zero_add]
    exact Nat.add_le_add (minterm_bank_size_le k) (minterm_bank_size_le l)
  have hLib : (libraryAndData k l).size ≤ 2^(2^k)*2^k := by
    simpa only [libraryAndData, Circuit.size_append, Circuit.size_comp, Circuit.size_wiring,
      Nat.add_zero, Nat.zero_add] using ShannonSynthesis.size_columnLibrary_le k
  have hSize : C.size ≤ lookupBankCost k l := by
    simp only [C, pre, Circuit.size_comp, Circuit.size_wiring, Nat.zero_add, lookupBankCost]
    omega
  have hRaw := Synthesis.circuit (I := interpretation) (s := inputs n) C (fun i z => z i)
    (fun i => ⟨i, rfl⟩)
  have hBank : Synthesis interpretation (inputs n) bank (lookupBankCost k l) :=
    hRaw.mono Set.Subset.rfl Set.Subset.rfl hSize
  let g (i : I) (z : BitString n) := f i (addressTail a z)
  have hOne (i : I) : Synthesis interpretation (inputs n ∪ bank) {g i} (2*2^l) := by
    let out := (outputFormula (k := k) (d := l) (f i)).toCircuit
    have hs := Synthesis.circuit (I := interpretation) (s := inputs n ∪ bank) out wire
      (fun j => Or.inr ⟨j, rfl⟩)
    have hout : out.size ≤ 2*2^l := by
      simpa only [out, Formula.size_toCircuit] using ShannonSynthesis.size_outputFormula_le (f i)
    apply hs.mono Set.Subset.rfl ?_ hout
    rintro _ rfl
    refine ⟨0, funext fun z => ?_⟩
    have he := ShannonSynthesis.eval_circuit (k := k) (d := l) (f i) (addressTail a z) 0
    simp only [out, wire, C, pre, g, addressTail, ShannonSynthesis.circuit, Circuit.eval_comp,
      Circuit.eval_wiring] at he ⊢
    exact he
  have hAll : Synthesis interpretation (inputs n ∪ bank) (Set.range g) (Fintype.card I*(2*2^l)) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ] using
      Synthesis.family g (fun _ => 2*2^l) hOne
  exact hBank.trans hAll

variable {a k l : ℕ}

/-- Repair all disjoint selected blocks using a single shared bank of
suffix lookups. Only the row-disjunction and prefix tests are per block. -/
theorem accepted_after_blocks_pin (E : Finset (BitString a)) (x : BitString (2^(a+(k+l))))
    (f : BooleanFunction (a+(k+l)))
    (hBudget : complexity interpretation (single f) +
      lookupBankCost k l + E.card*(2*2^l+2*a+3) + 5 ≤ (a+(k+l))^2) :
    mcspSquare (a+(k+l)) (substitute (pinAt x (blocks (d := k+l) E)) (MCSP.truthTable _ f)) = true := by
  let m := a+(k+l)
  let fix (p : E) (u : BitString (k+l)) :=
    f (Fin.append p.val u) ^^ x (BitString.equivFin m (Fin.append p.val u))
  let lookup (p : E) (z : BitString m) := fix p (addressTail a z)
  let term (p : E) (z : BitString m) := prefixMatch p.val z && lookup p z
  let correction (z : BitString m) := decide (∃ p : E, term p z = true)
  let bank := Set.range lookup
  have hLook : Synthesis interpretation (inputs m) bank (lookupBankCost k l + E.card*(2*2^l)) := by
    simpa only [Fintype.card_coe] using synth_suffix_lookups (a := a) fix
  have hTerm (p : E) : Synthesis interpretation (inputs m ∪ bank) {term p} (2*a+2) := by
    have hTag : Synthesis interpretation (inputs m ∪ bank) {prefixMatch (d := k+l) p.val} (2*a+1) :=
      (synthesis_prefix_match p.val).mono Set.subset_union_left Set.Subset.rfl le_rfl
    have hFix : Synthesis interpretation (inputs m ∪ bank) {lookup p} 0 :=
      Synthesis.of_mem (Or.inr ⟨p, rfl⟩)
    exact hTag.and hFix
  have hOr := Synthesis.exists_mem (Finset.univ : Finset E) term (fun _ => 2*a+2) (fun p _ => hTerm p)
  have hs := Synthesis.congr_iff hOr (g := correction) (fun z => by
    simp only [correction, decide_eq_true_eq, Finset.mem_univ, true_and])
  have hCost := (hLook.trans hs).complexity_le
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe] at hCost
  have hDec (z : BitString m) : correction z = true ↔
      ∃ p : E, addressHead (k+l) z = p.val ∧ lookup p z = true := by
    simp only [correction, decide_eq_true_eq, term, Bool.and_eq_true, prefixMatch]
  have hCorrect : MCSP.truthTable m (fun z => f z ^^ correction z) =
      substitute (pinAt x (blocks (d := k+l) E)) (MCSP.truthTable m f) := by
    funext i
    let z := (BitString.equivFin m).symm i
    simp only [MCSP.truthTable_apply]
    change (f z ^^ correction z) = substitute (pinAt x (blocks (d := k+l) E)) (MCSP.truthTable m f) i
    by_cases hi : i ∈ blocks (d := k+l) E
    · have hp : addressHead (k+l) z ∈ E := (Finset.mem_filter.mp hi).2
      let p : E := ⟨addressHead (k+l) z, hp⟩
      have hCorr : correction z = lookup p z := by
        apply Bool.eq_iff_iff.mpr
        rw [hDec]
        constructor
        · rintro ⟨q, hq, hVal⟩
          have he : q = p := Subtype.ext hq.symm
          exact he ▸ hVal
        · exact fun h => ⟨p, rfl, h⟩
      have hAppend : Fin.append p.val (addressTail a z) = z := append_prefix_suffix z
      rw [substitute_inr (show pinAt x (blocks (d := k+l) E) i = .inr (x i) by simp [pinAt, hi])]
      simp only [hCorr, lookup, fix, hAppend, z, Equiv.apply_symm_apply]
      cases f ((BitString.equivFin m).symm i) <;> cases x i <;> rfl
    · have hp : addressHead (k+l) z ∉ E := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have hCorr : correction z = false := Bool.eq_false_of_not_eq_true fun ht => by
        obtain ⟨p, he, _⟩ := (hDec z).mp ht
        exact hp (he.symm ▸ p.property)
      rw [substitute_inl (show pinAt x (blocks (d := k+l) E) i = .inl i by simp [pinAt, hi])]
      simp only [hCorr, Bool.xor_false, z, MCSP.truthTable_apply]
  rw [← hCorrect, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  have hC := complexity_xor_le f correction
  have hTotal : lookupBankCost k l + E.card*(2*2^l) + (E.card*(2*a+2+1)+1) =
      lookupBankCost k l + E.card*(2*2^l+2*a+3)+1 := by ring
  rw [hTotal] at hCost
  exact hC.trans (by omega)

end SharedLookup

section LowerBound

variable {a k l r : ℕ}

/-- Choose several covered address blocks from the actual wired certificate.
The proof counts their losses in the set difference for a single joint
restriction, with the full forest inequality on the one surviving circuit. -/
theorem original_multi_block_losses_and_residual
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l)))))
    (hr : 0 < r) (hm : 1 ≤ a+(k+l))
    (hRoom : r + descriptionBitBound (a+(k+l)) ≤ 2^a)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2) :
    ∃ (E : Finset (BitString a)) (x : BitString (2^(a+(k+l)))),
      E.card = r ∧ blocks (d := k+l) E ⊆ needInputs c.program (c.outputs 0) false ∧
      let P := blocks (d := k+l) E
      let f : BooleanFunction (2^(a+(k+l))) := fun y => mcspSquare (a+(k+l)) (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      r*2^(k+l) ≤ 2*(readerGates c.program (c.outputs 0) ∩ removed).card ∧
      (280*(2*2^(a+(k+l))) + 2*2^(a+(k+l)) ≤
        280*(complexity interpretation (single f) + 2*descriptionBitBound (a+(k+l)) + 1) +
          17*descriptionBitBound (a+(k+l))) ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  let m := a+(k+l)
  let root := c.outputs 0
  let S := needInputs c.program root false
  have hFew : descriptionBitBound m < 2^m :=
    (show descriptionBitBound m < 2^a by dsimp only [m]; omega).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (Nat.le_add_right a (k+l)))
  have hSparse := card_accepting_mcspSquare_le m
  have h0 := mcspSquare_constant_table m hm false
  have h1 := mcspSquare_constant_table m hm true
  have hc0 : cornerValue c.program false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue c.program true root = true := (congrFun (hc _) 0).trans h1
  have hNeed : 2^m ≤ S.card+descriptionBitBound m := card_needInputs_ge_of_sparse c hc hSparse false h0
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hMiss
  obtain ⟨E, hE, hCover⟩ := exists_covered_blocks (a := a) (d := k+l) S r (by
    dsimp only [m] at hNeed hMiss
    omega)
  let P := blocks (d := k+l) E
  have hQ (x : BitString (2^m)) (u : BitString m) (v : Bool) (c₁ c₂ : BitString m) :
      mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad u v c₁ c₂))) = true := by
    apply accepted_after_blocks_pin (k := k) (l := l)
    have hCost := complexity_quad_shared_le u v c₁ c₂
    dsimp only [m] at hCost
    rw [hE]
    omega
  obtain ⟨x, hCount, hForest, hBudget⟩ := pin_losses_and_residual_of_readers c hc hMin hm hFew
    P P (readerGates c.program root) (by rfl)
    (fun i hi => need_input_has_reader hc0 hc1 (hCover hi)) hQ
  have hCard : P.card = r*2^(k+l) := (card_blocks E).trans (by rw [hE])
  rw [hCard] at hCount
  exact ⟨E, x, hE, hCover, hCount, hForest, hBudget⟩

theorem mcspSquare_multi_block_pinning (hr : 0 < r) (hd : 1 ≤ k+l) (hm : 1 ≤ a+(k+l))
    (hRoom : r + descriptionBitBound (a+(k+l)) ≤ 2^a)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2) :
    280*(2*2^(a+(k+l)) + r*2^(k+l-1)) + 2*2^(a+(k+l)) ≤
      280*(complexity interpretation (single (mcspSquare (a+(k+l)))) +
        2*descriptionBitBound (a+(k+l)) + 1) + 17*descriptionBitBound (a+(k+l)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare (a+(k+l))))
  obtain ⟨E, x, _, _, hCount, hForest, hBudget⟩ :=
    original_multi_block_losses_and_residual c hc hSize hr hm hRoom hRepair
  have hSub := Finset.card_le_card (Finset.inter_subset_right
    (s₁ := readerGates c.program (c.outputs 0))
    (s₂ := fresh c.program Sum.inl \ fresh c.program (pinAt x (blocks (d := k+l) E))))
  have hPow : r*2^(k+l) = 2*(r*2^(k+l-1)) := calc
    _ = r*2^(k+l-1+1) := by rw [Nat.sub_add_cancel hd]
    _ = _ := by rw [pow_succ']; ring
  rw [hPow] at hCount
  omega

/-- Three separate 256-point blocks share the lookup bank at arity 32.
They pay for at least 384 distinct original readers. -/
theorem mcspSquare_32_three_blocks :
    8620556289 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := mcspSquare_multi_block_pinning (a := 24) (k := 2) (l := 6) (r := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show (24:ℕ)+(2+6) = 32 by decide, show descriptionBitBound 32 = 27672 by decide] at h
  norm_num at h
  omega

end LowerBound

section GrowingBlocks

def multiBlockArity (t : ℕ) : ℕ := 2^(2*t)

def multiBlockLoss (t : ℕ) : ℕ := 2^t * 2^(t.log2+(3*t-2)-1)

theorem multi_block_rows (t : ℕ) (ht : 8 ≤ t) :
    4*(2^t*2^(3*t-2)) = (multiBlockArity t)^2 := calc
  _ = 2^(2+(t+(3*t-2))) := by rw [show (4:ℕ) = 2^2 by decide, ← pow_add, ← pow_add]
  _ = 2^((2*t)*2) := congrArg (fun j : ℕ => 2^j) (by omega)
  _ = _ := pow_mul _ _ _

private theorem growing_block_parameters (t : ℕ) (ht : 8 ≤ t) :
    let m := multiBlockArity t
    let k := t.log2
    let l := 3*t-2
    let a := m-(k+l)
    k+l ≤ m ∧
      2^t+descriptionBitBound m ≤ 2^a ∧
      4*m + 48 + lookupBankCost k l + 2^t*(2*2^l+2*a+3) ≤ m^2 := by
  let m := multiBlockArity t
  let k := t.log2
  let l := 3*t-2
  let a := m-(k+l)
  let r := (2:ℕ)^t
  change k+l ≤ m ∧ r+descriptionBitBound m ≤ 2^a ∧
    4*m + 48 + lookupBankCost k l + r*(2*2^l+2*a+3) ≤ m^2
  have hR : 256 ≤ r := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ht
  have hM : m = r*r := by
    dsimp only [m, multiBlockArity, r]
    rw [show 2*t = t+t by omega, pow_add]
  have hMLarge : 65536 ≤ m := by
    rw [hM]
    exact Nat.mul_le_mul hR hR
  have hTR : t ≤ r := t.lt_two_pow_self.le
  have hRM : r ≤ m := by
    simpa only [Nat.mul_one, ← hM] using Nat.mul_le_mul_left r (by omega : 1 ≤ r)
  have hk : k ≤ t := Nat.log2_le_self t
  have hl : l = 3*t-2 := rfl
  have hd : 2*(k+l) ≤ m := calc
    _ ≤ 8*r := by omega
    _ ≤ r*r := Nat.mul_le_mul_right r (by omega)
    _ = _ := hM.symm
  have hHalf : m ≤ 2*a := by dsimp only [a]; omega
  have h128 : 128 ≤ a := by omega
  have hSelf : m ≤ m^3 := calc
    _ = m*1 := by simp
    _ ≤ m*m^2 := Nat.mul_le_mul_left _ (Nat.pow_pos (by omega))
    _ = _ := by ring
  have hDesc : r + descriptionBitBound m ≤ 2^a := calc
    _ ≤ m + (4*m+12)*m^2 := Nat.add_le_add hRM (description_le_polynomial m (by omega))
    _ ≤ m^3 + (5*m)*m^2 := Nat.add_le_add hSelf (Nat.mul_le_mul_right _ (by omega))
    _ = 6*m^3 := by ring
    _ ≤ 6*(2*a)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHalf 3)
    _ = 48*a^3 := by ring
    _ ≤ a*a^3 := Nat.mul_le_mul_right _ (by omega)
    _ = a^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp a (by omega)
  have hRows : 4*(r*2^l) = m^2 := multi_block_rows t ht
  have hL : 3*2^l ≤ r*2^l := Nat.mul_le_mul_right (2^l) (by omega)
  have hRowsCost : 32*(3*2^l+2*(r*2^l)) ≤ 24*m^2 := by omega
  have hK : 2^k ≤ t := Nat.log2_self_le (by omega : t ≠ 0)
  have hLib : 2^(2^k)*2^k ≤ m :=
    (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hK) (hK.trans hTR)).trans_eq hM.symm
  have hBase : 32*(4*m+48+3*2^k+2^(2^k)*2^k) ≤ m^2 := calc
    _ ≤ 288*m := by omega
    _ ≤ m*m := Nat.mul_le_mul_right _ (by omega)
    _ = _ := (pow_two m).symm
  have h24 : 24*r ≤ m := (Nat.mul_le_mul_right r (by omega : 24 ≤ r)).trans_eq hM.symm
  have hA : a ≤ m := Nat.sub_le ..
  have hPrefix : 32*(r*(2*a+3)) ≤ 4*m^2 := calc
    _ ≤ 32*(r*(3*m)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = (4*(24*r))*m := by ring
    _ ≤ (4*m)*m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h24)
    _ = _ := by ring
  refine ⟨by omega, hDesc, ?_⟩
  unfold lookupBankCost
  rw [show r*(2*2^l+2*a+3) = 2*(r*2^l)+r*(2*a+3) by ring]
  omega

/-- The growing family jointly pins `2^t` blocks at arity `2^(2*t)`. -/
theorem mcspSquare_growing_blocks (t : ℕ) (ht : 8 ≤ t) :
    280*(2*2^(multiBlockArity t) + multiBlockLoss t) + 2*2^(multiBlockArity t) ≤
      280*(complexity interpretation (single (mcspSquare (multiBlockArity t))) +
        2*descriptionBitBound (multiBlockArity t) + 1) + 17*descriptionBitBound (multiBlockArity t) := by
  obtain ⟨hd, hRoom, hRepair⟩ := growing_block_parameters t ht
  let m := multiBlockArity t
  let k := t.log2
  let l := 3*t-2
  let a := m-(k+l)
  have he : a+(k+l) = m := Nat.sub_add_cancel hd
  have hk : 1 ≤ k+l := by dsimp only [l]; omega
  have hm : 1 ≤ m := Nat.two_pow_pos _
  have h := mcspSquare_multi_block_pinning (a := a) (k := k) (l := l) (r := 2^t)
    (Nat.two_pow_pos t) hk (by rwa [he]) (by rwa [he]) (by rwa [he])
  rw [he] at h
  exact h

theorem arity_sq_log_lt_multiBlockLoss (t : ℕ) (ht : 8 ≤ t) :
    (multiBlockArity t)^2 * (multiBlockArity t).log2 < 32*multiBlockLoss t := by
  let l := 3*t-2
  let k := t.log2
  have hLog : (multiBlockArity t).log2 = 2*t := Nat.log2_two_pow
  have hK : t < 2*2^k := by rw [← pow_succ']; exact Nat.lt_log2_self (n := t)
  have hPos : 0 < (2:ℕ)^t * 2^l := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  have hD : 1 ≤ k+l := by dsimp only [l]; omega
  calc
    _ = 8*(2^t*2^l)*t := by rw [hLog, ← multi_block_rows t ht]; ring
    _ < 8*(2^t*2^l)*(2*2^k) := Nat.mul_lt_mul_of_pos_left hK (Nat.mul_pos (by decide) hPos)
    _ = 16*(2^t*(2^k*2^l)) := by ring
    _ = 16*(2^t*2^(k+l)) := by rw [pow_add]
    _ = 32*(2^t*2^(k+l-1)) := by
      have he : 2^(k+l) = 2*2^(k+l-1) := calc
        _ = 2^(k+l-1+1) := congrArg (fun j : ℕ => 2^j) (by omega)
        _ = _ := pow_succ' _ _
      rw [he]
      ring
    _ = _ := rfl
/-- On the scheduled arities the joint charge is four times the previous
single-block guarantee. -/
theorem multiBlockLoss_eq_four_shannonBlockLoss (t : ℕ) (ht : 8 ≤ t) :
    multiBlockLoss t = 4*shannonBlockLoss (multiBlockArity t) := calc
  _ = 2^(t+(t.log2+(3*t-2)-1)) := (pow_add ..).symm
  _ = 2^(2+(shannonBlockDimension (multiBlockArity t)-1)) := by
    apply congrArg (fun n : ℕ => 2^n)
    unfold shannonBlockDimension multiBlockArity
    rw [Nat.log2_two_pow, Nat.log2_two_mul (by omega : t ≠ 0)]
    omega
  _ = _ := by rw [pow_add]; rfl

end GrowingBlocks

#print axioms selected_readers_le_padded_capacity
#print axioms accepted_after_blocks_pin
#print axioms original_multi_block_losses_and_residual
#print axioms mcspSquare_32_three_blocks
#print axioms mcspSquare_growing_blocks
#print axioms arity_sq_log_lt_multiBlockLoss
#print axioms multiBlockLoss_eq_four_shannonBlockLoss

end PvsNP.Frontier.MultiBlockPinning
