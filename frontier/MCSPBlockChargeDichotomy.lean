module

public import MCSPRawReaderNecessity

/-! A raw pair buys a second exit. Its absence makes direct readers
injective in the pinned addresses. Both cases pay in one residual budget. -/

@[expose] public section

namespace PvsNP.Frontier.BlockChargeDichotomy

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest ForestBlockPinning ForestPinning
open RestrictionCharges FreshCharges NestedFaces QuadraticForest DownstreamBlockPinning
open IndependentBlockPinning MultiBlockPinning SecondBlockExits ConstantBlockExits
open ProbePairBarrier RawReaderNecessity
open scoped Classical BigOperators

section JointCharge

variable {a d g : ℕ}

/-- When there is no raw-pair gate in the block, a chosen direct reader
of each of its addresses gives an injection into original gates. -/
theorem direct_count_without_pair (p : Program signature (2^(a+d)) g) (s : BitString a)
    (hNo : ¬ HasRawPair (d := d) p s)
    (hRead : ∀ i ∈ block (d := d) s, ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i) :
    2^d ≤ (directReaders p (block (d := d) s)).card := by
  let P := block (d := d) s
  have take (i : P) : ∃ (j : directReaders p P), ∃ k, (p.lines j.val).wires k = .input i.val := by
    obtain ⟨j,k,hk⟩ := hRead i.val i.property
    exact ⟨⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.val,i.property,k,hk⟩⟩,k,hk⟩
  choose j arg he using take
  have hInj : Function.Injective j := by
    intro i u hEq
    apply Subtype.ext
    by_contra hn
    have hOther : ∃ k, (p.lines (j u).val).wires k = .input u.val := ⟨arg u,he u⟩
    rw [← hEq] at hOther
    obtain ⟨k,hk⟩ := hOther
    have hne : arg i ≠ k := by
      intro h
      exact hn (Wire.input.inj ((h ▸ he i).symm.trans hk))
    exact hNo ⟨(j i).val,arg i,k,hne,i.val,i.property,u.val,u.property,he i,hk⟩
  have hCard := Fintype.card_le_of_injective j hInj
  simpa only [Fintype.card_coe, P, card_block] using hCard

private theorem within_block_subset {E : Finset (BitString a)} {s : BitString a} (hs : s ∈ E) :
    block (d := d) s ⊆ blocks (d := d) E := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.symm ▸ hs⟩

/-- Separate the direct readers of different chosen blocks before adding
their counts. -/
theorem direct_card_sum_of_separated (p : Program signature (2^(a+d)) g)
    (E : Finset (BitString a)) (hSep : Separated p E) :
    (∑ s : E, (directReaders p (block (d := d) s.val)).card) ≤
      (directReaders p (blocks (d := d) E)).card := by
  let I := (Finset.univ : Finset E)
  let D (s : E) := directReaders p (block (d := d) s.val)
  have hDisj : (I : Set E).PairwiseDisjoint D := by
    intro s _ u _ hne
    apply Finset.disjoint_left.mpr
    intro j hs hu
    exact hSep s.val s.property u.val u.property (fun h => hne (Subtype.ext h)) j
      (readerTags_subset_nearby p j (mem_readerTags.mpr hs))
      (readerTags_subset_nearby p j (mem_readerTags.mpr hu))
  have hSub : I.biUnion D ⊆ directReaders p (blocks (d := d) E) := by
    intro j hj
    obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i,hi,k,hk⟩ := (Finset.mem_filter.mp hs).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,within_block_subset s.property hi,k,hk⟩
  rw [← Finset.card_biUnion hDisj]
  exact Finset.card_le_card hSub

/-- No raw-pair abundance assumption is needed for this combined charge.
Each block pays by a second exit or by its distinct direct readers. -/
theorem combined_charge_with_unpaired_bonus (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (hd : 1 ≤ d)
    (hSep : SeparatedBy (extendedTags p) E) (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i)
    (hNon : ∀ x : BitString (2^(a+d)),
      ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    ∃ x : BitString (2^(a+d)),
      E.card*(2^(d-1)+2) + (E.card-(rawPairBlocks p E).card)*(2^(d-1)-1) ≤ (directReaders p (blocks (d := d) E)).card +
        (downstreamReaders p (blocks (d := d) E) x).card := by
  have hNear : Separated p E := by
    intro u hu v hv hne j huj hvj
    exact hSep u hu v hv hne j (nearbyTags_subset_extended p j huj) (nearbyTags_subset_extended p j hvj)
  obtain ⟨x,hExit⟩ := rawPair_blocks_force_extra p root E hSep hFresh hLive hRead hNon
  have hPow : 2^d = 2*2^(d-1) := calc
    _ = 2^(d-1+1) := congrArg (fun j : ℕ => 2^j) (by omega)
    _ = _ := pow_succ' _ _
  have hPos : 1 ≤ 2^(d-1) := Nat.two_pow_pos _
  let Q := rawPairBlocks p E
  let U := (Finset.univ : Finset E) \ Q
  let extra (s : E) : ℕ := if s ∈ U then 2^(d-1) else 0
  have hLocal (s : E) : 2^(d-1)+extra s ≤ (directReaders p (block (d := d) s.val)).card := by
    let P := block (d := d) s.val
    have hh (i) (hi : i ∈ P) := hRead i (within_block_subset s.property hi)
    by_cases hPair : HasRawPair p s.val
    · have h := directReader_charge_of_coverage p P P x (by rfl) hFresh hh
      change (block (d := d) s.val).card ≤ 2*(directReaders p (block (d := d) s.val)).card at h
      rw [card_block, hPow] at h
      simp [extra, U, Q, rawPairBlocks, hPair]
      omega
    · have h := direct_count_without_pair p s.val hPair hh
      rw [hPow] at h
      simpa [extra, U, Q, rawPairBlocks, hPair, two_mul] using h
  have hSum : E.card*2^(d-1)+U.card*2^(d-1) ≤
      (directReaders p (blocks (d := d) E)).card := calc
    _ = ∑ s : E, (2^(d-1)+extra s) := by
      rw [Finset.sum_add_distrib]
      simp only [extra, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe]
    _ ≤ ∑ s : E, (directReaders p (block (d := d) s.val)).card :=
      Finset.sum_le_sum fun s _ => hLocal s
    _ ≤ _ := direct_card_sum_of_separated p E hNear
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Q)
  rw [Finset.card_univ, Fintype.card_coe] at hPart
  change U.card+(rawPairBlocks p E).card = E.card at hPart
  have hU : E.card-(rawPairBlocks p E).card=U.card := by omega
  have hGain : U.card*(2^(d-1)-1)+U.card=U.card*2^(d-1) := by
    rw [show U.card*(2^(d-1)-1)+U.card=U.card*((2^(d-1)-1)+1) by ring,
      Nat.sub_add_cancel hPos]
  refine ⟨x, ?_⟩
  rw [hU, Nat.mul_add]
  omega

/-- Each block pays the baseline regardless of which case it falls in. -/
theorem combined_direct_and_downstream_charge (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (hd : 1 ≤ d)
    (hSep : SeparatedBy (extendedTags p) E) (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i)
    (hNon : ∀ x : BitString (2^(a+d)),
      ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    ∃ x : BitString (2^(a+d)),
      E.card*(2^(d-1)+2) ≤ (directReaders p (blocks (d := d) E)).card +
        (downstreamReaders p (blocks (d := d) E) x).card := by
  obtain ⟨x,h⟩ := combined_charge_with_unpaired_bonus p root E hd hSep hFresh hLive hRead hNon
  exact ⟨x,(Nat.le_add_right _ _).trans h⟩

end JointCharge

section ExactMCSP

variable {a d : ℕ}

noncomputable def binaryPrefixes {g : ℕ} (p : Program signature (2^(a+d)) g) : Finset (BitString a) :=
  (binaryReadInputs p).image tag

/-- Covered prefixes that meet a binary-read address and admit distinctions
beyond their AND and OR flags. -/
noncomputable def eligiblePrefixes (c : Circuit signature (2^(a+d)) 1) : Finset (BitString a) :=
  binaryPrefixes c.program \
    ((((Finset.univ : Finset (Fin (2^(a+d)))) \ needInputs c.program (c.outputs 0) false).image tag) ∪
      flagOnlyBlocks a d)

theorem eligible_prefixes_dense (hd : 2 ≤ d) (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+d))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+d)))) :
    2^a ≤ 2*(eligiblePrefixes (a := a) (d := d) c).card+5*descriptionBitBound (a+d) := by
  let m := a+d
  let B := descriptionBitBound m
  let p := c.program
  let raw := binaryReadInputs p
  let G := binaryPrefixes (a := a) (d := d) p
  let S := needInputs p (c.outputs 0) false
  have hZero := mcspSquare_constant_table m (by omega) false
  have hSparse := card_accepting_mcspSquare_le m
  have hBinary := exact_mcsp_many_binary_read_inputs (by omega) c hc hMin hSparse
  have hSub : raw ⊆ blocks (d := d) G := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
  have hR : raw.card ≤ G.card*2^d := (Finset.card_le_card hSub).trans_eq (card_blocks G)
  have hPos : 0 < (2:ℕ)^d := Nat.two_pow_pos _
  have hG : 2^a ≤ 2*G.card+B := by
    apply (Nat.mul_le_mul_right_iff hPos).mp
    calc
      2^a*2^d = 2^m := (pow_add ..).symm
      _ ≤ 2*raw.card+B := hBinary
      _ ≤ 2*(G.card*2^d)+B := Nat.add_le_add_right (Nat.mul_le_mul_left _ hR) _
      _ ≤ 2*(G.card*2^d)+B*2^d := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hPos) _
      _ = _ := by ring
  have hS : 2^m ≤ S.card+B := card_needInputs_ge_of_sparse c hc hSparse false hZero
  have hM := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  rw [Finset.card_univ, Fintype.card_fin] at hM
  let missing := ((Finset.univ : Finset _) \ S).image tag
  have hMissing : missing.card ≤ ((Finset.univ : Finset _) \ S).card := Finset.card_image_le
  have hMissingB : missing.card ≤ B := by
    change ((Finset.univ : Finset _) \ S).card+S.card = 2^m at hM
    omega
  have hFlag := mcspSquare_individual_flag_capacity (a := a) (d := d) ⟨0,by omega⟩
  have hFour : 4 ≤ (2:ℕ)^d := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd
  have hFlagLower := Nat.mul_le_mul_left (flagOnlyBlocks a d).card hFour
  have hFlagB : (flagOnlyBlocks a d).card ≤ B := by
    change (flagOnlyBlocks a d).card*2^d ≤ 2*(flagOnlyBlocks a d).card+B at hFlag
    omega
  let bad := missing ∪ flagOnlyBlocks a d
  have hBad : bad.card ≤ 2*B := (Finset.card_union_le _ _).trans (by omega)
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁ := G) (s₂ := bad))
  have hei : G \ (G ∩ bad) = eligiblePrefixes (a := a) (d := d) c := by
    ext s
    simp [eligiblePrefixes, G, bad, missing, S, p]
  rw [hei] at hPart
  have hInter := Finset.card_le_card (Finset.inter_subset_right (s₁ := G) (s₂ := bad))
  change 2^a ≤ 2*(eligiblePrefixes (a := a) (d := d) c).card+5*B
  omega

theorem eligible_covered (c : Circuit signature (2^(a+d)) 1)
    (E : Finset (BitString a)) (hE : E ⊆ eligiblePrefixes (a := a) (d := d) c) :
    blocks (d := d) E ⊆ needInputs c.program (c.outputs 0) false := by
  intro i hi
  by_contra hm
  have ht := (Finset.mem_filter.mp hi).2
  have he := (Finset.mem_sdiff.mp (hE ht)).2
  exact he (Finset.mem_union_left _ (Finset.mem_image.mpr
    ⟨i,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hm⟩,rfl⟩))

/-- Select blocks with binary reading, full corner coverage, and a
semantic distinction beyond their flags. Then apply the joint charge. -/
theorem exact_mcsp_eligible_joint_bound {a k l r K H reserve : ℕ}
    (ha : 1 ≤ a) (hd : 2 ≤ k+l)
    (hFew : descriptionBitBound (a+(k+l)) < 2^(a+(k+l)))
    (hHeavy : 18*complexity interpretation (single (mcspSquare (a+(k+l)))) < K*(H+1))
    (hRoom : r*(18*K+1)+H+3*descriptionBitBound (a+(k+l)) ≤ 2^(a-1))
    (hRepair : 4*(a+(k+l))+48+lookupBankCost k l+
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (hReserve : reserve ≤ descriptionBitBound (a+(k+l)))
    (hFactorial : 2^(r*2^(k+l)+reserve) ≤ ((a+(k+l))^2).factorial) :
    280*(2*2^(a+(k+l)) + r*(2^(k+l-1)+2)) + 2*2^(a+(k+l)) ≤
      280*(complexity interpretation (single (mcspSquare (a+(k+l)))) +
        2*(descriptionBitBound (a+(k+l))-reserve)+1)+17*(descriptionBitBound (a+(k+l))-reserve) := by
  let m := a+(k+l)
  let B := descriptionBitBound m
  obtain ⟨c,hc,hMin⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  let p := c.program
  let root := c.outputs 0
  let pool := eligiblePrefixes (a := a) (d := k+l) c
  have hDense := eligible_prefixes_dense hd c hc hMin
  have hHalf : 2^a = 2*2^(a-1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  have hPool : r*(18*K+1)+H ≤ pool.card := by
    change 2^a ≤ 2*pool.card+5*B at hDense
    change r*(18*K+1)+H+3*B ≤ 2^(a-1) at hRoom
    omega
  obtain ⟨E,hE,hCard,hSep⟩ := exists_separated_subset_by (extendedTags (a := a) (d := k+l) p)
    (card_extendedTags_le p) pool r K H (hMin ▸ hHeavy) hPool
  let P := blocks (d := k+l) E
  have hP : P.card = r*2^(k+l) := (card_blocks E).trans (by rw [hCard])
  have hCover := eligible_covered c E hE
  have h0 := mcspSquare_constant_table m (by omega) false
  have h1 := mcspSquare_constant_table m (by omega) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hRead (i : Fin (2^m)) (hi : i ∈ P) : ∃ j : Fin c.size, ∃ q, (p.lines j).wires q = .input i := by
    obtain ⟨j,_,q,hq⟩ := need_input_has_reader hc0 hc1 (hCover hi)
    exact ⟨j,q,hq⟩
  have hOrig := not_constant_of_sparse hFew (card_accepting_mcspSquare_le m) h0
  have hFresh := minimum_fresh_univ c hc hMin hOrig
  have hLive := minimum_live_univ c hc hMin hOrig
  let f (x : BitString (2^m)) : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
  have hSparse (x : BitString (2^m)) : (acceptingTables (f x)).card ≤ 2^(B-reserve) :=
    padded_sparsity_of_factorial x P hReserve (by rwa [hP])
  have hQ (x : BitString (2^m)) (u : BitString m) (b : Bool) (v w : BitString m) :
      f x (MCSP.truthTable m (quad u b v w)) = true := by
    apply accepted_after_blocks_pin (k := k) (l := l)
    have hSize := QuadraticPinning.complexity_quad_shared_le u b v w
    dsimp only [m] at hSize
    rw [hCard]
    omega
  have hEq (x : BitString (2^m)) : restrictedWire p (pinAt x P) root = f x :=
    restricted_circuit_eq c hc (pinAt x P)
  have hNon (x : BitString (2^m)) : ¬∃ b : Bool, restrictedWire p (pinAt x P) root = fun _ => b := by
    rw [hEq]
    apply not_constant_of_sparse ((Nat.sub_le B reserve).trans_lt hFew) (hSparse x)
    have h := hQ x (zeroVec m) false (zeroVec m) (zeroVec m)
    have he : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, SuperTwoN.affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  obtain ⟨x,hLoss⟩ := combined_direct_and_downstream_charge p root E (by omega) hSep hFresh hLive hRead hNon
  rw [hCard] at hLoss
  have hForest := quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding (hSparse x) (hQ x)
  have hCost := original_reader_and_dead_budget p root P x (hNon x)
  rw [hEq x] at hCost
  have hCost' := hCost.trans_eq hMin
  dsimp only [m, B, P, f] at hCost' hForest
  omega

/-- Three blocks pay for at least 390 original gates at arity 32. -/
theorem mcspSquare_32_eligible_joint_bound :
    8620571619 ≤ complexity interpretation (single (mcspSquare 32)) := by
  by_contra! hSmall
  have h := exact_mcsp_eligible_joint_bound (a := 24) (k := 2) (l := 6) (r := 3)
    (K := 65536) (H := 4194304) (reserve := 7436)
    (by decide) (by decide) (by decide) (by
      change 18*complexity interpretation (single (mcspSquare 32)) < _
      omega) (by decide) (by decide) (by decide) (by
      rw [show (3:ℕ)*2^(2+6)+7436 = 8204 by decide]
      exact factorial_room_32_dyadic)
  rw [show (24:ℕ)+(2+6) = 32 by decide, show descriptionBitBound 32 = 27672 by decide] at h
  norm_num at h
  omega

end ExactMCSP

section GrowingSchedule

private theorem growing_eligible_room (t : ℕ) (ht : 8 ≤ t) :
    let m := multiBlockArity t
    let d := t.log2+2*t
    let a := m-d
    let r := separatedBlockCount t
    let K := 256*2^d
    let H := 2^(a-2)
    2 ≤ a ∧ r*(18*K+1)+H+3*descriptionBitBound m ≤ 2^(a-1) ∧
      descriptionBitBound m < 2^m ∧ 2*(multiBlockLoss t+2*r) ≤ 2^m := by
  let m := multiBlockArity t
  let d := t.log2+2*t
  let a := m-d
  let r := separatedBlockCount t
  let L := (2:ℕ)^d
  let K := 256*L
  let H := (2:ℕ)^(a-2)
  change 2 ≤ a ∧ r*(18*K+1)+H+3*descriptionBitBound m ≤ 2^(a-1) ∧
    descriptionBitBound m < 2^m ∧ 2*(multiBlockLoss t+2*r) ≤ 2^m
  have hR : 256 ≤ (2:ℕ)^t := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ht
  have hM : m = 2^t*2^t := by
    dsimp only [m, multiBlockArity]
    rw [show 2*t=t+t by omega, pow_add]
  have hm : 65536 ≤ m := hM ▸ Nat.mul_le_mul hR hR
  have htr : t ≤ (2:ℕ)^t := t.lt_two_pow_self.le
  have hr : 4*r = m := four_mul_separatedBlockCount t ht
  have hrm : r ≤ m := by omega
  have hd : 2*d+4 ≤ m := calc
    _ ≤ 10*2^t := by
      have hk := Nat.log2_le_self t
      dsimp only [d]
      omega
    _ ≤ 2^t*2^t := Nat.mul_le_mul_right (2^t) (by omega)
    _ = _ := hM.symm
  have ha : 2 ≤ a := by dsimp only [a]; omega
  have hHalf : m ≤ 2*(a-2) := by dsimp only [a]; omega
  have hA : 32768 ≤ a-2 := by omega
  have hM3 : m ≤ m^3 := calc
    _ = m*1 := by simp
    _ ≤ m*m^2 := Nat.mul_le_mul_left _ (Nat.pow_pos (by omega))
    _ = _ := by ring
  have hRows : 4*(r*2^(2*t)) = m^2 := separated_rows t ht
  have hk : (2:ℕ)^t.log2 ≤ t := Nat.log2_self_le (by omega : t ≠ 0)
  have hPay : 256*(2:ℕ)^t.log2 ≤ m :=
    (Nat.mul_le_mul_left 256 (hk.trans htr)).trans
      ((Nat.mul_le_mul_right (2^t) hR).trans_eq hM.symm)
  have hRL : 1024*(r*L) ≤ m^3 := calc
    _ = (4*(r*2^(2*t)))*(256*2^t.log2) := by dsimp only [L,d]; rw [pow_add]; ring
    _ ≤ m^2*m := Nat.mul_le_mul hRows.le hPay
    _ = _ := by ring
  have hB : descriptionBitBound m ≤ 5*m^3 := calc
    _ ≤ (4*m+12)*m^2 := QuadraticPinning.description_le_polynomial m (by omega)
    _ ≤ (5*m)*m^2 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have hSmall : r*(18*K+1)+3*descriptionBitBound m ≤ 21*m^3 := by
    rw [show r*(18*K+1) = 4608*(r*L)+r by dsimp only [K]; ring]
    omega
  have hCap : 21*m^3 ≤ H := calc
    _ ≤ 21*(2*(a-2))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHalf 3)
    _ = 168*(a-2)^3 := by ring
    _ ≤ (a-2)*(a-2)^3 := Nat.mul_le_mul_right _ (by omega)
    _ = (a-2)^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp _ (by omega)
  have hPow : 2^(a-1) = 2*H := by
    dsimp only [H]
    rw [← pow_succ', show a-2+1=a-1 by omega]
  have hLoss : 2*multiBlockLoss t = r*L := two_mul_multiBlockLoss t ht
  have hFloor : 6*m^3 ≤ 2^m := calc
    _ ≤ m*m^3 := Nat.mul_le_mul_right _ (by omega)
    _ = m^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp m (by omega)
  have hM3pos : 0 < m^3 := Nat.pow_pos (by omega)
  exact ⟨ha,by omega,by omega,by omega⟩

/-- The combined argument adds a second block charge on the growing
schedule, whether the additional gate is a direct reader or a second exit. -/
theorem mcspSquare_growing_eligible_joint_bound (t : ℕ) (ht : 8 ≤ t) :
    280*(2*2^(multiBlockArity t)+multiBlockLoss t+2*separatedBlockCount t)+2*2^(multiBlockArity t) ≤
      280*(complexity interpretation (single (mcspSquare (multiBlockArity t)))+
        2*descriptionBitBound (multiBlockArity t)+1)+17*descriptionBitBound (multiBlockArity t) := by
  let m := multiBlockArity t
  let k := t.log2
  let l := 2*t
  let d := k+l
  let a := m-d
  let L := (2:ℕ)^d
  let K := 256*L
  let H := (2:ℕ)^(a-2)
  let r := separatedBlockCount t
  let G := complexity interpretation (single (mcspSquare m))
  obtain ⟨hd,_,_,hRepair,_⟩ := growing_conflict_budget t ht
  have he : a+d=m := Nat.sub_add_cancel hd
  obtain ⟨ha,hRoom,hFew,hCeil⟩ := growing_eligible_room t ht
  change 280*(2*2^m+multiBlockLoss t+2*r)+2*2^m ≤
    280*(G+2*descriptionBitBound m+1)+17*descriptionBitBound m
  change 2*(multiBlockLoss t+2*r) ≤ 2^m at hCeil
  by_cases hG : G ≤ 3*2^m
  · have hN : 2^m = 4*H*L := by
      dsimp only [H,L]
      rw [show (4:ℕ)=2^2 by decide, ← pow_add, show 2+(a-2)=a by omega, ← pow_add, he]
    have hHeavy : 18*G < K*(H+1) := calc
      _ ≤ 18*(3*2^m) := Nat.mul_le_mul_left _ hG
      _ = (216*H)*L := by rw [hN]; ring
      _ < (256*(H+1))*L := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = _ := by unfold K; ring
    have h := exact_mcsp_eligible_joint_bound
      (a := a) (k := k) (l := l) (r := r) (K := K) (H := H) (reserve := 0)
      (by omega) (by dsimp only [l]; omega) (by rwa [show a+(k+l)=m from he])
      (by rwa [show a+(k+l)=m from he]) (by rwa [show a+(k+l)=m from he])
      (by rwa [show a+(k+l)=m from he]) (Nat.zero_le _) (by
        rw [Nat.add_zero, show a+(k+l)=m from he, ← two_mul_multiBlockLoss t ht]
        exact growing_blocks_fit_factorial t ht)
    have hG' : complexity interpretation (single (mcspSquare (a+(k+l)))) = G := by
      unfold G
      rw [show a+(k+l)=m from he]
    have hD : r*2^(k+l-1)=multiBlockLoss t := same_direct_charge t ht
    rw [hG', show r*(2^(k+l-1)+2) = multiBlockLoss t+2*r by rw [Nat.mul_add,hD,Nat.mul_comm r 2]] at h
    simpa only [show a+(k+l)=m from he,Nat.sub_zero,Nat.add_assoc] using h
  · omega

end GrowingSchedule

#print axioms combined_charge_with_unpaired_bonus
#print axioms combined_direct_and_downstream_charge
#print axioms eligible_prefixes_dense
#print axioms exact_mcsp_eligible_joint_bound
#print axioms mcspSquare_32_eligible_joint_bound
#print axioms mcspSquare_growing_eligible_joint_bound

end PvsNP.Frontier.BlockChargeDichotomy
