module

public import MCSPChargeMultiplicity

/-! Preserve local exit certificates while completing the other pins by
choosing the sparser branch. Only prescribed seed bits cost sparsity. -/

@[expose] public section

namespace PvsNP.Frontier.JointSparseCompletion

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure ForestBlockPinning ForestPinning
open RestrictionCharges FreshCharges NestedFaces QuadraticForest
open DownstreamBlockPinning IndependentBlockPinning MultiBlockPinning
open ChargeMultiplicity BlockChargeDichotomy ConstantBlockExits
open scoped Classical BigOperators

section Completion

variable {n : ℕ}

/-- Extend prescribed pins using minority branches one coordinate at a time.
The padded count only pays for the prescribed part. -/
theorem exists_sparse_completion (f : BooleanFunction n) (P Q : Finset (Fin n))
    (hSub : Q ⊆ P) (x : BitString n) :
    ∃ y : BitString n, (∀ i ∈ Q, y i = x i) ∧
      (acceptingTables fun z => f (substitute (pinAt y P) z)).card ≤
        2^Q.card*(acceptingTables f).card := by
  let base (z : BitString n) := f (substitute (pinAt x Q) z)
  obtain ⟨w, hw⟩ := exists_sparse_pins base (P \ Q)
  let y : BitString n := fun i => if i ∈ Q then x i else w i
  have he : compose (pinAt x Q) (pinAt w (P \ Q)) = pinAt y P := by
    funext i
    by_cases hQ : i ∈ Q
    · simp [compose, pinAt, hQ, hSub hQ, y]
    · by_cases hP : i ∈ P <;> simp [compose, pinAt, hP, hQ, y]
  refine ⟨y, fun i hi => by simp [y, hi], ?_⟩
  have heval : (fun z => base (substitute (pinAt w (P \ Q)) z)) =
      fun z => f (substitute (pinAt y P) z) := by
    funext z
    simp only [base, ← substitute_compose, he]
  rw [heval] at hw
  exact hw.trans (card_accepting_pin_le f x Q)

end Completion

section ExitSeeds

variable {a d g : ℕ}

noncomputable def outputTags (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) : Finset (BitString a) :=
  match root with
  | .input _ => ∅
  | .gate j => readerTags p j

private theorem card_outputTags_le (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) : (outputTags p root).card ≤ 2 := by
  cases root with
  | input => simp [outputTags]
  | gate j => exact card_readerTags_le p j

private theorem live_exit_edge (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (s : BitString a)
    (hRoot : s ∉ outputTags p root)
    (hFresh : fresh p Sum.inl = Finset.univ)
    {j : Fin g} (hLive : ResidualLive p Sum.inl root j)
    (hStart : j ∈ directReaders p (block (d := d) s)) :
    ∃ (v u : Fin g) (b : Fin (signature.Arity (p.lines u).op)),
      v ∈ directReaders p (block (d := d) s) ∧
      u ∉ directReaders p (block (d := d) s) ∧ (p.lines u).wires b = .gate v := by
  induction hLive with
  | @output u hRep =>
    have he := original_represents_gate hFresh hRep
    exact (hRoot (by rw [he]; exact mem_readerTags.mpr hStart)).elim
  | @argument u v hLive b hRep ih =>
    by_cases hu : u ∈ directReaders p (block (d := d) s)
    · exact ih hu
    · exact ⟨v,u,b,hStart,hu,original_represents_gate hFresh hRep⟩

/-- Take the final raw reader before going downstream. A controlling value
at one raw port fixes its output regardless of how other pins are filled. -/
private theorem seeded_exit (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (s : BitString a)
    (hRoot : s ∉ outputTags p root)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : (directReaders p (block (d := d) s)).Nonempty) :
    ∃ (i : Fin (2^(a+d))) (value : Bool) (u : Fin g),
      i ∈ block (d := d) s ∧ s ∈ nearbyTags p u ∧
      u ∉ directReaders p (block (d := d) s) ∧
      ∀ (P : Finset (Fin (2^(a+d)))) (x : BitString (2^(a+d))),
        i ∈ P → x i = value → u ∈ constantReaders p (pinAt x P) := by
  obtain ⟨j,hj⟩ := hRead
  obtain ⟨v,u,b,hv,hU,hWire⟩ := live_exit_edge p root s hRoot hFresh
    (mem_liveFresh_iff.mp (hLive.symm ▸ Finset.mem_univ j)) hj
  obtain ⟨i,hi,t,hInput⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨value,out,hAbsorb⟩ := op_can_force_constant (p.lines v).op t
  refine ⟨i,value,u,hi,readerTags_subset_nearby_of_wire p hWire (mem_readerTags.mpr hv),hU,?_⟩
  intro P x hiP hVal
  have hArg : restrictedWire p (pinAt x P) ((p.lines v).wires t) = fun _ => value := by
    rw [hInput, pin_input_constant p x hiP, hVal]
  have hConst : restrictedWire p (pinAt x P) (.gate v) = fun _ => out := by
    funext y
    unfold restrictedWire
    rw [p.trace_gate]
    exact hAbsorb _ (congrFun hArg y)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,out,hWire ▸ hConst⟩

/-- Keep a witnessed first exit from every selected block under any
completion of one designated input per block. Footprint separation keeps
the exits distinct and prevents another block from making one direct. -/
theorem joint_seeded_exits (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a))
    (hOut : ∀ s ∈ E, s ∉ outputTags p root)
    (hSep : SeparatedBy (SecondBlockExits.extendedTags p) E)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ s ∈ E, (directReaders p (block (d := d) s)).Nonempty) :
    ∃ (Q : Finset (Fin (2^(a+d)))) (x : BitString (2^(a+d))) (exit : E ↪ Fin g),
      Q ⊆ blocks (d := d) E ∧ Q.card ≤ E.card ∧
      (∀ s : E, s.val ∈ nearbyTags p (exit s)) ∧
      ∀ y : BitString (2^(a+d)), (∀ i ∈ Q, y i = x i) →
        ∀ s : E, exit s ∈ downstreamReaders p (block (d := d) s.val) y ∧
          exit s ∈ downstreamReaders p (blocks (d := d) E) y := by
  have hLocal (s : E) := seeded_exit p root s.val (hOut s.val s.property)
    hFresh hLive (hRead s.val s.property)
  choose i bit gate hi hTag hDirect hForce using hLocal
  let Q := (Finset.univ : Finset E).image i
  let x (j : Fin (2^(a+d))) : Bool := if h : tag j ∈ E then bit ⟨tag j,h⟩ else false
  have hVal (s : E) : x (i s) = bit s := by
    have ht : tag (i s) = s.val := (Finset.mem_filter.mp (hi s)).2
    simp only [x, ht, s.property, dite_true]
  have hinj : Function.Injective gate := by
    intro s t hEq
    apply Subtype.ext
    by_contra hn
    exact hSep s.val s.property t.val t.property hn (gate s)
      (SecondBlockExits.nearbyTags_subset_extended p _ (hTag s))
      (hEq.symm ▸ SecondBlockExits.nearbyTags_subset_extended p _ (hTag t))
  have hSub : Q ⊆ blocks (d := d) E := by
    intro j hj
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp (hi s)).2).symm ▸ s.property⟩
  refine ⟨Q,x,⟨gate,hinj⟩,hSub,?_,hTag,?_⟩
  · exact Finset.card_image_le.trans_eq (by simp)
  intro y hy s
  have hQi : i s ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hb := (hy _ hQi).trans (hVal s)
  refine ⟨Finset.mem_sdiff.mpr ⟨hForce s _ y (hi s) hb,hDirect s⟩, ?_⟩
  refine Finset.mem_sdiff.mpr ⟨hForce s _ y (hSub hQi) hb,?_⟩
  intro hD
  obtain ⟨j,hj,b,hb⟩ := (Finset.mem_filter.mp hD).2
  have hJ : tag j ∈ E := (Finset.mem_filter.mp hj).2
  have hRaw : tag j ∈ readerTags p (gate s) :=
    mem_readerTags.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,b,hb⟩)
  have he : s.val = tag j := by
    by_contra hn
    exact hSep s.val s.property _ hJ hn (gate s)
      (SecondBlockExits.nearbyTags_subset_extended p _ (hTag s))
      (SecondBlockExits.nearbyTags_subset_extended p _
        (readerTags_subset_nearby p _ hRaw))
  exact hDirect s (he.symm ▸ mem_readerTags.mp hRaw)

end ExitSeeds

section ExactMCSP

/-- Choose one joint restriction in a minimum circuit. The prescribed bits
preserve the same original first exits on the individual and joint pins.
The remaining pins are filled sparsely and all quadratic probes survive. -/
theorem exact_mcsp_joint_sparse_exits {a k l r K H B : ℕ}
    (ha : 1 ≤ a) (hd : 2 ≤ k+l)
    (hFew : descriptionBitBound (a+(k+l)) < 2^(a+(k+l)))
    (hSparse : (acceptingTables (mcspSquare (a+(k+l)))).card ≤ 2^B)
    (hResid : B+r < 2^(a+(k+l)))
    (hHeavy : 8*complexity interpretation (single (mcspSquare (a+(k+l)))) < K*(H+1))
    (hRoom : r*(8*K+1)+H+3*descriptionBitBound (a+(k+l))+2 ≤ 2^(a-1))
    (hRepair : 4*(a+(k+l))+48+lookupBankCost k l+
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l))))) :
    let m := a+(k+l)
    ∃ (E : Finset (BitString a)) (x : BitString (2^m)) (exit : E ↪ Fin c.size),
      E.card = r ∧
      (∀ s : E, exit s ∈ downstreamReaders c.program (block (d := k+l) s.val) x ∧
        exit s ∈ downstreamReaders c.program (blocks (d := k+l) E) x) ∧
      (let f : BooleanFunction (2^m) := fun y =>
        mcspSquare m (substitute (pinAt x (blocks (d := k+l) E)) y)
       (acceptingTables f).card ≤ 2^(B+r) ∧
       (∀ u b v w, f (MCSP.truthTable m (quad u b v w)) = true) ∧
       complexity interpretation (single f)+r*(2^(k+l-1)+1) ≤ c.size ∧
       280*(2*2^m+r*(2^(k+l-1)+1))+2*2^m ≤
         280*(c.size+2*(B+r)+1)+17*(B+r)) := by
  let m := a+(k+l)
  let p := c.program
  let root := c.outputs 0
  let eligible := eligiblePrefixes (a := a) (d := k+l) c
  let excluded := outputTags (a := a) (d := k+l) p root
  let pool := eligible \ excluded
  have hDense := eligible_prefixes_dense hd c hc hMin
  change 2^a ≤ 2*eligible.card+5*descriptionBitBound m at hDense
  have hHalf : 2^a = 2*2^(a-1) := by rw [← pow_succ', Nat.sub_add_cancel ha]
  have hExcl : excluded.card ≤ 2 := card_outputTags_le p root
  have hPart : pool.card+(eligible ∩ excluded).card = eligible.card := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_left (s₁ := eligible) (s₂ := excluded))
    rw [show eligible \ (eligible ∩ excluded) = pool by ext s; simp [pool]] at h
    exact h
  have hCut := Finset.card_le_card (Finset.inter_subset_right (s₁ := eligible) (s₂ := excluded))
  have hEnough : r*(8*K+1)+H ≤ pool.card := by
    change r*(8*K+1)+H+3*descriptionBitBound m+2 ≤ 2^(a-1) at hRoom
    omega
  obtain ⟨E,hE,hCard,hSep⟩ := tighter_separated_pool p pool r K H (hMin ▸ hHeavy) hEnough
  let P := blocks (d := k+l) E
  have hE' : E ⊆ eligible := hE.trans Finset.sdiff_subset
  have hCover := eligible_covered c E hE'
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
  have hLocal (s : BitString a) (hs : s ∈ E) : (directReaders p (block (d := k+l) s)).Nonempty := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (by rw [card_block]; exact Nat.two_pow_pos _ :
      0 < (block (d := k+l) s).card)
    have hiP : i ∈ P :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hi).2).symm ▸ hs⟩
    obtain ⟨j,q,hq⟩ := hRead i hiP
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,q,hq⟩⟩
  obtain ⟨Q,v,exit,hSub,hSize,_,hExit⟩ := joint_seeded_exits p root E
    (fun s hs => (Finset.mem_sdiff.mp (hE hs)).2) hSep hFresh hLive hLocal
  obtain ⟨x,hx,hS⟩ := exists_sparse_completion (mcspSquare m) P Q hSub v
  let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
  have hFinalSparse : (acceptingTables f).card ≤ 2^(B+r) := calc
    _ ≤ 2^Q.card*(acceptingTables (mcspSquare m)).card := hS
    _ ≤ 2^r*2^B := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (hSize.trans_eq hCard)) hSparse
    _ = _ := by rw [Nat.mul_comm, ← pow_add]
  have hQ (u : BitString m) (b : Bool) (v w : BitString m) : f (MCSP.truthTable m (quad u b v w)) = true := by
    apply accepted_after_blocks_pin (k := k) (l := l)
    have h := QuadraticPinning.complexity_quad_shared_le u b v w
    dsimp only [m] at h
    rw [hCard]
    omega
  have hEq : restrictedWire p (pinAt x P) root = f := restricted_circuit_eq c hc (pinAt x P)
  have hNon : ¬∃ b : Bool, restrictedWire p (pinAt x P) root = fun _ => b := by
    rw [hEq]
    apply not_constant_of_sparse hResid hFinalSparse
    have h := hQ (zeroVec m) false (zeroVec m) (zeroVec m)
    have he : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, SuperTwoN.affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  have hCount : r ≤ (downstreamReaders p P x).card := by
    let into (s : E) : downstreamReaders p P x := ⟨exit s,(hExit x hx s).2⟩
    have hinj : Function.Injective into := fun _ _ he => exit.injective (congrArg Subtype.val he)
    simpa only [Fintype.card_coe,hCard] using Fintype.card_le_of_injective into hinj
  have hDirect := directReader_charge_of_coverage p P P x Finset.Subset.rfl hFresh hRead
  have hPd : P.card = r*2^(k+l) := (card_blocks E).trans (by rw [hCard])
  rw [hPd, show (2:ℕ)^(k+l) = 2*2^(k+l-1) by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k+l)],
    show r*(2*2^(k+l-1)) = 2*(r*2^(k+l-1)) by ring] at hDirect
  have hBudget := original_reader_and_dead_budget p root P x hNon
  rw [hEq] at hBudget
  have hLoss : complexity interpretation (single f)+r*(2^(k+l-1)+1) ≤ c.size := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hForest := quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding hFinalSparse hQ
  refine ⟨E,x,exit,hCard,hExit x hx,hFinalSparse,hQ,hLoss,?_⟩
  change 280*(2*2^m+r*(2^(k+l-1)+1))+2*2^m ≤ 280*(c.size+2*(B+r)+1)+17*(B+r)
  omega

end ExactMCSP

section Arity32

private theorem mcsp32_sparsity_from_factorial (b : ℕ) (hb : b ≤ descriptionBitBound 32)
    (hRoom : 2^b ≤ ((32:ℕ)^2).factorial) :
    (acceptingTables (mcspSquare 32)).card ≤ 2^(descriptionBitBound 32-b) := by
  apply (Nat.mul_le_mul_right_iff (Nat.two_pow_pos b)).mp
  calc
    _ ≤ (acceptingTables (mcspSquare 32)).card * ((32:ℕ)^2).factorial :=
      Nat.mul_le_mul_left _ hRoom
    _ ≤ 2^descriptionBitBound 32 := card_accepting_mcspSquare_mul_factorial_le 32
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hb]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
set_option exponentiation.threshold 16384 in
theorem factorial_room_32_exact : (2:ℕ)^8769 ≤ (1024:ℕ).factorial ∧
    (1024:ℕ).factorial < 2^8770 := by decide

theorem mcsp32_tight_sparsity :
    (acceptingTables (mcspSquare 32)).card ≤ 2^18903 := by
  have h := mcsp32_sparsity_from_factorial 8769 (by decide) factorial_room_32_exact.1
  rwa [show descriptionBitBound 32-8769 = 18903 by decide] at h

theorem mcsp32_tight_unpinned_floor :
    8620573976 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := quad_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding mcsp32_tight_sparsity
    (fun a b c d => mcspSquare_accepts_quad 32 (by decide) a b c d)
  change 280*(2*(2^32))+2*(2^32) ≤
    280*(complexity interpretation (single (mcspSquare 32))+2*18903+1)+17*18903 at h
  norm_num at h
  omega

private theorem mcsp32_joint_inequality (B : ℕ) (hResid : B+3 < (2:ℕ)^32)
    (hSparse : (acceptingTables (mcspSquare 32)).card ≤ 2^B) :
    280*(2*(2^32)+387)+2*(2^32) ≤
      280*(complexity interpretation (single (mcspSquare 32))+2*(B+3)+1)+17*(B+3) := by
  let G := complexity interpretation (single (mcspSquare 32))
  by_cases hSize : G ≤ 3*(2^32)
  · obtain ⟨c,hc,hMin⟩ := exists_computes_size_eq_complexity
      (I := interpretation) (f := single (mcspSquare 32))
    have hHeavy : 8*G < 32768*(4194304+1) := by
      norm_num at hSize ⊢
      omega
    obtain ⟨E,x,exit,hE,hExit,hS,hQ,hLoss,h⟩ := exact_mcsp_joint_sparse_exits
      (a := 24) (k := 2) (l := 6) (r := 3) (K := 32768) (H := 4194304) (B := B)
      (by decide) (by decide) (by decide) hSparse hResid hHeavy (by decide) (by decide) c hc hMin
    rw [hMin] at h
    exact h
  · change 280*(2*(2^32)+387)+2*(2^32) ≤ 280*(G+2*(B+3)+1)+17*(B+3)
    norm_num at hSize ⊢
    omega

/-- Improvement due to the sparse joint pins alone, retaining the previous
dyadic factorial estimate. -/
theorem mcsp32_sparse_joint_floor_dyadic :
    8620573192 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have hS := mcsp32_sparsity_from_factorial 8204 (by decide) factorial_room_32_dyadic
  have h := mcsp32_joint_inequality (descriptionBitBound 32-8204) (by decide) hS
  rw [show descriptionBitBound 32-8204 = 19468 by decide] at h
  norm_num at h
  omega

/-- Combining the sparse joint pins with the exact factorial bit floor. -/
theorem mcsp32_sparse_joint_floor :
    8620574356 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := mcsp32_joint_inequality 18903 (by decide) mcsp32_tight_sparsity
  norm_num at h
  omega

set_option exponentiation.threshold 20000 in
/-- Smaller 16-entry blocks retain eleven distinct first exits at once.
This choice trades direct-reader losses for more simultaneous exits. -/
theorem mcsp32_eleven_joint_exits (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32)))
    (hSize : c.size ≤ 3*(2^32)) :
    ∃ (E : Finset (BitString 28)) (x : BitString (2^32)) (exit : E ↪ Fin c.size),
      E.card = 11 ∧
      (∀ s : E, exit s ∈ downstreamReaders c.program (block (d := 4) s.val) x ∧
        exit s ∈ downstreamReaders c.program (blocks (d := 4) E) x) ∧
      (let f : BooleanFunction (2^32) := fun y => mcspSquare 32
          (substitute (pinAt x (blocks (d := 4) E)) y)
       (acceptingTables f).card ≤ 2^18914 ∧
       (∀ u b v w, f (MCSP.truthTable 32 (quad u b v w)) = true) ∧
       complexity interpretation (single f)+99 ≤ c.size) := by
  have hHeavy : 8*complexity interpretation (single (mcspSquare 32)) < 32768*(4194304+1) := by
    rw [← hMin]
    norm_num at hSize ⊢
    omega
  obtain ⟨E,x,exit,hE,hExit,hS,hQ,hLoss,_⟩ := exact_mcsp_joint_sparse_exits
    (a := 28) (k := 2) (l := 2) (r := 11) (K := 32768) (H := 4194304) (B := 18903)
    (by decide) (by decide) (by decide) mcsp32_tight_sparsity
    (by decide) hHeavy (by decide) (by decide) c hc hMin
  exact ⟨E,x,exit,hE,hExit,hS,hQ,hLoss⟩

end Arity32

#print axioms exists_sparse_completion
#print axioms joint_seeded_exits
#print axioms exact_mcsp_joint_sparse_exits
#print axioms factorial_room_32_exact
#print axioms mcsp32_tight_unpinned_floor
#print axioms mcsp32_sparse_joint_floor_dyadic
#print axioms mcsp32_sparse_joint_floor
#print axioms mcsp32_eleven_joint_exits

end PvsNP.Frontier.JointSparseCompletion
