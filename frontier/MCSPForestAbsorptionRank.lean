module

public import MCSPForestTraceQuotient

/-! Pin a controlling input of a previously counted monotone component.
Its absorbed gates contribute zero to the forest's share of the rank. -/

@[expose] public section

namespace PvsNP.Frontier.ForestAbsorptionRank

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open BatchRank ResidualTraceRank RestrictionCharges ForestPinning DownstreamBlockPinning
open ForestTraceQuotient CornerCertificates JointSparseCompletion
open scoped Classical BigOperators

section PaidRank

variable {n k g : ℕ}

theorem quotient_trace_zero_of_constant (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (j : Fin g) (b : Bool)
    (h : restrictedWire p pin (.gate j) = fun _ => b) :
    pinQuotientTrace p pin a j = 0 := by
  have he : centered p (substitute pin a) (fun z => substitute pin (perturb a z)) (.gate j) = 0 := by
    funext z
    change bit (restrictedWire p pin (.gate j) a ^^ restrictedWire p pin (.gate j) (perturb a z)) = 0
    rw [h]
    simp [bit]
  change (rawSpan (substitute pin a) (fun z => substitute pin (perturb a z))).mkQ
    (centered p (substitute pin a) (fun z => substitute pin (perturb a z)) (.gate j)) = 0
  rw [he,map_zero]

/-- A gate that is constant on the entire restricted cube supplies no
direction to the paid span. -/
theorem paidRank_le_unabsorbed (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid absorbed : Finset (Fin g))
    (hAbs : ∀ j ∈ absorbed, ∃ b : Bool, restrictedWire p pin (.gate j) = fun _ => b) :
    paidRank p pin a paid ≤ (paid \ absorbed).card := by
  have hSp : paidSpan p pin a paid ≤ paidSpan p pin a (paid \ absorbed) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    by_cases he : j.val ∈ absorbed
    · obtain ⟨b,hb⟩ := hAbs j.val he
      change pinQuotientTrace p pin a j.val ∈ paidSpan p pin a (paid \ absorbed)
      rw [quotient_trace_zero_of_constant p pin a _ b hb]
      exact (paidSpan p pin a _).zero_mem
    · exact Submodule.subset_span ⟨⟨j.val,Finset.mem_sdiff.mpr ⟨j.property,he⟩⟩,rfl⟩
  exact (Submodule.finrank_mono hSp).trans
    ((finrank_range_le_card (fun j : ↥(paid \ absorbed) => pinQuotientTrace p pin a j.val)).trans_eq
      (Fintype.card_coe _))

theorem outsideRank_of_absorbed (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (out : Wire n g) (paid absorbed : Finset (Fin g)) (B : ℕ)
    (hYes : restrictedWire p pin out a = true)
    (hSparse : (acceptingTables (restrictedWire p pin out)).card ≤ 2^B)
    (hAbs : ∀ j ∈ absorbed, ∃ b : Bool, restrictedWire p pin (.gate j) = fun _ => b) :
    k-(B+(paid \ absorbed).card+1) ≤ remainingRank p pin a paid := by
  have hP := paidRank_le_unabsorbed p pin a paid absorbed hAbs
  have hR := remainingRank_lower_of_sparse p pin a out paid B hYes hSparse
  omega

/-- Seed values may be prescribed to absorb known paths. Completing the
other entries sparsely pays one description bit per seed. This bound
counts all paid gates only once, including those that were absorbed. -/
theorem choose_absorbing_sparse_pins (p : Program signature n g) (out : Wire n g)
    (P Q : Finset (Fin n)) (hSub : Q ⊆ P) (seed : BitString n)
    (paid absorbed : Finset (Fin g)) (B : ℕ)
    (hSparse : (acceptingTables fun z => p.trace interpretation z out).card ≤ 2^B)
    (hPaths : ∀ j ∈ absorbed, ∃ i ∈ Q,
      AbsorbingPath p (seed i) (.input i) (.gate j))
    (hAccept : ∀ x : BitString n, (∀ i ∈ Q, x i = seed i) →
      ∃ a, restrictedWire p (pinAt x P) out a = true) :
    ∃ (x a : BitString n),
      (∀ i ∈ Q, x i = seed i) ∧ restrictedWire p (pinAt x P) out a = true ∧
      (acceptingTables (restrictedWire p (pinAt x P) out)).card ≤ 2^(B+Q.card) ∧
      n-(B+Q.card+(paid \ absorbed).card+1) ≤ remainingRank p (pinAt x P) a paid ∧
      remainingRank p (pinAt x P) a paid+(paid ∪ constantReaders p (pinAt x P)).card ≤ g := by
  let f : BooleanFunction n := fun z => p.trace interpretation z out
  obtain ⟨x,hx,hS⟩ := exists_sparse_completion f P Q hSub seed
  obtain ⟨a,ha⟩ := hAccept x hx
  have hCount : (acceptingTables (restrictedWire p (pinAt x P) out)).card ≤ 2^(B+Q.card) := calc
    _ ≤ 2^Q.card*(acceptingTables f).card := hS
    _ ≤ 2^Q.card*2^B := Nat.mul_le_mul_left _ hSparse
    _ = _ := by rw [Nat.mul_comm,← pow_add]
  have hAbs (j : Fin g) (hj : j ∈ absorbed) :
      ∃ b : Bool, restrictedWire p (pinAt x P) (.gate j) = fun _ => b := by
    obtain ⟨i,hi,hPath⟩ := hPaths j hj
    have hI := pin_input_constant p x (hSub hi)
    rw [hx i hi] at hI
    exact ⟨seed i,hPath.restricted_eq _ hI⟩
  have hRank := outsideRank_of_absorbed p (pinAt x P) a out paid absorbed (B+Q.card) ha hCount hAbs
  exact ⟨x,a,hx,ha,hCount,hRank,remainingRank_with_paid_and_losses p _ a paid⟩

end PaidRank

section Slice

variable {I J D : Type*} {n g : ℕ}

noncomputable def paidBatchSpan (p : Program signature n g) (base : BitString n)
    (T : I → BitString n) (paid : Finset (Fin g)) :
    Submodule F₂ ((I → F₂) ⧸ rawSpan base T) :=
  Submodule.span F₂ (Set.range (fun j : paid =>
    (rawSpan base T).mkQ (centered p base T (.gate j.val))))

noncomputable def batchAfterPaid (p : Program signature n g) (base : BitString n)
    (T : I → BitString n) (paid : Finset (Fin g)) (j : Fin g) :=
  (paidBatchSpan p base T paid).mkQ ((rawSpan base T).mkQ (centered p base T (.gate j)))

/-- It suffices to find independent directions outside the paid span on a
single slice. They remain independent in the full batch with the same center. -/
theorem outside_independent_lifts_from_slice (p : Program signature n g) (base : BitString n)
    (T : I → BitString n) (select : J → I) (paid : Finset (Fin g)) (pick : D → Fin g)
    (h : LinearIndependent F₂ (fun i => batchAfterPaid p base (T ∘ select) paid (pick i))) :
    LinearIndependent F₂ (fun i => batchAfterPaid p base T paid (pick i)) := by
  let U := paidBatchSpan p base T paid
  let V := paidBatchSpan p base (T ∘ select) paid
  let q := V.mkQ.comp (restrictRawQuotient base T select)
  have hU : U ≤ LinearMap.ker q := Submodule.span_le.mpr (by
    rintro _ ⟨j,rfl⟩
    apply LinearMap.mem_ker.mpr
    change V.mkQ (restrictRawQuotient base T select
      ((rawSpan base T).mkQ (centered p base T (.gate j.val)))) = 0
    rw [restrictRawQuotient_trace]
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact Submodule.subset_span ⟨j,rfl⟩)
  let L := U.liftQ q hU
  apply LinearIndependent.of_comp L
  have he : (L ∘ fun i => batchAfterPaid p base T paid (pick i)) =
      fun i => batchAfterPaid p base (T ∘ select) paid (pick i) := by
    funext i
    change U.liftQ q hU (Submodule.Quotient.mk
      ((rawSpan base T).mkQ (centered p base T (.gate (pick i))))) = _
    rw [Submodule.liftQ_apply]
    change V.mkQ (restrictRawQuotient base T select
      ((rawSpan base T).mkQ (centered p base T (.gate (pick i))))) = _
    rw [restrictRawQuotient_trace]
    rfl
  rwa [he]

end Slice

section Control

open ChargeMultiplicity in
/-- The same signed-AND implementation can have large paid rank under
all-one pins and zero paid rank after preserving one opposite seed.
Only that prescribed seed pays in the padded sparsity count. -/
theorem signedAnd_adaptive_comb (r : ℕ) (hr : 10 ≤ r) :
    let m := JointOrbit.logArity r
    let N := 2^m
    ∃ (c : Circuit signature N 1) (paid : Finset (Fin c.size)),
      c.Computes interpretation (single (GrowingAndOrbit.control r hr)) ∧
      c.size ≤ (5100*(r+1)+1)*N ∧
      ∀ (P : Finset (Fin N)), (∀ i : Fin N, i.val = 0 → i ∈ P) → P.card ≤ 4 →
        N-P.card-1 ≤ paidRank c.program (pinAt (fun _ => true) P) (fun _ => true) paid ∧
        ∃ x : BitString N,
          (∀ i : Fin N, i.val = 0 → x i = false) ∧
          (let pin := pinAt x P
           let a : BitString N := fun _ => true
           restrictedWire c.program pin (c.outputs 0) a = true ∧
           (acceptingTables (restrictedWire c.program pin (c.outputs 0))).card ≤
             2^(descriptionBitBound m+1) ∧
           paidRank c.program pin a paid = 0 ∧
           N-(descriptionBitBound m+2) ≤ remainingRank c.program pin a paid) := by
  let m := JointOrbit.logArity r
  let N := 2^m
  let f := GrowingAndOrbit.control r hr
  have hm : 1024 ≤ m := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans
    (by dsimp [m,JointOrbit.logArity,JointOrbit.Arity]; omega)
  have hN : 8 ≤ N := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 3 ≤ m by omega)
  let zero : Fin N := ⟨0,by omega⟩
  obtain ⟨c,gate,hc,hSize,hTrace⟩ := same_recognizer_with_comb (by omega : 2 ≤ N)
    (signedAnd_constant r hr true)
  let paid := ((Finset.univ : Finset (Fin N)).filter (fun i => 0 < i.val)).image gate
  have hSize' : c.size ≤ (5100*(r+1)+1)*N := calc
    _ ≤ complexity interpretation (single f)+N := hSize
    _ ≤ 5100*(r+1)*N+N := Nat.add_le_add_right (GrowingAndOrbit.control_size r hr) _
    _ = _ := by ring
  refine ⟨c,paid,hc,hSize',?_⟩
  intro P h0 hP
  refine ⟨comb_paidRank_lower c.program gate hTrace P (by omega),?_⟩
  let Q : Finset (Fin N) := {zero}
  have hSub : Q ⊆ P := Finset.singleton_subset_iff.mpr (h0 zero rfl)
  obtain ⟨x,hx,hS⟩ := exists_sparse_completion f P Q hSub (fun _ => false)
  have hzero : x zero = false := hx zero (Finset.mem_singleton_self _)
  let pin := pinAt x P
  let a : BitString N := fun _ => true
  have hEq := NestedFaces.restricted_circuit_eq c hc pin
  have hYes : restrictedWire c.program pin (c.outputs 0) a = true := by
    let flips := P.filter (fun i => x i = false)
    have hd : flips.card ≤ 4 := (Finset.card_filter_le _ _).trans hP
    have he : substitute pin a = PatchedCut.patch flips a := by
      funext i
      by_cases hi : i ∈ P
      · cases he : x i <;> simp [pin,substitute,pinAt,hi,PatchedCut.patch,flips,a,he]
      · simp [pin,substitute,pinAt,hi,PatchedCut.patch,flips,a]
    rw [hEq]
    change f (substitute pin a) = true
    rw [he]
    exact signedAnd_patched_constant r hr true flips hd
  have hCount : (acceptingTables (restrictedWire c.program pin (c.outputs 0))).card ≤
      2^(descriptionBitBound m+1) := by
    rw [hEq]
    calc
      _ ≤ 2^Q.card*(acceptingTables f).card := hS
      _ ≤ 2^Q.card*2^descriptionBitBound m :=
        Nat.mul_le_mul_left _ (GrowingAndOrbit.control_sparse r hr)
      _ = _ := by rw [Nat.mul_comm,← pow_add,Finset.card_singleton]
  have hAbs (j : Fin c.size) (hj : j ∈ paid) :
      ∃ b : Bool, restrictedWire c.program pin (.gate j) = fun _ => b := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    refine ⟨false,funext fun z => ?_⟩
    change c.program.trace interpretation (substitute pin z) (.gate (gate i)) = false
    apply (hTrace i (Finset.mem_filter.mp hi).2 _).mpr
    refine ⟨zero,by change 0 ≤ i.val; omega,?_⟩
    have hz := pin_input_constant c.program x (h0 zero rfl)
    exact (congrFun hz z).trans hzero
  have hPaid := paidRank_le_unabsorbed c.program pin a paid paid hAbs
  rw [Finset.sdiff_self,Finset.card_empty] at hPaid
  have hPaid0 := Nat.le_zero.mp hPaid
  have hR := remainingRank_lower_of_sparse c.program pin a (c.outputs 0) paid
    (descriptionBitBound m+1) hYes hCount
  change N ≤ _ at hR
  rw [hPaid0] at hR
  refine ⟨x,fun i h => (Fin.ext h : i = zero).symm ▸ hzero,hYes,hCount,hPaid0,?_⟩
  change N-(descriptionBitBound m+2) ≤ remainingRank c.program pin a paid
  omega

open JointOrbit in
/-- The directions found by the zero pin survive in the full trace batch
after quotienting all of the same comb gates. The center is the accepting
table used on the adaptive slice. -/
theorem signedAnd_outside_independent_full (r : ℕ) (hr : 10 ≤ r) :
    let m := logArity r
    let N := 2^m
    ∃ (c : Circuit signature N 1) (paid : Finset (Fin c.size)) (base : BitString N)
      (pick : Fin (N-(descriptionBitBound m+2)) ↪ Fin c.size),
      c.Computes interpretation (single (GrowingAndOrbit.control r hr)) ∧
      c.size ≤ (5100*(r+1)+1)*N ∧ GrowingAndOrbit.control r hr base = true ∧
      (∀ i, pick i ∉ paid) ∧
      LinearIndependent F₂ (fun i => batchAfterPaid c.program base id paid (pick i)) := by
  let m := logArity r
  let N := 2^m
  have hn : 0 < N := Nat.two_pow_pos _
  let zero : Fin N := ⟨0,hn⟩
  let P : Finset (Fin N) := {zero}
  obtain ⟨c,paid,hc,hSize,h⟩ := signedAnd_adaptive_comb r hr
  have hZ (i : Fin N) (hi : i.val=0) : i ∈ P :=
    Finset.mem_singleton.mpr (Fin.ext hi)
  obtain ⟨_,x,_,hYes,_,_,hRank⟩ := h P hZ (by simp [P])
  let pin := pinAt x P
  let a : BitString N := fun _ => true
  let base := substitute pin a
  let select (z : Fin N → F₂) := substitute pin (perturb a z)
  have he : GrowingAndOrbit.control r hr base = true := by
    have hTrace : c.program.trace interpretation base (c.outputs 0) =
        GrowingAndOrbit.control r hr base := congrFun (hc base) 0
    exact hTrace.symm.trans hYes
  obtain ⟨pick,hP,hLI⟩ := independent_outside_paid c.program pin a paid
  let emb : Fin (N-(descriptionBitBound m+2)) ↪ Fin (remainingRank c.program pin a paid) :=
    ⟨Fin.castLE hRank,Fin.castLE_injective hRank⟩
  have hsmall : LinearIndependent F₂ (fun i => batchAfterPaid c.program base (id ∘ select)
      paid (pick (emb i))) := hLI.comp emb emb.injective
  refine ⟨c,paid,base,emb.trans pick,hc,hSize,he,fun i => (Finset.mem_sdiff.mp (hP (emb i))).2,?_⟩
  exact outside_independent_lifts_from_slice c.program base id select paid (emb.trans pick) hsmall

end Control

section FiniteBound

open ForestBlockPinning MultiBlockPinning QuadraticForest TwoCornerStructure FreshCharges

/-- Compare with the seeded exit restriction. Leaving every pin free to
take a minority value keeps the exact factorial reserve. Three covered
blocks still yield 384 direct reader losses. -/
theorem mcsp32_unseeded_sparse_block_floor :
    8620574360 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c,hc,hMin⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single (mcspSquare 32))
  let p := c.program
  let root := c.outputs 0
  let S := needInputs p root false
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hNeed : 2^32 ≤ S.card+18903 :=
    card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity false h0
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ,Fintype.card_fin] at hMiss
  obtain ⟨E,hE,hCover⟩ := exists_covered_blocks (a := 24) (d := 8) S 3 (by
    norm_num at hNeed hMiss ⊢
    omega)
  let P := blocks (d := 8) E
  have hP : P.card = 768 := by rw [show P = blocks (d := 8) E from rfl,card_blocks,hE]; decide
  have hQ (x : BitString (2^32)) (a : BitString 32) (b : Bool) (u w : BitString 32) :
      mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 (quad a b u w))) = true := by
    apply accepted_after_blocks_pin (a := 24) (k := 2) (l := 6)
    have hCost := QuadraticPinning.complexity_quad_shared_le a b u w
    rw [hE]
    norm_num [lookupBankCost] at hCost ⊢
    omega
  obtain ⟨x,hReaders,hForest,hBudget⟩ := pin_losses_and_residual_with_count c hc hMin
    (by decide) (show 18903 < (2:ℕ)^32 by decide) mcsp32_tight_sparsity
    P P (readerGates p root) Finset.Subset.rfl
    (fun i hi => need_input_has_reader hc0 hc1 (hCover hi)) hQ
  have hPart := Finset.card_le_card (Finset.inter_subset_right
    (s₁ := readerGates p root)
    (s₂ := fresh c.program Sum.inl \ fresh c.program (pinAt x P)))
  rw [hP] at hReaders
  rw [← hMin]
  norm_num at hForest
  omega

end FiniteBound

#print axioms outsideRank_of_absorbed
#print axioms choose_absorbing_sparse_pins
#print axioms outside_independent_lifts_from_slice
#print axioms signedAnd_adaptive_comb
#print axioms signedAnd_outside_independent_full
#print axioms mcsp32_unseeded_sparse_block_floor

end PvsNP.Frontier.ForestAbsorptionRank
