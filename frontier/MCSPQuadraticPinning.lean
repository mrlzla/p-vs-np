module

public import MCSPAffineProbes

/-! Shared repair circuits preserve rank-one quadratic witnesses along a
longer adaptive pinning schedule. The residual forest bound and the lost
original gate indices are counted separately. -/

@[expose] public section

namespace PvsNP.Frontier.QuadraticPinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates SuperTwoN QuadraticForest MinorityResidual
open ForestPinning RestrictionCharges FreshCharges NestedFaces
open scoped Classical BigOperators

section PointRepair

private def blockMatch {n k : ℕ} (w : Fin k → Fin n) (a : BitString k) :
    BooleanFunction n :=
  fun x => decide ((x ∘ w) = a)

private theorem match_cons_iff {n k : ℕ} (w : Fin (k+1) → Fin n)
    (a : BitString (k+1)) (x : BitString n) :
    blockMatch w a x = true ↔
      x (w 0) = a 0 ∧ blockMatch (w ∘ Fin.succ) (Fin.tail a) x = true := by
  simp only [blockMatch, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrArg Fin.tail h⟩
  · rintro ⟨h0, ht⟩
    funext i
    refine Fin.cases h0 (fun j => congrFun ht j) i

private theorem literal_mem {n : ℕ} (i : Fin n) (b : Bool) :
    (fun x : BitString n => decide (x i = b)) ∈ inputs n ∪ negatives n := by
  cases b
  · exact Or.inr ⟨i, funext fun x => by
      change (!(x i)) = decide (x i = false)
      cases x i <;> rfl⟩
  · exact Or.inl ⟨i, funext fun x => by
      change x i = decide (x i = true)
      cases x i <;> rfl⟩

private theorem synth_block_matches {n : ℕ} :
    ∀ (k : ℕ) (w : Fin (k+1) → Fin n),
      Synthesis interpretation (inputs n ∪ negatives n)
        (Set.range (blockMatch w)) (2^(k+2)-4)
  | 0, w => by
    apply Synthesis.of_subset
    rintro _ ⟨a, rfl⟩
    have he (x : BitString n) : blockMatch w a x = decide (x (w 0) = a 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [blockMatch, decide_eq_true_eq]
      exact ⟨fun h => congrFun h 0, fun h => funext fun i =>
        (Fin.eq_zero i).symm ▸ h⟩
    rw [funext he]
    exact literal_mem (w 0) (a 0)
  | k+1, w => by
    let S := inputs n ∪ negatives n
    let tail := blockMatch (w ∘ Fin.succ)
    have hTail : Synthesis interpretation S (Set.range tail) (2^(k+2)-4) :=
      synth_block_matches k (w ∘ Fin.succ)
    have hNext (a : BitString (k+2)) :
        Synthesis interpretation (S ∪ Set.range tail) {blockMatch w a} 1 := by
      let literal : BooleanFunction n := fun x => decide (x (w 0) = a 0)
      have h0 : Synthesis interpretation (S ∪ Set.range tail) {literal} 0 :=
        Synthesis.of_mem (Or.inl (literal_mem (w 0) (a 0)))
      have h1 : Synthesis interpretation (S ∪ Set.range tail) {tail (Fin.tail a)} 0 :=
        Synthesis.of_mem (Or.inr ⟨_, rfl⟩)
      exact Synthesis.congr_iff (h0.and h1) (fun x => by
        simpa only [Bool.and_eq_true, literal, decide_eq_true_eq, tail]
          using (match_cons_iff w a x).symm)
    have hAll : Synthesis interpretation (S ∪ Set.range tail) (Set.range (blockMatch w)) (2^(k+2)) := by
      simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, Nat.mul_one]
        using Synthesis.family (blockMatch w) (fun _ => 1) hNext
    apply (hTail.trans hAll).mono Set.Subset.rfl Set.Subset.rfl
    have hDouble : 2^(k+1+2) = 2 * (2^(k+2)) := by
      rw [show k+1+2 = k+2+1 by omega, pow_succ']
    rw [hDouble]
    have hPow : 4 ≤ 2^(k+2) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ k+2)
    omega

private theorem synth_nonempty_and {n : ℕ} {S : Set (BooleanFunction n)} :
    ∀ {k : ℕ} (f : Fin (k+1) → BooleanFunction n), (∀ i, f i ∈ S) →
      Synthesis interpretation S {fun x => decide (∀ i, f i x = true)} k
  | 0, f, hf =>
    Synthesis.congr_iff (Synthesis.of_mem (hf 0)) (fun x => by
      simp only [decide_eq_true_eq]
      exact ⟨fun h i => (Fin.eq_zero i).symm ▸ h, fun h => h 0⟩)
  | k+1, f, hf => by
    have h := (Synthesis.of_mem (hf 0)).and (synth_nonempty_and (f ∘ Fin.succ) (fun i => hf i.succ))
    have h' := Synthesis.congr_iff h (g := fun x => decide (∀ i, f i x = true)) (fun x => by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Fin.forall_fin_succ, Function.comp_apply])
    simpa only [Nat.zero_add] using h'

section Blocks

variable {m b w : ℕ}

/-- The padded last block reuses input coordinates; all original coordinates
still occur among the block checks. -/
private def chunk (hb : 0 < m) (block : Fin (b+1)) (offset : Fin (w+1)) : Fin m :=
  ⟨(finProdFinEquiv (block, offset)).val % m, Nat.mod_lt _ hb⟩

private theorem chunk_surjective (hm : 0 < m) (hCover : m ≤ (b+1)*(w+1)) :
    Function.Surjective (fun p : Fin (b+1) × Fin (w+1) => chunk hm p.1 p.2) := by
  intro i
  let j : Fin ((b+1)*(w+1)) := ⟨i.val, i.isLt.trans_le hCover⟩
  obtain ⟨⟨block, offset⟩, he⟩ := finProdFinEquiv.surjective j
  refine ⟨(block, offset), Fin.ext ?_⟩
  simp only [chunk, he, j, Nat.mod_eq_of_lt i.isLt]

private def blockBank (hm : 0 < m) (block : Fin (b+1)) : Set (BooleanFunction m) :=
  Set.range (blockMatch (chunk (w := w) hm block))

/-- Shared width-`w+1` address checks. Each repair point uses `b` binary
AND gates and one OR in the disjunction. -/
theorem point_indicator_complexity_le (hm : 0 < m) (hCover : m ≤ (b+1)*(w+1))
    (D : Finset (Fin (2^m))) :
    complexity interpretation (single (fun x : BitString m => decide (BitString.equivFin m x ∈ D))) ≤
      m + (b+1)*(2^(w+2)-4) + (b+1)*D.card + 1 := by
  let S := inputs m ∪ negatives m
  let B := ⋃ block : Fin (b+1), blockBank (w := w) hm block
  have hs : Synthesis interpretation S B ((b+1)*(2^(w+2)-4)) := by
    have h := Synthesis.iUnion (blockBank (w := w) hm) (fun _ => 2^(w+2)-4)
      (fun block : Fin (b+1) => synth_block_matches w (chunk hm block))
    simpa only [B, Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] using h
  let select (block : Fin (b+1)) : Fin (w+1) → Fin m := chunk hm block
  let test (u : Fin (2^m)) (block : Fin (b+1)) :=
    blockMatch (select block) ((BitString.equivFin m).symm u ∘ select block)
  let point (u : Fin (2^m)) (x : BitString m) := decide (∀ block, test u block x = true)
  have hPoint (u : Fin (2^m)) : Synthesis interpretation (S ∪ B) {point u} b := by
    apply synth_nonempty_and
    intro block
    exact Or.inr (Set.mem_iUnion.mpr ⟨block, ⟨_, rfl⟩⟩)
  have hv := Synthesis.exists_mem D point (fun _ => b) (fun u _ => hPoint u)
  have hSpec (x : BitString m) (u : Fin (2^m)) : point u x = true ↔ BitString.equivFin m x = u := by
    simp only [point, test, blockMatch, decide_eq_true_eq, ← Equiv.eq_symm_apply]
    constructor
    · intro h
      funext i
      obtain ⟨⟨block, offset⟩, rfl⟩ := chunk_surjective hm hCover i
      exact congrFun (h block) offset
    · intros h block
      rw [h]
  have hv' := Synthesis.congr_iff hv (g := fun x => decide (BitString.equivFin m x ∈ D)) (fun x => by
    simp only [decide_eq_true_eq, hSpec]
    exact ⟨fun ⟨u, hu, he⟩ => he.symm ▸ hu, fun hu => ⟨_, hu, rfl⟩⟩)
  have hb := ((synthesis_negatives m).trans (hs.trans hv')).complexity_le
  simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm D.card (b+1), Nat.add_assoc] using hb

end Blocks

/-- The original four-bit construction is an instance of the padded decoder. -/
theorem point_indicator_complexity_le_32 (D : Finset (Fin (2^32))) :
    complexity interpretation (single (fun x : BitString 32 => decide (BitString.equivFin 32 x ∈ D))) ≤
      257 + 8*D.card := by
  have h := point_indicator_complexity_le (b := 7) (w := 3) (by decide) (by decide) D
  change _ ≤ 32 + 8*28 + 8*D.card + 1 at h
  omega

end PointRepair

section ParitySharing

private def coefficientClass {m : ℕ} (weights : Fin 3 → BitString m) (i : Fin m) : BitString 3 :=
  fun j => weights j i

private noncomputable def group {m : ℕ} (weights : Fin 3 → BitString m) (b : BitString 3) :=
  Finset.univ.filter fun i => coefficientClass weights i = b

private noncomputable def groupParity {m : ℕ} (weights : Fin 3 → BitString m) (b : BitString 3) :
    BooleanFunction m :=
  fun x => ∑ i ∈ group weights b, x i

private def selects (j : Fin 3) : Finset (BitString 3) :=
  Finset.univ.filter fun b => b j = true

private theorem selects_card (j : Fin 3) : (selects j).card = 4 := by
  fin_cases j <;> decide

private theorem group_dot {m : ℕ} (weights : Fin 3 → BitString m) (j : Fin 3) (x : BitString m) :
    (∑ b ∈ selects j, groupParity weights b x) = dot (weights j) x := by
  rw [AffineProbes.dot_eq_sum]
  have h := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Fin m))
    (selects j) (coefficientClass weights) (fun i => x i)
  rw [show (∑ b ∈ selects j, groupParity weights b x) =
      ∑ b ∈ selects j, ∑ i ∈ group weights b, x i from rfl]
  change (∑ b ∈ selects j, ∑ i ∈ group weights b, x i) = _ at h
  rw [h, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [selects, coefficientClass, Finset.mem_filter, Finset.mem_univ, true_and]
  cases weights j i <;> rfl

private theorem synth_nonempty_sum {m : ℕ} {S : Set (BooleanFunction m)} {ι : Type*}
    (F : ι → BooleanFunction m) (I : Finset ι) (hI : I.Nonempty) (hF : ∀ i ∈ I, F i ∈ S) :
    Synthesis interpretation S {fun x => ∑ i ∈ I, F i x} (4*(I.card-1)) := by
  induction I using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hI).elim
  | @insert i I hi ih =>
    have h0 : Synthesis interpretation S {F i} 0 := Synthesis.of_mem (hF i (Finset.mem_insert_self ..))
    by_cases h : I.Nonempty
    · have htail := ih h (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have hxor := h0.xor htail
      have he : (fun x => ∑ j ∈ insert i I, F j x) =
          fun x => F i x ^^ (∑ j ∈ I, F j x) := by
        funext x
        rw [Finset.sum_insert hi, Bool.add_eq_xor]
      rw [he, Finset.card_insert_of_notMem hi]
      have hPos := h.card_pos
      exact hxor.mono Set.Subset.rfl Set.Subset.rfl (by omega)
    · rw [Finset.not_nonempty_iff_eq_empty.mp h]
      simpa using h0

/-- Share the three parity computations of a rank-one quadratic. Each input
enters only one coefficient class before class parities are combined. -/
theorem complexity_quad_shared_le {m : ℕ} (a : BitString m) (b0 : Bool) (c d : BitString m) :
    complexity interpretation (single (quad a b0 c d)) ≤ 4*m+43 := by
  let weights : Fin 3 → BitString m := ![a,c,d]
  let bank := Set.range (groupParity weights)
  let Z : Set (BooleanFunction m) := {fun _ => false}
  have hZero : Synthesis interpretation (inputs m) Z 1 := Synthesis.const false
  have hBankAux : Synthesis interpretation (inputs m ∪ Z) bank (4*m) := by
    have hOne (b : BitString 3) :
        Synthesis interpretation (inputs m ∪ Z) {groupParity weights b} (4*(group weights b).card) := by
      by_cases h : (group weights b).Nonempty
      · apply (synth_nonempty_sum (fun i (x : BitString m) => x i) (group weights b) h
          (fun i _ => show (fun x : BitString m => x i) ∈ inputs m ∪ Z from Or.inl ⟨i, rfl⟩)).mono
          Set.Subset.rfl Set.Subset.rfl
        omega
      · have he : group weights b = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        have hf : Synthesis interpretation (inputs m ∪ Z) {fun _ => false} 0 :=
          Synthesis.of_mem (Or.inr rfl)
        have hEq : groupParity weights b = fun _ => false := by
          funext x
          rw [groupParity, he, Finset.sum_empty]
          rfl
        rw [hEq, he]
        exact hf
    have h := Synthesis.family (groupParity weights) (fun b => 4*(group weights b).card) hOne
    have hCount : (∑ b : BitString 3, (group weights b).card) = m := by
      simpa only [group, Finset.mem_univ, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
        using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m))
          (Finset.univ : Finset (BitString 3)) (coefficientClass weights)
    simpa only [bank, ← Finset.mul_sum, hCount] using h
  have hBank := hZero.trans hBankAux
  let S := inputs m ∪ bank
  have hDot (j : Fin 3) : Synthesis interpretation S {dot (weights j)} 12 := by
    have hn : (selects j).Nonempty := Finset.card_pos.mp (by rw [selects_card]; decide)
    have h := synth_nonempty_sum (groupParity weights) (selects j) hn
      (fun b _ => show groupParity weights b ∈ S from Or.inr ⟨b, rfl⟩)
    rw [selects_card] at h
    have he : (fun x => ∑ b ∈ selects j, groupParity weights b x) = dot (weights j) :=
      funext (group_dot weights j)
    rw [he] at h
    exact h
  have h0 : Synthesis interpretation S {affine a b0} 13 := by
    have ha : Synthesis interpretation S {dot a} 12 := hDot 0
    cases b0
    · exact Synthesis.congr_iff (ha.mono Set.Subset.rfl Set.Subset.rfl (by decide)) (fun x => by simp [affine])
    · exact Synthesis.congr_iff ha.not (fun x => by simp [affine])
  have h1 : Synthesis interpretation S {dot c} 12 := hDot 1
  have h2 : Synthesis interpretation S {dot d} 12 := hDot 2
  have h := (hBank.trans (h0.xor (h1.and h2))).complexity_le
  change complexity interpretation (single (quad a b0 c d)) ≤ _ at h
  omega

end ParitySharing

section Pinning

/-- Repair a small represented circuit after fixing arbitrary table entries. -/
theorem pinned_probe_accepted {m b w : ℕ} (hm : 0 < m) (hCover : m ≤ (b+1)*(w+1))
    (f : BooleanFunction m) (x : BitString (2^m)) (P : Finset (Fin (2^m)))
    (hBudget : complexity interpretation (single f) + m + (b+1)*(2^(w+2)-4) +
      (b+1)*P.card + 5 ≤ m^2) :
    mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m f)) = true := by
  let T := MCSP.truthTable m f
  let D := P.filter fun i => T i ≠ x i
  let repair : BooleanFunction m := fun z => decide (BitString.equivFin m z ∈ D)
  have hEq : MCSP.truthTable m (fun z => f z ^^ repair z) = substitute (pinAt x P) T := by
    funext i
    simp only [MCSP.truthTable_apply, repair, Equiv.apply_symm_apply]
    change (T i ^^ decide (i ∈ D)) = substitute (pinAt x P) T i
    by_cases hi : i ∈ P
    · rw [substitute_inr (show pinAt x P i = .inr (x i) by simp [pinAt, hi])]
      simp only [D, Finset.mem_filter, hi, true_and]
      cases T i <;> cases x i <;> decide
    · rw [substitute_inl (show pinAt x P i = .inl i by simp [pinAt, hi])]
      simp [D, hi]
  change mcspSquare m (substitute (pinAt x P) T) = true
  rw [← hEq, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  have hD : D.card ≤ P.card := Finset.card_filter_le _ _
  have hMask : complexity interpretation (single repair) ≤
      m + (b+1)*(2^(w+2)-4) + (b+1)*D.card + 1 :=
    point_indicator_complexity_le hm hCover D
  have hCount := Nat.mul_le_mul_left (b+1) hD
  exact (complexity_xor_le f repair).trans (by omega)

theorem pinned_probe_accepted_32 (f : BooleanFunction 32) (x : BitString (2^32))
    (P : Finset (Fin (2^32)))
    (hBudget : complexity interpretation (single f)+261+8*P.card ≤ 32^2) :
    mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 f)) = true := by
  apply pinned_probe_accepted (b := 7) (w := 3) (by decide) (by decide)
  change complexity interpretation (single f) + 32 + 8*28 + 8*P.card + 5 ≤ 1024
  omega

/-- Every rank-one quadratic has a YES completion for any assignment to 74 table entries. -/
theorem pinned_quad_accepted_32 (x : BitString (2^32)) (P : Finset (Fin (2^32)))
    (hP : P.card ≤ 74) (a : BitString 32) (b : Bool) (c d : BitString 32) :
    mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 (quad a b c d))) = true := by
  apply pinned_probe_accepted_32
  have hq := complexity_quad_shared_le a b c d
  omega

/-- A family extending the gated-parity witness. The gate coordinate,
suffix parity and affine term can all vary independently. -/
def gatedProbe (j : Fin 32) (a : BitString 32) (b : Bool) (d : BitString 32) :
    BooleanFunction 32 :=
  fun z => affine a b z ^^ (z j && dot d z)

theorem gatedProbe_recovers_gatedParity :
    gatedProbe 0 (zeroVec 32) false (Fin.cons false (fun _ : Fin 31 => true)) =
      AffineProbes.gatedParity (k := 31) := by
  funext z
  have hz : affine (zeroVec 32) false z = false := by
    simp only [affine, dot_zero_left, Bool.false_xor]
  simp [gatedProbe, hz, dot, AffineProbes.gatedParity]

theorem pinned_gated_family_accepted_32 (x : BitString (2^32)) (P : Finset (Fin (2^32)))
    (hP : P.card ≤ 74) (j : Fin 32) (a : BitString 32) (b : Bool) (d : BitString 32) :
    mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 (gatedProbe j a b d))) = true := by
  have he : quad a b (fun i => decide (i = j)) d = gatedProbe j a b d := by
    funext z
    simp only [quad, gatedProbe, dot_basisVec]
  rw [← he]
  exact pinned_quad_accepted_32 x P hP a b _ d

/-- Count original gate indices that become redundant under the adaptive
pins, separately from the gates needed by the padded residual. -/
theorem original_losses_and_residual {m t : ℕ} (c : Circuit signature (2^m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (hFew : descriptionBitBound m < 2^m)
    (hRepair : ∀ (x : BitString (2^m)) (P : Finset (Fin (2^m))), P.card ≤ t →
      ∀ (a : BitString m) (v : Bool) (u w : BitString m),
        mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad a v u w))) = true) :
    ∃ (x : BitString (2^m)) (P : Finset (Fin (2^m))), P.card = t ∧
      let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      280 * (2 * 2^m) + 2 * 2^m ≤
        280 * (complexity interpretation (single f) + 2 * descriptionBitBound m + 1) +
          17 * descriptionBitBound m ∧
      t ≤ removed.card ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  have hZero (x : BitString (2^m)) (P : Finset (Fin (2^m))) (hP : P.card ≤ t) :
      mcspSquare m (substitute (pinAt x P) (fun _ => false)) = true := by
    have h := hRepair x P hP (zeroVec m) false (zeroVec m) (zeroVec m)
    have he : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  obtain ⟨x, P, hP, hSparse, hLoss⟩ :=
    minority_pinning_run_of_zero m c hc hFew t (fun x P h => hZero x P h.le)
  let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
  change (acceptingTables f).card ≤ _ at hSparse
  have hQuad (a : BitString m) (b : Bool) (u v : BitString m) :
      f (fun i => quad a b u v ((BitString.equivFin m).symm i)) = true :=
    hRepair x P hP.le a b u v
  have hR := quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding hSparse hQuad
  have hEq : restrictedWire c.program (pinAt x P) (c.outputs 0) = f :=
    restricted_circuit_eq c hc (pinAt x P)
  have hNon : ¬ ∃ b : Bool, restrictedWire c.program (pinAt x P) (c.outputs 0) = fun _ => b := by
    rintro ⟨b, hb⟩
    rw [hEq] at hb
    have hTrue : b = true := (congrFun hb (fun _ => false)).symm.trans (hZero x P hP.le)
    rw [hb, hTrue] at hSparse
    simp only [acceptingTables, Finset.filter_true, Finset.card_univ, BitString.card] at hSparse
    exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hFew)) hSparse
  have hSynth := fresh_complexity_le_of_nonconstant c.program (pinAt x P) (c.outputs 0) hNon
  rw [hEq] at hSynth
  have hAll : (fresh c.program (Sum.inl : Fin (2^m) → Fin (2^m) ⊕ Bool)).card ≤ c.size := by
    simpa using Finset.card_le_univ (fresh c.program (Sum.inl : Fin (2^m) → Fin (2^m) ⊕ Bool))
  have hSub : fresh c.program (pinAt x P) ⊆ fresh c.program Sum.inl :=
    fresh_nested c.program Sum.inl (pinAt x P)
  have hPartition := Finset.card_sdiff_add_card_eq_card hSub
  refine ⟨x, P, hP, hR, by omega, ?_⟩
  change complexity interpretation (single f) +
    (fresh c.program Sum.inl \ fresh c.program (pinAt x P)).card ≤ c.size
  omega

/-- The arity-32 result specializes the general disjoint accounting. -/
theorem original_losses_and_residual_32 (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    ∃ (x : BitString (2^32)) (P : Finset (Fin (2^32))), P.card = 74 ∧
      let f : BooleanFunction (2^32) := fun y => mcspSquare 32 (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      8620555905 ≤ complexity interpretation (single f) ∧
      74 ≤ removed.card ∧
      complexity interpretation (single f) + removed.card ≤ c.size := by
  obtain ⟨x, P, hP, hForest, hCount, hBudget⟩ :=
    original_losses_and_residual c hc (by decide) pinned_quad_accepted_32
  rw [show descriptionBitBound 32 = 27672 by decide] at hForest
  change 280 * (2 * 4294967296) + 2 * 4294967296 ≤
    280 * (complexity interpretation
      (single (fun y => mcspSquare 32 (substitute (pinAt x P) y))) + 2 * 27672 + 1) +
        17 * 27672 at hForest
  have hResid : 8620555905 ≤ complexity interpretation
      (single (fun y => mcspSquare 32 (substitute (pinAt x P) y))) := by omega
  exact ⟨x, P, hP, hResid, hCount, hBudget⟩

theorem mcspSquare_32_shared_repair :
    8620555979 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  obtain ⟨x, P, _, hr, hg, hsum⟩ := original_losses_and_residual_32 c hc
  omega

end Pinning

section Scaling

/-- The number of adaptive pins supported by logarithmic-width address blocks. -/
def scaledPins (m : ℕ) : ℕ := m * m.log2 / 2

theorem description_le_polynomial (m : ℕ) (hm : 16 ≤ m) :
    descriptionBitBound m ≤ (4*m+12)*m^2 := by
  have hLog := Nat.log2_le_self (m+1)
  have hSq : 6*m ≤ m^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right m (by omega : 6 ≤ m)
  have hCoeff : 3 + 4*((m+1).log2+1) ≤ 4*m+11 := by omega
  have hTerm := Nat.mul_le_mul_right (m^2) hCoeff
  change 4*((m+1).log2+1) + (3+4*((m+1).log2+1))*m^2 ≤ _
  rw [show (4*m+12)*m^2 = (4*m+11)*m^2 + m^2 by ring]
  omega

private theorem description_lt_table_length (m : ℕ) (hm : 256 ≤ m) :
    descriptionBitBound m < 2^m := by
  have hSq : 6*m ≤ m^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right m (by omega : 6 ≤ m)
  calc
    _ ≤ (4*m+12)*m^2 := description_le_polynomial m (by omega)
    _ < m^2*m^2 := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega : 0 < m))
    _ = m^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp m (by omega)

private theorem scaled_block_budget (m : ℕ) (hm : 256 ≤ m) :
    let b := (m-1)/m.log2
    let w := m.log2-1
    m ≤ (b+1)*(w+1) ∧
      (4*m+43) + m + (b+1)*(2^(w+2)-4) + (b+1)*scaledPins m + 5 ≤ m^2 := by
  let h := m.log2
  let b := (m-1)/h
  let w := h-1
  change m ≤ (b+1)*(w+1) ∧
    (4*m+43) + m + (b+1)*(2^(w+2)-4) + (b+1)*scaledPins m + 5 ≤ m^2
  have hh : 8 ≤ h := (Nat.le_log2 (by omega : m ≠ 0)).mpr hm
  have hw : w+1 = h := by dsimp only [w]; omega
  have hp : 2^h ≤ m := Nat.log2_self_le (by omega : m ≠ 0)
  have hLePow (k : ℕ) (hk : 8 ≤ k) : 8*k ≤ 2^k := by
    refine Nat.le_induction (m := 8) (P := fun i _ => 8*i ≤ 2^i) (by decide) ?_ k hk
    intro i hi ih
    rw [pow_succ']
    omega
  have hHM : 8*h ≤ m := (hLePow h hh).trans hp
  have hMod : (m-1)%h < h := Nat.mod_lt _ (by omega)
  have hSplit : (m-1)%h + b*h = m-1 := by
    simpa only [b, Nat.mul_comm b h, Nat.mul_comm ((m-1)/h) h] using Nat.mod_add_div (m-1) h
  have hBlocks : m ≤ (b+1)*h ∧ (b+1)*h ≤ m+h := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hCap : 8*((b+1)*h) ≤ 9*m := by omega
  refine ⟨hw ▸ hBlocks.1, ?_⟩
  have hTwo : 2^(w+2)-4 ≤ 2*m := by
    rw [show w+2 = h+1 by omega, pow_succ']
    omega
  have hBlockCount : 64*(b+1) ≤ 9*m := calc
    _ = 8*((b+1)*8) := by ring
    _ ≤ 8*((b+1)*h) := Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left (b+1) hh)
    _ ≤ _ := hCap
  have hDecoder : 32*((b+1)*(2^(w+2)-4)) ≤ 9*m^2 := calc
    _ ≤ 32*((b+1)*(2*m)) := Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left (b+1) hTwo)
    _ = (64*(b+1))*m := by ring
    _ ≤ (9*m)*m := Nat.mul_le_mul_right m hBlockCount
    _ = _ := by ring
  have hPins : 2*scaledPins m ≤ m*h := by
    change 2*(m*h/2) ≤ m*h
    omega
  have hRepair : 32*((b+1)*scaledPins m) ≤ 18*m^2 := calc
    _ = 16*((b+1)*(2*scaledPins m)) := by ring
    _ ≤ 16*((b+1)*(m*h)) := Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left (b+1) hPins)
    _ = (8*((b+1)*h))*(2*m) := by ring
    _ ≤ (9*m)*(2*m) := Nat.mul_le_mul_right (2*m) hCap
    _ = _ := by ring
  have hFixed : 32*(5*m+48) ≤ 5*m^2 := calc
    _ ≤ 200*m := by omega
    _ ≤ (5*m)*m := Nat.mul_le_mul_right m (by omega)
    _ = _ := by ring
  omega

/-- All rank-one quadratic probes survive arbitrary pins through the
logarithmic-width repair budget. -/
theorem pinned_quad_accepted_scaled {m : ℕ} (hm : 256 ≤ m)
    (x : BitString (2^m)) (P : Finset (Fin (2^m))) (hP : P.card ≤ scaledPins m)
    (a : BitString m) (v : Bool) (c d : BitString m) :
    mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad a v c d))) = true := by
  let b := (m-1)/m.log2
  let w := m.log2-1
  obtain ⟨hCover, hBudget⟩ := scaled_block_budget m hm
  change m ≤ (b+1)*(w+1) at hCover
  change (4*m+43) + m + (b+1)*(2^(w+2)-4) + (b+1)*scaledPins m + 5 ≤ m^2 at hBudget
  apply pinned_probe_accepted (by omega) hCover
  have hCost := complexity_quad_shared_le a v c d
  have hPatch := Nat.mul_le_mul_left (b+1) hP
  omega

/-- On every arity from 256 on, the original gate indices lost under the
pins contribute at least `⌊m log₂(m) / 2⌋` in addition to the full forest
bound for the residual. -/
theorem original_losses_and_residual_scaled {m : ℕ} (hm : 256 ≤ m)
    (c : Circuit signature (2^m) 1) (hc : c.Computes interpretation (single (mcspSquare m))) :
    ∃ (x : BitString (2^m)) (P : Finset (Fin (2^m))), P.card = scaledPins m ∧
      let f : BooleanFunction (2^m) := fun y => mcspSquare m (substitute (pinAt x P) y)
      let removed := fresh c.program Sum.inl \ fresh c.program (pinAt x P)
      280 * (2 * 2^m) + 2 * 2^m ≤
        280 * (complexity interpretation (single f) + 2 * descriptionBitBound m + 1) +
          17 * descriptionBitBound m ∧
      scaledPins m ≤ removed.card ∧
      complexity interpretation (single f) + removed.card ≤ c.size :=
    original_losses_and_residual c hc (description_lt_table_length m hm)
      (pinned_quad_accepted_scaled hm)

/-- The full-size quadratic forest bound gains all the original gate losses. -/
theorem mcspSquare_scaled_pinning {m : ℕ} (hm : 256 ≤ m) :
    280 * (2 * 2^m + scaledPins m) + 2 * 2^m ≤
      280 * (complexity interpretation (single (mcspSquare m)) + 2 * descriptionBitBound m + 1) +
        17 * descriptionBitBound m := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  obtain ⟨x, P, _, hForest, hCount, hBudget⟩ := original_losses_and_residual_scaled hm c hc
  omega

end Scaling

section RepairCapacity

/-- Place one chosen repair point in each of `t` disjoint address blocks.
If every such repaired zero table fits the cutoff, their descriptions must
encode `t*q` independent bits. -/
theorem uniform_zero_repair_capacity {m t q : ℕ} (hRoom : t*2^q ≤ 2^m)
    (hRepair : ∀ (x : BitString (2^m)) (P : Finset (Fin (2^m))), P.card ≤ t →
      mcspSquare m (substitute (pinAt x P) (fun _ => false)) = true) :
    t*q ≤ descriptionBitBound m := by
  let addr : Fin t × Fin (2^q) ↪ Fin (2^m) :=
    finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hRoom)
  let indices (u : Fin t → Fin (2^q)) :=
    Finset.univ.image fun j => addr (j, u j)
  let table (u : Fin t → Fin (2^q)) : BitString (2^m) :=
    fun i => decide (i ∈ indices u)
  have hAccept (u : Fin t → Fin (2^q)) : mcspSquare m (table u) = true := by
    have hCard : (indices u).card ≤ t := Finset.card_image_le.trans (by simp)
    have h := hRepair (fun _ => true) (indices u) hCard
    have he : substitute (pinAt (fun _ => true) (indices u)) (fun _ => false) = table u := by
      funext i
      by_cases hi : i ∈ indices u <;> simp [substitute, pinAt, table, hi]
    rwa [he] at h
  have hInj : Function.Injective table := by
    intro u v he
    funext j
    have hu : addr (j, u j) ∈ indices u := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hv : addr (j, u j) ∈ indices v := by
      have hb := congrFun he (addr (j, u j))
      simpa only [table, hu, decide_true, decide_eq_true_eq] using hb.symm
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hv
    have hPair := addr.injective hk
    have hIndex : k = j := congrArg Prod.fst hPair
    subst k
    exact (congrArg Prod.snd hPair).symm
  let into (u : Fin t → Fin (2^q)) : acceptingTables (mcspSquare m) :=
    ⟨table u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAccept u⟩⟩
  have hCard := (Fintype.card_le_of_injective into (fun _ _ h => hInj (congrArg Subtype.val h)))
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, Nat.mul_comm q t,
    Fintype.card_coe] at hCard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (hCard.trans (card_accepting_mcspSquare_le m))

/-- Uniform repair for arbitrary positions is limited to order
`m log₂ m`, even if it is only required for the zero probe. -/
theorem uniform_zero_repair_le {m t : ℕ} (hm : 256 ≤ m)
    (hRepair : ∀ (x : BitString (2^m)) (P : Finset (Fin (2^m))), P.card ≤ t →
      mcspSquare m (substitute (pinAt x P) (fun _ => false)) = true) :
    t ≤ 24*((m+1).log2+1)*m := by
  let q := m/2
  let a := m-q
  let b := (m+1).log2+1
  have hAdd : a+q = m := by dsimp [a, q]; omega
  have hA : 128 ≤ a := by dsimp [a, q]; omega
  have hHalf : m ≤ 2*a := by dsimp [a, q]; omega
  have hQ : m ≤ 3*q := by dsimp [q]; omega
  have hPos : 1 ≤ q := by dsimp [q]; omega
  have hDesc : descriptionBitBound m < 2^a := calc
    _ ≤ (4*m+12)*m^2 := description_le_polynomial m (by omega)
    _ ≤ (6*m)*m^2 := Nat.mul_le_mul_right _ (by omega)
    _ = 6*m^3 := by ring
    _ ≤ 6*(2*a)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHalf 3)
    _ = 48*a^3 := by ring
    _ < a*a^3 := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega : 0 < a))
    _ = a^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp a (by omega)
  have hBound : t < 2^a := by
    by_contra! ht
    have hRoom : (2^a)*2^q ≤ 2^m := by rw [← pow_add, hAdd]
    have h := uniform_zero_repair_capacity hRoom (fun x P h => hRepair x P (h.trans ht))
    have hLower := Nat.mul_le_mul_left (2^a) hPos
    omega
  have hRoom : t*2^q ≤ 2^m := calc
    _ ≤ (2^a)*2^q := Nat.mul_le_mul_right _ hBound.le
    _ = _ := by rw [← pow_add, hAdd]
  have hCount := uniform_zero_repair_capacity hRoom hRepair
  have hPoly : descriptionBitBound m ≤ 8*b*m^2 := by
    change 4*b + (3+4*b)*m^2 ≤ _
    have hb : 1 ≤ b := by dsimp [b]; omega
    have hm2 : 4 ≤ m^2 := Nat.pow_le_pow_left (by omega : 2 ≤ m) 2
    have hFirst : 4*b ≤ b*m^2 := by simpa only [Nat.mul_comm 4 b] using Nat.mul_le_mul_left b hm2
    have hSecond := Nat.mul_le_mul_right (m^2) (by omega : 3+4*b ≤ 7*b)
    rw [show 8*b*m^2 = b*m^2+7*b*m^2 by ring]
    omega
  have hFinish : t*m ≤ (24*b*m)*m := calc
    _ ≤ t*(3*q) := Nat.mul_le_mul_left t hQ
    _ = 3*(t*q) := by ring
    _ ≤ 3*(8*b*m^2) := Nat.mul_le_mul_left 3 (hCount.trans hPoly)
    _ = _ := by ring
  exact (Nat.mul_le_mul_right_iff (by omega : 0 < m)).mp hFinish

end RepairCapacity

#print axioms point_indicator_complexity_le_32
#print axioms complexity_quad_shared_le
#print axioms pinned_gated_family_accepted_32
#print axioms original_losses_and_residual_32
#print axioms mcspSquare_32_shared_repair
#print axioms pinned_quad_accepted_scaled
#print axioms original_losses_and_residual_scaled
#print axioms mcspSquare_scaled_pinning
#print axioms uniform_zero_repair_le

end PvsNP.Frontier.QuadraticPinning
