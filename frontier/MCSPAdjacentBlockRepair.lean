module

public import MCSPJointSparseCompletion

/-! Repair a 1024-entry block by sharing its long prefix test and
multiplexing four 256-entry suffix lookups. -/

@[expose] public section

namespace PvsNP.Frontier.AdjacentBlockRepair

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure ForestBlockPinning ForestPinning
open RestrictionCharges FreshCharges MultiBlockPinning QuadraticForest JointSparseCompletion
open scoped Classical

private theorem mux_synthesis {n c d : ℕ} {S : Set (BooleanFunction n)}
    (b f₀ f₁ : BooleanFunction n) (hb : b ∈ S)
    (h₀ : Synthesis interpretation S {f₀} c) (h₁ : Synthesis interpretation S {f₁} d) :
    Synthesis interpretation S {fun z => if b z then f₁ z else f₀ z} (c+d+4) := by
  have hB : Synthesis interpretation S {b} 0 := Synthesis.of_mem hb
  have hs := (hB.not.and h₀).or (hB.and h₁)
  refine (Synthesis.congr_iff hs (fun z => ?_)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  cases b z <;> simp

private theorem choose_four (t : BitString 2) (F : BitString 2 → Bool) :
    (if t 0 then (if t 1 then F ![true,true] else F ![true,false])
      else (if t 1 then F ![false,true] else F ![false,false])) = F t := by
  have he : t = ![t 0,t 1] := by
    funext i
    fin_cases i <;> rfl
  conv_rhs => rw [he]
  cases t 0 <;> cases t 1 <;> rfl

private theorem split_tail (z : BitString 32) :
    Fin.append (addressHead (a := 2) 8 (addressTail (d := 10) 22 z))
      (addressTail (d := 8) 24 z) = addressTail (d := 10) 22 z := by
  have he : addressTail (d := 8) 2 (addressTail (d := 10) 22 z) = addressTail (d := 8) 24 z := by
    funext i
    apply congrArg z
    apply Fin.ext
    change 22+(2+i.val) = 24+i.val
    omega
  rw [← he,append_prefix_suffix]

private theorem in_block_iff {a d : ℕ} (p : BitString a) (z : BitString (a+d)) :
    BitString.equivFin (a+d) z ∈ block (d := d) p ↔ addressHead d z = p := by
  have he : tag (a := a) (d := d) (BitString.equivFin (a+d) z) = addressHead d z := by
    unfold tag
    rw [Equiv.symm_apply_apply]
  constructor
  · intro h
    have ht := (Finset.mem_filter.mp h).2
    rwa [he] at ht
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm ▸ h⟩

private theorem patch_eval {n : ℕ} (P : Finset (Fin (2^n))) (x : BitString (2^n))
    (f check fix : BooleanFunction n)
    (hCheck : ∀ z, check z = true ↔ BitString.equivFin n z ∈ P)
    (hFix : ∀ z, BitString.equivFin n z ∈ P → fix z = (f z ^^ x (BitString.equivFin n z))) :
    (MCSP.truthTable n).symm (substitute (pinAt x P) (MCSP.truthTable n f)) =
      fun z => f z ^^ (check z && fix z) := by
  funext z
  change substitute (pinAt x P) (MCSP.truthTable n f) (BitString.equivFin n z) =
    (f z ^^ (check z && fix z))
  by_cases hz : BitString.equivFin n z ∈ P
  · have hc := (hCheck z).mpr hz
    simp only [substitute,pinAt,hz,ite_true,Sum.elim_inr,hc,Bool.true_and,hFix z hz]
    cases f z <;> cases x (BitString.equivFin n z) <;> rfl
  · have hc : check z = false := Bool.eq_false_of_not_eq_true (fun h => hz ((hCheck z).mp h))
    simp only [substitute,pinAt,hz,ite_false,Sum.elim_inl,hc,Bool.false_and,Bool.xor_false,
      MCSP.truthTable_apply,Equiv.symm_apply_apply]

set_option maxRecDepth 3000 in
set_option maxHeartbeats 800000 in
/-- The long-prefix test is shared by all four lookups and a two-bit
multiplexer selects the appropriate repair. -/
theorem accepted_after_1024_pin (p : BitString 22) (x : BitString (2^32))
    (f : BooleanFunction 32) (hf : complexity interpretation (single f) ≤ 171) :
    mcspSquare 32 (substitute (pinAt x (block (d := 10) p)) (MCSP.truthTable 32 f)) = true := by
  let addr (t : BitString 2) (u : BitString 8) : BitString 32 := Fin.append p (Fin.append t u)
  let fix (t : BitString 2) (u : BitString 8) := f (addr t u) ^^ x (BitString.equivFin 32 (addr t u))
  let look (t : BitString 2) (z : BitString 32) := fix t (addressTail 24 z)
  let mid (z : BitString 32) : BitString 2 :=
    addressHead (a := 2) 8 (addressTail (d := 10) 22 z)
  let sel (i : Fin 2) (z : BitString 32) := mid z i
  let low (z : BitString 32) := if sel 1 z then look ![false,true] z else look ![false,false] z
  let high (z : BitString 32) := if sel 1 z then look ![true,true] z else look ![true,false] z
  let row (z : BitString 32) := if sel 0 z then high z else low z
  let guard : BooleanFunction 32 := prefixMatch (d := 10) p
  let correction (z : BitString 32) := guard z && row z
  let S := inputs 32 ∪ Set.range look
  have hLook : Synthesis interpretation (inputs 32) (Set.range look) 780 := by
    have h := synth_suffix_lookups (a := 24) (k := 2) (l := 6) fix
    rw [BitString.card,show lookupBankCost 2 6+2^2*(2*2^6)=780 by decide] at h
    exact h
  have hRead (t : BitString 2) : Synthesis interpretation S {look t} 0 :=
    Synthesis.of_mem (Or.inr ⟨t,rfl⟩)
  have hSel (i : Fin 2) : sel i ∈ S :=
    Or.inl ⟨Fin.natAdd 22 (Fin.castAdd 8 i),rfl⟩
  have hLow : Synthesis interpretation S {low} 4 :=
    mux_synthesis _ _ _ (hSel 1) (hRead _) (hRead _)
  have hHigh : Synthesis interpretation S {high} 4 :=
    mux_synthesis _ _ _ (hSel 1) (hRead _) (hRead _)
  have hRow : Synthesis interpretation S {row} 12 :=
    mux_synthesis _ _ _ (hSel 0) hLow hHigh
  have hGuard : Synthesis interpretation S {guard} 45 :=
    (synthesis_prefix_match (d := 10) p).mono Set.subset_union_left Set.Subset.rfl le_rfl
  have hFix : Synthesis interpretation (inputs 32) {correction} 838 :=
    hLook.trans (hGuard.and hRow)
  have hEval := patch_eval (block (d := 10) p) x f guard row (fun z => by
    change decide (addressHead 10 z = p) = true ↔ _
    rw [decide_eq_true_eq]
    exact (in_block_iff p z).symm) (fun z hz => by
      have hp : addressHead 10 z = p := (in_block_iff p z).mp hz
      have hRowEq : row z = look (mid z) z := choose_four (mid z) (fun t => look t z)
      have hAddr : addr (mid z) (addressTail 24 z) = z := by
        unfold addr mid
        rw [split_tail,← hp,append_prefix_suffix]
      rw [hRowEq]
      unfold look fix
      rw [hAddr])
  have hCost := complexity_xor_le f correction
  have hL := hFix.complexity_le
  rw [mcspSquare,GapMCSP.slice_yesSet_eq_true_iff,hEval]
  change complexity interpretation (single (fun z => f z ^^ correction z)) ≤ _
  exact hCost.trans (by omega)

/-- The port count and the exact factorial savings, before any block pins. -/
theorem mcsp32_unpinned_floor_ports :
    8630799706 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := quad_reindexed_forest_size_ports (BitString.equivFin 32).symm.toEmbedding
    mcsp32_tight_sparsity (mcspSquare_accepts_quad 32 (by decide))
  norm_num at h
  omega

/-- One covered block and minority choices preserve the full forest bound
with the exact factorial reserve. The shared prefix buys 512 reader losses. -/
theorem mcsp32_adjacent_block_floor_ports :
    8630800218 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c,hc,hMin⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single (mcspSquare 32))
  let p := c.program
  let root := c.outputs 0
  let S := needInputs p root false
  have h0 := mcspSquare_constant_table 32 (by decide) false
  have h1 := mcspSquare_constant_table 32 (by decide) true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hNeed : 2^32 ≤ S.card+18903 := card_needInputs_ge_of_sparse c hc mcsp32_tight_sparsity false h0
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ,Fintype.card_fin] at hMiss
  obtain ⟨q,hCover⟩ := exists_covered_block (a := 22) (d := 10) S (by
    norm_num at hMiss hNeed ⊢
    omega)
  let P := block (d := 10) q
  have hP : P.card = 1024 := card_block q
  have hQ (x : BitString (2^32)) (a : BitString 32) (b : Bool) (u w : BitString 32) :
      mcspSquare 32 (substitute (pinAt x P) (MCSP.truthTable 32 (quad a b u w))) = true :=
    accepted_after_1024_pin q x _ (QuadraticPinning.complexity_quad_shared_le a b u w)
  obtain ⟨x,hReaders,hSparse,hProbes,hBudget⟩ := pin_losses_and_residual_probes_with_count c hc hMin
    (by decide) (show 18903 < (2:ℕ)^32 by decide) mcsp32_tight_sparsity
    P P (readerGates p root) Finset.Subset.rfl
    (fun i hi => need_input_has_reader hc0 hc1 (hCover hi)) hQ
  have hForest := quad_reindexed_forest_size_ports (BitString.equivFin 32).symm.toEmbedding hSparse hProbes
  have hPart := Finset.card_le_card (Finset.inter_subset_right
    (s₁ := readerGates p root) (s₂ := fresh c.program Sum.inl \ fresh c.program (pinAt x P)))
  rw [hP] at hReaders
  rw [← hMin]
  norm_num at hForest
  omega

theorem mcsp32_adjacent_block_floor :
    8620574488 ≤ complexity interpretation (single (mcspSquare 32)) :=
  (by decide : 8620574488 ≤ 8630800218).trans mcsp32_adjacent_block_floor_ports

#print axioms accepted_after_1024_pin
#print axioms mcsp32_adjacent_block_floor
#print axioms mcsp32_unpinned_floor_ports
#print axioms mcsp32_adjacent_block_floor_ports

end PvsNP.Frontier.AdjacentBlockRepair
