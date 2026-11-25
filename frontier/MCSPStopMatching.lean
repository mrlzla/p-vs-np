module

public import MCSPPairSeparation

/-! Match partners of one free entry to original stop gates and their bypass readers. -/

@[expose] public section

namespace PvsNP.Frontier.StopMatching

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open ForestPinning SuperTwoN MonotoneForest TwoCornerStructure CornerCertificates
open RestrictionCharges FreshCharges PairSeparation

variable {n g : ℕ}

/-- A direct reader uses the original raw input as an argument. -/
def Reads (p : Program signature n g) (k : Fin g) (i : Fin n) : Prop :=
  ∃ a, (p.lines k).wires a = .input i

private noncomputable def rawInputs (p : Program signature n g) (k : Fin g) :
    Finset (Fin n) := open scoped Classical in Finset.univ.filter (Reads p k)

private theorem rawInputs_card_le (p : Program signature n g) (k : Fin g) :
    (rawInputs p k).card ≤ 2 := by
  classical
  let into (i : rawInputs p k) : Fin (signature.Arity (p.lines k).op) :=
    ((Finset.mem_filter.mp i.property).2).choose
  have hInj : Function.Injective into := by
    intro i j h
    have hi := ((Finset.mem_filter.mp i.property).2).choose_spec
    have hj := ((Finset.mem_filter.mp j.property).2).choose_spec
    change ((p.lines k).wires (into i)) = .input i.val at hi
    change ((p.lines k).wires (into j)) = .input j.val at hj
    rw [h, hj] at hi
    injection hi with he
    exact Subtype.ext he.symm
  have hCard := Fintype.card_le_of_injective into hInj
  have hFan := Program.fanInAtMost_iff.mp p.fanInAtMost_two k
  simp only [Fintype.card_coe, Fintype.card_fin] at hCard
  exact hCard.trans hFan

private theorem pair_reads_unique {p : Program signature n g} {k : Fin g}
    {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l)
    (hi : Reads p k i) (hj : Reads p k j) (hl : Reads p k l) : j = l := by
  classical
  by_contra hne
  have hSub : ({i, j, l} : Finset (Fin n)) ⊆ rawInputs p k := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
  have hCard := (Finset.card_le_card hSub).trans (rawInputs_card_le p k)
  simp [hij, hil, hne] at hCard

private theorem rawInputs_union_card_le (p : Program signature n g) (R : Finset (Fin g)) :
    (R.biUnion (rawInputs p)).card ≤ 2 * R.card := by
  classical
  calc
    _ ≤ ∑ k ∈ R, (rawInputs p k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ R, 2 := Finset.sum_le_sum fun k _ => rawInputs_card_le p k
    _ = _ := by simp [Nat.mul_comm]

/-- Keep one representative per distinct witness, with the witness map
injective on the chosen representatives. -/
private theorem representatives {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : T → β) :
    ∃ M ⊆ T, M.card = (T.attach.image f).card ∧
      ∃ rep : M → T, (∀ j, (rep j).val = j.val) ∧ Function.Injective (f ∘ rep) := by
  classical
  let R := T.attach.image f
  have hPre (b : R) : ∃ j : T, f j = b.val := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp b.property
    exact ⟨j, hj⟩
  let pick (b : R) := (hPre b).choose
  have hp (b : R) : f (pick b) = b.val := (hPre b).choose_spec
  let raw (b : R) := (pick b).val
  have hRaw : Function.Injective raw := by
    intro u v h
    apply Subtype.ext
    rw [← hp u, ← hp v, show pick u = pick v from Subtype.ext h]
  let M := R.attach.image raw
  have hSub : M ⊆ T := by
    intro i hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hi
    exact (pick b).property
  have hCard : M.card = R.card := by
    simp [M, Finset.card_image_of_injective _ hRaw]
  let rep (j : M) : T := ⟨j.val, hSub j.property⟩
  refine ⟨M, hSub, hCard, rep, fun _ => rfl, ?_⟩
  intro i j hij
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp i.property
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp j.property
  have hu' : pick u = rep i := Subtype.ext hu
  have hv' : pick v = rep j := Subtype.ext hv
  have huv : u = v := Subtype.ext (by simpa only [Function.comp_apply, hp, ← hu', ← hv'] using hij)
  exact Subtype.ext (hu.symm.trans (huv ▸ hv))

/-- The fresh stop gates lost when the selected second entries are pinned. -/
noncomputable def losses (p : Program signature n g) (root : Wire n g)
    (x : BitString n) (P J : Finset (Fin n)) : Finset (Fin g) :=
  StopGate p root ∩ nextFreshLoss p (pinAt x P) (pinAt x J)

/-- A charge to the selected targets persists when more coordinates are
pinned to the same reference table. -/
theorem losses_mono_targets (p : Program signature n g) (root : Wire n g)
    (x : BitString n) (P : Finset (Fin n)) {J Q : Finset (Fin n)} (h : J ⊆ Q) :
    losses p root x P J ⊆ losses p root x P Q := by
  have hCompose : compose (pinAt x J) (pinAt x Q) = pinAt x Q := by
    funext i
    by_cases hi : i ∈ J
    · simp [compose, pinAt, hi, h hi]
    · simp [compose, pinAt, hi]
  have hFresh := fresh_nested p (compose (pinAt x P) (pinAt x J)) (pinAt x Q)
  rw [AdaptivePinning.compose_assoc, hCompose] at hFresh
  intro k hk
  obtain ⟨hStop, hNew⟩ := Finset.mem_inter.mp hk
  obtain ⟨hBefore, hAfter⟩ := Finset.mem_sdiff.mp hNew
  exact Finset.mem_inter.mpr ⟨hStop, Finset.mem_sdiff.mpr
    ⟨hBefore, fun hQ => hAfter (hFresh hQ)⟩⟩

/-- Only a nonconstant already-redundant stop gate that reads a target can
absorb a second-reader charge. -/
noncomputable def earlyReaders (p : Program signature n g) (root : Wire n g)
    (x : BitString n) (P J : Finset (Fin n)) : Finset (Fin g) := open scoped Classical in
  ((StopGate p root ∩ surviving p (pinAt x P)) \ fresh p (pinAt x P)).filter
    (fun k => ∃ j ∈ J, Reads p k j)

/-- Match targets to separate fresh joint readers. Anchors can repeat,
and they are kept outside the target set. After removing the exceptional
targets, at least half of the others also match to distinct bypass readers
disjoint from the joint readers. -/
theorem match_oriented_readers {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} (hMask : IsForestMask p root x P)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (anchor : Fin n → Fin n) (J E : Finset (Fin n))
    (hJ : ∀ j ∈ J, j ∉ P)
    (hAnchor : ∀ j ∈ J, anchor j ∉ P ∧ anchor j ∉ J)
    (hSep : ∀ j ∈ J \ E, ∀ v : Bool,
      EssentialAt (restrictedWire p (branchPin x P (anchor j) v) root) j)
    (hJoint : ∀ j ∈ J, ∃ k ∈ StopGate p root, k ∈ fresh p (pinAt x P) ∧
      ((p.lines k).op = .and ∨ (p.lines k).op = .or) ∧ Reads p k (anchor j) ∧ Reads p k j) :
    ∃ (M : Finset (Fin n)) (joint : J → Fin g) (bypass : M → Fin g),
      M ⊆ J \ E ∧ (J \ E).card ≤ 2 * M.card ∧
      Function.Injective joint ∧ Function.Injective bypass ∧
      (∀ j t, joint j ≠ bypass t) ∧
      (∀ j, joint j ∈ losses p root x P J ∧ Reads p (joint j) (anchor j.val) ∧ Reads p (joint j) j.val) ∧
      (∀ t, Reads p (bypass t) t.val ∧
        (bypass t ∈ losses p root x P J ∨ bypass t ∈ earlyReaders p root x P J)) ∧
      J.card ≤ (losses p root x P J).card ∧
      J.card + M.card ≤ (losses p root x P J).card + (earlyReaders p root x P J).card ∧
      J.card + M.card ≤ (StopGate p root).card := by
  classical
  let C := J \ E
  have hJi {j l : Fin n} (hj : j ∈ J) (hl : l ∈ J) : anchor j ≠ l :=
    fun h => (hAnchor j hj).2 (h.symm ▸ hl)
  let joint (j : J) := (hJoint j.val j.property).choose
  have hJointSpec (j : J) := (hJoint j.val j.property).choose_spec
  have hJointInj : Function.Injective joint := by
    intro j l h
    apply Subtype.ext
    have hl : Reads p (joint j) l.val := h.symm ▸ (hJointSpec l).2.2.2.2
    exact pair_reads_unique (hJi j.property j.property) (hJi j.property l.property)
      (hJointSpec j).2.2.2.1 (hJointSpec j).2.2.2.2 hl
  have hBypass (j : C) : ∃ k ∈ StopGate p root,
      k ≠ joint ⟨j.val, (Finset.mem_sdiff.mp j.property).1⟩ ∧
      Reads p k j.val ∧ EssentialAt (restrictedWire p (pinAt x P) (.gate k)) j.val := by
    let jp : J := ⟨j.val, (Finset.mem_sdiff.mp j.property).1⟩
    let k := joint jp
    let i := anchor jp.val
    have hi : i ∉ P := (hAnchor jp.val jp.property).1
    have hOp : ∃ v : Bool, ((p.lines k).op = .and ∧ v = false) ∨
        ((p.lines k).op = .or ∧ v = true) := by
      rcases (hJointSpec jp).2.2.1 with ha | ho
      · exact ⟨false, Or.inl ⟨ha, rfl⟩⟩
      · exact ⟨true, Or.inr ⟨ho, rfl⟩⟩
    obtain ⟨v, hv⟩ := hOp
    have hConst := branch_absorbs_gate p x P i v k hv (hJointSpec jp).2.2.2.1
    have hSkip : ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.gate k)) j.val := by
      rw [hConst]
      rintro ⟨_, _, _, hn⟩
      exact hn rfl
    obtain ⟨t, ht, hne, hReads, he, _⟩ :=
      separated_branch_bypass hMask h0 h1 hi (hJ jp.val jp.property) v k
        (hSep j.val j.property v) hSkip
    exact ⟨t, ht, hne, hReads, he⟩
  let backup (j : C) := (hBypass j).choose
  have hBackup (j : C) := (hBypass j).choose_spec
  let R := C.attach.image backup
  have hCover : C ⊆ R.biUnion (rawInputs p) := by
    intro j hj
    let q : C := ⟨j, hj⟩
    exact Finset.mem_biUnion.mpr ⟨backup q,
      Finset.mem_image.mpr ⟨q, Finset.mem_attach C q, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hBackup q).2.2.1⟩⟩
  have hCapacity := (Finset.card_le_card hCover).trans (rawInputs_union_card_le p R)
  obtain ⟨M, hM, hMCard, rep, hRep, hInj⟩ := representatives C backup
  let bypass := backup ∘ rep
  have hJointDisj (j : J) (t : M) : joint j ≠ bypass t := by
    intro h
    have hjt : Reads p (joint j) (rep t).val := h.symm ▸ (hBackup (rep t)).2.2.1
    have he := pair_reads_unique (hJi j.property j.property)
      (hJi j.property (Finset.mem_sdiff.mp (rep t).property).1)
      (hJointSpec j).2.2.2.1 (hJointSpec j).2.2.2.2 hjt
    have he' : j = (⟨(rep t).val, (Finset.mem_sdiff.mp (rep t).property).1⟩ : J) :=
      Subtype.ext he
    have hb : backup (rep t) = joint j := h.symm
    exact (hBackup (rep t)).2.1 (hb.trans (congrArg joint he'))
  have hPrimary (j : J) : joint j ∈ losses p root x P J ∧
      Reads p (joint j) (anchor j.val) ∧ Reads p (joint j) j.val := by
    obtain ⟨hk, hf, _, hI, hRead⟩ := hJointSpec j
    exact ⟨Finset.mem_inter.mpr ⟨hk, fresh_reader_loss_of_mem p x P J (hJ j.val j.property)
      j.property hf hRead⟩, hI, hRead⟩
  have hSecondary (t : M) : Reads p (bypass t) t.val ∧
      (bypass t ∈ losses p root x P J ∨ bypass t ∈ earlyReaders p root x P J) := by
    have hJt : (rep t).val ∈ J := (Finset.mem_sdiff.mp (rep t).property).1
    obtain ⟨hk, _, hRead, he⟩ := hBackup (rep t)
    refine ⟨hRep t ▸ hRead, ?_⟩
    by_cases hf : bypass t ∈ fresh p (pinAt x P)
    · exact Or.inl (Finset.mem_inter.mpr ⟨hk,
        fresh_reader_loss_of_mem p x P J (hJ (rep t).val hJt) hJt hf hRead⟩)
    · obtain ⟨u, v, _, hne⟩ := he
      exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, v, hne⟩⟩, hf⟩,
        (rep t).val, hJt, hRead⟩)
  let A := J.attach.image joint
  let D := M.attach.image bypass
  have hA : A.card = J.card := by simp [A, Finset.card_image_of_injective _ hJointInj]
  have hByInj : Function.Injective bypass := hInj
  have hD : D.card = M.card := by simp [D, Finset.card_image_of_injective _ hByInj]
  have hALoss : A ⊆ losses p root x P J := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact (hPrimary j).1
  have hU : A ∪ D ⊆ losses p root x P J ∪ earlyReaders p root x P J := by
    intro k hk
    rcases Finset.mem_union.mp hk with ha | hd
    · exact Finset.mem_union_left _ (hALoss ha)
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_union.mpr (hSecondary t).2
  have hDisj : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro k ha hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hd
    exact hJointDisj j t ht.symm
  have hUS : losses p root x P J ∪ earlyReaders p root x P J ⊆ StopGate p root := by
    intro k hk
    rcases Finset.mem_union.mp hk with hd | he
    · exact (Finset.mem_inter.mp hd).1
    · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1).1
  have hBoth := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  have hStop := Finset.card_le_card (hU.trans hUS)
  rw [Finset.card_union_of_disjoint hDisj, hA, hD] at hBoth hStop
  exact ⟨M, joint, bypass, hM, hMCard ▸ hCapacity, hJointInj, hByInj, hJointDisj,
    hPrimary, hSecondary, hA ▸ Finset.card_le_card hALoss, hBoth, hStop⟩

/-- With anchors in T, there are at most 2B exceptions per anchor.
The extra losses beyond the joint readers depend on the early alias count. -/
theorem mcsp_affine_oriented_charge (m : ℕ) (hm : 7 ≤ m)
    (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (a : BitString m) (b : Bool) (P J T : Finset (Fin (2 ^ m)))
    (hMask : IsForestMask c.program (c.outputs 0) (MCSP.truthTable m (affine a b)) P)
    (anchor : Fin (2 ^ m) → Fin (2 ^ m))
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m)
    (hJ : Disjoint J P) (hT : Disjoint T P) (hTJ : Disjoint T J)
    (hAnchor : ∀ j ∈ J, anchor j ∈ T)
    (hJoint : ∀ j ∈ J, ∃ k ∈ StopGate c.program (c.outputs 0),
      k ∈ fresh c.program (pinAt (MCSP.truthTable m (affine a b)) P) ∧
      ((c.program.lines k).op = .and ∨ (c.program.lines k).op = .or) ∧
      Reads c.program k (anchor j) ∧ Reads c.program k j) :
    let x := MCSP.truthTable m (affine a b)
    let D := (losses c.program (c.outputs 0) x P J).card
    let A := (earlyReaders c.program (c.outputs 0) x P J).card
    J.card + ((J.card - 2 * descriptionBitBound m * T.card + 1) / 2 - A) ≤ D ∧
      3 * J.card ≤ 2 * (StopGate c.program (c.outputs 0)).card +
        2 * descriptionBitBound m * T.card := by
  classical
  dsimp only
  have hEx (i : T) :=
    affine_two_bit_separation_except m hm a b P i.val
      (fun h => Finset.disjoint_left.mp hT i.property h) hFree
  let exception (i : Fin (2 ^ m)) : Finset (Fin (2 ^ m)) :=
    if hi : i ∈ T then (hEx ⟨i, hi⟩).choose else ∅
  let E := J.filter fun j => j ∈ exception (anchor j)
  have hEc : E.card ≤ 2 * descriptionBitBound m * T.card := by
    have hSub : E ⊆ T.biUnion exception := by
      intro j hj
      obtain ⟨hjJ, hjE⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_biUnion.mpr ⟨anchor j, hAnchor j hjJ, hjE⟩
    calc
      _ ≤ (T.biUnion exception).card := Finset.card_le_card hSub
      _ ≤ ∑ i ∈ T, (exception i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ T, 2 * descriptionBitBound m := Finset.sum_le_sum fun i hi => by
        simpa only [exception, hi, dite_true] using (hEx ⟨i, hi⟩).choose_spec.2.1
      _ = _ := by simp [Nat.mul_comm _ T.card]
  have hAnchor' (j : Fin (2 ^ m)) (hj : j ∈ J) : anchor j ∉ P ∧ anchor j ∉ J :=
    ⟨fun h => Finset.disjoint_left.mp hT (hAnchor j hj) h,
      fun h => Finset.disjoint_left.mp hTJ (hAnchor j hj) h⟩
  have hSep (j : Fin (2 ^ m)) (hj : j ∈ J \ E) (v : Bool) :
      EssentialAt (restrictedWire c.program
        (branchPin (MCSP.truthTable m (affine a b)) P (anchor j) v) (c.outputs 0)) j := by
    obtain ⟨hjJ, hjE⟩ := Finset.mem_sdiff.mp hj
    have hi := hAnchor j hjJ
    have hEdge := (hEx ⟨anchor j, hi⟩).choose_spec.2.2
    have hFreeJ : j ∉ insert (anchor j) P := by
      intro h
      rcases Finset.mem_insert.mp h with he | hp
      · exact (hAnchor' j hjJ).2 (he ▸ hjJ)
      · exact Finset.disjoint_left.mp hJ hjJ hp
    have hNot : j ∉ (hEx ⟨anchor j, hi⟩).choose := by
      intro he
      apply hjE
      refine Finset.mem_filter.mpr ⟨hjJ, ?_⟩
      simpa only [exception, hi, dite_true] using he
    rw [NestedFaces.restricted_circuit_eq c hc]
    exact hEdge j (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hFreeJ⟩,
      hNot⟩) v
  have h0 : cornerValue c.program false (c.outputs 0) = true :=
    (congrFun (hc _) 0).trans (mcspSquare_constant_table m (by omega) false)
  have h1 : cornerValue c.program true (c.outputs 0) = true :=
    (congrFun (hc _) 0).trans (mcspSquare_constant_table m (by omega) true)
  obtain ⟨M, _, _, _, hCapacity, _, _, _, _, _, hPrimary, hTotal, hStop⟩ :=
    match_oriented_readers hMask h0 h1 anchor J E
      (fun _ hj hp => Finset.disjoint_left.mp hJ hj hp) hAnchor' hSep hJoint
  have hBound : J.card ≤ (J \ E).card + E.card := by
    have hSub : J ⊆ (J \ E) ∪ E := by
      intro j hj
      by_cases he : j ∈ E
      · exact Finset.mem_union_right _ he
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hj, he⟩)
    exact (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)
  omega

/-- A degree-one reader graph can put every candidate pair inside the
exception sets even when each set has size one. -/
theorem exceptions_can_cover_all_candidates (k : ℕ) :
    ∃ E : (Fin k × Bool) → Finset (Fin k × Bool),
      (∀ i, (E i).card = 1 ∧ i ∉ E i) ∧
      (∀ r : Fin k, (r, true) ∈ E (r, false) ∧ (r, false) ∈ E (r, true)) := by
  refine ⟨fun i => {(i.1, !i.2)}, ?_, ?_⟩
  · rintro ⟨r, b⟩
    cases b <;> simp
  · intro r
    simp

/-- The matching counts and the earlier forest budgets are compatible
with every matched bypass being an early alias. Here the selected targets
are the full set of later pins, and their number is linear in the table size. -/
theorem alias_counts_allow_only_joint_losses (m B : ℕ) :
    ∃ (L H R P J M A D : ℕ),
      L = 561 * 2 ^ m ∧ J = 1500 * 2 ^ m ∧ D = J ∧
      H ≤ 56 * L ∧ J + R ≤ 10 * B + 1326 * L + 2 * H ∧
      12 * P ≤ 13 * R + 2 * 2 ^ (m + 20) ∧
      2 ^ (m + 20) ≤ P + J + B ∧ J ≤ 2 * (A + D) ∧
      J = 2 * M ∧ J + M ≤ D + A ∧ D + A ≤ H ∧ M = A := by
  have hN : (2 : ℕ) ^ (m + 20) = 1048576 * 2 ^ m := by
    rw [pow_add, mul_comm]
    rfl
  refine ⟨561 * 2 ^ m, 31416 * 2 ^ m, 805218 * 2 ^ m, 1047076 * 2 ^ m,
    1500 * 2 ^ m, 750 * 2 ^ m, 750 * 2 ^ m, 1500 * 2 ^ m, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> omega

#print axioms losses_mono_targets
#print axioms match_oriented_readers
#print axioms mcsp_affine_oriented_charge
#print axioms exceptions_can_cover_all_candidates
#print axioms alias_counts_allow_only_joint_losses

end PvsNP.Frontier.StopMatching
