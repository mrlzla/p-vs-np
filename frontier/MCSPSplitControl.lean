module

public import MCSPPairWiring

/-! A narrow-cut control that also preserves split-pair orientation. -/

@[expose] public section

namespace PvsNP.Frontier.SplitControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut NarrowCut PairWiring
open SampleControls (agreesOn agreesOn_eq_true agreesOn_cost)

variable {r s : ℕ}

def railBlock (keep : Finset (BitString s)) (a : BitString r) (b : Bool) :
    Finset (Fin (2 ^ (r + (s + 1)))) := keep.image (position a b)

theorem position_mem_railBlock (keep : Finset (BitString s)) (a : BitString r) (b : Bool)
    {u : BitString s} (hu : u ∈ keep) : position a b u ∈ railBlock keep a b :=
  Finset.mem_image.mpr ⟨u, hu, rfl⟩

theorem card_railBlock (keep : Finset (BitString s)) (a : BitString r) (b : Bool) :
    (railBlock keep a b).card = keep.card := by
  have hinj : Function.Injective (position a b (s := s)) := by
    intro x y heq
    change positionEquiv r s (a, b, x) = positionEquiv r s (a, b, y) at heq
    exact congrArg (fun z : BitString r × Bool × BitString s => z.2.2) ((positionEquiv r s).injective heq)
  exact Finset.card_image_of_injective _ hinj

/-- Keep the two split-bit rails separate within each prefix block. -/
noncomputable def railControl (r : ℕ) (keep : Finset (BitString s))
    (x : BitString (2 ^ (r + (s + 1)))) : Bool := open scoped Classical in
  decide (∀ a : BitString r × Bool, agreesOn (railBlock keep a.1 a.2) x = true)

theorem railControl_accepts_probe (keep : Finset (BitString s)) (f : BooleanFunction r) :
    railControl r keep (probe s f) = true := by
  classical
  rw [railControl, decide_eq_true_eq]
  rintro ⟨a, b⟩
  apply (agreesOn_eq_true _ _).mpr
  intro i hi j hj
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
  simp

@[simp] theorem splitProjection_at (a : BitString r) (b : Bool) (u : BitString s) :
    splitProjection r s (position a b u) = b := by
  simp [splitProjection, position]

theorem railControl_accepts_split (r : ℕ) (keep : Finset (BitString s)) :
    railControl r keep (splitProjection r s) = true := by
  classical
  rw [railControl, decide_eq_true_eq]
  rintro ⟨a, b⟩
  apply (agreesOn_eq_true _ _).mpr
  intro i hi j hj
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
  simp

open scoped Classical in
theorem railControl_size_bound (r : ℕ) (keep : Finset (BitString s)) :
    complexity interpretation (single (railControl r keep)) ≤
      (2 ^ r * 2) * (2 * keep.card + 5) + 1 := by
  classical
  have hSynth := Synthesis.forall_mem (Finset.univ : Finset (BitString r × Bool))
    (fun a => agreesOn (railBlock keep a.1 a.2)) (fun a => 2 * (railBlock keep a.1 a.2).card + 4)
    (fun a _ => agreesOn_cost _)
  have h := Synthesis.congr_iff hSynth (g := railControl r keep) (fun x => by simp [railControl])
  apply h.complexity_le.trans
  simp [card_railBlock]

open scoped Classical in
theorem railControl_accepting_count_le (r : ℕ) (keep : Finset (BitString s)) (hne : keep.Nonempty) :
    (acceptingTables (railControl r keep)).card ≤ 2 ^ ((2 ^ r * 2) + (2 ^ r * 2) * keepᶜ.card) := by
  classical
  let known := acceptingTables (railControl r keep)
  let code (x : known) : ((BitString r × Bool) → Bool) ×
      (((BitString r × Bool) × (↑(keepᶜ) : Type)) → Bool) :=
    (fun a => x.val (position a.1 a.2 hne.choose), fun q => x.val (position q.1.1 q.1.2 q.2.val))
  have hinj : Function.Injective code := by
    intro x y heq
    apply Subtype.ext
    funext i
    obtain ⟨⟨a, b, u⟩, rfl⟩ := (positionEquiv r s).surjective i
    change x.val (position a b u) = y.val (position a b u)
    by_cases hu : u ∈ keep
    · have hx := (agreesOn_eq_true _ _).mp
        ((of_decide_eq_true (Finset.mem_filter.mp x.property).2) (a, b))
        (position a b u) (position_mem_railBlock keep a b hu)
        (position a b hne.choose) (position_mem_railBlock keep a b hne.choose_spec)
      have hy := (agreesOn_eq_true _ _).mp
        ((of_decide_eq_true (Finset.mem_filter.mp y.property).2) (a, b))
        (position a b u) (position_mem_railBlock keep a b hu)
        (position a b hne.choose) (position_mem_railBlock keep a b hne.choose_spec)
      exact hx.trans ((congrFun (congrArg Prod.fst heq) (a, b)).trans hy.symm)
    · exact congrFun (congrArg Prod.snd heq) ((a, b), ⟨u, Finset.mem_compl.mpr hu⟩)
  have hCard := Fintype.card_le_of_injective code hinj
  rw [Finset.card_compl, BitString.card]
  simpa [known, Fintype.card_prod, Fintype.card_fun, BitString.card, pow_add, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hCard

theorem railControl_equality (keep : Finset (BitString s)) (h : BooleanFunction s)
    (hVaries : ∃ u ∈ keep, ∃ v ∈ keep, h u ≠ h v) (f g : BooleanFunction r) :
    railControl r keep (splice (mask r h) (probe s f) (probe s g)) = true ↔ f = g := by
  classical
  constructor
  · intro hAccept
    obtain ⟨u, hu, v, hv, huv⟩ := hVaries
    funext a
    have hBlocks := of_decide_eq_true hAccept
    have hPair := (agreesOn_eq_true _ _).mp (hBlocks (a, false))
      (position a false u) (position_mem_railBlock keep a false hu)
      (position a false v) (position_mem_railBlock keep a false hv)
    simp only [splice, mask_at_position, Bool.false_xor, probe_at_position] at hPair
    cases hU : h u <;> cases hV : h v
    · exact (huv (hU.trans hV.symm)).elim
    · simpa [hU, hV] using hPair.symm
    · simpa [hU, hV] using hPair
    · exact (huv (hU.trans hV.symm)).elim
  · rintro rfl
    rw [splice_self]
    exact railControl_accepts_probe keep f

open scoped Classical in
/-- A selector constant on the retained suffixes has a small exceptional-table circuit. -/
theorem mask_accepted_of_constant_on_keep (r : ℕ) (keep : Finset (BitString s))
    (h : BooleanFunction s) (b : Bool) (hConst : ∀ t ∈ keep, h t = b)
    (budget : keepᶜ.card * (2 * s + 2) + 6 ≤ (r + (s + 1)) ^ 2) :
    mcspSquare (r + (s + 1)) (mask r h) = true := by
  classical
  let m := r + (s + 1)
  let select (j : Fin s) : Fin m := Fin.natAdd r j.succ
  let exceptions := keepᶜ.filter fun t => h t ≠ b
  have hExc (t : BitString s) : t ∈ exceptions ↔ h t ≠ b := by
    change t ∈ keepᶜ.filter (fun t => h t ≠ b) ↔ _
    simp only [Finset.mem_filter, Finset.mem_compl]
    exact ⟨And.right, fun hh => ⟨fun hk => hh (hConst t hk), hh⟩⟩
  let exceptional (x : BitString m) : Bool := decide ((x ∘ select) ∈ exceptions)
  have hExceptional : Synthesis interpretation (inputs m) {exceptional}
      (exceptions.card * (2 * s + 2) + 1) := by
    have hSyn := Synthesis.exists_mem exceptions
      (fun t (x : BitString m) => decide ((fun j => x (select j)) = t))
      (fun _ => 2 * s + 1) (fun t _ => synthesis_minterm select t)
    have hw := Synthesis.congr_iff hSyn (g := exceptional) (fun x => by simp [exceptional, Function.comp_def])
    apply hw.mono Set.Subset.rfl Set.Subset.rfl
    simp [Nat.add_assoc]
  have hCard : exceptions.card ≤ keepᶜ.card := Finset.card_filter_le _ _
  have hCost := Nat.mul_le_mul_right (2 * s + 2) hCard
  have hLift : Synthesis interpretation (inputs m) {fun x => h (x ∘ select)}
      (keepᶜ.card * (2 * s + 2) + 2) := by
    cases b with
    | false =>
      have hSyn := Synthesis.congr_iff hExceptional (g := fun x => h (x ∘ select))
        (fun x => by simp [exceptional, hExc])
      exact hSyn.mono Set.Subset.rfl Set.Subset.rfl (by omega)
    | true =>
      have hSyn := Synthesis.congr_iff hExceptional.not (g := fun x => h (x ∘ select))
        (fun x => by simp [exceptional, hExc])
      exact hSyn.mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hSplit : Synthesis interpretation (inputs m)
      {fun x => x (Fin.natAdd r (0 : Fin (s + 1)))} 0 := Synthesis.of_mem ⟨_, rfl⟩
  have hMask := (hSplit.xor hLift).complexity_le
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, mask, Equiv.symm_apply_apply]
  exact hMask.trans (by omega)

def omittedIndex (i : Fin 4) : Fin (2 ^ 22) := ⟨i.val + 1, by omega⟩

def omitted : Finset (BitString 22) :=
  (Finset.univ : Finset (Fin 4)).image ((BitString.equivFin 22).symm ∘ omittedIndex)

noncomputable def keep : Finset (BitString 22) := open scoped Classical in omittedᶜ

private theorem card_omitted : omitted.card = 4 := by
  rw [omitted, Finset.card_image_of_injective]
  · simp
  · intro i j heq
    have hij := congrArg Fin.val ((BitString.equivFin 22).symm.injective heq)
    apply Fin.ext
    exact Nat.add_right_cancel hij

theorem card_keep : keep.card = 2 ^ 22 - 4 := by
  classical
  rw [keep, Finset.card_compl, BitString.card, card_omitted]

open scoped Classical in
private theorem card_keep_compl : keepᶜ.card = 4 := by
  classical
  simp [keep, card_omitted]

private theorem retained (i : Fin (2 ^ 22)) (hi : i.val = 0 ∨ 5 ≤ i.val) :
    (BitString.equivFin 22).symm i ∈ keep := by
  classical
  simp only [keep, Finset.mem_compl, omitted, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨j, hj⟩
  have hp := congrArg Fin.val ((BitString.equivFin 22).symm.injective hj)
  change j.val + 1 = i.val at hp
  omega

private theorem keep_nonempty : keep.Nonempty := ⟨_, retained 0 (Or.inl rfl)⟩

theorem has_other_retained (u : BitString 22) : ∃ v ∈ keep, u ≠ v := by
  let e := (BitString.equivFin 22).symm
  by_cases h : u = e 0
  · exact ⟨e 5, retained 5 (Or.inr (by decide)), h ▸ e.injective.ne (by decide)⟩
  · exact ⟨e 0, retained 0 (Or.inl rfl), h⟩

theorem good_selector_varies {h : BooleanFunction 22} (hGood : h ∉ badSelectors 9 22) :
    ∃ u ∈ keep, ∃ v ∈ keep, h u ≠ h v := by
  classical
  by_contra! hSame
  obtain ⟨u, hu⟩ := keep_nonempty
  have hTrue := mask_accepted_of_constant_on_keep 9 keep h (h u)
    (fun t ht => hSame t ht u hu) (by rw [card_keep_compl]; decide)
  have hne : (fun _ : BitString 9 => true) ≠ (fun _ => false) := by
    intro heq
    cases congrFun heq (fun _ => false)
  have hFalse := separates_of_notMem_badSelectors hGood _ _ hne
  have hMix : splice (mask 9 h) (probe 22 (fun _ : BitString 9 => true))
      (probe 22 (fun _ : BitString 9 => false)) = mask 9 h := by
    funext i
    cases hBit : mask 9 h i <;> simp [splice, probe, MCSP.truthTable, hBit]
  rw [hMix, hTrue] at hFalse
  cases hFalse

theorem every_railControl_circuit_is_wide (h : BooleanFunction 22) (hGood : h ∉ badSelectors 9 22)
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (railControl 9 keep)))
    (owner : Wire (2 ^ 32) c.size → Bool) (hOwner : ∀ i, owner (.input i) = mask 9 h i) :
    512 ≤ (crossingWires c.program owner).card :=
  crossingWires_lower_bound_of_equality h (railControl 9 keep)
    (railControl_equality keep h (good_selector_varies hGood)) c hc owner hOwner

theorem railControl32_sparse :
    (acceptingTables (railControl 9 keep)).card ≤ 2 ^ descriptionBitBound 32 := by
  classical
  have h := railControl_accepting_count_le 9 keep keep_nonempty
  rw [card_keep_compl] at h
  exact h.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide))

open scoped Classical in
theorem swap_split_at (key : BitString r × BitString s) (a : BitString r) (b : Bool) (u : BitString s) :
    swapPair key (splitProjection r s) (position a b u) = if (a, u) = key then !b else b := by
  have h : (positionEquiv r s).symm (position a b u) = (a, b, u) :=
    (positionEquiv r s).symm_apply_apply (a, b, u)
  simp [swapPair, h]

theorem railControl_rejects_retained_swap (keep : Finset (BitString s)) (a : BitString r)
    {u v : BitString s} (hu : u ∈ keep) (hv : v ∈ keep) (huv : u ≠ v) :
    railControl r keep (swapPair (a, u) (splitProjection r s)) = false := by
  classical
  cases h : railControl r keep (swapPair (a, u) (splitProjection r s)) with
  | false => rfl
  | true =>
    have hBlocks := of_decide_eq_true h
    have hPair := (agreesOn_eq_true _ _).mp (hBlocks (a, false))
      (position a false u) (position_mem_railBlock keep a false hu)
      (position a false v) (position_mem_railBlock keep a false hv)
    simp [swap_split_at, Ne.symm huv] at hPair

open scoped Classical in
theorem railControl_symmetric_wiring_bound (keep : Finset (BitString s))
    (hOther : ∀ u ∈ keep, ∃ v ∈ keep, u ≠ v) (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (railControl r keep))) :
    ((Finset.univ : Finset (BitString r × BitString s)).filter (PairWiredSymmetrically c)).card ≤
      2 ^ r * keepᶜ.card := by
  classical
  let zero : BitString (2 ^ (r + (s + 1))) := fun _ => false
  have hZero : railControl r keep zero = true := by
    simp [railControl, agreesOn_eq_true, zero]
  have ho := output_is_gate_of_accepts_zero c ((congrFun (hc zero) 0).trans hZero)
  have hSub : ((Finset.univ : Finset (BitString r × BitString s)).filter
      (PairWiredSymmetrically c)) ⊆ ((Finset.univ : Finset (BitString r)) ×ˢ keepᶜ) := by
    rintro ⟨a, u⟩ hu
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_compl.mpr
    intro hKeep
    obtain ⟨v, hv, huv⟩ := hOther u hKeep
    have hReject := railControl_rejects_retained_swap keep a hKeep hv huv
    have hInvariant := eval_swap_of_symmetric_pair c ho (Finset.mem_filter.mp hu).2 (splitProjection r s)
    have hTrue : railControl r keep (swapPair (a, u) (splitProjection r s)) = true :=
      (congrFun (hc _) 0).symm.trans (hInvariant.trans
        ((congrFun (hc _) 0).trans (railControl_accepts_split r keep)))
    rw [hReject] at hTrue
    cases hTrue
  exact (Finset.card_le_card hSub).trans (by simp)

open scoped Classical in
theorem railControl32_symmetric_wiring_bound (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (railControl 9 keep))) :
    ((Finset.univ : Finset (BitString 9 × BitString 22)).filter (PairWiredSymmetrically c)).card ≤ 2048 := by
  have h := railControl_symmetric_wiring_bound keep (fun u _ => has_other_retained u) c hc
  rw [card_keep_compl] at h
  exact h

def suffixProjection (r : ℕ) (j : Fin s) : BitString (2 ^ (r + (s + 1))) :=
  MCSP.truthTable _ (fun x => x (Fin.natAdd r j.succ))

@[simp] theorem suffixProjection_at (j : Fin s) (a : BitString r) (b : Bool) (u : BitString s) :
    suffixProjection r j (position a b u) = u j := by
  simp [suffixProjection, position]

theorem railControl_rejects_suffix (r : ℕ) (keep : Finset (BitString s)) (j : Fin s)
    {u v : BitString s} (hu : u ∈ keep) (hv : v ∈ keep) (hne : u j ≠ v j) :
    railControl r keep (suffixProjection r j) = false := by
  classical
  cases h : railControl r keep (suffixProjection r j) with
  | false => rfl
  | true =>
    rw [railControl, decide_eq_true_eq] at h
    let a : BitString r := fun _ => false
    have hPair := (agreesOn_eq_true _ _).mp (h (a, false))
      (position a false u) (position_mem_railBlock keep a false hu)
      (position a false v) (position_mem_railBlock keep a false hv)
    exact (hne (by simpa using hPair)).elim

theorem suffix_projection_distinguishes : ∃ j : Fin 22,
    railControl 9 keep (suffixProjection 9 j) = false ∧ mcspSquare 32 (suffixProjection 9 j) = true := by
  classical
  obtain ⟨u, hu⟩ := keep_nonempty
  obtain ⟨v, hv, huv⟩ := has_other_retained u
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ v j := by
    by_contra! heq
    exact huv (funext heq)
  refine ⟨j, ?_, ?_⟩
  · exact railControl_rejects_suffix 9 keep j hu hv hj
  · rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, suffixProjection, Equiv.symm_apply_apply,
      complexity_single_proj]
    exact Nat.zero_le _

open scoped Classical in
theorem minimum_wide_railControl_32 :
    ∃ c : Circuit signature (2 ^ 32) 1,
      c.Computes interpretation (single (railControl 9 keep)) ∧
      c.size = complexity interpretation (single (railControl 9 keep)) ∧
      c.size + 3071 ≤ 2 * 2 ^ 32 ∧
      ((Finset.univ : Finset (BitString 9 × BitString 22)).filter (PairWiredSymmetrically c)).card ≤ 2048 ∧
      ∀ (h : BooleanFunction 22) (_ : h ∉ badSelectors 9 22) (owner : Wire (2 ^ 32) c.size → Bool),
        (∀ i, owner (.input i) = mask 9 h i) → 512 ≤ (crossingWires c.program owner).card := by
  obtain ⟨c, hc, hMin⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (railControl 9 keep))
  refine ⟨c, hc, hMin, ?_, railControl32_symmetric_wiring_bound c hc, fun h hh owner hOwner =>
    every_railControl_circuit_is_wide h hh c hc owner hOwner⟩
  have hSize := railControl_size_bound 9 keep
  rw [card_keep] at hSize
  omega

end PvsNP.Frontier.SplitControl
