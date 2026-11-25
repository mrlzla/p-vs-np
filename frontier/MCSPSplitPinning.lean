module

public import MCSPPinning
public import MCSPSplitControl

/-! Pinning an agreement test eliminates one of its two uniform assignments. -/

@[expose] public section

namespace PvsNP.Frontier.SplitControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Pinning CommunicationCut
open SampleControls (agreesOn agreesOn_eq_true agreesOn_cost)

section Blocks

variable {κ : Type} [Fintype κ] {n : ℕ}

noncomputable def blockControl (blocks : κ → Finset (Fin n)) : BooleanFunction n :=
  open scoped Classical in fun x => decide (∀ q, agreesOn (blocks q) x = true)

theorem active_in_certificate (blocks : κ → Finset (Fin n)) (active : Finset (Fin n))
    (hactive : ∀ i ∈ active, ∃ q, i ∈ blocks q ∧ ∃ j ∈ blocks q, j ≠ i)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single (blockControl blocks)))
    (sample : Finset (BitString n)) (b : Bool) (hb : (fun _ => b) ∈ sample) :
    active ⊆ certificate c sample (fun _ => b) := by
  classical
  intro i hi
  by_contra h
  obtain ⟨q, hi, j, hj, hne⟩ := hactive i hi
  let x : BitString n := Function.update (fun _ => b) i (!b)
  have hconstant : blockControl blocks (fun _ => b) = true := by
    simp [blockControl, agreesOn_eq_true]
  have hgood := accepts_of_agrees_on_certificate _ c hc sample hb hconstant (y := x) fun k hk => by
    have hki : k ≠ i := fun e => h (e ▸ hk)
    simp [x, Function.update_of_ne hki]
  have hBlocks := of_decide_eq_true hgood
  have hPair := (agreesOn_eq_true _ _).mp (hBlocks q) i hi j hj
  cases b <;> simp [x, Function.update_of_ne hne] at hPair

theorem blockControl_lower (blocks : κ → Finset (Fin n)) (active : Finset (Fin n))
    (hactive : ∀ i ∈ active, ∃ q, i ∈ blocks q ∧ ∃ j ∈ blocks q, j ≠ i) :
    2 * active.card ≤ complexity interpretation (single (blockControl blocks)) + 1 := by
  classical
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (blockControl blocks))
  let x : BitString n := fun _ => false
  let sample : Finset (BitString n) := {x, flip x}
  have h0 := Finset.card_le_card (active_in_certificate blocks active hactive c hc sample false
    (show x ∈ sample from Finset.mem_insert_self ..))
  have h1 := Finset.card_le_card (active_in_certificate blocks active hactive c hc sample true
    (show flip x ∈ sample from Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  rw [← hsize, two_mul]
  exact (Nat.add_le_add h0 h1).trans (certificate_card_add_bound c x)

private def remaining (i : Fin (n + 1)) (block : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun j => i.succAbove j ∈ block

private theorem card_remaining_le (i : Fin (n + 1)) (block : Finset (Fin (n + 1))) :
    (remaining i block).card ≤ (block.erase i).card := by
  apply Finset.card_le_card_of_injOn i.succAbove
  · intro j hj
    exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne _ _, (Finset.mem_filter.mp hj).2⟩
  · exact Fin.succAbove_right_injective.injOn

private theorem agreesOn_pin_iff (i : Fin (n + 1)) (block : Finset (Fin (n + 1)))
    (v : Bool) (x : BitString n) :
    agreesOn block (i.insertNth v x) = true ↔
      if i ∈ block then ∀ j ∈ remaining i block, x j = v
      else agreesOn (remaining i block) x = true := by
  have member (j : Fin n) : j ∈ remaining i block ↔ i.succAbove j ∈ block := by simp [remaining]
  rw [agreesOn_eq_true]
  by_cases hi : i ∈ block
  · simp only [hi, ite_true]
    constructor
    · intro h j hj
      simpa using h (i.succAbove j) ((member j).mp hj) i hi
    · intro h
      have constant (j : Fin (n + 1)) : j ∈ block → i.insertNth (α := fun _ => Bool) v x j = v := by
        refine i.succAboveCases ?_ (fun k => ?_) j
        · simp
        · intro hk
          simpa using h k ((member k).mpr hk)
      exact fun j hj k hk => (constant j hj).trans (constant k hk).symm
  · simp only [hi, ite_false, agreesOn_eq_true]
    constructor
    · intro h j hj k hk
      simpa using h (i.succAbove j) ((member j).mp hj) (i.succAbove k) ((member k).mp hk)
    · intro h j
      refine i.succAboveCases (fun hj => (hi hj).elim) (fun j' => ?_) j
      intro hj k
      refine i.succAboveCases (fun hk => (hi hk).elim) (fun k' => ?_) k
      intro hk
      simpa using h j' ((member j').mpr hj) k' ((member k').mpr hk)

private theorem allSame_cost (S : Finset (Fin n)) (v : Bool) :
    Synthesis interpretation (inputs n) {fun x => decide (∀ j ∈ S, x j = v)} (S.card + 2) := by
  classical
  have hinput (j : Fin n) : Synthesis interpretation (inputs n) {fun x => x j} 0 :=
    Synthesis.of_mem ⟨j, rfl⟩
  cases v
  · have hSome := Synthesis.exists_mem S (fun j x => x j) (fun _ => 0) (fun j _ => hinput j)
    have h := Synthesis.congr_iff hSome.not
      (g := fun x => decide (∀ j ∈ S, x j = false)) (fun x => by simp)
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by simp)
  · have hAll := Synthesis.forall_mem S (fun j x => x j) (fun _ => 0) (fun j _ => hinput j)
    have h := Synthesis.congr_iff hAll
      (g := fun x => decide (∀ j ∈ S, x j = true)) (fun x => by simp)
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by simp)

theorem blockControl_pin_upper (blocks : κ → Finset (Fin (n + 1))) (i : Fin (n + 1)) (v : Bool)
    (chosen : κ) (L : ℕ) (hcard : ∀ q, (blocks q).card ≤ L)
    (hmem : ∀ q, i ∈ blocks q ↔ q = chosen) :
    complexity interpretation (single (pin (blockControl blocks) i v)) ≤
      (Fintype.card κ - 1) * (2 * L + 5) + L + 3 := by
  classical
  let keys := (Finset.univ : Finset κ).erase chosen
  have hShared := Synthesis.forall_mem keys (fun q => agreesOn (remaining i (blocks q)))
    (fun _ => 2 * L + 4) fun q _ => by
      have h := (card_remaining_le i (blocks q)).trans (Finset.card_erase_le.trans (hcard q))
      exact (agreesOn_cost _).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  have hChosen := allSame_cost (remaining i (blocks chosen)) v
  have hSyn := Synthesis.congr_iff (hShared.and hChosen)
    (g := pin (blockControl blocks) i v) fun x => by
      simp only [pin, blockControl, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨hother, hhere⟩ q
        apply (agreesOn_pin_iff i (blocks q) v x).mpr
        by_cases h : q = chosen
        · subst q
          simpa [hmem] using hhere
        · simpa [hmem, h] using hother q (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
      · intro h
        constructor
        · intro q hq
          have hne := (Finset.mem_erase.mp hq).1
          simpa [hmem, hne] using (agreesOn_pin_iff i (blocks q) v x).mp (h q)
        · simpa [hmem] using (agreesOn_pin_iff i (blocks chosen) v x).mp (h chosen)
  have hKeys : keys.card = Fintype.card κ - 1 := by simp [keys, Finset.card_erase_of_mem]
  have hChosenCard := card_remaining_le i (blocks chosen)
  rw [Finset.card_erase_of_mem ((hmem chosen).mpr rfl)] at hChosenCard
  have hL := hcard chosen
  have hpos := Finset.card_pos.mpr ⟨i, (hmem chosen).mpr rfl⟩
  apply hSyn.complexity_le.trans
  simp only [Finset.sum_const, Nat.nsmul_eq_mul]
  rw [hKeys, show 2 * L + 4 + 1 = 2 * L + 5 by omega]
  omega

theorem blockControl_pin_unchanged_of_omitted (blocks : κ → Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (v w : Bool) (hi : ∀ q, i ∉ blocks q) :
    pin (blockControl blocks) i v = pin (blockControl blocks) i w := by
  classical
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [pin, blockControl, decide_eq_true_eq]
  have key (q : κ) (b : Bool) :
      agreesOn (blocks q) (i.insertNth b x) = true ↔ agreesOn (remaining i (blocks q)) x = true := by
    simpa [hi q] using agreesOn_pin_iff i (blocks q) b x
  simp only [key]

end Blocks

private theorem pos_mem_block_iff {r s : ℕ} (K : Finset (BitString s))
    (a a' : BitString r) (d d' : Bool) (u : BitString s) :
    position a d u ∈ railBlock K a' d' ↔ (a, d) = (a', d') ∧ u ∈ K := by
  constructor
  · intro h
    obtain ⟨v, hv, h⟩ := Finset.mem_image.mp h
    change positionEquiv r s (a', d', v) = positionEquiv r s (a, d, u) at h
    cases (positionEquiv r s).injective h
    exact ⟨rfl, hv⟩
  · rintro ⟨h, hu⟩
    cases h
    exact position_mem_railBlock K a d hu

private def active (r : ℕ) {s : ℕ} (K : Finset (BitString s)) :
    Finset (Fin (2 ^ (r + (s + 1)))) :=
  (Finset.univ ×ˢ K).map (((Equiv.prodAssoc (BitString r) Bool (BitString s)).trans
    (positionEquiv r s)).toEmbedding)

private theorem card_active (r : ℕ) {s : ℕ} (K : Finset (BitString s)) :
    (active r K).card = (2 ^ r * 2) * K.card := by
  rw [active, Finset.card_map, Finset.card_product, Finset.card_univ, Fintype.card_prod,
    BitString.card, Fintype.card_bool]

private theorem control_rails (r : ℕ) {s : ℕ} (K : Finset (BitString s)) :
    blockControl (fun q : BitString r × Bool => railBlock K q.1 q.2) = railControl r K := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [blockControl, railControl, decide_eq_true_eq]

private theorem active_has_mate (r : ℕ) {s : ℕ} (K : Finset (BitString s))
    (hOther : ∀ u ∈ K, ∃ v ∈ K, u ≠ v) :
    ∀ i ∈ active r K, ∃ q : BitString r × Bool,
      i ∈ railBlock K q.1 q.2 ∧ ∃ j ∈ railBlock K q.1 q.2, j ≠ i := by
  intro i hi
  obtain ⟨⟨⟨a, d⟩, u⟩, hmem, rfl⟩ := Finset.mem_map.mp hi
  have hu := (Finset.mem_product.mp hmem).2
  obtain ⟨v, hv, huv⟩ := hOther u hu
  refine ⟨(a, d), position_mem_railBlock K a d hu,
    position a d v, position_mem_railBlock K a d hv, ?_⟩
  intro h
  change positionEquiv r s (a, d, v) = positionEquiv r s (a, d, u) at h
  exact huv (congrArg (fun p : BitString r × Bool × BitString s => p.2.2)
    ((positionEquiv r s).injective h)).symm

theorem railControl_lower (r : ℕ) {s : ℕ} (K : Finset (BitString s))
    (hOther : ∀ u ∈ K, ∃ v ∈ K, u ≠ v) :
    2 * ((2 ^ r * 2) * K.card) ≤ complexity interpretation (single (railControl r K)) + 1 := by
  rw [← control_rails r K, ← card_active r K]
  exact blockControl_lower _ _ (active_has_mate r K hOther)

/-- Each constant certificate of the split control reads every retained entry,
even when it is used as part of a larger pool. -/
theorem railControl_inputStates_card (r : ℕ) {s : ℕ} (K : Finset (BitString s))
    (hOther : ∀ u ∈ K, ∃ v ∈ K, u ≠ v)
    (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (railControl r K)))
    (sample : Finset (BitString (2 ^ (r + (s + 1))))) (b : Bool) (hb : (fun _ => b) ∈ sample) :
    (2 ^ r * 2) * K.card ≤ (MultiCertificates.inputStates c.program (c.outputs 0) sample b).card := by
  classical
  have h := active_in_certificate (fun q : BitString r × Bool => railBlock K q.1 q.2)
    (active r K) (active_has_mate r K hOther)
    c (by rw [control_rails]; exact hc) sample b hb
  rw [← card_active r K]
  have hSub : certificate c sample (fun _ => b) ⊆ MultiCertificates.inputStates c.program (c.outputs 0) sample b :=
    fun _ hi => (Finset.mem_filter.mp hi).2
  exact (Finset.card_le_card h).trans (Finset.card_le_card hSub)

abbrev Remaining : ℕ := 4294967295

theorem railControl32_pin_upper (a : BitString 9) (d v : Bool) {u : BitString 22}
    (hu : u ∈ keep) :
    complexity interpretation (single (pin (n := Remaining) (railControl 9 keep) (position a d u) v)) ≤
      1023 * (2 * keep.card + 5) + keep.card + 3 := by
  rw [← control_rails 9 keep]
  let blocks (q : BitString 9 × Bool) : Finset (Fin (Remaining + 1)) :=
    railBlock (r := 9) (s := 22) keep q.1 q.2
  let i : Fin (Remaining + 1) := position a d u
  have hSize (q : BitString 9 × Bool) : (blocks q).card ≤ keep.card :=
    (card_railBlock keep q.1 q.2).le
  have hMem (q : BitString 9 × Bool) : i ∈ blocks q ↔ q = (a, d) := by
    have hh := pos_mem_block_iff keep a q.1 d q.2 u
    exact hh.trans ⟨fun h => h.1.symm, fun h => ⟨h.symm, hu⟩⟩
  have h := blockControl_pin_upper blocks i v (a, d) keep.card hSize hMem
  have hCard : Fintype.card (BitString 9 × Bool) - 1 = 1023 := by
    rw [Fintype.card_prod, BitString.card, Fintype.card_bool]
    decide
  exact hCard ▸ h

theorem railControl32_pin_saves_at_least (a : BitString 9) (d v : Bool) {u : BitString 22}
    (hu : u ∈ keep) :
    complexity interpretation (single (pin (n := Remaining) (railControl 9 keep) (position a d u) v)) +
      4189181 ≤ complexity interpretation (single (railControl 9 keep)) := by
  have h := railControl32_pin_upper a d v hu
  have hFull := railControl_lower 9 keep (fun u _ => has_other_retained u)
  rw [card_keep] at h hFull
  norm_num at h hFull
  omega

theorem railControl32_pin_unchanged_of_omitted (a : BitString 9) (d v w : Bool)
    {u : BitString 22} (hu : u ∉ keep) :
    pin (n := Remaining) (railControl 9 keep) (position a d u) v =
      pin (railControl 9 keep) (position a d u) w := by
  rw [← control_rails 9 keep]
  let blocks (q : BitString 9 × Bool) : Finset (Fin (Remaining + 1)) :=
    railBlock (r := 9) (s := 22) keep q.1 q.2
  let i : Fin (Remaining + 1) := position a d u
  exact blockControl_pin_unchanged_of_omitted blocks i v w fun q h =>
    hu ((pos_mem_block_iff keep a q.1 d q.2 u).mp h).2

#print axioms railControl32_pin_saves_at_least
#print axioms railControl32_pin_unchanged_of_omitted

end PvsNP.Frontier.SplitControl
