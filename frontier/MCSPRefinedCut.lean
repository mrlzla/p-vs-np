module

public import MCSPDownstream

/-! Refine the exact-MCSP cut by splitting the two rails on 32 selected prefixes. -/

@[expose] public section

namespace PvsNP.Frontier.RefinedCut

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut Downstream

set_option maxRecDepth 2048

abbrev Coordinate := BitString 9 ⊕ BitString 5

def low (a : BitString 9) : BitString 5 := a ∘ Fin.castAdd 4
def high (a : BitString 9) : BitString 4 := a ∘ Fin.natAdd 5
def zeroHigh : BitString 4 := fun _ => false

def pick (a : BitString 9) (b : Bool) : Coordinate :=
  if b && decide (high a = zeroHigh) then .inr (low a) else .inl a

def label (i : Fin (2 ^ 32)) : Coordinate :=
  let abt := (positionEquiv 9 22).symm i
  pick abt.1 abt.2.1

private theorem label_at_position (a : BitString 9) (b : Bool) (t : BitString 22) :
    label (position a b t) = pick a b := by
  change label (positionEquiv 9 22 (a, b, t)) = _
  simp [label]

private theorem label_realized (q : Coordinate) :
    ∃ (a : BitString 9) (b : Bool), ∀ t : BitString 22, label (position a b t) = q := by
  cases q with
  | inl a => exact ⟨a, false, fun t => by simp [label_at_position, pick]⟩
  | inr a =>
    have hi : high (Fin.append a zeroHigh) = zeroHigh := by
      funext j
      simp [high]
    have lo : low (Fin.append a zeroHigh) = a := by
      funext j
      simp [low]
    exact ⟨Fin.append a zeroHigh, true, fun t => by simp [label_at_position, pick, hi, lo]⟩

theorem pick_surjective : Function.Surjective (fun p : BitString 9 × Bool => pick p.1 p.2) := by
  intro q
  obtain ⟨a, b, h⟩ := label_realized q
  exact ⟨(a, b), (label_at_position a b (fun _ => false)).symm.trans (h (fun _ => false))⟩

theorem shannon_lift {k d n : ℕ} (f : BooleanFunction (k + d)) (select : Fin (k + d) → Fin n) :
    complexity interpretation (single fun x => f (x ∘ select)) ≤ ShannonSynthesis.bound k d := by
  let c := (ShannonSynthesis.circuit f).comp (Circuit.wiring signature select)
  have hc : c.Computes interpretation (single fun x => f (x ∘ select)) := by
    intro x
    funext o
    simp [c, Circuit.eval_comp, Circuit.eval_wiring]
  exact (complexity_le_of_computes c hc).trans (by
    simpa [c, Circuit.size_comp] using ShannonSynthesis.size_circuit_le f)

private def prefixBits (x : BitString 32) : BitString 9 := x ∘ Fin.castAdd 23
private def splitBit (x : BitString 32) : Bool := x (Fin.natAdd 9 (0 : Fin 23))

private theorem label_truthTable_eq (z : Coordinate → Bool) (x : BitString 32) :
    z (label (BitString.equivFin 32 x)) = z (pick (prefixBits x) (splitBit x)) := by
  obtain ⟨⟨a, b, t⟩, h⟩ := (positionEquiv 9 22).surjective (BitString.equivFin 32 x)
  change position a b t = BitString.equivFin 32 x at h
  have hx : x = Fin.append a (Fin.cons b t) := (BitString.equivFin 32).injective h.symm
  rw [← h, label_at_position]
  rw [hx]
  have hs : splitBit (Fin.append a (Fin.cons b t)) = b := by
    change (Fin.append a (Fin.cons b t) ∘ Fin.natAdd 9) (0 : Fin 23) = b
    rw [Fin.append_comp_natAdd, Fin.cons_zero]
  simp [prefixBits, Function.comp_def, hs]

private theorem accepted_probe (z : Coordinate → Bool) : mcspSquare 32 (z ∘ label) = true := by
  let base : BooleanFunction 32 := fun x => z (.inl (prefixBits x))
  let arm : BooleanFunction 5 := fun u => z (.inl (Fin.append u zeroHigh)) ^^ z (.inr u)
  let delta : BooleanFunction 32 := fun x => arm (low (prefixBits x))
  let guard : BooleanFunction 32 := fun x => decide (high (prefixBits x) = zeroHigh)
  let enable : BooleanFunction 32 := fun x => guard x && splitBit x
  let extra : BooleanFunction 32 := fun x => delta x && enable x
  have hb : complexity interpretation (single base) ≤ 848 := by
    have h := shannon_lift (k := 2) (d := 7) (fun a => z (.inl a)) (Fin.castAdd 23)
    exact h
  have hd : complexity interpretation (single delta) ≤ 128 := by
    have h := shannon_lift (k := 2) (d := 3) arm (Fin.castAdd 23 ∘ Fin.castAdd 4)
    exact h
  have hg : complexity interpretation (single guard) ≤ 9 :=
    (synthesis_minterm (Fin.castAdd 23 ∘ Fin.natAdd 5) zeroHigh).complexity_le
  have hs : complexity interpretation (single splitBit) = 0 :=
    complexity_single_proj (Fin.natAdd 9 (0 : Fin 23))
  have hEnable : complexity interpretation (single enable) ≤ 10 :=
    (complexity_and_le guard splitBit).trans (by omega)
  have he : complexity interpretation (single extra) ≤ 139 :=
    (complexity_and_le delta enable).trans (Nat.add_le_add_right (Nat.add_le_add hd hEnable) 1)
  have hf : (MCSP.truthTable 32).symm (z ∘ label) = fun x => base x ^^ extra x := by
    funext x
    change z (label (BitString.equivFin 32 x)) = _
    rw [label_truthTable_eq z x]
    by_cases h : high (prefixBits x) = zeroHigh
    · have hAppend : Fin.append (low (prefixBits x)) zeroHigh = prefixBits x := by
        rw [← h]
        exact Fin.append_castAdd_natAdd
      cases hs : splitBit x <;> simp [pick, base, extra, delta, arm, enable, guard, h, hAppend, hs]
    · simp [pick, base, extra, delta, arm, enable, guard, h]
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hf]
  exact (complexity_xor_le base extra).trans (by omega)

section Selectors

variable {ι : Type*} {r s : ℕ}

private theorem splice_injective (ℓ : Fin (2 ^ (r + (s + 1))) → ι)
    (hℓ : ∀ q : ι, ∃ (a : BitString r) (b : Bool), ∀ t : BitString s, ℓ (position a b t) = q)
    {f g : ι → Bool} (hne : f ≠ g) :
    Function.Injective fun h : BooleanFunction s => splice (mask r h) (f ∘ ℓ) (g ∘ ℓ) := by
  obtain ⟨q, hq⟩ : ∃ q, f q ≠ g q := by
    by_contra! h
    exact hne (funext h)
  obtain ⟨a, b, hlabel⟩ := hℓ q
  intro h₁ h₂ he
  funext t
  have h := congrFun he (position a b t)
  simp only [splice, mask_at_position, Function.comp_apply, hlabel] at h
  cases b <;> cases hA : h₁ t <;> cases hB : h₂ t <;> simp_all

private noncomputable def badPair (ℓ : Fin (2 ^ (r + (s + 1))) → ι)
    (p : (ι → Bool) × (ι → Bool)) : Finset (BooleanFunction s) := open scoped Classical in
  if p.1 = p.2 then ∅ else Finset.univ.filter fun h =>
    mcspSquare (r + (s + 1)) (splice (mask r h) (p.1 ∘ ℓ) (p.2 ∘ ℓ)) = true

private theorem card_bad_pair (ℓ : Fin (2 ^ (r + (s + 1))) → ι)
    (hℓ : ∀ q : ι, ∃ (a : BitString r) (b : Bool), ∀ t : BitString s, ℓ (position a b t) = q)
    (p : (ι → Bool) × (ι → Bool)) :
    (badPair ℓ p).card ≤ 2 ^ descriptionBitBound (r + (s + 1)) := by
  classical
  by_cases h : p.1 = p.2
  · simp [badPair, h]
  · apply le_trans _ (card_accepting_mcspSquare_le (r + (s + 1)))
    apply Finset.card_le_card_of_injOn (fun h => splice (mask r h) (p.1 ∘ ℓ) (p.2 ∘ ℓ))
    · intro s hs
      simpa [badPair, h, acceptingTables] using hs
    · exact (splice_injective ℓ hℓ h).injOn

private theorem exists_good_labels_on [Fintype ι] (ℓ : Fin (2 ^ (r + (s + 1))) → ι)
    (hℓ : ∀ q : ι, ∃ (a : BitString r) (b : Bool), ∀ t : BitString s, ℓ (position a b t) = q)
    (hAccepted : ∀ f : ι → Bool, mcspSquare (r + (s + 1)) (f ∘ ℓ) = true)
    (avoid : Finset (BooleanFunction s)) (E : ℕ)
    (hAvoid : avoid.card ≤ 2 ^ E)
    (hE : Fintype.card ι + Fintype.card ι + descriptionBitBound (r + (s + 1)) ≤ E)
    (candidates : Finset (BooleanFunction s)) (hGap : 2 ^ (E + 1) < candidates.card) :
    ∃ h : BooleanFunction s, h ∈ candidates ∧ h ∉ avoid ∧ ∀ f g : ι → Bool,
      mcspSquare (r + (s + 1)) (splice (mask r h) (f ∘ ℓ) (g ∘ ℓ)) = true ↔ f = g := by
  classical
  let pairs := (Finset.univ : Finset ((ι → Bool) × (ι → Bool)))
  let bad := pairs.biUnion (badPair ℓ) ∪ avoid
  have hCount : pairs.card = 2 ^ (Fintype.card ι + Fintype.card ι) := by
    simp only [pairs, Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, pow_add]
  have hPair : (pairs.biUnion (badPair ℓ)).card ≤ 2 ^ E := calc
    _ ≤ ∑ p ∈ pairs, (badPair ℓ p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ pairs, 2 ^ descriptionBitBound (r + (s + 1)) :=
      Finset.sum_le_sum fun p _ => card_bad_pair ℓ hℓ p
    _ = 2 ^ (Fintype.card ι + Fintype.card ι + descriptionBitBound (r + (s + 1))) := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, hCount, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hE
  have hCard : bad.card ≤ 2 ^ (E + 1) := calc
    _ ≤ (pairs.biUnion (badPair ℓ)).card + avoid.card := Finset.card_union_le ..
    _ ≤ 2 ^ E + 2 ^ E := Nat.add_le_add hPair hAvoid
    _ = _ := by rw [pow_succ', two_mul]
  have hLt := hCard.trans_lt hGap
  obtain ⟨h, hCandidate, hGood⟩ : ∃ h : BooleanFunction s, h ∈ candidates ∧ h ∉ bad := by
    by_contra! hf
    exact (not_le_of_gt hLt) (Finset.card_le_card hf)
  refine ⟨h, hCandidate, fun hh => hGood (Finset.mem_union_right _ hh), ?_⟩
  intro f g
  constructor
  · intro hAccept
    by_contra hne
    apply hGood
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨(f, g), Finset.mem_univ _, by simp [badPair, hne, hAccept]⟩)
  · rintro rfl
    rw [splice_self]
    exact hAccepted f

end Selectors

private theorem coordinate_card : Fintype.card Coordinate = 544 := by
  rw [Fintype.card_sum, BitString.card, BitString.card]
  decide

private theorem exists_refined_selector_on (E : ℕ)
    (hE : Fintype.card Coordinate + Fintype.card Coordinate +
      descriptionBitBound (9 + (22 + 1)) ≤ E)
    (hOld : 2 ^ 9 + 2 ^ 9 + descriptionBitBound (9 + (22 + 1)) ≤ E)
    (candidates : Finset (BooleanFunction 22)) (hGap : 2 ^ (E + 1) < candidates.card) :
    ∃ h : BooleanFunction 22, h ∈ candidates ∧ h ∉ badSelectors 9 22 ∧ ∀ f g : Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ label) (g ∘ label)) = true ↔ f = g := by
  have hOldCount : (badSelectors 9 22).card ≤ 2 ^ E := (card_badSelectors_le 9 22).trans
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hOld)
  exact exists_good_labels_on (r := 9) (s := 22) label label_realized accepted_probe
    (badSelectors 9 22) E hOldCount hE candidates hGap

theorem exists_refined_equality_cut_on (candidates : Finset (BooleanFunction 22))
    (hc : 2 ^ (28760 + 1) < candidates.card) :
    ∃ h : BooleanFunction 22, h ∈ candidates ∧ h ∉ badSelectors 9 22 ∧ ∀ f g : Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ label) (g ∘ label)) = true ↔ f = g := by
  have hB : descriptionBitBound (9 + (22 + 1)) = 27672 := by decide
  have hE : Fintype.card Coordinate + Fintype.card Coordinate + descriptionBitBound (9 + (22 + 1)) ≤ 28760 := by
    rw [coordinate_card, hB]
  have hOldExp : 2 ^ 9 + 2 ^ 9 + descriptionBitBound (9 + (22 + 1)) ≤ 28760 := by
    rw [hB]
    decide
  exact exists_refined_selector_on 28760 hE hOldExp candidates hc

private theorem pow_lt_card_full {w E : ℕ} (h : E < 2 ^ w) :
    2 ^ E < (Finset.univ : Finset (BooleanFunction w)).card := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, BitString.card]
  exact Nat.pow_lt_pow_right (by decide) h

theorem exists_refined_equality_cut :
    ∃ h : BooleanFunction 22, h ∉ badSelectors 9 22 ∧ ∀ f g : Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ label) (g ∘ label)) = true ↔ f = g := by
  classical
  have hExp : 28760 + 1 < (2 : ℕ) ^ 22 := by decide
  obtain ⟨h, _, hGood, heq⟩ := exists_refined_equality_cut_on Finset.univ (pow_lt_card_full hExp)
  exact ⟨h, hGood, heq⟩

noncomputable def prescribed {w : ℕ} (S : Finset (BitString w)) (p : BooleanFunction w) :
    Finset (BooleanFunction w) := open scoped Classical in
  Finset.univ.filter fun h => ∀ t ∈ S, h t = p t

theorem mem_prescribed {w : ℕ} {S : Finset (BitString w)} {p h : BooleanFunction w} :
    h ∈ prescribed S p ↔ ∀ t ∈ S, h t = p t := by
  simp only [prescribed, Finset.mem_filter, Finset.mem_univ, true_and]

theorem prescribed_large {w E : ℕ} (S : Finset (BitString w)) (p : BooleanFunction w)
    (gap : E < 2 ^ w - S.card) : 2 ^ E < (prescribed S p).card := by
  classical
  let outside := (Finset.univ : Finset (BitString w)) \ S
  let fill (u : outside → Bool) (t : BitString w) := if ht : t ∈ outside then u ⟨t, ht⟩ else p t
  let into (u : outside → Bool) : prescribed S p :=
    ⟨fill u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht => by simp [fill, outside, ht]⟩⟩
  have hi : Function.Injective into := by
    intro u v h
    funext t
    simpa [into, fill, t.property] using congrFun (congrArg Subtype.val h) t.val
  have hc := Fintype.card_le_of_injective into hi
  have hout : outside.card = 2 ^ w - S.card := by
    simp [outside, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hout] at hc
  exact (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) gap).trans_le hc

set_option linter.constructorNameAsVariable false in
theorem exists_refined_equality_cut_with (S : Finset (BitString 22)) (p : BooleanFunction 22)
    (gap : 28760 + 1 < 2 ^ 22 - S.card) :
    ∃ h : BooleanFunction 22, (∀ t ∈ S, h t = p t) ∧ h ∉ badSelectors 9 22 ∧
      ∀ f g : Coordinate → Bool,
        mcspSquare 32 (splice (mask 9 h) (f ∘ label) (g ∘ label)) = true ↔ f = g := by
  obtain ⟨h, hh, hgood, heq⟩ := exists_refined_equality_cut_on (prescribed S p) (prescribed_large S p gap)
  simp only [prescribed, Finset.mem_filter, Finset.mem_univ, true_and] at hh
  exact ⟨h, hh, hgood, heq⟩

theorem square32_width_544 :
    ∃ h : BooleanFunction 22, h ∉ badSelectors 9 22 ∧
      ∀ (c : Circuit signature (2 ^ 32) 1)
        (_ : c.Computes interpretation (single (mcspSquare 32)))
        (owner : Wire (2 ^ 32) c.size → Bool) (_ : ∀ i, owner (.input i) = mask 9 h i),
        544 ≤ (crossingWires c.program owner).card := by
  obtain ⟨h, hOld, hEq⟩ := exists_refined_equality_cut
  refine ⟨h, hOld, ?_⟩
  intro c hc owner howner
  obtain ⟨choose, hinj, hchoose⟩ := exists_distinct_downstream_sources _ label (mask 9 h) c hc
    hEq owner howner
  have hWidth := width_of_distinct_sources c.program owner label choose hinj hchoose
  rwa [coordinate_card] at hWidth

#print axioms square32_width_544

end PvsNP.Frontier.RefinedCut
