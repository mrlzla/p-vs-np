module

public import MCSPPatchedControl

/-! Selectors can adapt to the fixed set of locations a circuit observes.
The four-flip tests on both sides then require nine complete sampled pairs. -/

@[expose] public section

namespace PvsNP.Frontier.MultiSelector

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CommunicationCut SuperTwoN PermutedCut PatchedCut
open InvariantControl (point point_cons unit)
open scoped Classical

abbrev Tail := BitString 22

def readsOnly (F : BooleanFunction (2 ^ 32)) (S : Finset Address) : Prop :=
  ∀ X Y : BitString (2 ^ 32), (∀ i ∈ S, X i = Y i) → F X = F Y

noncomputable def pairs (S : Finset Address) (a : BitString 9) : Finset Tail :=
  Finset.univ.filter (fun t => position a false t ∈ S ∧ position a true t ∈ S)

noncomputable def anchoredTails (S : Finset Address) (a : BitString 9) : Finset Tail :=
  Finset.univ.filter (fun t => position a false t ∈ S ∨ position a true t ∈ S)

private theorem pos_injective_tail {r s : ℕ} (a : BitString r) {b b' : Bool} {t t' : BitString s}
    (he : position a b t = position a b' t') : t = t' := by
  change (positionEquiv r s) (a, b, t) = (positionEquiv r s) (a, b', t') at he
  exact congrArg (fun x : BitString r × Bool × BitString s => x.2.2) ((positionEquiv r s).injective he)

theorem anchoredTails_card (S : Finset Address) (a : BitString 9) : (anchoredTails S a).card ≤ S.card := by
  let b (t : Tail) := !(decide (position a false t ∈ S))
  apply Finset.card_le_card_of_injOn (fun t => position a (b t) t)
  · intro t ht
    rcases (Finset.mem_filter.mp ht).2 with h | h
    · simp [b, h]
    · by_cases h' : position a false t ∈ S <;> simp [b, h', h]
  · intro x _ y _ he
    exact pos_injective_tail a he

private theorem exists_four_split (E : Finset Address) (hE : E.card ≤ 8) :
    ∃ A B : Finset Address, A.card ≤ 4 ∧ B.card ≤ 4 ∧ A ∪ B = E ∧ Disjoint A B := by
  obtain ⟨A, hSub, hA⟩ := Finset.exists_subset_card_eq (min_le_right 4 E.card)
  refine ⟨A, E \ A, ?_, ?_, Finset.union_sdiff_of_subset hSub, ?_⟩
  · omega
  · have hh := Finset.card_sdiff_add_card_eq_card hSub
    omega
  · exact Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_sdiff.mp hj).2 hi)

private theorem patched_zero_agrees {S E A B : Finset Address} {T : BitString (2 ^ 32)}
    (hT : ∀ i ∈ S, T i = decide (i ∈ E)) (hE : A ∪ B = E) (hDis : Disjoint A B) :
    ∀ i ∈ S, patch A T i = patch B (fun _ => false) i := by
  intro i hi
  have ht := hT i hi
  rw [← hE] at ht
  by_cases hA : i ∈ A
  · have hB : i ∉ B := fun h => (Finset.disjoint_left.mp hDis) hA h
    simp [patch, ht, hA, hB]
  · by_cases hB : i ∈ B <;> simp [patch, ht, hA, hB]

private theorem mixed_hides_row (S : Finset Address) (a : BitString 9)
    {h : Selector} (hAnchor : ∀ t ∈ anchoredTails S a,
      h t = decide (position a true t ∈ S ∧ position a false t ∉ S)) :
    ∀ i ∈ S, mixed h (fun p => decide (p = a)) (fun _ => false) i =
      decide (i ∈ (pairs S a).image (position a true)) := by
  intro i hi
  obtain ⟨⟨p,b,t⟩, rfl⟩ := (positionEquiv 9 22).surjective i
  change position p b t ∈ S at hi
  change mixed h (fun p => decide (p = a)) (fun _ => false) (position p b t) =
    decide (position p b t ∈ (pairs S a).image (position a true))
  have hImage :
      position p b t ∈ (pairs S a).image (position a true) ↔ p = a ∧ b = true ∧ t ∈ pairs S a := by
    constructor
    · rintro h
      obtain ⟨u, hu, hEq⟩ := Finset.mem_image.mp h
      have ht : (a, true, u) = (p, b, t) := (positionEquiv 9 22).injective hEq
      cases ht
      exact ⟨rfl, rfl, hu⟩
    · rintro ⟨rfl, rfl, h⟩
      exact Finset.mem_image_of_mem (position p true) h
  unfold mixed splice
  simp only [mask_at_position, probe_at_position, hImage]
  by_cases hp : p = a
  · subst p
    have ht : t ∈ anchoredTails S a := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      cases b
      · exact Or.inl hi
      · exact Or.inr hi
    rw [hAnchor t ht]
    cases b with
    | false => simp [hi]
    | true =>
      by_cases hF : position a false t ∈ S <;> simp [pairs, hi, hF]
  · simp [hp]

/-- A sampler valid for every four-flip selector needs nine complete split
pairs in each row. Eight discrepancies can be shared between two patches. -/
theorem nine_pairs_of_all_selectors (F : BooleanFunction (2 ^ 32)) (S : Finset Address)
    (hRead : readsOnly F S) (hTests : ∀ h, Tests (mcspSquare 32) h → Tests F h)
    (a : BitString 9) (hRoom : 28828 < 2 ^ 22 - (anchoredTails S a).card) :
    9 ≤ (pairs S a).card := by
  by_contra! hFew
  have h8 : (pairs S a).card ≤ 8 := by omega
  let v : Selector := fun t => decide (position a true t ∈ S ∧ position a false t ∉ S)
  obtain ⟨h, hAnchor, hMCSP⟩ := exists_patched_selector_with (anchoredTails S a) v hRoom
  let E := (pairs S a).image (position a true)
  have hE : E.card ≤ 8 := Finset.card_image_le.trans h8
  obtain ⟨A, B, hA, hB, hUnion, hSep⟩ := exists_four_split E hE
  let f : Prefix := fun p => decide (p = a)
  let g : Prefix := fun _ => false
  have hfg : f ≠ g := by
    intro he
    have h := congrFun he a
    simp [f, g] at h
  have hEqual := hRead _ _ (patched_zero_agrees (mixed_hides_row S a hAnchor) hUnion hSep)
  have hDiag : mixed h g g = fun _ => false := by
    have he : probe 22 g = fun _ => false := by
      funext i
      obtain ⟨⟨x,b,t⟩, rfl⟩ := (positionEquiv 9 22).surjective i
      change probe 22 g (position x b t) = false
      rw [probe_at_position]
    unfold mixed
    rw [splice_self, he]
  have hYes := (hTests h hMCSP g g B hB).mpr rfl
  rw [hDiag] at hYes
  exact hfg ((hTests h hMCSP f g A hA).mp (hEqual.trans hYes))

theorem nine_pairs_after_transport (F : BooleanFunction (2 ^ 32)) (S : Finset Address)
    (hRead : readsOnly F S) (e : Equiv.Perm (Fin 23))
    (hTests : ∀ h, Tests (mcspSquare 32) h → ∀ (f g : Prefix) (D : Finset Address), D.card ≤ 4 →
      (F (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) = true ↔ f = g))
    (a : BitString 9) (hRoom : 28828 < 2 ^ 22 - S.card) :
    9 ≤ (pairs (S.map (tablePerm (liftTail 9 e)).toEmbedding) a).card := by
  let p := tablePerm (liftTail 9 e)
  let G : BooleanFunction (2 ^ 32) := fun T => F (T ∘ p)
  have hRG : readsOnly G (S.map p.toEmbedding) := by
    intro X Y h
    apply hRead
    intro i hi
    exact h (p i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  have hTG (h : Selector) (hh : Tests (mcspSquare 32) h) : Tests G h := by
    intro f g D hD
    have he : (patch D (mixed h f g)) ∘ p =
        patch (D.map p.symm.toEmbedding) (mixed h f g ∘ p) := by
      funext i
      simp [patch, Function.comp_apply]
    unfold G
    rw [he]
    exact hTests h hh f g _ (by simpa using hD)
  have hc := anchoredTails_card (S.map p.toEmbedding) a
  rw [Finset.card_map] at hc
  exact nine_pairs_of_all_selectors G _ hRG hTG a (hRoom.trans_le (Nat.sub_le_sub_left hc _))

/-- The earlier parity sampler misses a selector with zero anchors after
swapping the split bit with a coordinate outside its nine sampled units. -/
theorem previous_bank_fails :
    ∃ h : Selector, Tests (mcspSquare 32) h ∧
      ∃ e : Equiv.Perm (Fin 23), ∃ f g : Prefix, f ≠ g ∧
        (mixed h f g ∘ tablePerm (liftTail 9 e)) ∘ sampleRead =
        (mixed h g g ∘ tablePerm (liftTail 9 e)) ∘ sampleRead := by
  have hGap (k : ℕ) (hk : k ≤ 576) : 28828 < 2 ^ 22 - k := by omega
  obtain ⟨h, hh, hMCSP⟩ := exists_patched_selector_with parityAnchors (fun _ => false)
    (hGap _ (Finset.card_image_le.trans (RefinedProbeControl.sample_card 23)))
  let e : Equiv.Perm (Fin 23) := Equiv.swap 0 10
  let f : Prefix := fun _ => true
  let g : Prefix := fun _ => false
  refine ⟨h, hMCSP, e, f, g, ?_, ?_⟩
  · intro he
    have hx : true = false := congrFun he (fun _ => false)
    cases hx
  · have hValue (a : BitString 9) (j : Fin 9) (b : Bool) :
        mixed h f g (tablePerm (liftTail 9 e) (readAddress a j b)) =
        mixed h g g (tablePerm (liftTail 9 e) (readAddress a j b)) := by
      let t : Fin 22 := j.castLE (by decide)
      let z : BitString 23 := Fin.cons b (unit t)
      change mixed h f g (tablePerm (liftTail 9 e) (point a z)) =
        mixed h g g (tablePerm (liftTail 9 e) (point a z))
      rw [InvariantControl.perm_point]
      let w := z ∘ e
      have hzero : w 0 = false := by
        have he : e 0 = (9 : Fin 22).succ := by decide
        have hne : (9 : Fin 22) ≠ t := by
          intro h
          have he := congrArg Fin.val h
          change 9 = j.val at he
          omega
        change z (e 0) = false
        rw [he]
        change (Fin.cons b (unit t) : BitString 23) (9 : Fin 22).succ = false
        rw [Fin.cons_succ]
        exact decide_eq_false hne
      have hAnchor : h (Fin.tail w) = false :=
        hh _ (Finset.mem_image.mpr ⟨w, RefinedProbeControl.sample_perm e (cons_unit_sample b t), rfl⟩)
      change mixed h f g (point a w) = mixed h g g (point a w)
      rw [point_tail]
      unfold mixed splice
      rw [mask_at_position, hzero, hAnchor]
      rfl
    funext i
    let x := sampleIndex.symm i
    exact hValue x.1 x.2.1 x.2.2

#print axioms nine_pairs_of_all_selectors
#print axioms nine_pairs_after_transport
#print axioms previous_bank_fails

end PvsNP.Frontier.MultiSelector
