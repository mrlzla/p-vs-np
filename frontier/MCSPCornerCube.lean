module

public import MCSPRefinedCut

/-! Large accepting subcubes through both constant tables of exact quadratic MCSP. -/

@[expose] public section

namespace PvsNP.Frontier.CornerCube

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut RefinedCut

set_option maxRecDepth 2048

def zeroSuffix : BitString 22 := fun _ => false

def cornerIndex : Coordinate → Fin (2 ^ 32) :=
  Sum.elim (fun a => position a false zeroSuffix)
    (fun a => position (Fin.append a zeroHigh) true zeroSuffix)

/-- The 512 entries on one rail and 32 on the other, all at a fixed suffix. -/
def cornerFree : Finset (Fin (2 ^ 32)) := (Finset.univ : Finset Coordinate).image cornerIndex

private theorem append_high (a : BitString 5) : high (Fin.append a zeroHigh) = zeroHigh := by
  funext i
  simp [high]

private theorem append_low (a : BitString 5) : low (Fin.append a zeroHigh) = a := by
  funext i
  simp [low]

private theorem append_restore (a : BitString 9) (ha : high a = zeroHigh) :
    Fin.append (low a) zeroHigh = a := by
  rw [← ha]
  exact Fin.append_castAdd_natAdd

theorem card_cornerFree : cornerFree.card = 544 := by
  have hi : Function.Injective cornerIndex := by
    rintro (a | a) (b | b) h
    · change positionEquiv 9 22 (a, false, zeroSuffix) = positionEquiv 9 22 (b, false, zeroSuffix) at h
      have h := (positionEquiv 9 22).injective h
      exact congrArg Sum.inl (congrArg Prod.fst h)
    · change positionEquiv 9 22 (a, false, zeroSuffix) =
        positionEquiv 9 22 (Fin.append b zeroHigh, true, zeroSuffix) at h
      have h := (positionEquiv 9 22).injective h
      cases congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.1) h
    · change positionEquiv 9 22 (Fin.append a zeroHigh, true, zeroSuffix) =
        positionEquiv 9 22 (b, false, zeroSuffix) at h
      have h := (positionEquiv 9 22).injective h
      cases congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.1) h
    · change positionEquiv 9 22 (Fin.append a zeroHigh, true, zeroSuffix) =
        positionEquiv 9 22 (Fin.append b zeroHigh, true, zeroSuffix) at h
      have h := (positionEquiv 9 22).injective h
      have h := congrArg (fun p : BitString 9 × Bool × BitString 22 => low p.1) h
      exact congrArg Sum.inr (by simpa only [append_low] using h)
  rw [cornerFree, Finset.card_image_of_injective _ hi, Finset.card_univ,
    Fintype.card_sum, BitString.card, BitString.card]
  decide

private theorem mem_cornerFree_at (a : BitString 9) (d : Bool) (t : BitString 22) :
    position a d t ∈ cornerFree ↔ t = zeroSuffix ∧ (d = false ∨ high a = zeroHigh) := by
  constructor
  · intro h
    obtain ⟨u, _, he⟩ := Finset.mem_image.mp h
    cases u with
    | inl u =>
      change positionEquiv 9 22 (u, false, zeroSuffix) = positionEquiv 9 22 (a, d, t) at he
      have h := (positionEquiv 9 22).injective he
      exact ⟨(congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.2) h).symm,
        .inl (congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.1) h).symm⟩
    | inr u =>
      change positionEquiv 9 22 (Fin.append u zeroHigh, true, zeroSuffix) = positionEquiv 9 22 (a, d, t) at he
      have h := (positionEquiv 9 22).injective he
      exact ⟨(congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.2) h).symm,
        .inr ((congrArg (fun p : BitString 9 × Bool × BitString 22 => high p.1) h).symm.trans
          (append_high u))⟩
  · rintro ⟨rfl, h⟩
    cases d with
    | false => exact Finset.mem_image.mpr ⟨.inl a, Finset.mem_univ _, rfl⟩
    | true =>
      have hh : high a = zeroHigh := h.resolve_left (by decide)
      exact Finset.mem_image.mpr ⟨.inr (low a), Finset.mem_univ _,
        congrArg (fun w => position w true zeroSuffix) (append_restore a hh)⟩

private def prefixBits (x : BitString 32) : BitString 9 := x ∘ Fin.castAdd 23
private def splitBit (x : BitString 32) : Bool := x (Fin.natAdd 9 (0 : Fin 23))
private def suffixBits (x : BitString 32) : BitString 22 := x ∘ (Fin.natAdd 9 ∘ Fin.succ)

private theorem splitBit_at (a : BitString 9) (d : Bool) (t : BitString 22) :
    splitBit (Fin.append a (Fin.cons d t)) = d := by
  change (Fin.append a (Fin.cons d t) ∘ Fin.natAdd 9) (0 : Fin 23) = d
  rw [Fin.append_comp_natAdd, Fin.cons_zero]

private theorem suffixBits_at (a : BitString 9) (d : Bool) (t : BitString 22) :
    suffixBits (Fin.append a (Fin.cons d t)) = t := by
  change (Fin.append a (Fin.cons d t) ∘ Fin.natAdd 9) ∘ Fin.succ = t
  rw [Fin.append_comp_natAdd]
  funext j
  simp

private theorem truthTable_at_position {r s : ℕ} (f : BooleanFunction (r + (s + 1)))
    (a : BitString r) (d : Bool) (u : BitString s) :
    MCSP.truthTable _ f (position a d u) = f (Fin.append a (Fin.cons d u)) := by
  simp [MCSP.truthTable, position]

theorem accepts_cornerCube (b : Bool) (t : BitString (2 ^ 32)) :
    mcspSquare 32 (restrictTable (fun _ => b) cornerFree t) = true := by
  let left : BooleanFunction 9 := fun a => t (cornerIndex (.inl a)) ^^ b
  let right : BooleanFunction 5 := fun a => t (cornerIndex (.inr a)) ^^ b
  let tail : BooleanFunction 32 := fun x => decide (suffixBits x = zeroSuffix)
  let highZero : BooleanFunction 32 := fun x => decide (high (prefixBits x) = zeroHigh)
  let fLeft : BooleanFunction 32 := fun x => left (prefixBits x)
  let fRight : BooleanFunction 32 := fun x => right (low (prefixBits x))
  let notSplit : BooleanFunction 32 := fun x => !splitBit x
  let L : BooleanFunction 32 := fun x => notSplit x && fLeft x
  let enable : BooleanFunction 32 := fun x => splitBit x && highZero x
  let R : BooleanFunction 32 := fun x => enable x && fRight x
  let both : BooleanFunction 32 := fun x => L x || R x
  let mixed : BooleanFunction 32 := fun x => tail x && both x
  let target : BooleanFunction 32 := fun x => mixed x ^^ b
  have hLeft : complexity interpretation (single fLeft) ≤ 848 :=
    shannon_lift (k := 2) (d := 7) left (Fin.castAdd 23)
  have hRight : complexity interpretation (single fRight) ≤ 112 :=
    shannon_lift (k := 1) (d := 4) right (Fin.castAdd 23 ∘ Fin.castAdd 4)
  have hTail : complexity interpretation (single tail) ≤ 45 :=
    (synthesis_minterm (Fin.natAdd 9 ∘ Fin.succ) zeroSuffix).complexity_le
  have hHigh : complexity interpretation (single highZero) ≤ 9 :=
    (synthesis_minterm (Fin.castAdd 23 ∘ Fin.natAdd 5) zeroHigh).complexity_le
  have hSplit : complexity interpretation (single splitBit) = 0 :=
    complexity_single_proj (Fin.natAdd 9 (0 : Fin 23))
  have hNot : complexity interpretation (single notSplit) ≤ 1 :=
    (complexity_not_le splitBit).trans (by omega)
  have hL : complexity interpretation (single L) ≤ 850 :=
    (complexity_and_le notSplit fLeft).trans (Nat.add_le_add_right (Nat.add_le_add hNot hLeft) 1)
  have hEnable : complexity interpretation (single enable) ≤ 10 :=
    (complexity_and_le splitBit highZero).trans (Nat.add_le_add_right (Nat.add_le_add hSplit.le hHigh) 1)
  have hR : complexity interpretation (single R) ≤ 123 :=
    (complexity_and_le enable fRight).trans (Nat.add_le_add_right (Nat.add_le_add hEnable hRight) 1)
  have hBoth : complexity interpretation (single both) ≤ 974 :=
    (complexity_or_le L R).trans (Nat.add_le_add_right (Nat.add_le_add hL hR) 1)
  have hMixed : complexity interpretation (single mixed) ≤ 1020 :=
    (complexity_and_le tail both).trans (Nat.add_le_add_right (Nat.add_le_add hTail hBoth) 1)
  have hTable : restrictTable (fun _ => b) cornerFree t = MCSP.truthTable 32 target := by
    funext i
    obtain ⟨⟨a, d, u⟩, he⟩ := (positionEquiv 9 22).surjective i
    change position a d u = i at he
    have hEval := truthTable_at_position (r := 9) (s := 22) target a d u
    change MCSP.truthTable 32 target (position a d u) = _ at hEval
    rw [← he, hEval, restrictTable]
    have hp : prefixBits (Fin.append a (Fin.cons d u)) = a := Fin.append_comp_castAdd ..
    simp only [target, mixed, both, L, R, enable, notSplit, tail, highZero, fLeft, fRight,
      splitBit_at, suffixBits_at, hp, left, right]
    by_cases hu : u = zeroSuffix
    · subst u
      cases d with
      | false =>
        have hmem := (mem_cornerFree_at a false zeroSuffix).mpr ⟨rfl, .inl rfl⟩
        simp [hmem, cornerIndex]
      | true =>
        by_cases ha : high a = zeroHigh
        · have hmem := (mem_cornerFree_at a true zeroSuffix).mpr ⟨rfl, .inr ha⟩
          simp [hmem, ha, cornerIndex, append_restore a ha]
        · have hmem : position a true zeroSuffix ∉ cornerFree :=
            fun hm => ha (((mem_cornerFree_at a true zeroSuffix).mp hm).2.resolve_left (by decide))
          simp [hmem, ha]
    · have hmem : position a d u ∉ cornerFree := fun hm => hu ((mem_cornerFree_at a d u).mp hm).1
      simp [hmem, hu]
  rw [hTable, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  cases b
  · have he : target = mixed := funext fun x => by simp [target]
    rw [he]
    exact hMixed.trans (by decide)
  · have he : target = fun x => !mixed x := funext fun x => by simp [target]
    rw [he]
    exact (complexity_not_le mixed).trans ((Nat.add_le_add_right hMixed 1).trans (by decide))

/-- Even an optimal uniform semantic certificate bound at the corners loses at
least 544 input states per corner. -/
theorem uniform_corner_certificate_bound_le (L : ℕ)
    (h : ∀ (b : Bool) (S : Finset (Fin (2 ^ 32))),
      (∀ x : BitString (2 ^ 32), (∀ i ∈ S, x i = b) → mcspSquare 32 x = true) → L ≤ S.card) :
    L + 544 ≤ 2 ^ 32 := by
  let fixed := (Finset.univ : Finset (Fin (2 ^ 32))) \ cornerFree
  have hFixed := h false fixed fun x hx => by
    have he : restrictTable (fun _ => false) cornerFree x = x := by
      funext i
      by_cases hi : i ∈ cornerFree
      · simp [restrictTable, hi]
      · have hb := hx i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)
        simp [restrictTable, hi, hb]
    rw [← he]
    exact accepts_cornerCube false x
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ cornerFree)
  rw [card_cornerFree, Finset.card_univ, Fintype.card_fin] at hc
  exact (Nat.add_le_add_right hFixed 544).trans_eq hc

theorem uniform_corner_bound_with_unit_credits {L credit : ℕ}
    (h : ∀ (b : Bool) (S : Finset (Fin (2 ^ 32))),
      (∀ x : BitString (2 ^ 32), (∀ i ∈ S, x i = b) → mcspSquare 32 x = true) → L ≤ S.card)
    (hcredit : credit ≤ 2 * 544) : 2 * L + credit ≤ 2 * 2 ^ 32 := by
  have hL := uniform_corner_certificate_bound_le L h
  omega

#print axioms accepts_cornerCube
#print axioms uniform_corner_bound_with_unit_credits

end PvsNP.Frontier.CornerCube
