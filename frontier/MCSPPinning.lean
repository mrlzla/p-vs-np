module

public import MCSPMultiCertificates
public import Complexity.Computability.Circuit.Boolean.Synthesis

/-! Two accepted certificates after fixing one truth-table entry. -/

@[expose] public section

namespace PvsNP.Frontier.Pinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean MultiCertificates

variable {n g : ℕ}

def flip (x : BitString n) : BitString n := fun j => !x j

def pin (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) (b : Bool) : BooleanFunction n :=
  fun x => f (i.insertNth b x)

private theorem pair_requested_le (p : Program signature n g) (root : Wire n g)
    (x y : BitString n) (k : Fin g) :
    (requestedArguments p root {x, y} k).card ≤ (outputValues p root {x, y} k).card + 1 := by
  classical
  let sample : Finset (BitString n) := {x, y}
  let v (z : BitString n) := p.trace interpretation z (.gate k)
  let used (b : Bool) := Needed p root sample (.gate k, b)
  let S := outputValues p root sample k
  have eqRequested : requestedArguments p root sample k =
      (if used (v x) then argumentsAt p k x else ∅) ∪
      (if used (v y) then argumentsAt p k y else ∅) := by
    ext key
    simp only [requestedArguments, Finset.mem_biUnion, Finset.mem_filter, sample,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    have memIf (z : BitString n) :
        key ∈ (if used (v z) then argumentsAt p k z else ∅) ↔
          used (v z) ∧ key ∈ argumentsAt p k z := by
      by_cases h : used (v z) <;> simp [h]
    rw [memIf, memIf]
    constructor
    · rintro ⟨z, ⟨rfl | rfl, hz⟩, hk⟩
      · exact Or.inl ⟨hz, hk⟩
      · exact Or.inr ⟨hz, hk⟩
    · rintro (⟨hx, hk⟩ | ⟨hy, hk⟩)
      · exact ⟨x, ⟨Or.inl rfl, hx⟩, hk⟩
      · exact ⟨y, ⟨Or.inr rfl, hy⟩, hk⟩
  have one (z : BitString n) : (argumentsAt p k z).card ≤ 2 :=
    CornerCertificates.card_argumentStates_le ..
  have two : (argumentsAt p k x ∪ argumentsAt p k y).card ≤ if v x = v y then 2 else 3 := by
    simpa only [argumentsAt, v, p.trace_gate] using
      CornerCertificates.union_bound (p.lines k).op (p.lines k).wires
        (fun a => p.trace interpretation x ((p.lines k).wires a))
        (fun a => p.trace interpretation y ((p.lines k).wires a))
  have memS (b : Bool) (h : used b) : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  change (requestedArguments p root sample k).card ≤ S.card + 1
  rw [eqRequested]
  by_cases hx : used (v x) <;> by_cases hy : used (v y) <;> simp only [hx, hy, ite_true, ite_false]
  · by_cases heq : v x = v y
    · have hS := Finset.card_pos.mpr ⟨_, memS _ hx⟩
      simp [heq] at two
      omega
    · have hS := Finset.card_le_card (show {v x, v y} ⊆ S by
          simp [Finset.insert_subset, memS _ hx, memS _ hy])
      simp [heq] at two hS
      omega
  · rw [Finset.union_empty]
    have hS := Finset.card_pos.mpr ⟨_, memS _ hx⟩
    have := one x
    omega
  · rw [Finset.empty_union]
    have hS := Finset.card_pos.mpr ⟨_, memS _ hy⟩
    have := one y
    omega
  · simp

noncomputable def certificate (c : Circuit signature n 1) (sample : Finset (BitString n))
    (x : BitString n) : Finset (Fin n) := open scoped Classical in
  Finset.univ.filter fun i => i ∈ inputStates c.program (c.outputs 0) sample (x i)

theorem accepts_of_agrees_on_certificate (f : BooleanFunction n) (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f)) (sample : Finset (BitString n))
    {x y : BitString n} (hx : x ∈ sample) (haccept : f x = true)
    (hagree : ∀ i ∈ certificate c sample x, y i = x i) : f y = true := by
  classical
  have htrace := certifies_accepted c.program (c.outputs 0) sample x y hx
    ((congrFun (hc x) 0).trans haccept) (fun i hi => hagree i (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hi⟩))
  exact (congrFun (hc y) 0).symm.trans htrace

theorem certificate_card_add_bound (c : Circuit signature n 1) (x : BitString n) :
    (certificate c {x, flip x} x).card + (certificate c {x, flip x} (flip x)).card ≤
      c.size + 1 := by
  classical
  let sample : Finset (BitString n) := {x, flip x}
  let S := inputStates c.program (c.outputs 0) sample
  let A := certificate c sample x
  let B := certificate c sample (flip x)
  let map : (↑A ⊕ ↑B) → (↑(S false) ⊕ ↑(S true)) := fun side =>
    let lift (z : BitString n) (i : ↑(certificate c sample z)) :
        ↑(S false) ⊕ ↑(S true) :=
      if h : z i = false then .inl ⟨i, h ▸ (Finset.mem_filter.mp i.property).2⟩
      else .inr ⟨i, (Bool.eq_true_of_not_eq_false h) ▸ (Finset.mem_filter.mp i.property).2⟩
    side.elim (lift x) (lift (flip x))
  let pos (side : ↑(S false) ⊕ ↑(S true)) : Fin n := side.elim Subtype.val Subtype.val
  let polarity (side : ↑(S false) ⊕ ↑(S true)) : Bool := side.elim (fun _ => false) (fun _ => true)
  have hPos (a : A) : pos (map (.inl a)) = a.val := by
    dsimp [pos, map]
    split <;> rfl
  have hPos' (b : B) : pos (map (.inr b)) = b.val := by
    dsimp [pos, map]
    split <;> rfl
  have hPol (a : A) : polarity (map (.inl a)) = x a := by
    dsimp [polarity, map]
    split <;> simp_all
  have hPol' (b : B) : polarity (map (.inr b)) = flip x b := by
    dsimp [polarity, map]
    split <;> simp_all
  have separated (a : A) (b : B) (h : map (.inl a) = map (.inr b)) : False := by
    have hi := congrArg pos h
    rw [hPos, hPos'] at hi
    have hb := congrArg polarity h
    rw [hPol, hPol', flip, hi] at hb
    cases x b <;> simp_all
  have hinj : Function.Injective map := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext ((hPos a).symm.trans ((congrArg pos h).trans (hPos b))))
    · exact (separated a b h).elim
    · exact (separated b a h.symm).elim
    · exact congrArg Sum.inr (Subtype.ext ((hPos' a).symm.trans ((congrArg pos h).trans (hPos' b))))
  have hcard : A.card + B.card ≤ (S false).card + (S true).card := by
    simpa only [Fintype.card_sum, Fintype.card_coe] using Fintype.card_le_of_injective map hinj
  have hCount := input_states_add_charges_le c.program (c.outputs 0) sample
  have hExcess (k : Fin c.size) : excess c.program (c.outputs 0) sample k = 0 :=
    Nat.sub_eq_zero_of_le (pair_requested_le _ _ x (flip x) k)
  simp only [hExcess, Finset.sum_const_zero, Nat.add_zero] at hCount
  change (S false).card + (S true).card + _ + _ ≤ c.size + 1 at hCount
  exact hcard.trans (by omega)

theorem certificate_card_lower_of_sparse (f : BooleanFunction n) (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f)) (sample : Finset (BitString n))
    {x : BitString n} (hx : x ∈ sample) (haccept : f x = true)
    (B : ℕ) (hcount : (acceptingTables f).card ≤ 2 ^ B) :
    n ≤ (certificate c sample x).card + B := by
  classical
  let free := Finset.univ \ certificate c sample x
  have hAll (y : BitString n) : f (restrictTable x free y) = true :=
    accepts_of_agrees_on_certificate f c hc sample hx haccept fun i hi => by
      simp [restrictTable, free, hi]
  have hEmpty : essentialPositions (fun y => f (restrictTable x free y)) free = ∅ := by
    ext i
    simp [essentialPositions, EssentialAt, hAll]
  have hPow := (pow_card_inessential_le f x free haccept).trans hcount
  rw [hEmpty, Finset.sdiff_empty] at hPow
  have hFree := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPow
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (certificate c sample x))
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  change free.card + (certificate c sample x).card = n at hSplit
  omega

theorem complexity_lower_of_sparse_opposite (f : BooleanFunction n)
    (x : BitString n) (hx : f x = true) (hy : f (flip x) = true)
    (B : ℕ) (hcount : (acceptingTables f).card ≤ 2 ^ B) :
    2 * n ≤ complexity interpretation (single f) + 1 + 2 * B := by
  classical
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  have h₀ := certificate_card_lower_of_sparse f c hc {x, flip x} (x := x) (by simp) hx B hcount
  have h₁ := certificate_card_lower_of_sparse f c hc {x, flip x} (x := flip x) (by simp) hy B hcount
  have h := certificate_card_add_bound c x
  omega

def pinToTable {m n : ℕ} (hn : n + 1 = 2 ^ m) (i : Fin (n + 1)) (b : Bool)
    (x : BitString n) : BitString (2 ^ m) :=
  i.insertNth b x ∘ Fin.cast hn.symm

noncomputable def squarePin {m n : ℕ} (hn : n + 1 = 2 ^ m) (i : Fin (n + 1)) (b : Bool) :
    BooleanFunction n := mcspSquare m ∘ pinToTable hn i b

theorem mcspSquare_accepts_point (m : ℕ) (hm : 3 ≤ m) (j : Fin (2 ^ m)) (b : Bool) :
    mcspSquare m (fun k => if k = j then b else !b) = true := by
  let w := (BitString.equivFin m).symm j
  let synth := synthesis_minterm (id : Fin m → Fin m) w
  have hbudget : 2 * m + 2 ≤ m ^ 2 := by
    nlinarith [Nat.mul_le_mul_right m hm]
  have indexEq (x : BitString m) : BitString.equivFin m x = j ↔ x = w := by
    change _ ↔ x = (BitString.equivFin m).symm j
    rw [Equiv.eq_symm_apply]
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff]
  cases b
  · apply (Synthesis.congr_iff synth.not (fun x => ?_)).complexity_le.trans hbudget
    change (!(decide (x = w))) = true ↔ (if BitString.equivFin m x = j then false else true) = true
    by_cases h : x = w <;> simp [h, indexEq]
  · apply (Synthesis.congr_iff synth (fun x => ?_)).complexity_le.trans (by omega)
    change decide (x = w) = true ↔ (if BitString.equivFin m x = j then true else false) = true
    by_cases h : x = w <;> simp [h, indexEq]

theorem squarePin_accepts_opposite {m n : ℕ} (hm : 3 ≤ m) (hn : n + 1 = 2 ^ m)
    (i : Fin (n + 1)) (b : Bool) :
    squarePin hn i b (fun _ => b) = true ∧ squarePin hn i b (fun _ => !b) = true := by
  have hconstant : pinToTable hn i b (fun _ => b) = fun _ => b := by
    funext j
    unfold pinToTable
    change i.insertNth (α := fun _ => Bool) b (fun _ => b) (Fin.cast hn.symm j) = b
    refine i.succAboveCases ?_ (fun k => ?_) (Fin.cast hn.symm j)
    · simp
    · simp
  have hpoint : pinToTable hn i b (fun _ => !b) = fun j => if j = Fin.cast hn i then b else !b := by
    funext j
    obtain ⟨k, rfl⟩ := (Fin.castOrderIso hn).surjective j
    change i.insertNth (α := fun _ => Bool) b (fun _ => !b) k =
      if Fin.cast hn k = Fin.cast hn i then b else !b
    refine i.succAboveCases ?_ (fun l => ?_) k
    · simp
    · simp
  exact ⟨(congrArg (mcspSquare m) hconstant).trans (mcspSquare_constant_table m (by omega) b),
    (congrArg (mcspSquare m) hpoint).trans (mcspSquare_accepts_point m hm (Fin.cast hn i) b)⟩

theorem card_accepting_squarePin_le {m n : ℕ} (hn : n + 1 = 2 ^ m)
    (i : Fin (n + 1)) (b : Bool) :
    (acceptingTables (squarePin hn i b)).card ≤ 2 ^ descriptionBitBound m := by
  apply (Finset.card_le_card_of_injOn (pinToTable hn i b) ?_ ?_).trans
    (card_accepting_mcspSquare_le m)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    funext j
    simpa [pinToTable] using congrFun h (Fin.cast hn (i.succAbove j))

/-- Both one-bit restrictions retain the near-twice-linear lower bound. -/
theorem squarePin_lower {m n : ℕ} (hm : 3 ≤ m) (hn : n + 1 = 2 ^ m)
    (i : Fin (n + 1)) (b : Bool) :
    2 * n ≤ complexity interpretation (single (squarePin hn i b)) + 1 + 2 * descriptionBitBound m := by
  have hx := squarePin_accepts_opposite hm hn i b
  exact complexity_lower_of_sparse_opposite _ (fun _ => b) hx.1 hx.2 _
    (card_accepting_squarePin_le hn i b)

private theorem card_squarePin_pair_le {m n : ℕ} (hn : n + 1 = 2 ^ m) (i : Fin (n + 1)) :
    (acceptingTables (squarePin hn i false)).card + (acceptingTables (squarePin hn i true)).card ≤
      (acceptingTables (mcspSquare m)).card := by
  classical
  let A (b : Bool) := acceptingTables (squarePin hn i b)
  let insertAccepted (b : Bool) (x : A b) : acceptingTables (mcspSquare m) :=
    ⟨pinToTable hn i b x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp x.property).2⟩⟩
  let combine : (↑(A false) ⊕ ↑(A true)) → ↑(acceptingTables (mcspSquare m)) :=
    Sum.elim (insertAccepted false) (insertAccepted true)
  have equalRest (b v : Bool) (x : A b) (y : A v)
      (h : insertAccepted b x = insertAccepted v y) : x.val = y.val := by
    funext j
    have hh := congrFun (congrArg Subtype.val h) (Fin.cast hn (i.succAbove j))
    simpa [insertAccepted, pinToTable] using hh
  have equalPin (b v : Bool) (x : A b) (y : A v)
      (h : insertAccepted b x = insertAccepted v y) : b = v := by
    have hh := congrFun (congrArg Subtype.val h) (Fin.cast hn i)
    simpa [insertAccepted, pinToTable] using hh
  have hinj : Function.Injective combine := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (Subtype.ext (equalRest false false x y h))
    · cases equalPin false true x y h
    · cases equalPin true false x y h
    · exact congrArg Sum.inr (Subtype.ext (equalRest true true x y h))
  simpa only [Fintype.card_sum, Fintype.card_coe] using Fintype.card_le_of_injective combine hinj

/-- The sparser pinning value saves one bit in the count of accepted restricted tables. -/
theorem exists_squarePin_lower_of_count {m n B : ℕ} (hm : 3 ≤ m) (hn : n + 1 = 2 ^ m)
    (i : Fin (n + 1)) (hcount : (acceptingTables (mcspSquare m)).card ≤ 2 ^ (B + 1)) :
    ∃ b : Bool, 2 * n ≤ complexity interpretation (single (squarePin hn i b)) + 1 + 2 * B := by
  have hTwo := (card_squarePin_pair_le hn i).trans hcount
  rw [pow_succ' (2 : ℕ) B] at hTwo
  have hSmall : ∃ b : Bool, (acceptingTables (squarePin hn i b)).card ≤ 2 ^ B := by
    by_cases h : (acceptingTables (squarePin hn i false)).card ≤ 2 ^ B
    · exact ⟨false, h⟩
    · exact ⟨true, by omega⟩
  obtain ⟨b, hb⟩ := hSmall
  have hx := squarePin_accepts_opposite hm hn i b
  exact ⟨b, complexity_lower_of_sparse_opposite _ (fun _ => b) hx.1 hx.2 B hb⟩

theorem squarePin_nonconstant {m n : ℕ} (hm : 3 ≤ m) (hn : n + 1 = 2 ^ m)
    (hsparse : descriptionBitBound m < n) (i : Fin (n + 1)) (b : Bool) :
    ∃ x y, squarePin hn i b x ≠ squarePin hn i b y := by
  classical
  let f := squarePin hn i b
  have haccept : f (fun _ => b) = true := (squarePin_accepts_opposite hm hn i b).1
  by_contra! hconstant
  have hall : acceptingTables f = Finset.univ := by
    ext x
    simp only [acceptingTables, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (hconstant x (fun _ => b)).trans haccept
  have hCard : (acceptingTables f).card = 2 ^ n := by
    rw [hall, Finset.card_univ, BitString.card]
  have hCount := card_accepting_squarePin_le hn i b
  change (acceptingTables f).card ≤ _ at hCount
  rw [hCard] at hCount
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hsparse)) hCount

#print axioms squarePin_lower
#print axioms exists_squarePin_lower_of_count
#print axioms squarePin_nonconstant

end PvsNP.Frontier.Pinning
