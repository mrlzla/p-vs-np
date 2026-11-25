module

public import MCSPForestPinning
public import MCSPPermutedCut

/-! Two-bit separation and direct stop readers of affine-pinned MCSP. -/

@[expose] public section

namespace PvsNP.Frontier.PairSeparation

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open ForestPinning SuperTwoN MonotoneForest TwoCornerStructure
open CornerCertificates RestrictionCharges FreshCharges PermutedCut

variable {n g : ℕ}

/-- Pin one more coordinate, allowing either value while preserving the base mask. -/
def branchPin (x : BitString n) (P : Finset (Fin n)) (i : Fin n) (v : Bool) :
    Fin n → Fin n ⊕ Bool :=
  pinAt (Function.update x i v) (insert i P)

theorem branchPin_compose (x : BitString n) (P : Finset (Fin n)) (i : Fin n)
    (v : Bool) (hi : i ∉ P) :
    branchPin x P i v = compose (pinAt x P) (pinAt (Function.update x i v) {i}) := by
  funext j
  by_cases he : j = i
  · subst j
    simp [branchPin, compose, pinAt, hi]
  · by_cases hj : j ∈ P <;> simp [branchPin, compose, pinAt, hj, he]

private theorem essential_iff_update (f : BooleanFunction n) (j : Fin n) :
    EssentialAt f j ↔ ∃ y, f (Function.update y j false) ≠ f (Function.update y j true) := by
  constructor
  · rintro ⟨x, y, ha, hn⟩
    have he : Function.update x j (y j) = y := by
      funext u
      by_cases hu : u = j
      · subst u
        simp
      · simp [Function.update_of_ne hu, ha u hu]
    have hx : Function.update x j (x j) = x := Function.update_eq_self j x
    have hn' : f (Function.update x j (x j)) ≠ f (Function.update x j (y j)) := by
      rwa [hx, he]
    refine ⟨x, ?_⟩
    cases h1 : x j <;> cases h2 : y j <;> simp_all [Ne.symm]
  · rintro ⟨y, hy⟩
    exact ⟨_, _, fun u hu => by simp [Function.update_of_ne hu], hy⟩

/-- A fixed value at one free position can hide at most B other positions. -/
theorem affine_branch_inessential_bound (m : ℕ) (hm : 7 ≤ m)
    (a : BitString m) (b : Bool) (P : Finset (Fin (2 ^ m)))
    (i : Fin (2 ^ m)) (hi : i ∉ P)
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m) (v : Bool) :
    (((Finset.univ \ insert i P) : Finset (Fin (2 ^ m))) \
      essentialPositions (fun y => mcspSquare m
        (substitute (branchPin (MCSP.truthTable m (affine a b)) P i v) y))
        (Finset.univ \ insert i P)).card ≤ descriptionBitBound m := by
  classical
  obtain ⟨y, _, hAgree, hyi, _, hAccept, _⟩ :=
    mcspSquare_affine_pin_branches_nonconstant m hm a b P i hi hFree v
  let W : Finset (Fin (2 ^ m)) := Finset.univ \ insert i P
  have hEq (z : BitString (2 ^ m)) : restrictTable y W z =
      substitute (branchPin (MCSP.truthTable m (affine a b)) P i v) z := by
    funext j
    by_cases he : j = i
    · subst j
      simp [W, restrictTable, branchPin, substitute, pinAt, hyi]
    · by_cases hj : j ∈ P
      · simp [W, restrictTable, branchPin, substitute, pinAt, he, hj, (hAgree j hj).1]
      · simp [W, restrictTable, branchPin, substitute, pinAt, he, hj]
  have h := (pow_card_inessential_le (mcspSquare m) y W hAccept).trans
    (card_accepting_mcspSquare_le m)
  simp only [hEq] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

/-- For a fixed free position, both values retain a separating witness at
all but at most 2B other free positions. -/
theorem affine_two_bit_separation_except (m : ℕ) (hm : 7 ≤ m)
    (a : BitString m) (b : Bool) (P : Finset (Fin (2 ^ m)))
    (i : Fin (2 ^ m)) (hi : i ∉ P)
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m) :
    ∃ E ⊆ (Finset.univ \ insert i P : Finset (Fin (2 ^ m))),
      E.card ≤ 2 * descriptionBitBound m ∧
      ∀ j ∈ (Finset.univ \ insert i P) \ E, ∀ v : Bool,
        EssentialAt (fun y => mcspSquare m
          (substitute (branchPin (MCSP.truthTable m (affine a b)) P i v) y)) j := by
  classical
  let W : Finset (Fin (2 ^ m)) := Finset.univ \ insert i P
  let F (v : Bool) (y : BitString (2 ^ m)) :=
    mcspSquare m (substitute (branchPin (MCSP.truthTable m (affine a b)) P i v) y)
  let missing (v : Bool) := W \ essentialPositions (F v) W
  have hCap (v : Bool) : (missing v).card ≤ descriptionBitBound m :=
    affine_branch_inessential_bound m hm a b P i hi hFree v
  have hUnion := Finset.card_union_le (missing false) (missing true)
  have h₀ := hCap false
  have h₁ := hCap true
  refine ⟨missing false ∪ missing true,
    Finset.union_subset Finset.sdiff_subset Finset.sdiff_subset, by omega, ?_⟩
  intro j hj v
  obtain ⟨hW, hNot⟩ := Finset.mem_sdiff.mp hj
  have hMem : j ∈ essentialPositions (F v) W := by
    by_contra h
    have hMiss : j ∈ missing v := Finset.mem_sdiff.mpr ⟨hW, h⟩
    cases v
    · exact hNot (Finset.mem_union_left _ hMiss)
    · exact hNot (Finset.mem_union_right _ hMiss)
  exact (Finset.mem_filter.mp hMem).2

/-- An edge in each of the two rows of the Boolean square has a separation
witness. Any three branches contain a complete row, so they cannot coincide. -/
theorem no_three_equal_branches (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) (i j : Fin n)
    (h : ∀ v : Bool, EssentialAt (fun y => f (substitute (branchPin x P i v) y)) j) :
    ¬ ∃ a b : Bool, ∀ y,
      f (substitute (branchPin x P i (!a)) (Function.update y j b)) =
        f (substitute (branchPin x P i a) (Function.update y j (!b))) ∧
      f (substitute (branchPin x P i a) (Function.update y j (!b))) =
        f (substitute (branchPin x P i (!a)) (Function.update y j (!b))) := by
  rintro ⟨a, b, he⟩
  obtain ⟨y, hy⟩ := (essential_iff_update _ _).mp (h (!a))
  have hy' := (he y).1.trans (he y).2
  cases b
  · exact hy hy'
  · exact hy hy'.symm

/-- The forest mask remains valid after further pinning, if the old pins
are kept at their previous values. -/
private theorem extend_mask {p : Program signature n g} {root : Wire n g}
    {x y : BitString n} {P Q : Finset (Fin n)} (hMask : IsForestMask p root x P)
    (hPQ : P ⊆ Q) (hEq : ∀ i ∈ P, y i = x i) : IsForestMask p root y Q := by
  constructor
  · intro r hr
    rcases hMask.1 r hr with ⟨i, hi, hiP, hxi⟩ | hLeaf
    · exact Or.inl ⟨i, hi, hPQ hiP, (hEq i hiP).trans hxi⟩
    · exact Or.inr (hLeaf.trans hPQ)
  · intro r hr
    rcases hMask.2 r hr with ⟨i, hi, hiP, hxi⟩ | hLeaf
    · exact Or.inl ⟨i, hi, hPQ hiP, (hEq i hiP).trans hxi⟩
    · exact Or.inr (hLeaf.trans hPQ)

private theorem essential_before_branch (p : Program signature n g) (w : Wire n g)
    (x : BitString n) (P : Finset (Fin n)) {i j : Fin n} (hi : i ∉ P) 
    (v : Bool) (he : EssentialAt (restrictedWire p (branchPin x P i v) w) j) :
    EssentialAt (restrictedWire p (pinAt x P) w) j := by
  rw [branchPin_compose x P i v hi, restrictedWire_compose] at he
  obtain ⟨y, z, ha, hn⟩ := he
  let ρ := pinAt (Function.update x i v) ({i} : Finset (Fin n))
  refine ⟨substitute ρ y, substitute ρ z, ?_, hn⟩
  intro u hu
  by_cases hui : u = i
  · simp [ρ, substitute, pinAt, hui]
  · simp [ρ, substitute, pinAt, hui, ha u hu]

theorem fresh_reader_loss_of_mem (p : Program signature n g)
    (x : BitString n) (P Q : Finset (Fin n)) {j : Fin n} (hj : j ∉ P) (hjQ : j ∈ Q)
    {k : Fin g} (hf : k ∈ fresh p (pinAt x P))
    (hReads : ∃ a, (p.lines k).wires a = .input j) :
    k ∈ nextFreshLoss p (pinAt x P) (pinAt x Q) := by
  classical
  obtain ⟨a, ha⟩ := hReads
  have hArg : restrictedWire p (pinAt x P) ((p.lines k).wires a) = projection j := by
    rw [ha]
    funext y
    change substitute (pinAt x P) y j = y j
    simp [substitute, pinAt, hj]
  have hLoss := disclosed_of_pinned_projection p (pinAt x P) (pinAt x Q) k a j (x j)
    hArg (by simp [pinAt, hjQ])
  exact Finset.mem_sdiff.mpr ⟨hf, fun hu => (Finset.mem_filter.mp hu).2 hLoss⟩

private theorem fresh_reader_loss (p : Program signature n g)
    (x : BitString n) (P : Finset (Fin n)) {j : Fin n} (hj : j ∉ P)
    {k : Fin g} (hf : k ∈ fresh p (pinAt x P))
    (hReads : ∃ a, (p.lines k).wires a = .input j) :
    k ∈ nextFreshLoss p (pinAt x P) (pinAt x {j}) :=
  fresh_reader_loss_of_mem p x P {j} hj (by simp) hf hReads

/-- A branch in which one reader is insensitive and the output is sensitive
requires a distinct direct stop reader. The reader still depends on j before
the branch pin, and pinning j loses that original index if it was fresh. -/
theorem separated_branch_bypass {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} (hMask : IsForestMask p root x P)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {i j : Fin n} (hi : i ∉ P) (hj : j ∉ P)  (v : Bool) (skip : Fin g)
    (hEss : EssentialAt (restrictedWire p (branchPin x P i v) root) j)
    (hSkip : ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.gate skip)) j) :
    ∃ k ∈ StopGate p root, k ≠ skip ∧ (∃ a, (p.lines k).wires a = .input j) ∧
      EssentialAt (restrictedWire p (pinAt x P) (.gate k)) j ∧
      (k ∈ fresh p (pinAt x P) →
        k ∈ nextFreshLoss p (pinAt x P) (pinAt x {j})) := by
  classical
  have hExt := extend_mask hMask (Q := insert i P) (y := Function.update x i v)
    (fun _ ha => Finset.mem_insert_of_mem ha)
    (fun u hu => by
      have hne : u ≠ i := fun he => hi (he ▸ hu)
      simp [Function.update_of_ne hne])
  obtain ⟨k, hk, ⟨a, ha⟩, he⟩ := essential_stop_reader hExt h0 h1 hEss
  have hne : k ≠ skip := fun h => hSkip (h ▸ he)
  exact ⟨k, hk, hne, ⟨a, ha⟩, essential_before_branch p _ x P hi v he, fun hf =>
    fresh_reader_loss p x P hj hf ⟨a, ha⟩⟩

private theorem absorbed_eval (op : Op) (args : Fin (signature.Arity op) → Bool)
    (a : Fin (signature.Arity op)) (v : Bool)
    (hop : (op = .and ∧ v = false) ∨ (op = .or ∧ v = true)) (ha : args a = v) :
    interpretation op args = v := by
  have hIndex (t : Fin 2) : t = 0 ∨ t = 1 := by
    have ht := t.isLt
    have h : t.val = 0 ∨ t.val = 1 := by omega
    exact h.imp Fin.ext Fin.ext
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hIndex a with h | h <;> rw [h] at ha <;> simp [interpretation, ha]
  · rcases hIndex a with h | h <;> rw [h] at ha <;> simp [interpretation, ha]

/-- A controlling value makes every direct AND or OR reader constant,
irrespective of the values on its other argument. -/
theorem branch_absorbs_gate (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) (i : Fin n) (v : Bool) (k : Fin g)
    (hop : ((p.lines k).op = .and ∧ v = false) ∨
      ((p.lines k).op = .or ∧ v = true))
    (hReads : ∃ a, (p.lines k).wires a = .input i) :
    restrictedWire p (branchPin x P i v) (.gate k) = fun _ => v := by
  obtain ⟨a, ha⟩ := hReads
  funext y
  unfold restrictedWire
  rw [p.trace_gate]
  apply absorbed_eval (p.lines k).op _ a v hop
  rw [ha]
  change substitute (branchPin x P i v) y i = v
  simp [substitute, branchPin, pinAt]

/-- When the remaining varying stop readers are fresh, an absorbed joint
reader and its bypass charge two distinct original gates to the j pin. -/
theorem separated_two_fresh_stop_losses {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} (hMask : IsForestMask p root x P)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {i j : Fin n} (hi : i ∉ P) (hj : j ∉ P) (v : Bool) (k : Fin g)
    (hk : k ∈ StopGate p root) (hf : k ∈ fresh p (pinAt x P))
    (hop : ((p.lines k).op = .and ∧ v = false) ∨
      ((p.lines k).op = .or ∧ v = true))
    (hReadsI : ∃ a, (p.lines k).wires a = .input i)
    (hReadsJ : ∃ a, (p.lines k).wires a = .input j)
    (hEss : EssentialAt (restrictedWire p (branchPin x P i v) root) j)
    (hFresh : ∀ t ∈ StopGate p root, t ≠ k →
      (∃ a, (p.lines t).wires a = .input j) →
      EssentialAt (restrictedWire p (pinAt x P) (.gate t)) j → t ∈ fresh p (pinAt x P)) :
    2 ≤ (StopGate p root ∩ nextFreshLoss p (pinAt x P) (pinAt x {j})).card := by
  have hSkip : ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.gate k)) j := by
    rw [branch_absorbs_gate p x P i v k hop hReadsI]
    rintro ⟨_, _, _, hn⟩
    exact hn rfl
  obtain ⟨t, ht, hne, hReads, he, hLoss⟩ :=
    separated_branch_bypass hMask h0 h1 hi hj v k hEss hSkip
  exact Finset.one_lt_card.mpr ⟨t, Finset.mem_inter.mpr ⟨ht, hLoss (hFresh t ht hne hReads he)⟩,
    k, Finset.mem_inter.mpr ⟨hk, fresh_reader_loss p x P hj hf hReadsJ⟩, hne⟩

/-- A represented-variable swap can act as the transposition of just two
free truth-table entries while permuting the coordinates pinned to zero.
This blocks unconditional separation of 10 and 01 on all free pairs. -/
theorem zero_affine_mask_has_equal_mixed_branches (m : ℕ) :
    ∃ (P : Finset (Fin (2 ^ (m + 2)))) (i j : Fin (2 ^ (m + 2))),
      i ∉ P ∧ j ∉ P ∧ i ≠ j ∧
      2 ^ (m + 1) ≤ (Finset.univ \ P).card ∧
      ∀ z : BitString (2 ^ (m + 2)),
        mcspSquare (m + 2) (substitute (branchPin (fun _ => false) P i true)
          (Function.update z j false)) =
        mcspSquare (m + 2) (substitute (branchPin (fun _ => false) P i false)
          (Function.update z j true)) := by
  classical
  let a : Fin (m + 2) := 0
  let b : Fin (m + 2) := Fin.last (m + 1)
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    simp [a, b] at hv
  let e := Equiv.swap a b
  let t := tablePerm e
  let i := BitString.equivFin (m + 2) (fun k => decide (k = a))
  let j := BitString.equivFin (m + 2) (fun k => decide (k = b))
  have hi : t i = j := by
    change tablePerm e (BitString.equivFin _ _) = _
    rw [tablePerm_at_assignment]
    apply congrArg (BitString.equivFin (m + 2))
    funext k
    change decide (e k = a) = decide (k = b)
    have he : e b = a := by simp [e]
    simp [← he]
  have hj : t j = i := by
    change tablePerm e (BitString.equivFin _ _) = _
    rw [tablePerm_at_assignment]
    apply congrArg (BitString.equivFin (m + 2))
    funext k
    change decide (e k = b) = decide (k = a)
    have he : e a = b := by simp [e]
    simp [← he]
  have hij : i ≠ j := by
    intro h
    have hv := congrFun ((BitString.equivFin (m + 2)).injective h) a
    simp [hab] at hv
  let U : Finset (Fin (2 ^ (m + 2))) :=
    Finset.univ.filter fun k => t k = k ∨ k = i ∨ k = j
  let P : Finset (Fin (2 ^ (m + 2))) := Finset.univ \ U
  have hPchar (k : Fin (2 ^ (m + 2))) : k ∈ P ↔ t k ≠ k ∧ k ≠ i ∧ k ≠ j := by
    simp [P, U, not_or]
  have hiP : i ∉ P := by simp [hPchar]
  have hjP : j ∉ P := by simp [hPchar]
  have hStable (k : Fin (2 ^ (m + 2))) (hk : k ∈ P) : t k ∈ P := by
    obtain ⟨hmov, hki, hkj⟩ := (hPchar k).mp hk
    exact (hPchar (t k)).mpr
      ⟨fun h => hmov (t.injective h), fun h => hkj (t.injective (h.trans hj.symm)),
        fun h => hki (t.injective (h.trans hi.symm))⟩
  let dup (z : BitString (m + 1)) : BitString (m + 2) := Fin.snoc z (z 0)
  let fixed (z : BitString (m + 1)) := BitString.equivFin (m + 2) (dup z)
  have hFix (z : BitString (m + 1)) : t (fixed z) = fixed z := by
    change tablePerm e (BitString.equivFin _ _) = _
    rw [tablePerm_at_assignment]
    apply congrArg (BitString.equivFin (m + 2))
    have hz0 : dup z a = z 0 := by
      change dup z (0 : Fin (m + 1)).castSucc = _
      simp [dup]
    have hzLast : dup z b = z 0 := by simp [dup, b]
    funext k
    change dup z (e k) = _
    by_cases hk : k = a
    · subst k
      simp [e, hzLast, hz0]
    · by_cases hl : k = b
      · subst k
        simp [e, hzLast, hz0]
      · simp [e, Equiv.swap_apply_of_ne_of_ne hk hl]
  let into (z : BitString (m + 1)) : (Finset.univ \ P : Finset (Fin (2 ^ (m + 2)))) :=
    ⟨fixed z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (hPchar _).mp h |>.1 (hFix z)⟩⟩
  have hInj : Function.Injective into := by
    intro y z h
    have hv := (BitString.equivFin (m + 2)).injective (congrArg Subtype.val h)
    funext k
    simpa [dup] using congrFun hv k.castSucc
  have hSize := Fintype.card_le_of_injective into hInj
  have hFree : 2 ^ (m + 1) ≤ (Finset.univ \ P).card := by
    simpa only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_coe] using hSize
  refine ⟨P, i, j, hiP, hjP, hij, hFree, ?_⟩
  intro z
  let T (u v : Bool) := substitute (branchPin (fun _ => false) P i u) (Function.update z j v)
  have hShift : T true false ∘ t = T false true := by
    funext k
    change T true false (t k) = T false true k
    by_cases hki : k = i
    · subst k
      simp [T, hi, branchPin, pinAt, hiP, hjP, hij.symm]
    · by_cases hkj : k = j
      · subst k
        simp [T, hj, branchPin, pinAt, hiP, hjP, hij.symm]
      · by_cases hk : k ∈ P
        · have htk := hStable k hk
          have htki : t k ≠ i := fun h => hiP (h ▸ htk)
          simp [T, branchPin, pinAt, hk, htk, hki, htki]
        · have hFixK : t k = k := by
            by_contra h
            exact hk ((hPchar _).mpr ⟨h, hki, hkj⟩)
          simp [T, hFixK, branchPin, pinAt, hk, hki, hkj]
  have he := square_comp_tablePerm e (T true false)
  change mcspSquare (m + 2) (T true false ∘ t) = _ at he
  rw [hShift] at he
  exact he.symm

/-- A fresh stop gate reading two free entries has a precise alternative.
Outside the exceptional partners, pinning the second entry loses at least two
original stop gates or there is a distinct, already redundant varying reader. -/
theorem affine_pair_stop_loss_test (m : ℕ) (hm : 7 ≤ m)
    (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (a : BitString m) (b : Bool) (P : Finset (Fin (2 ^ m)))
    (hMask : IsForestMask c.program (c.outputs 0) (MCSP.truthTable m (affine a b)) P)
    (i : Fin (2 ^ m)) (hi : i ∉ P)
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m) :
    let x := MCSP.truthTable m (affine a b)
    let p := c.program
    let root := c.outputs 0
    ∃ E ⊆ (Finset.univ \ insert i P : Finset (Fin (2 ^ m))),
      E.card ≤ 2 * descriptionBitBound m ∧
      ∀ j ∈ (Finset.univ \ insert i P) \ E, ∀ k ∈ StopGate p root,
        k ∈ fresh p (pinAt x P) →
        ((p.lines k).op = .and ∨ (p.lines k).op = .or) →
        (∃ s, (p.lines k).wires s = .input i) →
        (∃ s, (p.lines k).wires s = .input j) →
        (2 ≤ (StopGate p root ∩ nextFreshLoss p (pinAt x P) (pinAt x {j})).card) ∨
        ∃ t ∈ StopGate p root, t ≠ k ∧ (∃ s, (p.lines t).wires s = .input j) ∧
          EssentialAt (restrictedWire p (pinAt x P) (.gate t)) j ∧
          t ∉ fresh p (pinAt x P) := by
  classical
  dsimp only
  obtain ⟨E, hE, hCard, hSep⟩ := affine_two_bit_separation_except m hm a b P i hi hFree
  refine ⟨E, hE, hCard, ?_⟩
  intro j hj k hk hFresh hOp hReadsI hReadsJ
  by_cases hAlias : ∃ t ∈ StopGate c.program (c.outputs 0), t ≠ k ∧
      (∃ s, (c.program.lines t).wires s = .input j) ∧
      EssentialAt (restrictedWire c.program (pinAt (MCSP.truthTable m (affine a b)) P)
        (.gate t)) j ∧ t ∉ fresh c.program (pinAt (MCSP.truthTable m (affine a b)) P)
  · exact Or.inr hAlias
  · left
    have hjP : j ∉ P := fun h => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).2
      (Finset.mem_insert_of_mem h)
    obtain ⟨v, hop⟩ : ∃ v : Bool, ((c.program.lines k).op = .and ∧ v = false) ∨
        ((c.program.lines k).op = .or ∧ v = true) := by
      rcases hOp with ha | ho
      · exact ⟨false, Or.inl ⟨ha, rfl⟩⟩
      · exact ⟨true, Or.inr ⟨ho, rfl⟩⟩
    have h0 : cornerValue c.program false (c.outputs 0) = true :=
      (congrFun (hc _) 0).trans (mcspSquare_constant_table m (by omega) false)
    have h1 : cornerValue c.program true (c.outputs 0) = true :=
      (congrFun (hc _) 0).trans (mcspSquare_constant_table m (by omega) true)
    have hOut : EssentialAt (restrictedWire c.program
        (branchPin (MCSP.truthTable m (affine a b)) P i v) (c.outputs 0)) j := by
      rw [NestedFaces.restricted_circuit_eq c hc]
      exact hSep j hj v
    exact separated_two_fresh_stop_losses hMask h0 h1 hi hjP v k hk hFresh hop hReadsI
      hReadsJ hOut (fun t ht hne hReads he => by
        by_contra hn
        exact hAlias ⟨t, ht, hne, hReads, he, hn⟩)

#print axioms affine_two_bit_separation_except
#print axioms no_three_equal_branches
#print axioms separated_branch_bypass
#print axioms affine_pair_stop_loss_test
#print axioms separated_two_fresh_stop_losses
#print axioms zero_affine_mask_has_equal_mixed_branches

end PvsNP.Frontier.PairSeparation
