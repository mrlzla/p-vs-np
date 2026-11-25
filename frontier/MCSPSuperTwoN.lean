module

public import MCSPMonotoneForest
public import Complexity.Computability.Circuit.Boolean.Synthesis

/-! Unconditional super-`2N` De Morgan circuit size lower bounds for `mcspSquare m` and
for sparse circuits accepting all `RefinedProbeControl.pattern p` truth tables, deduced from
the monotone OR/AND forest decomposition in `MCSPMonotoneForest.lean`. -/

@[expose] public section

namespace PvsNP.Frontier.SuperTwoN

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open WireAccounting CornerCertificates TwoCornerStructure MonotoneForest

/-! ### Masked truth-table counting bound -/

/-- If fixing a coordinate subset `Mask` to match `x` forces a sparse function `f`
(with at most `2 ^ B` accepting tables) to output `true`, then `n ≤ Mask.card + B`. -/
theorem card_masked_le {n B : ℕ} {f : BooleanFunction n}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (x : BitString n) (Mask : Finset (Fin n))
    (hAccept : ∀ y : BitString n, (∀ i ∈ Mask, y i = x i) → f y = true) :
    n ≤ Mask.card + B := by
  classical
  let outside : Finset (Fin n) := Finset.univ \ Mask
  let table (bits : (i : outside) → Bool) : BitString n :=
    fun i => if h : i ∈ outside then bits ⟨i, h⟩ else x i
  have hTableAccept (bits : (i : outside) → Bool) : table bits ∈ acceptingTables f := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAccept (table bits) fun i hi => ?_⟩
    have hNotOut : i ∉ outside := fun hOut => (Finset.mem_sdiff.mp hOut).2 hi
    simp [table, hNotOut]
  let into (bits : (i : outside) → Bool) : acceptingTables f := ⟨table bits, hTableAccept bits⟩
  have hInj : Function.Injective into := by
    intro a b hEq
    funext i
    have hi := congrFun (congrArg Subtype.val hEq) i.val
    simpa [into, table, i.property] using hi
  have hPow : 2 ^ outside.card ≤ (acceptingTables f).card := by
    simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using
      Fintype.card_le_of_injective into hInj
  have hOutLe : outside.card ≤ B :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hPow.trans hSparse)
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Mask)
  dsimp only [outside] at hOutLe
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  omega

/-! ### Affine Boolean functions and their De Morgan circuit complexity -/

/-- Inner product over `GF(2)` defined recursively on the dimension `m`. -/
def dot : {m : ℕ} → BitString m → BitString m → Bool
  | 0, _, _ => false
  | _ + 1, a, z => (a 0 && z 0) ^^ dot (Fin.tail a) (Fin.tail z)

/-- Affine Boolean function `z ↦ b0 ^^ dot a z`. -/
def affine {m : ℕ} (a : BitString m) (b0 : Bool) (z : BitString m) : Bool :=
  b0 ^^ dot a z

private theorem bool_xor_left_comm (x y z : Bool) : (x ^^ (y ^^ z)) = (y ^^ (x ^^ z)) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem bool_xor_assoc (x y z : Bool) : ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem bool_xor_cancel_right {x y z : Bool} (h : (x ^^ z) = (y ^^ z)) : x = y := by
  revert h; cases x <;> cases y <;> cases z <;> decide

private theorem bool_xor_cancel_left {x y z : Bool} (h : (z ^^ x) = (z ^^ y)) : x = y := by
  revert h; cases x <;> cases y <;> cases z <;> decide

private theorem bool_xor_eq_iff {x y z : Bool} : (x ^^ y) = z ↔ x = (z ^^ y) := by
  cases x <;> cases y <;> cases z <;> decide

private theorem affine_succ {m : ℕ} (a : BitString (m + 1)) (b0 : Bool) (z : BitString (m + 1)) :
    affine a b0 z = ((a 0 && z 0) ^^ affine (Fin.tail a) b0 (Fin.tail z)) :=
  bool_xor_left_comm b0 (a 0 && z 0) (dot (Fin.tail a) (Fin.tail z))

private theorem affine_cons {m : ℕ} (a : BitString (m + 1)) (b0 : Bool)
    (bit : Bool) (z' : BitString m) :
    affine a b0 (Fin.cons bit z') = affine (Fin.tail a) (b0 ^^ (a 0 && bit)) z' :=
  (bool_xor_assoc b0 (a 0 && bit) (dot (Fin.tail a) z')).symm

private theorem synthesis_affine_comp {n : ℕ} {s : Set (BooleanFunction n)} :
    ∀ {m : ℕ} (a : BitString m) (b0 : Bool) (vars : Fin m → BooleanFunction n),
      (∀ i : Fin m, vars i ∈ s) →
      Synthesis interpretation s {fun x => affine a b0 (fun i => vars i x)} (4 * m + 1)
  | 0, a, b0, vars, _ => by
    have hEq : (fun x : BitString n => affine a b0 (fun i => vars i x)) = fun _ => b0 := by
      funext x
      unfold affine dot
      cases b0 <;> rfl
    rw [hEq]
    exact Synthesis.const b0
  | m + 1, a, b0, vars, hvars => by
    have ih := synthesis_affine_comp (Fin.tail a) b0 (fun i : Fin m => vars i.succ)
      (fun i => hvars i.succ)
    cases ha0 : a 0 with
    | false =>
      have hEq : (fun x : BitString n => affine a b0 (fun i => vars i x)) =
          fun x => affine (Fin.tail a) b0 (fun i => vars i.succ x) := by
        funext x
        rw [affine_succ, ha0]
        simp
        rfl
      rw [hEq]
      exact ih.mono Set.Subset.rfl Set.Subset.rfl (by omega)
    | true =>
      have h0 : Synthesis interpretation s {vars 0} 0 := Synthesis.of_mem (hvars 0)
      have hXor := h0.xor ih
      have hEq : (fun x : BitString n => vars 0 x ^^ affine (Fin.tail a) b0 (fun i => vars i.succ x)) =
          fun x => affine a b0 (fun i => vars i x) := by
        funext x
        rw [affine_succ, ha0]
        simp
        rfl
      rw [hEq] at hXor
      exact hXor.mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- Every `m`-variable affine Boolean function has De Morgan circuit complexity at most `4m + 1`. -/
theorem complexity_affine_le {m : ℕ} (a : BitString m) (b0 : Bool) :
    complexity interpretation (single (affine a b0)) ≤ 4 * m + 1 := by
  have h := synthesis_affine_comp (n := m) (s := inputs m) a b0 (fun i x => x i)
    (fun i => ⟨i, rfl⟩)
  exact h.complexity_le

/-- For `m ≥ 5`, every affine truth table is accepted by `mcspSquare m` (since `4m + 1 ≤ m^2`). -/
theorem mcspSquare_accepts_affine (m : ℕ) (hm : 5 ≤ m) (a : BitString m) (b0 : Bool) :
    mcspSquare m (MCSP.truthTable m (affine a b0)) = true := by
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  exact (complexity_affine_le a b0).trans (by nlinarith)

/-! ### Affine orthogonality / vanishing bound -/

/-- The set of affine parameters `(a, b0)` that are identically equal to `target` on `U`. -/
noncomputable def constAffines {m : ℕ} (U : Finset (BitString m)) (target : Bool) :
    Finset (BitString m × Bool) :=
  Finset.univ.filter fun ab => ∀ z ∈ U, affine ab.1 ab.2 z = target

/-- For any subset `U ⊆ {0,1}^m` and `target : Bool`, the number of affine functions
constant with value `target` on `U` satisfies `|constAffines U target| * |U| ≤ 2 ^ m`. -/
theorem card_affine_const_le : ∀ {m : ℕ} (U : Finset (BitString m)) (target : Bool),
    (constAffines U target).card * U.card ≤ 2 ^ m
  | 0, U, target => by
    classical
    by_cases hU : U.Nonempty
    · obtain ⟨z0, hz0⟩ := hU
      have hUCard : U.card ≤ 1 := by
        have h1 : (Finset.univ : Finset (BitString 0)).card = 1 := by
          simp [BitString]
        exact (Finset.card_le_univ U).trans h1.le
      have hACard : (constAffines U target).card ≤ 1 := by
        refine Finset.card_le_one.mpr fun ab1 h1 ab2 h2 => ?_
        have ha : ab1.1 = ab2.1 := funext fun i => Fin.elim0 i
        have hb1 : affine ab1.1 ab1.2 z0 = target := (Finset.mem_filter.mp h1).2 z0 hz0
        have hb2 : affine ab2.1 ab2.2 z0 = target := (Finset.mem_filter.mp h2).2 z0 hz0
        have hb1' : ab1.2 = target := by simpa [affine, dot] using hb1
        have hb2' : ab2.2 = target := by simpa [affine, dot] using hb2
        exact Prod.ext ha (hb1'.trans hb2'.symm)
      exact (Nat.mul_le_mul hACard hUCard).trans (by decide)
    · have hEmpty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      simp [hEmpty]
  | m + 1, U, target => by
    classical
    let U0 : Finset (BitString m) := Finset.univ.filter fun z' => Fin.cons false z' ∈ U
    let U1 : Finset (BitString m) := Finset.univ.filter fun z' => Fin.cons true z' ∈ U
    let ins0 : BitString m → BitString (m + 1) := fun z' => Fin.cons false z'
    let ins1 : BitString m → BitString (m + 1) := fun z' => Fin.cons true z'
    have hUCard : U.card ≤ U0.card + U1.card := by
      have hSub : U ⊆ U0.image ins0 ∪ U1.image ins1 := by
        intro z hz
        have hCons : Fin.cons (z 0) (Fin.tail z) = z := Fin.cons_self_tail z
        cases hz0 : z 0 with
        | false =>
          apply Finset.mem_union_left
          refine Finset.mem_image.mpr ⟨Fin.tail z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rwa [← hz0, hCons]
          · dsimp only [ins0]; rw [← hz0, hCons]
        | true =>
          apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨Fin.tail z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rwa [← hz0, hCons]
          · dsimp only [ins1]; rw [← hz0, hCons]
      have h1 := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
      have h2 : (U0.image ins0).card ≤ U0.card := Finset.card_image_le
      have h3 : (U1.image ins1).card ≤ U1.card := Finset.card_image_le
      omega
    let proj0 (ab : BitString (m + 1) × Bool) : BitString m × Bool := (Fin.tail ab.1, ab.2)
    let proj1 (ab : BitString (m + 1) × Bool) : BitString m × Bool := (Fin.tail ab.1, ab.2 ^^ ab.1 0)
    have hMaps0 : ∀ ab ∈ constAffines U target, proj0 ab ∈ constAffines U0 target := by
      intro ab hab
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z' hz' => ?_⟩
      have hzU : Fin.cons false z' ∈ U := (Finset.mem_filter.mp hz').2
      have hVal := (Finset.mem_filter.mp hab).2 (Fin.cons false z') hzU
      rw [affine_cons] at hVal
      simpa [proj0] using hVal
    have hMaps1 : ∀ ab ∈ constAffines U target, proj1 ab ∈ constAffines U1 target := by
      intro ab hab
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z' hz' => ?_⟩
      have hzU : Fin.cons true z' ∈ U := (Finset.mem_filter.mp hz').2
      have hVal := (Finset.mem_filter.mp hab).2 (Fin.cons true z') hzU
      rw [affine_cons] at hVal
      simpa [proj1] using hVal
    have hLeTwo0 : (constAffines U target).card ≤ 2 * (constAffines U0 target).card := by
      let f0 (ab : BitString (m + 1) × Bool) : Bool × (BitString m × Bool) := (ab.1 0, proj0 ab)
      have hMap : ∀ ab ∈ constAffines U target,
          f0 ab ∈ (Finset.univ : Finset Bool) ×ˢ constAffines U0 target :=
        fun ab hab => Finset.mem_product.mpr ⟨Finset.mem_univ _, hMaps0 ab hab⟩
      have hInj : Set.InjOn f0 (constAffines U target) := by
        intro ab1 _ ab2 _ hEq
        have hBit : ab1.1 0 = ab2.1 0 := congrArg Prod.fst hEq
        have hTail : Fin.tail ab1.1 = Fin.tail ab2.1 := congrArg (fun p => p.2.1) hEq
        have hB : ab1.2 = ab2.2 := congrArg (fun p => p.2.2) hEq
        have hA : ab1.1 = ab2.1 := by
          rw [← Fin.cons_self_tail ab1.1, ← Fin.cons_self_tail ab2.1, hBit, hTail]
        exact Prod.ext hA hB
      have hCard := Finset.card_le_card_of_injOn f0 hMap hInj
      simpa [Finset.card_product] using hCard
    have hLeTwo1 : (constAffines U target).card ≤ 2 * (constAffines U1 target).card := by
      let f1 (ab : BitString (m + 1) × Bool) : Bool × (BitString m × Bool) := (ab.1 0, proj1 ab)
      have hMap : ∀ ab ∈ constAffines U target,
          f1 ab ∈ (Finset.univ : Finset Bool) ×ˢ constAffines U1 target :=
        fun ab hab => Finset.mem_product.mpr ⟨Finset.mem_univ _, hMaps1 ab hab⟩
      have hInj : Set.InjOn f1 (constAffines U target) := by
        intro ab1 _ ab2 _ hEq
        have hBit : ab1.1 0 = ab2.1 0 := congrArg Prod.fst hEq
        have hTail : Fin.tail ab1.1 = Fin.tail ab2.1 := congrArg (fun p => p.2.1) hEq
        have hBXor : (ab1.2 ^^ ab1.1 0) = (ab2.2 ^^ ab2.1 0) := congrArg (fun p => p.2.2) hEq
        rw [hBit] at hBXor
        have hB : ab1.2 = ab2.2 := bool_xor_cancel_right hBXor
        have hA : ab1.1 = ab2.1 := by
          rw [← Fin.cons_self_tail ab1.1, ← Fin.cons_self_tail ab2.1, hBit, hTail]
        exact Prod.ext hA hB
      have hCard := Finset.card_le_card_of_injOn f1 hMap hInj
      simpa [Finset.card_product] using hCard
    have ih0 := card_affine_const_le U0 target
    have ih1 := card_affine_const_le U1 target
    by_cases hU0 : U0.Nonempty <;> by_cases hU1 : U1.Nonempty
    · obtain ⟨z0, hz0⟩ := hU0
      obtain ⟨z1, hz1⟩ := hU1
      have hLe0 : (constAffines U target).card ≤ (constAffines U0 target).card := by
        refine Finset.card_le_card_of_injOn proj0 hMaps0 ?_
        intro ab1 hab1 ab2 hab2 hEq
        have hTail : Fin.tail ab1.1 = Fin.tail ab2.1 := congrArg Prod.fst hEq
        have hB : ab1.2 = ab2.2 := congrArg (fun p : BitString m × Bool => p.2) hEq
        have hz1U : Fin.cons true z1 ∈ U := (Finset.mem_filter.mp hz1).2
        have hV1 := (Finset.mem_filter.mp hab1).2 (Fin.cons true z1) hz1U
        have hV2 := (Finset.mem_filter.mp hab2).2 (Fin.cons true z1) hz1U
        rw [affine_cons] at hV1 hV2
        have hComb : affine (Fin.tail ab1.1) (ab1.2 ^^ (ab1.1 0 && true)) z1 =
            affine (Fin.tail ab1.1) (ab1.2 ^^ (ab2.1 0 && true)) z1 := by
          rw [hV1, ← hV2, hTail, hB]
        have hX : (ab1.2 ^^ (ab1.1 0 && true)) = (ab1.2 ^^ (ab2.1 0 && true)) :=
          bool_xor_cancel_right hComb
        have hBit : ab1.1 0 = ab2.1 0 := by
          simpa using bool_xor_cancel_left hX
        have hA : ab1.1 = ab2.1 := by
          rw [← Fin.cons_self_tail ab1.1, ← Fin.cons_self_tail ab2.1, hBit, hTail]
        exact Prod.ext hA hB
      have hLe1 : (constAffines U target).card ≤ (constAffines U1 target).card := by
        refine Finset.card_le_card_of_injOn proj1 hMaps1 ?_
        intro ab1 hab1 ab2 hab2 hEq
        have hTail : Fin.tail ab1.1 = Fin.tail ab2.1 := congrArg Prod.fst hEq
        have hBXor : (ab1.2 ^^ ab1.1 0) = (ab2.2 ^^ ab2.1 0) :=
          congrArg (fun p : BitString m × Bool => p.2) hEq
        have hz0U : Fin.cons false z0 ∈ U := (Finset.mem_filter.mp hz0).2
        have hV1 := (Finset.mem_filter.mp hab1).2 (Fin.cons false z0) hz0U
        have hV2 := (Finset.mem_filter.mp hab2).2 (Fin.cons false z0) hz0U
        rw [affine_cons] at hV1 hV2
        have hComb : affine (Fin.tail ab1.1) (ab1.2 ^^ (ab1.1 0 && false)) z0 =
            affine (Fin.tail ab1.1) (ab2.2 ^^ (ab2.1 0 && false)) z0 := by
          rw [hV1, ← hV2, hTail]
        have hB : ab1.2 = ab2.2 := by
          simpa using bool_xor_cancel_right hComb
        rw [hB] at hBXor
        have hBit : ab1.1 0 = ab2.1 0 := bool_xor_cancel_left hBXor
        have hA : ab1.1 = ab2.1 := by
          rw [← Fin.cons_self_tail ab1.1, ← Fin.cons_self_tail ab2.1, hBit, hTail]
        exact Prod.ext hA hB
      have hM0 : (constAffines U target).card * U0.card ≤ 2 ^ m :=
        (Nat.mul_le_mul_right U0.card hLe0).trans ih0
      have hM1 : (constAffines U target).card * U1.card ≤ 2 ^ m :=
        (Nat.mul_le_mul_right U1.card hLe1).trans ih1
      have hMul := Nat.mul_le_mul_left (constAffines U target).card hUCard
      rw [Nat.mul_add] at hMul
      rw [Nat.pow_succ]
      omega
    · have hU1Empty : U1.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU1)
      have hULe0 : U.card ≤ U0.card := by omega
      have hMul : (constAffines U target).card * U.card ≤
          2 * ((constAffines U0 target).card * U0.card) := by
        calc
          (constAffines U target).card * U.card ≤
              (2 * (constAffines U0 target).card) * U0.card := Nat.mul_le_mul hLeTwo0 hULe0
          _ = 2 * ((constAffines U0 target).card * U0.card) := Nat.mul_assoc 2 _ _
      rw [Nat.pow_succ]
      omega
    · have hU0Empty : U0.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU0)
      have hULe1 : U.card ≤ U1.card := by omega
      have hMul : (constAffines U target).card * U.card ≤
          2 * ((constAffines U1 target).card * U1.card) := by
        calc
          (constAffines U target).card * U.card ≤
              (2 * (constAffines U1 target).card) * U1.card := Nat.mul_le_mul hLeTwo1 hULe1
          _ = 2 * ((constAffines U1 target).card * U1.card) := Nat.mul_assoc 2 _ _
      rw [Nat.pow_succ]
      omega
    · have hU0Empty : U0.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU0)
      have hU1Empty : U1.card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hU1)
      have hUEmpty : U.card = 0 := by omega
      simp [hUEmpty]

/-! ### Two-Corner Bottleneck Fooling Bound (inspired by Schlesinger's `Frontier/Ledger`) -/

/-- Any fooling set `S : Finset (BitString n)` whose elements are pairwise separated by the
Two-Corner Bottleneck (`cutInputs`, `ORRoot` traces, `ANDRoot` traces) has cardinality at most
`2 ^ (cutInputs.card + ORRoot.card + ANDRoot.card) ≤ 2 ^ (10 * B + 1559 * slack)`. -/
theorem bottleneck_fooling_card_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (S : Finset (BitString n))
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (∃ i ∈ cutInputs c.program (c.outputs 0), x i ≠ y i) ∨
      (∃ r ∈ ORRoot c.program (c.outputs 0),
        c.program.trace interpretation x (.gate r) ≠ c.program.trace interpretation y (.gate r)) ∨
      (∃ r' ∈ ANDRoot c.program (c.outputs 0),
        c.program.trace interpretation x (.gate r') ≠ c.program.trace interpretation y (.gate r'))) :
    S.card ≤ 2 ^ (10 * B + 1559 * slack c.program (c.outputs 0)) := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let C_in := cutInputs p root
  let T_OR := ORRoot p root
  let T_AND := ANDRoot p root
  let ledger (x : BitString n) :
      (C_in → Bool) × (T_OR → Bool) × (T_AND → Bool) :=
    (fun i => x i.1,
     fun r => p.trace interpretation x (.gate r.1),
     fun r' => p.trace interpretation x (.gate r'.1))
  have hInj : Set.InjOn ledger (S : Set (BitString n)) := by
    intro x hx y hy hEq
    by_contra hne
    have hEq1 := congrArg Prod.fst hEq
    have hEq2 := congrArg (fun q => q.2.1) hEq
    have hEq3 := congrArg (fun q => q.2.2) hEq
    rcases hSep x hx y hy hne with ⟨i, hi, hneI⟩ | ⟨r, hr, hneR⟩ | ⟨r', hr', hneR'⟩
    · exact hneI (congrFun hEq1 ⟨i, hi⟩)
    · exact hneR (congrFun hEq2 ⟨r, hr⟩)
    · exact hneR' (congrFun hEq3 ⟨r', hr'⟩)
  have hCardImg : (S.image ledger).card = S.card := Finset.card_image_of_injOn hInj
  have hLeUniv : (S.image ledger).card ≤
      Fintype.card ((C_in → Bool) × (T_OR → Bool) × (T_AND → Bool)) :=
    Finset.card_le_univ _
  rw [hCardImg] at hLeUniv
  simp only [Fintype.card_prod, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe] at hLeUniv
  have hPow : 2 ^ C_in.card * (2 ^ T_OR.card * 2 ^ T_AND.card) =
      2 ^ (C_in.card + (T_OR.card + T_AND.card)) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
  rw [hPow] at hLeUniv
  have hCutLe : C_in.card ≤ 117 * slack p root := card_cutInputs_le_slack p root h0 h1
  have hRootsLe : T_OR.card + T_AND.card ≤ 10 * B + 1442 * slack p root :=
    card_orRoot_add_andRoot_le c hc hSparse hf0 hf1
  dsimp only [p, root] at hCutLe hRootsLe ⊢
  exact hLeUniv.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-! ### Slack and gate-count lower bounds via affine probes (`mcspSquare_super_twoN`) -/

/-- Averaging the extra pins beyond the first over all affine probes.
The bound on the number of extra pins uses the integrality of the leaf count. -/
private theorem affine_mask_extra_le {m : ℕ} (U : Finset (BitString m)) (b : Bool) :
    (∑ ab : BitString m × Bool, 12 * (if ab ∈ constAffines U b then U.card - 1 else 0)) ≤
      (U.card + 1) * (2 ^ m * 2) := by
  classical
  rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, smul_eq_mul]
  have hQuad : 12 * (U.card - 1) ≤ 2 * (U.card + 1) * U.card := by
    cases U.card with
    | zero => simp
    | succ k =>
      simp only [Nat.succ_sub_one]
      zify
      by_cases hk : (k : ℤ) ≤ 1
      · nlinarith [mul_nonneg (show 0 ≤ 1 - (k : ℤ) by omega)
          (show 0 ≤ 2 - (k : ℤ) by omega)]
      · nlinarith [mul_nonneg (show 0 ≤ (k : ℤ) - 1 by omega)
          (show 0 ≤ (k : ℤ) - 2 by omega)]
  calc
    _ = 12 * (U.card - 1) * (constAffines U b).card := by ring
    _ ≤ (2 * (U.card + 1) * U.card) * (constAffines U b).card := Nat.mul_le_mul_right _ hQuad
    _ = (2 * (U.card + 1)) * ((constAffines U b).card * U.card) := by ring
    _ ≤ (2 * (U.card + 1)) * 2 ^ m := Nat.mul_le_mul_left _ (card_affine_const_le U b)
    _ = _ := by ring

private def xorThree {m : ℕ} (x y z : BitString m) : BitString m :=
  fun i => x i ^^ (y i ^^ z i)

private theorem affine_xorThree {m : ℕ} (a : BitString m) (b : Bool) (x y z : BitString m) :
    affine a b (xorThree x y z) = (affine a b x ^^ (affine a b y ^^ affine a b z)) := by
  induction m with
  | zero => cases b <;> rfl
  | succ m ih =>
    simp only [affine_succ (m := m)]
    change ((a 0 && (x 0 ^^ (y 0 ^^ z 0))) ^^
      affine (Fin.tail a) b (xorThree (Fin.tail x) (Fin.tail y) (Fin.tail z))) = _
    rw [ih]
    generalize a 0 = v
    generalize x 0 = x₀
    generalize y 0 = y₀
    generalize z 0 = z₀
    generalize affine (Fin.tail a) b (Fin.tail x) = x₁
    generalize affine (Fin.tail a) b (Fin.tail y) = y₁
    generalize affine (Fin.tail a) b (Fin.tail z) = z₁
    cases v <;> cases x₀ <;> cases y₀ <;> cases z₀ <;> cases x₁ <;> cases y₁ <;> cases z₁ <;> decide

private theorem card_three_affine_const {m : ℕ} (U : Finset (BitString m)) (b : Bool)
    (hU : U.card = 3) : (constAffines U b).card * 4 ≤ 2 ^ m := by
  classical
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (by omega : 2 < U.card)
  let w := xorThree x y z
  have hw_bit (x y z : Bool) :
      ((x ^^ (y ^^ z)) = x → y = z) ∧ ((x ^^ (y ^^ z)) = y → x = z) ∧
      ((x ^^ (y ^^ z)) = z → x = y) := by
    cases x <;> cases y <;> cases z <;> decide
  have hwx : w ≠ x := fun h => hyz (funext fun i => (hw_bit (x i) (y i) (z i)).1 (congrFun h i))
  have hwy : w ≠ y := fun h => hxz (funext fun i => (hw_bit (x i) (y i) (z i)).2.1 (congrFun h i))
  have hwz : w ≠ z := fun h => hxy (funext fun i => (hw_bit (x i) (y i) (z i)).2.2 (congrFun h i))
  have hEq : U = {x, y, z} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hv : v = x ∨ v = y ∨ v = z)
        with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    · rw [hU]
      simp [Finset.card_insert_of_notMem, hxy, hxz, hyz]
  have hw : w ∉ U := by simp [hEq, hwx, hwy, hwz]
  have hCard : (insert w U).card = 4 := by
    rw [Finset.card_insert_of_notMem hw, hU]
  have hSub : constAffines U b ⊆ constAffines (insert w U) b := by
    intro ab hab
    have hOn := (Finset.mem_filter.mp hab).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · change affine ab.1 ab.2 (xorThree x y z) = b
      rw [affine_xorThree, hOn x hx, hOn y hy, hOn z hz]
      cases b <;> rfl
    · exact hOn i hi
  have h := card_affine_const_le (insert w U) b
  rw [hCard] at h
  exact (Nat.mul_le_mul_right 4 (Finset.card_le_card hSub)).trans h

/-- Three distinct leaves supply a fourth affine constraint. This gives a
stronger uniform estimate for the extra pins of a forest component. -/
private theorem affine_mask_extra_tight {m : ℕ} (U : Finset (BitString m)) (b : Bool) :
    (∑ ab : BitString m × Bool, 16 * (if ab ∈ constAffines U b then U.card - 1 else 0)) ≤
      (U.card + 2) * (2 ^ m * 2) := by
  classical
  rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, smul_eq_mul]
  by_cases hThree : U.card = 3
  · have h := card_three_affine_const U b hThree
    rw [hThree]
    omega
  · have hQuad : 16 * (U.card - 1) ≤ 2 * (U.card + 2) * U.card := by
      cases he : U.card with
      | zero => decide
      | succ k =>
        have hk : k ≠ 2 := by omega
        simp only [Nat.succ_sub_one]
        zify
        by_cases h : (k : ℤ) ≤ 1
        · nlinarith [mul_nonneg (show 0 ≤ 1 - (k : ℤ) by omega)
            (show 0 ≤ 3 - (k : ℤ) by omega)]
        · nlinarith [mul_nonneg (show 0 ≤ (k : ℤ) - 1 by omega)
            (show 0 ≤ (k : ℤ) - 3 by omega)]
    calc
      _ = 16 * (U.card - 1) * (constAffines U b).card := by ring
      _ ≤ (2 * (U.card + 2) * U.card) * (constAffines U b).card := Nat.mul_le_mul_right _ hQuad
      _ = (2 * (U.card + 2)) * ((constAffines U b).card * U.card) := by ring
      _ ≤ (2 * (U.card + 2)) * 2 ^ m := Nat.mul_le_mul_left _ (card_affine_const_le U b)
      _ = _ := by ring

/-- Each forest root has either an absorbing witness or all of its direct
input leaves fixed to the reference table. -/
def IsForestMask {g : ℕ} (p : Program signature n g) (root : Wire n g)
    (x : BitString n) (P : Finset (Fin n)) : Prop :=
  (∀ r ∈ ORRoot p root,
    (∃ i ∈ orInputs p root r, i ∈ P ∧ x i = true) ∨ orInputs p root r ⊆ P) ∧
  (∀ r ∈ ANDRoot p root,
    (∃ i ∈ andInputs p root r, i ∈ P ∧ x i = false) ∨ andInputs p root r ⊆ P)

theorem IsForestMask.trace_eq {g : ℕ} {p : Program signature n g} {root : Wire n g}
    {x y z : BitString n} {P : Finset (Fin n)} (h : IsForestMask p root x P)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (hy : ∀ i ∈ P, y i = x i) (hz : ∀ i ∈ P, z i = x i)
    (hStop : ∀ k ∈ StopGate p root,
      (∀ a i, (p.lines k).wires a = .input i → z i = y i) ∨
      p.trace interpretation z (.gate k) = p.trace interpretation y (.gate k)) :
    p.trace interpretation z root = p.trace interpretation y root := by
  apply stopReaders_perturbation_invariant h0 h1 y z hStop
  · intro r hr
    rcases h.1 r hr with ⟨i, hi, hiP, hxi⟩ | hsub
    · exact Or.inl ⟨i, hi, (hy i hiP).trans hxi, (hz i hiP).trans hxi⟩
    · exact Or.inr fun i hi => (hz i (hsub hi)).trans (hy i (hsub hi)).symm
  · intro r hr
    rcases h.2 r hr with ⟨i, hi, hiP, hxi⟩ | hsub
    · exact Or.inl ⟨i, hi, (hy i hiP).trans hxi, (hz i hiP).trans hxi⟩
    · exact Or.inr fun i hi => (hz i (hsub hi)).trans (hy i (hsub hi)).symm

/-- Use a uniform bound on the extra pins of each root to average the affine probes. -/
private theorem exists_weighted_affine_forest_mask_witness {m : ℕ} {f : BooleanFunction n}
    (scale penalty : ℕ)
    (hExtra : ∀ (U : Finset (BitString m)) (b : Bool),
      (∑ ab : BitString m × Bool, scale * (if ab ∈ constAffines U b then U.card - 1 else 0)) ≤
        (U.card + penalty) * (2 ^ m * 2))
    (e : Fin n ↪ BitString m)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (fun i => affine a b0 (e i)) = true) :
    ∃ (x : BitString n) (P : Finset (Fin n)),
      scale * P.card ≤ (scale + penalty) * ((ORRoot c.program (c.outputs 0)).card +
        (ANDRoot c.program (c.outputs 0)).card) + 2 * n ∧
      IsForestMask c.program (c.outputs 0) x P ∧ f x = true ∧
      ∃ a b, x = fun i => affine a b (e i) := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let T_OR := ORRoot p root
  let T_AND := ANDRoot p root
  let I_OR (r : Fin c.size) : Finset (Fin n) := orInputs p root r
  let I_AND (r' : Fin c.size) : Finset (Fin n) := andInputs p root r'
  let U_OR (r : Fin c.size) : Finset (BitString m) :=
    (I_OR r).image e
  let U_AND (r' : Fin c.size) : Finset (BitString m) :=
    (I_AND r').image e
  have hCardUOR (r : Fin c.size) : (U_OR r).card = (I_OR r).card :=
    Finset.card_image_of_injective _ e.injective
  have hCardUAND (r' : Fin c.size) : (U_AND r').card = (I_AND r').card :=
    Finset.card_image_of_injective _ e.injective
  let failOR (ab : BitString m × Bool) : ℕ :=
    ∑ r ∈ T_OR, if ab ∈ constAffines (U_OR r) false then (I_OR r).card - 1 else 0
  let failAND (ab : BitString m × Bool) : ℕ :=
    ∑ r ∈ T_AND, if ab ∈ constAffines (U_AND r) true then (I_AND r).card - 1 else 0
  have hSumIOR : ∑ r ∈ T_OR, (I_OR r).card ≤ n := by
    have hDisj : ∀ r1 ∈ T_OR, ∀ r2 ∈ T_OR, r1 ≠ r2 → Disjoint (I_OR r1) (I_OR r2) :=
      fun _ _ _ _ hne => orInputs_disjoint h0 hne
    rw [← Finset.card_biUnion hDisj]
    exact (Finset.card_le_univ _).trans (by simp)
  have hSumIAND : ∑ r ∈ T_AND, (I_AND r).card ≤ n := by
    have hDisj : ∀ r1 ∈ T_AND, ∀ r2 ∈ T_AND, r1 ≠ r2 → Disjoint (I_AND r1) (I_AND r2) :=
      fun _ _ _ _ hne => andInputs_disjoint h1 hne
    rw [← Finset.card_biUnion hDisj]
    exact (Finset.card_le_univ _).trans (by simp)
  have hSumOR : ∑ ab : BitString m × Bool, scale * failOR ab ≤ (n + penalty * T_OR.card) * (2 ^ m * 2) := by
    dsimp only [failOR]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r ∈ T_OR, ((I_OR r).card + penalty) * (2 ^ m * 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        simpa only [hCardUOR] using hExtra (U_OR r) false
      _ ≤ _ := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm _ penalty]
        exact Nat.mul_le_mul_right _ (by omega)
  have hSumAND : ∑ ab : BitString m × Bool, scale * failAND ab ≤ (n + penalty * T_AND.card) * (2 ^ m * 2) := by
    dsimp only [failAND]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r ∈ T_AND, ((I_AND r).card + penalty) * (2 ^ m * 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        simpa only [hCardUAND] using hExtra (U_AND r) true
      _ ≤ _ := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm _ penalty]
        exact Nat.mul_le_mul_right _ (by omega)
  have hExAb : ∃ ab : BitString m × Bool,
      scale * (failOR ab + failAND ab) ≤ 2 * n + penalty * (T_OR.card + T_AND.card) := by
    by_contra hNot
    simp only [not_exists, not_le] at hNot
    have hUnivCard : (Finset.univ : Finset (BitString m × Bool)).card = 2 ^ m * 2 := by
      simp [Fintype.card_prod, BitString, Fintype.card_bool, Fintype.card_fin]
    have hLower : (2 ^ m * 2) * (2 * n + penalty * (T_OR.card + T_AND.card) + 1) ≤
        ∑ ab : BitString m × Bool, scale * (failOR ab + failAND ab) := by
      calc
        _ = ∑ _ab : BitString m × Bool, (2 * n + penalty * (T_OR.card + T_AND.card) + 1) := by
            rw [Finset.sum_const, smul_eq_mul, hUnivCard]
        _ ≤ _ := Finset.sum_le_sum fun ab _ => hNot ab
    rw [show (∑ ab : BitString m × Bool, scale * (failOR ab + failAND ab)) =
        (∑ ab : BitString m × Bool, scale * failOR ab) + ∑ ab : BitString m × Bool, scale * failAND ab by
      simp only [Nat.mul_add, Finset.sum_add_distrib]] at hLower
    have hUpper := add_le_add hSumOR hSumAND
    have hUpper' : (∑ ab : BitString m × Bool, scale * failOR ab) +
        (∑ ab : BitString m × Bool, scale * failAND ab) ≤
        (2 * n + penalty * (T_OR.card + T_AND.card)) * (2 ^ m * 2) := by
      convert hUpper using 1
      ring
    have hGap := hLower.trans hUpper'
    have hPos : 0 < 2 ^ m * 2 := by positivity
    rw [Nat.mul_comm (2 ^ m * 2)] at hGap
    have h := (Nat.mul_le_mul_right_iff hPos).mp hGap
    omega
  obtain ⟨ab, habLe⟩ := hExAb
  let x : BitString n := fun i => affine ab.1 ab.2 (e i)
  let maskOR (r : Fin c.size) : Finset (Fin n) :=
    if h : ∃ w ∈ I_OR r, x w = true then {Classical.choose h} else I_OR r
  let maskAND (r' : Fin c.size) : Finset (Fin n) :=
    if h : ∃ u ∈ I_AND r', x u = false then {Classical.choose h} else I_AND r'
  have hMaskORCard (r : Fin c.size) :
      (maskOR r).card ≤ 1 + (if ab ∈ constAffines (U_OR r) false then (I_OR r).card - 1 else 0) := by
    by_cases h1 : ∃ w ∈ I_OR r, x w = true <;>
      by_cases h2 : ab ∈ constAffines (U_OR r) false
    · simp [maskOR, h1, h2]
    · simp [maskOR, h1, h2]
    · simp [maskOR, h1, h2]
      omega
    · exfalso
      apply h2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      by_contra hNeF
      have hXT : x i = true := by
        have hEqX : x i = affine ab.1 ab.2 (e i) := by
          rfl
        rw [hEqX]
        exact Bool.eq_true_of_not_eq_false hNeF
      exact h1 ⟨i, hi, hXT⟩
  have hMaskANDCard (r' : Fin c.size) :
      (maskAND r').card ≤ 1 + (if ab ∈ constAffines (U_AND r') true then (I_AND r').card - 1 else 0) := by
    by_cases h1 : ∃ u ∈ I_AND r', x u = false <;>
      by_cases h2 : ab ∈ constAffines (U_AND r') true
    · simp [maskAND, h1, h2]
    · simp [maskAND, h1, h2]
    · simp [maskAND, h1, h2]
      omega
    · exfalso
      apply h2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      by_contra hNeT
      have hXF : x i = false := by
        have hEqX : x i = affine ab.1 ab.2 (e i) := by
          rfl
        rw [hEqX]
        exact Bool.eq_false_iff.mpr hNeT
      exact h1 ⟨i, hi, hXF⟩
  let Mask : Finset (Fin n) :=
    T_OR.biUnion maskOR ∪ T_AND.biUnion maskAND
  have hMaskCard : Mask.card ≤
      T_OR.card + failOR ab + T_AND.card + failAND ab := by
    have hU := Finset.card_union_le (T_OR.biUnion maskOR) (T_AND.biUnion maskAND)
    have hB1 : (T_OR.biUnion maskOR).card ≤ T_OR.card + failOR ab := by
      calc
        (T_OR.biUnion maskOR).card ≤ ∑ r ∈ T_OR, (maskOR r).card := Finset.card_biUnion_le
        _ ≤ ∑ r ∈ T_OR, (1 + (if ab ∈ constAffines (U_OR r) false then (I_OR r).card - 1 else 0)) :=
            Finset.sum_le_sum fun r _ => hMaskORCard r
        _ = T_OR.card + failOR ab := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hB2 : (T_AND.biUnion maskAND).card ≤ T_AND.card + failAND ab := by
      calc
        (T_AND.biUnion maskAND).card ≤ ∑ r' ∈ T_AND, (maskAND r').card := Finset.card_biUnion_le
        _ ≤ ∑ r' ∈ T_AND, (1 + (if ab ∈ constAffines (U_AND r') true then (I_AND r').card - 1 else 0)) :=
            Finset.sum_le_sum fun r' _ => hMaskANDCard r'
        _ = T_AND.card + failAND ab := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    dsimp only [Mask]
    omega
  refine ⟨x, Mask, ?_, ⟨?_, ?_⟩, hAff ab.1 ab.2, ab.1, ab.2, rfl⟩
  · have hGrouped : Mask.card ≤ (T_OR.card + T_AND.card) + (failOR ab + failAND ab) := by omega
    have hScaled := Nat.mul_le_mul_left scale hGrouped
    rw [Nat.mul_add] at hScaled
    rw [Nat.add_mul]
    dsimp only [T_OR, T_AND, p, root] at hScaled habLe ⊢
    omega
  · intro r hr
    by_cases hEx : ∃ w ∈ I_OR r, x w = true
    · left
      let w := Classical.choose hEx
      have hw := Classical.choose_spec hEx
      refine ⟨w, hw.1, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, hr, ?_⟩), hw.2⟩
      simp [maskOR, hEx, w]
    · right
      intro i hi
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, hr, by
        simpa [maskOR, hEx] using hi⟩)
  · intro r hr
    by_cases hEx : ∃ u ∈ I_AND r, x u = false
    · left
      let u := Classical.choose hEx
      have hu := Classical.choose_spec hEx
      refine ⟨u, hu.1, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, ?_⟩), hu.2⟩
      simp [maskAND, hEx, u]
    · right
      intro i hi
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, by
        simpa [maskAND, hEx] using hi⟩)

/-- Average the affine probes on any injectively labelled set of input slots. -/
theorem exists_reindexed_affine_forest_mask_witness {m : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (fun i => affine a b0 (e i)) = true) :
    ∃ (x : BitString n) (P : Finset (Fin n)),
      12 * P.card ≤ 13 * ((ORRoot c.program (c.outputs 0)).card +
        (ANDRoot c.program (c.outputs 0)).card) + 2 * n ∧
      IsForestMask c.program (c.outputs 0) x P ∧ f x = true ∧
      ∃ a b, x = fun i => affine a b (e i) :=
  exists_weighted_affine_forest_mask_witness 12 1 affine_mask_extra_le e c hc hf0 hf1 hAff

theorem exists_reindexed_affine_forest_mask {m : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (fun i => affine a b0 (e i)) = true) :
    ∃ (x : BitString n) (P : Finset (Fin n)),
      12 * P.card ≤ 13 * ((ORRoot c.program (c.outputs 0)).card +
        (ANDRoot c.program (c.outputs 0)).card) + 2 * n ∧
      ∀ y, (∀ i ∈ P ∪ stopInputs c.program (c.outputs 0), y i = x i) → f y = true := by
  obtain ⟨x, P, hP, hMask, hx, _⟩ := exists_reindexed_affine_forest_mask_witness e c hc hf0 hf1 hAff
  refine ⟨x, P, hP, fun y hy => ?_⟩
  have h0 : cornerValue c.program false (c.outputs 0) = true := (congrFun (hc _) 0).trans hf0
  have h1 : cornerValue c.program true (c.outputs 0) = true := (congrFun (hc _) 0).trans hf1
  have he := hMask.trace_eq h0 h1 (fun _ _ => rfl)
    (fun i hi => hy i (Finset.mem_union_left _ hi))
    (fun _ hk => Or.inl fun a i ha => hy i
      (Finset.mem_union_right _ (stopInput_mem_of_wire hk a ha)))
  exact (congrFun (hc y) 0).symm.trans (he.trans ((congrFun (hc x) 0).trans hx))

/-- The full-size bound uses one joint fan-in budget at stop gates. -/
theorem sparse_reindexed_affine_stop_budget {m B : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (fun i => affine a b0 (e i)) = true) :
    10 * n ≤ 142 * B + 17238 * slack c.program (c.outputs 0) +
      26 * (StopGate c.program (c.outputs 0)).card := by
  obtain ⟨x, P, hP, hAccept⟩ := exists_reindexed_affine_forest_mask e c hc hf0 hf1 hAff
  have hMasked := card_masked_le hSparse x _ hAccept
  have hUnion := Finset.card_union_le P (stopInputs c.program (c.outputs 0))
  have hBudget := card_stopInputs_and_roots_le c hc hSparse hf0 hf1
  omega

theorem tight_reindexed_forest_size {m B : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m) (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hAff : ∀ (a : BitString m) (b : Bool), f (fun i => affine a b (e i)) = true) :
    25884 * (2 * n) + 14 * n ≤
      25884 * (complexity interpretation (single f) + 2 * B + 1) + 196 * B := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  have hf (b : Bool) : f (fun _ => b) = true := by
    have hev (d : ℕ) (z : BitString d) : affine (fun _ => false) b z = b := by
      induction d with
      | zero => simp [affine, dot]
      | succ d ih =>
        rw [affine_succ]
        change (false ^^ affine (fun _ => false) b (Fin.tail z)) = b
        simp [ih]
    simpa only [hev m] using hAff (fun _ => false) b
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc _) 0).trans (hf false)
  have h1 : cornerValue p true root = true := (congrFun (hc _) 0).trans (hf true)
  obtain ⟨x, P, hP, hMask, hx, _⟩ := exists_weighted_affine_forest_mask_witness 16 2
    affine_mask_extra_tight e c hc (hf false) (hf true) hAff
  have hAccept (y : BitString n) (hy : ∀ i ∈ P ∪ stopInputs p root, y i = x i) : f y = true := by
    have he := hMask.trace_eq h0 h1 (fun _ _ => rfl)
      (fun i hi => hy i (Finset.mem_union_left _ hi))
      (fun _ hk => Or.inl fun a i ha => hy i (Finset.mem_union_right _ (stopInput_mem_of_wire hk a ha)))
    exact (congrFun (hc y) 0).symm.trans (he.trans ((congrFun (hc x) 0).trans hx))
  have hMasked := card_masked_le hSparse x _ hAccept
  have hUnion := Finset.card_union_le P (stopInputs p root)
  have hBudget := card_stopInputs_and_roots_le c hc hSparse (hf false) (hf true)
  have hStop := card_stopGate_le_56_slack p root h0 h1
  have hN0 := card_needInputs_ge_of_sparse c hc hSparse false (hf false)
  have hN1 := card_needInputs_ge_of_sparse c hc hSparse true (hf true)
  have hAcct := needInputs_add_slack_eq p root h0 h1
  dsimp only [p, root] at hMasked hUnion hStop hAcct
  omega

theorem mcspSquare_32_tight_forest :
    8592202077 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := tight_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding
    (card_accepting_mcspSquare_le 32) (fun a b => by
      change mcspSquare 32 (MCSP.truthTable 32 (affine a b)) = true
      exact mcspSquare_accepts_affine 32 (by decide) a b)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 25884 * (2 * 4294967296) + 14 * 4294967296 ≤
    25884 * (complexity interpretation (single (mcspSquare 32)) + 2 * 27672 + 1) + 196 * 27672 at h
  omega

#print axioms tight_reindexed_forest_size
#print axioms mcspSquare_32_tight_forest

theorem exists_affine_forest_mask_witness {m : ℕ} {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (MCSP.truthTable m (affine a b0)) = true) :
    ∃ (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m))),
      12 * P.card ≤ 13 * ((ORRoot c.program (c.outputs 0)).card +
        (ANDRoot c.program (c.outputs 0)).card) + 2 * 2 ^ m ∧
      IsForestMask c.program (c.outputs 0) x P ∧ f x = true ∧
      ∃ a b, x = MCSP.truthTable m (affine a b) := by
  simpa [MCSP.truthTable] using
    exists_reindexed_affine_forest_mask_witness (BitString.equivFin m).symm.toEmbedding c hc hf0 hf1
      (fun a b => by simpa [MCSP.truthTable] using hAff a b)

theorem exists_affine_forest_mask {m : ℕ} {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (MCSP.truthTable m (affine a b0)) = true) :
    ∃ (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m))),
      12 * P.card ≤ 13 * ((ORRoot c.program (c.outputs 0)).card +
        (ANDRoot c.program (c.outputs 0)).card) + 2 * 2 ^ m ∧
      ∀ y, (∀ i ∈ P ∪ stopInputs c.program (c.outputs 0), y i = x i) → f y = true := by
  exact exists_reindexed_affine_forest_mask (BitString.equivFin m).symm.toEmbedding c hc hf0 hf1
    (fun a b => by simpa [MCSP.truthTable] using hAff a b)

theorem sparse_affine_stop_budget {m B : ℕ} {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (MCSP.truthTable m (affine a b0)) = true) :
    10 * 2 ^ m ≤ 142 * B + 17238 * slack c.program (c.outputs 0) +
      26 * (StopGate c.program (c.outputs 0)).card := by
  exact sparse_reindexed_affine_stop_budget (BitString.equivFin m).symm.toEmbedding c hc hSparse hf0 hf1
    (fun a b => by simpa [MCSP.truthTable] using hAff a b)

theorem sparse_affine_slack_bound_joint {m B : ℕ} {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (MCSP.truthTable m (affine a b0)) = true) :
    10 * 2 ^ m ≤ 142 * B + 18746 * slack c.program (c.outputs 0) := by
  have h := sparse_affine_stop_budget c hc hSparse hf0 hf1 hAff
  have h0 : cornerValue c.program false (c.outputs 0) = true :=
    (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue c.program true (c.outputs 0) = true :=
    (congrFun (hc (fun _ => true)) 0).trans hf1
  have hStop := card_stopGate_le_slack c.program (c.outputs 0) h0 h1
  omega

theorem sparse_affine_slack_bound {m B : ℕ} {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b0 : Bool), f (MCSP.truthTable m (affine a b0)) = true) :
    2 ^ m ≤ 16 * B + 2280 * slack c.program (c.outputs 0) := by
  have h := sparse_affine_slack_bound_joint c hc hSparse hf0 hf1 hAff
  omega

/-- For `m ≥ 5`, any circuit computing `mcspSquare m` has `2 ^ m ≤ 16 * B(m) + 2280 * slack`. -/
theorem mcspSquare_slack_bound (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m))) :
    2 ^ m ≤ 16 * descriptionBitBound m + 2280 * slack c.program (c.outputs 0) :=
  sparse_affine_slack_bound c hc (card_accepting_mcspSquare_le m)
    (mcspSquare_constant_table m (by omega) false)
    (mcspSquare_constant_table m (by omega) true)
    (mcspSquare_accepts_affine m hm)

/-- Unconditional super-`2N` gate lower bound for `mcspSquare m` (`m ≥ 5`, `N = 2 ^ m`):
`2 * 2 ^ m + 2 ^ m / 2280 ≤ complexity (mcspSquare m) + 3 * descriptionBitBound m + 1`. -/
theorem mcspSquare_super_twoN (m : ℕ) (hm : 5 ≤ m) :
    2 * 2 ^ m + 2 ^ m / 2280 ≤
      complexity interpretation (single (mcspSquare m)) + 3 * descriptionBitBound m + 1 := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  let p := c.program
  let root := c.outputs 0
  have hf0 : mcspSquare m (fun _ => false) = true := mcspSquare_constant_table m (by omega) false
  have hf1 : mcspSquare m (fun _ => true) = true := mcspSquare_constant_table m (by omega) true
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  have hSparse := card_accepting_mcspSquare_le m
  have hNI0 := card_needInputs_ge_of_sparse c hc hSparse false hf0
  have hNI1 := card_needInputs_ge_of_sparse c hc hSparse true hf1
  have hAcct := needInputs_add_slack_eq p root h0 h1
  have hSlack := mcspSquare_slack_bound m hm c hc
  dsimp only [p, root] at hAcct
  omega

/-- Concrete super-`2N` threshold theorem at `m = 32` (`N = 2 ^ 32`):
every De Morgan circuit computing `mcspSquare 32` requires strictly more than `2 * 2 ^ 32` gates
(in fact at least `2 * 2 ^ 32 + 1800537` gates). -/
theorem mcspSquare_32_gt_twoN :
    2 * 2 ^ 32 < complexity interpretation (single (mcspSquare 32)) := by
  have hSuper := mcspSquare_super_twoN 32 (by decide)
  have hB32 : descriptionBitBound 32 = 27672 := by decide
  rw [hB32] at hSuper
  omega

/-! ### Super-`2N` bound for sparse circuits accepting `RefinedProbeControl.pattern` probes -/

/-- Signed coordinate-or-constant pattern `z ↦ p.1 ^^ p.2.elim false z` from `MCSPRefinedProbeControl`. -/
abbrev Pattern (w : ℕ) := Bool × Option (Fin w)

/-- Evaluation of a refined-probe pattern `p : Pattern w` on `z : BitString w`. -/
def pattern {w : ℕ} (p : Pattern w) (z : BitString w) : Bool :=
  p.1 ^^ p.2.elim false z

/-- Signed coordinate projections `(b, j) : Bool × Fin m` that are constant with value `target` on `U`. -/
noncomputable def vanishPat {m : ℕ} (U : Finset (BitString m)) (target : Bool) :
    Finset (Bool × Fin m) :=
  Finset.univ.filter fun bj => ∀ z ∈ U, pattern (bj.1, some bj.2) z = target

/-- On any subset `U ⊆ {0,1}^m` of size `|U| ≥ 2`, at most `m - 1` signed coordinate projections
`(b, j) ∈ Bool × Fin m` can be constant with value `target` on `U`. -/
theorem card_vanishPat_le_of_two_le {m : ℕ} (U : Finset (BitString m)) (target : Bool)
    (hTwo : 2 ≤ U.card) :
    (vanishPat U target).card ≤ m - 1 := by
  classical
  obtain ⟨z1, hz1, z2, hz2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
  have hExJ : ∃ j0 : Fin m, z1 j0 ≠ z2 j0 := Function.ne_iff.mp hne
  obtain ⟨j0, hj0⟩ := hExJ
  let cand : Finset (Bool × Fin m) :=
    (Finset.univ.erase j0).image fun j => (target ^^ z1 j, j)
  have hSub : vanishPat U target ⊆ cand := by
    intro ⟨b, j⟩ hbj
    have hAll := (Finset.mem_filter.mp hbj).2
    have h1 : (b ^^ z1 j) = target := by simpa [pattern] using hAll z1 hz1
    have h2 : (b ^^ z2 j) = target := by simpa [pattern] using hAll z2 hz2
    have hb : b = (target ^^ z1 j) := bool_xor_eq_iff.mp h1
    have hjNe : j ≠ j0 := by
      intro hEq
      subst hEq
      exact hj0 (bool_xor_cancel_left (h1.trans h2.symm))
    exact Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hjNe, Finset.mem_univ j⟩, Prod.ext hb.symm rfl⟩
  have hCardCand : cand.card ≤ m - 1 := by
    calc
      cand.card ≤ (Finset.univ.erase j0).card := Finset.card_image_le
      _ = m - 1 := by simp [Finset.card_erase_of_mem]
  exact (Finset.card_le_card hSub).trans hCardCand

/-- Any sparse circuit (`|acceptingTables f| ≤ 2 ^ B`) accepting all `2m + 2` refined-probe patterns
`MCSP.truthTable m (pattern p)` (`p : Pattern m`) satisfies
`2 ^ m ≤ 11 * m * B + 1559 * m * slack` and
`2 * 2 ^ m + 2 ^ m / (1559 * m) ≤ c.size + 3 * B + 1`
(sharpened via `cutInputs_perturbation_invariant`, eliminating `Finset.univ \ S_in`). -/
theorem sparse_pattern_super_twoN {m B : ℕ} (hm : 1 ≤ m) {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hPat : ∀ p : Pattern m, f (MCSP.truthTable m (pattern p)) = true) :
    2 ^ m ≤ 11 * m * B + 1559 * m * slack c.program (c.outputs 0) ∧
      2 * 2 ^ m + 2 ^ m / (1559 * m) ≤ c.size + 3 * B + 1 := by
  classical
  let p := c.program
  let root := c.outputs 0
  have hf0 : f (fun _ => false) = true := by
    have h := hPat (false, none)
    have hEq : MCSP.truthTable m (pattern (false, none)) = fun _ => false := by
      funext i; simp [MCSP.truthTable_apply, pattern]
    rwa [hEq] at h
  have hf1 : f (fun _ => true) = true := by
    have h := hPat (true, none)
    have hEq : MCSP.truthTable m (pattern (true, none)) = fun _ => true := by
      funext i; simp [MCSP.truthTable_apply, pattern]
    rwa [hEq] at h
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let T_OR := ORRoot p root
  let T_AND := ANDRoot p root
  let C_in := cutInputs p root
  have hRoots : T_OR.card + T_AND.card ≤ 10 * B + 1442 * slack p root :=
    card_orRoot_add_andRoot_le c hc hSparse hf0 hf1
  have hCut : C_in.card ≤ 117 * slack p root := card_cutInputs_le_slack p root h0 h1
  let I_OR (r : Fin c.size) : Finset (Fin (2 ^ m)) := orInputs p root r
  let I_AND (r' : Fin c.size) : Finset (Fin (2 ^ m)) := andInputs p root r'
  let U_OR (r : Fin c.size) : Finset (BitString m) :=
    (I_OR r).image (BitString.equivFin m).symm
  let U_AND (r' : Fin c.size) : Finset (BitString m) :=
    (I_AND r').image (BitString.equivFin m).symm
  have hCardUOR (r : Fin c.size) : (U_OR r).card = (I_OR r).card :=
    Finset.card_image_of_injective _ (BitString.equivFin m).symm.injective
  have hCardUAND (r' : Fin c.size) : (U_AND r').card = (I_AND r').card :=
    Finset.card_image_of_injective _ (BitString.equivFin m).symm.injective
  have hSumIOR : ∑ r ∈ T_OR, (I_OR r).card ≤ 2 ^ m := by
    have hDisj : ∀ r1 ∈ T_OR, ∀ r2 ∈ T_OR, r1 ≠ r2 → Disjoint (I_OR r1) (I_OR r2) :=
      fun _ _ _ _ hne => orInputs_disjoint h0 hne
    rw [← Finset.card_biUnion hDisj]
    exact (Finset.card_le_univ _).trans (by simp)
  have hSumIAND : ∑ r' ∈ T_AND, (I_AND r').card ≤ 2 ^ m := by
    have hDisj : ∀ r1 ∈ T_AND, ∀ r2 ∈ T_AND, r1 ≠ r2 → Disjoint (I_AND r1) (I_AND r2) :=
      fun _ _ _ _ hne => andInputs_disjoint h1 hne
    rw [← Finset.card_biUnion hDisj]
    exact (Finset.card_le_univ _).trans (by simp)
  let extraOR (r : Fin c.size) (bj : Bool × Fin m) : ℕ :=
    if 2 ≤ (I_OR r).card ∧ bj ∈ vanishPat (U_OR r) false then (I_OR r).card else 0
  let extraAND (r' : Fin c.size) (bj : Bool × Fin m) : ℕ :=
    if 2 ≤ (I_AND r').card ∧ bj ∈ vanishPat (U_AND r') true then (I_AND r').card else 0
  let failOR (bj : Bool × Fin m) : ℕ := ∑ r ∈ T_OR, extraOR r bj
  let failAND (bj : Bool × Fin m) : ℕ := ∑ r' ∈ T_AND, extraAND r' bj
  have hTreeOR (r : Fin c.size) :
      ∑ bj : Bool × Fin m, extraOR r bj ≤ (m - 1) * (I_OR r).card := by
    dsimp only [extraOR]
    by_cases hTwo : 2 ≤ (I_OR r).card
    · simp only [hTwo, true_and]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, smul_eq_mul]
      have hTwoU : 2 ≤ (U_OR r).card := by rwa [hCardUOR]
      exact Nat.mul_le_mul_right _ (card_vanishPat_le_of_two_le (U_OR r) false hTwoU)
    · simp [hTwo]
  have hTreeAND (r' : Fin c.size) :
      ∑ bj : Bool × Fin m, extraAND r' bj ≤ (m - 1) * (I_AND r').card := by
    dsimp only [extraAND]
    by_cases hTwo : 2 ≤ (I_AND r').card
    · simp only [hTwo, true_and]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, smul_eq_mul]
      have hTwoU : 2 ≤ (U_AND r').card := by rwa [hCardUAND]
      exact Nat.mul_le_mul_right _ (card_vanishPat_le_of_two_le (U_AND r') true hTwoU)
    · simp [hTwo]
  have hSumFailOR : ∑ bj : Bool × Fin m, failOR bj ≤ (m - 1) * 2 ^ m := by
    dsimp only [failOR]
    rw [Finset.sum_comm]
    calc
      ∑ r ∈ T_OR, ∑ bj : Bool × Fin m, extraOR r bj
        ≤ ∑ r ∈ T_OR, (m - 1) * (I_OR r).card := Finset.sum_le_sum fun r _ => hTreeOR r
      _ = (m - 1) * ∑ r ∈ T_OR, (I_OR r).card := by rw [← Finset.mul_sum]
      _ ≤ (m - 1) * 2 ^ m := Nat.mul_le_mul_left _ hSumIOR
  have hSumFailAND : ∑ bj : Bool × Fin m, failAND bj ≤ (m - 1) * 2 ^ m := by
    dsimp only [failAND]
    rw [Finset.sum_comm]
    calc
      ∑ r' ∈ T_AND, ∑ bj : Bool × Fin m, extraAND r' bj
        ≤ ∑ r' ∈ T_AND, (m - 1) * (I_AND r').card := Finset.sum_le_sum fun r' _ => hTreeAND r'
      _ = (m - 1) * ∑ r' ∈ T_AND, (I_AND r').card := by rw [← Finset.mul_sum]
      _ ≤ (m - 1) * 2 ^ m := Nat.mul_le_mul_left _ hSumIAND
  have hExBj : ∃ bj : Bool × Fin m, m * (failOR bj + failAND bj) ≤ (m - 1) * 2 ^ m := by
    by_contra hNot
    simp only [not_exists, not_le] at hNot
    have hUnivCard : (Finset.univ : Finset (Bool × Fin m)).card = 2 * m := by
      simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    have hLower : (2 * m) * ((m - 1) * 2 ^ m + 1) ≤
        ∑ bj : Bool × Fin m, m * (failOR bj + failAND bj) := by
      calc
        (2 * m) * ((m - 1) * 2 ^ m + 1)
          = ∑ _bj : Bool × Fin m, ((m - 1) * 2 ^ m + 1) := by
            rw [Finset.sum_const, smul_eq_mul, hUnivCard]
        _ ≤ ∑ bj : Bool × Fin m, m * (failOR bj + failAND bj) :=
            Finset.sum_le_sum fun bj _ => hNot bj
    have hUpper : ∑ bj : Bool × Fin m, m * (failOR bj + failAND bj) ≤
        m * (2 * ((m - 1) * 2 ^ m)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      have := add_le_add hSumFailOR hSumFailAND
      nlinarith
    nlinarith
  obtain ⟨bj, hbjLe⟩ := hExBj
  let x : BitString (2 ^ m) := MCSP.truthTable m (pattern (bj.1, some bj.2))
  let maskOR (r : Fin c.size) : Finset (Fin (2 ^ m)) :=
    if h : ∃ w ∈ I_OR r, x w = true then {Classical.choose h} else I_OR r
  let maskAND (r' : Fin c.size) : Finset (Fin (2 ^ m)) :=
    if h : ∃ u ∈ I_AND r', x u = false then {Classical.choose h} else I_AND r'
  have hMaskORCard (r : Fin c.size) : (maskOR r).card ≤ 1 + extraOR r bj := by
    by_cases h1 : ∃ w ∈ I_OR r, x w = true <;>
      by_cases h2 : 2 ≤ (I_OR r).card ∧ bj ∈ vanishPat (U_OR r) false
    · simp [maskOR, extraOR, h1, h2]
    · simp [maskOR, extraOR, h1, h2]
    · simp [maskOR, extraOR, h1, h2]
    · by_cases hTwo : 2 ≤ (I_OR r).card
      · exfalso
        apply h2
        refine ⟨hTwo, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩⟩
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        by_contra hNeF
        have hXT : x i = true := by
          have hEqX : x i = pattern (bj.1, some bj.2) ((BitString.equivFin m).symm i) := by
            simp [x, MCSP.truthTable_apply]
          rw [hEqX]
          exact Bool.eq_true_of_not_eq_false hNeF
        exact h1 ⟨i, hi, hXT⟩
      · simp only [maskOR, extraOR, h1, h2, dite_false, ite_false]
        omega
  have hMaskANDCard (r' : Fin c.size) : (maskAND r').card ≤ 1 + extraAND r' bj := by
    by_cases h1 : ∃ u ∈ I_AND r', x u = false <;>
      by_cases h2 : 2 ≤ (I_AND r').card ∧ bj ∈ vanishPat (U_AND r') true
    · simp [maskAND, extraAND, h1, h2]
    · simp [maskAND, extraAND, h1, h2]
    · simp [maskAND, extraAND, h1, h2]
    · by_cases hTwo : 2 ≤ (I_AND r').card
      · exfalso
        apply h2
        refine ⟨hTwo, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩⟩
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        by_contra hNeT
        have hXF : x i = false := by
          have hEqX : x i = pattern (bj.1, some bj.2) ((BitString.equivFin m).symm i) := by
            simp [x, MCSP.truthTable_apply]
          rw [hEqX]
          exact Bool.eq_false_iff.mpr hNeT
        exact h1 ⟨i, hi, hXF⟩
      · simp only [maskAND, extraAND, h1, h2, dite_false, ite_false]
        omega
  let Mask : Finset (Fin (2 ^ m)) :=
    C_in ∪ T_OR.biUnion maskOR ∪ T_AND.biUnion maskAND
  have hMaskCard : Mask.card ≤
      C_in.card + T_OR.card + failOR bj + T_AND.card + failAND bj := by
    have hU1 := Finset.card_union_le (C_in ∪ T_OR.biUnion maskOR) (T_AND.biUnion maskAND)
    have hU2 := Finset.card_union_le C_in (T_OR.biUnion maskOR)
    have hB1 : (T_OR.biUnion maskOR).card ≤ T_OR.card + failOR bj := by
      calc
        (T_OR.biUnion maskOR).card ≤ ∑ r ∈ T_OR, (maskOR r).card := Finset.card_biUnion_le
        _ ≤ ∑ r ∈ T_OR, (1 + extraOR r bj) := Finset.sum_le_sum fun r _ => hMaskORCard r
        _ = T_OR.card + failOR bj := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hB2 : (T_AND.biUnion maskAND).card ≤ T_AND.card + failAND bj := by
      calc
        (T_AND.biUnion maskAND).card ≤ ∑ r' ∈ T_AND, (maskAND r').card := Finset.card_biUnion_le
        _ ≤ ∑ r' ∈ T_AND, (1 + extraAND r' bj) := Finset.sum_le_sum fun r' _ => hMaskANDCard r'
        _ = T_AND.card + failAND bj := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    dsimp only [Mask]
    omega
  have hAcceptMask : ∀ y : BitString (2 ^ m), (∀ i ∈ Mask, y i = x i) → f y = true := by
    intro y hy
    have hEq := cutInputs_perturbation_invariant h0 h1 x y
      (fun i hiCut => hy i (Finset.mem_union_left _ (Finset.mem_union_left _ hiCut)))
      (fun r hr => by
        by_cases hEx : ∃ w ∈ I_OR r, x w = true
        · left
          let w := Classical.choose hEx
          have hwSpec := Classical.choose_spec hEx
          have hwMemMask : w ∈ Mask := Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨r, hr, by simp [maskOR, hEx, w]⟩))
          exact ⟨w, hwSpec.1, hwSpec.2, (hy w hwMemMask).trans hwSpec.2⟩
        · right
          intro i hiOr
          have hiI : i ∈ I_OR r := hiOr
          have hiMask : i ∈ Mask := Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨r, hr, by simp [maskOR, hEx, hiI]⟩))
          exact hy i hiMask)
      (fun r' hr' => by
        by_cases hEx : ∃ u ∈ I_AND r', x u = false
        · left
          let u := Classical.choose hEx
          have huSpec := Classical.choose_spec hEx
          have huMemMask : u ∈ Mask := Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨r', hr', by simp [maskAND, hEx, u]⟩)
          exact ⟨u, huSpec.1, huSpec.2, (hy u huMemMask).trans huSpec.2⟩
        · right
          intro i hiAnd
          have hiI : i ∈ I_AND r' := hiAnd
          have hiMask : i ∈ Mask := Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨r', hr', by simp [maskAND, hEx, hiI]⟩)
          exact hy i hiMask)
    exact (congrFun (hc y) 0).symm.trans (hEq.trans ((congrFun (hc x) 0).trans (hPat (bj.1, some bj.2))))
  have hMasked := card_masked_le hSparse x Mask hAcceptMask
  have hMulPow : (m - 1) * 2 ^ m + 2 ^ m = m * 2 ^ m := by
    cases m with
    | zero => omega
    | succ m' => simp [Nat.succ_mul]
  have hSlackBound : 2 ^ m ≤ 11 * m * B + 1559 * m * slack c.program (c.outputs 0) := by
    have hMulMask := Nat.mul_le_mul_left m (hMasked.trans (Nat.add_le_add_right hMaskCard B))
    have hMulRoots := Nat.mul_le_mul_left m hRoots
    have hMulCut := Nat.mul_le_mul_left m hCut
    dsimp only [p, root] at hRoots hCut hMulRoots hMulCut
    nlinarith
  have hNI0 := card_needInputs_ge_of_sparse c hc hSparse false hf0
  have hNI1 := card_needInputs_ge_of_sparse c hc hSparse true hf1
  have hAcct := needInputs_add_slack_eq p root h0 h1
  dsimp only [p, root] at hAcct ⊢
  refine ⟨hSlackBound, ?_⟩
  have hDiv : 2 ^ m / (1559 * m) ≤ B + slack c.program (c.outputs 0) := by
    apply Nat.div_le_of_le_mul
    nlinarith
  omega

#print axioms bottleneck_fooling_card_le
#print axioms mcspSquare_super_twoN
#print axioms mcspSquare_32_gt_twoN
#print axioms sparse_pattern_super_twoN

end PvsNP.Frontier.SuperTwoN
