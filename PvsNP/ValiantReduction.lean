module

public import PvsNP.StrideContraction

@[expose] public section

/-!
# Valiant Depth-Reduction Compiler & $O(n \log n)$ Skip-Wire Barrier

Advances the algorithmic `#SAT` frontier in `PvsNP/` along two complementary axes:

1. **Bit-level Valiant depth decomposition & subset averaging (`highestDiffBit`, `compressBits`,
   `exists_subset_sum_le`)**: compresses `k`-bit topological depths while avoiding any subset
   `S : Finset (Fin k)` of bit positions.
2. **Valiant's depth-reduction lemma (`residualDepth`, `valiantDepthReduction`,
   `valiant_halving_cut`)**: on **every** circuit `c` of binary depth `< 2 ^ k`, cutting at most
   `2 * t * binaryGateCount c / k` binary gates reduces every residual cone depth strictly below
   `2 ^ (k - t)`.
3. **Universal residual-depth block compiler (`compileResidualDepth`, `depthCutCertificate`,
   `valiantBlockCertificate`, `depthCut_subexponential`)**: compiles any circuit + depth cut of
   residual depth `< H` into an exact-counting `BlockContractionCertificate source (2 ^ H)` with at
   most `keptCount n cut + 1` blocks, yielding `2 ^ o(n)` `#SAT` whenever `keptCount + 1 = O(n (log n)^α)`
   (`α < 1 / 2`) at constant `H`.
4. **General stride-`h` crossing lower bound (`strideCertificate_blocks_ge_min_crossing`)**:
   lower-bounds `(strideCertificate source h hh).blocks` by the minimum crossing-wire count over all
   `r : Fin h`.
5. **Explicit $O(n \log n)$ bounded-fanout skip-wire barrier (`SkipRing`)**: synchronous `D`-layer
   ring circuits with skip span `s` have exact binary gate count `D * n`, max fanout `≤ 3` on every
   wire (`source_fanout_le_three`, blocking `LiteralPropagation` via `source_hitting_cut_lower`), and
   `totalTruncatedSpan ≥ h * ((D - s) * n)` (`source_totalTruncatedSpan_ge`), forcing every stride-`h`
   residue in `StrideContraction` to retain `≥ (D - s) * n` blocks (`source_strideCertificate_blocks_ge`).
   At `D = Nat.log 2 n + s` (`O(n log n)` total gates), `SkipRing` provably escapes `StrideContraction`'s
   subexponential window (`source_escapes_stride_subexponential_window`), while Valiant's depth-reduction
   cut ignores `wireSpan` completely (`source_valiant_span_invariant`).
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Bit-Level Valiant Decomposition & Subset Averaging -/

/-- Highest differing bit index strictly below `k` between `x` and `y` (returns `0` if `k = 0`). -/
def highestDiffBit : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k + 1, x, y =>
    if x / 2 ^ k = y / 2 ^ k then highestDiffBit k (x % 2 ^ k) (y % 2 ^ k) else k

theorem highestDiffBit_lt {k x y : Nat} (hk : 0 < k) : highestDiffBit k x y < k := by
  induction k generalizing x y with
  | zero => cases hk
  | succ k ih =>
    simp only [highestDiffBit]
    split_ifs
    · cases k with
      | zero => simp [highestDiffBit]
      | succ k' => exact Nat.lt_trans (ih (Nat.succ_pos k')) (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self k

/-- Count of bit positions below `m` not erased by `S`. -/
def keepCount (S : Nat → Bool) : Nat → Nat
  | 0 => 0
  | m + 1 => keepCount S m + if S m then 0 else 1

private theorem keepCount_add_filter_card (k : Nat) (S : Finset (Fin k)) :
    ∀ m, m ≤ k →
      keepCount (fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)) m +
        (S.filter (fun b : Fin k => b.val < m)).card = m
  | 0, _ => by
    simp only [keepCount, Nat.zero_add]
    have hEmpty : S.filter (fun b : Fin k => b.val < 0) = ∅ := by
      ext b
      simp
    rw [hEmpty, Finset.card_empty]
  | m + 1, hm => by
    have ih := keepCount_add_filter_card k S m (Nat.le_of_succ_le hm)
    let fPred : Nat → Bool := fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)
    let bm : Fin k := ⟨m, hm⟩
    have hSplit :
        (S.filter (fun b : Fin k => b.val < m + 1)).card =
          (S.filter (fun b : Fin k => b.val < m)).card + if bm ∈ S then 1 else 0 := by
      by_cases hMem : bm ∈ S
      · have hEq : S.filter (fun b : Fin k => b.val < m + 1) =
            insert bm (S.filter (fun b : Fin k => b.val < m)) := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff, bm]
          constructor
          · rintro ⟨hbS, hbLt⟩
            by_cases hbEq : b.val = m
            · exact Or.inl hbEq
            · exact Or.inr ⟨hbS, by omega⟩
          · rintro (hbEq | ⟨hbS, hbLt⟩)
            · subst hbEq
              exact ⟨hMem, Nat.lt_succ_self _⟩
            · exact ⟨hbS, Nat.lt_trans hbLt (Nat.lt_succ_self m)⟩
        have hNotMem : bm ∉ S.filter (fun b : Fin k => b.val < m) := by
          simp [bm]
        rw [hEq, Finset.card_insert_of_notMem hNotMem]
        simp [hMem]
      · have hEq : S.filter (fun b : Fin k => b.val < m + 1) =
            S.filter (fun b : Fin k => b.val < m) := by
          ext b
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hbS, hbLt⟩
            refine ⟨hbS, ?_⟩
            by_contra hGe
            have hbEq : b = bm := Fin.ext (by dsimp [bm]; omega)
            exact hMem (hbEq ▸ hbS)
          · rintro ⟨hbS, hbLt⟩
            exact ⟨hbS, Nat.lt_trans hbLt (Nat.lt_succ_self m)⟩
        rw [hEq]
        simp [hMem]
    have hF : fPred m = decide (bm ∈ S) := by
      simp only [fPred, bm, decide_eq_decide]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨hm, h⟩
    have ih' : keepCount fPred m + (S.filter (fun b : Fin k => b.val < m)).card = m := ih
    change keepCount fPred m + (if fPred m then 0 else 1) +
        (S.filter (fun b : Fin k => b.val < m + 1)).card = m + 1
    rw [hSplit, hF]
    by_cases hMem' : bm ∈ S
    · simp only [hMem', decide_true, ↓reduceIte]
      omega
    · simp only [hMem', decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

theorem keepCount_finset (k : Nat) (S : Finset (Fin k)) :
    keepCount (fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)) k = k - S.card := by
  have h := keepCount_add_filter_card k S k (le_refl k)
  have hFull : S.filter (fun b : Fin k => b.val < k) = S := by
    ext b
    simp
  rw [hFull] at h
  omega

/-- Drops bit positions in `S` from the `k`-bit binary representation of `d`. -/
def compressBits (S : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, d =>
    if S k then compressBits S k (d % 2 ^ k)
    else ((d / 2 ^ k) % 2) * 2 ^ (keepCount S k) + compressBits S k (d % 2 ^ k)

theorem compressBits_lt (S : Nat → Bool) :
    ∀ k d : Nat, compressBits S k d < 2 ^ (keepCount S k)
  | 0, _ => by simp [compressBits, keepCount]
  | k + 1, d => by
    have ih := compressBits_lt S k (d % 2 ^ k)
    simp only [compressBits, keepCount]
    split_ifs with hSk
    · simpa using ih
    · have hBit : (d / 2 ^ k) % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      have hMul : ((d / 2 ^ k) % 2) * 2 ^ keepCount S k ≤ 1 * 2 ^ keepCount S k :=
        Nat.mul_le_mul_right _ hBit
      rw [Nat.pow_succ]
      omega

/-- Strictly order-preserving compression whenever the highest differing bit avoids `S`. -/
theorem compressBits_lt_of_avoid (S : Nat → Bool) :
    ∀ k x y : Nat, x < y → y < 2 ^ k → S (highestDiffBit k x y) = false →
      compressBits S k x < compressBits S k y
  | 0, _, _, hxy, hy, _ => by
    simp at hy
    omega
  | k + 1, x, y, hxy, hy, hAvoid => by
    by_cases hEq : x / 2 ^ k = y / 2 ^ k
    · have hDiff : highestDiffBit (k + 1) x y = highestDiffBit k (x % 2 ^ k) (y % 2 ^ k) := by
        simp [highestDiffBit, hEq]
      rw [hDiff] at hAvoid
      have hxMod : x % 2 ^ k < y % 2 ^ k := by
        have hx := Nat.div_add_mod x (2 ^ k)
        have hy' := Nat.div_add_mod y (2 ^ k)
        rw [hEq] at hx
        omega
      have hyMod : y % 2 ^ k < 2 ^ k := Nat.mod_lt y (Nat.two_pow_pos k)
      have ih := compressBits_lt_of_avoid S k (x % 2 ^ k) (y % 2 ^ k) hxMod hyMod hAvoid
      simp only [compressBits]
      split_ifs with hSk
      · exact ih
      · rw [hEq]
        exact Nat.add_lt_add_left ih _
    · have hDiff : highestDiffBit (k + 1) x y = k := by
        simp [highestDiffBit, hEq]
      rw [hDiff] at hAvoid
      have hy2 : y / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
        simpa [Nat.pow_succ, Nat.mul_comm] using hy
      have hxLe : x / 2 ^ k ≤ y / 2 ^ k := Nat.div_le_div_right (le_of_lt hxy)
      have hyPos : 0 < y / 2 ^ k := Nat.pos_of_ne_zero fun hy0 => by
        have hx0 : x / 2 ^ k = 0 := Nat.eq_zero_of_le_zero (hxLe.trans_eq hy0)
        exact hEq (hx0.trans hy0.symm)
      have hy1 : y / 2 ^ k = 1 := Nat.le_antisymm (Nat.lt_succ_iff.mp hy2) hyPos
      have hxZero : x / 2 ^ k = 0 := by
        rw [hy1] at hxLe
        rcases Nat.eq_zero_or_pos (x / 2 ^ k) with h0 | hxPos
        · exact h0
        · exact absurd ((Nat.le_antisymm hxLe hxPos).trans hy1.symm) hEq
      have hLtX := compressBits_lt S k (x % 2 ^ k)
      simp only [compressBits, hAvoid, Bool.false_eq_true, ↓reduceIte, hxZero, hy1]
      omega

/-- Exact `t`-subset averaging: any nonnegative weight function on `Fin k` has a `t`-element
subset carrying at most `t / k` of the total weight. -/
theorem exists_subset_sum_le {k : Nat} (hk : 0 < k) (f : Fin k → Nat) :
    ∀ t ≤ k, ∃ S : Finset (Fin k), S.card = t ∧
      k * ∑ b ∈ S, f b ≤ t * ∑ b : Fin k, f b
  | 0, _ => ⟨∅, by simp⟩
  | t + 1, ht => by
    obtain ⟨S, hCard, hBound⟩ := exists_subset_sum_le hk f t (Nat.le_of_succ_le ht)
    let R : Finset (Fin k) := Finset.univ \ S
    have hSub : S ⊆ Finset.univ := Finset.subset_univ S
    have hRCard : R.card = k - t := by
      rw [Finset.card_sdiff_of_subset hSub, Finset.card_univ, Fintype.card_fin, hCard]
    have hRPos : 0 < R.card := by omega
    obtain ⟨b₀, hb₀R, hb₀Min⟩ := Finset.exists_min_image R f (Finset.card_pos.mp hRPos)
    have hb₀NotS : b₀ ∉ S := (Finset.mem_sdiff.mp hb₀R).2
    have hRSum : (k - t) * f b₀ ≤ ∑ b ∈ R, f b := by
      calc (k - t) * f b₀ = ∑ _ ∈ R, f b₀ := by rw [Finset.sum_const, smul_eq_mul, hRCard]
        _ ≤ ∑ b ∈ R, f b := Finset.sum_le_sum fun b hb => hb₀Min b hb
    have hSplit : ∑ b ∈ S, f b + ∑ b ∈ R, f b = ∑ b : Fin k, f b :=
      Finset.sum_add_sum_compl S f
    have hktPos : 0 < k - t := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hktPos.ne'
    have hKt : m + t + 1 = k := by omega
    have hStep : (k - t) * (k * (∑ b ∈ insert b₀ S, f b)) ≤
        (k - t) * ((t + 1) * ∑ b : Fin k, f b) := by
      rw [Finset.sum_insert hb₀NotS]
      have hSplitK : k * ∑ b ∈ S, f b + k * ∑ b ∈ R, f b = k * ∑ b : Fin k, f b := by
        rw [← Nat.mul_add, hSplit]
      have h1 : k * ((k - t) * f b₀) ≤ k * ∑ b ∈ R, f b := Nat.mul_le_mul_left k hRSum
      have h2 : m * (k * ∑ b ∈ S, f b) ≤ m * (t * ∑ b : Fin k, f b) := Nat.mul_le_mul_left m hBound
      have hLHS : (k - t) * (k * (f b₀ + ∑ b ∈ S, f b)) =
          k * ((k - t) * f b₀) + m * (k * ∑ b ∈ S, f b) + k * ∑ b ∈ S, f b := by
        rw [hm, Nat.succ_eq_add_one]; ring
      have hMulMT : (m + 1) * (t + 1) = m * t + (m + t + 1) := by ring
      have hRHS : (k - t) * ((t + 1) * ∑ b : Fin k, f b) =
          m * (t * ∑ b : Fin k, f b) + k * ∑ b : Fin k, f b := by
        rw [hm, Nat.succ_eq_add_one, ← Nat.mul_assoc, hMulMT, hKt, Nat.add_mul, Nat.mul_assoc]
      omega
    refine ⟨insert b₀ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hb₀NotS, hCard]
    · exact Nat.le_of_mul_le_mul_left hStep hktPos

/-! ### 2. Valiant Depth-Reduction Lemma for General Circuits -/

/-- Binary topological depth after resetting cut wires (`cut u = true`) to depth `0`. -/
def residualDepth {n : Nat} : {w : Nat} → Circuit n w → (Fin w → Bool) → Fin w → Nat
  | _, .inputsOnly, _, _ => 0
  | _, .snoc earlier (.not a), cut, u =>
    Fin.lastCases
      (if cut (Fin.last _) then 0 else residualDepth earlier (cut ∘ Fin.castSucc) a)
      (residualDepth earlier (cut ∘ Fin.castSucc)) u
  | _, .snoc earlier (.and a b), cut, u =>
    Fin.lastCases
      (if cut (Fin.last _) then 0 else
        max (residualDepth earlier (cut ∘ Fin.castSucc) a)
          (residualDepth earlier (cut ∘ Fin.castSucc) b) + 1)
      (residualDepth earlier (cut ∘ Fin.castSucc)) u
  | _, .snoc earlier (.or a b), cut, u =>
    Fin.lastCases
      (if cut (Fin.last _) then 0 else
        max (residualDepth earlier (cut ∘ Fin.castSucc) a)
          (residualDepth earlier (cut ∘ Fin.castSucc) b) + 1)
      (residualDepth earlier (cut ∘ Fin.castSucc)) u

@[simp] theorem residualDepth_inputsOnly {n : Nat} (cut : Fin n → Bool) (u : Fin n) :
    residualDepth (Circuit.inputsOnly : Circuit n n) cut u = 0 := rfl

@[simp] theorem residualDepth_snoc_not_last {n w : Nat} (c : Circuit n w) (a : Fin w)
    (cut : Fin (w + 1) → Bool) :
    residualDepth (c.snoc (.not a)) cut (Fin.last w) =
      if cut (Fin.last w) then 0 else residualDepth c (cut ∘ Fin.castSucc) a := by
  simp [residualDepth]

@[simp] theorem residualDepth_snoc_and_last {n w : Nat} (c : Circuit n w) (a b : Fin w)
    (cut : Fin (w + 1) → Bool) :
    residualDepth (c.snoc (.and a b)) cut (Fin.last w) =
      if cut (Fin.last w) then 0 else
        max (residualDepth c (cut ∘ Fin.castSucc) a)
          (residualDepth c (cut ∘ Fin.castSucc) b) + 1 := by
  simp [residualDepth]

@[simp] theorem residualDepth_snoc_or_last {n w : Nat} (c : Circuit n w) (a b : Fin w)
    (cut : Fin (w + 1) → Bool) :
    residualDepth (c.snoc (.or a b)) cut (Fin.last w) =
      if cut (Fin.last w) then 0 else
        max (residualDepth c (cut ∘ Fin.castSucc) a)
          (residualDepth c (cut ∘ Fin.castSucc) b) + 1 := by
  simp [residualDepth]

@[simp] theorem residualDepth_snoc_castSucc {n w : Nat} (c : Circuit n w) (g : Gate w)
    (cut : Fin (w + 1) → Bool) (q : Fin w) :
    residualDepth (c.snoc g) cut q.castSucc = residualDepth c (cut ∘ Fin.castSucc) q := by
  cases g <;> simp [residualDepth]

theorem residualDepth_input_eq_zero {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (cut : Fin w → Bool) → (u : Fin w) → u.val < n →
      residualDepth c cut u = 0
  | _, .inputsOnly, _, _, _ => rfl
  | _, .snoc earlier g, cut, u, hu => by
    cases u using Fin.lastCases with
    | last =>
      have hge := earlier.inputs_le_wires
      simp only [Fin.val_last] at hu
      omega
    | cast q =>
      rw [residualDepth_snoc_castSucc]
      exact residualDepth_input_eq_zero earlier (cut ∘ Fin.castSucc) q (by simpa using hu)

theorem residualDepth_le_of_cut_imp {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (cut₁ cut₂ : Fin w → Bool) →
    (∀ u : Fin w, cut₁ u = true → cut₂ u = true) →
    ∀ u : Fin w, residualDepth c cut₂ u ≤ residualDepth c cut₁ u
  | _, .inputsOnly, _, _, _, _ => le_rfl
  | _, .snoc earlier g, cut₁, cut₂, hImp, u => by
    have hImp' : ∀ q : Fin _, (cut₁ ∘ Fin.castSucc) q = true → (cut₂ ∘ Fin.castSucc) q = true :=
      fun q hq => hImp q.castSucc hq
    have ih := residualDepth_le_of_cut_imp earlier (cut₁ ∘ Fin.castSucc) (cut₂ ∘ Fin.castSucc) hImp'
    cases u using Fin.lastCases with
    | cast q =>
      simpa using ih q
    | last =>
      cases g with
      | not a =>
        simp only [residualDepth_snoc_not_last]
        by_cases h2 : cut₂ (Fin.last _) = true <;> by_cases h1 : cut₁ (Fin.last _) = true <;>
          simp only [h2, h1, ↓reduceIte, Bool.false_eq_true]
        · exact Nat.zero_le _
        · exact Nat.zero_le _
        · exact absurd (hImp _ h1) h2
        · exact ih a
      | and a b =>
        simp only [residualDepth_snoc_and_last]
        by_cases h2 : cut₂ (Fin.last _) = true <;> by_cases h1 : cut₁ (Fin.last _) = true <;>
          simp only [h2, h1, ↓reduceIte, Bool.false_eq_true]
        · exact Nat.zero_le _
        · exact Nat.zero_le _
        · exact absurd (hImp _ h1) h2
        · have ha := ih a
          have hb := ih b
          omega
      | or a b =>
        simp only [residualDepth_snoc_or_last]
        by_cases h2 : cut₂ (Fin.last _) = true <;> by_cases h1 : cut₁ (Fin.last _) = true <;>
          simp only [h2, h1, ↓reduceIte, Bool.false_eq_true]
        · exact Nat.zero_le _
        · exact Nat.zero_le _
        · exact absurd (hImp _ h1) h2
        · have ha := ih a
          have hb := ih b
          omega

/-- Valiant cut predicate: a binary gate is hit by `S` iff the highest differing bit between its
depth and either operand's depth falls in `S`. -/
def valiantGateHit {n : Nat} : {w : Nat} → Circuit n w → Nat → (Nat → Bool) → Fin w → Bool
  | _, .inputsOnly, _, _, _ => false
  | _, .snoc earlier (.not _), k, S, u => Fin.lastCases false (valiantGateHit earlier k S) u
  | _, .snoc earlier (.and a b), k, S, u =>
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    Fin.lastCases
      (S (highestDiffBit k (wireDepth earlier a) d) ||
        S (highestDiffBit k (wireDepth earlier b) d))
      (valiantGateHit earlier k S) u
  | _, .snoc earlier (.or a b), k, S, u =>
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    Fin.lastCases
      (S (highestDiffBit k (wireDepth earlier a) d) ||
        S (highestDiffBit k (wireDepth earlier b) d))
      (valiantGateHit earlier k S) u

@[simp] theorem valiantGateHit_snoc_castSucc {n w : Nat} (c : Circuit n w) (g : Gate w)
    (k : Nat) (S : Nat → Bool) (q : Fin w) :
    valiantGateHit (c.snoc g) k S q.castSucc = valiantGateHit c k S q := by
  cases g <;> simp [valiantGateHit]

def valiantCut {n w : Nat} (c : Circuit n w) (k : Nat) (S : Finset (Fin k)) : Fin w → Bool :=
  valiantGateHit c k (fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S))

def valiantLevelCount {n w : Nat} (c : Circuit n w) (k : Nat) (b : Fin k) : Nat :=
  keptCount n (valiantCut c k {b})

theorem sum_valiantLevelCount_le {n w : Nat} (c : Circuit n w) (k : Nat) (hk : 0 < k) :
    ∑ b : Fin k, valiantLevelCount c k b ≤ 2 * binaryGateCount c := by
  induction c with
  | inputsOnly =>
    have hZero : ∀ b : Fin k, valiantLevelCount (Circuit.inputsOnly : Circuit n n) k b = 0 := by
      intro b
      unfold valiantLevelCount keptCount
      have hEmpty : Finset.univ.filter (fun u : Fin n => n ≤ u.val ∧
          valiantCut (Circuit.inputsOnly : Circuit n n) k {b} u = true) = ∅ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        have := u.isLt
        omega
      rw [hEmpty, Finset.card_empty]
    simp [hZero, binaryGateCount, unhitBinaryGates]
  | snoc earlier g ih =>
    rename_i w
    have hComp (b : Fin k) :
        valiantCut (earlier.snoc g) k {b} ∘ Fin.castSucc = valiantCut earlier k {b} := by
      funext q
      simp [valiantCut]
    cases g with
    | not a =>
      have hBin : binaryGateCount (earlier.snoc (.not a)) = binaryGateCount earlier := by
        dsimp [binaryGateCount, unhitBinaryGates]; rfl
      have hStep (b : Fin k) :
          valiantLevelCount (earlier.snoc (.not a)) k b = valiantLevelCount earlier k b := by
        dsimp only [valiantLevelCount]
        rw [keptCount_snoc, hComp b]
        have hLast : valiantCut (earlier.snoc (.not a)) k {b} (Fin.last w) = false := by
          simp [valiantCut, valiantGateHit]
        simp [hLast]
      simp_rw [hStep, hBin]
      exact ih
    | and a b =>
      have hBin : binaryGateCount (earlier.snoc (.and a b)) = binaryGateCount earlier + 1 := by
        dsimp [binaryGateCount, unhitBinaryGates]
      let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
      let b₁ : Fin k := ⟨highestDiffBit k (wireDepth earlier a) d, highestDiffBit_lt hk⟩
      let b₂ : Fin k := ⟨highestDiffBit k (wireDepth earlier b) d, highestDiffBit_lt hk⟩
      have hStep (r : Fin k) :
          valiantLevelCount (earlier.snoc (.and a b)) k r ≤
            valiantLevelCount earlier k r + (if r = b₁ then 1 else 0) + (if r = b₂ then 1 else 0) := by
        dsimp only [valiantLevelCount]
        rw [keptCount_snoc, hComp r]
        by_cases hCut : n ≤ w ∧ valiantCut (earlier.snoc (.and a b)) k {r} (Fin.last w) = true
        · have hLast : r = b₁ ∨ r = b₂ := by
            have hOr := hCut.2
            simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_singleton] at hOr
            rcases hOr with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          simp only [hCut]
          rcases hLast with rfl | rfl <;> simp
        · simp only [hCut, ↓reduceIte]
          omega
      calc
        ∑ r : Fin k, valiantLevelCount (earlier.snoc (.and a b)) k r
          ≤ ∑ r : Fin k, (valiantLevelCount earlier k r +
              (if r = b₁ then 1 else 0) + (if r = b₂ then 1 else 0)) :=
            Finset.sum_le_sum fun r _ => hStep r
        _ = (∑ r : Fin k, valiantLevelCount earlier k r) +
              (∑ r : Fin k, if r = b₁ then 1 else 0) + (∑ r : Fin k, if r = b₂ then 1 else 0) := by
            simp [Finset.sum_add_distrib]
        _ = (∑ r : Fin k, valiantLevelCount earlier k r) + 1 + 1 := by simp
        _ ≤ 2 * binaryGateCount (earlier.snoc (.and a b)) := by rw [hBin]; omega
    | or a b =>
      have hBin : binaryGateCount (earlier.snoc (.or a b)) = binaryGateCount earlier + 1 := by
        dsimp [binaryGateCount, unhitBinaryGates]; rfl
      let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
      let b₁ : Fin k := ⟨highestDiffBit k (wireDepth earlier a) d, highestDiffBit_lt hk⟩
      let b₂ : Fin k := ⟨highestDiffBit k (wireDepth earlier b) d, highestDiffBit_lt hk⟩
      have hStep (r : Fin k) :
          valiantLevelCount (earlier.snoc (.or a b)) k r ≤
            valiantLevelCount earlier k r + (if r = b₁ then 1 else 0) + (if r = b₂ then 1 else 0) := by
        dsimp only [valiantLevelCount]
        rw [keptCount_snoc, hComp r]
        by_cases hCut : n ≤ w ∧ valiantCut (earlier.snoc (.or a b)) k {r} (Fin.last w) = true
        · have hLast : r = b₁ ∨ r = b₂ := by
            have hOr := hCut.2
            simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_singleton] at hOr
            rcases hOr with ⟨_, h⟩ | ⟨_, h⟩
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          simp only [hCut]
          rcases hLast with rfl | rfl <;> simp
        · simp only [hCut, ↓reduceIte]
          omega
      calc
        ∑ r : Fin k, valiantLevelCount (earlier.snoc (.or a b)) k r
          ≤ ∑ r : Fin k, (valiantLevelCount earlier k r +
              (if r = b₁ then 1 else 0) + (if r = b₂ then 1 else 0)) :=
            Finset.sum_le_sum fun r _ => hStep r
        _ = (∑ r : Fin k, valiantLevelCount earlier k r) +
              (∑ r : Fin k, if r = b₁ then 1 else 0) + (∑ r : Fin k, if r = b₂ then 1 else 0) := by
            simp [Finset.sum_add_distrib]
        _ = (∑ r : Fin k, valiantLevelCount earlier k r) + 1 + 1 := by simp
        _ ≤ 2 * binaryGateCount (earlier.snoc (.or a b)) := by rw [hBin]; omega

theorem keptCount_valiantCut_le_sum {n w : Nat} (c : Circuit n w) (k : Nat)
    (S : Finset (Fin k)) :
    keptCount n (valiantCut c k S) ≤ ∑ b ∈ S, valiantLevelCount c k b := by
  induction c with
  | inputsOnly =>
    unfold keptCount
    have hEmpty : Finset.univ.filter (fun u : Fin n => n ≤ u.val ∧
        valiantCut (Circuit.inputsOnly : Circuit n n) k S u = true) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      have := u.isLt
      omega
    rw [hEmpty, Finset.card_empty]
    exact Nat.zero_le _
  | snoc earlier g ih =>
    rename_i w
    have hComp (T : Finset (Fin k)) :
        valiantCut (earlier.snoc g) k T ∘ Fin.castSucc = valiantCut earlier k T := by
      funext q
      simp [valiantCut]
    rw [keptCount_snoc, hComp S]
    have hTail (b : Fin k) : valiantLevelCount (earlier.snoc g) k b =
        valiantLevelCount earlier k b +
          if n ≤ w ∧ valiantCut (earlier.snoc g) k {b} (Fin.last w) = true then 1 else 0 := by
      dsimp only [valiantLevelCount]
      rw [keptCount_snoc, hComp {b}]
    simp_rw [hTail, Finset.sum_add_distrib]
    by_cases hHit : n ≤ w ∧ valiantCut (earlier.snoc g) k S (Fin.last w) = true
    · conv_lhs => rw [ite_eq_left_iff.mpr (fun h => absurd hHit h)]
      obtain ⟨r, hrS, hrSing⟩ : ∃ r ∈ S,
          valiantCut (earlier.snoc g) k {r} (Fin.last w) = true := by
        cases g with
        | not _ => simp [valiantCut, valiantGateHit] at hHit
        | and a b =>
          have hOr := hHit.2
          simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
            decide_eq_true_eq] at hOr
          rcases hOr with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · refine ⟨⟨highestDiffBit k _ _, hl⟩, hr, ?_⟩
            simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_singleton]
            exact Or.inl ⟨hl, trivial⟩
          · refine ⟨⟨highestDiffBit k _ _, hl⟩, hr, ?_⟩
            simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_singleton]
            exact Or.inr ⟨hl, trivial⟩
        | or a b =>
          have hOr := hHit.2
          simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
            decide_eq_true_eq] at hOr
          rcases hOr with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · refine ⟨⟨highestDiffBit k _ _, hl⟩, hr, ?_⟩
            simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_singleton]
            exact Or.inl ⟨hl, trivial⟩
          · refine ⟨⟨highestDiffBit k _ _, hl⟩, hr, ?_⟩
            simp only [valiantCut, valiantGateHit, Fin.lastCases_last, Bool.or_eq_true,
              decide_eq_true_eq, Finset.mem_singleton]
            exact Or.inr ⟨hl, trivial⟩
      have hOne : 1 ≤ ∑ b ∈ S,
          if n ≤ w ∧ valiantCut (earlier.snoc g) k {b} (Fin.last w) = true then 1 else 0 := by
        calc
          1 = (if n ≤ w ∧ valiantCut (earlier.snoc g) k {r} (Fin.last w) = true then 1 else 0) := by
              simp [hHit.1, hrSing]
          _ ≤ ∑ b ∈ S, if n ≤ w ∧ valiantCut (earlier.snoc g) k {b} (Fin.last w) = true
              then 1 else 0 :=
            Finset.single_le_sum
              (f := fun b : Fin k =>
                if n ≤ w ∧ valiantCut (earlier.snoc g) k {b} (Fin.last w) = true then 1 else 0)
              (fun _ _ => Nat.zero_le _) hrS
      omega
    · conv_lhs => rw [ite_eq_right_iff.mpr (fun h => absurd h hHit)]
      rw [Nat.add_zero]
      exact Nat.le_add_right_of_le ih

theorem residualDepth_le_compressBits {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (k : Nat) → (S : Nat → Bool) → (cut : Fin w → Bool) →
    (∀ u : Fin w, wireDepth c u < 2 ^ k) →
    (∀ u : Fin w, valiantGateHit c k S u = true → cut u = true) →
    ∀ u : Fin w, residualDepth c cut u ≤ compressBits S k (wireDepth c u)
  | _, .inputsOnly, _, _, _, _, _, _ => Nat.zero_le _
  | w + 1, .snoc earlier g, k, S, cut, hDepth, hHit, u => by
    have hDepthEarlier : ∀ q : Fin w, wireDepth earlier q < 2 ^ k := by
      intro q
      simpa using hDepth q.castSucc
    have hHitEarlier : ∀ q : Fin w, valiantGateHit earlier k S q = true →
        (cut ∘ Fin.castSucc) q = true := by
      intro q hq
      exact hHit q.castSucc (by simpa using hq)
    have ih := residualDepth_le_compressBits earlier k S (cut ∘ Fin.castSucc)
      hDepthEarlier hHitEarlier
    cases u using Fin.lastCases with
    | cast q =>
      simpa using ih q
    | last =>
      cases g with
      | not a =>
        simp only [residualDepth_snoc_not_last, wireDepth_snoc_not_last]
        split_ifs
        · exact Nat.zero_le _
        · exact ih a
      | and a b =>
        simp only [residualDepth_snoc_and_last, wireDepth_snoc_and_last]
        split_ifs with hCut
        · exact Nat.zero_le _
        · have hHitLast : valiantGateHit (earlier.snoc (.and a b)) k S (Fin.last w) = false := by
            cases hV : valiantGateHit (earlier.snoc (.and a b)) k S (Fin.last w)
            · rfl
            · exact absurd (hHit (Fin.last w) hV) hCut
          simp only [valiantGateHit, Fin.lastCases_last, Bool.or_eq_false_iff] at hHitLast
          have hdLt : max (wireDepth earlier a) (wireDepth earlier b) + 1 < 2 ^ k := by
            simpa using hDepth (Fin.last w)
          have haLt : wireDepth earlier a <
              compressBits S k (max (wireDepth earlier a) (wireDepth earlier b) + 1) →
              True := fun _ => trivial
          have hCa : compressBits S k (wireDepth earlier a) <
              compressBits S k (max (wireDepth earlier a) (wireDepth earlier b) + 1) :=
            compressBits_lt_of_avoid S k (wireDepth earlier a)
              (max (wireDepth earlier a) (wireDepth earlier b) + 1)
              (by omega) hdLt hHitLast.1
          have hCb : compressBits S k (wireDepth earlier b) <
              compressBits S k (max (wireDepth earlier a) (wireDepth earlier b) + 1) :=
            compressBits_lt_of_avoid S k (wireDepth earlier b)
              (max (wireDepth earlier a) (wireDepth earlier b) + 1)
              (by omega) hdLt hHitLast.2
          have iha := ih a
          have ihb := ih b
          omega
      | or a b =>
        simp only [residualDepth_snoc_or_last, wireDepth_snoc_or_last]
        split_ifs with hCut
        · exact Nat.zero_le _
        · have hHitLast : valiantGateHit (earlier.snoc (.or a b)) k S (Fin.last w) = false := by
            cases hV : valiantGateHit (earlier.snoc (.or a b)) k S (Fin.last w)
            · rfl
            · exact absurd (hHit (Fin.last w) hV) hCut
          simp only [valiantGateHit, Fin.lastCases_last, Bool.or_eq_false_iff] at hHitLast
          have hdLt : max (wireDepth earlier a) (wireDepth earlier b) + 1 < 2 ^ k := by
            simpa using hDepth (Fin.last w)
          have hCa : compressBits S k (wireDepth earlier a) <
              compressBits S k (max (wireDepth earlier a) (wireDepth earlier b) + 1) :=
            compressBits_lt_of_avoid S k (wireDepth earlier a)
              (max (wireDepth earlier a) (wireDepth earlier b) + 1)
              (by omega) hdLt hHitLast.1
          have hCb : compressBits S k (wireDepth earlier b) <
              compressBits S k (max (wireDepth earlier a) (wireDepth earlier b) + 1) :=
            compressBits_lt_of_avoid S k (wireDepth earlier b)
              (max (wireDepth earlier a) (wireDepth earlier b) + 1)
              (by omega) hdLt hHitLast.2
          have iha := ih a
          have ihb := ih b
          omega

/-- **Valiant Depth-Reduction Lemma**: for any `t ≤ k` (`0 < k`), every circuit of binary depth
`< 2 ^ k` admits a wire cut of size `≤ 2 * t * binaryGateCount c / k` reducing every residual cone
depth strictly below `2 ^ (k - t)`. -/
theorem valiantDepthReduction {n w : Nat} (c : Circuit n w) (k : Nat) (hk : 0 < k)
    (hDepth : ∀ u : Fin w, wireDepth c u < 2 ^ k) (t : Nat) (ht : t ≤ k) :
    ∃ cut : Fin w → Bool,
      keptCount n cut ≤ 2 * t * binaryGateCount c / k ∧
      ∀ u : Fin w, residualDepth c cut u < 2 ^ (k - t) := by
  obtain ⟨S, hCard, hSum⟩ := exists_subset_sum_le hk (valiantLevelCount c k) t ht
  refine ⟨valiantCut c k S, ?_, ?_⟩
  · have hKept := keptCount_valiantCut_le_sum c k S
    have hTotal := sum_valiantLevelCount_le c k hk
    have hMulKept : k * keptCount n (valiantCut c k S) ≤ 2 * t * binaryGateCount c := by
      calc
        k * keptCount n (valiantCut c k S)
          ≤ k * ∑ b ∈ S, valiantLevelCount c k b := Nat.mul_le_mul_left k hKept
        _ ≤ t * ∑ b : Fin k, valiantLevelCount c k b := hSum
        _ ≤ t * (2 * binaryGateCount c) := Nat.mul_le_mul_left t hTotal
        _ = 2 * t * binaryGateCount c := by ring
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hMulKept)
  · intro u
    let fPred : Nat → Bool := fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)
    have hRes := residualDepth_le_compressBits c k fPred (valiantCut c k S) hDepth
      (fun _ hv => hv) u
    have hComp := compressBits_lt fPred k (wireDepth c u)
    have hKeep : keepCount fPred k = k - t := by
      rw [keepCount_finset, hCard]
    rw [hKeep] at hComp
    exact lt_of_le_of_lt hRes hComp

theorem valiant_halving_cut {n w : Nat} (c : Circuit n w) (k : Nat) (hk : 1 ≤ k)
    (hDepth : ∀ u : Fin w, wireDepth c u < 2 ^ k) :
    ∃ cut : Fin w → Bool,
      keptCount n cut ≤ 2 * binaryGateCount c / k ∧
      ∀ u : Fin w, residualDepth c cut u < 2 ^ (k - 1) := by
  simpa using valiantDepthReduction c k (by omega) hDepth 1 hk

/-! ### 3. Universal Residual-Depth Block Compiler -/

/-- Non-dependent compiled prefix state for `compileResidualDepth`. Every wire's residual cone fits
inside `Fin (2 ^ H) → Fin (n + blocks)` while only inspecting the first
`2 ^ (residualDepth c cut u)` entries (`cone_local`). -/
structure DepthState {n w : Nat} (c : Circuit n w) (cut : Fin w → Bool) (H : Nat) where
  blocks : Nat
  bc : BlockCircuit n (2 ^ H) (n + blocks)
  blocks_eq : blocks = keptCount n cut
  wireIdx : Fin w → Fin (n + blocks)
  wireIdx_eval : ∀ x u, (u.val < n ∨ cut u = true) → bc.evalWires x (wireIdx u) = c.evalWires x u
  coneArgs : Fin w → Fin (2 ^ H) → Fin (n + blocks)
  coneEval : Fin w → (Fin (2 ^ H) → Bool) → Bool
  cone_correct : ∀ x u, coneEval u (fun j => bc.evalWires x (coneArgs u j)) = c.evalWires x u
  cone_local : ∀ u vals₁ vals₂,
    (∀ j : Fin (2 ^ H), j.val < 2 ^ (residualDepth c cut u) → vals₁ j = vals₂ j) →
    coneEval u vals₁ = coneEval u vals₂

def extendDepthState {n w : Nat} {earlier : Circuit n w} (g : Gate w)
    (cut : Fin (w + 1) → Bool) (H : Nat) (hn : 0 < n)
    (prev : DepthState earlier (cut ∘ Fin.castSucc) H)
    (coneArgsLast : Fin (2 ^ H) → Fin (n + prev.blocks))
    (coneEvalLast : (Fin (2 ^ H) → Bool) → Bool)
    (hLast : ∀ x, coneEvalLast (fun j => prev.bc.evalWires x (coneArgsLast j)) =
      (earlier.snoc g).evalWires x (Fin.last w))
    (hLocal : ¬(n ≤ w ∧ cut (Fin.last w) = true) → ∀ vals₁ vals₂,
      (∀ j : Fin (2 ^ H), j.val < 2 ^ (residualDepth (earlier.snoc g) cut (Fin.last w)) →
        vals₁ j = vals₂ j) →
      coneEvalLast vals₁ = coneEvalLast vals₂) :
    DepthState (earlier.snoc g) cut H :=
  let nw : Nat := n + prev.blocks
  if hKeep : n ≤ w ∧ cut (Fin.last w) = true then
    let newBc : BlockCircuit n (2 ^ H) (n + (prev.blocks + 1)) :=
      prev.bc.snoc coneArgsLast coneEvalLast
    { blocks := prev.blocks + 1
      bc := newBc
      blocks_eq := by simp [keptCount_snoc, hKeep, prev.blocks_eq]
      wireIdx := Fin.lastCases (Fin.last nw) (fun q => (prev.wireIdx q).castSucc)
      wireIdx_eval := fun x u hu => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          dsimp only [newBc, BlockCircuit.evalWires]
          rw [Fin.snoc_last]
          exact hLast x
        | cast q =>
          rw [Fin.lastCases_castSucc]
          have hq : q.val < n ∨ (cut ∘ Fin.castSucc) q = true := by
            simpa [Fin.val_castSucc] using hu
          dsimp only [newBc, BlockCircuit.evalWires]
          rw [Fin.snoc_castSucc, prev.wireIdx_eval x q hq]
          simp [Circuit.evalWires, Fin.snoc_castSucc]
      coneArgs := Fin.lastCases (fun _ => Fin.last nw) (fun q j => (prev.coneArgs q j).castSucc)
      coneEval := Fin.lastCases (fun vals => vals ⟨0, Nat.two_pow_pos H⟩) prev.coneEval
      cone_correct := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, Fin.lastCases_last]
          dsimp only [newBc, BlockCircuit.evalWires]
          rw [Fin.snoc_last]
          exact hLast x
        | cast q =>
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          have hW : (fun j => newBc.evalWires x (prev.coneArgs q j).castSucc) =
              fun j => prev.bc.evalWires x (prev.coneArgs q j) := by
            funext j
            dsimp only [newBc, BlockCircuit.evalWires]
            rw [Fin.snoc_castSucc]
          rw [hW, prev.cone_correct]
          simp [Circuit.evalWires, Fin.snoc_castSucc]
      cone_local := fun u vals₁ vals₂ hAgree => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact hAgree ⟨0, Nat.two_pow_pos H⟩ (Nat.two_pow_pos _)
        | cast q =>
          rw [Fin.lastCases_castSucc]
          rw [residualDepth_snoc_castSucc] at hAgree
          exact prev.cone_local q vals₁ vals₂ hAgree }
  else
    { blocks := prev.blocks
      bc := prev.bc
      blocks_eq := by simp [keptCount_snoc, hKeep, prev.blocks_eq]
      wireIdx := Fin.lastCases (⟨0, by omega⟩) prev.wireIdx
      wireIdx_eval := fun x u hu => by
        cases u using Fin.lastCases with
        | last =>
          exfalso
          have hge := earlier.inputs_le_wires
          rcases hu with huLt | hCutT
          · simp only [Fin.val_last] at huLt; omega
          · exact hKeep ⟨hge, hCutT⟩
        | cast q =>
          rw [Fin.lastCases_castSucc]
          have hq : q.val < n ∨ (cut ∘ Fin.castSucc) q = true := by
            simpa [Fin.val_castSucc] using hu
          simp [Circuit.evalWires, Fin.snoc_castSucc, prev.wireIdx_eval x q hq]
      coneArgs := Fin.lastCases coneArgsLast prev.coneArgs
      coneEval := Fin.lastCases coneEvalLast prev.coneEval
      cone_correct := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, Fin.lastCases_last]
          exact hLast x
        | cast q =>
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          simp [Circuit.evalWires, Fin.snoc_castSucc, prev.cone_correct]
      cone_local := fun u vals₁ vals₂ hAgree => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact hLocal hKeep vals₁ vals₂ hAgree
        | cast q =>
          rw [Fin.lastCases_castSucc]
          rw [residualDepth_snoc_castSucc] at hAgree
          exact prev.cone_local q vals₁ vals₂ hAgree }

/-- **Universal Residual-Depth Compiler**: compiles any circuit `c` with `residualDepth c cut u < H`
into a `2 ^ H`-input `BlockCircuit` with `keptCount n cut` blocks. -/
def compileResidualDepth {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (cut : Fin w → Bool) → (H : Nat) → (0 < H) → (0 < n) →
    (∀ u : Fin w, residualDepth c cut u < H) → DepthState c cut H
  | _, .inputsOnly, cut, H, _, _, _ =>
    { blocks := 0
      bc := BlockCircuit.inputsOnly
      blocks_eq := by
        unfold keptCount
        have hEmpty : Finset.univ.filter (fun u : Fin n => n ≤ u.val ∧ cut u = true) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          have := u.isLt
          omega
        rw [hEmpty, Finset.card_empty]
      wireIdx := fun u => u
      wireIdx_eval := fun _ _ _ => rfl
      coneArgs := fun u => (singleWireConeH H u).1
      coneEval := fun u => (singleWireConeH H u).2
      cone_correct := fun _ _ => rfl
      cone_local := fun _ _ _ hAgree => hAgree ⟨0, Nat.two_pow_pos H⟩ (Nat.two_pow_pos _) }
  | w + 1, .snoc earlier (.not a), cut, H, hH, hn, hRes =>
    let prev := compileResidualDepth earlier (cut ∘ Fin.castSucc) H hH hn fun q => by
      simpa using hRes q.castSucc
    extendDepthState (.not a) cut H hn prev (prev.coneArgs a) (fun vals => !(prev.coneEval a vals))
      (fun x => by
        have hEq := prev.cone_correct x a
        simpa [Circuit.evalWires, Gate.eval, Fin.snoc_last] using congrArg Bool.not hEq)
      (fun hNotKeep vals₁ vals₂ hAgree => by
        have hge := earlier.inputs_le_wires
        have hNotCut : cut (Fin.last w) = false := by
          cases hc : cut (Fin.last w)
          · rfl
          · exact absurd ⟨hge, hc⟩ hNotKeep
        simp only [residualDepth_snoc_not_last, hNotCut, Bool.false_eq_true, ↓reduceIte] at hAgree
        exact congrArg Bool.not (prev.cone_local a vals₁ vals₂ hAgree))
  | w + 1, .snoc earlier (.and a b), cut, H, hH, hn, hRes =>
    let prev := compileResidualDepth earlier (cut ∘ Fin.castSucc) H hH hn fun q => by
      simpa using hRes q.castSucc
    let da := residualDepth earlier (cut ∘ Fin.castSucc) a
    let db := residualDepth earlier (cut ∘ Fin.castSucc) b
    let t := max da db
    let ht : t + 1 ≤ H := by
      by_cases hCut : cut (Fin.last w) = true
      · have hResA : da < H := by simpa [da] using hRes a.castSucc
        have hResB : db < H := by simpa [db] using hRes b.castSucc
        omega
      · have hLast := hRes (Fin.last w)
        simp only [residualDepth_snoc_and_last, hCut] at hLast
        exact Nat.le_of_lt hLast
    let dummy : Fin (n + prev.blocks) := ⟨0, by omega⟩
    let combined := combineConesH H t ht dummy (· && ·)
      (prev.coneArgs a) (prev.coneArgs b) (prev.coneEval a) (prev.coneEval b)
    have hlLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ H), j.val < 2 ^ t → vals₁ j = vals₂ j) →
        prev.coneEval a vals₁ = prev.coneEval a vals₂ := fun vals₁ vals₂ hAgree =>
      prev.cone_local a vals₁ vals₂ fun j hj =>
        hAgree j (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (le_max_left da db)))
    have hrLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ H), j.val < 2 ^ t → vals₁ j = vals₂ j) →
        prev.coneEval b vals₁ = prev.coneEval b vals₂ := fun vals₁ vals₂ hAgree =>
      prev.cone_local b vals₁ vals₂ fun j hj =>
        hAgree j (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (le_max_right da db)))
    extendDepthState (.and a b) cut H hn prev combined.1 combined.2
      (fun x => by
        have hComb := eval_combineConesH H t ht dummy (· && ·)
          (prev.coneArgs a) (prev.coneArgs b) (prev.coneEval a) (prev.coneEval b)
          hlLocal hrLocal (prev.bc.evalWires x)
        have hL := prev.cone_correct x a
        have hR := prev.cone_correct x b
        simpa [Circuit.evalWires, Gate.eval, Fin.snoc_last] using
          hComb.trans (congrArg₂ (· && ·) hL hR))
      (fun hNotKeep vals₁ vals₂ hAgree => by
        have hge := earlier.inputs_le_wires
        have hNotCut : cut (Fin.last w) = false := by
          cases hc : cut (Fin.last w)
          · rfl
          · exact absurd ⟨hge, hc⟩ hNotKeep
        simp only [residualDepth_snoc_and_last, hNotCut, Bool.false_eq_true, ↓reduceIte] at hAgree
        exact local_combineConesH H t ht dummy (· && ·)
          (prev.coneArgs a) (prev.coneArgs b) (prev.coneEval a) (prev.coneEval b)
          hlLocal vals₁ vals₂ hAgree)
  | w + 1, .snoc earlier (.or a b), cut, H, hH, hn, hRes =>
    let prev := compileResidualDepth earlier (cut ∘ Fin.castSucc) H hH hn fun q => by
      simpa using hRes q.castSucc
    let da := residualDepth earlier (cut ∘ Fin.castSucc) a
    let db := residualDepth earlier (cut ∘ Fin.castSucc) b
    let t := max da db
    let ht : t + 1 ≤ H := by
      by_cases hCut : cut (Fin.last w) = true
      · have hResA : da < H := by simpa [da] using hRes a.castSucc
        have hResB : db < H := by simpa [db] using hRes b.castSucc
        omega
      · have hLast := hRes (Fin.last w)
        simp only [residualDepth_snoc_or_last, hCut] at hLast
        exact Nat.le_of_lt hLast
    let dummy : Fin (n + prev.blocks) := ⟨0, by omega⟩
    let combined := combineConesH H t ht dummy (· || ·)
      (prev.coneArgs a) (prev.coneArgs b) (prev.coneEval a) (prev.coneEval b)
    have hlLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ H), j.val < 2 ^ t → vals₁ j = vals₂ j) →
        prev.coneEval a vals₁ = prev.coneEval a vals₂ := fun vals₁ vals₂ hAgree =>
      prev.cone_local a vals₁ vals₂ fun j hj =>
        hAgree j (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (le_max_left da db)))
    have hrLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ H), j.val < 2 ^ t → vals₁ j = vals₂ j) →
        prev.coneEval b vals₁ = prev.coneEval b vals₂ := fun vals₁ vals₂ hAgree =>
      prev.cone_local b vals₁ vals₂ fun j hj =>
        hAgree j (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) (le_max_right da db)))
    extendDepthState (.or a b) cut H hn prev combined.1 combined.2
      (fun x => by
        have hComb := eval_combineConesH H t ht dummy (· || ·)
          (prev.coneArgs a) (prev.coneArgs b) (prev.coneEval a) (prev.coneEval b)
          hlLocal hrLocal (prev.bc.evalWires x)
        have hL := prev.cone_correct x a
        have hR := prev.cone_correct x b
        simpa [Circuit.evalWires, Gate.eval, Fin.snoc_last] using
          hComb.trans (congrArg₂ (· || ·) hL hR))
      (fun hNotKeep vals₁ vals₂ hAgree => by
        have hge := earlier.inputs_le_wires
        have hNotCut : cut (Fin.last w) = false := by
          cases hc : cut (Fin.last w)
          · rfl
          · exact absurd ⟨hge, hc⟩ hNotKeep
        simp only [residualDepth_snoc_or_last, hNotCut, Bool.false_eq_true, ↓reduceIte] at hAgree
        exact local_combineConesH H t ht dummy (· || ·)
          (prev.coneArgs a) (prev.coneArgs b) (prev.coneEval a) (prev.coneEval b)
          hlLocal vals₁ vals₂ hAgree)

/-- Compiles any `CircuitInstance n` equipped with a depth cut of residual depth `< H` into a
`BlockContractionCertificate source (2 ^ H)`. -/
def depthCutCertificate {n : Nat} (source : CircuitInstance n) (cut : Fin source.wires → Bool)
    (H : Nat) (hH : 0 < H) (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    BlockContractionCertificate source (2 ^ H) :=
  let cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  let hRes' : ∀ u : Fin source.wires, residualDepth source.circuit cut' u < H := fun u =>
    lt_of_le_of_lt (residualDepth_le_of_cut_imp source.circuit cut cut'
      (fun v hv => by simp [cut', hv]) u) (hRes u)
  let hn : 0 < n := source.circuit.inputs_pos_of_wire source.output
  let st := compileResidualDepth source.circuit cut' H hH hn hRes'
  let hOut : source.output.val < n ∨ cut' source.output = true := by
    by_cases hlt : source.output.val < n
    · exact Or.inl hlt
    · right; simp [cut', show n ≤ source.output.val by omega]
  { blocks := st.blocks
    bc := st.bc
    output := st.wireIdx source.output
    eval_eq := fun x => st.wireIdx_eval x source.output hOut }

theorem depthCutCertificate_blocks_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    (depthCutCertificate source cut H hH hRes).blocks ≤ keptCount n cut + 1 := by
  classical
  dsimp only [depthCutCertificate]
  set cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  set st := compileResidualDepth source.circuit cut' H hH
    (source.circuit.inputs_pos_of_wire source.output) _
  rw [st.blocks_eq]
  have hSub :
      Finset.univ.filter (fun u : Fin source.wires => n ≤ u.val ∧ cut' u = true) ⊆
        Finset.univ.filter (fun u : Fin source.wires => n ≤ u.val ∧ cut u = true) ∪
          {source.output} := by
    intro u hu
    obtain ⟨hGe, hC⟩ := (Finset.mem_filter.mp hu).2
    simp only [cut', Bool.or_eq_true, decide_eq_true_eq] at hC
    rcases hC with hCut | ⟨rfl, _⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGe, hCut⟩)
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  calc
    keptCount n cut'
      ≤ (Finset.univ.filter (fun u : Fin source.wires => n ≤ u.val ∧ cut u = true) ∪
          {source.output}).card := Finset.card_le_card hSub
    _ ≤ keptCount n cut + ({source.output} : Finset (Fin source.wires)).card :=
        Finset.card_union_le _ _
    _ = keptCount n cut + 1 := by simp

/-- Automatic Valiant-cut `BlockContractionCertificate` with block count
`≤ 2 * t * binaryGateCount / k + 1` and interface width `2 ^ (2 ^ (k - t))`. -/
noncomputable def valiantBlockCertificate {n : Nat} (source : CircuitInstance n)
    (k t : Nat) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ u : Fin source.wires, wireDepth source.circuit u < 2 ^ k) :
    BlockContractionCertificate source (2 ^ (2 ^ (k - t))) :=
  let hEx := valiantDepthReduction source.circuit k hk hDepth t ht
  depthCutCertificate source (Classical.choose hEx) (2 ^ (k - t)) (Nat.two_pow_pos _)
    (Classical.choose_spec hEx).2

theorem valiantBlockCertificate_blocks_le {n : Nat} (source : CircuitInstance n)
    (k t : Nat) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ u : Fin source.wires, wireDepth source.circuit u < 2 ^ k) :
    (valiantBlockCertificate source k t hk ht hDepth).blocks ≤
      2 * t * binaryGateCount source.circuit / k + 1 := by
  dsimp only [valiantBlockCertificate]
  have hBound := (Classical.choose_spec (valiantDepthReduction source.circuit k hk hDepth t ht)).1
  exact (depthCutCertificate_blocks_le _ _ _ _ _).trans (Nat.add_le_add_right hBound 1)

theorem depthCut_subexponential {n : Nat → Nat} (source : (i : Nat) → CircuitInstance (n i))
    (H : Nat) (hH : 0 < H) (cut : (i : Nat) → Fin (source i).wires → Bool)
    (hRes : ∀ i, ∀ u : Fin (source i).wires, residualDepth (source i).circuit (cut i) u < H)
    (hn : Tendsto n atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hCut : ∀ᶠ i in atTop,
      ((keptCount (n i) (cut i) + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C overheadDeg : ℝ) :
    (fun i => logTimeBudget (n i)
      (n i + (depthCutCertificate (source i) (cut i) H hH (hRes i)).blocks) C overheadDeg)
      =o[atTop] fun i => (n i : ℝ) := by
  refine block_contraction_subexponential source
    (fun i => depthCutCertificate (source i) (cut i) H hH (hRes i)) hn hc hα ?_ C overheadDeg
  filter_upwards [hCut] with i hi
  have hLe : ((depthCutCertificate (source i) (cut i) H hH (hRes i)).blocks : ℝ) ≤
      ((keptCount (n i) (cut i) + 1 : Nat) : ℝ) := by
    exact_mod_cast depthCutCertificate_blocks_le (source i) (cut i) H hH (hRes i)
  exact hLe.trans hi

/-! ### 4. General `strideCertificate` Crossing Lower Bound -/

theorem strideCertificate_blocks_ge_min_crossing {n : Nat} (source : CircuitInstance n)
    (h : Nat) (hh : 0 < h) (L : Nat)
    (hAll : ∀ r : Fin h, L ≤ (crossingWires source.circuit h r.val).card) :
    L ≤ (strideCertificate source h hh).blocks := by
  classical
  dsimp only [strideCertificate]
  set r : Fin h := Classical.choose (exists_stride_residue_le source.circuit h hh)
  set keep : Fin source.wires → Bool := fun u =>
    isCrossing source.circuit h r.val u || decide (u = source.output ∧ n ≤ u.val)
  set st := compileStride source.circuit h r.val hh
    (source.circuit.inputs_pos_of_wire source.output) keep _
  rw [st.blocks_eq]
  have hSub : crossingWires source.circuit h r.val ⊆
      Finset.univ.filter (fun u : Fin source.wires => n ≤ u.val ∧ keep u = true) := by
    intro u hu
    have hCr : isCrossing source.circuit h r.val u = true := (Finset.mem_filter.mp hu).2
    have hGe : n ≤ u.val := by
      simp only [isCrossing, decide_eq_true_eq] at hCr
      exact hCr.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGe, by simp [keep, hCr]⟩
  exact (hAll r).trans (Finset.card_le_card hSub)

/-! ### 5. Explicit $O(n \log n)$ Bounded-Fanout Skip-Wire Barrier (`SkipRing`) -/

namespace SkipRing

def prevCol (n col : Nat) : Nat :=
  if col = 0 then n - 1 else col - 1

theorem prevCol_lt {n col : Nat} (hn : 0 < n) (hc : col < n) : prevCol n col < n := by
  unfold prevCol
  split_ifs <;> omega

theorem succ_mod_eq_iff {n j col : Nat} (hj : j < n) (hc : col < n) :
    (j + 1) % n = col ↔ j = prevCol n col := by
  unfold prevCol
  by_cases hj1 : j + 1 < n
  · rw [Nat.mod_eq_of_lt hj1]
    split_ifs <;> omega
  · have hjEq : j + 1 = n := by omega
    rw [hjEq, Nat.mod_self]
    split_ifs <;> omega

def skipGate (k ℓ s j : Nat) (_hj : j < k + 1) :
    Gate (LayeredRing.ringWires (k + 1) ℓ + j) :=
  let n := k + 1
  have hnPos : 1 ≤ n := Nat.succ_pos k
  have hBase : LayeredRing.ringWires n ℓ = (ℓ + 1) * n := LayeredRing.ringWires_eq n ℓ
  let a : Fin (LayeredRing.ringWires n ℓ + j) := ⟨ℓ * n + j, by
    rw [hBase]
    have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
    omega⟩
  let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
  have hbLayerLe : bLayer ≤ ℓ := by
    dsimp [bLayer]
    split_ifs with hs
    · omega
    · exact le_rfl
  let b : Fin (LayeredRing.ringWires n ℓ + j) := ⟨bLayer * n + (j + 1) % n, by
    have hm : (j + 1) % n < n := Nat.mod_lt (j + 1) (Nat.succ_pos k)
    have hMulLe : bLayer * n ≤ ℓ * n := Nat.mul_le_mul_right n hbLayerLe
    rw [hBase]
    have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
    omega⟩
  if ℓ % 2 = 0 then .and a b else .or a b

def appendSkipRow (k ℓ s : Nat) :
    (j : Nat) → j ≤ k + 1 → Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ) →
      Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ + j)
  | 0, _, c => c
  | j + 1, hj, c => (appendSkipRow k ℓ s j (by omega) c).snoc (skipGate k ℓ s j (by omega))

def buildSkipRing (k : Nat) : (D s : Nat) → Circuit (k + 1) (LayeredRing.ringWires (k + 1) D)
  | 0, _ => Circuit.inputsOnly
  | D + 1, s => appendSkipRow k D s (k + 1) (le_refl _) (buildSkipRing k D s)

/-- Synchronous `D`-layer cyclic ring circuit on `n = k + 1` inputs with backward skip span `s`,
exact binary gate count `D * (k + 1)`, and max fanout `≤ 3`. -/
def source (k D s : Nat) : CircuitInstance (k + 1) where
  wires := LayeredRing.ringWires (k + 1) D
  circuit := buildSkipRing k D s
  output := ⟨LayeredRing.ringWires (k + 1) D - 1, by
    have hEq := LayeredRing.ringWires_eq (k + 1) D
    have hPos : 0 < (D + 1) * (k + 1) := Nat.mul_pos (Nat.succ_pos D) (Nat.succ_pos k)
    omega⟩

private theorem gateCount_appendSkipRow (k ℓ s : Nat)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ)) :
    ∀ j (hj : j ≤ k + 1), (appendSkipRow k ℓ s j hj c).gateCount = c.gateCount + j
  | 0, _ => rfl
  | j + 1, hj => by
    dsimp [appendSkipRow, skipGate]
    split_ifs <;> simp [Circuit.gateCount, gateCount_appendSkipRow k ℓ s c j (by omega), Nat.add_assoc]

theorem source_gateCount (k D s : Nat) :
    (source k D s).circuit.gateCount = D * (k + 1) := by
  dsimp [source]
  induction D with
  | zero => simp [buildSkipRing, Circuit.gateCount]
  | succ D ih =>
    change (appendSkipRow k D s (k + 1) (le_refl _) (buildSkipRing k D s)).gateCount =
      (D + 1) * (k + 1)
    rw [gateCount_appendSkipRow, ih]
    ring

private theorem binaryGateCount_snoc_ite {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    binaryGateCount (c.snoc (if P then .and a b else .or a b)) = binaryGateCount c + 1 := by
  by_cases hP : P
  · rw [ite_eq_left_iff.mpr (fun h => absurd hP h)]; rfl
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hP)]; rfl

private theorem binaryFanout_snoc_ite_last {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    binaryFanout (c.snoc (if P then .and a b else .or a b)) (Fin.last w) = 0 := by
  by_cases hP : P
  · simp [hP, binaryFanout_snoc_and_last]
  · simp [hP, binaryFanout_snoc_or_last]

private theorem binaryFanout_snoc_ite_castSucc {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b q : Fin w) :
    binaryFanout (c.snoc (if P then .and a b else .or a b)) q.castSucc =
      binaryFanout c q + if q = a ∨ q = b then 1 else 0 := by
  by_cases hP : P
  · simp [hP, binaryFanout_snoc_and_castSucc]
  · simp [hP, binaryFanout_snoc_or_castSucc]

private theorem wireDepth_snoc_ite_last {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    wireDepth (c.snoc (if P then .and a b else .or a b)) (Fin.last w) =
      max (wireDepth c a) (wireDepth c b) + 1 := by
  by_cases hP : P
  · simp [hP, wireDepth_snoc_and_last]
  · simp [hP, wireDepth_snoc_or_last]

private theorem maxBinaryReaderDepth_snoc_ite_castSucc {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b q : Fin w) :
    maxBinaryReaderDepth (c.snoc (if P then .and a b else .or a b)) q.castSucc =
      if q = a ∨ q = b then
        max (maxBinaryReaderDepth c q) (max (wireDepth c a) (wireDepth c b) + 1)
      else maxBinaryReaderDepth c q := by
  by_cases hP : P
  · simp [hP, maxBinaryReaderDepth_snoc_and_castSucc]
  · simp [hP, maxBinaryReaderDepth_snoc_or_castSucc]

private theorem binaryGateCount_appendSkipRow (k ℓ s : Nat)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ)) :
    ∀ j (hj : j ≤ k + 1), binaryGateCount (appendSkipRow k ℓ s j hj c) = binaryGateCount c + j
  | 0, _ => rfl
  | j + 1, hj => by
    change binaryGateCount ((appendSkipRow k ℓ s j (by omega) c).snoc (skipGate k ℓ s j (by omega))) =
      binaryGateCount c + (j + 1)
    dsimp [skipGate]
    rw [binaryGateCount_snoc_ite, binaryGateCount_appendSkipRow k ℓ s c j (by omega)]
    omega

theorem source_binaryGateCount (k D s : Nat) :
    binaryGateCount (source k D s).circuit = D * (k + 1) := by
  dsimp [source]
  induction D with
  | zero =>
    simp [buildSkipRing, binaryGateCount, unhitBinaryGates]
  | succ D ih =>
    change binaryGateCount (appendSkipRow k D s (k + 1) (le_refl _) (buildSkipRing k D s)) =
      (D + 1) * (k + 1)
    rw [binaryGateCount_appendSkipRow, ih]
    ring

private def rowFanoutBudget (n s ℓ j : Nat) (u : Nat) : Nat :=
  (if u / n < ℓ ∨ (u / n = ℓ ∧ u % n < j) then 1 else 0) +
  (if (s = 0 ∨ u / n + 1 < s) ∧ (u / n < ℓ ∨ (u / n = ℓ ∧ prevCol n (u % n) < j)) then 1 else 0) +
  (if 0 < s ∧ (u / n + s ≤ ℓ ∨ (u / n + s = ℓ + 1 ∧ prevCol n (u % n) < j)) then 1 else 0)

private theorem rowFanoutBudget_le_three (n s ℓ j u : Nat) :
    rowFanoutBudget n s ℓ j u ≤ 3 := by
  unfold rowFanoutBudget
  split_ifs <;> omega

private theorem rowFanoutBudget_succ_row (n s ℓ u : Nat) (hn : 0 < n) :
    rowFanoutBudget n s ℓ n u = rowFanoutBudget n s (ℓ + 1) 0 u := by
  unfold rowFanoutBudget
  have hMod : u % n < n := Nat.mod_lt u hn
  have hPrev : prevCol n (u % n) < n := prevCol_lt hn hMod
  have h1 : (u / n < ℓ ∨ (u / n = ℓ ∧ u % n < n)) ↔ (u / n < ℓ + 1 ∨ (u / n = ℓ + 1 ∧ u % n < 0)) := by
    constructor <;> intro h <;> rcases h with h | ⟨hA, hB⟩ <;> omega
  have h2 : (u / n < ℓ ∨ (u / n = ℓ ∧ prevCol n (u % n) < n)) ↔
      (u / n < ℓ + 1 ∨ (u / n = ℓ + 1 ∧ prevCol n (u % n) < 0)) := by
    constructor <;> intro h <;> rcases h with h | ⟨hA, hB⟩ <;> omega
  have h3 : (u / n + s ≤ ℓ ∨ (u / n + s = ℓ + 1 ∧ prevCol n (u % n) < n)) ↔
      (u / n + s ≤ ℓ + 1 ∨ (u / n + s = ℓ + 1 + 1 ∧ prevCol n (u % n) < 0)) := by
    constructor <;> intro h <;> rcases h with h | ⟨hA, hB⟩ <;> omega
  simp only [h1, h2, h3]

private theorem div_mod_layer {n L c : Nat} (hc : c < n) :
    (L * n + c) / n = L ∧ (L * n + c) % n = c := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  constructor
  · rw [Nat.add_comm (L * n) c, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm (L * n) c, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

private theorem appendSkipRow_fanout_inv (k ℓ s : Nat)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ))
    (hInv : ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ),
      binaryFanout c u ≤ rowFanoutBudget (k + 1) s ℓ 0 u.val) :
    ∀ j (hj : j ≤ k + 1),
      ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ + j),
        binaryFanout (appendSkipRow k ℓ s j hj c) u ≤ rowFanoutBudget (k + 1) s ℓ j u.val := by
  intro j
  induction j with
  | zero => intro _ u; exact hInv u
  | succ j ih =>
    intro hj u
    have ih' := ih (by omega)
    let n := k + 1
    let prev := appendSkipRow k ℓ s j (by omega) c
    have hn : 0 < n := Nat.succ_pos k
    have hjn : j < k + 1 := by omega
    have hBase : LayeredRing.ringWires n ℓ = (ℓ + 1) * n := LayeredRing.ringWires_eq n ℓ
    let a : Fin (LayeredRing.ringWires n ℓ + j) := ⟨ℓ * n + j, by
      rw [hBase]; dsimp [n]; nlinarith⟩
    let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
    have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
    let b : Fin (LayeredRing.ringWires n ℓ + j) := ⟨bLayer * n + (j + 1) % n, by
      have hm : (j + 1) % n < n := Nat.mod_lt (j + 1) hn
      have hMulLe : bLayer * n ≤ ℓ * n := Nat.mul_le_mul_right n hbLayerLe
      rw [hBase]; dsimp [n] at hm hMulLe ⊢; nlinarith⟩
    cases u using Fin.lastCases with
    | last =>
      have hBinZero : binaryFanout (prev.snoc (skipGate k ℓ s j (by omega))) (Fin.last _) = 0 := by
        dsimp [skipGate]
        exact binaryFanout_snoc_ite_last prev _ _ _
      change binaryFanout (prev.snoc (skipGate k ℓ s j (by omega))) (Fin.last _) ≤ _
      rw [hBinZero]
      exact Nat.zero_le _
    | cast q =>
      change binaryFanout (prev.snoc (skipGate k ℓ s j (by omega))) q.castSucc ≤ _
      have hFan : binaryFanout (prev.snoc (skipGate k ℓ s j (by omega))) q.castSucc =
          binaryFanout prev q + (if q = a ∨ q = b then 1 else 0) := by
        dsimp [skipGate]
        exact binaryFanout_snoc_ite_castSucc prev _ _ _ q
      rw [hFan]
      have hPrev : binaryFanout prev q ≤ rowFanoutBudget (k + 1) s ℓ j q.val := ih' q
      have hA : q = a ↔ q.val / n = ℓ ∧ q.val % n = j := by
        have haDM := div_mod_layer (L := ℓ) (show j < n from by dsimp [n]; exact hjn)
        constructor
        · intro hEq; subst hEq; simpa [a] using haDM
        · rintro ⟨hd, hm⟩
          apply Fin.ext
          have h1 := Nat.div_add_mod q.val n
          dsimp [a]
          rw [hd, hm, Nat.mul_comm] at h1
          exact h1.symm
      have hB : q = b ↔ q.val / n = bLayer ∧ prevCol n (q.val % n) = j := by
        have hbDM := div_mod_layer (L := bLayer) (Nat.mod_lt (j + 1) hn)
        constructor
        · intro hEq
          subst hEq
          have hd : b.val / n = bLayer := hbDM.1
          have hm : b.val % n = (j + 1) % n := hbDM.2
          refine ⟨hd, ?_⟩
          have hs := (succ_mod_eq_iff (show j < n from by dsimp [n]; exact hjn)
            (Nat.mod_lt b.val hn)).mp hm.symm
          exact hs.symm
        · rintro ⟨hd, hp⟩
          apply Fin.ext
          have hm : (j + 1) % n = q.val % n :=
            (succ_mod_eq_iff (show j < n from by dsimp [n]; exact hjn)
              (Nat.mod_lt q.val hn)).mpr hp.symm
          have h1 := Nat.div_add_mod q.val n
          dsimp [b]
          rw [hd, ← hm, Nat.mul_comm] at h1
          exact h1.symm
      have hDeltaA :
          (if q.val / n < ℓ ∨ (q.val / n = ℓ ∧ q.val % n < j) then 1 else 0) +
          (if q = a then 1 else 0) ≤
          (if q.val / n < ℓ ∨ (q.val / n = ℓ ∧ q.val % n < j + 1) then 1 else 0) := by
        by_cases hqa : q = a
        · obtain ⟨hd, hm⟩ := hA.mp hqa
          rw [ite_eq_left_iff.mpr (fun h => absurd hqa h), hd, hm]
          simp
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hqa), Nat.add_zero]
          split_ifs <;> omega
      have hDeltaB :
          ((if (s = 0 ∨ q.val / n + 1 < s) ∧
              (q.val / n < ℓ ∨ (q.val / n = ℓ ∧ prevCol n (q.val % n) < j)) then 1 else 0) +
           (if 0 < s ∧
              (q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j)) then 1 else 0)) +
          (if q = b then 1 else 0) ≤
          ((if (s = 0 ∨ q.val / n + 1 < s) ∧
              (q.val / n < ℓ ∨ (q.val / n = ℓ ∧ prevCol n (q.val % n) < j + 1)) then 1 else 0) +
           (if 0 < s ∧
              (q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j + 1)) then 1 else 0)) := by
        by_cases hqb : q = b
        · obtain ⟨hd, hp⟩ := hB.mp hqb
          rw [ite_eq_left_iff.mpr (fun h => absurd hqb h)]
          by_cases hCaseA : 0 < s ∧ s ≤ ℓ + 1
          · have hBL : bLayer = ℓ + 1 - s := by simp [bLayer, hCaseA]
            have hQDiv : q.val / n = ℓ + 1 - s := hd.trans hBL
            have hLayerSum : q.val / n + s = ℓ + 1 := by rw [hQDiv]; omega
            have hNotLe : ¬(q.val / n + s ≤ ℓ) := by rw [hLayerSum]; omega
            have hTerm2Eq :
                (if (s = 0 ∨ q.val / n + 1 < s) ∧
                    (q.val / n < ℓ ∨ (q.val / n = ℓ ∧ prevCol n (q.val % n) < j)) then 1 else 0) =
                (if (s = 0 ∨ q.val / n + 1 < s) ∧
                    (q.val / n < ℓ ∨ (q.val / n = ℓ ∧ prevCol n (q.val % n) < j + 1)) then 1 else 0) := by
              by_cases hs1 : s = 1
              · have hNot : ¬(s = 0 ∨ q.val / n + 1 < s) := by omega
                simp [hNot]
              · have hLt : q.val / n < ℓ := by rw [hQDiv]; omega
                simp [hLt]
            have hTerm3Old :
                (if 0 < s ∧
                    (q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j)) then 1 else 0) = 0 := by
              rw [hp]; simp [hNotLe]
            have hTerm3New :
                (if 0 < s ∧
                    (q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j + 1)) then 1 else 0) = 1 := by
              rw [hp]; simp [hCaseA.1, hLayerSum]
            omega
          · have hBL : bLayer = ℓ := by simp [bLayer, hCaseA]
            have hLayerEq : q.val / n = ℓ := hd.trans hBL
            have hS : s = 0 ∨ ℓ + 1 < s := by
              by_cases hs0 : s = 0
              · exact Or.inl hs0
              · right; omega
            have hTerm2Old :
                (if (s = 0 ∨ q.val / n + 1 < s) ∧
                    (q.val / n < ℓ ∨ (q.val / n = ℓ ∧ prevCol n (q.val % n) < j)) then 1 else 0) = 0 := by
              rw [hLayerEq, hp]; simp
            have hTerm2New :
                (if (s = 0 ∨ q.val / n + 1 < s) ∧
                    (q.val / n < ℓ ∨ (q.val / n = ℓ ∧ prevCol n (q.val % n) < j + 1)) then 1 else 0) = 1 := by
              rw [hLayerEq, hp]; simp [hS]
            have hTerm3Mono :
                (if 0 < s ∧
                    (q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j)) then 1 else 0) ≤
                (if 0 < s ∧
                    (q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j + 1)) then 1 else 0) := by
              split_ifs <;> omega
            omega
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hqb), Nat.add_zero]
          split_ifs <;> omega
      have hIndicator : (if q = a ∨ q = b then 1 else 0) ≤
          (if q = a then 1 else 0) + (if q = b then 1 else 0) := by
        split_ifs <;> omega
      dsimp only [rowFanoutBudget] at hPrev ⊢
      simp only [Fin.val_castSucc]
      dsimp only [n] at hDeltaA hDeltaB
      omega

private theorem buildSkipRing_fanout_inv (k D s : Nat) :
    ∀ u : Fin (LayeredRing.ringWires (k + 1) D),
      binaryFanout (buildSkipRing k D s) u ≤ rowFanoutBudget (k + 1) s D 0 u.val := by
  induction D with
  | zero =>
    intro u
    simp [buildSkipRing, binaryFanout]
  | succ D ih =>
    intro u
    have hRow := appendSkipRow_fanout_inv k D s (buildSkipRing k D s) ih (k + 1) (le_refl _) u
    have hRowEq := rowFanoutBudget_succ_row (k + 1) s D u.val (Nat.succ_pos k)
    change binaryFanout (appendSkipRow k D s (k + 1) (le_refl _) (buildSkipRing k D s)) u ≤ _
    omega

theorem source_fanout_le_three (k D s : Nat) (u : Fin (source k D s).wires) :
    binaryFanout (source k D s).circuit u ≤ 3 :=
  (buildSkipRing_fanout_inv k D s u).trans (rowFanoutBudget_le_three (k + 1) s D 0 u.val)

theorem source_hitting_cut_lower (k D s : Nat) (cut : Finset (Fin (source k D s).wires)) :
    D * (k + 1) ≤ unhitBinaryGatesOnCut (source k D s).circuit cut + 3 * cut.card := by
  have hBase := binaryGateCount_le_unhit_add_maxFanout (source k D s).circuit 3
    (source_fanout_le_three k D s) cut
  rwa [source_binaryGateCount] at hBase

private theorem appendSkipRow_depth_inv (k ℓ s : Nat)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ))
    (hDepth : ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ),
      wireDepth c u = u.val / (k + 1)) :
    ∀ j (hj : j ≤ k + 1),
      ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ + j),
        wireDepth (appendSkipRow k ℓ s j hj c) u = u.val / (k + 1) := by
  intro j
  induction j with
  | zero => intro _ u; exact hDepth u
  | succ j ih =>
    intro hj u
    have ihD := ih (by omega)
    let n := k + 1
    let prev := appendSkipRow k ℓ s j (by omega) c
    have hjn : j < k + 1 := by omega
    have hBase : LayeredRing.ringWires n ℓ = (ℓ + 1) * n := LayeredRing.ringWires_eq n ℓ
    let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
    have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
    let a : Fin (LayeredRing.ringWires n ℓ + j) := ⟨ℓ * n + j, by
      rw [hBase]; dsimp [n]; nlinarith⟩
    let b : Fin (LayeredRing.ringWires n ℓ + j) := ⟨bLayer * n + (j + 1) % n, by
      have hm := Nat.mod_lt (j + 1) (Nat.succ_pos k)
      have hMulLe : bLayer * n ≤ ℓ * n := Nat.mul_le_mul_right n hbLayerLe
      rw [hBase]; dsimp [n] at hm hMulLe ⊢; nlinarith⟩
    have haD : wireDepth prev a = ℓ := (ihD a).trans (div_mod_layer (by omega : j < n)).1
    have hbD : wireDepth prev b = bLayer := (ihD b).trans (div_mod_layer (Nat.mod_lt _ (Nat.succ_pos k))).1
    have hLastDiv : (LayeredRing.ringWires (k + 1) ℓ + j) / (k + 1) = ℓ + 1 := by
      change (LayeredRing.ringWires n ℓ + j) / n = ℓ + 1
      rw [hBase]
      exact (div_mod_layer (L := ℓ + 1) (by omega : j < n)).1
    cases u using Fin.lastCases with
    | last =>
      change wireDepth (prev.snoc (skipGate k ℓ s j (by omega))) (Fin.last _) = _
      dsimp [skipGate]
      rw [wireDepth_snoc_ite_last]
      change max (wireDepth prev a) (wireDepth prev b) + 1 = _
      rw [haD, hbD, hLastDiv]
      omega
    | cast q =>
      change wireDepth (prev.snoc (skipGate k ℓ s j (by omega))) q.castSucc = _
      rw [wireDepth_snoc_castSucc]
      exact ihD q

theorem source_wireDepth (k D s : Nat) (u : Fin (source k D s).wires) :
    wireDepth (source k D s).circuit u = u.val / (k + 1) := by
  dsimp [source]
  induction D with
  | zero =>
    have hu : u.val < k + 1 := u.isLt
    change wireDepth Circuit.inputsOnly u = _
    simp [Nat.div_eq_of_lt hu]
  | succ D ih =>
    exact appendSkipRow_depth_inv k D s (buildSkipRing k D s) ih (k + 1) (le_refl _) u

private theorem appendSkipRow_readerDepth_inv (k ℓ s : Nat) (hs : 0 < s)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ))
    (hD : ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ), wireDepth c u = u.val / (k + 1))
    (hM : ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ),
      u.val / (k + 1) + s ≤ ℓ → u.val / (k + 1) + s ≤ maxBinaryReaderDepth c u) :
    ∀ j (hj : j ≤ k + 1),
      ∀ u : Fin (LayeredRing.ringWires (k + 1) ℓ + j),
        (u.val / (k + 1) + s ≤ ℓ ∨ (u.val / (k + 1) + s = ℓ + 1 ∧ prevCol (k + 1) (u.val % (k + 1)) < j)) →
        u.val / (k + 1) + s ≤ maxBinaryReaderDepth (appendSkipRow k ℓ s j hj c) u := by
  intro j
  induction j with
  | zero =>
    intro _ u hu
    rcases hu with hLe | ⟨_, hLt0⟩
    · exact hM u hLe
    · omega
  | succ j ih =>
    intro hj u hu
    have ih' := ih (by omega)
    let n := k + 1
    let prev := appendSkipRow k ℓ s j (by omega) c
    have hn : 0 < n := Nat.succ_pos k
    have hjn : j < k + 1 := by omega
    have hBase : LayeredRing.ringWires n ℓ = (ℓ + 1) * n := LayeredRing.ringWires_eq n ℓ
    let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
    have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
    let a : Fin (LayeredRing.ringWires n ℓ + j) := ⟨ℓ * n + j, by
      rw [hBase]; dsimp [n]; nlinarith⟩
    let b : Fin (LayeredRing.ringWires n ℓ + j) := ⟨bLayer * n + (j + 1) % n, by
      have hm := Nat.mod_lt (j + 1) hn
      have hMulLe : bLayer * n ≤ ℓ * n := Nat.mul_le_mul_right n hbLayerLe
      rw [hBase]; dsimp [n] at hm hMulLe ⊢; nlinarith⟩
    have hPrevD := appendSkipRow_depth_inv k ℓ s c hD j (by omega)
    have haD : wireDepth prev a = ℓ := (hPrevD a).trans (div_mod_layer (by omega : j < n)).1
    have hbD : wireDepth prev b = bLayer := (hPrevD b).trans (div_mod_layer (Nat.mod_lt _ hn)).1
    cases u using Fin.lastCases with
    | last =>
      exfalso
      have hLastVal : (Fin.last ((LayeredRing.ringWires (k + 1) ℓ).add j)).val =
          (ℓ + 1) * (k + 1) + j := by
        simp [LayeredRing.ringWires_eq, Nat.add_eq]
      have hLastDiv : (Fin.last ((LayeredRing.ringWires (k + 1) ℓ).add j)).val / (k + 1) = ℓ + 1 := by
        rw [hLastVal]
        exact (div_mod_layer (L := ℓ + 1) hjn).1
      rw [hLastDiv] at hu
      omega
    | cast q =>
      change _ ≤ maxBinaryReaderDepth (prev.snoc (skipGate k ℓ s j (by omega))) q.castSucc
      have hGeOld : maxBinaryReaderDepth prev q ≤
          maxBinaryReaderDepth (prev.snoc (skipGate k ℓ s j (by omega))) q.castSucc :=
        maxBinaryReaderDepth_snoc_castSucc_ge prev _ q
      have hu' : q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j + 1) := by
        simpa [n] using hu
      by_cases hOld : q.val / n + s ≤ ℓ ∨ (q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) < j)
      · exact (ih' q (by simpa [n] using hOld)).trans hGeOld
      · have hHit : q.val / n + s = ℓ + 1 ∧ prevCol n (q.val % n) = j := by
          rcases hu' with hL | ⟨hEq, hLt⟩
          · exact absurd (Or.inl hL) hOld
          · have hNotLt : ¬(prevCol n (q.val % n) < j) := fun hP => hOld (Or.inr ⟨hEq, hP⟩)
            exact ⟨hEq, Nat.le_antisymm (Nat.lt_succ_iff.mp hLt) (Nat.le_of_not_lt hNotLt)⟩
        have hSLe : s ≤ ℓ + 1 := (Nat.le_add_left s (q.val / n)).trans_eq hHit.1
        have hBL : bLayer = ℓ + 1 - s := by simp [bLayer, hs, hSLe]
        have hEqB : q = b := by
          apply Fin.ext
          have hm : (j + 1) % n = q.val % n :=
            (succ_mod_eq_iff (show j < n from by dsimp [n]; exact hjn)
              (Nat.mod_lt q.val hn)).mpr hHit.2.symm
          have h1 := Nat.div_add_mod q.val n
          dsimp [b]
          have hDivBL : q.val / n = bLayer := by
            rw [hBL]
            exact Nat.eq_sub_of_add_eq hHit.1
          rw [hDivBL, ← hm, Nat.mul_comm] at h1
          exact h1.symm
        have hGateDepth : max (wireDepth prev a) (wireDepth prev b) + 1 = ℓ + 1 := by
          rw [haD, hbD]; omega
        dsimp [skipGate]
        rw [maxBinaryReaderDepth_snoc_ite_castSucc]
        change q.val / (k + 1) + s ≤ if q = a ∨ q = b then
            max (maxBinaryReaderDepth prev q) (max (wireDepth prev a) (wireDepth prev b) + 1)
          else maxBinaryReaderDepth prev q
        rw [ite_eq_left_iff.mpr (fun hNot => absurd (Or.inr hEqB) hNot), hGateDepth]
        have hHitN : q.val / (k + 1) + s = ℓ + 1 := by simpa [n] using hHit.1
        exact le_trans (le_of_eq hHitN) (le_max_right _ _)

private theorem buildSkipRing_readerDepth_inv (k D s : Nat) (hs : 0 < s) :
    ∀ u : Fin (LayeredRing.ringWires (k + 1) D),
      u.val / (k + 1) + s ≤ D →
      u.val / (k + 1) + s ≤ maxBinaryReaderDepth (buildSkipRing k D s) u := by
  induction D with
  | zero =>
    intro u hu
    omega
  | succ D ih =>
    intro u hu
    have hD : ∀ v : Fin (LayeredRing.ringWires (k + 1) D),
        wireDepth (buildSkipRing k D s) v = v.val / (k + 1) :=
      source_wireDepth k D s
    have hRow := appendSkipRow_readerDepth_inv k D s hs (buildSkipRing k D s) hD ih (k + 1) (le_refl _) u
    have hPrem : u.val / (k + 1) + s ≤ D ∨
        (u.val / (k + 1) + s = D + 1 ∧ prevCol (k + 1) (u.val % (k + 1)) < k + 1) := by
      have hPrev : prevCol (k + 1) (u.val % (k + 1)) < k + 1 :=
        prevCol_lt (Nat.succ_pos k) (Nat.mod_lt _ (Nat.succ_pos k))
      omega
    exact hRow hPrem

theorem source_maxBinaryReaderDepth_ge (k D s : Nat) (hs : 0 < s)
    (u : Fin (source k D s).wires) (hu : u.val / (k + 1) + s ≤ D) :
    u.val / (k + 1) + s ≤ maxBinaryReaderDepth (source k D s).circuit u :=
  buildSkipRing_readerDepth_inv k D s hs u hu

theorem source_wireSpan_ge (k D s : Nat) (hs : 0 < s)
    (u : Fin (source k D s).wires) (hu : u.val / (k + 1) + s ≤ D) :
    s ≤ wireSpan (source k D s).circuit u := by
  have hD := source_wireDepth k D s u
  have hM := source_maxBinaryReaderDepth_ge k D s hs u hu
  unfold wireSpan
  omega

/-- Gate wires in layers `[1, D - s]`, each forwarded across skip distance `≥ s`. -/
def skipCore (k D s : Nat) : Finset (Fin (source k D s).wires) :=
  Finset.univ.filter fun u : Fin (source k D s).wires =>
    k + 1 ≤ u.val ∧ u.val / (k + 1) + s ≤ D

theorem skipCore_card (k D s : Nat) :
    (skipCore k D s).card = (D - s) * (k + 1) := by
  by_cases hDs : D ≤ s
  · have hEmpty : skipCore k D s = ∅ := by
      ext u
      simp only [skipCore, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro ⟨hGe, hLe⟩
      have hDivGe : 1 ≤ u.val / (k + 1) :=
        Nat.le_div_iff_mul_le (Nat.succ_pos k) |>.mpr (by simpa using hGe)
      omega
    rw [hEmpty, Finset.card_empty, Nat.sub_eq_zero_of_le hDs, Nat.zero_mul]
  · have hBase : (source k D s).wires = (D + 1) * (k + 1) := LayeredRing.ringWires_eq (k + 1) D
    let f : Fin (D - s) × Fin (k + 1) → Fin (source k D s).wires := fun p =>
      ⟨(p.1.val + 1) * (k + 1) + p.2.val, by
        rw [hBase]
        have hp1 : p.1.val + 1 ≤ D := by omega
        nlinarith [p.2.isLt]⟩
    have hCard : (skipCore k D s).card = (Finset.univ : Finset (Fin (D - s) × Fin (k + 1))).card := by
      refine (Finset.card_bij (fun p _ => f p) ?_ ?_ ?_).symm
      · intro p _
        simp only [skipCore, Finset.mem_filter, Finset.mem_univ, true_and, f]
        have hDM := div_mod_layer (L := p.1.val + 1) p.2.isLt
        refine ⟨?_, ?_⟩
        · have : 1 * (k + 1) ≤ (p.1.val + 1) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
          omega
        · rw [hDM.1]; omega
      · intro p₁ _ p₂ _ hEq
        have hv : (f p₁).val = (f p₂).val := congrArg Fin.val hEq
        dsimp [f] at hv
        have h1 := div_mod_layer (L := p₁.1.val + 1) p₁.2.isLt
        have h2 := div_mod_layer (L := p₂.1.val + 1) p₂.2.isLt
        have hDiv : ((p₁.1.val + 1) * (k + 1) + p₁.2.val) / (k + 1) =
            ((p₂.1.val + 1) * (k + 1) + p₂.2.val) / (k + 1) := by rw [hv]
        have hMod : ((p₁.1.val + 1) * (k + 1) + p₁.2.val) % (k + 1) =
            ((p₂.1.val + 1) * (k + 1) + p₂.2.val) % (k + 1) := by rw [hv]
        rw [h1.1, h2.1] at hDiv
        rw [h1.2, h2.2] at hMod
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext hMod)
      · intro u hu
        obtain ⟨hGe, hLe⟩ := (Finset.mem_filter.mp hu).2
        have hDivPos : 1 ≤ u.val / (k + 1) :=
          (Nat.le_div_iff_mul_le (Nat.succ_pos k)).mpr (by simpa using hGe)
        let p : Fin (D - s) × Fin (k + 1) :=
          (⟨u.val / (k + 1) - 1, by omega⟩, ⟨u.val % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩)
        refine ⟨p, Finset.mem_univ _, Fin.ext ?_⟩
        dsimp [f, p]
        have hSum : u.val / (k + 1) - 1 + 1 = u.val / (k + 1) := by omega
        rw [hSum, Nat.mul_comm (u.val / (k + 1)) (k + 1)]
        exact Nat.div_add_mod u.val (k + 1)
    simpa [Fintype.card_prod] using hCard

theorem source_totalTruncatedSpan_ge (k D s h : Nat) (hs : 0 < s) (hLe : h ≤ s) :
    h * ((D - s) * (k + 1)) ≤ totalTruncatedSpan (source k D s).circuit h := by
  have hSub : skipCore k D s ⊆ Finset.univ.filter (fun u : Fin (source k D s).wires => k + 1 ≤ u.val) := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩
  calc
    h * ((D - s) * (k + 1))
      = ∑ _ ∈ skipCore k D s, h := by rw [Finset.sum_const, smul_eq_mul, skipCore_card, Nat.mul_comm]
    _ ≤ ∑ u ∈ skipCore k D s, min h (wireSpan (source k D s).circuit u) := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hSpan := source_wireSpan_ge k D s hs u (Finset.mem_filter.mp hu).2.2
        exact le_min le_rfl (hLe.trans hSpan)
    _ ≤ totalTruncatedSpan (source k D s).circuit h :=
        Finset.sum_le_sum_of_subset hSub

theorem source_crossingWires_ge (k D s h : Nat) (hh : 0 < h) (hLe : h ≤ s) (r : Fin h) :
    (D - s) * (k + 1) ≤ (crossingWires (source k D s).circuit h r.val).card := by
  have hs : 0 < s := lt_of_lt_of_le hh hLe
  have hSub : skipCore k D s ⊆ crossingWires (source k D s).circuit h r.val := by
    intro u hu
    obtain ⟨hGe, hU⟩ := (Finset.mem_filter.mp hu).2
    have hD := source_wireDepth k D s u
    have hM := source_maxBinaryReaderDepth_ge k D s hs u hU
    have hPlus : wireDepth (source k D s).circuit u + h ≤
        maxBinaryReaderDepth (source k D s).circuit u := by omega
    have hStep : bucket h r.val (wireDepth (source k D s).circuit u) <
        bucket h r.val (maxBinaryReaderDepth (source k D s).circuit u) := by
      unfold bucket
      have h1 : (wireDepth (source k D s).circuit u + r.val) / h + 1 =
          (wireDepth (source k D s).circuit u + r.val + h) / h := by
        rw [Nat.add_div_right _ hh]
      have h2 : (wireDepth (source k D s).circuit u + r.val + h) / h ≤
          (maxBinaryReaderDepth (source k D s).circuit u + r.val) / h :=
        Nat.div_le_div_right (by omega)
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ⟨hGe, hStep⟩⟩
  calc
    (D - s) * (k + 1) = (skipCore k D s).card := (skipCore_card k D s).symm
    _ ≤ (crossingWires (source k D s).circuit h r.val).card := Finset.card_le_card hSub

theorem source_strideCertificate_blocks_ge (k D s h : Nat) (hh : 0 < h) (hLe : h ≤ s) :
    (D - s) * (k + 1) ≤ (strideCertificate (source k D s) h hh).blocks :=
  strideCertificate_blocks_ge_min_crossing (source k D s) h hh ((D - s) * (k + 1))
    (source_crossingWires_ge k D s h hh hLe)

/-- **`SkipRing` $O(n \log n)$ Barrier Against `StrideContraction`**: with logarithmic depth
`D i = Nat.log 2 (n i) + s`, `SkipRing` has `O(n log n)` binary gates and max fanout `≤ 3`, yet
`strideCertificate` cannot compress it into `O(n * (log n) ^ α)` blocks for any `α < 1`. -/
theorem source_escapes_stride_subexponential_window (k : Nat → Nat) (s h : Nat)
    (hh : 0 < h) (hLe : h ≤ s) (hk : Tendsto k atTop atTop) (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((strideCertificate (source (k i) (Nat.log 2 (k i + 1) + s) s) h hh).blocks : ℝ) ≤
        c * ((k i + 1 : Nat) : ℝ) * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ α) := by
  intro hEv
  let β : ℝ := max α 0
  have hβNonneg : 0 ≤ β := le_max_right α 0
  have hβLt : β < 1 := max_lt hα (by norm_num)
  have hSubPos : 0 < 1 - β := sub_pos.mpr hβLt
  let n : Nat → Nat := fun i => k i + 1
  let L : Nat → ℝ := fun i => Real.log ((n i : ℝ) + 16)
  have hnNat : Tendsto n atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hk b
      exact ⟨M, fun i hi => by have := hM i hi; dsimp [n]; omega⟩
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnNat
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  have hLRpow : Tendsto (fun i => (L i) ^ (1 - β)) atTop atTop :=
    (tendsto_rpow_atTop hSubPos).comp hL
  let K : ℝ := (max c 0 + 2) * Real.log 2
  have hK : ∀ᶠ i in atTop, K < (L i) ^ (1 - β) :=
    hLRpow.eventually_gt_atTop K
  have hN16 : ∀ᶠ i in atTop, 16 ≤ n i := hnNat.eventually_ge_atTop 16
  have hL1 : ∀ᶠ i in atTop, 1 ≤ L i := hL.eventually_ge_atTop 1
  obtain ⟨i, hEvI, hKI, hN16I, hL1I⟩ := (hEv.and (hK.and (hN16.and hL1))).exists
  have hBlocksGe : Nat.log 2 (n i) * n i ≤
      (strideCertificate (source (k i) (Nat.log 2 (n i) + s) s) h hh).blocks := by
    simpa [n, Nat.add_sub_cancel] using
      source_strideCertificate_blocks_ge (k i) (Nat.log 2 (n i) + s) s h hh hLe
  have hBlocksCast : (Nat.log 2 (n i) : ℝ) * (n i : ℝ) ≤
      c * (n i : ℝ) * (L i) ^ α := by
    have hLe : ((Nat.log 2 (n i) * n i : Nat) : ℝ) ≤
        ((strideCertificate (source (k i) (Nat.log 2 (n i) + s) s) h hh).blocks : ℝ) := by
      exact_mod_cast hBlocksGe
    push_cast at hLe
    exact hLe.trans hEvI
  have hnPos : (0 : ℝ) < (n i : ℝ) := by positivity
  have hLogLe : (Nat.log 2 (n i) : ℝ) ≤ max c 0 * (L i) ^ β := by
    have hRpowLe : (L i) ^ α ≤ (L i) ^ β := Real.rpow_le_rpow_of_exponent_le hL1I (le_max_left α 0)
    have hPow0 : 0 ≤ (L i) ^ α := by positivity
    have hStep1 : (Nat.log 2 (n i) : ℝ) * (n i : ℝ) ≤ max c 0 * (L i) ^ α * (n i : ℝ) := by
      have hMaxC : c * (n i : ℝ) * (L i) ^ α ≤ max c 0 * (n i : ℝ) * (L i) ^ α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left c 0) hnPos.le) hPow0
      calc (Nat.log 2 (n i) : ℝ) * (n i : ℝ)
          ≤ c * (n i : ℝ) * (L i) ^ α := hBlocksCast
        _ ≤ max c 0 * (n i : ℝ) * (L i) ^ α := hMaxC
        _ = max c 0 * (L i) ^ α * (n i : ℝ) := by ring
    have hStep2 : max c 0 * (L i) ^ α * (n i : ℝ) ≤ max c 0 * (L i) ^ β * (n i : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRpowLe (le_max_right c 0)) hnPos.le
    exact le_of_mul_le_mul_right (hStep1.trans hStep2) hnPos
  have hPowBound : (n i : ℝ) + 16 < (2 : ℝ) ^ (Nat.log 2 (n i) + 2) := by
    have hNatLt : n i < 2 ^ (Nat.log 2 (n i) + 1) :=
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n i)
    have hNat2 : n i + 16 < 2 ^ (Nat.log 2 (n i) + 2) := by
      rw [Nat.pow_succ]
      omega
    exact_mod_cast hNat2
  have hLLe : L i ≤ ((Nat.log 2 (n i) : ℝ) + 2) * Real.log 2 := by
    have hPosL : 0 < (n i : ℝ) + 16 := by positivity
    have hLog := Real.log_le_log hPosL hPowBound.le
    simpa [L, Real.log_pow] using hLog
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPowGe1 : 1 ≤ (L i) ^ β := Real.one_le_rpow hL1I hβNonneg
  have hPowPos : 0 < (L i) ^ β := lt_of_lt_of_le (by norm_num) hPowGe1
  have hLUpper : L i ≤ K * (L i) ^ β := by
    calc
      L i ≤ ((Nat.log 2 (n i) : ℝ) + 2) * Real.log 2 := hLLe
      _ ≤ (max c 0 * (L i) ^ β + 2) * Real.log 2 := by nlinarith
      _ ≤ (max c 0 * (L i) ^ β + 2 * (L i) ^ β) * Real.log 2 := by nlinarith
      _ = K * (L i) ^ β := by dsimp [K]; ring
  have hLSplit : L i = (L i) ^ (1 - β) * (L i) ^ β := by
    have hPos : 0 < L i := by linarith
    rw [← Real.rpow_add hPos, sub_add_cancel, Real.rpow_one]
  conv_lhs at hLUpper => rw [hLSplit]
  have hFinal : (L i) ^ (1 - β) ≤ K := le_of_mul_le_mul_right hLUpper hPowPos
  linarith

/-- In sharp contrast to `strideCertificate`, `valiantBlockCertificate` ignores `wireSpan` / `s`:
on `SkipRing.source k D s` with `D < 2 ^ kBit`, its block bound depends only on `kBit, t, D, k`. -/
theorem source_valiant_span_invariant (k D s kBit t : Nat) (hkBit : 0 < kBit) (ht : t ≤ kBit)
    (hD : D < 2 ^ kBit) :
    (∀ u : Fin (source k D s).wires, wireDepth (source k D s).circuit u < 2 ^ kBit) ∧
    (valiantBlockCertificate (source k D s) kBit t hkBit ht (fun u => by
      rw [source_wireDepth]
      have hu : u.val < (D + 1) * (k + 1) := by
        simpa [source, LayeredRing.ringWires_eq] using u.isLt
      have hDiv : u.val / (k + 1) ≤ D :=
        Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mpr
          (by simpa [Nat.succ_mul] using hu))
      exact lt_of_le_of_lt hDiv hD)).blocks ≤
      2 * t * (D * (k + 1)) / kBit + 1 := by
  have hDepth : ∀ u : Fin (source k D s).wires, wireDepth (source k D s).circuit u < 2 ^ kBit := by
    intro u
    rw [source_wireDepth]
    have hu : u.val < (D + 1) * (k + 1) := by
      simpa [source, LayeredRing.ringWires_eq] using u.isLt
    have hDiv : u.val / (k + 1) ≤ D :=
      Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (Nat.succ_pos k)).mpr
        (by simpa [Nat.succ_mul] using hu))
    exact lt_of_le_of_lt hDiv hD
  refine ⟨hDepth, ?_⟩
  simpa [source_binaryGateCount] using
    valiantBlockCertificate_blocks_le (source k D s) kBit t hkBit ht hDepth

end SkipRing

end PvsNP
