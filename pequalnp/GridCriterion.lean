import PEqualNP.MetaComplexity.Helpers.Natural
import Mathlib.Logic.Equiv.Fin.Basic

/-! The counting hypothesis of L-meta-060 at the quadratic circuit cutoff. -/

namespace PvsNP.PEqualNPAudit

open PEqualNP.MetaComplexity

/-- The row parity predicate in the public grid criterion. -/
def RowEven (rows columns : ℕ) (T : List Bool) : Prop :=
  ∀ i : ℕ, i < rows →
    ((List.range columns).filter fun j => T.getD (i * columns + j) false = true).length % 2 = 0

private def completeRow {columns : ℕ} (x : Fin columns → Bool) : Fin (columns + 1) → Bool :=
  Fin.cases (decide ((List.ofFn x).count true % 2 = 1)) x

private def completeGrid {rows columns : ℕ} (x : Fin rows → Fin columns → Bool) : List Bool :=
  List.ofFn fun k : Fin (rows * (columns + 1)) =>
    let ij := finProdFinEquiv.symm k
    completeRow (x ij.1) ij.2

private theorem getD_completeGrid {rows columns : ℕ} (x : Fin rows → Fin columns → Bool)
    (i : Fin rows) (j : Fin (columns + 1)) :
    (completeGrid x).getD (i.val * (columns + 1) + j.val) false = completeRow (x i) j := by
  let k : Fin (rows * (columns + 1)) := finProdFinEquiv (i, j)
  have hval : k.val = i.val * (columns + 1) + j.val := by
    change j.val + (columns + 1) * i.val = _
    ac_rfl
  rw [← hval]
  have hk : k.val < (completeGrid x).length := by rw [completeGrid, List.length_ofFn]; exact k.isLt
  rw [List.getD_eq_getElem _ _ hk]
  simp only [completeGrid, List.getElem_ofFn]
  change completeRow (x (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 = _
  rw [show finProdFinEquiv.symm k = (i, j) from finProdFinEquiv.symm_apply_apply _]

private theorem completeGrid_injective (rows columns : ℕ) :
    Function.Injective (@completeGrid rows columns) := by
  intro x y hxy
  funext i j
  have h := congrArg (fun T : List Bool => T.getD (i.val * (columns + 1) + j.succ.val) false) hxy
  change (completeGrid x).getD _ false = (completeGrid y).getD _ false at h
  rw [getD_completeGrid x i j.succ, getD_completeGrid y i j.succ] at h
  exact h

private theorem rowEven_completeGrid {rows columns : ℕ} (x : Fin rows → Fin columns → Bool) :
    RowEven rows (columns + 1) (completeGrid x) := by
  intro i hi
  let value := fun j => (completeGrid x).getD (i * (columns + 1) + j) false
  let row := List.ofFn (completeRow (x ⟨i, hi⟩))
  have hrow : (List.range (columns + 1)).map value = row := by
    apply List.ext_getElem (by simp [row])
    intro j hj hrowj
    simp only [List.getElem_map, List.getElem_range, row, List.getElem_ofFn]
    exact getD_completeGrid x ⟨i, hi⟩ ⟨j, by simpa [row] using hrowj⟩
  have hcount : ((List.range (columns + 1)).filter fun j => value j = true).length =
      row.count true := by
    rw [← hrow, List.count_eq_countP, List.countP_eq_length_filter, List.filter_map]
    simp [Function.comp_def]
  change ((List.range (columns + 1)).filter fun j => value j = true).length % 2 = 0
  rw [hcount]
  simp only [row, List.ofFn_succ, completeRow, Fin.cases_zero, Fin.cases_succ, List.count_cons]
  split <;> simp_all
  omega

private theorem card_rowEven_lower (rows columns : ℕ) :
    2 ^ (rows * columns) ≤
      {T : List Bool | T.length = rows * (columns + 1) ∧ RowEven rows (columns + 1) T}.ncard := by
  have hsub : Set.range (@completeGrid rows columns) ⊆
      {T : List Bool | T.length = rows * (columns + 1) ∧ RowEven rows (columns + 1) T} := by
    rintro _ ⟨x, rfl⟩
    exact ⟨by simp [completeGrid], rowEven_completeGrid x⟩
  have h := Set.ncard_le_ncard hsub (Helpers.Natural.finite_len _ _)
  rw [Set.ncard_range_of_injective (completeGrid_injective rows columns)] at h
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, ← pow_mul, Nat.mul_comm columns rows] using h

/-- The strict counting hypothesis of L-meta-060 fails when the circuit-count exponent
is below the number of free bits in a row-even grid with at least two columns. -/
theorem grid_counting_obstruction (a b s : ℕ) (hb : 0 < b)
    (hcode : 2 * (a + b + s + 2) ≤ 2 ^ (a + b))
    (hsparse : 2 * (a + b) * s + 2 * (a + b) + 1 ≤ 2 ^ (a + b) - 2 ^ a) :
    2 ^ (2 ^ (a + b)) ≤
      2 ^ (2 ^ b - 1) *
        ({T : List Bool | T.length = 2 ^ (a + b) ∧ RowEven (2 ^ a) (2 ^ b) T ∧
          ¬ HasCircuitSize (a + b) (tableFun (a + b) T) s}.ncard * 2 ^ (2 ^ a) +
          {T : List Bool | T.length = 2 ^ (a + b) ∧
            HasCircuitSize (a + b) (tableFun (a + b) T) s}.ncard) := by
  let R := 2 ^ a
  let C := 2 ^ b
  let N := 2 ^ (a + b)
  let B := 2 * (a + b) * s + 2 * (a + b)
  let even : Set (List Bool) := {T | T.length = N ∧ RowEven R C T}
  let easy : Set (List Bool) := {T | T.length = N ∧ HasCircuitSize (a + b) (tableFun (a + b) T) s}
  let hard : Set (List Bool) := {T | T.length = N ∧ RowEven R C T ∧
    ¬ HasCircuitSize (a + b) (tableFun (a + b) T) s}
  have hN : N = R * C := pow_add 2 a b
  have hC : 2 ≤ C := Nat.le_pow hb
  have hcols : C - 1 + 1 = C := by omega
  have hfree : R * (C - 1) = N - R := by rw [hN, Nat.mul_sub_left_distrib, mul_one]
  have heven : 2 ^ (N - R) ≤ even.ncard := by
    have hc := card_rowEven_lower R (C - 1)
    rw [hfree, hcols, ← hN] at hc
    exact hc
  have heasy : easy.ncard ≤ 2 ^ B := Helpers.Natural.card_easy_tables (a + b) s hcode
  have hunion : even ⊆ hard ∪ easy := by
    intro T hT
    by_cases h : HasCircuitSize (a + b) (tableFun (a + b) T) s
    · exact Or.inr ⟨hT.1, h⟩
    · exact Or.inl ⟨hT.1, hT.2, h⟩
  have hfinite : (hard ∪ easy).Finite :=
    (Helpers.Natural.finite_len _ _).union (Helpers.Natural.finite_len _ _)
  have hcount := heven.trans ((Set.ncard_le_ncard hunion hfinite).trans (Set.ncard_union_le hard easy))
  have hhalf : 2 ^ B ≤ 2 ^ (N - R - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : 2 ^ (N - R) = 2 * 2 ^ (N - R - 1) := by
    rw [← pow_succ', show N - R - 1 + 1 = N - R by omega]
  have hhard : 2 ^ (N - R - 1) ≤ hard.ncard := by omega
  change 2 ^ N ≤ 2 ^ (C - 1) * (hard.ncard * 2 ^ R + easy.ncard)
  calc
    2 ^ N ≤ 2 ^ (C - 1 + (N - R - 1 + R)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ (C - 1) * (2 ^ (N - R - 1) * 2 ^ R) := by rw [pow_add, pow_add]
    _ ≤ _ := by gcongr; exact Nat.le_add_right_of_le (Nat.mul_le_mul_right _ hhard)

private theorem square_grid_growth (m : ℕ) (hm : 32 ≤ m) :
    2 * (2 * m * m ^ 2 + 2 * m + 1) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    rw [pow_succ' (2 : ℕ) m]
    apply le_trans _ (Nat.mul_le_mul_left 2 ih)
    nlinarith [Nat.mul_le_mul_right (m ^ 2) (show 4 ≤ m by omega),
      Nat.mul_le_mul_right m (show 4 ≤ m by omega)]

/-- For arity at least 32, every grid with at least two columns fails the hypothesis
at the quadratic cutoff. -/
theorem grid_counting_obstruction_square (a b : ℕ) (hab : 32 ≤ a + b) (hb : 0 < b) :
    2 ^ (2 ^ (a + b)) ≤
      2 ^ (2 ^ b - 1) *
        ({T : List Bool | T.length = 2 ^ (a + b) ∧ RowEven (2 ^ a) (2 ^ b) T ∧
          ¬ HasCircuitSize (a + b) (tableFun (a + b) T) ((a + b) ^ 2)}.ncard * 2 ^ (2 ^ a) +
          {T : List Bool | T.length = 2 ^ (a + b) ∧
            HasCircuitSize (a + b) (tableFun (a + b) T) ((a + b) ^ 2)}.ncard) := by
  apply grid_counting_obstruction a b ((a + b) ^ 2) hb
  · apply le_trans _ (square_grid_growth (a + b) hab)
    have hmul := Nat.mul_le_mul_right ((a + b) ^ 2) (show 1 ≤ a + b by omega)
    nlinarith
  · have hR : 2 ^ a ≤ 2 ^ (a + b - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hN : 2 ^ (a + b) = 2 * 2 ^ (a + b - 1) := by
      rw [← pow_succ', show a + b - 1 + 1 = a + b by omega]
    have hgrowth := square_grid_growth (a + b) hab
    omega

#print axioms grid_counting_obstruction_square

end PvsNP.PEqualNPAudit
