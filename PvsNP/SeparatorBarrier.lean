module

public import PvsNP.CircuitCSPTradeoff
public import PvsNP.BranchingCompression

@[expose] public section

/-!
# Balanced Vertex Separators: `SkipRing` Collapse vs. `ButterflyNet` Core

Formalizes the sharp separation inside the shallow $O(\log n)$-depth, $O(n \log n)$-gate
frontier identified in `CircuitCSP.lean` and `CircuitCSPTradeoff.lean`:

1. **`SkipRing` collapses in `2 ^ o(n)` exact `#3-SAT` time via balanced column separators**:
   - `SkipRing.separatorSOPCertificate`: partitioning `n = (m + 1) * (p + 1)` columns into
     `m + 1` blocks of width `p + 1` separated by `m + 1` column boundaries (`K = (m + 1) * (D + 1)`
     wires) decouples `SkipRing.source` into `m + 1` independent block-local pod circuits of size
     `≤ (D + 1) * (p + 1) + 2 * D + 8`.
   - `SkipRing.separator_subexponential`: choosing `p = Θ(log^2 n)` makes `K = o(n)` and pod
     size `O(log^3 n) = O(n)` (`o(n * sqrt(log n))`), yielding `sopLogTimeBudget = o(n)` (`2 ^ o(n)`).
2. **`ButterflyNet` defeats all existing local & depth compilers at `O(n log n)` gates, depth
   `log₂ n`, and max fanout `≤ 2`**:
   - `source_binaryGateCount` (`d * 2 ^ d`), `source_wireDepth` (`u.val / 2 ^ d`),
     `source_fanout_le_two` (`≤ 2`).
   - `source_hitting_cut_lower`: blocks `LiteralPropagation`.
   - `source_stride_blocks_ge`, `source_escapes_stride_subexponential_window`: blocks
     `StrideContraction`.
   - `source_escapes_valiant_shallow_wall`: blocks **all** Valiant cut schedules (`t ≥ 1`).
3. **Balanced vertex separator lower bound (`Ω(n)` congestion wall on `ButterflyNet`)**:
   - `CircuitEdge`, `UndirectedReachAvoiding`, `SeparatesInputs`: general undirected circuit
     graph separation over wire cuts `S : Finset (Fin w)`.
   - `bfly_walk_hits_separator` and `bfly_vertex_congestion_le`: every input pair `(x, y)` has a
     canonical butterfly-plus-return walk routed across `ButterflyNet`, with total pair
     congestion `≤ 2 * 2 ^ d` at every wire.
   - `butterfly_separator_lower_bound` (`A.card * B.card ≤ 2 * 2 ^ d * S.card`),
     `butterfly_balanced_separator_linear` (`2 ^ d ≤ 18 * S.card`),
     `butterfly_component_separator_linear` (any `≤ 2n/3` component partition requires
     `n ≤ 18 * S.card`), and `butterfly_escapes_sublinear_separator` (no `o(n)` balanced
     separator exists, isolating `ButterflyNet` as the true shallow `O(n log n)` core).
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. `SkipRing` Collapses in `2 ^ o(n)` Time via Balanced Column Separators -/

namespace SkipRing

/-- Total wires allocated in a width-`(p + 1)` pod block after layer `ℓ`, defined recursively
so `podGridWires p (ℓ + 1) = podGridWires p ℓ + (p + 1)` holds definitionally. -/
def podGridWires (p : Nat) : Nat → Nat
  | 0 => p + 4
  | ℓ + 1 => podGridWires p ℓ + (p + 1)

theorem podGridWires_eq (p : Nat) : ∀ ℓ, podGridWires p ℓ = (p + 4) + ℓ * (p + 1)
  | 0 => by simp [podGridWires]
  | ℓ + 1 => by
    rw [podGridWires, podGridWires_eq p ℓ, Nat.succ_mul]
    ring

/-- Wire index in `Fin (podGridWires p L)` for grid cell `(ℓ, r)` (`ℓ ≤ L`, `r < p + 1`). -/
def podWireIdx (p L ℓ r : Nat) (hℓ : ℓ ≤ L) (hr : r < p + 1) : Fin (podGridWires p L) :=
  ⟨if ℓ = 0 then r else (p + 4) + (ℓ - 1) * (p + 1) + r, by
    rw [podGridWires_eq p L]
    split_ifs with h0
    · omega
    · have hEq : (ℓ - 1) * (p + 1) + (p + 1) = ℓ * (p + 1) := by
        cases ℓ with
        | zero => exact absurd rfl h0
        | succ ℓ' => simp [Nat.succ_mul]
      have hMul : ℓ * (p + 1) ≤ L * (p + 1) := Nat.mul_le_mul_right _ hℓ
      omega⟩

/-- Helper constant wire in a pod block (`true` -> `p + 2`, `false` -> `p + 3`). -/
def podConstWire (p L : Nat) (b : Bool) : Fin (podGridWires p L) :=
  ⟨if b then p + 2 else p + 3, by
    rw [podGridWires_eq p L]
    split_ifs <;> omega⟩

/-- Builds helper constant wires `p + 1` (`not0`), `p + 2` (`true`), `p + 3` (`false`). -/
def initPodBase (p : Nat) : Circuit (p + 1) (podGridWires p 0) :=
  let c0 : Circuit (p + 1) (p + 1) := Circuit.inputsOnly
  let i0 : Fin (p + 1) := ⟨0, Nat.succ_pos p⟩
  let c1 := c0.snoc (.not i0)
  let c2 := c1.snoc (.or i0.castSucc (Fin.last (p + 1)))
  c2.snoc (.and i0.castSucc.castSucc (Fin.last (p + 1)).castSucc)

theorem initPodBase_eval_lt (p : Nat) (x : Fin (p + 1) → Bool) (r : Fin (p + 1)) :
    (initPodBase p).evalWires x (podWireIdx p 0 0 r.val (le_rfl) r.isLt) = x r := by
  dsimp [initPodBase, podWireIdx]
  change (((Circuit.inputsOnly.snoc (.not ⟨0, Nat.succ_pos p⟩)).snoc _).snoc _).evalWires x
      r.castSucc.castSucc.castSucc = x r
  simp [Circuit.evalWires, Fin.snoc_castSucc]

private theorem fin_snoc_zero {k : Nat} (f : Fin (k + 1) → Bool) (b : Bool) :
    Fin.snoc (α := fun _ => Bool) f b 0 = f 0 :=
  Fin.snoc_castSucc (α := fun _ => Bool) b f 0

theorem initPodBase_const (p : Nat) (x : Fin (p + 1) → Bool) (b : Bool) :
    (initPodBase p).evalWires x (podConstWire p 0 b) = b := by
  dsimp [initPodBase, podConstWire]
  have h0 : (⟨0, Nat.succ_pos p⟩ : Fin (p + 1)) = 0 := rfl
  cases b
  · change (((Circuit.inputsOnly.snoc (.not ⟨0, _⟩)).snoc _).snoc _).evalWires x
        (Fin.last (p + 3)) = false
    simp only [Circuit.evalWires, Gate.eval, Fin.snoc_last, Fin.snoc_castSucc, fin_snoc_zero, h0]
    cases x 0 <;> rfl
  · change (((Circuit.inputsOnly.snoc (.not ⟨0, _⟩)).snoc _).snoc _).evalWires x
        (Fin.last (p + 2)).castSucc = true
    simp only [Circuit.evalWires, Gate.eval, Fin.snoc_castSucc, Fin.snoc_last, fin_snoc_zero, h0]
    cases x 0 <;> rfl

/-- One gate in row `ℓ + 1`, local column `r` of pod `j` under pinned boundary `fixed`. -/
def podGate (m p D s ℓ r : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool) (j : Fin (m + 1))
    (hr : r < p + 1) : Gate (podGridWires p ℓ + r) :=
  let a : Fin (podGridWires p ℓ + r) :=
    ⟨(podWireIdx p ℓ ℓ r (le_rfl) hr).val,
      Nat.lt_of_lt_of_le (podWireIdx p ℓ ℓ r (le_rfl) hr).isLt (Nat.le_add_right _ _)⟩
  let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
  have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
  let b : Fin (podGridWires p ℓ + r) :=
    if hIn : r + 1 < p + 1 then
      ⟨(podWireIdx p ℓ bLayer (r + 1) hbLayerLe hIn).val,
        Nat.lt_of_lt_of_le (podWireIdx p ℓ bLayer (r + 1) hbLayerLe hIn).isLt
          (Nat.le_add_right _ _)⟩
    else
      let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
      let lIdx : Fin (D + 1) :=
        ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
      let valB := fixed (finProdFinEquiv (jNext, lIdx))
      ⟨(podConstWire p ℓ valB).val,
        Nat.lt_of_lt_of_le (podConstWire p ℓ valB).isLt (Nat.le_add_right _ _)⟩
  if ℓ % 2 = 0 then .and a b else .or a b

def appendPodRow (m p D s ℓ : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool) (j : Fin (m + 1)) :
    (r : Nat) → r ≤ p + 1 → Circuit (p + 1) (podGridWires p ℓ) →
      Circuit (p + 1) (podGridWires p ℓ + r)
  | 0, _, c => c
  | r + 1, hr, c =>
    (appendPodRow m p D s ℓ fixed j r (by omega) c).snoc (podGate m p D s ℓ r fixed j (by omega))

def buildPodGrid (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool) (j : Fin (m + 1)) :
    (L : Nat) → Circuit (p + 1) (podGridWires p L)
  | 0 => initPodBase p
  | L + 1 => appendPodRow m p D s L fixed j (p + 1) (le_rfl) (buildPodGrid m p D s fixed j L)

private theorem evalWires_snoc_lt {n w : Nat} (c : Circuit n w) (g : Gate w)
    (x : Fin n → Bool) (u : Fin w) :
    (c.snoc g).evalWires x u.castSucc = c.evalWires x u := by
  simp [Circuit.evalWires, Fin.snoc_castSucc]

theorem evalWires_appendPodRow_lt (m p D s ℓ : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (c : Circuit (p + 1) (podGridWires p ℓ)) (x : Fin (p + 1) → Bool) :
    ∀ r (hr : r ≤ p + 1) (u : Fin (podGridWires p ℓ)),
      (appendPodRow m p D s ℓ fixed j r hr c).evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩ = c.evalWires x u
  | 0, _, _ => rfl
  | r + 1, hr, u => by
    have ih := evalWires_appendPodRow_lt m p D s ℓ fixed j c x r (by omega) u
    change ((appendPodRow m p D s ℓ fixed j r (by omega) c).snoc _).evalWires x
        (Fin.castSucc ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩) = _
    rw [evalWires_snoc_lt]
    exact ih

theorem evalWires_appendPodRow_last (m p D s ℓ : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (c : Circuit (p + 1) (podGridWires p ℓ)) (x : Fin (p + 1) → Bool) :
    ∀ r (hr : r ≤ p + 1) (q : Nat) (hq : q < r),
      (appendPodRow m p D s ℓ fixed j r hr c).evalWires x ⟨podGridWires p ℓ + q, by omega⟩ =
        (let a : Fin (podGridWires p ℓ) := podWireIdx p ℓ ℓ q (le_rfl) (by omega)
         let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
         have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
         let b : Fin (podGridWires p ℓ) :=
           if hIn : q + 1 < p + 1 then podWireIdx p ℓ bLayer (q + 1) hbLayerLe hIn
           else
             let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
             let lIdx : Fin (D + 1) := ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
             podConstWire p ℓ (fixed (finProdFinEquiv (jNext, lIdx)))
         let gBool := if ℓ % 2 = 0 then Bool.and else Bool.or
         gBool (c.evalWires x a) (c.evalWires x b))
  | 0, _, _, hq => by omega
  | r + 1, hr, q, hq => by
    by_cases hqr : q < r
    · have ih := evalWires_appendPodRow_last m p D s ℓ fixed j c x r (by omega) q hqr
      change ((appendPodRow m p D s ℓ fixed j r (by omega) c).snoc _).evalWires x
          (Fin.castSucc ⟨podGridWires p ℓ + q, by omega⟩) = _
      rw [evalWires_snoc_lt]
      exact ih
    · have hEq : q = r := by omega
      subst hEq
      change ((appendPodRow m p D s ℓ fixed j q (by omega) c).snoc
          (podGate m p D s ℓ q fixed j (by omega))).evalWires x
          (Fin.last (podGridWires p ℓ + q)) = _
      dsimp [podGate]
      have hOld := evalWires_appendPodRow_lt m p D s ℓ fixed j c x q (by omega)
      have hA := hOld (podWireIdx p ℓ ℓ q (le_rfl) (by omega))
      let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
      have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
      by_cases hMod : ℓ % 2 = 0
      · simp only [hMod, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last]
        by_cases hIn : q + 1 < p + 1
        · simp only [hIn, ↓reduceDIte]
          have hB := hOld (podWireIdx p ℓ bLayer (q + 1) hbLayerLe hIn)
          exact congrArg₂ Bool.and hA hB
        · simp only [hIn, ↓reduceDIte]
          let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
          let lIdx : Fin (D + 1) := ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
          have hB := hOld (podConstWire p ℓ (fixed (finProdFinEquiv (jNext, lIdx))))
          exact congrArg₂ Bool.and hA hB
      · simp only [hMod, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last]
        by_cases hIn : q + 1 < p + 1
        · simp only [hIn, ↓reduceDIte]
          have hB := hOld (podWireIdx p ℓ bLayer (q + 1) hbLayerLe hIn)
          exact congrArg₂ Bool.or hA hB
        · simp only [hIn, ↓reduceDIte]
          let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
          let lIdx : Fin (D + 1) := ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
          have hB := hOld (podConstWire p ℓ (fixed (finProdFinEquiv (jNext, lIdx))))
          exact congrArg₂ Bool.or hA hB

theorem buildPodGrid_const (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (x : Fin (p + 1) → Bool) :
    ∀ L (b : Bool), (buildPodGrid m p D s fixed j L).evalWires x (podConstWire p L b) = b
  | 0, b => initPodBase_const p x b
  | L + 1, b => by
    have ih := buildPodGrid_const m p D s fixed j x L b
    have hOld := evalWires_appendPodRow_lt m p D s L fixed j (buildPodGrid m p D s fixed j L) x
      (p + 1) (le_rfl) (podConstWire p L b)
    have hEqW : podConstWire p (L + 1) b =
        ⟨(podConstWire p L b).val,
          Nat.lt_of_lt_of_le (podConstWire p L b).isLt (Nat.le_add_right _ _)⟩ :=
      Fin.ext rfl
    change (appendPodRow m p D s L fixed j (p + 1) (le_rfl)
      (buildPodGrid m p D s fixed j L)).evalWires x (podConstWire p (L + 1) b) = b
    rw [hEqW]
    exact hOld.trans ih

theorem buildPodGrid_eval_lt (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (x : Fin (p + 1) → Bool) :
    ∀ L ℓ r (hℓ : ℓ ≤ L) (hr : r < p + 1),
      (buildPodGrid m p D s fixed j (L + 1)).evalWires x
          (podWireIdx p (L + 1) ℓ r (Nat.le_succ_of_le hℓ) hr) =
        (buildPodGrid m p D s fixed j L).evalWires x (podWireIdx p L ℓ r hℓ hr) := by
  intro L ℓ r hℓ hr
  exact evalWires_appendPodRow_lt m p D s L fixed j (buildPodGrid m p D s fixed j L) x
    (p + 1) (le_rfl) (podWireIdx p L ℓ r hℓ hr)

theorem buildPodGrid_eval_last (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (x : Fin (p + 1) → Bool) (ℓ r : Nat) (hr : r < p + 1) :
    (buildPodGrid m p D s fixed j (ℓ + 1)).evalWires x
        (podWireIdx p (ℓ + 1) (ℓ + 1) r (le_rfl) hr) =
      (let a := (buildPodGrid m p D s fixed j ℓ).evalWires x (podWireIdx p ℓ ℓ r (le_rfl) hr)
       let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
       have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
       let b :=
         if hIn : r + 1 < p + 1 then
           (buildPodGrid m p D s fixed j ℓ).evalWires x (podWireIdx p ℓ bLayer (r + 1) hbLayerLe hIn)
         else
           let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
           let lIdx : Fin (D + 1) := ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
           fixed (finProdFinEquiv (jNext, lIdx))
       let gBool := if ℓ % 2 = 0 then Bool.and else Bool.or
       gBool a b) := by
  have hWireEq : (podWireIdx p (ℓ + 1) (ℓ + 1) r (le_rfl) hr).val = podGridWires p ℓ + r := by
    dsimp [podWireIdx]
    rw [podGridWires_eq p ℓ]
  have hStep := evalWires_appendPodRow_last m p D s ℓ fixed j (buildPodGrid m p D s fixed j ℓ) x
    (p + 1) (le_rfl) r hr
  let tgt : Fin (podGridWires p ℓ + (p + 1)) := ⟨podGridWires p ℓ + r, by omega⟩
  have hFinEq : podWireIdx p (ℓ + 1) (ℓ + 1) r (le_rfl) hr = tgt := Fin.ext hWireEq
  change (appendPodRow m p D s ℓ fixed j (p + 1) (le_rfl)
      (buildPodGrid m p D s fixed j ℓ)).evalWires x (podWireIdx p (ℓ + 1) (ℓ + 1) r (le_rfl) hr) = _
  rw [hFinEq, hStep]
  by_cases hIn : r + 1 < p + 1
  · simp only [hIn, ↓reduceDIte]
  · simp only [hIn, ↓reduceDIte]
    rw [buildPodGrid_const]

theorem buildPodGrid_eval_stable (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (x : Fin (p + 1) → Bool) :
    ∀ L₁ L₂ ℓ r (h1 : ℓ ≤ L₁) (h2 : ℓ ≤ L₂) (hr : r < p + 1),
      (buildPodGrid m p D s fixed j L₁).evalWires x (podWireIdx p L₁ ℓ r h1 hr) =
        (buildPodGrid m p D s fixed j L₂).evalWires x (podWireIdx p L₂ ℓ r h2 hr) := by
  have hMono : ∀ L ℓ r (h : ℓ ≤ L) (hr : r < p + 1),
      (buildPodGrid m p D s fixed j L).evalWires x (podWireIdx p L ℓ r h hr) =
        (buildPodGrid m p D s fixed j ℓ).evalWires x (podWireIdx p ℓ ℓ r (le_rfl) hr) := by
    intro L ℓ r h hr
    induction L with
    | zero =>
      have h0 : ℓ = 0 := by omega
      subst h0
      rfl
    | succ L ih =>
      by_cases hEq : ℓ = L + 1
      · subst hEq; rfl
      · have hLe : ℓ ≤ L := by omega
        exact (buildPodGrid_eval_lt m p D s fixed j x L ℓ r hLe hr).trans (ih hLe)
  intro L₁ L₂ ℓ r h1 h2 hr
  rw [hMono L₁ ℓ r h1 hr, hMono L₂ ℓ r h2 hr]

/-- Result of appending equality checks onto a pod circuit, carrying `w ≤ w'`. -/
structure CheckAcc (p w : Nat) where
  w' : Nat
  circuit : Circuit (p + 1) w'
  acc : Fin w'
  le : w ≤ w'

/-- Appends one equality check `(c.evalWires x target == expected)` onto `acc`. -/
def appendCheckBit {p w : Nat} (c : Circuit (p + 1) w) (acc target : Fin w) (expected : Bool) :
    CheckAcc p w :=
  if expected then
    ⟨w + 1, c.snoc (.and acc target), Fin.last w, Nat.le_succ w⟩
  else
    let c1 := c.snoc (.not target)
    ⟨w + 2, c1.snoc (.and acc.castSucc (Fin.last w)), Fin.last (w + 1), by omega⟩

theorem evalWires_appendCheckBit_lt {p w : Nat} (c : Circuit (p + 1) w) (acc target : Fin w)
    (expected : Bool) (x : Fin (p + 1) → Bool) (u : Fin w) :
    let res := appendCheckBit c acc target expected
    res.circuit.evalWires x ⟨u.val, Nat.lt_of_lt_of_le u.isLt res.le⟩ = c.evalWires x u := by
  cases expected
  · dsimp [appendCheckBit]
    change ((c.snoc (.not target)).snoc _).evalWires x u.castSucc.castSucc = c.evalWires x u
    rw [evalWires_snoc_lt, evalWires_snoc_lt]
  · dsimp [appendCheckBit]
    exact evalWires_snoc_lt c _ x u

theorem evalWires_appendCheckBit_acc {p w : Nat} (c : Circuit (p + 1) w) (acc target : Fin w)
    (expected : Bool) (x : Fin (p + 1) → Bool) :
    let res := appendCheckBit c acc target expected
    res.circuit.evalWires x res.acc =
      (c.evalWires x acc && decide (c.evalWires x target = expected)) := by
  cases expected
  · dsimp [appendCheckBit]
    change ((c.snoc (.not target)).snoc (.and acc.castSucc (Fin.last w))).evalWires x
        (Fin.last (w + 1)) = _
    simp only [Circuit.evalWires, Gate.eval, Fin.snoc_last, Fin.snoc_castSucc]
    cases c.evalWires x acc <;> cases c.evalWires x target <;> rfl
  · dsimp [appendCheckBit]
    simp [Circuit.evalWires, Gate.eval, Fin.snoc_last]

/-- Sequentially ANDs equality checks `wire(ℓ, 0) == fixed(j, ℓ)` for `ℓ = 0..cMax - 1`. -/
def appendBoundaryChecks (m p D : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) :
    (cMax : Nat) → cMax ≤ D + 1 →
    (w : Nat) → (podGridWires p D ≤ w) →
    Circuit (p + 1) w → Fin w →
    CheckAcc p w
  | 0, _, w, _, c, acc => ⟨w, c, acc, le_rfl⟩
  | cMax + 1, hcMax, w, hw, c, acc =>
    let prev := appendBoundaryChecks m p D fixed j cMax (by omega) w hw c acc
    let hPrev : podGridWires p D ≤ prev.w' := hw.trans prev.le
    let tgt : Fin prev.w' :=
      ⟨(podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).val,
        Nat.lt_of_lt_of_le (podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).isLt hPrev⟩
    let expVal := fixed (finProdFinEquiv (j, ⟨cMax, by omega⟩))
    let step := appendCheckBit prev.circuit prev.acc tgt expVal
    ⟨step.w', step.circuit, step.acc, prev.le.trans step.le⟩

theorem appendBoundaryChecks_wires_le (m p D : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) :
    ∀ cMax (hcMax : cMax ≤ D + 1) w (hw : podGridWires p D ≤ w)
      (c : Circuit (p + 1) w) (acc : Fin w),
      (appendBoundaryChecks m p D fixed j cMax hcMax w hw c acc).w' ≤ w + 2 * cMax
  | 0, _, w, _, _, _ => by simp [appendBoundaryChecks]
  | cMax + 1, hcMax, w, hw, c, acc => by
    have ih := appendBoundaryChecks_wires_le m p D fixed j cMax (by omega) w hw c acc
    dsimp [appendBoundaryChecks, appendCheckBit]
    split_ifs <;> dsimp only <;> omega

theorem appendBoundaryChecks_eval_lt (m p D : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) :
    ∀ cMax (hcMax : cMax ≤ D + 1) w (hw : podGridWires p D ≤ w)
      (c : Circuit (p + 1) w) (acc : Fin w) (x : Fin (p + 1) → Bool) (u : Fin w),
      (appendBoundaryChecks m p D fixed j cMax hcMax w hw c acc).circuit.evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt
          (appendBoundaryChecks m p D fixed j cMax hcMax w hw c acc).le⟩ =
        c.evalWires x u
  | 0, _, _, _, _, _, _, _ => rfl
  | cMax + 1, hcMax, w, hw, c, acc, x, u => by
    have ih := appendBoundaryChecks_eval_lt m p D fixed j cMax (by omega) w hw c acc x u
    dsimp [appendBoundaryChecks]
    let prev := appendBoundaryChecks m p D fixed j cMax (by omega) w hw c acc
    let hPrev : podGridWires p D ≤ prev.w' := hw.trans prev.le
    let tgt : Fin prev.w' :=
      ⟨(podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).val,
        Nat.lt_of_lt_of_le (podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).isLt hPrev⟩
    let expVal := fixed (finProdFinEquiv (j, ⟨cMax, by omega⟩))
    let u' : Fin prev.w' := ⟨u.val, Nat.lt_of_lt_of_le u.isLt prev.le⟩
    have hStep := evalWires_appendCheckBit_lt prev.circuit prev.acc tgt expVal x u'
    exact hStep.trans ih

theorem appendBoundaryChecks_eval_acc (m p D : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) :
    ∀ cMax (hcMax : cMax ≤ D + 1) w (hw : podGridWires p D ≤ w)
      (c : Circuit (p + 1) w) (acc : Fin w) (x : Fin (p + 1) → Bool),
      ((appendBoundaryChecks m p D fixed j cMax hcMax w hw c acc).circuit.evalWires x
          (appendBoundaryChecks m p D fixed j cMax hcMax w hw c acc).acc = true) ↔
        (c.evalWires x acc = true ∧
          ∀ ℓ (hℓ : ℓ < cMax),
            c.evalWires x ⟨(podWireIdx p D ℓ 0 (by omega) (Nat.succ_pos p)).val,
              Nat.lt_of_lt_of_le (podWireIdx p D ℓ 0 (by omega) (Nat.succ_pos p)).isLt hw⟩ =
              fixed (finProdFinEquiv (j, ⟨ℓ, by omega⟩)))
  | 0, _, w, hw, c, acc, x => by
    simp [appendBoundaryChecks]
  | cMax + 1, hcMax, w, hw, c, acc, x => by
    have ih := appendBoundaryChecks_eval_acc m p D fixed j cMax (by omega) w hw c acc x
    dsimp [appendBoundaryChecks]
    let prev := appendBoundaryChecks m p D fixed j cMax (by omega) w hw c acc
    have hPrev : podGridWires p D ≤ prev.w' := hw.trans prev.le
    let tgt : Fin prev.w' :=
      ⟨(podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).val,
        Nat.lt_of_lt_of_le (podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).isLt hPrev⟩
    let expVal := fixed (finProdFinEquiv (j, ⟨cMax, by omega⟩))
    have hStep := evalWires_appendCheckBit_acc prev.circuit prev.acc tgt expVal x
    have hTgtEq : prev.circuit.evalWires x tgt =
        c.evalWires x ⟨(podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).val,
          Nat.lt_of_lt_of_le (podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).isLt hw⟩ :=
      appendBoundaryChecks_eval_lt m p D fixed j cMax (by omega) w hw c acc x
        ⟨(podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).val,
          Nat.lt_of_lt_of_le (podWireIdx p D cMax 0 (by omega) (Nat.succ_pos p)).isLt hw⟩
    rw [hStep, Bool.and_eq_true, decide_eq_true_eq, ih, hTgtEq]
    constructor
    · rintro ⟨⟨hcAcc, hAll⟩, hLast⟩
      refine ⟨hcAcc, fun ℓ hℓ => ?_⟩
      by_cases hEq : ℓ = cMax
      · subst hEq; exact hLast
      · exact hAll ℓ (by omega)
    · rintro ⟨hcAcc, hAll⟩
      exact ⟨⟨hcAcc, fun ℓ hℓ => hAll ℓ (by omega)⟩, hAll cMax (Nat.lt_succ_self cMax)⟩

/-- Block-local pod circuit over `p + 1` inputs simulating block `j` of
`SkipRing.source (m * (p + 1) + p) D s` under pinned boundary `fixed`. -/
def podCircuit (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool) (j : Fin (m + 1)) :
    CircuitInstance (p + 1) :=
  let gridC := buildPodGrid m p D s fixed j D
  let initAcc := podConstWire p D true
  let chk := appendBoundaryChecks m p D fixed j (D + 1) (le_rfl) (podGridWires p D) (le_rfl)
    gridC initAcc
  if _hjLast : j.val = m then
    let outWire : Fin chk.w' :=
      ⟨(podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)).val,
        Nat.lt_of_lt_of_le (podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)).isLt chk.le⟩
    let step := appendCheckBit chk.circuit chk.acc outWire true
    ⟨step.w', step.circuit, step.acc⟩
  else
    ⟨chk.w', chk.circuit, chk.acc⟩

theorem podCircuit_wires_le (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) :
    (podCircuit m p D s fixed j).wires ≤ (D + 1) * (p + 1) + 2 * D + 8 := by
  dsimp [podCircuit]
  have hChk := appendBoundaryChecks_wires_le m p D fixed j (D + 1) (le_rfl) (podGridWires p D)
    (le_rfl) (buildPodGrid m p D s fixed j D) (podConstWire p D true)
  have hGridEq : podGridWires p D + 2 * (D + 1) = (D + 1) * (p + 1) + 2 * D + 5 := by
    rw [podGridWires_eq]
    ring
  split_ifs <;> dsimp [appendCheckBit] <;> omega

theorem podCircuit_eval_iff (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (j : Fin (m + 1)) (x : Fin (p + 1) → Bool) :
    (podCircuit m p D s fixed j).eval x = true ↔
      (∀ ℓ (hℓ : ℓ ≤ D),
        (buildPodGrid m p D s fixed j D).evalWires x (podWireIdx p D ℓ 0 hℓ (Nat.succ_pos p)) =
          fixed (finProdFinEquiv (j, ⟨ℓ, Nat.lt_succ_of_le hℓ⟩))) ∧
      (j.val = m →
        (buildPodGrid m p D s fixed j D).evalWires x
          (podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)) = true) := by
  let gridC := buildPodGrid m p D s fixed j D
  let initAcc := podConstWire p D true
  let chk := appendBoundaryChecks m p D fixed j (D + 1) (le_rfl) (podGridWires p D) (le_rfl)
    gridC initAcc
  have hInit : gridC.evalWires x initAcc = true := buildPodGrid_const m p D s fixed j x D true
  have hChkAcc := appendBoundaryChecks_eval_acc m p D fixed j (D + 1) (le_rfl)
    (podGridWires p D) (le_rfl) gridC initAcc x
  by_cases hjLast : j.val = m
  · let outWire : Fin chk.w' :=
      ⟨(podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)).val,
        Nat.lt_of_lt_of_le (podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)).isLt chk.le⟩
    have hPod : podCircuit m p D s fixed j =
        ⟨(appendCheckBit chk.circuit chk.acc outWire true).w',
          (appendCheckBit chk.circuit chk.acc outWire true).circuit,
          (appendCheckBit chk.circuit chk.acc outWire true).acc⟩ := by
      dsimp only [podCircuit]
      simp only [hjLast, ↓reduceDIte]
      rfl
    rw [hPod]
    dsimp [CircuitInstance.eval]
    have hStep := evalWires_appendCheckBit_acc chk.circuit chk.acc outWire true x
    have hOutEq : chk.circuit.evalWires x outWire =
        gridC.evalWires x (podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)) :=
      appendBoundaryChecks_eval_lt m p D fixed j (D + 1) (le_rfl) (podGridWires p D) (le_rfl)
        gridC initAcc x (podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p))
    rw [hStep, Bool.and_eq_true, decide_eq_true_eq, hChkAcc, hOutEq]
    simp only [hInit, true_and]
    constructor
    · rintro ⟨hAll, hOut⟩
      exact ⟨fun ℓ hℓ => hAll ℓ (Nat.lt_succ_of_le hℓ), fun _ => hOut⟩
    · rintro ⟨hAll, hOut⟩
      exact ⟨fun ℓ hℓ => hAll ℓ (Nat.lt_succ_iff.mp hℓ), hOut hjLast⟩
  · have hPod : podCircuit m p D s fixed j = ⟨chk.w', chk.circuit, chk.acc⟩ := by
      dsimp only [podCircuit]
      simp only [hjLast, ↓reduceDIte]
      rfl
    rw [hPod]
    dsimp [CircuitInstance.eval]
    rw [hChkAcc]
    simp only [hInit, true_and]
    constructor
    · intro hAll
      exact ⟨fun ℓ hℓ => hAll ℓ (Nat.lt_succ_of_le hℓ), fun h => absurd h hjLast⟩
    · rintro ⟨hAll, _⟩ ℓ hℓ
      exact hAll ℓ (Nat.lt_succ_iff.mp hℓ)

/-- Total column count `n = (m + 1) * (p + 1) = (m * (p + 1) + p) + 1`. -/
theorem blockCols_eq (m p : Nat) : (m * (p + 1) + p) + 1 = (m + 1) * (p + 1) := by ring

/-- Separator wire map pinning column `j * (p + 1)` at every layer `ℓ ∈ Fin (D + 1)`. -/
def separatorBoundary (m p D s : Nat) :
    Fin ((m + 1) * (D + 1)) → Fin (source (m * (p + 1) + p) D s).wires := fun idx =>
  let pPair := finProdFinEquiv.symm idx
  let j := pPair.1
  let ℓ := pPair.2
  ⟨ℓ.val * (m * (p + 1) + p + 1) + j.val * (p + 1), by
    change _ < LayeredRing.ringWires (m * (p + 1) + p + 1) D
    rw [LayeredRing.ringWires_eq, Nat.succ_mul]
    have hj : j.val * (p + 1) < m * (p + 1) + p + 1 := by
      have : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
      have : j.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
      omega
    have hℓLe : ℓ.val ≤ D := Nat.lt_succ_iff.mp ℓ.isLt
    have hMul : ℓ.val * (m * (p + 1) + p + 1) ≤ D * (m * (p + 1) + p + 1) :=
      Nat.mul_le_mul_right _ hℓLe
    omega⟩

/-- Helper lemma evaluating `appendSkipRow` at wires `< ringWires n ℓ`. -/
theorem evalWires_appendSkipRow_lt (k ℓ s : Nat)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ)) (x : Fin (k + 1) → Bool) :
    ∀ j (hj : j ≤ k + 1) (u : Fin (LayeredRing.ringWires (k + 1) ℓ)),
      (appendSkipRow k ℓ s j hj c).evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩ = c.evalWires x u
  | 0, _, _ => rfl
  | j + 1, hj, u => by
    have ih := evalWires_appendSkipRow_lt k ℓ s c x j (by omega) u
    change ((appendSkipRow k ℓ s j (by omega) c).snoc _).evalWires x
        (Fin.castSucc ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩) = _
    rw [evalWires_snoc_lt]
    exact ih

/-- Helper lemma evaluating `appendSkipRow` at layer `ℓ + 1`, column `q < r`. -/
theorem evalWires_appendSkipRow_last (k ℓ s : Nat)
    (c : Circuit (k + 1) (LayeredRing.ringWires (k + 1) ℓ)) (x : Fin (k + 1) → Bool) :
    ∀ r (hr : r ≤ k + 1) (q : Nat) (hq : q < r),
      (appendSkipRow k ℓ s r hr c).evalWires x ⟨LayeredRing.ringWires (k + 1) ℓ + q, by omega⟩ =
        (let n := k + 1
         have hBase : LayeredRing.ringWires n ℓ = (ℓ + 1) * n := LayeredRing.ringWires_eq n ℓ
         have hqn : q < n := by dsimp [n]; omega
         let a : Fin (LayeredRing.ringWires n ℓ) := ⟨ℓ * n + q, by
           rw [hBase]
           have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
           omega⟩
         let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
         have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
         let b : Fin (LayeredRing.ringWires n ℓ) := ⟨bLayer * n + (q + 1) % n, by
           have hm := Nat.mod_lt (q + 1) (Nat.succ_pos k)
           have hMulLe := Nat.mul_le_mul_right n hbLayerLe
           have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
           rw [hBase]
           dsimp [n] at hm hMulLe hMul ⊢
           omega⟩
         let gBool := if ℓ % 2 = 0 then Bool.and else Bool.or
         gBool (c.evalWires x a) (c.evalWires x b))
  | 0, _, _, hq => by omega
  | r + 1, hr, q, hq => by
    by_cases hqr : q < r
    · have ih := evalWires_appendSkipRow_last k ℓ s c x r (by omega) q hqr
      change ((appendSkipRow k ℓ s r (by omega) c).snoc _).evalWires x
          (Fin.castSucc ⟨LayeredRing.ringWires (k + 1) ℓ + q, by omega⟩) = _
      rw [evalWires_snoc_lt]
      exact ih
    · have hEq : q = r := by omega
      subst hEq
      change ((appendSkipRow k ℓ s q (by omega) c).snoc
          (skipGate k ℓ s q (by omega))).evalWires x
          (Fin.last (LayeredRing.ringWires (k + 1) ℓ + q)) = _
      dsimp [skipGate]
      have hOld := evalWires_appendSkipRow_lt k ℓ s c x q (by omega)
      have hBase : LayeredRing.ringWires (k + 1) ℓ = (ℓ + 1) * (k + 1) :=
        LayeredRing.ringWires_eq (k + 1) ℓ
      have hqn : q < k + 1 := by omega
      let a : Fin (LayeredRing.ringWires (k + 1) ℓ) := ⟨ℓ * (k + 1) + q, by
        rw [hBase]
        have hMul : ℓ * (k + 1) + (k + 1) = (ℓ + 1) * (k + 1) := by ring
        omega⟩
      let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
      have hbLayerLe : bLayer ≤ ℓ := by dsimp [bLayer]; split_ifs <;> omega
      let b : Fin (LayeredRing.ringWires (k + 1) ℓ) := ⟨bLayer * (k + 1) + (q + 1) % (k + 1), by
        have hm : (q + 1) % (k + 1) < k + 1 := Nat.mod_lt (q + 1) (Nat.succ_pos k)
        have hMulLe := Nat.mul_le_mul_right (k + 1) hbLayerLe
        have hMul : ℓ * (k + 1) + (k + 1) = (ℓ + 1) * (k + 1) := by ring
        rw [hBase]; omega⟩
      by_cases hMod : ℓ % 2 = 0
      · simp only [hMod, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last]
        exact congrArg₂ Bool.and (hOld a) (hOld b)
      · simp only [hMod, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last]
        exact congrArg₂ Bool.or (hOld a) (hOld b)

theorem buildSkipRing_eval_stable (k s : Nat) (x : Fin (k + 1) → Bool) :
    ∀ D₁ D₂ ℓ col (h1 : ℓ ≤ D₁) (h2 : ℓ ≤ D₂) (hc : col < k + 1),
      let w1 : Fin (LayeredRing.ringWires (k + 1) D₁) := ⟨ℓ * (k + 1) + col, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩
      let w2 : Fin (LayeredRing.ringWires (k + 1) D₂) := ⟨ℓ * (k + 1) + col, by
        rw [LayeredRing.ringWires_eq]; nlinarith⟩
      (buildSkipRing k D₁ s).evalWires x w1 = (buildSkipRing k D₂ s).evalWires x w2 := by
  have hMono : ∀ D ℓ col (h : ℓ ≤ D) (hc : col < k + 1),
      (buildSkipRing k D s).evalWires x ⟨ℓ * (k + 1) + col, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ =
        (buildSkipRing k ℓ s).evalWires x ⟨ℓ * (k + 1) + col, by
          rw [LayeredRing.ringWires_eq]; nlinarith⟩ := by
    intro D ℓ col h hc
    induction D with
    | zero =>
      have h0 : ℓ = 0 := by omega
      subst h0
      rfl
    | succ D ih =>
      by_cases hEq : ℓ = D + 1
      · subst hEq; rfl
      · have hLe : ℓ ≤ D := by omega
        have hLt := evalWires_appendSkipRow_lt k D s (buildSkipRing k D s) x (k + 1) (le_rfl)
          ⟨ℓ * (k + 1) + col, by rw [LayeredRing.ringWires_eq]; nlinarith⟩
        exact hLt.trans (ih hLe)
  intro D₁ D₂ ℓ col h1 h2 hc
  dsimp only
  rw [hMono D₁ ℓ col h1 hc, hMono D₂ ℓ col h2 hc]

theorem buildSkipRing_eval_succ (k D s ℓ col : Nat) (hℓ : ℓ < D) (hc : col < k + 1)
    (x : Fin (k + 1) → Bool) :
    let n := k + 1
    let srcW (L' c' : Nat) (hL' : L' ≤ D) (hc' : c' < n) : Fin (LayeredRing.ringWires n D) :=
      ⟨L' * n + c', by rw [LayeredRing.ringWires_eq]; nlinarith⟩
    let bLayer := if 0 < s ∧ s ≤ ℓ + 1 then ℓ + 1 - s else ℓ
    have hbLe : bLayer ≤ D := by dsimp [bLayer]; split_ifs <;> omega
    (buildSkipRing k D s).evalWires x (srcW (ℓ + 1) col hℓ hc) =
      (let gBool := if ℓ % 2 = 0 then Bool.and else Bool.or
       gBool
         ((buildSkipRing k D s).evalWires x (srcW ℓ col (by omega) hc))
         ((buildSkipRing k D s).evalWires x
           (srcW bLayer ((col + 1) % n) hbLe (Nat.mod_lt _ (Nat.succ_pos k))))) := by
  intro n srcW bLayer hbLe
  have h1 := buildSkipRing_eval_stable k s x D (ℓ + 1) (ℓ + 1) col hℓ (le_rfl) hc
  have h2 := buildSkipRing_eval_stable k s x D ℓ ℓ col (by omega) (le_rfl) hc
  have h3 := buildSkipRing_eval_stable k s x D ℓ bLayer ((col + 1) % n) hbLe
    (by dsimp [bLayer]; split_ifs <;> omega) (Nat.mod_lt _ (Nat.succ_pos k))
  dsimp only [srcW] at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  have hWireEq : (ℓ + 1) * n + col = LayeredRing.ringWires n ℓ + col := by
    rw [LayeredRing.ringWires_eq]
  have hStep := evalWires_appendSkipRow_last k ℓ s (buildSkipRing k ℓ s) x (k + 1) (le_rfl) col hc
  dsimp only [n] at hWireEq ⊢
  refine Eq.trans ?_ hStep
  congr 1
  exact Fin.ext hWireEq

private theorem col_succ_mod_block (m p : Nat) (j : Fin (m + 1)) (r : Nat) (hr : r < p + 1) :
    let n := m * (p + 1) + p + 1
    let col := j.val * (p + 1) + r
    (col + 1) % n =
      if r + 1 < p + 1 then j.val * (p + 1) + (r + 1)
      else ((j.val + 1) % (m + 1)) * (p + 1) := by
  intro n col
  have hn : n = (m + 1) * (p + 1) := blockCols_eq m p
  by_cases hIn : r + 1 < p + 1
  · simp only [hIn, ↓reduceIte]
    have hLt : col + 1 < n := by
      dsimp [col]
      rw [hn]
      have hj : j.val + 1 ≤ m + 1 := j.isLt
      nlinarith
    rw [Nat.mod_eq_of_lt hLt]
    dsimp [col]
    omega
  · simp only [hIn, ↓reduceIte]
    have hrEq : r + 1 = p + 1 := by omega
    have hEq : col + 1 = (j.val + 1) * (p + 1) := by dsimp [col]; nlinarith
    rw [hEq, hn]
    by_cases hj : j.val + 1 < m + 1
    · rw [Nat.mod_eq_of_lt (Nat.mul_lt_mul_of_pos_right hj (Nat.succ_pos p)), Nat.mod_eq_of_lt hj]
    · have hjEq : j.val + 1 = m + 1 := by omega
      rw [hjEq, Nat.mod_self, Nat.mod_self, Nat.zero_mul]

/-- Layer-by-layer agreement between the local pod grids and the global `SkipRing` circuit
whenever pinned boundary values match at all layers strictly below `D + 1`. -/
theorem podGrid_layer_eq_source (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (input : Fin (m * (p + 1) + p + 1) → Bool)
    (blockInput : Fin (m + 1) → Fin (p + 1) → Bool)
    (hInputs : ∀ (j : Fin (m + 1)) (r : Fin (p + 1)),
      blockInput j r = input ⟨j.val * (p + 1) + r.val, by
        have := j.isLt; have := r.isLt; nlinarith⟩)
    (hSrcFix : ∀ (j' : Fin (m + 1)) (ℓ' : Nat) (hℓ' : ℓ' ≤ D),
      (buildSkipRing (m * (p + 1) + p) D s).evalWires input
          ⟨ℓ' * (m * (p + 1) + p + 1) + j'.val * (p + 1), by
            rw [LayeredRing.ringWires_eq, Nat.succ_mul]
            have hjLe : j'.val * (p + 1) < m * (p + 1) + p + 1 := by
              have : j'.val ≤ m := Nat.lt_succ_iff.mp j'.isLt
              have : j'.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
              omega
            have hMul := Nat.mul_le_mul_right (m * (p + 1) + p + 1) hℓ'
            omega⟩ =
        fixed (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩))) :
    ∀ ℓ (hℓ : ℓ ≤ D) (j : Fin (m + 1)) (r : Fin (p + 1)),
      (buildPodGrid m p D s fixed j D).evalWires (blockInput j)
          (podWireIdx p D ℓ r.val hℓ r.isLt) =
        (buildSkipRing (m * (p + 1) + p) D s).evalWires input
          ⟨ℓ * (m * (p + 1) + p + 1) + (j.val * (p + 1) + r.val), by
            rw [LayeredRing.ringWires_eq, Nat.succ_mul]
            have hj : j.val * (p + 1) + r.val < m * (p + 1) + p + 1 := by
              have : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
              have : j.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
              have := r.isLt
              omega
            have hMul := Nat.mul_le_mul_right (m * (p + 1) + p + 1) hℓ
            omega⟩ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
    intro hℓ j r
    cases ℓ with
    | zero =>
      have hPod0 := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D 0 0 r.val hℓ (le_rfl) r.isLt
      have hInit := initPodBase_eval_lt p (blockInput j) r
      have hSrc0 := buildSkipRing_eval_stable (m * (p + 1) + p) s input D 0 0
        (j.val * (p + 1) + r.val) hℓ (le_rfl) (by have := j.isLt; have := r.isLt; nlinarith)
      dsimp [buildPodGrid] at hPod0
      rw [hPod0, hInit, hSrc0, hInputs j r]
      congr 1
      apply Fin.ext
      simp
    | succ ℓ' =>
      have hPodStable := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D (ℓ' + 1) (ℓ' + 1)
        r.val hℓ (le_rfl) r.isLt
      have hPodLast := buildPodGrid_eval_last m p D s fixed j (blockInput j) ℓ' r.val r.isLt
      have hSrcSucc := buildSkipRing_eval_succ (m * (p + 1) + p) D s ℓ'
        (j.val * (p + 1) + r.val) (by omega) (by have := j.isLt; have := r.isLt; nlinarith) input
      rw [hPodStable, hPodLast, hSrcSucc]
      have hA : (buildPodGrid m p D s fixed j ℓ').evalWires (blockInput j)
            (podWireIdx p ℓ' ℓ' r.val (le_rfl) r.isLt) =
          (buildSkipRing (m * (p + 1) + p) D s).evalWires input
            ⟨ℓ' * (m * (p + 1) + p + 1) + (j.val * (p + 1) + r.val), by
              rw [LayeredRing.ringWires_eq, Nat.succ_mul]
              have hj : j.val * (p + 1) + r.val < m * (p + 1) + p + 1 := by
                have : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
                have : j.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
                have := r.isLt
                omega
              have hMul : ℓ' * (m * (p + 1) + p + 1) ≤ D * (m * (p + 1) + p + 1) :=
                Nat.mul_le_mul_right _ (by omega)
              omega⟩ := by
        have hSt := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D ℓ' ℓ' r.val
          (by omega) (le_rfl) r.isLt
        rw [← hSt]
        exact ih ℓ' (Nat.lt_succ_self ℓ') (by omega) j r
      let bLayer := if 0 < s ∧ s ≤ ℓ' + 1 then ℓ' + 1 - s else ℓ'
      have hbLt : bLayer < ℓ' + 1 := by dsimp [bLayer]; split_ifs <;> omega
      have hbLeD : bLayer ≤ D := by omega
      have hbLeL : bLayer ≤ ℓ' := by omega
      have hB : (if hIn : r.val + 1 < p + 1 then
            (buildPodGrid m p D s fixed j ℓ').evalWires (blockInput j)
              (podWireIdx p ℓ' bLayer (r.val + 1) hbLeL hIn)
          else
            let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
            let lIdx : Fin (D + 1) := ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
            fixed (finProdFinEquiv (jNext, lIdx))) =
          (buildSkipRing (m * (p + 1) + p) D s).evalWires input
            ⟨bLayer * (m * (p + 1) + p + 1) + ((j.val * (p + 1) + r.val + 1) %
              (m * (p + 1) + p + 1)), by
              rw [LayeredRing.ringWires_eq, Nat.succ_mul]
              have hm : (j.val * (p + 1) + r.val + 1) % (m * (p + 1) + p + 1) <
                  m * (p + 1) + p + 1 := Nat.mod_lt _ (Nat.succ_pos _)
              have hMul := Nat.mul_le_mul_right (m * (p + 1) + p + 1) hbLeD
              omega⟩ := by
        have hModEq := col_succ_mod_block m p j r.val r.isLt
        by_cases hIn : r.val + 1 < p + 1
        · simp only [hIn, ↓reduceDIte, ↓reduceIte] at hModEq ⊢
          have hSt := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D ℓ' bLayer (r.val + 1)
            hbLeD hbLeL hIn
          rw [← hSt, ih bLayer hbLt hbLeD j ⟨r.val + 1, hIn⟩]
          congr 1
          apply Fin.ext
          exact congrArg (bLayer * (m * (p + 1) + p + 1) + ·) hModEq.symm
        · simp only [hIn, ↓reduceDIte, ↓reduceIte] at hModEq ⊢
          have hLbD : bLayer < D + 1 := by omega
          let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
          have hIdxEq : (⟨if bLayer < D + 1 then bLayer else 0, by split_ifs; all_goals omega⟩ :
                Fin (D + 1)) = ⟨bLayer, hLbD⟩ := by
            apply Fin.ext
            simp [hLbD]
          rw [hIdxEq, ← hSrcFix jNext bLayer hbLeD]
          congr 1
          apply Fin.ext
          dsimp [jNext]
          omega
      dsimp only
      rw [hA, hB]

/-- Opposite-direction layer-by-layer agreement: if every pod passes its column-0 checks
(`podEval (j, ℓ, 0) = fixed (j, ℓ)` for all `j, ℓ`), then every pod grid matches `SkipRing`
at every layer `ℓ ≤ D`. -/
theorem podGrid_layer_eq_source_of_podChecks (m p D s : Nat)
    (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (input : Fin (m * (p + 1) + p + 1) → Bool)
    (blockInput : Fin (m + 1) → Fin (p + 1) → Bool)
    (hInputs : ∀ (j : Fin (m + 1)) (r : Fin (p + 1)),
      blockInput j r = input ⟨j.val * (p + 1) + r.val, by
        have := j.isLt; have := r.isLt; nlinarith⟩)
    (hPodFix : ∀ (j' : Fin (m + 1)) (ℓ' : Nat) (hℓ' : ℓ' ≤ D),
      (buildPodGrid m p D s fixed j' D).evalWires (blockInput j')
          (podWireIdx p D ℓ' 0 hℓ' (Nat.succ_pos p)) =
        fixed (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩))) :
    ∀ ℓ (hℓ : ℓ ≤ D) (j : Fin (m + 1)) (r : Fin (p + 1)),
      (buildPodGrid m p D s fixed j D).evalWires (blockInput j)
          (podWireIdx p D ℓ r.val hℓ r.isLt) =
        (buildSkipRing (m * (p + 1) + p) D s).evalWires input
          ⟨ℓ * (m * (p + 1) + p + 1) + (j.val * (p + 1) + r.val), by
            rw [LayeredRing.ringWires_eq, Nat.succ_mul]
            have hj : j.val * (p + 1) + r.val < m * (p + 1) + p + 1 := by
              have : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
              have : j.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
              have := r.isLt
              omega
            have hMul := Nat.mul_le_mul_right (m * (p + 1) + p + 1) hℓ
            omega⟩ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
    intro hℓ j r
    cases ℓ with
    | zero =>
      have hPod0 := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D 0 0 r.val hℓ (le_rfl) r.isLt
      have hInit := initPodBase_eval_lt p (blockInput j) r
      have hSrc0 := buildSkipRing_eval_stable (m * (p + 1) + p) s input D 0 0
        (j.val * (p + 1) + r.val) hℓ (le_rfl) (by have := j.isLt; have := r.isLt; nlinarith)
      dsimp [buildPodGrid] at hPod0
      rw [hPod0, hInit, hSrc0, hInputs j r]
      congr 1
      apply Fin.ext
      simp
    | succ ℓ' =>
      have hPodStable := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D (ℓ' + 1) (ℓ' + 1)
        r.val hℓ (le_rfl) r.isLt
      have hPodLast := buildPodGrid_eval_last m p D s fixed j (blockInput j) ℓ' r.val r.isLt
      have hSrcSucc := buildSkipRing_eval_succ (m * (p + 1) + p) D s ℓ'
        (j.val * (p + 1) + r.val) (by omega) (by have := j.isLt; have := r.isLt; nlinarith) input
      rw [hPodStable, hPodLast, hSrcSucc]
      have hA : (buildPodGrid m p D s fixed j ℓ').evalWires (blockInput j)
            (podWireIdx p ℓ' ℓ' r.val (le_rfl) r.isLt) =
          (buildSkipRing (m * (p + 1) + p) D s).evalWires input
            ⟨ℓ' * (m * (p + 1) + p + 1) + (j.val * (p + 1) + r.val), by
              rw [LayeredRing.ringWires_eq, Nat.succ_mul]
              have hj : j.val * (p + 1) + r.val < m * (p + 1) + p + 1 := by
                have : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
                have : j.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
                have := r.isLt
                omega
              have hMul : ℓ' * (m * (p + 1) + p + 1) ≤ D * (m * (p + 1) + p + 1) :=
                Nat.mul_le_mul_right _ (by omega)
              omega⟩ := by
        have hSt := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D ℓ' ℓ' r.val
          (by omega) (le_rfl) r.isLt
        rw [← hSt]
        exact ih ℓ' (Nat.lt_succ_self ℓ') (by omega) j r
      let bLayer := if 0 < s ∧ s ≤ ℓ' + 1 then ℓ' + 1 - s else ℓ'
      have hbLt : bLayer < ℓ' + 1 := by dsimp [bLayer]; split_ifs <;> omega
      have hbLeD : bLayer ≤ D := by omega
      have hbLeL : bLayer ≤ ℓ' := by omega
      have hB : (if hIn : r.val + 1 < p + 1 then
            (buildPodGrid m p D s fixed j ℓ').evalWires (blockInput j)
              (podWireIdx p ℓ' bLayer (r.val + 1) hbLeL hIn)
          else
            let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
            let lIdx : Fin (D + 1) := ⟨if bLayer < D + 1 then bLayer else 0, by split_ifs <;> omega⟩
            fixed (finProdFinEquiv (jNext, lIdx))) =
          (buildSkipRing (m * (p + 1) + p) D s).evalWires input
            ⟨bLayer * (m * (p + 1) + p + 1) + ((j.val * (p + 1) + r.val + 1) %
              (m * (p + 1) + p + 1)), by
              rw [LayeredRing.ringWires_eq, Nat.succ_mul]
              have hm : (j.val * (p + 1) + r.val + 1) % (m * (p + 1) + p + 1) <
                  m * (p + 1) + p + 1 := Nat.mod_lt _ (Nat.succ_pos _)
              have hMul := Nat.mul_le_mul_right (m * (p + 1) + p + 1) hbLeD
              omega⟩ := by
        have hModEq := col_succ_mod_block m p j r.val r.isLt
        by_cases hIn : r.val + 1 < p + 1
        · simp only [hIn, ↓reduceDIte, ↓reduceIte] at hModEq ⊢
          have hSt := buildPodGrid_eval_stable m p D s fixed j (blockInput j) D ℓ' bLayer (r.val + 1)
            hbLeD hbLeL hIn
          rw [← hSt, ih bLayer hbLt hbLeD j ⟨r.val + 1, hIn⟩]
          congr 1
          apply Fin.ext
          exact congrArg (bLayer * (m * (p + 1) + p + 1) + ·) hModEq.symm
        · simp only [hIn, ↓reduceDIte, ↓reduceIte] at hModEq ⊢
          have hLbD : bLayer < D + 1 := by omega
          let jNext : Fin (m + 1) := ⟨(j.val + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
          have hIdxEq : (⟨if bLayer < D + 1 then bLayer else 0, by split_ifs; all_goals omega⟩ :
                Fin (D + 1)) = ⟨bLayer, hLbD⟩ := by
            apply Fin.ext
            simp [hLbD]
          rw [hIdxEq, ← hPodFix jNext bLayer hbLeD, ih bLayer hbLt hbLeD jNext ⟨0, Nat.succ_pos p⟩]
          congr 1
          apply Fin.ext
          dsimp [jNext]
          omega
      dsimp only
      rw [hA, hB]

theorem podCircuit_factored_iff (m p D s : Nat) (fixed : Fin ((m + 1) * (D + 1)) → Bool)
    (input : Fin (m * (p + 1) + p + 1) → Bool)
    (blockInput : Fin (m + 1) → Fin (p + 1) → Bool)
    (hInputs : ∀ (j : Fin (m + 1)) (r : Fin (p + 1)),
      blockInput j r = input ⟨j.val * (p + 1) + r.val, by
        have := j.isLt; have := r.isLt; nlinarith⟩) :
    ((source (m * (p + 1) + p) D s).eval input = true ∧
        (source (m * (p + 1) + p) D s).circuit.evalWires input ∘ separatorBoundary m p D s = fixed) ↔
      ∀ j : Fin (m + 1), (podCircuit m p D s fixed j).eval (blockInput j) = true := by
  let n := m * (p + 1) + p + 1
  have hOutIdx : (source (m * (p + 1) + p) D s).output =
      ⟨D * n + (m * (p + 1) + p), by
        dsimp [source, n]
        rw [LayeredRing.ringWires_eq, Nat.succ_mul]
        omega⟩ := by
    apply Fin.ext
    dsimp [source, n]
    rw [LayeredRing.ringWires_eq, Nat.succ_mul]
    omega
  have hSepWire : ∀ (j'' : Fin (m + 1)) (ℓ'' : Fin (D + 1)),
      (⟨(separatorBoundary m p D s (finProdFinEquiv (j'', ℓ''))).val, by
          have hW := (separatorBoundary m p D s (finProdFinEquiv (j'', ℓ''))).isLt
          exact hW⟩ : Fin (LayeredRing.ringWires n D)) =
        ⟨ℓ''.val * n + j''.val * (p + 1), by
          rw [LayeredRing.ringWires_eq, Nat.succ_mul]
          have : j''.val ≤ m := Nat.lt_succ_iff.mp j''.isLt
          have : j''.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
          have hj : j''.val * (p + 1) < n := by dsimp [n]; omega
          have hMul := Nat.mul_le_mul_right n (Nat.lt_succ_iff.mp ℓ''.isLt)
          omega⟩ := by
    intro j'' ℓ''
    apply Fin.ext
    change (finProdFinEquiv.symm (finProdFinEquiv (j'', ℓ''))).2.val * (m * (p + 1) + p + 1) +
        (finProdFinEquiv.symm (finProdFinEquiv (j'', ℓ''))).1.val * (p + 1) =
      ℓ''.val * n + j''.val * (p + 1)
    rw [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hSrcEval, hBound⟩ j
    have hSrcFix : ∀ (j' : Fin (m + 1)) (ℓ' : Nat) (hℓ' : ℓ' ≤ D),
        (buildSkipRing (m * (p + 1) + p) D s).evalWires input
            ⟨ℓ' * n + j'.val * (p + 1), by
              rw [LayeredRing.ringWires_eq, Nat.succ_mul]
              have hj : j'.val * (p + 1) < n := by
                have : j'.val ≤ m := Nat.lt_succ_iff.mp j'.isLt
                have : j'.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
                omega
              have hMul := Nat.mul_le_mul_right n hℓ'
              have hnEq : m * (p + 1) + p + 1 = n := rfl
              rw [hnEq]
              omega⟩ =
          fixed (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩)) := by
      intro j' ℓ' hℓ'
      have hb := congrFun hBound (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩))
      change (buildSkipRing (m * (p + 1) + p) D s).evalWires input
          ⟨(separatorBoundary m p D s (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩))).val,
            (separatorBoundary m p D s (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩))).isLt⟩ =
        fixed (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩)) at hb
      rw [hSepWire] at hb
      exact hb
    have hLayer := podGrid_layer_eq_source m p D s fixed input blockInput hInputs hSrcFix
    rw [podCircuit_eval_iff]
    constructor
    · intro ℓ hℓ
      rw [hLayer ℓ hℓ j ⟨0, Nat.succ_pos p⟩]
      exact hSrcFix j ℓ hℓ
    · intro hj
      rw [hLayer D (le_rfl) j ⟨p, Nat.lt_succ_self p⟩]
      have hOutW : (⟨D * n + (j.val * (p + 1) + p), by
          rw [LayeredRing.ringWires_eq, Nat.succ_mul]
          have : j.val ≤ m := Nat.lt_succ_iff.mp j.isLt
          have : j.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
          have hLt : j.val * (p + 1) + p < n := by dsimp [n]; omega
          omega⟩ :
          Fin (LayeredRing.ringWires n D)) = (source (m * (p + 1) + p) D s).output := by
        rw [hOutIdx]
        apply Fin.ext
        dsimp
        rw [hj]
      rw [hOutW]
      exact hSrcEval
  · intro hPods
    have hPodFix : ∀ (j' : Fin (m + 1)) (ℓ' : Nat) (hℓ' : ℓ' ≤ D),
        (buildPodGrid m p D s fixed j' D).evalWires (blockInput j')
            (podWireIdx p D ℓ' 0 hℓ' (Nat.succ_pos p)) =
          fixed (finProdFinEquiv (j', ⟨ℓ', Nat.lt_succ_of_le hℓ'⟩)) := fun j' ℓ' hℓ' =>
      ((podCircuit_eval_iff m p D s fixed j' (blockInput j')).mp (hPods j')).1 ℓ' hℓ'
    have hOutPod : (buildPodGrid m p D s fixed ⟨m, Nat.lt_succ_self m⟩ D).evalWires
        (blockInput ⟨m, Nat.lt_succ_self m⟩)
        (podWireIdx p D D p (le_rfl) (Nat.lt_succ_self p)) = true :=
      ((podCircuit_eval_iff m p D s fixed ⟨m, Nat.lt_succ_self m⟩
        (blockInput ⟨m, Nat.lt_succ_self m⟩)).mp (hPods ⟨m, Nat.lt_succ_self m⟩)).2 rfl
    have hLayer := podGrid_layer_eq_source_of_podChecks m p D s fixed input blockInput hInputs hPodFix
    constructor
    · dsimp [CircuitInstance.eval]
      rw [hOutIdx]
      have hEq := hLayer D (le_rfl) ⟨m, Nat.lt_succ_self m⟩ ⟨p, Nat.lt_succ_self p⟩
      rw [hOutPod] at hEq
      exact hEq.symm
    · funext idx
      rcases Equiv.surjective finProdFinEquiv idx with ⟨⟨j', ℓ'⟩, rfl⟩
      have hEq := hLayer ℓ'.val (Nat.lt_succ_iff.mp ℓ'.isLt) j' ⟨0, Nat.succ_pos p⟩
      have hFix := hPodFix j' ℓ'.val (Nat.lt_succ_iff.mp ℓ'.isLt)
      change (buildSkipRing (m * (p + 1) + p) D s).evalWires input
          ⟨(separatorBoundary m p D s (finProdFinEquiv (j', ℓ'))).val,
            (separatorBoundary m p D s (finProdFinEquiv (j', ℓ'))).isLt⟩ =
        fixed (finProdFinEquiv (j', ℓ'))
      rw [hSepWire]
      have hFinEq : (⟨ℓ'.val * n + j'.val * (p + 1), by
          rw [LayeredRing.ringWires_eq, Nat.succ_mul]
          have : j'.val ≤ m := Nat.lt_succ_iff.mp j'.isLt
          have : j'.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
          have hj : j'.val * (p + 1) < n := by dsimp [n]; omega
          have hℓLe : ℓ'.val ≤ D := Nat.lt_succ_iff.mp ℓ'.isLt
          have hMul := Nat.mul_le_mul_right n hℓLe
          omega⟩ :
          Fin (LayeredRing.ringWires n D)) =
          ⟨ℓ'.val * n + (j'.val * (p + 1) + 0), by
            rw [LayeredRing.ringWires_eq, Nat.succ_mul]
            have : j'.val ≤ m := Nat.lt_succ_iff.mp j'.isLt
            have : j'.val * (p + 1) ≤ m * (p + 1) := Nat.mul_le_mul_right _ this
            have hj : j'.val * (p + 1) + 0 < n := by dsimp [n]; omega
            have hℓLe : ℓ'.val ≤ D := Nat.lt_succ_iff.mp ℓ'.isLt
            have hMul := Nat.mul_le_mul_right n hℓLe
            omega⟩ := by
        apply Fin.ext; dsimp
      rw [hFinEq, ← hEq, hFix]

/-- Balanced column-separator `SumOfProductsCertificate` for `SkipRing.source`. -/
noncomputable def separatorSOPCertificate (m p D s : Nat) :
    SumOfProductsCertificate (source (m * (p + 1) + p) D s) where
  branches := 2 ^ ((m + 1) * (D + 1))
  factors := fun _ => m + 1
  vars := fun b j => (podCircuit m p D s ((cutBranchEquiv ((m + 1) * (D + 1))).symm b) j).wires
  formula := fun b j => (podCircuit m p D s ((cutBranchEquiv ((m + 1) * (D + 1))).symm b) j).cnf
  modelsEquiv := by
    let colEquiv : Fin (m + 1) × Fin (p + 1) ≃ Fin (m * (p + 1) + p + 1) :=
      finProdFinEquiv.trans (finCongr (blockCols_eq m p).symm)
    let blockAssemble : (Fin (m + 1) → Fin (p + 1) → Bool) ≃
        (Fin (m * (p + 1) + p + 1) → Bool) :=
      { toFun := fun g idx => g (colEquiv.symm idx).1 (colEquiv.symm idx).2
        invFun := fun input j r => input (colEquiv (j, r))
        left_inv := fun g => funext fun j => funext fun r => by simp
        right_inv := fun input => funext fun idx => congrArg input (colEquiv.apply_symm_apply idx) }
    have hBlockInput : ∀ (g : Fin (m + 1) → Fin (p + 1) → Bool) (j : Fin (m + 1)) (r : Fin (p + 1)),
        g j r = (blockAssemble g) ⟨j.val * (p + 1) + r.val, by
          have := j.isLt; have := r.isLt; nlinarith⟩ := fun g j r => by
      have hIdx : colEquiv (j, r) = ⟨j.val * (p + 1) + r.val, by
          have := j.isLt; have := r.isLt; nlinarith⟩ := by
        apply Fin.ext
        simp [colEquiv, finProdFinEquiv]
        ring
      rw [← hIdx]
      exact (congrFun (congrFun (blockAssemble.left_inv g) j) r).symm
    let branchSlice (fixed : Fin ((m + 1) * (D + 1)) → Bool) :=
      { input : Fin (m * (p + 1) + p + 1) → Bool //
        ∀ j : Fin (m + 1),
          (podCircuit m p D s fixed j).eval (fun r => blockAssemble.symm input j r) = true }
    let partEquiv : (Σ fixed : Fin ((m + 1) * (D + 1)) → Bool, branchSlice fixed) ≃
        (source (m * (p + 1) + p) D s).Accepting :=
      { toFun := fun ⟨fixed, input, hIn⟩ =>
          ⟨input, ((podCircuit_factored_iff m p D s fixed input
              (blockAssemble.symm input) fun j r => by
                have h := hBlockInput (blockAssemble.symm input) j r
                simpa using h).mpr hIn).1⟩
        invFun := fun input =>
          ⟨(source (m * (p + 1) + p) D s).circuit.evalWires input.val ∘
              separatorBoundary m p D s,
            ⟨input.val, ((podCircuit_factored_iff m p D s _ input.val
              (blockAssemble.symm input.val) fun j r => by
                have h := hBlockInput (blockAssemble.symm input.val) j r
                simpa using h).mp ⟨input.property, rfl⟩)⟩⟩
        left_inv := fun ⟨fixed, input, hIn⟩ => by
          have hFix := ((podCircuit_factored_iff m p D s fixed input
              (blockAssemble.symm input) fun j r => by
                have h := hBlockInput (blockAssemble.symm input) j r
                simpa using h).mpr hIn).2
          subst hFix
          rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    refine (Equiv.sigmaCongr (cutBranchEquiv ((m + 1) * (D + 1))).symm fun b => ?_).trans partEquiv
    let fixed := (cutBranchEquiv ((m + 1) * (D + 1))).symm b
    refine (Equiv.piCongrRight fun j =>
      (podCircuit m p D s fixed j).circuit.acceptingAssignmentsEquiv
        (podCircuit m p D s fixed j).output).trans ?_
    exact
      { toFun := fun f => ⟨blockAssemble (fun j => (f j).val), fun j => by
          change (podCircuit m p D s fixed j).eval _ = true
          have hBlk : (blockAssemble.symm (blockAssemble (fun j' => (f j').val))) j = (f j).val :=
            congrFun (blockAssemble.left_inv (fun j' => (f j').val)) j
          rw [hBlk]
          exact (f j).property⟩
        invFun := fun s j => ⟨blockAssemble.symm s.val j, s.property j⟩
        left_inv := fun f => funext fun j =>
          Subtype.ext (congrFun (blockAssemble.left_inv (fun j' => (f j').val)) j)
        right_inv := fun s => Subtype.ext (blockAssemble.right_inv s.val) }
  width := fun b j _ h =>
    (podCircuit m p D s ((cutBranchEquiv ((m + 1) * (D + 1))).symm b) j).circuit.encode_width
      (podCircuit m p D s ((cutBranchEquiv ((m + 1) * (D + 1))).symm b) j).output h

theorem separatorSOPCertificate_vars_le (m p D s : Nat)
    (b : Fin (separatorSOPCertificate m p D s).branches) (j : Fin (m + 1)) :
    (separatorSOPCertificate m p D s).vars b j ≤ (D + 1) * (p + 1) + 2 * D + 8 :=
  podCircuit_wires_le m p D s _ j

private theorem nat_log2_mul_le (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have h1 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
  have h2 : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) b
  have hMul : a * b < 2 ^ ((Nat.log 2 a + Nat.log 2 b + 1) + 1) := by
    calc
      a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ ((Nat.log 2 a + 1) + (Nat.log 2 b + 1)) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ ((Nat.log 2 a + Nat.log 2 b + 1) + 1) := by ring_nf
  exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (Nat.mul_ne_zero ha.ne' hb.ne')).mpr hMul)

private theorem nat_log2_sq_succ_le (t : Nat) (ht : 1 ≤ t) :
    Nat.log 2 (t ^ 2 + 1) ≤ 2 * t + 1 := by
  have h1 : t < 2 ^ t := Nat.lt_pow_self (by decide : 1 < 2)
  have hPow : t ^ 2 + 1 < 2 ^ (2 * t + 1 + 1) := by
    have hSq : t ^ 2 < 2 ^ (2 * t) := by
      calc
        t ^ 2 = t * t := by ring
        _ < 2 ^ t * 2 ^ t := Nat.mul_lt_mul'' h1 h1
        _ = 2 ^ (t + t) := (Nat.pow_add 2 t t).symm
        _ = 2 ^ (2 * t) := by ring_nf
    have h2 : 2 ^ (2 * t) + 1 < 2 ^ (2 * t + 2) := by
      have : 1 ≤ 2 ^ (2 * t) := Nat.one_le_two_pow
      rw [Nat.pow_succ, Nat.pow_succ]
      omega
    have hEq : (2 * t + 1) + 1 = 2 * t + 2 := by ring
    rw [hEq]
    omega
  exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by positivity)).mpr hPow)

/-- **`SkipRing` Collapses via Balanced Separators**: even though `SkipRing` defeats
`LiteralPropagation`, `StrideContraction`, and `ValiantReduction`, balanced column separators of
width `p i = (Nat.log 2 (q i + 1) + s + 2) ^ 2` compress it into `2 ^ o(n)` exact `#3-SAT` time. -/
theorem separator_subexponential (q : Nat → Nat) (s : Nat) (hq : Tendsto q atTop atTop)
    (C d : ℝ) :
    let m : Nat → Nat := fun i => q i
    let p : Nat → Nat := fun i => (Nat.log 2 (q i + 1) + s + 2) ^ 2
    let n : Nat → Nat := fun i => (m i + 1) * (p i + 1)
    let D : Nat → Nat := fun i => Nat.log 2 (n i) + s
    let R : Nat → Nat := fun i => (separatorSOPCertificate (m i) (p i) (D i) s).branches
    let M : Nat → Nat := fun i => m i + 1
    let v : Nat → Nat := fun i => (D i + 1) * (p i + 1) + 2 * D i + 8
    (fun i => sopLogTimeBudget (n i) (R i) (M i) (v i) C d) =o[atTop] fun i => (n i : ℝ) := by
  intro m p n D R M v
  have hqReal : Tendsto (fun i => (q i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hnNat : Tendsto n atTop atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun B => ?_
    obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp hq B
    refine ⟨K, fun i hi => ?_⟩
    have h1 : 1 ≤ p i + 1 := Nat.succ_pos _
    have hB : B ≤ m i + 1 := (hK i hi).trans (Nat.le_add_right _ _)
    calc
      B = B * 1 := (Nat.mul_one B).symm
      _ ≤ (m i + 1) * (p i + 1) := Nat.mul_le_mul hB h1
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnNat
  have hDBound : ∀ i, D i + 1 ≤ 3 * (Nat.log 2 (q i + 1) + s + 2) + 3 := by
    intro i
    have hMul : Nat.log 2 (n i) ≤
        Nat.log 2 (q i + 1) + Nat.log 2 (p i + 1) + 1 := by
      simpa [n, m] using nat_log2_mul_le (q i + 1) (p i + 1) (Nat.succ_pos _) (Nat.succ_pos _)
    have hSq : Nat.log 2 (p i + 1) ≤ 2 * (Nat.log 2 (q i + 1) + s + 2) + 1 :=
      nat_log2_sq_succ_le (Nat.log 2 (q i + 1) + s + 2) (by omega)
    dsimp [D]
    omega
  have hBranches : (fun i => Real.log ((R i : ℝ) + 1)) =o[atTop] fun i => (n i : ℝ) := by
    have hExpO : (fun i => (((m i + 1) * (D i + 1) + 1 : Nat) : ℝ)) =o[atTop]
        fun i => (n i : ℝ) := by
      rw [Asymptotics.isLittleO_iff]
      intro ε hε
      have hLogQ : Tendsto (fun i => (Nat.log 2 (q i + 1) : ℝ)) atTop atTop := by
        refine Filter.tendsto_atTop_atTop.mpr fun B => ?_
        obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp hq (2 ^ (Nat.ceil (max B 0) + 1))
        refine ⟨K, fun i hi => ?_⟩
        have hPow : 2 ^ Nat.ceil (max B 0) ≤ q i + 1 := by
          have := hK i hi
          have h1 : 2 ^ Nat.ceil (max B 0) ≤ 2 ^ (Nat.ceil (max B 0) + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
          omega
        have hLogGe : Nat.ceil (max B 0) ≤ Nat.log 2 (q i + 1) := by
          have := Nat.log_mono_right (b := 2) hPow
          rwa [Nat.log_pow (by decide : 1 < 2)] at this
        have hReal : max B 0 ≤ (Nat.ceil (max B 0) : ℝ) := Nat.le_ceil _
        have hCast : (Nat.ceil (max B 0) : ℝ) ≤ (Nat.log 2 (q i + 1) : ℝ) := by
          exact_mod_cast hLogGe
        linarith [le_max_left B 0]
      let T : ℝ := 5 / ε
      filter_upwards [hLogQ.eventually_ge_atTop (max T 1)] with i hi
      have hTLe : T ≤ (Nat.log 2 (q i + 1) : ℝ) := (le_max_left T 1).trans hi
      have hGe1 : (1 : ℝ) ≤ (Nat.log 2 (q i + 1) : ℝ) := (le_max_right T 1).trans hi
      have hGe1Nat : 1 ≤ Nat.log 2 (q i + 1) := by exact_mod_cast hGe1
      let Lq : ℝ := (Nat.log 2 (q i + 1) : ℝ) + s + 2
      have hLqPos : 0 < Lq := by dsimp [Lq]; positivity
      have hLqGe1 : 1 ≤ Lq := by dsimp [Lq]; linarith
      have hTLeLq : T ≤ Lq := by dsimp [Lq]; linarith [show (0 : ℝ) ≤ s + 2 by positivity]
      have hDLe : (((D i + 1 : Nat) : ℝ)) ≤ 4 * Lq := by
        have hNat : D i + 1 ≤ 4 * (Nat.log 2 (q i + 1) + s + 2) := by
          have := hDBound i
          omega
        have hCast : ((D i + 1 : Nat) : ℝ) ≤
            ((4 * (Nat.log 2 (q i + 1) + s + 2) : Nat) : ℝ) := by exact_mod_cast hNat
        simpa [Lq] using hCast
      have hEpsLq : 5 ≤ ε * Lq := by
        have : 5 = ε * T := by dsimp [T]; field_simp [hε.ne']
        rw [this]
        exact mul_le_mul_of_nonneg_left hTLeLq hε.le
      have hPGe : Lq ^ 2 ≤ ((p i + 1 : Nat) : ℝ) := by
        dsimp [p, Lq]
        push_cast
        linarith
      have hNumLe : (((m i + 1) * (D i + 1) + 1 : Nat) : ℝ) ≤
          5 * (((m i + 1 : Nat) : ℝ) * Lq) := by
        have hGeM : (1 : ℝ) ≤ ((m i + 1 : Nat) : ℝ) := by
          exact_mod_cast Nat.succ_pos (m i)
        have h1Le : 1 ≤ ((m i + 1 : Nat) : ℝ) * Lq := by
          simpa using mul_le_mul hGeM hLqGe1 (by norm_num) (by positivity)
        have hMulD := mul_le_mul_of_nonneg_left hDLe (by positivity : 0 ≤ ((m i + 1 : Nat) : ℝ))
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        linarith
      have hTarget : 5 * (((m i + 1 : Nat) : ℝ) * Lq) ≤ ε * (n i : ℝ) := by
        have hnEq : (n i : ℝ) = ((m i + 1 : Nat) : ℝ) * ((p i + 1 : Nat) : ℝ) := by
          dsimp [n]; push_cast; ring
        rw [hnEq]
        calc
          5 * (((m i + 1 : Nat) : ℝ) * Lq)
            = (((m i + 1 : Nat) : ℝ) * Lq) * 5 := by ring
          _ ≤ (((m i + 1 : Nat) : ℝ) * Lq) * (ε * Lq) :=
              mul_le_mul_of_nonneg_left hEpsLq (by positivity)
          _ = ε * (((m i + 1 : Nat) : ℝ) * Lq ^ 2) := by ring
          _ ≤ ε * (((m i + 1 : Nat) : ℝ) * ((p i + 1 : Nat) : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ hε.le
              exact mul_le_mul_of_nonneg_left hPGe (by positivity)
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact hNumLe.trans hTarget
    have hDom : (fun i => Real.log ((R i : ℝ) + 1)) =O[atTop]
        fun i => (((m i + 1) * (D i + 1) + 1 : Nat) : ℝ) := by
      refine IsBigO.of_bound 2 ?_
      refine Eventually.of_forall fun i => ?_
      have hGe1 : (1 : ℝ) ≤ (R i : ℝ) + 1 := by linarith [show (0 : ℝ) ≤ (R i : ℝ) by positivity]
      rw [Real.norm_of_nonneg (Real.log_nonneg hGe1), Real.norm_of_nonneg (by positivity)]
      have hPow : (R i : ℝ) + 1 ≤ (2 : ℝ) ^ ((m i + 1) * (D i + 1) + 1) := by
        dsimp [R, separatorSOPCertificate]
        push_cast
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((m i + 1) * (D i + 1)) := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        linarith
      calc
        Real.log ((R i : ℝ) + 1)
          ≤ Real.log ((2 : ℝ) ^ ((m i + 1) * (D i + 1) + 1)) := Real.log_le_log (by positivity) hPow
        _ = (((m i + 1) * (D i + 1) + 1 : Nat) : ℝ) * Real.log 2 := by
            rw [Real.log_pow]
        _ ≤ 2 * (((m i + 1) * (D i + 1) + 1 : Nat) : ℝ) := by
            have hLog2 : Real.log 2 ≤ 2 :=
              (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
            nlinarith [show (0 : ℝ) ≤ (((m i + 1) * (D i + 1) + 1 : Nat) : ℝ) by positivity]
    exact hDom.trans_isLittleO hExpO
  have hFactors : (fun i => Real.log ((M i : ℝ) + 1)) =o[atTop] fun i => (n i : ℝ) := by
    have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
    have hShiftO : (fun i => (n i : ℝ) + 16) =O[atTop] fun i => (n i : ℝ) := by
      refine IsBigO.of_bound 17 ?_
      filter_upwards [hnReal.eventually_ge_atTop 1] with i hi
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      linarith
    have hLogN := (Real.isLittleO_log_id_atTop.comp_tendsto hnShift).trans_isBigO hShiftO
    have hDom : (fun i => Real.log ((M i : ℝ) + 1)) =O[atTop] fun i => Real.log ((n i : ℝ) + 16) := by
      refine IsBigO.of_bound 1 ?_
      refine Eventually.of_forall fun i => ?_
      have hMLeN : M i ≤ n i := by
        dsimp [M, n]
        exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      have hLogM : Real.log ((M i : ℝ) + 1) ≤ Real.log ((n i : ℝ) + 16) := by
        apply Real.log_le_log (by positivity)
        have : (M i : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hMLeN
        linarith
      rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (M i : ℝ) by positivity])),
        Real.norm_of_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (n i : ℝ) by positivity]))]
      linarith
    exact hDom.trans_isLittleO hLogN
  let c : ℝ := ((9 * s + 44 : Nat) : ℝ)
  have hcNonneg : 0 ≤ c := by positivity
  have hVars : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ (0 : ℝ) := by
    refine Eventually.of_forall fun i => ?_
    have hLogLt : Nat.log 2 (q i + 1) ≤ q i + 1 :=
      (Nat.log_lt_self 2 (Nat.succ_ne_zero (q i))).le
    have hDLeM : D i + 1 ≤ (3 * s + 12) * (m i + 1) := by
      have h1 := hDBound i
      have hGe1 : 1 ≤ m i + 1 := Nat.succ_pos _
      dsimp [m] at hGe1 ⊢
      nlinarith
    have hPGe1 : 1 ≤ p i + 1 := Nat.succ_pos _
    have hMGe1 : 1 ≤ m i + 1 := Nat.succ_pos _
    have hMn : m i + 1 ≤ n i := Nat.le_mul_of_pos_right _ hPGe1
    have hMul1 : (D i + 1) * (p i + 1) ≤ (3 * s + 12) * n i := by
      calc
        (D i + 1) * (p i + 1) ≤ ((3 * s + 12) * (m i + 1)) * (p i + 1) :=
          Nat.mul_le_mul_right _ hDLeM
        _ = (3 * s + 12) * n i := by dsimp [n]; ring
    have h2D : 2 * D i ≤ (6 * s + 24) * n i := by
      have h1 : D i ≤ (3 * s + 12) * n i := le_trans (by omega) (le_trans hDLeM (Nat.mul_le_mul_left _ hMn))
      calc
        2 * D i ≤ 2 * ((3 * s + 12) * n i) := Nat.mul_le_mul_left 2 h1
        _ = (6 * s + 24) * n i := by ring
    have hNGe1 : 1 ≤ n i := le_trans hMGe1 hMn
    have hVLe : v i ≤ (9 * s + 44) * n i := by
      dsimp [v]
      have h8 : 8 ≤ 8 * n i := by nlinarith
      have hSum : (3 * s + 12) * n i + (6 * s + 24) * n i + 8 * n i = (9 * s + 44) * n i := by ring
      omega
    have hCast : (v i : ℝ) ≤ c * (n i : ℝ) := by
      calc
        (v i : ℝ) ≤ (((9 * s + 44) * n i : Nat) : ℝ) := by exact_mod_cast hVLe
        _ = c * (n i : ℝ) := by dsimp [c]; push_cast; ring
    simpa [Real.rpow_zero, mul_one] using hCast
  exact sopLogTimeBudget_isLittleO_of_rpow_log hnNat hBranches hFactors hcNonneg
    (by norm_num : (0 : ℝ) < 1 / 2) hVars C d

end SkipRing

/-! ### 2. `ButterflyNet`: Explicit $O(\log n)$-Depth, $O(n \log n)$-Gate, Fanout-`≤ 2` Hard Core -/

namespace ButterflyNet

/-- Flips the `ℓ`-th binary bit of `z`. -/
def flipBit (z ℓ : Nat) : Nat :=
  if (z / 2 ^ ℓ) % 2 = 0 then z + 2 ^ ℓ else z - 2 ^ ℓ

theorem flipBit_lt {d z ℓ : Nat} (hz : z < 2 ^ d) (hℓ : ℓ < d) : flipBit z ℓ < 2 ^ d := by
  unfold flipBit
  let P := 2 ^ ℓ
  have hP : 0 < P := Nat.two_pow_pos _
  have hdEq : d = (d - ℓ - 1) + 1 + ℓ := by omega
  have hPowEq : 2 ^ d = 2 ^ (d - ℓ - 1) * 2 * P := by
    conv_lhs => rw [hdEq, Nat.pow_add, Nat.pow_add, Nat.pow_one]
  by_cases hBit : (z / P) % 2 = 0
  · simp only [P] at hBit
    simp only [hBit, ↓reduceIte]
    have hDivMod := Nat.div_add_mod z P
    have hModLt := Nat.mod_lt z hP
    have hQMul : (z / P) * P ≤ z := by
      have : P * (z / P) = (z / P) * P := Nat.mul_comm _ _
      omega
    have hQDiv : z / P = 2 * ((z / P) / 2) := by
      have h := Nat.div_add_mod (z / P) 2
      rw [hBit, Nat.add_zero] at h
      exact h.symm
    have hkLt : (z / P) / 2 < 2 ^ (d - ℓ - 1) := by
      by_contra hGe
      have hGe' : 2 ^ (d - ℓ - 1) ≤ (z / P) / 2 := Nat.le_of_not_gt hGe
      have h1 : 2 ^ d ≤ (z / P) * P := by
        rw [hPowEq, hQDiv]
        nlinarith [Nat.mul_le_mul_right P (show 2 ^ (d - ℓ - 1) * 2 ≤ 2 * ((z / P) / 2) by omega)]
      omega
    have hNext : (z / P + 2) ≤ 2 ^ (d - ℓ - 1) * 2 := by omega
    calc
      z + P = (P * (z / P) + z % P) + P := by rw [hDivMod]
      _ = (z / P + 1) * P + z % P := by ring
      _ < (z / P + 1) * P + P := Nat.add_lt_add_left hModLt _
      _ = (z / P + 2) * P := by ring
      _ ≤ (2 ^ (d - ℓ - 1) * 2) * P := Nat.mul_le_mul_right P hNext
      _ = 2 ^ d := hPowEq.symm
  · dsimp only [P] at hBit
    simp only [hBit, ↓reduceIte]
    omega

theorem flipBit_involutive (z ℓ : Nat) : flipBit (flipBit z ℓ) ℓ = z := by
  unfold flipBit
  let P := 2 ^ ℓ
  have hP : 0 < P := Nat.two_pow_pos _
  have hDivMod := Nat.div_add_mod z P
  have hModLt := Nat.mod_lt z hP
  by_cases hBit : (z / P) % 2 = 0
  · have hBit2 : (z / 2 ^ ℓ) % 2 = 0 := hBit
    simp only [hBit2, ↓reduceIte]
    have hDivAdd : (z + P) / P = z / P + 1 := by
      have h1 : z + P = z + 1 * P := by ring
      rw [h1, Nat.add_mul_div_right _ _ hP]
    have hOdd : ((z + P) / P) % 2 ≠ 0 := by
      rw [hDivAdd, Nat.add_mod, hBit]
      decide
    have hOdd2 : ((z + 2 ^ ℓ) / 2 ^ ℓ) % 2 ≠ 0 := hOdd
    simp only [hOdd2, ↓reduceIte]
    omega
  · have hBit2 : (z / 2 ^ ℓ) % 2 ≠ 0 := hBit
    simp only [hBit2, ↓reduceIte]
    have hBit1 : (z / P) % 2 = 1 := by
      have := Nat.mod_lt (z / P) (by decide : 0 < 2)
      dsimp [P] at *
      omega
    have hQPos : 1 ≤ z / P := by
      by_contra h0
      have hEq0 : z / P = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h0)
      rw [hEq0] at hBit1
      simp at hBit1
    have hPLe : P ≤ z := by
      have h1 : 1 * P ≤ (z / P) * P := Nat.mul_le_mul_right P hQPos
      have h2 : P * (z / P) = (z / P) * P := Nat.mul_comm _ _
      omega
    have hEqSub : z - P + P = z := Nat.sub_add_cancel hPLe
    have hDivSub : (z - P) / P = z / P - 1 := by
      have h1 : z = (z - P) + 1 * P := by omega
      have h2 := congrArg (· / P) h1
      rw [Nat.add_mul_div_right _ _ hP] at h2
      omega
    have hEven : ((z - P) / P) % 2 = 0 := by
      rw [hDivSub]
      have h := Nat.div_add_mod (z / P) 2
      rw [hBit1] at h
      have hPrev : z / P - 1 = 2 * ((z / P) / 2) := by omega
      rw [hPrev]
      simp
    have hEven2 : ((z - 2 ^ ℓ) / 2 ^ ℓ) % 2 = 0 := hEven
    simp only [hEven2, ↓reduceIte]
    exact hEqSub

theorem flipBit_ne_self (z ℓ : Nat) : flipBit z ℓ ≠ z := by
  unfold flipBit
  let P := 2 ^ ℓ
  have hP : 0 < P := Nat.two_pow_pos _
  by_cases hBit : (z / P) % 2 = 0
  · have hBit2 : (z / 2 ^ ℓ) % 2 = 0 := hBit
    simp only [hBit2, ↓reduceIte]; omega
  · have hBit2 : (z / 2 ^ ℓ) % 2 ≠ 0 := hBit
    simp only [hBit2, ↓reduceIte]
    have hBit1 : (z / P) % 2 = 1 := by
      have := Nat.mod_lt (z / P) (by decide : 0 < 2)
      dsimp [P] at *
      omega
    have hQPos : 1 ≤ z / P := by
      by_contra h0
      have hEq0 : z / P = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge h0)
      rw [hEq0] at hBit1
      simp at hBit1
    have hDivMod := Nat.div_add_mod z P
    have h1 : 1 * P ≤ (z / P) * P := Nat.mul_le_mul_right P hQPos
    have h2 : P * (z / P) = (z / P) * P := Nat.mul_comm _ _
    omega

theorem flipBit_eq_iff (x y ℓ : Nat) : flipBit x ℓ = y ↔ x = flipBit y ℓ := by
  constructor
  · rintro rfl; exact (flipBit_involutive x ℓ).symm
  · rintro rfl; exact flipBit_involutive y ℓ

/-- Butterfly gate at layer `ℓ + 1`, column `j < 2 ^ d` reading `(ℓ, j)` and `(ℓ, flipBit j ℓ)`. -/
def bflyGate (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    Gate (LayeredRing.ringWires (2 ^ d) ℓ + j) :=
  let N := 2 ^ d
  have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
  let a : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + j, by
    rw [hBase]
    have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
    omega⟩
  let b : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + flipBit j ℓ, by
    have hf := flipBit_lt hj hℓ
    rw [hBase]
    have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
    omega⟩
  if ℓ % 2 = 0 then .and a b else .or a b

def appendBflyRow (d ℓ : Nat) (hℓ : ℓ < d) :
    (j : Nat) → j ≤ 2 ^ d → Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ) →
      Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ + j)
  | 0, _, c => c
  | j + 1, hj, c =>
    (appendBflyRow d ℓ hℓ j (by omega) c).snoc (bflyGate d ℓ j hℓ (by omega))

def buildBfly (d : Nat) : (ℓ : Nat) → ℓ ≤ d → Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)
  | 0, _ => Circuit.inputsOnly
  | ℓ + 1, hℓ =>
    appendBflyRow d ℓ (by omega) (2 ^ d) (le_rfl) (buildBfly d ℓ (by omega))

/-- `d`-stage butterfly circuit over `n = 2 ^ d` inputs (`wires = (d + 1) * 2 ^ d`, depth `d`,
binary gates `d * 2 ^ d`, max fanout `≤ 2`). -/
def source (d : Nat) : CircuitInstance (2 ^ d) where
  wires := LayeredRing.ringWires (2 ^ d) d
  circuit := buildBfly d d (le_rfl)
  output := ⟨LayeredRing.ringWires (2 ^ d) d - 1, by
    have hEq := LayeredRing.ringWires_eq (2 ^ d) d
    have hPos : 0 < (d + 1) * 2 ^ d := Nat.mul_pos (Nat.succ_pos d) (Nat.two_pow_pos d)
    omega⟩

private theorem bfly_div_mod_layer {N L col : Nat} (hc : col < N) :
    (L * N + col) / N = L ∧ (L * N + col) % N = col := by
  have hN : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le col) hc
  constructor
  · rw [Nat.add_comm (L * N) col, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm (L * N) col, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

private theorem binaryGateCount_snoc_ite' {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    binaryGateCount (c.snoc (if P then .and a b else .or a b)) = binaryGateCount c + 1 := by
  by_cases hP : P
  · simp only [hP, ↓reduceIte]; rfl
  · simp only [hP, ↓reduceIte]; rfl

private theorem binaryFanout_snoc_ite_last' {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    binaryFanout (c.snoc (if P then .and a b else .or a b)) (Fin.last w) = 0 := by
  by_cases hP : P
  · simp [hP, binaryFanout_snoc_and_last]
  · simp [hP, binaryFanout_snoc_or_last]

private theorem binaryFanout_snoc_ite_castSucc' {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b q : Fin w) :
    binaryFanout (c.snoc (if P then .and a b else .or a b)) q.castSucc =
      binaryFanout c q + if q = a ∨ q = b then 1 else 0 := by
  by_cases hP : P
  · simp [hP, binaryFanout_snoc_and_castSucc]
  · simp [hP, binaryFanout_snoc_or_castSucc]

private theorem wireDepth_snoc_ite_last' {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    wireDepth (c.snoc (if P then .and a b else .or a b)) (Fin.last w) =
      max (wireDepth c a) (wireDepth c b) + 1 := by
  by_cases hP : P
  · simp [hP, wireDepth_snoc_and_last]
  · simp [hP, wireDepth_snoc_or_last]

private theorem maxBinaryReaderDepth_snoc_ite_castSucc' {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b q : Fin w) :
    maxBinaryReaderDepth (c.snoc (if P then .and a b else .or a b)) q.castSucc =
      if q = a ∨ q = b then
        max (maxBinaryReaderDepth c q) (max (wireDepth c a) (wireDepth c b) + 1)
      else maxBinaryReaderDepth c q := by
  by_cases hP : P
  · simp [hP, maxBinaryReaderDepth_snoc_and_castSucc]
  · simp [hP, maxBinaryReaderDepth_snoc_or_castSucc]

private theorem binaryGateCount_appendBflyRow (d ℓ : Nat) (hℓ : ℓ < d)
    (c : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) :
    ∀ j (hj : j ≤ 2 ^ d), binaryGateCount (appendBflyRow d ℓ hℓ j hj c) = binaryGateCount c + j
  | 0, _ => rfl
  | j + 1, hj => by
    change binaryGateCount ((appendBflyRow d ℓ hℓ j (by omega) c).snoc
        (bflyGate d ℓ j hℓ (by omega))) = binaryGateCount c + (j + 1)
    dsimp [bflyGate]
    rw [binaryGateCount_snoc_ite', binaryGateCount_appendBflyRow d ℓ hℓ c j (by omega)]
    omega

private theorem buildBfly_binaryGateCount (d : Nat) :
    ∀ D (hD : D ≤ d), binaryGateCount (buildBfly d D hD) = D * 2 ^ d
  | 0, _ => by simp [buildBfly, binaryGateCount, unhitBinaryGates]
  | D + 1, hD => by
    change binaryGateCount (appendBflyRow d D (by omega) (2 ^ d) (le_rfl) (buildBfly d D (by omega))) =
      (D + 1) * 2 ^ d
    rw [binaryGateCount_appendBflyRow, buildBfly_binaryGateCount d D (by omega)]
    ring

theorem source_binaryGateCount (d : Nat) :
    binaryGateCount (source d).circuit = d * 2 ^ d :=
  buildBfly_binaryGateCount d d (le_rfl)

private def bflyFanoutBudget (N ℓ₀ j₀ : Nat) (u : Nat) : Nat :=
  (if u / N < ℓ₀ ∨ (u / N = ℓ₀ ∧ u % N < j₀) then 1 else 0) +
  (if u / N < ℓ₀ ∨ (u / N = ℓ₀ ∧ flipBit (u % N) (u / N) < j₀) then 1 else 0)

private theorem bflyFanoutBudget_le_two (N ℓ₀ j₀ u : Nat) :
    bflyFanoutBudget N ℓ₀ j₀ u ≤ 2 := by
  unfold bflyFanoutBudget
  split_ifs <;> omega

private theorem bflyFanoutBudget_succ_row_le (N ℓ₀ u : Nat) :
    bflyFanoutBudget N ℓ₀ N u ≤ bflyFanoutBudget N (ℓ₀ + 1) 0 u := by
  unfold bflyFanoutBudget
  split_ifs <;> omega

private theorem appendBflyRow_fanout_inv (d ℓ : Nat) (hℓ : ℓ < d)
    (c : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (hInv : ∀ u : Fin (LayeredRing.ringWires (2 ^ d) ℓ),
      binaryFanout c u ≤ bflyFanoutBudget (2 ^ d) ℓ 0 u.val) :
    ∀ j (hj : j ≤ 2 ^ d) (u : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j)),
      binaryFanout (appendBflyRow d ℓ hℓ j hj c) u ≤ bflyFanoutBudget (2 ^ d) ℓ j u.val := by
  intro j
  induction j with
  | zero =>
    intro _ u
    exact hInv u
  | succ j ih =>
    intro hj u
    have hPrevAll := ih (by omega)
    let N := 2 ^ d
    let prev := appendBflyRow d ℓ hℓ j (by omega) c
    have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
    have hjn : j < N := by omega
    have hfn : flipBit j ℓ < N := flipBit_lt hjn hℓ
    let a : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + j, by
      rw [hBase]
      have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
      omega⟩
    let b : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + flipBit j ℓ, by
      rw [hBase]
      have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
      omega⟩
    cases u using Fin.lastCases with
    | last =>
      change binaryFanout (prev.snoc (bflyGate d ℓ j hℓ (by omega))) (Fin.last _) ≤ _
      dsimp [bflyGate]
      rw [binaryFanout_snoc_ite_last']
      exact Nat.zero_le _
    | cast q =>
      change binaryFanout (prev.snoc (bflyGate d ℓ j hℓ (by omega))) q.castSucc ≤ _
      dsimp [bflyGate]
      rw [binaryFanout_snoc_ite_castSucc']
      change binaryFanout prev q + (if q = a ∨ q = b then 1 else 0) ≤ _
      have hPrev := hPrevAll q
      have hDelta :
          (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ q.val % N < j + 1) then 1 else 0) +
          (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ flipBit (q.val % N) (q.val / N) < j + 1) then 1 else 0) =
            (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ q.val % N < j) then 1 else 0) +
            (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ flipBit (q.val % N) (q.val / N) < j) then 1 else 0) +
            (if q = a then 1 else 0) + (if q = b then 1 else 0) := by
        have hQa : q = a ↔ q.val / N = ℓ ∧ q.val % N = j := by
          constructor
          · intro hEq
            have hv : q.val = ℓ * N + j := congrArg Fin.val hEq
            rw [hv]
            exact bfly_div_mod_layer hjn
          · rintro ⟨hDiv, hMod⟩
            apply Fin.ext
            change q.val = ℓ * N + j
            have hN : 0 < N := Nat.two_pow_pos d
            have hDM := Nat.div_add_mod q.val N
            rw [hDiv, hMod, Nat.mul_comm N ℓ] at hDM
            exact hDM.symm
        have hQb : q = b ↔ q.val / N = ℓ ∧ flipBit (q.val % N) (q.val / N) = j := by
          constructor
          · intro hEq
            have hv : q.val = ℓ * N + flipBit j ℓ := congrArg Fin.val hEq
            have hDM := bfly_div_mod_layer (L := ℓ) hfn
            rw [← hv] at hDM
            refine ⟨hDM.1, ?_⟩
            rw [hDM.1, hDM.2, flipBit_involutive]
          · rintro ⟨hDiv, hFlip⟩
            apply Fin.ext
            change q.val = ℓ * N + flipBit j ℓ
            rw [hDiv] at hFlip
            have hMod : q.val % N = flipBit j ℓ := (flipBit_eq_iff _ _ _).mp hFlip
            have hN : 0 < N := Nat.two_pow_pos d
            have hDM := Nat.div_add_mod q.val N
            rw [hDiv, hMod, Nat.mul_comm N ℓ] at hDM
            exact hDM.symm
        have h1 :
            (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ q.val % N < j + 1) then 1 else 0) =
              (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ q.val % N < j) then 1 else 0) +
              (if q = a then 1 else 0) := by
          by_cases hA : q = a
          · have hPair := hQa.mp hA
            rw [hPair.1, hPair.2]
            simp [hA]
          · have hNot : ¬ (q.val / N = ℓ ∧ q.val % N = j) := fun h => hA (hQa.mpr h)
            simp only [hA, ↓reduceIte, Nat.add_zero]
            split_ifs <;> omega
        have h2 :
            (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ flipBit (q.val % N) (q.val / N) < j + 1) then 1 else 0) =
              (if q.val / N < ℓ ∨ (q.val / N = ℓ ∧ flipBit (q.val % N) (q.val / N) < j) then 1 else 0) +
              (if q = b then 1 else 0) := by
          by_cases hB : q = b
          · have hPair := hQb.mp hB
            rw [hPair.2, hPair.1]
            simp [hB]
          · have hNot : ¬ (q.val / N = ℓ ∧ flipBit (q.val % N) (q.val / N) = j) :=
              fun h => hB (hQb.mpr h)
            simp only [hB, ↓reduceIte, Nat.add_zero]
            split_ifs <;> omega
        omega
      have hStep : (if q = a ∨ q = b then 1 else 0) ≤
          (if q = a then 1 else 0) + (if q = b then 1 else 0) := by
        split_ifs <;> omega
      dsimp only [bflyFanoutBudget, prev] at hPrev ⊢
      dsimp only [N] at hDelta
      omega

private theorem buildBfly_fanout_inv (d : Nat) :
    ∀ D (hD : D ≤ d) (u : Fin (LayeredRing.ringWires (2 ^ d) D)),
      binaryFanout (buildBfly d D hD) u ≤ bflyFanoutBudget (2 ^ d) D 0 u.val
  | 0, _, u => by
    simp [buildBfly, binaryFanout]
  | D + 1, hD, u => by
    have hRow := appendBflyRow_fanout_inv d D (by omega) (buildBfly d D (by omega))
      (buildBfly_fanout_inv d D (by omega)) (2 ^ d) (le_rfl) u
    have hBudget := bflyFanoutBudget_succ_row_le (2 ^ d) D u.val
    change binaryFanout (appendBflyRow d D (by omega) (2 ^ d) (le_rfl)
      (buildBfly d D (by omega))) u ≤ _
    exact hRow.trans hBudget

theorem source_fanout_le_two (d : Nat) (u : Fin (source d).wires) :
    binaryFanout (source d).circuit u ≤ 2 :=
  (buildBfly_fanout_inv d d (le_rfl) u).trans (bflyFanoutBudget_le_two (2 ^ d) d 0 u.val)

theorem source_hitting_cut_lower (d : Nat) (cut : Finset (Fin (source d).wires)) :
    d * 2 ^ d ≤ unhitBinaryGatesOnCut (source d).circuit cut + 2 * cut.card := by
  have hBase := binaryGateCount_le_unhit_add_maxFanout (source d).circuit 2
    (source_fanout_le_two d) cut
  rwa [source_binaryGateCount] at hBase

private theorem appendBflyRow_depth_inv (d ℓ : Nat) (hℓ : ℓ < d)
    (c : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (hDepth : ∀ u : Fin (LayeredRing.ringWires (2 ^ d) ℓ),
      wireDepth c u = u.val / 2 ^ d) :
    ∀ j (hj : j ≤ 2 ^ d) (u : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j)),
      wireDepth (appendBflyRow d ℓ hℓ j hj c) u = u.val / 2 ^ d := by
  intro j
  induction j with
  | zero => intro _ u; exact hDepth u
  | succ j ih =>
    intro hj u
    have ihD := ih (by omega)
    let N := 2 ^ d
    let prev := appendBflyRow d ℓ hℓ j (by omega) c
    have hjn : j < N := by omega
    have hfn : flipBit j ℓ < N := flipBit_lt hjn hℓ
    have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
    let a : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + j, by
      rw [hBase]
      have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
      omega⟩
    let b : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + flipBit j ℓ, by
      rw [hBase]
      have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
      omega⟩
    have haD : wireDepth prev a = ℓ := (ihD a).trans (bfly_div_mod_layer hjn).1
    have hbD : wireDepth prev b = ℓ := (ihD b).trans (bfly_div_mod_layer hfn).1
    have hLastDiv : (LayeredRing.ringWires (2 ^ d) ℓ + j) / 2 ^ d = ℓ + 1 := by
      change (LayeredRing.ringWires N ℓ + j) / N = ℓ + 1
      rw [hBase]
      exact (bfly_div_mod_layer (L := ℓ + 1) hjn).1
    cases u using Fin.lastCases with
    | last =>
      change wireDepth (prev.snoc (bflyGate d ℓ j hℓ (by omega))) (Fin.last _) = _
      dsimp [bflyGate]
      rw [wireDepth_snoc_ite_last']
      change max (wireDepth prev a) (wireDepth prev b) + 1 = _
      rw [haD, hbD, hLastDiv]
      omega
    | cast q =>
      change wireDepth (prev.snoc (bflyGate d ℓ j hℓ (by omega))) q.castSucc = _
      rw [wireDepth_snoc_castSucc]
      exact ihD q

private theorem buildBfly_depth_inv (d : Nat) :
    ∀ D (hD : D ≤ d) (u : Fin (LayeredRing.ringWires (2 ^ d) D)),
      wireDepth (buildBfly d D hD) u = u.val / 2 ^ d
  | 0, _, u => by
    have hu : u.val < 2 ^ d := u.isLt
    change wireDepth Circuit.inputsOnly u = _
    simp [Nat.div_eq_of_lt hu]
  | D + 1, hD, u =>
    appendBflyRow_depth_inv d D (by omega) (buildBfly d D (by omega))
      (buildBfly_depth_inv d D (by omega)) (2 ^ d) (le_rfl) u

theorem source_wireDepth (d : Nat) (u : Fin (source d).wires) :
    wireDepth (source d).circuit u = u.val / 2 ^ d :=
  buildBfly_depth_inv d d (le_rfl) u

private theorem appendBflyRow_readerDepth_inv (d ℓ : Nat) (hℓ : ℓ < d)
    (c : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ))
    (hDepth : ∀ u : Fin (LayeredRing.ringWires (2 ^ d) ℓ),
      wireDepth c u = u.val / 2 ^ d)
    (hReader : ∀ u : Fin (LayeredRing.ringWires (2 ^ d) ℓ),
      u.val / 2 ^ d < ℓ → u.val / 2 ^ d + 1 ≤ maxBinaryReaderDepth c u) :
    ∀ j (hj : j ≤ 2 ^ d) (u : Fin (LayeredRing.ringWires (2 ^ d) ℓ + j)),
      (u.val / 2 ^ d < ℓ ∨ (u.val / 2 ^ d = ℓ ∧ u.val % 2 ^ d < j)) →
        u.val / 2 ^ d + 1 ≤ maxBinaryReaderDepth (appendBflyRow d ℓ hℓ j hj c) u := by
  intro j
  induction j with
  | zero =>
    intro _ u hu
    rcases hu with hLt | ⟨_, hZero⟩
    · exact hReader u hLt
    · omega
  | succ j ih =>
    intro hj u hu
    let N := 2 ^ d
    let prev := appendBflyRow d ℓ hℓ j (by omega) c
    have hPrevDepth := appendBflyRow_depth_inv d ℓ hℓ c hDepth j (by omega)
    have hPrevReader := ih (by omega)
    have hjn : j < N := by omega
    have hfn : flipBit j ℓ < N := flipBit_lt hjn hℓ
    have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
    let a : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + j, by
      rw [hBase]
      have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
      omega⟩
    let b : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + flipBit j ℓ, by
      rw [hBase]
      have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
      omega⟩
    have haD : wireDepth prev a = ℓ := (hPrevDepth a).trans (bfly_div_mod_layer hjn).1
    have hbD : wireDepth prev b = ℓ := (hPrevDepth b).trans (bfly_div_mod_layer hfn).1
    cases u using Fin.lastCases with
    | last =>
      exfalso
      have hLastDiv : (LayeredRing.ringWires N ℓ + j) / N = ℓ + 1 := by
        rw [hBase]
        exact (bfly_div_mod_layer (L := ℓ + 1) hjn).1
      change (LayeredRing.ringWires N ℓ + j) / N < ℓ ∨
        ((LayeredRing.ringWires N ℓ + j) / N = ℓ ∧ _) at hu
      rw [hLastDiv] at hu
      omega
    | cast q =>
      change _ ≤ maxBinaryReaderDepth (prev.snoc (bflyGate d ℓ j hℓ (by omega))) q.castSucc
      dsimp [bflyGate]
      rw [maxBinaryReaderDepth_snoc_ite_castSucc']
      change _ ≤ if q = a ∨ q = b then
          max (maxBinaryReaderDepth prev q) (max (wireDepth prev a) (wireDepth prev b) + 1)
        else maxBinaryReaderDepth prev q
      rw [haD, hbD]
      have huQ : q.val / N < ℓ ∨ (q.val / N = ℓ ∧ q.val % N < j + 1) := hu
      by_cases hQa : q = a
      · have hDiv : q.val / N = ℓ := by
          have hv : q.val = ℓ * N + j := congrArg Fin.val hQa
          rw [hv]
          exact (bfly_div_mod_layer hjn).1
        have hIf : q = a ∨ q = b := Or.inl hQa
        simp only [hIf, ↓reduceIte]
        have hMax : ℓ + 1 ≤ max (maxBinaryReaderDepth prev q) (max ℓ ℓ + 1) :=
          le_trans (by omega) (le_max_right _ _)
        change q.val / N + 1 ≤ _
        omega
      · have hNeVal : q.val ≠ ℓ * N + j := fun h => hQa (Fin.ext h)
        have hNotPair : ¬ (q.val / N = ℓ ∧ q.val % N = j) := by
          rintro ⟨h1, h2⟩
          apply hNeVal
          have hDM := Nat.div_add_mod q.val N
          rw [h1, h2, Nat.mul_comm N ℓ] at hDM
          exact hDM.symm
        have huPrev : q.val / N < ℓ ∨ (q.val / N = ℓ ∧ q.val % N < j) := by
          rcases huQ with hLt | ⟨hEq, hLt⟩
          · exact Or.inl hLt
          · exact Or.inr ⟨hEq, by omega⟩
        have hLe := hPrevReader q huPrev
        split_ifs
        · exact hLe.trans (le_max_left _ _)
        · exact hLe

private theorem buildBfly_readerDepth_inv (d : Nat) :
    ∀ D (hD : D ≤ d) (u : Fin (LayeredRing.ringWires (2 ^ d) D)),
      u.val / 2 ^ d < D → u.val / 2 ^ d + 1 ≤ maxBinaryReaderDepth (buildBfly d D hD) u
  | 0, _, _, hu => by omega
  | D + 1, hD, u, hu => by
    have hPrevD := buildBfly_depth_inv d D (by omega)
    have hPrevR := buildBfly_readerDepth_inv d D (by omega)
    have hRow := appendBflyRow_readerDepth_inv d D (by omega) (buildBfly d D (by omega))
      hPrevD hPrevR (2 ^ d) (le_rfl) u
    have hPrem : u.val / 2 ^ d < D ∨ (u.val / 2 ^ d = D ∧ u.val % 2 ^ d < 2 ^ d) := by
      have hm := Nat.mod_lt u.val (Nat.two_pow_pos d)
      omega
    exact hRow hPrem

theorem source_maxBinaryReaderDepth_ge (d : Nat) (u : Fin (source d).wires)
    (hu : u.val / 2 ^ d < d) :
    u.val / 2 ^ d + 1 ≤ maxBinaryReaderDepth (source d).circuit u :=
  buildBfly_readerDepth_inv d d (le_rfl) u hu

theorem source_crossingWires_ge (d h : Nat) (hh : 0 < h) (r : Fin h) :
    (d / h - 1) * 2 ^ d ≤ (crossingWires (source d).circuit h r.val).card := by
  by_cases hd : d / h ≤ 1
  · have hZero : d / h - 1 = 0 := by omega
    rw [hZero, Nat.zero_mul]
    exact Nat.zero_le _
  · have hBase : (source d).wires = (d + 1) * 2 ^ d := LayeredRing.ringWires_eq (2 ^ d) d
    let f : Fin (d / h - 1) × Fin (2 ^ d) → Fin (source d).wires := fun p =>
      let L := (p.1.val + 1) * h + (h - 1 - r.val)
      ⟨L * 2 ^ d + p.2.val, by
        rw [hBase]
        have hq : p.1.val + 1 ≤ d / h - 1 := by omega
        have hqh : (p.1.val + 1) * h ≤ (d / h - 1) * h := Nat.mul_le_mul_right h hq
        have hDivMul : (d / h) * h ≤ d := Nat.div_mul_le_self d h
        have hSubMul : (d / h - 1) * h + h = (d / h) * h := by
          have : 1 ≤ d / h := by omega
          calc
            (d / h - 1) * h + h = (d / h - 1 + 1) * h := by ring
            _ = (d / h) * h := by rw [Nat.sub_add_cancel this]
        have hLlt : L < d := by dsimp [L]; omega
        nlinarith [p.2.isLt]⟩
    have hCard : (d / h - 1) * 2 ^ d =
        (Finset.univ : Finset (Fin (d / h - 1) × Fin (2 ^ d))).card := by
      simp [Fintype.card_prod]
    rw [hCard]
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro p _
      let L := (p.1.val + 1) * h + (h - 1 - r.val)
      have hDM := bfly_div_mod_layer (L := L) p.2.isLt
      have hLge1 : 1 ≤ L := by
        have h1 : 1 * h ≤ (p.1.val + 1) * h := Nat.mul_le_mul_right h (by omega)
        dsimp [L]
        omega
      have hGe : 2 ^ d ≤ (f p).val := by
        change 2 ^ d ≤ L * 2 ^ d + p.2.val
        have h1 : 1 * 2 ^ d ≤ L * 2 ^ d := Nat.mul_le_mul_right (2 ^ d) hLge1
        omega
      have hLlt : L < d := by
        have hq : p.1.val + 1 ≤ d / h - 1 := by omega
        have hqh : (p.1.val + 1) * h ≤ (d / h - 1) * h := Nat.mul_le_mul_right h hq
        have hDivMul : (d / h) * h ≤ d := Nat.div_mul_le_self d h
        have hSubMul : (d / h - 1) * h + h = (d / h) * h := by
          have : 1 ≤ d / h := by omega
          calc
            (d / h - 1) * h + h = (d / h - 1 + 1) * h := by ring
            _ = (d / h) * h := by rw [Nat.sub_add_cancel this]
        dsimp [L]
        omega
      have hD : wireDepth (source d).circuit (f p) = L := (source_wireDepth d (f p)).trans hDM.1
      have hM : L + 1 ≤ maxBinaryReaderDepth (source d).circuit (f p) := by
        have hRaw := source_maxBinaryReaderDepth_ge d (f p) (by rw [hDM.1]; exact hLlt)
        rwa [hDM.1] at hRaw
      have hStep : bucket h r.val (wireDepth (source d).circuit (f p)) <
          bucket h r.val (maxBinaryReaderDepth (source d).circuit (f p)) := by
        rw [hD]
        unfold bucket
        have hSum : L + r.val = (p.1.val + 1) * h + (h - 1) := by
          dsimp [L]; omega
        have hSum1 : L + 1 + r.val = (p.1.val + 2) * h := by
          dsimp [L]
          have : h - 1 - r.val + 1 + r.val = h := by omega
          calc
            (p.1.val + 1) * h + (h - 1 - r.val) + 1 + r.val
              = (p.1.val + 1) * h + (h - 1 - r.val + 1 + r.val) := by omega
            _ = (p.1.val + 1) * h + h := by rw [this]
            _ = (p.1.val + 2) * h := by ring
        have hDiv1 : (L + r.val) / h = p.1.val + 1 := by
          rw [hSum, Nat.add_comm ((p.1.val + 1) * h) (h - 1),
            Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt (by omega), Nat.zero_add]
        have hDiv2 : (L + 1 + r.val) / h = p.1.val + 2 := by
          rw [hSum1, Nat.mul_div_cancel _ hh]
        have hMono : (L + 1 + r.val) / h ≤
            (maxBinaryReaderDepth (source d).circuit (f p) + r.val) / h :=
          Nat.div_le_div_right (by omega)
        omega
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, decide_eq_true ⟨hGe, hStep⟩⟩)
    · intro p₁ _ p₂ _ hEq
      have hv : (f p₁).val = (f p₂).val := congrArg Fin.val hEq
      have h1 := bfly_div_mod_layer (L := (p₁.1.val + 1) * h + (h - 1 - r.val)) p₁.2.isLt
      have h2 := bfly_div_mod_layer (L := (p₂.1.val + 1) * h + (h - 1 - r.val)) p₂.2.isLt
      have hDiv : ((f p₁).val) / 2 ^ d = ((f p₂).val) / 2 ^ d := congrArg (· / 2 ^ d) hv
      have hMod : ((f p₁).val) % 2 ^ d = ((f p₂).val) % 2 ^ d := congrArg (· % 2 ^ d) hv
      dsimp [f] at hDiv hMod
      rw [h1.1, h2.1] at hDiv
      rw [h1.2, h2.2] at hMod
      have hP1 : (p₁.1.val + 1) * h = (p₂.1.val + 1) * h := by omega
      have hFst : p₁.1.val + 1 = p₂.1.val + 1 := Nat.eq_of_mul_eq_mul_right hh hP1
      exact Prod.ext (Fin.ext (by omega)) (Fin.ext hMod)

theorem source_stride_blocks_ge (d h : Nat) (hh : 0 < h) :
    (d / h - 1) * 2 ^ d ≤ (strideCertificate (source d) h hh).blocks :=
  strideCertificate_blocks_ge_min_crossing (source d) h hh ((d / h - 1) * 2 ^ d)
    (source_crossingWires_ge d h hh)

/-- `ButterflyNet` defeats `StrideContraction`: at logarithmic depth `d`, no stride `h ≥ 1`
compresses `source d` into `O(n (log n) ^ α)` blocks for any `α < 1`. -/
theorem source_escapes_stride_subexponential_window (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (h : Nat) (hh : 0 < h) (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((strideCertificate (source (d i)) h hh).blocks : ℝ) ≤
        c * ((2 ^ d i : Nat) : ℝ) * (Real.log (((2 ^ d i : Nat) : ℝ) + 16)) ^ α) := by
  intro hEv
  let β : ℝ := max α 0
  have hβNonneg : 0 ≤ β := le_max_right α 0
  have hβLt : β < 1 := max_lt hα (by norm_num)
  have hSubPos : 0 < 1 - β := sub_pos.mpr hβLt
  let n : Nat → Nat := fun i => 2 ^ d i
  let L : Nat → ℝ := fun i => Real.log ((n i : ℝ) + 16)
  have hnNat : Tendsto n atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hd b
      exact ⟨M, fun i hi => by
        have hdi := hM i hi
        dsimp [n]
        exact le_trans hdi (le_of_lt (Nat.lt_two_pow_self (n := d i)))⟩
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnNat
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  have hLRpow : Tendsto (fun i => (L i) ^ (1 - β)) atTop atTop :=
    (tendsto_rpow_atTop hSubPos).comp hL
  let K : ℝ := 8 * (h : ℝ) * Real.log 2 * (max c 0 + 1)
  have hK : ∀ᶠ i in atTop, K < (L i) ^ (1 - β) :=
    hLRpow.eventually_gt_atTop K
  have hD4h : ∀ᶠ i in atTop, 4 * h ≤ d i := hd.eventually_ge_atTop (4 * h)
  have hD4 : ∀ᶠ i in atTop, 4 ≤ d i := hd.eventually_ge_atTop 4
  have hL1 : ∀ᶠ i in atTop, 1 ≤ L i := hL.eventually_ge_atTop 1
  obtain ⟨i, hEvI, hKI, hD4hI, hD4I, hL1I⟩ :=
    (hEv.and (hK.and (hD4h.and (hD4.and hL1)))).exists
  have hBlocksGe : (d i / h - 1) * n i ≤ (strideCertificate (source (d i)) h hh).blocks := by
    simpa [n] using source_stride_blocks_ge (d i) h hh
  have hQGe : d i ≤ 2 * h * (d i / h - 1) + 3 * h := by
    have hDM := Nat.div_add_mod (d i) h
    have hMod : d i % h < h := Nat.mod_lt (d i) hh
    have hMul : 1 ≤ d i / h := Nat.le_div_iff_mul_le hh |>.mpr (by omega)
    have hSub : (d i / h - 1) + 1 = d i / h := Nat.sub_add_cancel hMul
    nlinarith [Nat.mul_comm h (d i / h)]
  have hDLeMul : d i ≤ 4 * h * (d i / h - 1) := by
    have h2 : 2 ≤ d i / h - 1 := by
      have h3 : 4 ≤ d i / h := (Nat.le_div_iff_mul_le hh).mpr (by omega)
      omega
    nlinarith
  have hCastBlocks : ((d i / h - 1 : Nat) : ℝ) * (n i : ℝ) ≤ c * (n i : ℝ) * (L i) ^ α := by
    have hLe : (((d i / h - 1) * n i : Nat) : ℝ) ≤
        ((strideCertificate (source (d i)) h hh).blocks : ℝ) := by exact_mod_cast hBlocksGe
    have hEq : (((d i / h - 1) * n i : Nat) : ℝ) = ((d i / h - 1 : Nat) : ℝ) * (n i : ℝ) := by
      push_cast; rfl
    linarith [hEvI]
  have hPow2Bound : (n i : ℝ) + 16 < (2 : ℝ) ^ (d i + 2) := by
    have h16 : 16 < 2 ^ (d i + 1) := by
      have : 2 ^ 5 ≤ 2 ^ (d i + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hNat : n i + 16 < 2 ^ (d i + 2) := by
      dsimp [n]
      rw [Nat.pow_succ]
      omega
    exact_mod_cast hNat
  have hLLeLog2 : L i ≤ 2 * (d i : ℝ) * Real.log 2 := by
    have hPosL : 0 < (n i : ℝ) + 16 := by positivity
    have hLog := Real.log_le_log hPosL hPow2Bound.le
    rw [Real.log_pow] at hLog
    have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hDReal : (4 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hD4I
    push_cast at hLog
    nlinarith
  have hNPos : (0 : ℝ) < (n i : ℝ) := by dsimp [n]; positivity
  have hDivN : ((d i / h - 1 : Nat) : ℝ) ≤ c * (L i) ^ α := by
    nlinarith
  have hPowAlphaLeBeta : (L i) ^ α ≤ (L i) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hL1I (le_max_left α 0)
  have hCBound : c * (L i) ^ α ≤ (max c 0 + 1) * (L i) ^ β := by
    have hPowNonneg : 0 ≤ (L i) ^ α := Real.rpow_nonneg (by linarith) _
    have hcLe : c ≤ max c 0 + 1 := by linarith [le_max_left c 0]
    have hNonneg : 0 ≤ max c 0 + 1 := by linarith [le_max_right c 0]
    calc
      c * (L i) ^ α ≤ (max c 0 + 1) * (L i) ^ α := mul_le_mul_of_nonneg_right hcLe hPowNonneg
      _ ≤ (max c 0 + 1) * (L i) ^ β := mul_le_mul_of_nonneg_left hPowAlphaLeBeta hNonneg
  have hDRealLe : (d i : ℝ) ≤ 4 * (h : ℝ) * ((d i / h - 1 : Nat) : ℝ) := by exact_mod_cast hDLeMul
  have hLUpper : L i ≤ 8 * (h : ℝ) * Real.log 2 * (max c 0 + 1) * (L i) ^ β := by
    have hLog2Nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hhNonneg : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
    calc
      L i ≤ 2 * (d i : ℝ) * Real.log 2 := hLLeLog2
      _ ≤ 2 * (4 * (h : ℝ) * ((d i / h - 1 : Nat) : ℝ)) * Real.log 2 := by
          gcongr
      _ ≤ 2 * (4 * (h : ℝ) * ((max c 0 + 1) * (L i) ^ β)) * Real.log 2 := by
          have : ((d i / h - 1 : Nat) : ℝ) ≤ (max c 0 + 1) * (L i) ^ β := le_trans hDivN hCBound
          gcongr
      _ = 8 * (h : ℝ) * Real.log 2 * (max c 0 + 1) * (L i) ^ β := by ring
  have hSplit : (L i) ^ (1 - β) * (L i) ^ β = L i := by
    have hLPos : 0 < L i := by linarith
    rw [← Real.rpow_add hLPos]
    simp
  have hLBetaPos : 0 < (L i) ^ β := Real.rpow_pos_of_pos (by linarith) _
  have hCancel : (L i) ^ (1 - β) ≤ 8 * (h : ℝ) * Real.log 2 * (max c 0 + 1) := by
    have h1 : (L i) ^ (1 - β) * (L i) ^ β ≤
        (8 * (h : ℝ) * Real.log 2 * (max c 0 + 1)) * (L i) ^ β := by
      linarith [hSplit, hLUpper]
    exact le_of_mul_le_mul_right h1 hLBetaPos
  dsimp [K] at hKI
  linarith

/-- **`ButterflyNet` Defeats All Valiant Cut Schedules**: at `n = 2 ^ d` inputs, `d * 2 ^ d`
binary gates, and depth `d < 2 ^ (Nat.log 2 d + 1)`, no Valiant cut schedule `t ≥ 1` keeps
`2 * t * (d * 2 ^ d) / (Nat.log 2 d + 1) + 1` within `O(n * (log n) ^ α)` for any `α < 1`. -/
theorem source_escapes_valiant_shallow_wall (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (t : Nat → Nat) (ht : ∀ i, 1 ≤ t i) (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((2 * t i * binaryGateCount (source (d i)).circuit /
          (Nat.log 2 (d i) + 1) + 1 : Nat) : ℝ) ≤
        c * ((2 ^ d i : Nat) : ℝ) * (Real.log (((2 ^ d i : Nat) : ℝ) + 16)) ^ α) := by
  let n : Nat → Nat := fun i => 2 ^ d i
  let sg : Nat → Nat := fun i => binaryGateCount (source (d i)).circuit
  let kBit : Nat → Nat := fun i => Nat.log 2 (d i) + 1
  have hnNat : Tendsto n atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hd b
      exact ⟨M, fun i hi => by
        have hdi := hM i hi
        dsimp [n]
        exact le_trans hdi (le_of_lt (Nat.lt_two_pow_self (n := d i)))⟩
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnNat
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCgPos : 0 < 1 / (2 * Real.log 2) := by positivity
  have hGates : ∀ᶠ i in atTop,
      (1 / (2 * Real.log 2)) * (n i : ℝ) * Real.log ((n i : ℝ) + 16) ≤ (sg i : ℝ) := by
    filter_upwards [hd.eventually_ge_atTop 4] with i hd4
    have hEqSg : sg i = d i * n i := by simpa [sg, n] using source_binaryGateCount (d i)
    have hPowBound : (n i : ℝ) + 16 < (2 : ℝ) ^ (d i + 2) := by
      have h16 : 16 < 2 ^ (d i + 1) := by
        have : 2 ^ 5 ≤ 2 ^ (d i + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hNat : n i + 16 < 2 ^ (d i + 2) := by
        dsimp [n]
        rw [Nat.pow_succ]
        omega
      exact_mod_cast hNat
    have hLLe : Real.log ((n i : ℝ) + 16) ≤ ((d i : ℝ) + 2) * Real.log 2 := by
      have hPosL : 0 < (n i : ℝ) + 16 := by positivity
      have h := Real.log_le_log hPosL hPowBound.le
      rw [Real.log_pow] at h
      push_cast at h
      exact h
    have hDReal : (4 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hd4
    have hLin : (d i : ℝ) + 2 ≤ 2 * (d i : ℝ) := by linarith
    have hLogDiv : (1 / (2 * Real.log 2)) * Real.log ((n i : ℝ) + 16) ≤ (d i : ℝ) := by
      calc
        (1 / (2 * Real.log 2)) * Real.log ((n i : ℝ) + 16)
          ≤ (1 / (2 * Real.log 2)) * (((d i : ℝ) + 2) * Real.log 2) := by
              exact mul_le_mul_of_nonneg_left hLLe (by positivity)
        _ = ((d i : ℝ) + 2) / 2 := by field_simp
        _ ≤ (d i : ℝ) := by linarith
    have hSgEqR : (sg i : ℝ) = (d i : ℝ) * (n i : ℝ) := by
      rw [hEqSg]; push_cast; rfl
    calc
      (1 / (2 * Real.log 2)) * (n i : ℝ) * Real.log ((n i : ℝ) + 16)
        = (n i : ℝ) * ((1 / (2 * Real.log 2)) * Real.log ((n i : ℝ) + 16)) := by ring
      _ ≤ (n i : ℝ) * (d i : ℝ) := mul_le_mul_of_nonneg_left hLogDiv (by positivity)
      _ = (sg i : ℝ) := by rw [hSgEqR]; ring
  have hShallow : ∀ᶠ i in atTop,
      (kBit i : ℝ) ≤
        (1 / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) +
          ((Real.log (1 / Real.log 2 + 1)) / Real.log 2 + 1) := by
    filter_upwards [hd.eventually_ge_atTop 4, hnReal.eventually_ge_atTop (Real.exp 1)] with
        i hd4 hNExp
    have hPowLog : (2 : ℝ) ^ Nat.log 2 (d i) ≤ (d i : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hDLogLe : (d i : ℝ) * Real.log 2 ≤ Real.log ((n i : ℝ) + 16) := by
      have h2Pow : (2 : ℝ) ^ d i ≤ (n i : ℝ) + 16 := by
        have : n i ≤ n i + 16 := Nat.le_add_right _ _
        have hReal : (n i : ℝ) ≤ (n i : ℝ) + 16 := by linarith
        simp [n]
      have hPos : (0 : ℝ) < (2 : ℝ) ^ d i := by positivity
      simpa [Real.log_pow] using Real.log_le_log hPos h2Pow
    have hLPos : 0 < Real.log ((n i : ℝ) + 16) := by
      have h1 : 1 ≤ Real.log ((n i : ℝ) + 16) := by
        calc
          1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log ((n i : ℝ) + 16) := Real.log_le_log (Real.exp_pos 1) (by linarith)
      linarith
    have h2PowLe : (2 : ℝ) ^ Nat.log 2 (d i) ≤
        (1 / Real.log 2 + 1) * Real.log ((n i : ℝ) + 16) := by
      have hDLe : (d i : ℝ) ≤ (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) := by
        calc
          (d i : ℝ) = ((d i : ℝ) * Real.log 2) / Real.log 2 := by field_simp
          _ ≤ Real.log ((n i : ℝ) + 16) / Real.log 2 :=
              div_le_div_of_nonneg_right hDLogLe hLog2Pos.le
          _ = (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) := by ring
      have hSub : (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) ≤
          (1 / Real.log 2 + 1) * Real.log ((n i : ℝ) + 16) := by
        nlinarith [hLPos]
      exact hPowLog.trans (hDLe.trans hSub)
    have hLogPow : ((Nat.log 2 (d i) : ℝ)) * Real.log 2 ≤
        Real.log (1 / Real.log 2 + 1) + Real.log (Real.log ((n i : ℝ) + 16)) := by
      have hPowPos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 (d i) := by positivity
      have hPosA : 0 < 1 / Real.log 2 + 1 := by positivity
      have h := Real.log_le_log hPowPos h2PowLe
      rw [Real.log_pow, Real.log_mul hPosA.ne' hLPos.ne'] at h
      exact h
    have hkEq : (kBit i : ℝ) = (Nat.log 2 (d i) : ℝ) + 1 := by
      dsimp [kBit]; push_cast; rfl
    rw [hkEq]
    have hDiv : (Nat.log 2 (d i) : ℝ) ≤
        (1 / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) +
          (Real.log (1 / Real.log 2 + 1)) / Real.log 2 := by
      have h := div_le_div_of_nonneg_right hLogPow hLog2Pos.le
      calc
        (Nat.log 2 (d i) : ℝ) = ((Nat.log 2 (d i) : ℝ) * Real.log 2) / Real.log 2 := by field_simp
        _ ≤ (Real.log (1 / Real.log 2 + 1) + Real.log (Real.log ((n i : ℝ) + 16))) / Real.log 2 := h
        _ = (1 / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) +
            (Real.log (1 / Real.log 2 + 1)) / Real.log 2 := by ring
    linarith
  exact valiant_shallow_nlogn_wall hnNat (fun _ => Nat.succ_pos _) ht hCgPos (by positivity)
    hGates hShallow c α hα

end ButterflyNet

/-! ### 3. Balanced Vertex Separator Lower Bound (`Ω(n)` Congestion Wall on `ButterflyNet`) -/

/-- Undirected parent-child adjacency in a `Circuit n w`. -/
inductive CircuitEdge {n : Nat} : {w : Nat} → Circuit n w → Fin w → Fin w → Prop where
  | cast {w : Nat} (earlier : Circuit n w) (g : Gate w) {u v : Fin w} :
      CircuitEdge earlier u v → CircuitEdge (earlier.snoc g) u.castSucc v.castSucc
  | not_in {w : Nat} (earlier : Circuit n w) (a : Fin w) :
      CircuitEdge (earlier.snoc (.not a)) a.castSucc (Fin.last w)
  | not_out {w : Nat} (earlier : Circuit n w) (a : Fin w) :
      CircuitEdge (earlier.snoc (.not a)) (Fin.last w) a.castSucc
  | and_left {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.and a b)) a.castSucc (Fin.last w)
  | and_right {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.and a b)) b.castSucc (Fin.last w)
  | and_out_left {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.and a b)) (Fin.last w) a.castSucc
  | and_out_right {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.and a b)) (Fin.last w) b.castSucc
  | or_left {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.or a b)) a.castSucc (Fin.last w)
  | or_right {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.or a b)) b.castSucc (Fin.last w)
  | or_out_left {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.or a b)) (Fin.last w) a.castSucc
  | or_out_right {w : Nat} (earlier : Circuit n w) (a b : Fin w) :
      CircuitEdge (earlier.snoc (.or a b)) (Fin.last w) b.castSucc

theorem CircuitEdge.symm {n w : Nat} {c : Circuit n w} {u v : Fin w}
    (h : CircuitEdge c u v) : CircuitEdge c v u := by
  induction h with
  | cast earlier g _ ih => exact .cast earlier g ih
  | not_in earlier a => exact .not_out earlier a
  | not_out earlier a => exact .not_in earlier a
  | and_left earlier a b => exact .and_out_left earlier a b
  | and_right earlier a b => exact .and_out_right earlier a b
  | and_out_left earlier a b => exact .and_left earlier a b
  | and_out_right earlier a b => exact .and_right earlier a b
  | or_left earlier a b => exact .or_out_left earlier a b
  | or_right earlier a b => exact .or_out_right earlier a b
  | or_out_left earlier a b => exact .or_left earlier a b
  | or_out_right earlier a b => exact .or_right earlier a b

/-- Undirected reachability in `c` avoiding every vertex in cut `S`. -/
inductive UndirectedReachAvoiding {n w : Nat} (c : Circuit n w) (S : Finset (Fin w)) :
    Fin w → Fin w → Prop where
  | refl (u : Fin w) (hu : u ∉ S) : UndirectedReachAvoiding c S u u
  | step {u v z : Fin w} (hu : u ∉ S) (hEdge : CircuitEdge c u v)
      (hRest : UndirectedReachAvoiding c S v z) : UndirectedReachAvoiding c S u z

theorem UndirectedReachAvoiding.trans {n w : Nat} {c : Circuit n w} {S : Finset (Fin w)}
    {u v z : Fin w} (h1 : UndirectedReachAvoiding c S u v)
    (h2 : UndirectedReachAvoiding c S v z) : UndirectedReachAvoiding c S u z := by
  induction h1 with
  | refl _ _ => exact h2
  | step hu hEdge _ ih => exact .step hu hEdge (ih h2)

/-- A vertex cut `S` separates input sets `A, B ⊆ Fin n` in circuit `c` when no undirected walk
in `c \ S` connects any input in `A` to any input in `B`. -/
def SeparatesInputs {n w : Nat} (c : Circuit n w) (S : Finset (Fin w))
    (A B : Finset (Fin n)) (hnw : n ≤ w) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B,
    ¬ UndirectedReachAvoiding c S ⟨x.val, lt_of_lt_of_le x.isLt hnw⟩
      ⟨y.val, lt_of_lt_of_le y.isLt hnw⟩

namespace ButterflyNet

theorem wires_eq (d : Nat) : (source d).wires = (d + 1) * 2 ^ d :=
  LayeredRing.ringWires_eq (2 ^ d) d

theorem inputs_le_wires (d : Nat) : 2 ^ d ≤ (source d).wires := by
  rw [wires_eq]
  exact Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d)

/-- Canonical wire `(ℓ, z)` in `ButterflyNet.source d`. -/
def bflyWire (d ℓ z : Nat) (hℓ : ℓ ≤ d) (hz : z < 2 ^ d) : Fin (source d).wires :=
  ⟨ℓ * 2 ^ d + z, by
    rw [wires_eq]
    nlinarith⟩

private theorem CircuitEdge.snoc_lift {n w : Nat} (earlier : Circuit n w) (g : Gate w)
    {u v : Fin w} (h : CircuitEdge earlier u v) :
    CircuitEdge (earlier.snoc g) u.castSucc v.castSucc :=
  .cast earlier g h

private theorem CircuitEdge.appendBflyRow_lift (d ℓ : Nat) (hℓ : ℓ < d)
    (c : Circuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) ℓ)) :
    ∀ j (hj : j ≤ 2 ^ d) {u v : Fin (LayeredRing.ringWires (2 ^ d) ℓ)},
      CircuitEdge c u v →
        CircuitEdge (appendBflyRow d ℓ hℓ j hj c) ⟨u.val, by omega⟩ ⟨v.val, by omega⟩
  | 0, _, _, _, h => h
  | j + 1, hj, _, _, h => by
    change CircuitEdge ((appendBflyRow d ℓ hℓ j (by omega) c).snoc (bflyGate d ℓ j hℓ (by omega)))
      _ _
    exact .cast _ _ (CircuitEdge.appendBflyRow_lift d ℓ hℓ c j (by omega) h)

private theorem CircuitEdge.buildBfly_lift (d D₁ D₂ : Nat) (h12 : D₁ ≤ D₂) (h2 : D₂ ≤ d)
    {u v : Fin (LayeredRing.ringWires (2 ^ d) D₁)}
    (h : CircuitEdge (buildBfly d D₁ (le_trans h12 h2)) u v) :
    CircuitEdge (buildBfly d D₂ h2)
      ⟨u.val, lt_of_lt_of_le u.isLt (by
        rw [LayeredRing.ringWires_eq, LayeredRing.ringWires_eq]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h12 1))⟩
      ⟨v.val, lt_of_lt_of_le v.isLt (by
        rw [LayeredRing.ringWires_eq, LayeredRing.ringWires_eq]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h12 1))⟩ := by
  induction D₂ generalizing D₁ with
  | zero =>
    have hEq : D₁ = 0 := by omega
    subst hEq
    exact h
  | succ D₂ ih =>
    by_cases hEq : D₁ = D₂ + 1
    · subst hEq; exact h
    · have h12' : D₁ ≤ D₂ := by omega
      have hLift := ih D₁ h12' (by omega) h
      change CircuitEdge (appendBflyRow d D₂ (by omega) (2 ^ d) (le_rfl)
        (buildBfly d D₂ (by omega))) _ _
      exact CircuitEdge.appendBflyRow_lift d D₂ (by omega) (buildBfly d D₂ (by omega))
        (2 ^ d) (le_rfl) hLift

private theorem appendBflyRow_edge_at (d ℓ j : Nat) (hℓ : ℓ < d) (hj : j < 2 ^ d) :
    ∀ k (hk : k ≤ 2 ^ d) (hjk : j < k),
      CircuitEdge (appendBflyRow d ℓ hℓ k hk (buildBfly d ℓ (by omega)))
        ⟨ℓ * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]
          have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
          omega⟩
        ⟨(ℓ + 1) * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; omega⟩ ∧
      CircuitEdge (appendBflyRow d ℓ hℓ k hk (buildBfly d ℓ (by omega)))
        ⟨ℓ * 2 ^ d + flipBit j ℓ, by
          have hf := flipBit_lt hj hℓ
          rw [LayeredRing.ringWires_eq]
          have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
          omega⟩
        ⟨(ℓ + 1) * 2 ^ d + j, by
          rw [LayeredRing.ringWires_eq]; omega⟩
  | 0, _, hjk => by omega
  | k + 1, hk, hjk => by
    let N := 2 ^ d
    have hBase : LayeredRing.ringWires N ℓ = (ℓ + 1) * N := LayeredRing.ringWires_eq N ℓ
    by_cases hEq : j = k
    · subst hEq
      let prev := appendBflyRow d ℓ hℓ j (by omega) (buildBfly d ℓ (by omega))
      let a : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + j, by
        rw [hBase]
        have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
        omega⟩
      let b : Fin (LayeredRing.ringWires N ℓ + j) := ⟨ℓ * N + flipBit j ℓ, by
        have hf := flipBit_lt hj hℓ
        rw [hBase]
        have hMul : ℓ * N + N = (ℓ + 1) * N := by ring
        omega⟩
      have hLastVal : (Fin.last (LayeredRing.ringWires N ℓ + j)).val = (ℓ + 1) * N + j := by
        simp [Fin.val_last, hBase]
      have hEdgeA : CircuitEdge (prev.snoc (bflyGate d ℓ j hℓ hj)) a.castSucc (Fin.last _) := by
        dsimp [bflyGate]
        by_cases hPar : ℓ % 2 = 0
        · simp only [hPar, ↓reduceIte]; exact .and_left prev a b
        · simp only [hPar, ↓reduceIte]; exact .or_left prev a b
      have hEdgeB : CircuitEdge (prev.snoc (bflyGate d ℓ j hℓ hj)) b.castSucc (Fin.last _) := by
        dsimp [bflyGate]
        by_cases hPar : ℓ % 2 = 0
        · simp only [hPar, ↓reduceIte]; exact .and_right prev a b
        · simp only [hPar, ↓reduceIte]; exact .or_right prev a b
      constructor
      · have h1 : a.castSucc = ⟨ℓ * 2 ^ d + j, by
            dsimp only [N]
            rw [LayeredRing.ringWires_eq, Nat.succ_mul]
            have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            have h2 : (ℓ + 1) * 2 ^ d ≤ (ℓ + 1) * 2 ^ d + 2 ^ d := Nat.le_add_right _ _
            omega⟩ := Fin.ext rfl
        have h2 : Fin.last (LayeredRing.ringWires N ℓ + j) = ⟨(ℓ + 1) * 2 ^ d + j, by
            dsimp only [N]
            rw [LayeredRing.ringWires_eq]; omega⟩ := by
          apply Fin.ext
          exact hLastVal
        rw [← h1, ← h2]
        exact hEdgeA
      · have h1 : b.castSucc = ⟨ℓ * 2 ^ d + flipBit j ℓ, by
            have hf := flipBit_lt hj hℓ
            dsimp only [N]
            rw [LayeredRing.ringWires_eq, Nat.succ_mul]
            have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
            have h2 : (ℓ + 1) * 2 ^ d ≤ (ℓ + 1) * 2 ^ d + 2 ^ d := Nat.le_add_right _ _
            omega⟩ := Fin.ext rfl
        have h2 : Fin.last (LayeredRing.ringWires N ℓ + j) = ⟨(ℓ + 1) * 2 ^ d + j, by
            dsimp only [N]
            rw [LayeredRing.ringWires_eq]; omega⟩ := by
          apply Fin.ext
          exact hLastVal
        rw [← h1, ← h2]
        exact hEdgeB
    · have ih := appendBflyRow_edge_at d ℓ j hℓ hj k (by omega) (by omega)
      constructor
      · exact .cast _ _ ih.1
      · exact .cast _ _ ih.2

theorem bfly_straight_edge (d ℓ : Nat) (hℓ : ℓ < d) (j : Nat) (hj : j < 2 ^ d) :
    CircuitEdge (source d).circuit
      (bflyWire d ℓ j (by omega) hj)
      (bflyWire d (ℓ + 1) j (by omega) hj) := by
  have hRow := (appendBflyRow_edge_at d ℓ j hℓ hj (2 ^ d) (le_rfl) hj).1
  exact CircuitEdge.buildBfly_lift d (ℓ + 1) d (by omega) (le_rfl) hRow

theorem bfly_cross_edge (d ℓ : Nat) (hℓ : ℓ < d) (j : Nat) (hj : j < 2 ^ d) :
    CircuitEdge (source d).circuit
      (bflyWire d ℓ (flipBit j ℓ) (by omega) (flipBit_lt hj hℓ))
      (bflyWire d (ℓ + 1) j (by omega) hj) := by
  have hRow := (appendBflyRow_edge_at d ℓ j hℓ hj (2 ^ d) (le_rfl) hj).2
  exact CircuitEdge.buildBfly_lift d (ℓ + 1) d (by omega) (le_rfl) hRow

/-- Canonical bit-fixing butterfly route at stage `ℓ`, switching `x`'s low `ℓ` bits to `y`'s. -/
def bflyRoute (_d x y ℓ : Nat) : Nat :=
  (x / 2 ^ ℓ) * 2 ^ ℓ + y % 2 ^ ℓ

theorem bflyRoute_zero (d x y : Nat) : bflyRoute d x y 0 = x := by
  simp [bflyRoute, Nat.mod_one]

theorem bflyRoute_top {d x y : Nat} (hx : x < 2 ^ d) (hy : y < 2 ^ d) :
    bflyRoute d x y d = y := by
  simp [bflyRoute, Nat.div_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem bflyRoute_lt {d x y ℓ : Nat} (hx : x < 2 ^ d) (_hy : y < 2 ^ d) (hℓ : ℓ ≤ d) :
    bflyRoute d x y ℓ < 2 ^ d := by
  unfold bflyRoute
  have hPow : 2 ^ d = 2 ^ ℓ * 2 ^ (d - ℓ) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hℓ]
  have hP : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  have hxDiv : x / 2 ^ ℓ < 2 ^ (d - ℓ) := by
    rw [hPow] at hx
    exact Nat.div_lt_of_lt_mul hx
  have hyMod : y % 2 ^ ℓ < 2 ^ ℓ := Nat.mod_lt y hP
  have hMulLe : (x / 2 ^ ℓ + 1) * 2 ^ ℓ ≤ 2 ^ (d - ℓ) * 2 ^ ℓ :=
    Nat.mul_le_mul_right (2 ^ ℓ) hxDiv
  have hPowComm : 2 ^ (d - ℓ) * 2 ^ ℓ = 2 ^ d := by
    rw [hPow, Nat.mul_comm]
  nlinarith

theorem bflyRoute_step (x y ℓ : Nat) :
    bflyRoute d x y (ℓ + 1) = bflyRoute d x y ℓ ∨
      bflyRoute d x y (ℓ + 1) = flipBit (bflyRoute d x y ℓ) ℓ := by
  unfold bflyRoute flipBit
  let P := 2 ^ ℓ
  have hP : 0 < P := Nat.two_pow_pos ℓ
  have hP2 : 2 ^ (ℓ + 1) = 2 * P := by rw [Nat.pow_succ, Nat.mul_comm]
  have hxDivMod : x / P = 2 * (x / (2 * P)) + (x / P) % 2 := by
    have h1 := Nat.div_add_mod (x / P) 2
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm P 2] at h1
    exact h1.symm
  have hyMod2P : y % (2 * P) = ((y / P) % 2) * P + y % P := by
    have hyDM : y = (y / P) * P + y % P := by
      have h := Nat.div_add_mod y P
      linarith [Nat.mul_comm P (y / P)]
    have hyDM2 : y / P = 2 * (y / (2 * P)) + (y / P) % 2 := by
      have h1 := Nat.div_add_mod (y / P) 2
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm P 2] at h1
      exact h1.symm
    have hyExpand : y = (y / (2 * P)) * (2 * P) + (((y / P) % 2) * P + y % P) := by
      conv_lhs => rw [hyDM, hyDM2]
      ring
    have hySmall : ((y / P) % 2) * P + y % P < 2 * P := by
      have h1 : (y / P) % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide : 0 < 2))
      have h2 : y % P < P := Nat.mod_lt _ hP
      nlinarith
    have hMod := congrArg (· % (2 * P)) hyExpand
    rw [Nat.add_comm ((y / (2 * P)) * (2 * P)), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hySmall] at hMod
    exact hMod
  have hBitR : (((x / P) * P + y % P) / P) % 2 = (x / P) % 2 := by
    have hDiv : ((x / P) * P + y % P) / P = x / P := by
      rw [Nat.add_comm ((x / P) * P), Nat.add_mul_div_right _ _ hP,
        Nat.div_eq_of_lt (Nat.mod_lt y hP), Nat.zero_add]
    rw [hDiv]
  have hL : (x / 2 ^ (ℓ + 1)) * 2 ^ (ℓ + 1) + y % 2 ^ (ℓ + 1) =
      (x / (2 * P)) * (2 * P) + ((y / P) % 2) * P + y % P := by
    rw [hP2, hyMod2P]; ring
  have hR : (x / P) * P + y % P = (x / (2 * P)) * (2 * P) + ((x / P) % 2) * P + y % P := by
    conv_lhs => rw [hxDivMod]
    ring
  change (x / 2 ^ (ℓ + 1)) * 2 ^ (ℓ + 1) + y % 2 ^ (ℓ + 1) = (x / P) * P + y % P ∨
    (x / 2 ^ (ℓ + 1)) * 2 ^ (ℓ + 1) + y % 2 ^ (ℓ + 1) =
      if (((x / P) * P + y % P) / P) % 2 = 0 then (x / P) * P + y % P + P
      else (x / P) * P + y % P - P
  rw [hL, hBitR, hR]
  have hxBit := Nat.mod_lt (x / P) (by decide : 0 < 2)
  have hyBit := Nat.mod_lt (y / P) (by decide : 0 < 2)
  by_cases hx0 : (x / P) % 2 = 0 <;> by_cases hy0 : (y / P) % 2 = 0
  · left; simp [hx0, hy0]
  · right; have hy1 : (y / P) % 2 = 1 := by omega
    simp [hx0, hy1]; ring
  · right; have hx1 : (x / P) % 2 = 1 := by omega
    simp [hx1, hy0]; omega
  · left; have hx1 : (x / P) % 2 = 1 := by omega
    have hy1 : (y / P) % 2 = 1 := by omega
    simp [hx1, hy1]

/-- Predicate indicating whether wire `u` lies on the canonical butterfly+return walk
routing input pair `(x, y)`. -/
def hitsBflyWalk (d : Nat) (u : Fin (source d).wires) (x y : Fin (2 ^ d)) : Prop :=
  u.val % 2 ^ d = bflyRoute d x.val y.val (u.val / 2 ^ d) ∨ y.val = u.val % 2 ^ d

instance (d : Nat) (u : Fin (source d).wires) (x y : Fin (2 ^ d)) :
    Decidable (hitsBflyWalk d u x y) :=
  inferInstanceAs (Decidable (u.val % 2 ^ d = bflyRoute d x.val y.val (u.val / 2 ^ d) ∨
    y.val = u.val % 2 ^ d))

private theorem wire_div_le (d : Nat) (u : Fin (source d).wires) : u.val / 2 ^ d ≤ d := by
  have hu : u.val < (d + 1) * 2 ^ d := by
    have hLt := u.isLt
    have hEq := wires_eq d
    omega
  have hLt : u.val / 2 ^ d < d + 1 :=
    Nat.div_lt_of_lt_mul (by linarith [Nat.mul_comm (d + 1) (2 ^ d)])
  omega

theorem bfly_walk_hits_separator (d : Nat) (S : Finset (Fin (source d).wires))
    {A B : Finset (Fin (2 ^ d))} (hSep : SeparatesInputs (source d).circuit S A B (inputs_le_wires d))
    {x y : Fin (2 ^ d)} (hx : x ∈ A) (hy : y ∈ B) :
    ∃ u ∈ S, hitsBflyWalk d u x y := by
  by_contra hNone
  push Not at hNone
  have hFwdNotS : ∀ ℓ (hℓ : ℓ ≤ d),
      bflyWire d ℓ (bflyRoute d x.val y.val ℓ) hℓ (bflyRoute_lt x.isLt y.isLt hℓ) ∉ S := by
    intro ℓ hℓ hMem
    have hHits := hNone _ hMem
    apply hHits
    left
    have hDM := bfly_div_mod_layer (L := ℓ) (bflyRoute_lt x.isLt y.isLt hℓ)
    simp only [bflyWire]
    rw [hDM.1, hDM.2]
  have hBwdNotS : ∀ ℓ (hℓ : ℓ ≤ d), bflyWire d ℓ y.val hℓ y.isLt ∉ S := by
    intro ℓ hℓ hMem
    have hHits := hNone _ hMem
    apply hHits
    right
    exact (bfly_div_mod_layer (L := ℓ) y.isLt).2.symm
  have hFwd : ∀ ℓ (hℓ : ℓ ≤ d),
      UndirectedReachAvoiding (source d).circuit S
        ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩
        (bflyWire d ℓ (bflyRoute d x.val y.val ℓ) hℓ (bflyRoute_lt x.isLt y.isLt hℓ)) := by
    intro ℓ
    induction ℓ with
    | zero =>
      intro h0
      have hW : ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩ =
          bflyWire d 0 (bflyRoute d x.val y.val 0) h0 (bflyRoute_lt x.isLt y.isLt h0) := by
        apply Fin.ext
        simp [bflyWire, bflyRoute_zero]
      rw [hW]
      exact .refl _ (hFwdNotS 0 h0)
    | succ ℓ ih =>
      intro hSucc
      have hPre := ih (by omega)
      have hStepEdge : CircuitEdge (source d).circuit
          (bflyWire d ℓ (bflyRoute d x.val y.val ℓ) (by omega)
            (bflyRoute_lt x.isLt y.isLt (by omega)))
          (bflyWire d (ℓ + 1) (bflyRoute d x.val y.val (ℓ + 1)) hSucc
            (bflyRoute_lt x.isLt y.isLt hSucc)) := by
        rcases bflyRoute_step (d := d) x.val y.val ℓ with hSame | hFlip
        · have hEqW : bflyWire d (ℓ + 1) (bflyRoute d x.val y.val (ℓ + 1)) hSucc
              (bflyRoute_lt x.isLt y.isLt hSucc) =
              bflyWire d (ℓ + 1) (bflyRoute d x.val y.val ℓ) hSucc
                (bflyRoute_lt x.isLt y.isLt (by omega)) := by
            apply Fin.ext
            change (ℓ + 1) * 2 ^ d + bflyRoute d x.val y.val (ℓ + 1) =
              (ℓ + 1) * 2 ^ d + bflyRoute d x.val y.val ℓ
            rw [hSame]
          rw [hEqW]
          exact bfly_straight_edge d ℓ (by omega) (bflyRoute d x.val y.val ℓ)
            (bflyRoute_lt x.isLt y.isLt (by omega))
        · have hInv : flipBit (bflyRoute d x.val y.val (ℓ + 1)) ℓ = bflyRoute d x.val y.val ℓ := by
            rw [hFlip, flipBit_involutive]
          have hEqW : bflyWire d ℓ (bflyRoute d x.val y.val ℓ) (by omega)
              (bflyRoute_lt x.isLt y.isLt (by omega)) =
              bflyWire d ℓ (flipBit (bflyRoute d x.val y.val (ℓ + 1)) ℓ) (by omega)
                (flipBit_lt (bflyRoute_lt x.isLt y.isLt hSucc) (by omega)) := by
            apply Fin.ext
            change ℓ * 2 ^ d + bflyRoute d x.val y.val ℓ =
              ℓ * 2 ^ d + flipBit (bflyRoute d x.val y.val (ℓ + 1)) ℓ
            rw [hInv]
          rw [hEqW]
          exact bfly_cross_edge d ℓ (by omega) (bflyRoute d x.val y.val (ℓ + 1))
            (bflyRoute_lt x.isLt y.isLt hSucc)
      have hOne : UndirectedReachAvoiding (source d).circuit S
          (bflyWire d ℓ (bflyRoute d x.val y.val ℓ) (by omega)
            (bflyRoute_lt x.isLt y.isLt (by omega)))
          (bflyWire d (ℓ + 1) (bflyRoute d x.val y.val (ℓ + 1)) hSucc
            (bflyRoute_lt x.isLt y.isLt hSucc)) :=
        .step (hFwdNotS ℓ (by omega)) hStepEdge (.refl _ (hFwdNotS (ℓ + 1) hSucc))
      exact hPre.trans hOne
  have hBwd : ∀ ℓ (hℓ : ℓ ≤ d),
      UndirectedReachAvoiding (source d).circuit S
        (bflyWire d ℓ y.val hℓ y.isLt)
        ⟨y.val, lt_of_lt_of_le y.isLt (inputs_le_wires d)⟩ := by
    intro ℓ
    induction ℓ with
    | zero =>
      intro h0
      have hW : bflyWire d 0 y.val h0 y.isLt =
          ⟨y.val, lt_of_lt_of_le y.isLt (inputs_le_wires d)⟩ := by
        apply Fin.ext; simp [bflyWire]
      rw [← hW]
      exact .refl _ (hBwdNotS 0 h0)
    | succ ℓ ih =>
      intro hSucc
      have hEdge := (bfly_straight_edge d ℓ (by omega) y.val y.isLt).symm
      exact .step (hBwdNotS (ℓ + 1) hSucc) hEdge (ih (by omega))
  have hMid : bflyWire d d (bflyRoute d x.val y.val d) (le_rfl) (bflyRoute_lt x.isLt y.isLt le_rfl) =
      bflyWire d d y.val (le_rfl) y.isLt := by
    apply Fin.ext
    change d * 2 ^ d + bflyRoute d x.val y.val d = d * 2 ^ d + y.val
    rw [bflyRoute_top x.isLt y.isLt]
  have hReach : UndirectedReachAvoiding (source d).circuit S
      ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩
      ⟨y.val, lt_of_lt_of_le y.isLt (inputs_le_wires d)⟩ := by
    refine (hFwd d le_rfl).trans ?_
    rw [hMid]
    exact hBwd d le_rfl
  exact hSep x hx y hy hReach

theorem bfly_vertex_congestion_le (d : Nat) (u : Fin (source d).wires) :
    (Finset.univ.filter fun p : Fin (2 ^ d) × Fin (2 ^ d) => hitsBflyWalk d u p.1 p.2).card ≤
      2 * 2 ^ d := by
  let fwdSet : Finset (Fin (2 ^ d) × Fin (2 ^ d)) :=
    Finset.univ.filter fun p => u.val % 2 ^ d = bflyRoute d p.1.val p.2.val (u.val / 2 ^ d)
  let bwdSet : Finset (Fin (2 ^ d) × Fin (2 ^ d)) :=
    Finset.univ.filter fun p => p.2.val = u.val % 2 ^ d
  have hSub : (Finset.univ.filter fun p : Fin (2 ^ d) × Fin (2 ^ d) =>
      hitsBflyWalk d u p.1 p.2) ⊆ fwdSet ∪ bwdSet := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
  let L := u.val / 2 ^ d
  have hL : L ≤ d := wire_div_le d u
  have hPPos : 0 < 2 ^ L := Nat.two_pow_pos L
  let gFwd : Fin (2 ^ d) × Fin (2 ^ d) → Fin (2 ^ L) × Fin (2 ^ (d - L)) := fun p =>
    (⟨p.1.val % 2 ^ L, Nat.mod_lt _ hPPos⟩,
     ⟨p.2.val / 2 ^ L, by
       have h2 : p.2.val < 2 ^ L * 2 ^ (d - L) := by
         rw [← Nat.pow_add, Nat.add_sub_cancel' hL]; exact p.2.isLt
       exact Nat.div_lt_of_lt_mul h2⟩)
  have hFwdCard : fwdSet.card ≤ (Finset.univ : Finset (Fin (2 ^ L) × Fin (2 ^ (d - L)))).card := by
    refine Finset.card_le_card_of_injOn gFwd (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
    intro p₁ hp₁ p₂ hp₂ hEq
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
    have hP1 : p₁.1.val % 2 ^ L = p₂.1.val % 2 ^ L :=
      congrArg (fun z => z.1.val) hEq
    have hP2 : p₁.2.val / 2 ^ L = p₂.2.val / 2 ^ L :=
      congrArg (fun z => z.2.val) hEq
    have hEqR : bflyRoute d p₁.1.val p₁.2.val L = bflyRoute d p₂.1.val p₂.2.val L :=
      h1.symm.trans h2
    dsimp [bflyRoute] at hEqR
    have hDM1 := bfly_div_mod_layer (N := 2 ^ L) (L := p₁.1.val / 2 ^ L)
      (Nat.mod_lt p₁.2.val hPPos)
    have hDM2 := bfly_div_mod_layer (N := 2 ^ L) (L := p₂.1.val / 2 ^ L)
      (Nat.mod_lt p₂.2.val hPPos)
    have hDivX : p₁.1.val / 2 ^ L = p₂.1.val / 2 ^ L := by
      have h := congrArg (· / 2 ^ L) hEqR
      rw [hDM1.1, hDM2.1] at h
      exact h
    have hModY : p₁.2.val % 2 ^ L = p₂.2.val % 2 ^ L := by
      have h := congrArg (· % 2 ^ L) hEqR
      rw [hDM1.2, hDM2.2] at h
      exact h
    have hxEq : p₁.1.val = p₂.1.val := by
      have d1 := Nat.div_add_mod p₁.1.val (2 ^ L)
      have d2 := Nat.div_add_mod p₂.1.val (2 ^ L)
      rw [hDivX, hP1] at d1
      linarith
    have hyEq : p₁.2.val = p₂.2.val := by
      have d1 := Nat.div_add_mod p₁.2.val (2 ^ L)
      have d2 := Nat.div_add_mod p₂.2.val (2 ^ L)
      rw [hP2, hModY] at d1
      linarith
    exact Prod.ext (Fin.ext hxEq) (Fin.ext hyEq)
  have hFwdLe : fwdSet.card ≤ 2 ^ d := by
    have hU : (Finset.univ : Finset (Fin (2 ^ L) × Fin (2 ^ (d - L)))).card = 2 ^ d := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← Nat.pow_add,
        Nat.add_comm L (d - L), Nat.sub_add_cancel hL]
    omega
  have hBwdCard : bwdSet.card ≤ (Finset.univ : Finset (Fin (2 ^ d))).card := by
    refine Finset.card_le_card_of_injOn (fun p => p.1)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
    intro p₁ hp₁ p₂ hp₂ hEq
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
    exact Prod.ext hEq (Fin.ext (h1.trans h2.symm))
  have hBwdLe : bwdSet.card ≤ 2 ^ d := by
    simpa [Finset.card_univ, Fintype.card_fin] using hBwdCard
  calc
    (Finset.univ.filter fun p : Fin (2 ^ d) × Fin (2 ^ d) => hitsBflyWalk d u p.1 p.2).card
      ≤ (fwdSet ∪ bwdSet).card := Finset.card_le_card hSub
    _ ≤ fwdSet.card + bwdSet.card := Finset.card_union_le _ _
    _ ≤ 2 ^ d + 2 ^ d := Nat.add_le_add hFwdLe hBwdLe
    _ = 2 * 2 ^ d := by ring

theorem butterfly_separator_lower_bound (d : Nat) (S : Finset (Fin (source d).wires))
    {A B : Finset (Fin (2 ^ d))}
    (hSep : SeparatesInputs (source d).circuit S A B (inputs_le_wires d)) :
    A.card * B.card ≤ 2 * 2 ^ d * S.card := by
  have hSub : A ×ˢ B ⊆
      S.biUnion fun u =>
        Finset.univ.filter fun p : Fin (2 ^ d) × Fin (2 ^ d) => hitsBflyWalk d u p.1 p.2 := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
    obtain ⟨u, huS, huHit⟩ := bfly_walk_hits_separator d S hSep hx hy
    exact Finset.mem_biUnion.mpr ⟨u, huS, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huHit⟩⟩
  calc
    A.card * B.card = (A ×ˢ B).card := (Finset.card_product A B).symm
    _ ≤ (S.biUnion fun u =>
          Finset.univ.filter fun p : Fin (2 ^ d) × Fin (2 ^ d) => hitsBflyWalk d u p.1 p.2).card :=
        Finset.card_le_card hSub
    _ ≤ ∑ u ∈ S, (Finset.univ.filter fun p : Fin (2 ^ d) × Fin (2 ^ d) =>
          hitsBflyWalk d u p.1 p.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, (2 * 2 ^ d) := Finset.sum_le_sum fun u _ => bfly_vertex_congestion_le d u
    _ = 2 * 2 ^ d * S.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

theorem butterfly_balanced_separator_linear (d : Nat) (S : Finset (Fin (source d).wires))
    {A B : Finset (Fin (2 ^ d))}
    (hSep : SeparatesInputs (source d).circuit S A B (inputs_le_wires d))
    (hA : 2 ^ d ≤ 3 * A.card) (hB : 2 ^ d ≤ 3 * B.card) :
    2 ^ d ≤ 18 * S.card := by
  have hLower := butterfly_separator_lower_bound d S hSep
  have hProd : 2 ^ d * 2 ^ d ≤ 2 ^ d * (18 * S.card) := by
    calc
      2 ^ d * 2 ^ d ≤ (3 * A.card) * (3 * B.card) := Nat.mul_le_mul hA hB
      _ = 9 * (A.card * B.card) := by ring
      _ ≤ 9 * (2 * 2 ^ d * S.card) := Nat.mul_le_mul_left 9 hLower
      _ = 2 ^ d * (18 * S.card) := by ring
  exact Nat.le_of_mul_le_mul_left hProd (Nat.two_pow_pos d)

private theorem exists_balanced_bipartition {n m : Nat} (hn : 0 < n)
    (C : Fin m → Finset (Fin n))
    (hCover : ∀ x : Fin n, ∃ i, x ∈ C i)
    (hSmall : ∀ i, 3 * (C i).card ≤ 2 * n) :
    ∃ A B : Finset (Fin n),
      n ≤ 3 * A.card ∧ n ≤ 3 * B.card ∧
      ((∃ i₀, A = C i₀ ∧ B = Finset.univ \ C i₀) ∨
       (∃ k₀ : Nat, k₀ ≤ m ∧
         A = (Finset.range k₀).biUnion (fun j => if hj : j < m then C ⟨j, hj⟩ else ∅) ∧
         B = Finset.univ \ A)) := by
  by_cases hBig : ∃ i, n ≤ 3 * (C i).card
  · obtain ⟨i₀, hi₀⟩ := hBig
    refine ⟨C i₀, Finset.univ \ C i₀, hi₀, ?_, Or.inl ⟨i₀, rfl, rfl⟩⟩
    have hBCard : (Finset.univ \ C i₀).card = n - (C i₀).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hBCard]
    have hi₀Small := hSmall i₀
    omega
  · push Not at hBig
    let U : Nat → Finset (Fin n) := fun k =>
      (Finset.range k).biUnion fun j => if hj : j < m then C ⟨j, hj⟩ else ∅
    have hUM : U m = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true, U, Finset.mem_biUnion, Finset.mem_range]
      obtain ⟨i, hi⟩ := hCover x
      exact ⟨i.val, i.isLt, by simp [i.isLt, hi]⟩
    have hEx : ∃ k, n ≤ 3 * (U k).card := ⟨m, by rw [hUM, Finset.card_univ, Fintype.card_fin]; omega⟩
    let k₀ := Nat.find hEx
    have hk₀Spec : n ≤ 3 * (U k₀).card := Nat.find_spec hEx
    have hk₀Pos : 1 ≤ k₀ := by
      by_contra h0
      have hEq0 : k₀ = 0 := by omega
      have h0Card : (U k₀).card = 0 := by simp [U, hEq0]
      rw [h0Card] at hk₀Spec
      omega
    have hk₀LeM : k₀ ≤ m := by
      by_contra hGt
      have hmLt : m < k₀ := by omega
      have := Nat.find_min hEx hmLt
      rw [hUM, Finset.card_univ, Fintype.card_fin] at this
      omega
    have hPrev : 3 * (U (k₀ - 1)).card < n :=
      Nat.lt_of_not_ge (Nat.find_min hEx (by omega : k₀ - 1 < k₀))
    have hLastLt : k₀ - 1 < m := by omega
    have hUSub : U k₀ ⊆ U (k₀ - 1) ∪ C ⟨k₀ - 1, hLastLt⟩ := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      rcases hx with ⟨j, hjRange, hxJ⟩
      rw [Finset.mem_range] at hjRange
      by_cases hjEq : j = k₀ - 1
      · subst hjEq
        simp only [hLastLt, ↓reduceDIte] at hxJ
        exact Finset.mem_union_right _ hxJ
      · have hjLt : j < k₀ - 1 := by omega
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjLt, hxJ⟩)
    have hUCardLe : (U k₀).card ≤ (U (k₀ - 1)).card + (C ⟨k₀ - 1, hLastLt⟩).card :=
      (Finset.card_le_card hUSub).trans (Finset.card_union_le _ _)
    have hCSmall : 3 * (C ⟨k₀ - 1, hLastLt⟩).card < n := hBig ⟨k₀ - 1, hLastLt⟩
    refine ⟨U k₀, Finset.univ \ U k₀, hk₀Spec, ?_, Or.inr ⟨k₀, hk₀LeM, rfl, rfl⟩⟩
    have hBCard : (Finset.univ \ U k₀).card = n - (U k₀).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hBCard]
    omega

/-- Any vertex separator `S` partitioning `ButterflyNet` inputs into connected components of size
`≤ 2n / 3` must have size `|S| ≥ n / 18`. -/
theorem butterfly_component_separator_linear (d m : Nat) (S : Finset (Fin (source d).wires))
    (C : Fin m → Finset (Fin (2 ^ d)))
    (hCover : ∀ x : Fin (2 ^ d), ∃ i, x ∈ C i)
    (hDisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hComp : ∀ x y : Fin (2 ^ d),
      UndirectedReachAvoiding (source d).circuit S
        ⟨x.val, lt_of_lt_of_le x.isLt (inputs_le_wires d)⟩
        ⟨y.val, lt_of_lt_of_le y.isLt (inputs_le_wires d)⟩ →
      ∃ i, x ∈ C i ∧ y ∈ C i)
    (hSmall : ∀ i, 3 * (C i).card ≤ 2 * 2 ^ d) :
    2 ^ d ≤ 18 * S.card := by
  obtain ⟨A, B, hA, hB, hCase⟩ :=
    exists_balanced_bipartition (Nat.two_pow_pos d) C hCover hSmall
  refine butterfly_balanced_separator_linear d S ?_ hA hB
  intro x hx y hy hReach
  obtain ⟨j, hxJ, hyJ⟩ := hComp x y hReach
  rcases hCase with ⟨i₀, rfl, rfl⟩ | ⟨k₀, _, rfl, rfl⟩
  · have hyNot : y ∉ C i₀ := (Finset.mem_sdiff.mp hy).2
    have hNe : j ≠ i₀ := fun h => hyNot (h ▸ hyJ)
    exact (Finset.disjoint_left.mp (hDisj j i₀ hNe)) hxJ hx
  · rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨i, hiRange, hxI⟩
    have hiM : i < m := by
      by_contra hGe
      simp [hGe] at hxI
    simp only [hiM, ↓reduceDIte] at hxI
    have hyNot : y ∉ (Finset.range k₀).biUnion (fun j => if hj : j < m then C ⟨j, hj⟩ else ∅) :=
      (Finset.mem_sdiff.mp hy).2
    have hJGe : k₀ ≤ j.val := by
      by_contra hLt
      apply hyNot
      refine Finset.mem_biUnion.mpr ⟨j.val, Finset.mem_range.mpr (by omega), ?_⟩
      simp [j.isLt, hyJ]
    have hiLt : i < k₀ := Finset.mem_range.mp hiRange
    have hNe : j ≠ ⟨i, hiM⟩ := fun h => by
      have : j.val = i := congrArg Fin.val h
      omega
    exact (Finset.disjoint_left.mp (hDisj j ⟨i, hiM⟩ hNe)) hxJ hxI

/-- **No $o(n)$ Balanced Separator on `ButterflyNet`**: for any family `d i → ∞`, no sequence
of balanced vertex separators `S i` separating `A i, B i` (`|A i|, |B i| ≥ 2 ^ d i / 3`) has
sublinear size `|S i| = o(2 ^ d i)`. -/
theorem butterfly_escapes_sublinear_separator (d : Nat → Nat) (_hd : Tendsto d atTop atTop)
    (S : ∀ i, Finset (Fin (source (d i)).wires))
    (A B : ∀ i, Finset (Fin (2 ^ d i)))
    (hSep : ∀ i, SeparatesInputs (source (d i)).circuit (S i) (A i) (B i) (inputs_le_wires (d i)))
    (hA : ∀ i, 2 ^ d i ≤ 3 * (A i).card)
    (hB : ∀ i, 2 ^ d i ≤ 3 * (B i).card) :
    ¬ ((fun i => ((S i).card : ℝ)) =o[atTop] (fun i => ((2 ^ d i : Nat) : ℝ))) := by
  intro hLittleO
  have hBound : ∀ᶠ i in atTop, ‖((S i).card : ℝ)‖ ≤ (1 / 36 : ℝ) * ‖((2 ^ d i : Nat) : ℝ)‖ :=
    hLittleO.bound (by norm_num : (0 : ℝ) < 1 / 36)
  obtain ⟨i, hi⟩ := hBound.exists
  have hLin : ((2 ^ d i : Nat) : ℝ) ≤ 18 * ((S i).card : ℝ) := by
    exact_mod_cast butterfly_balanced_separator_linear (d i) (S i) (hSep i) (hA i) (hB i)
  have hNPos : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by positivity
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hi
  linarith

end ButterflyNet

end PvsNP
