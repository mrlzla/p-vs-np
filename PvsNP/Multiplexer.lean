module

public import PvsNP.FormulaCircuit
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace PvsNP.Multiplexer

open BoolFormula Filter

variable {α : Type}

def selectBit (selector : α) (bit : Bool) : BoolFormula α :=
  if bit then .var selector else .not (.var selector)

def prepend {k : Nat} (bit : Bool) (address : Fin k → Bool) : Fin (k + 1) → Bool :=
  @Fin.cons k (fun _ => Bool) bit address

/-- Disjoin the minterms. Each leaf receives its own copy of all its selector tests. -/
def expandedWith : (k : Nat) → (Fin k → α) → ((Fin k → Bool) → α) →
    (BoolFormula α → BoolFormula α) → BoolFormula α
  | 0, _, dataBit, guard => guard (.var (dataBit Fin.elim0))
  | k + 1, selector, dataBit, guard => .binary .or
      (expandedWith k (selector ∘ Fin.succ) (dataBit ∘ prepend false)
        (fun e => guard (.binary .and (selectBit (selector 0) false) e)))
      (expandedWith k (selector ∘ Fin.succ) (dataBit ∘ prepend true)
        (fun e => guard (.binary .and (selectBit (selector 0) true) e)))

/-- Pull each selector test out of all the terms of its branch. -/
def factored : (k : Nat) → (Fin k → α) → ((Fin k → Bool) → α) → BoolFormula α
  | 0, _, dataBit => .var (dataBit Fin.elim0)
  | k + 1, selector, dataBit => .binary .or
      (.binary .and (selectBit (selector 0) false)
        (factored k (selector ∘ Fin.succ) (dataBit ∘ prepend false)))
      (.binary .and (selectBit (selector 0) true)
        (factored k (selector ∘ Fin.succ) (dataBit ∘ prepend true)))

private theorem address_cons {k : Nat} (values : α → Bool) (selector : Fin (k + 1) → α) :
    prepend (values (selector 0)) (values ∘ selector ∘ Fin.succ) = values ∘ selector :=
  Fin.cons_self_tail (values ∘ selector)

private theorem expandedWith_eval (values : α → Bool) (k : Nat) :
    ∀ (selector : Fin k → α) (dataBit : (Fin k → Bool) → α)
      (guard : BoolFormula α → BoolFormula α) (enabled : Bool),
      (∀ e, (guard e).eval values = (enabled && e.eval values)) →
      (expandedWith k selector dataBit guard).eval values =
        (enabled && values (dataBit (values ∘ selector))) := by
  induction k with
  | zero =>
    intro selector dataBit guard enabled hGuard
    rw [expandedWith, hGuard, eval, Subsingleton.elim Fin.elim0 (values ∘ selector)]
  | succ k ih =>
    intro selector dataBit guard enabled hGuard
    have hBranch (bit : Bool) (e : BoolFormula α) :
        (guard (.binary .and (selectBit (selector 0) bit) e)).eval values =
          ((enabled && (selectBit (selector 0) bit).eval values) && e.eval values) := by
      rw [hGuard, eval, BinaryGate.eval, Bool.and_assoc]
    have left := ih (selector ∘ Fin.succ) (dataBit ∘ prepend false) _ _ (hBranch false)
    have right := ih (selector ∘ Fin.succ) (dataBit ∘ prepend true) _ _ (hBranch true)
    rw [expandedWith, eval, BinaryGate.eval, left, right, ← address_cons values selector]
    cases h : values (selector 0) <;> simp [selectBit, eval, h, Function.comp_apply]

private theorem factored_eval (values : α → Bool) (k : Nat) :
    ∀ (selector : Fin k → α) (dataBit : (Fin k → Bool) → α),
      (factored k selector dataBit).eval values = values (dataBit (values ∘ selector)) := by
  induction k with
  | zero =>
    intro selector dataBit
    rw [factored, eval, Subsingleton.elim Fin.elim0 (values ∘ selector)]
  | succ k ih =>
    intro selector dataBit
    simp only [factored, eval, BinaryGate.eval, ih]
    rw [← address_cons values selector]
    cases h : values (selector 0) <;> simp [selectBit, eval, h, Function.comp_apply]

private theorem expandedWith_gates (k : Nat) :
    ∀ (selector : Fin k → α) (dataBit : (Fin k → Bool) → α)
      (guard : BoolFormula α → BoolFormula α) (cost : Nat),
      (∀ e, (guard e).gateCount = cost + e.gateCount) →
      2 * ((expandedWith k selector dataBit guard).gateCount + 1) =
        2 ^ k * (2 * cost + 3 * k + 2) := by
  induction k with
  | zero =>
    intro selector dataBit guard cost hGuard
    rw [expandedWith, hGuard, gateCount]
    omega
  | succ k ih =>
    intro selector dataBit guard cost hGuard
    let branch (bit : Bool) := expandedWith k (selector ∘ Fin.succ) (dataBit ∘ prepend bit)
      (fun e => guard (.binary .and (selectBit (selector 0) bit) e))
    have left : 2 * ((branch false).gateCount + 1) = 2 ^ k * (2 * (cost + 2) + 3 * k + 2) := by
      apply ih
      intro e
      rw [hGuard]
      simp [selectBit, gateCount]
      omega
    have right : 2 * ((branch true).gateCount + 1) = 2 ^ k * (2 * (cost + 1) + 3 * k + 2) := by
      apply ih
      intro e
      rw [hGuard]
      simp [selectBit, gateCount]
      omega
    calc
      2 * ((expandedWith (k + 1) selector dataBit guard).gateCount + 1) =
          2 * ((branch false).gateCount + 1) + 2 * ((branch true).gateCount + 1) := by
        change 2 * ((.binary .or (branch false) (branch true) : BoolFormula α).gateCount + 1) = _
        simp only [gateCount]
        omega
      _ = _ := by rw [left, right, pow_succ]; ring

private theorem factored_gates (k : Nat) :
    ∀ (selector : Fin k → α) (dataBit : (Fin k → Bool) → α),
      (factored k selector dataBit).gateCount + 4 = 4 * 2 ^ k := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro selector dataBit
    have left := ih (selector ∘ Fin.succ) (dataBit ∘ prepend false)
    have right := ih (selector ∘ Fin.succ) (dataBit ∘ prepend true)
    simp [factored, gateCount, selectBit, pow_succ]
    omega

/-- There are `k` selector bits and `2^k` individually addressable data bits. -/
def inputCount (k : Nat) : Nat := k + 2 ^ k

def selector (k : Nat) (j : Fin k) : Fin (inputCount k) := Fin.castAdd (2 ^ k) j

def dataBit (k : Nat) (address : Fin k → Bool) : Fin (inputCount k) :=
  Fin.natAdd k (finFunctionFinEquiv (finTwoEquiv.symm ∘ address))

def source (k : Nat) : CircuitInstance (inputCount k) :=
  (expandedWith k (selector k) (dataBit k) id).toCircuit id

def compressed (k : Nat) : CircuitInstance (inputCount k) :=
  (factored k (selector k) (dataBit k)).toCircuit id

theorem compressed_eval (k : Nat) (input : Fin (inputCount k) → Bool) :
    (compressed k).eval input = (source k).eval input := by
  simp only [compressed, source, eval_toCircuit, Function.comp_id]
  rw [factored_eval]
  simpa using (expandedWith_eval input k (selector k) (dataBit k) id true (by simp)).symm

theorem source_gates (k : Nat) :
    2 * ((source k).circuit.gateCount + 1) = 2 ^ k * (3 * k + 2) := by
  simp only [source, gateCount_toCircuit]
  simpa using expandedWith_gates k (selector k) (dataBit k) id 0 (by simp)

theorem compressed_gates (k : Nat) : (compressed k).circuit.gateCount + 4 = 4 * 2 ^ k := by
  simpa [compressed, gateCount_toCircuit] using factored_gates k (selector k) (dataBit k)

theorem inputCount_log2 (k : Nat) : (inputCount k).log2 = k := by
  have h : 0 < (2 : Nat) ^ k := by positivity
  apply (Nat.log2_eq_iff (by unfold inputCount; omega)).mpr
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  unfold inputCount
  rw [pow_succ]
  omega

theorem source_gate_bounds (k : Nat) (hk : 2 ≤ inputCount k) :
    inputCount k * (inputCount k).log2 ≤ 2 * (source k).circuit.gateCount ∧
      (source k).circuit.gateCount ≤ 3 * (inputCount k * (inputCount k).log2) := by
  have hkPos : 1 ≤ k := by
    cases k with
    | zero => simp [inputCount] at hk
    | succ k => omega
  have hPow : 0 < (2 : Nat) ^ k := by positivity
  have hSmall : k < 2 ^ k := Nat.lt_two_pow_self
  have hBelow : (2 : Nat) ^ k ≤ inputCount k := Nat.le_add_left _ _
  have hAbove : inputCount k ≤ 2 * 2 ^ k := by unfold inputCount; omega
  have hExact := source_gates k
  have hMin := Nat.mul_le_mul_left (2 ^ k) (show 2 * k + 2 ≤ 3 * k + 2 by omega)
  have hMax := Nat.mul_le_mul_left (2 ^ k) (show 3 * k + 2 ≤ 6 * k by omega)
  have hLower : 2 ^ k * k ≤ (source k).circuit.gateCount := by nlinarith
  have hUpper : (source k).circuit.gateCount ≤ 3 * (2 ^ k * k) := by nlinarith
  rw [inputCount_log2]
  constructor
  · calc
      inputCount k * k ≤ (2 * 2 ^ k) * k := Nat.mul_le_mul_right k hAbove
      _ = 2 * (2 ^ k * k) := Nat.mul_assoc ..
      _ ≤ 2 * (source k).circuit.gateCount := Nat.mul_le_mul_left 2 hLower
  · exact hUpper.trans (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right k hBelow))

theorem compressed_wire_bound (k : Nat) : (compressed k).wires ≤ 5 * inputCount k := by
  have hSize := compressed_gates k
  have hInputs : (2 : Nat) ^ k ≤ inputCount k := Nat.le_add_left _ _
  rw [Circuit.wire_count (compressed k).circuit]
  omega

def modelsEquiv (k : Nat) : Models (compressed k).cnf ≃ (source k).Accepting :=
  ((compressed k).circuit.acceptingAssignmentsEquiv (compressed k).output).trans
    (Equiv.subtypeEquivRight fun input => by
      change (compressed k).eval input = true ↔ (source k).eval input = true
      rw [compressed_eval])

theorem model_count (k : Nat) : Nat.card (Models (compressed k).cnf) = Nat.card (source k).Accepting :=
  Nat.card_congr (modelsEquiv k)

theorem canonical_model_count (k : Nat) :
    Nat.card (CanonicalModels (canonicalize (compressed k).cnf)) = Nat.card (source k).Accepting :=
  Nat.card_congr ((canonicalModelsEquiv (compressed k).cnf).trans (modelsEquiv k))

theorem compression : CircuitCompressionTask inputCount source compressed where
  inputsGrow := tendsto_atTop_mono (fun k => Nat.le_add_right k (2 ^ k)) tendsto_id
  sourceSize := ⟨2, 3, by decide, by decide, source_gate_bounds⟩
  equivalent := compressed_eval
  exactCount := fun k => ⟨modelsEquiv k⟩
  variableBound := ⟨5, compressed_wire_bound⟩
  clauses := ⟨13, fun k => by
    have hSize := compressed_gates k
    have hInputs : (2 : Nat) ^ k ≤ inputCount k := Nat.le_add_left _ _
    have hPositive : 0 < (2 : Nat) ^ k := by positivity
    have hCnf := (compressed k).circuit.encode_size (compressed k).output
    change (compressed k).cnf.clauses.size ≤ _ at hCnf
    omega⟩
  width := fun k _ h => (compressed k).circuit.encode_width (compressed k).output h
  subexponential := fun C d =>
    logTimeBudget_isLittleO (tendsto_atTop_mono (fun k => Nat.le_add_right k (2 ^ k)) tendsto_id)
      (fun k => calc
        inputCount k ≤ inputCount k + (compressed k).circuit.gateCount := Nat.le_add_right ..
        _ = (compressed k).wires := (Circuit.wire_count (compressed k).circuit).symm)
      5 compressed_wire_bound C d

theorem canonical_width (k : Nat) (clause : Finset (Fin (compressed k).wires × Bool))
    (hClause : clause ∈ canonicalize (compressed k).cnf) : clause.card ≤ 3 :=
  canonicalize_width (compressed k).cnf (compression.width k) clause hClause

theorem canonical_clause_bound : ∃ c : Nat, ∀ k,
    (canonicalize (compressed k).cnf).card ≤ c * inputCount k := by
  obtain ⟨c, h⟩ := compression.clauses
  exact ⟨c, fun k => (canonicalize_clause_count_le _).trans (h k)⟩

end PvsNP.Multiplexer
