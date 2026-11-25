module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Card
public import Std.Sat.CNF

@[expose] public section

/-! The Tseitin encoding for topologically ordered, fan-in two Boolean circuits. -/

namespace PvsNP

open Std.Sat (CNF)

/-- A gate whose operands are among the `n` existing wires. -/
inductive Gate (n : Nat) where
  | and (left right : Fin n)
  | or (left right : Fin n)
  | not (input : Fin n)

def Gate.eval {n : Nat} (gate : Gate n) (values : Fin n → Bool) : Bool :=
  match gate with
  | .and left right => values left && values right
  | .or left right => values left || values right
  | .not input => !values input

/-- The clauses equating the fresh output variable with the gate value. -/
def Gate.encode {n : Nat} (gate : Gate n) : CNF (Fin (n + 1)) :=
  let out := Fin.last n
  match gate with
  | .and left right =>
    let x := left.castSucc
    let y := right.castSucc
    CNF.empty |>.add (CNF.Clause.empty |>.add x false |>.add y false |>.add out true)
           |>.add (CNF.Clause.empty |>.add x true |>.add out false)
           |>.add (CNF.Clause.empty |>.add y true |>.add out false)
  | .or left right =>
    let x := left.castSucc
    let y := right.castSucc
    CNF.empty |>.add (CNF.Clause.empty |>.add x true |>.add y true |>.add out false)
           |>.add (CNF.Clause.empty |>.add x false |>.add out true)
           |>.add (CNF.Clause.empty |>.add y false |>.add out true)
  | .not input =>
    let x := input.castSucc
    CNF.empty |>.add (CNF.Clause.empty |>.add x true |>.add out true)
           |>.add (CNF.Clause.empty |>.add x false |>.add out false)

theorem Gate.eval_encode {n : Nat} (gate : Gate n) (values : Fin (n + 1) → Bool) :
    gate.encode.eval values = true ↔ values (Fin.last n) = gate.eval (Fin.init values) := by
  cases gate with
  | and x y =>
    cases hOut : values (Fin.last n) <;> cases hX : values x.castSucc <;>
      cases hY : values y.castSucc <;> simp [encode, eval, Fin.init, hOut, hX, hY]
  | or x y =>
    cases hOut : values (Fin.last n) <;> cases hX : values x.castSucc <;>
      cases hY : values y.castSucc <;> simp [encode, eval, Fin.init, hOut, hX, hY]
  | not x =>
    cases hOut : values (Fin.last n) <;> cases hX : values x.castSucc <;>
      simp [encode, eval, Fin.init, hOut, hX]

theorem Gate.encode_size {n : Nat} (gate : Gate n) : gate.encode.clauses.size ≤ 3 := by
  cases gate <;> simp [encode, CNF.empty, CNF.add]

theorem Gate.encode_width {n : Nat} (gate : Gate n)
    {clause : CNF.Clause (Fin (n + 1))} (h : clause ∈ gate.encode.clauses) :
    clause.size ≤ 3 := by
  cases gate <;> simp [encode, CNF.empty, CNF.add] at h <;>
    rcases h with (rfl | rfl | rfl) <;> simp [CNF.Clause.size_add]

/-- Start with `inputs` input wires, then append one fresh wire per gate. -/
inductive Circuit (inputs : Nat) : Nat → Type where
  | inputsOnly : Circuit inputs inputs
  | snoc {n : Nat} (earlier : Circuit inputs n) (gate : Gate n) : Circuit inputs (n + 1)

namespace Circuit

variable {inputs wires : Nat}

def gateCount : {n : Nat} → Circuit inputs n → Nat
  | _, .inputsOnly => 0
  | _, .snoc earlier _ => earlier.gateCount + 1

theorem wire_count (circuit : Circuit inputs wires) : wires = inputs + circuit.gateCount := by
  induction circuit with
  | inputsOnly => simp [gateCount]
  | snoc earlier gate ih => simpa [gateCount, ← Nat.add_assoc] using ih

/-- Evaluate every wire with the given input assignment. -/
def evalWires : {n : Nat} → Circuit inputs n → (Fin inputs → Bool) → (Fin n → Bool)
  | _, .inputsOnly, input => input
  | _, .snoc earlier gate, input =>
    let values := earlier.evalWires input
    Fin.snoc values (gate.eval values)

/-- Restrict a wire assignment to the input wires. -/
def restrictInputs : {n : Nat} → Circuit inputs n → (Fin n → Bool) → (Fin inputs → Bool)
  | _, .inputsOnly, values => values
  | _, .snoc earlier _, values => earlier.restrictInputs (Fin.init values)

@[simp] theorem restrictInputs_evalWires (circuit : Circuit inputs wires) (input : Fin inputs → Bool) :
    circuit.restrictInputs (circuit.evalWires input) = input := by
  induction circuit with
  | inputsOnly => rfl
  | snoc earlier gate ih => simpa [restrictInputs, evalWires] using ih

def gateConstraints : {n : Nat} → Circuit inputs n → CNF (Fin n)
  | _, .inputsOnly => .empty
  | _, .snoc earlier gate => earlier.gateConstraints.relabel Fin.castSucc ++ gate.encode

theorem eval_gateConstraints_iff (circuit : Circuit inputs wires) (values : Fin wires → Bool) :
    circuit.gateConstraints.eval values = true ↔
      circuit.evalWires (circuit.restrictInputs values) = values := by
  induction circuit with
  | inputsOnly => simp [gateConstraints, evalWires, restrictInputs]
  | snoc earlier gate ih =>
    rw [gateConstraints, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, Gate.eval_encode]
    rw [show values ∘ Fin.castSucc = Fin.init values from rfl, ih]
    constructor
    · rintro ⟨hPrefix, hLast⟩
      simp [evalWires, restrictInputs, hPrefix, ← hLast]
    · intro h
      have hPrefix := congrArg Fin.init h
      simp only [evalWires, restrictInputs, Fin.init_snoc] at hPrefix
      refine ⟨hPrefix, ?_⟩
      have hLast := congrFun h (Fin.last _)
      simpa [evalWires, restrictInputs, hPrefix] using hLast.symm

/-- Require the selected output wire to be true. -/
def encode (circuit : Circuit inputs wires) (output : Fin wires) : CNF (Fin wires) :=
  circuit.gateConstraints.add (CNF.Clause.unit output true)

theorem eval_encode_iff (circuit : Circuit inputs wires) (output : Fin wires)
    (values : Fin wires → Bool) :
    (circuit.encode output).eval values = true ↔
      circuit.evalWires (circuit.restrictInputs values) = values ∧ values output = true := by
  simp [encode, eval_gateConstraints_iff, and_comm]

/-- Satisfying wire assignments correspond bijectively to accepting input assignments. -/
def acceptingAssignmentsEquiv (circuit : Circuit inputs wires) (output : Fin wires) :
    { values : Fin wires → Bool // (circuit.encode output).eval values = true } ≃
      { input : Fin inputs → Bool // circuit.evalWires input output = true } where
  toFun values := ⟨circuit.restrictInputs values.val, by
    obtain ⟨hEval, hOut⟩ := (eval_encode_iff circuit output values.val).mp values.property
    rw [hEval]
    exact hOut⟩
  invFun input := ⟨circuit.evalWires input.val, (eval_encode_iff circuit output _).mpr
    ⟨by rw [restrictInputs_evalWires], input.property⟩⟩
  left_inv values := Subtype.ext ((eval_encode_iff circuit output values.val).mp values.property).1
  right_inv input := Subtype.ext (circuit.restrictInputs_evalWires input.val)

/-- Conditioning on selected wires partitions the accepting inputs into disjoint branches. -/
def acceptingAssignmentsByBoundary {b : Nat} (circuit : Circuit inputs wires) (output : Fin wires)
    (boundary : Fin b → Fin wires) :
    { input : Fin inputs → Bool // circuit.evalWires input output = true } ≃
      Σ fixed : Fin b → Bool, { values : Fin wires → Bool //
        (circuit.encode output).eval values = true ∧ values ∘ boundary = fixed } :=
  (circuit.acceptingAssignmentsEquiv output).symm.trans
    { toFun := fun values => ⟨values.val ∘ boundary, ⟨values.val, values.property, rfl⟩⟩
      invFun := fun branch => ⟨branch.2.val, branch.2.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨fixed, values, hSat, rfl⟩
        rfl }

theorem gateConstraints_size (circuit : Circuit inputs wires) :
    circuit.gateConstraints.clauses.size ≤ 3 * circuit.gateCount := by
  induction circuit with
  | inputsOnly => simp [gateConstraints, CNF.empty, gateCount]
  | snoc earlier gate ih =>
    have hGate := gate.encode_size
    simp only [gateConstraints, CNF.Internal.clauses_append, CNF.relabel, Array.size_append,
      Array.size_map, gateCount]
    omega

theorem encode_size (circuit : Circuit inputs wires) (output : Fin wires) :
    (circuit.encode output).clauses.size ≤ 3 * circuit.gateCount + 1 := by
  simpa [encode, CNF.add] using
    Nat.add_le_add_right circuit.gateConstraints_size 1

theorem gateConstraints_width (circuit : Circuit inputs wires)
    {clause : CNF.Clause (Fin wires)} (h : clause ∈ circuit.gateConstraints.clauses) :
    clause.size ≤ 3 := by
  induction circuit with
  | inputsOnly => simp [gateConstraints, CNF.empty] at h
  | snoc earlier gate ih =>
    simp only [gateConstraints, CNF.Internal.clauses_append, Array.mem_append, CNF.relabel,
      Array.mem_map] at h
    rcases h with ⟨prior, hPrior, rfl⟩ | hGate
    · simpa [CNF.Clause.relabel, CNF.Clause.Internal.size_eq_size_atoms] using ih hPrior
    · exact gate.encode_width hGate

theorem encode_width (circuit : Circuit inputs wires) (output : Fin wires)
    {clause : CNF.Clause (Fin wires)} (h : clause ∈ (circuit.encode output).clauses) :
    clause.size ≤ 3 := by
  simp [encode, CNF.add] at h
  rcases h with hGate | rfl
  · exact circuit.gateConstraints_width hGate
  · simp [CNF.Clause.unit_def]

end Circuit

/-- Encoding OR directly on its `n` inputs needs a clause of width at least `n`. -/
theorem or_requires_wide_clause {n : Nat} (formula : CNF (Fin n))
    (hOr : ∀ values, CNF.Sat values formula ↔ ∃ i, values i = true) :
    ∃ clause ∈ formula.clauses, n ≤ clause.size := by
  have hFalse : ¬CNF.Sat (fun _ => false) formula := by
    simp [hOr]
  obtain ⟨clause, hMem, hFail⟩ := CNF.not_sat_iff_exists_mem_not_sat.mp hFalse
  refine ⟨clause, CNF.Internal.mem_iff.mp hMem, ?_⟩
  have hVars : ∀ i : Fin n, i ∈ clause.atoms.toList.toFinset := by
    intro i
    let single (j : Fin n) : Bool := decide (j = i)
    have hSat := CNF.sat_of_mem ((hOr single).mpr ⟨i, by simp [single]⟩) hMem
    obtain ⟨⟨j, polarity⟩, hLit, hValue⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp hSat
    cases polarity with
    | false => exact (hFail (CNF.Clause.sat_of_mem_of_eq hLit rfl)).elim
    | true =>
      have hji : j = i := by simpa [single] using hValue
      rw [← CNF.Clause.Internal.map_fst_literals, List.mem_toFinset]
      exact List.mem_map.mpr ⟨(j, true), CNF.Clause.mem_literals_iff.mpr hLit, hji⟩
  simpa [Finset.eq_univ_of_forall hVars, CNF.Clause.Internal.size_eq_size_atoms] using
    (List.toFinset_card_le (l := clause.atoms.toList))

end PvsNP
