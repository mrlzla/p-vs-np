module

public import PvsNP.CompressionTask

@[expose] public section

namespace PvsNP

inductive BinaryGate where
  | and
  | or

def BinaryGate.asGate {n : Nat} (op : BinaryGate) (x y : Fin n) : Gate n :=
  match op with
  | .and => .and x y
  | .or => .or x y

def BinaryGate.eval (op : BinaryGate) (x y : Bool) : Bool :=
  match op with
  | .and => x && y
  | .or => x || y

@[simp] theorem BinaryGate.eval_asGate {n : Nat} (op : BinaryGate) (x y : Fin n)
    (values : Fin n → Bool) : (op.asGate x y).eval values = op.eval (values x) (values y) := by
  cases op <;> rfl

/-- Boolean formulas represent fan-in-two circuits without sharing internal gates. -/
inductive BoolFormula (α : Type) where
  | var (index : α)
  | not (child : BoolFormula α)
  | binary (op : BinaryGate) (left right : BoolFormula α)

namespace BoolFormula

variable {α : Type}

def eval (values : α → Bool) : BoolFormula α → Bool
  | .var index => values index
  | .not child => !(child.eval values)
  | .binary op left right => op.eval (left.eval values) (right.eval values)

def gateCount : BoolFormula α → Nat
  | .var _ => 0
  | .not child => child.gateCount + 1
  | .binary _ left right => left.gateCount + right.gateCount + 1

/-- Compiling into an existing circuit preserves its wires and accounts for each new gate. -/
structure Compilation {n start : Nat} (earlier : Circuit n start)
    (formula : BoolFormula α) (names : α → Fin start) where
  stop : Nat
  circuit : Circuit n stop
  embed : Fin start → Fin stop
  output : Fin stop
  preserves : ∀ input j, circuit.evalWires input (embed j) = earlier.evalWires input j
  output_correct : ∀ input, circuit.evalWires input output =
    formula.eval (earlier.evalWires input ∘ names)
  gate_count : circuit.gateCount = earlier.gateCount + formula.gateCount

def compileNot {n start : Nat} {earlier : Circuit n start} {names : α → Fin start}
    {child : BoolFormula α} (inner : Compilation earlier child names) :
    Compilation earlier (.not child) names where
  stop := inner.stop + 1
  circuit := inner.circuit.snoc (.not inner.output)
  embed := Fin.castSucc ∘ inner.embed
  output := Fin.last inner.stop
  preserves := fun input j => by
    simpa [Circuit.evalWires, Function.comp_def] using inner.preserves input j
  output_correct := fun input => by
    simp [Circuit.evalWires, Gate.eval, eval, inner.output_correct]
  gate_count := by simp [Circuit.gateCount, gateCount, inner.gate_count, Nat.add_assoc]

def compileBinary {n start : Nat} {earlier : Circuit n start} {names : α → Fin start}
    {left right : BoolFormula α} (op : BinaryGate) (first : Compilation earlier left names)
    (second : Compilation first.circuit right (first.embed ∘ names)) :
    Compilation earlier (.binary op left right) names where
  stop := second.stop + 1
  circuit := second.circuit.snoc (op.asGate (second.embed first.output) second.output)
  embed := Fin.castSucc ∘ second.embed ∘ first.embed
  output := Fin.last second.stop
  preserves := fun input j => by
    simpa [Circuit.evalWires, Function.comp_def] using
      (second.preserves input (first.embed j)).trans (first.preserves input j)
  output_correct := fun input => by
    have rightInput : first.circuit.evalWires input ∘ first.embed ∘ names =
        earlier.evalWires input ∘ names := funext fun j => first.preserves input (names j)
    simp [Circuit.evalWires, eval, second.preserves, first.output_correct,
      second.output_correct, rightInput]
  gate_count := by
    simp [Circuit.gateCount, gateCount, first.gate_count, second.gate_count, Nat.add_assoc]

def compile (formula : BoolFormula α) {n start : Nat} (earlier : Circuit n start)
    (names : α → Fin start) : Compilation earlier formula names :=
  match formula with
  | .var j => ⟨start, earlier, id, names j, fun _ _ => rfl, fun _ => rfl, by simp [gateCount]⟩
  | .not child => compileNot (child.compile earlier names)
  | .binary op left right =>
    let first := left.compile earlier names
    compileBinary op first (right.compile first.circuit (first.embed ∘ names))
termination_by structural formula

def toCircuit {n : Nat} (formula : BoolFormula α) (names : α → Fin n) : CircuitInstance n :=
  let result := formula.compile Circuit.inputsOnly names
  ⟨result.stop, result.circuit, result.output⟩

theorem eval_toCircuit {n : Nat} (formula : BoolFormula α) (names : α → Fin n)
    (input : Fin n → Bool) : (formula.toCircuit names).eval input = formula.eval (input ∘ names) :=
  (formula.compile Circuit.inputsOnly names).output_correct input

theorem gateCount_toCircuit {n : Nat} (formula : BoolFormula α) (names : α → Fin n) :
    (formula.toCircuit names).circuit.gateCount = formula.gateCount := by
  simpa [toCircuit, Circuit.gateCount] using (formula.compile Circuit.inputsOnly names).gate_count

end BoolFormula
end PvsNP
