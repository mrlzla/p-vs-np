module

public import PvsNP.BranchingCompression

@[expose] public section

/-!
# Symbolic Literal Propagation and Reader-Eliminating Wire Cuts

Bridges gate-elimination under wire pinning with subexponential `#SAT` branching:
1. **Zero-variable `NOT`s and constant/alias folding (`compileSym`)**: compiles any
   `Circuit inputs wires` under partial wire pins `pin : Fin wires → Option Bool` into an
   exact-counting width-`≤ 3` CNF over `Fin (inputs + activeGates)`, allocating zero auxiliary
   variables for `.not` gates, constants, wire aliases (`AND(1, y) = y`, `OR(0, y) = y`),
   idempotent gates (`AND(y, y) = y`), and complementary gates (`AND(y, ¬y) = 0`).
2. **Internal-wire cut pinning (`branchingOfPinnedCut`)**: conditioning on any wire cut
   `cut : Finset (Fin source.wires)` enforces each pinned internal wire via at most one unit
   clause of width `≤ 1` and substitutes its constant value into all downstream gates, eliminating
   **every** binary (`AND`/`OR`) gate incident to `cut` in **all** `2 ^ cut.card` branches.
3. **Subexponential `#SAT` for small binary-reader hitting cuts (`hitting_cut_subexponential`)**:
   any circuit family admitting a wire cut of size `o(n)` that hits all but
   `O(n * (log n) ^ α)` (`α < 1 / 2`) binary `AND`/`OR` gates runs in `2 ^ o(n)` deterministic
   time under the fixed-width exact `#3-SAT` counter.
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Symbolic Literals and Zero-Variable Negation / Constant Enforcement -/

/-- A wire value represented either as a compile-time constant or as a signed variable literal
`(σ var == pol)` over `v` declared CNF variables. -/
inductive SymLit (v : Nat) where
  | const (val : Bool)
  | lit (var : Fin v) (pol : Bool)

namespace SymLit

def eval {v : Nat} (σ : Fin v → Bool) : SymLit v → Bool
  | .const val => val
  | .lit var pol => σ var == pol

def neg {v : Nat} : SymLit v → SymLit v
  | .const val => .const (!val)
  | .lit var pol => .lit var (!pol)

@[simp] theorem eval_neg {v : Nat} (σ : Fin v → Bool) (l : SymLit v) :
    l.neg.eval σ = !(l.eval σ) := by
  cases l with
  | const val => rfl
  | lit var pol =>
    simp only [neg, eval]
    cases σ var <;> cases pol <;> rfl

def castSucc {v : Nat} : SymLit v → SymLit (v + 1)
  | .const val => .const val
  | .lit var pol => .lit var.castSucc pol

@[simp] theorem eval_castSucc {v : Nat} (σ : Fin (v + 1) → Bool) (l : SymLit v) :
    l.castSucc.eval σ = l.eval (Fin.init σ) := by
  cases l <;> rfl

/-- Unit (or empty) CNF constraint forcing `l.eval σ = target` without adding variables. -/
def enforceEq {v : Nat} (l : SymLit v) (target : Bool) : CNF (Fin v) :=
  match l with
  | .const val => if val == target then CNF.empty else CNF.empty.add CNF.Clause.empty
  | .lit var pol => CNF.empty.add (CNF.Clause.unit var (if pol then target else !target))

theorem eval_enforceEq {v : Nat} (l : SymLit v) (target : Bool) (σ : Fin v → Bool) :
    (l.enforceEq target).eval σ = true ↔ l.eval σ = target := by
  cases l with
  | const val =>
    cases val <;> cases target <;> simp [enforceEq, eval]
  | lit var pol =>
    cases hV : σ var <;> cases pol <;> cases target <;>
      simp [enforceEq, eval, hV]

theorem enforceEq_width {v : Nat} (l : SymLit v) (target : Bool)
    {clause : CNF.Clause (Fin v)} (h : clause ∈ (l.enforceEq target).clauses) :
    clause.size ≤ 3 := by
  cases l with
  | const val =>
    cases val <;> cases target <;> simp [enforceEq, CNF.empty, CNF.add] at h
    all_goals subst h; simp
  | lit var pol =>
    simp [enforceEq, CNF.empty, CNF.add] at h
    subst h
    simp [CNF.Clause.unit_def]

end SymLit

/-- Three-clause Tseitin encoding equating `Fin.last v` with `(σ x == px) && (σ y == py)`. -/
def encodeSignedAnd {v : Nat} (x : Fin v) (px : Bool) (y : Fin v) (py : Bool) :
    CNF (Fin (v + 1)) :=
  let out := Fin.last v
  let x' := x.castSucc
  let y' := y.castSucc
  CNF.empty |>.add (CNF.Clause.empty |>.add x' (!px) |>.add y' (!py) |>.add out true)
         |>.add (CNF.Clause.empty |>.add x' px |>.add out false)
         |>.add (CNF.Clause.empty |>.add y' py |>.add out false)

theorem eval_encodeSignedAnd {v : Nat} (x : Fin v) (px : Bool) (y : Fin v) (py : Bool)
    (σ : Fin (v + 1) → Bool) :
    (encodeSignedAnd x px y py).eval σ = true ↔
      σ (Fin.last v) = ((Fin.init σ x == px) && (Fin.init σ y == py)) := by
  cases hOut : σ (Fin.last v) <;> cases hX : σ x.castSucc <;> cases hY : σ y.castSucc <;>
    cases px <;> cases py <;>
    simp [encodeSignedAnd, Fin.init, hOut, hX, hY]

theorem encodeSignedAnd_width {v : Nat} (x : Fin v) (px : Bool) (y : Fin v) (py : Bool)
    {clause : CNF.Clause (Fin (v + 1))} (h : clause ∈ (encodeSignedAnd x px y py).clauses) :
    clause.size ≤ 3 := by
  simp [encodeSignedAnd, CNF.empty, CNF.add] at h
  rcases h with (rfl | rfl | rfl) <;> simp [CNF.Clause.size_add]

/-! ### 2. Symbolic Circuit Compilation Under Wire Pins -/

/-- Counts binary (`AND`/`OR`) gates in `c` neither of whose operands is pinned in `pin`. -/
def unhitBinaryGates {inputs : Nat} : {w : Nat} → Circuit inputs w → (Fin w → Option Bool) → Nat
  | _, .inputsOnly, _ => 0
  | _, .snoc earlier (.not _), pin => unhitBinaryGates earlier (pin ∘ Fin.castSucc)
  | _, .snoc earlier (.and u v), pin =>
    unhitBinaryGates earlier (pin ∘ Fin.castSucc) +
      if (pin u.castSucc).isSome || (pin v.castSucc).isSome then 0 else 1
  | _, .snoc earlier (.or u v), pin =>
    unhitBinaryGates earlier (pin ∘ Fin.castSucc) +
      if (pin u.castSucc).isSome || (pin v.castSucc).isSome then 0 else 1

/-- Total `AND`/`OR` gates in `c` (with `.not` gates free). -/
def binaryGateCount {inputs w : Nat} (c : Circuit inputs w) : Nat :=
  unhitBinaryGates c (fun _ => none)

/-- Inductive state of symbolic literal propagation on `c` with partial wire pins `pin`. -/
structure SymCompilation {n w : Nat} (c : Circuit n w) (pin : Fin w → Option Bool) where
  activeGates : Nat
  wireMap : Fin w → SymLit (n + activeGates)
  constraints : CNF (Fin (n + activeGates))
  liftAssign : (Fin n → Bool) → (Fin (n + activeGates) → Bool)
  lift_prefix : ∀ input (i : Fin n), liftAssign input (Fin.castAdd activeGates i) = input i
  width_le : ∀ clause ∈ constraints.clauses, clause.size ≤ 3
  constraints_iff : ∀ σ : Fin (n + activeGates) → Bool,
    constraints.eval σ = true ↔
      (σ = liftAssign (fun i => σ (Fin.castAdd activeGates i)) ∧
        ∀ (u : Fin w) (b : Bool), pin u = some b →
          c.evalWires (fun i => σ (Fin.castAdd activeGates i)) u = b)
  wireMap_eval : ∀ (input : Fin n → Bool),
    (∀ (u : Fin w) (b : Bool), pin u = some b → c.evalWires input u = b) →
    ∀ u : Fin w, (wireMap u).eval (liftAssign input) = c.evalWires input u
  pinned_is_const : ∀ (u : Fin w) (b : Bool), pin u = some b → wireMap u = .const b
  active_le : activeGates ≤ unhitBinaryGates c pin

theorem appendCNF {v : Nat} (f1 f2 : CNF (Fin v))
    (hw1 : ∀ cl ∈ f1.clauses, cl.size ≤ 3) (hw2 : ∀ cl ∈ f2.clauses, cl.size ≤ 3) :
    ∀ cl ∈ (f1 ++ f2).clauses, cl.size ≤ 3 := by
  intro cl h
  simp only [CNF.Internal.clauses_append, Array.mem_append] at h
  rcases h with h1 | h2
  · exact hw1 cl h1
  · exact hw2 cl h2

/-- Enforce input pins on `Fin n` with `0` auxiliary variables. -/
def inputPinConstraints : (m : Nat) → {v : Nat} → (Fin m → Fin v) →
    (Fin m → Option Bool) → CNF (Fin v)
  | 0, _, _, _ => CNF.empty
  | m + 1, _, emb, pin =>
    inputPinConstraints m (emb ∘ Fin.castSucc) (pin ∘ Fin.castSucc) ++
      match pin (Fin.last m) with
      | none => CNF.empty
      | some b => (SymLit.lit (emb (Fin.last m)) true).enforceEq b

theorem eval_inputPinConstraints : ∀ (m : Nat) {v : Nat} (emb : Fin m → Fin v)
    (pin : Fin m → Option Bool) (σ : Fin v → Bool),
    (inputPinConstraints m emb pin).eval σ = true ↔
      ∀ (u : Fin m) (b : Bool), pin u = some b → σ (emb u) = b
  | 0, _, _, _, _ => by simp [inputPinConstraints]
  | m + 1, _, emb, pin, σ => by
    rw [inputPinConstraints, CNF.eval_append, Bool.and_eq_true,
      eval_inputPinConstraints m (emb ∘ Fin.castSucc) (pin ∘ Fin.castSucc) σ]
    constructor
    · rintro ⟨hInit, hLast⟩ u b hub
      cases u using Fin.lastCases with
      | last =>
        rw [hub] at hLast
        have hEq := (SymLit.eval_enforceEq (.lit (emb (Fin.last m)) true) b σ).mp hLast
        simpa [SymLit.eval] using hEq
      | cast u' => exact hInit u' b hub
    · intro hAll
      refine ⟨fun u' b hub => hAll u'.castSucc b hub, ?_⟩
      cases hP : pin (Fin.last m) with
      | none => simp
      | some b =>
        rw [SymLit.eval_enforceEq]
        simpa [SymLit.eval] using hAll (Fin.last m) b hP

theorem inputPinConstraints_width : ∀ (m : Nat) {v : Nat} (emb : Fin m → Fin v)
    (pin : Fin m → Option Bool) {cl : CNF.Clause (Fin v)},
    cl ∈ (inputPinConstraints m emb pin).clauses → cl.size ≤ 3
  | 0, _, _, _, cl, h => by simp [inputPinConstraints, CNF.empty] at h
  | m + 1, _, emb, pin, cl, h => by
    refine appendCNF _ _ (fun _ hc => inputPinConstraints_width m _ _ hc) (fun _ hc => ?_) cl h
    cases hP : pin (Fin.last m) <;> simp only [hP] at hc
    · simp [CNF.empty] at hc
    · exact SymLit.enforceEq_width _ _ hc

/-- Base compilation for `Circuit.inputsOnly`. -/
def compileInputsOnly (n : Nat) (pin : Fin n → Option Bool) :
    SymCompilation (Circuit.inputsOnly (inputs := n)) pin where
  activeGates := 0
  wireMap := fun u =>
    match pin u with
    | none => .lit (Fin.castAdd 0 u) true
    | some b => .const b
  constraints := inputPinConstraints n (Fin.castAdd 0) pin
  liftAssign := fun input j => input (Fin.cast (Nat.add_zero n) j)
  lift_prefix := fun _ _ => rfl
  width_le := fun _ h => inputPinConstraints_width n (Fin.castAdd 0) pin h
  constraints_iff := fun σ => by
    rw [eval_inputPinConstraints]
    constructor
    · intro hPins
      refine ⟨funext fun j => rfl, fun u b hub => ?_⟩
      simpa [Circuit.evalWires] using hPins u b hub
    · rintro ⟨_, hPins⟩ u b hub
      simpa [Circuit.evalWires] using hPins u b hub
  wireMap_eval := fun input hPins u => by
    cases hP : pin u with
    | none => simp [SymLit.eval, Circuit.evalWires]
    | some b =>
      have hb := hPins u b hP
      simpa [SymLit.eval] using hb.symm
  pinned_is_const := fun u b hub => by simp [hub]
  active_le := Nat.le_refl 0

/-- Append a newly evaluated wire (without adding an auxiliary variable) and apply its pin. -/
def finishFoldedStep {n w : Nat} {earlier : Circuit n w}
    {gate : Gate w} {pin : Fin (w + 1) → Option Bool}
    (prev : SymCompilation earlier (pin ∘ Fin.castSucc))
    (rawOut : SymLit (n + prev.activeGates))
    (hRaw : ∀ input,
      (∀ (u : Fin w) (b : Bool), pin u.castSucc = some b → earlier.evalWires input u = b) →
      rawOut.eval (prev.liftAssign input) = gate.eval (earlier.evalWires input))
    (hCount : prev.activeGates ≤ unhitBinaryGates (.snoc earlier gate) pin) :
    SymCompilation (.snoc earlier gate) pin where
  activeGates := prev.activeGates
  wireMap := Fin.snoc prev.wireMap
    (match pin (Fin.last w) with
    | none => rawOut
    | some b => .const b)
  constraints := prev.constraints ++
    (match pin (Fin.last w) with
    | none => CNF.empty
    | some b => rawOut.enforceEq b)
  liftAssign := prev.liftAssign
  lift_prefix := prev.lift_prefix
  width_le := appendCNF _ _ prev.width_le fun cl h => by
    cases hP : pin (Fin.last w) <;> simp only [hP] at h
    · simp [CNF.empty] at h
    · exact SymLit.enforceEq_width rawOut _ h
  constraints_iff := fun σ => by
    rw [CNF.eval_append, Bool.and_eq_true, prev.constraints_iff σ]
    let x : Fin n → Bool := fun i => σ (Fin.castAdd prev.activeGates i)
    constructor
    · rintro ⟨⟨hLift, hPrevPins⟩, hLastPin⟩
      refine ⟨hLift, fun u b hub => ?_⟩
      cases u using Fin.lastCases with
      | cast u' =>
        simpa [Circuit.evalWires] using hPrevPins u' b hub
      | last =>
        rw [hub] at hLastPin
        have hEnf := (SymLit.eval_enforceEq rawOut b σ).mp hLastPin
        rw [hLift] at hEnf
        change rawOut.eval (prev.liftAssign x) = b at hEnf
        have hR := hRaw x hPrevPins
        simpa [Circuit.evalWires, hR] using hEnf
    · rintro ⟨hLift, hAllPins⟩
      have hPrevPins : ∀ (u' : Fin w) (b : Bool),
          pin u'.castSucc = some b → earlier.evalWires x u' = b := fun u' b hub => by
        simpa [Circuit.evalWires] using hAllPins u'.castSucc b hub
      refine ⟨⟨hLift, hPrevPins⟩, ?_⟩
      cases hP : pin (Fin.last w) with
      | none => simp
      | some b =>
        rw [SymLit.eval_enforceEq, hLift]
        change rawOut.eval (prev.liftAssign x) = b
        rw [hRaw x hPrevPins]
        simpa [Circuit.evalWires] using hAllPins (Fin.last w) b hP
  wireMap_eval := fun input hAllPins u => by
    have hPrevPins : ∀ (u' : Fin w) (b : Bool),
        pin u'.castSucc = some b → earlier.evalWires input u' = b := fun u' b hub => by
      simpa [Circuit.evalWires] using hAllPins u'.castSucc b hub
    cases u using Fin.lastCases with
    | cast u' =>
      simpa [Circuit.evalWires] using prev.wireMap_eval input hPrevPins u'
    | last =>
      simp only [Fin.snoc_last]
      cases hP : pin (Fin.last w) with
      | none =>
        simpa [Circuit.evalWires] using hRaw input hPrevPins
      | some b =>
        have hb := hAllPins (Fin.last w) b hP
        simpa [SymLit.eval] using hb.symm
  pinned_is_const := fun u b hub => by
    cases u using Fin.lastCases with
    | cast u' =>
      simpa using prev.pinned_is_const u' b hub
    | last =>
      simp [hub]
  active_le := hCount

/-- Append a genuinely fresh binary `AND`/`OR` gate variable (`outPol = true` for `AND`,
`outPol = false` for De Morgan `OR = ¬(¬u ∧ ¬v)`) and apply any pin on `Fin.last w`. -/
def finishFreshAndStep {n w : Nat} {earlier : Circuit n w}
    {gate : Gate w} {pin : Fin (w + 1) → Option Bool}
    (prev : SymCompilation earlier (pin ∘ Fin.castSucc))
    (xi : Fin (n + prev.activeGates)) (px : Bool)
    (yi : Fin (n + prev.activeGates)) (py : Bool)
    (outPol : Bool)
    (hGateSem : ∀ input,
      (∀ (u : Fin w) (b : Bool), pin u.castSucc = some b → earlier.evalWires input u = b) →
      gate.eval (earlier.evalWires input) =
        ((((prev.liftAssign input xi == px) && (prev.liftAssign input yi == py)) == outPol)))
    (hCount : prev.activeGates + 1 ≤ unhitBinaryGates (.snoc earlier gate) pin) :
    SymCompilation (.snoc earlier gate) pin :=
  let v := n + prev.activeGates
  let rawOut : SymLit (v + 1) := .lit (Fin.last v) outPol
  { activeGates := prev.activeGates + 1
    wireMap := Fin.snoc (fun u => (prev.wireMap u).castSucc)
      (match pin (Fin.last w) with
      | none => rawOut
      | some b => .const b)
    constraints :=
      (prev.constraints.relabel Fin.castSucc ++ encodeSignedAnd xi px yi py) ++
        (match pin (Fin.last w) with
        | none => CNF.empty
        | some b => rawOut.enforceEq b)
    liftAssign := fun input =>
      Fin.snoc (prev.liftAssign input)
        ((prev.liftAssign input xi == px) && (prev.liftAssign input yi == py))
    lift_prefix := fun input i => by
      have hCast : Fin.castAdd (prev.activeGates + 1) i =
          (Fin.castAdd prev.activeGates i).castSucc := rfl
      rw [hCast, Fin.snoc_castSucc]
      exact prev.lift_prefix input i
    width_le := by
      refine appendCNF _ _ (appendCNF _ _ (fun cl h => ?_)
        (fun cl h => encodeSignedAnd_width xi px yi py h)) fun cl h => ?_
      · simp only [CNF.relabel, Array.mem_map] at h
        obtain ⟨old, hOld, rfl⟩ := h
        simpa [CNF.Clause.relabel, CNF.Clause.Internal.size_eq_size_atoms] using
          prev.width_le old hOld
      · cases hP : pin (Fin.last w) <;> simp only [hP] at h
        · simp [CNF.empty] at h
        · exact SymLit.enforceEq_width rawOut _ h
    constraints_iff := fun σ => by
      rw [CNF.eval_append, Bool.and_eq_true, CNF.eval_append, Bool.and_eq_true,
        CNF.eval_relabel, eval_encodeSignedAnd]
      have hCompInit : σ ∘ Fin.castSucc = Fin.init σ := rfl
      rw [hCompInit, prev.constraints_iff (Fin.init σ)]
      let x : Fin n → Bool := fun i => σ (Fin.castAdd (prev.activeGates + 1) i)
      have hxEq : (fun i => Fin.init σ (Fin.castAdd prev.activeGates i)) = x := rfl
      rw [hxEq]
      constructor
      · rintro ⟨⟨⟨hInitLift, hPrevPins⟩, hLastVar⟩, hLastPin⟩
        have hFullLift : σ = Fin.snoc (prev.liftAssign x)
            ((prev.liftAssign x xi == px) && (prev.liftAssign x yi == py)) := by
          ext j
          cases j using Fin.lastCases with
          | cast j' =>
            have hj : σ j'.castSucc = Fin.init σ j' := rfl
            rw [hj, hInitLift, Fin.snoc_castSucc]
          | last =>
            rw [Fin.snoc_last, hLastVar, hInitLift]
        refine ⟨hFullLift, fun u b hub => ?_⟩
        cases u using Fin.lastCases with
        | cast u' => simpa [Circuit.evalWires] using hPrevPins u' b hub
        | last =>
          rw [hub] at hLastPin
          have hEnf := (SymLit.eval_enforceEq rawOut b σ).mp hLastPin
          rw [hFullLift] at hEnf
          have hRawVal : rawOut.eval (Fin.snoc (prev.liftAssign x)
              ((prev.liftAssign x xi == px) && (prev.liftAssign x yi == py))) =
              gate.eval (earlier.evalWires x) := by
            rw [hGateSem x hPrevPins]
            dsimp [rawOut, SymLit.eval]
            rw [Fin.snoc_last]
          rw [hRawVal] at hEnf
          simpa [Circuit.evalWires] using hEnf
      · rintro ⟨hFullLift, hAllPins⟩
        have hPrevPins : ∀ (u' : Fin w) (b : Bool),
            pin u'.castSucc = some b → earlier.evalWires x u' = b := fun u' b hub => by
          simpa [Circuit.evalWires] using hAllPins u'.castSucc b hub
        have hInitLift : Fin.init σ = prev.liftAssign x := by
          ext j'
          have hj : Fin.init σ j' = σ j'.castSucc := rfl
          rw [hj, hFullLift, Fin.snoc_castSucc]
        have hLastVar : σ (Fin.last v) =
            ((Fin.init σ xi == px) && (Fin.init σ yi == py)) := by
          rw [hInitLift]
          exact (congrFun hFullLift (Fin.last (n + prev.activeGates))).trans (Fin.snoc_last _ _)
        refine ⟨⟨⟨hInitLift, hPrevPins⟩, hLastVar⟩, ?_⟩
        cases hP : pin (Fin.last w) with
        | none => simp
        | some b =>
          rw [SymLit.eval_enforceEq, hFullLift]
          have hRawVal : rawOut.eval (Fin.snoc (prev.liftAssign x)
              ((prev.liftAssign x xi == px) && (prev.liftAssign x yi == py))) =
              gate.eval (earlier.evalWires x) := by
            rw [hGateSem x hPrevPins]
            dsimp [rawOut, SymLit.eval]
            rw [Fin.snoc_last]
          rw [hRawVal]
          simpa [Circuit.evalWires] using hAllPins (Fin.last w) b hP
    wireMap_eval := fun input hAllPins u => by
      have hPrevPins : ∀ (u' : Fin w) (b : Bool),
          pin u'.castSucc = some b → earlier.evalWires input u' = b := fun u' b hub => by
        simpa [Circuit.evalWires] using hAllPins u'.castSucc b hub
      cases u using Fin.lastCases with
      | cast u' =>
        simp only [Fin.snoc_castSucc, SymLit.eval_castSucc, Fin.init_snoc]
        simpa [Circuit.evalWires] using prev.wireMap_eval input hPrevPins u'
      | last =>
        simp only [Fin.snoc_last]
        cases hP : pin (Fin.last w) with
        | none =>
          dsimp [rawOut, SymLit.eval]
          rw [Fin.snoc_last, ← hGateSem input hPrevPins]
          simp [Circuit.evalWires]
        | some b =>
          have hb := hAllPins (Fin.last w) b hP
          simpa [SymLit.eval] using hb.symm
    pinned_is_const := fun u b hub => by
      cases u using Fin.lastCases with
      | cast u' =>
        have hPrev := prev.pinned_is_const u' b hub
        simp [hPrev, SymLit.castSucc]
      | last =>
        simp [hub]
    active_le := hCount }

/-- Symbolic step for `AND` (`outPol = true`) and De Morgan `OR` (`outPol = false` on negated
operands), folding constants, identical variables, and opposite-polarity variables for free. -/
def compileSignedAndStep {n w : Nat} {earlier : Circuit n w}
    {gate : Gate w} {pin : Fin (w + 1) → Option Bool}
    (prev : SymCompilation earlier (pin ∘ Fin.castSucc))
    (u v : Fin w) (negInputs : Bool) (outPol : Bool)
    (hSem : ∀ input, gate.eval (earlier.evalWires input) =
      (((if negInputs then !(earlier.evalWires input u) else earlier.evalWires input u) &&
        (if negInputs then !(earlier.evalWires input v) else earlier.evalWires input v)) == outPol))
    (hUnhit : unhitBinaryGates (.snoc earlier gate) pin =
      unhitBinaryGates earlier (pin ∘ Fin.castSucc) +
        if (pin u.castSucc).isSome || (pin v.castSucc).isSome then 0 else 1) :
    SymCompilation (.snoc earlier gate) pin :=
  let lu : SymLit (n + prev.activeGates) :=
    if negInputs then (prev.wireMap u).neg else prev.wireMap u
  let lv : SymLit (n + prev.activeGates) :=
    if negInputs then (prev.wireMap v).neg else prev.wireMap v
  have hLu : ∀ input,
      (∀ (q : Fin w) (b : Bool), pin q.castSucc = some b → earlier.evalWires input q = b) →
      lu.eval (prev.liftAssign input) =
        (if negInputs then !(earlier.evalWires input u) else earlier.evalWires input u) := by
    intro input hP
    have hu := prev.wireMap_eval input hP u
    cases negInputs <;> simp [lu, hu]
  have hLv : ∀ input,
      (∀ (q : Fin w) (b : Bool), pin q.castSucc = some b → earlier.evalWires input q = b) →
      lv.eval (prev.liftAssign input) =
        (if negInputs then !(earlier.evalWires input v) else earlier.evalWires input v) := by
    intro input hP
    have hv := prev.wireMap_eval input hP v
    cases negInputs <;> simp [lv, hv]
  have hMonoCount : prev.activeGates ≤ unhitBinaryGates (.snoc earlier gate) pin := by
    rw [hUnhit]
    exact prev.active_le.trans (Nat.le_add_right _ _)
  let applyOutPol (l : SymLit (n + prev.activeGates)) : SymLit (n + prev.activeGates) :=
    if outPol then l else l.neg
  have hOutPolEval (σ : Fin (n + prev.activeGates) → Bool) (l : SymLit (n + prev.activeGates)) :
      (applyOutPol l).eval σ = (l.eval σ == outPol) := by
    cases outPol <;> cases h : l.eval σ <;> simp [applyOutPol, h]
  match h1 : lu, h2 : lv with
  | .const b1, lv' =>
    let raw := applyOutPol (if b1 then lv' else .const false)
    finishFoldedStep prev raw (fun input hP => by
      rw [hSem input, ← hLu input hP, ← hLv input hP, hOutPolEval]
      cases b1 <;> rfl) hMonoCount
  | .lit xi px, .const b2 =>
    let raw := applyOutPol (if b2 then .lit xi px else .const false)
    finishFoldedStep prev raw (fun input hP => by
      rw [hSem input, ← hLu input hP, ← hLv input hP, hOutPolEval]
      cases b2 <;> simp [SymLit.eval]) hMonoCount
  | .lit xi px, .lit yi py =>
    if hEqVar : xi = yi then
      let raw := applyOutPol (if px == py then .lit xi px else .const false)
      finishFoldedStep prev raw (fun input hP => by
        subst hEqVar
        rw [hSem input, ← hLu input hP, ← hLv input hP, hOutPolEval]
        cases hVal : prev.liftAssign input xi <;> cases px <;> cases py <;>
          simp [SymLit.eval, hVal]) hMonoCount
    else
      have hU_unpinned : (pin u.castSucc).isSome = false := by
        cases hPU : pin u.castSucc with
        | none => rfl
        | some b =>
          have hC := prev.pinned_is_const u b hPU
          cases negInputs <;> simp [lu, hC, SymLit.neg] at h1
      have hV_unpinned : (pin v.castSucc).isSome = false := by
        cases hPV : pin v.castSucc with
        | none => rfl
        | some b =>
          have hC := prev.pinned_is_const v b hPV
          cases negInputs <;> simp [lv, hC, SymLit.neg] at h2
      finishFreshAndStep prev xi px yi py outPol
        (fun input hP => by
          rw [hSem input, ← hLu input hP, ← hLv input hP]
          rfl)
        (by
          rw [hUnhit, hU_unpinned, hV_unpinned]
          exact Nat.add_le_add_right prev.active_le 1)

/-- Full symbolic compiler for any `Circuit n w` and partial wire pins `pin`. -/
def compileSym {n : Nat} : {w : Nat} → (c : Circuit n w) → (pin : Fin w → Option Bool) →
    SymCompilation c pin
  | _, .inputsOnly, pin => compileInputsOnly n pin
  | _, .snoc earlier (.not u), pin =>
    let prev := compileSym earlier (pin ∘ Fin.castSucc)
    finishFoldedStep prev (prev.wireMap u).neg
      (fun input hP => by simp [Gate.eval, prev.wireMap_eval input hP u])
      prev.active_le
  | _, .snoc earlier (.and u v), pin =>
    compileSignedAndStep (compileSym earlier (pin ∘ Fin.castSucc)) u v false true
      (fun _ => by simp [Gate.eval]) rfl
  | _, .snoc earlier (.or u v), pin =>
    compileSignedAndStep (compileSym earlier (pin ∘ Fin.castSucc)) u v true false
      (fun input => by
        cases hu : earlier.evalWires input u <;> cases hv : earlier.evalWires input v <;>
          simp [Gate.eval, hu, hv])
      rfl

/-! ### 3. Exact `#SAT` Equivalence & Pinned Reader-Elimination Certificates -/

/-- Compiled width-`≤ 3` CNF requiring `source` acceptance together with `pin`. -/
def compiledCNF {n : Nat} (source : CircuitInstance n)
    (pin : Fin source.wires → Option Bool) :
    CNF (Fin (n + (compileSym source.circuit pin).activeGates)) :=
  (compileSym source.circuit pin).constraints ++
    ((compileSym source.circuit pin).wireMap source.output).enforceEq true

theorem compiledCNF_width {n : Nat} (source : CircuitInstance n)
    (pin : Fin source.wires → Option Bool)
    {cl : CNF.Clause (Fin (n + (compileSym source.circuit pin).activeGates))}
    (h : cl ∈ (compiledCNF source pin).clauses) :
    cl.size ≤ 3 :=
  appendCNF _ _ (compileSym source.circuit pin).width_le
    (fun _ hc => SymLit.enforceEq_width _ true hc) cl h

private theorem eval_compiledCNF {n : Nat} (source : CircuitInstance n)
    (pin : Fin source.wires → Option Bool)
    (σ : Fin (n + (compileSym source.circuit pin).activeGates) → Bool) :
    (compiledCNF source pin).eval σ = true ↔
      (compileSym source.circuit pin).constraints.eval σ = true ∧
      ((compileSym source.circuit pin).wireMap source.output).eval σ = true := by
  unfold compiledCNF
  rw [CNF.eval_append, Bool.and_eq_true, SymLit.eval_enforceEq]

/-- Exact bijection between models of `compiledCNF source pin` and accepting inputs of `source`
consistent with `pin`. -/
def compiledModelsEquiv {n : Nat} (source : CircuitInstance n)
    (pin : Fin source.wires → Option Bool) :
    Models (compiledCNF source pin) ≃
      { input : Fin n → Bool //
        source.eval input = true ∧
          ∀ (u : Fin source.wires) (b : Bool),
            pin u = some b → source.circuit.evalWires input u = b } where
  toFun := fun σ =>
    let comp := compileSym source.circuit pin
    let x : Fin n → Bool := fun i => σ.val (Fin.castAdd comp.activeGates i)
    ⟨x, by
      obtain ⟨hCons, hOut⟩ := (eval_compiledCNF source pin σ.val).mp σ.property
      obtain ⟨hLift, hPins⟩ := (comp.constraints_iff σ.val).mp hCons
      have hEval := comp.wireMap_eval x hPins source.output
      exact ⟨hEval.symm.trans ((congrArg ((comp.wireMap source.output).eval) hLift).symm.trans hOut),
        hPins⟩⟩
  invFun := fun input =>
    let comp := compileSym source.circuit pin
    ⟨comp.liftAssign input.val, by
      apply (eval_compiledCNF source pin _).mpr
      constructor
      · apply (comp.constraints_iff _).mpr
        have hCast : (fun i => comp.liftAssign input.val (Fin.castAdd comp.activeGates i)) =
            input.val := funext fun i => comp.lift_prefix input.val i
        rw [hCast]
        exact ⟨rfl, input.property.2⟩
      · exact (comp.wireMap_eval input.val input.property.2 source.output).trans input.property.1⟩
  left_inv := fun σ => by
    have hCons := ((eval_compiledCNF source pin σ.val).mp σ.property).1
    have hLift := (((compileSym source.circuit pin).constraints_iff σ.val).mp hCons).1
    exact Subtype.ext hLift.symm
  right_inv := fun input =>
    Subtype.ext (funext fun i => (compileSym source.circuit pin).lift_prefix input.val i)

/-- Unpinned specialization: zero-variable `.not` propagation gives an exact `#SAT` bijection
using at most `n + binaryGateCount source.circuit` variables! -/
def prunedModelsEquiv {n : Nat} (source : CircuitInstance n) :
    Models (compiledCNF source (fun _ => none)) ≃ source.Accepting :=
  (compiledModelsEquiv source (fun _ => none)).trans
    { toFun := fun x => ⟨x.val, x.property.1⟩
      invFun := fun x => ⟨x.val, x.property, fun _ _ h => by cases h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem pruned_vars_le {n : Nat} (source : CircuitInstance n) :
    n + (compileSym source.circuit (fun _ => none)).activeGates ≤
      n + binaryGateCount source.circuit :=
  Nat.add_le_add_left (compileSym source.circuit (fun _ => none)).active_le n

/-- Pin assignment induced by a Boolean assignment to `cut : Finset (Fin w)`. -/
def pinOfCut {w : Nat} (cut : Finset (Fin w)) (fixed : { u : Fin w // u ∈ cut } → Bool)
    (u : Fin w) : Option Bool :=
  if h : u ∈ cut then some (fixed ⟨u, h⟩) else none

/-- Number of binary (`AND`/`OR`) gates in `c` with neither operand in `cut`. -/
def unhitBinaryGatesOnCut {inputs : Nat} :
    {w : Nat} → Circuit inputs w → Finset (Fin w) → Nat
  | _, .inputsOnly, _ => 0
  | _, .snoc earlier (.not _), cut =>
    unhitBinaryGatesOnCut earlier (Finset.univ.filter fun q => q.castSucc ∈ cut)
  | _, .snoc earlier (.and u v), cut =>
    unhitBinaryGatesOnCut earlier (Finset.univ.filter fun q => q.castSucc ∈ cut) +
      if u.castSucc ∈ cut ∨ v.castSucc ∈ cut then 0 else 1
  | _, .snoc earlier (.or u v), cut =>
    unhitBinaryGatesOnCut earlier (Finset.univ.filter fun q => q.castSucc ∈ cut) +
      if u.castSucc ∈ cut ∨ v.castSucc ∈ cut then 0 else 1

theorem unhitBinaryGates_pinOfCut {inputs : Nat} :
    ∀ {w : Nat} (c : Circuit inputs w) (cut : Finset (Fin w))
      (fixed : { u : Fin w // u ∈ cut } → Bool),
      unhitBinaryGates c (pinOfCut cut fixed) = unhitBinaryGatesOnCut c cut
  | _, .inputsOnly, _, _ => rfl
  | _, .snoc earlier (.not _), cut, fixed => by
    let cut' := Finset.univ.filter fun q : Fin _ => q.castSucc ∈ cut
    let fixed' : { q // q ∈ cut' } → Bool :=
      fun q => fixed ⟨q.val.castSucc, (Finset.mem_filter.mp q.property).2⟩
    have hEqPin : pinOfCut cut fixed ∘ Fin.castSucc = pinOfCut cut' fixed' := by
      funext q
      by_cases hq : q.castSucc ∈ cut
      · have hq' : q ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩
        simp [pinOfCut, hq, hq', fixed']
      · have hq' : q ∉ cut' := fun h => hq (Finset.mem_filter.mp h).2
        simp [pinOfCut, hq, hq']
    simpa [unhitBinaryGates, unhitBinaryGatesOnCut, hEqPin, cut'] using
      unhitBinaryGates_pinOfCut earlier cut' fixed'
  | _, .snoc earlier (.and u v), cut, fixed => by
    let cut' := Finset.univ.filter fun q : Fin _ => q.castSucc ∈ cut
    let fixed' : { q // q ∈ cut' } → Bool :=
      fun q => fixed ⟨q.val.castSucc, (Finset.mem_filter.mp q.property).2⟩
    have hEqPin : pinOfCut cut fixed ∘ Fin.castSucc = pinOfCut cut' fixed' := by
      funext q
      by_cases hq : q.castSucc ∈ cut
      · have hq' : q ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩
        simp [pinOfCut, hq, hq', fixed']
      · have hq' : q ∉ cut' := fun h => hq (Finset.mem_filter.mp h).2
        simp [pinOfCut, hq, hq']
    have hIsSome (q : Fin _) : (pinOfCut cut fixed q).isSome = decide (q ∈ cut) := by
      by_cases hq : q ∈ cut <;> simp [pinOfCut, hq]
    simp only [unhitBinaryGates, unhitBinaryGatesOnCut, hEqPin,
      unhitBinaryGates_pinOfCut earlier cut' fixed', hIsSome, cut']
    by_cases hOr : u.castSucc ∈ cut ∨ v.castSucc ∈ cut
    · rcases hOr with hu | hv
      · simp [hu]
      · simp [hv]
    · push Not at hOr
      simp [hOr.1, hOr.2]
  | _, .snoc earlier (.or u v), cut, fixed => by
    let cut' := Finset.univ.filter fun q : Fin _ => q.castSucc ∈ cut
    let fixed' : { q // q ∈ cut' } → Bool :=
      fun q => fixed ⟨q.val.castSucc, (Finset.mem_filter.mp q.property).2⟩
    have hEqPin : pinOfCut cut fixed ∘ Fin.castSucc = pinOfCut cut' fixed' := by
      funext q
      by_cases hq : q.castSucc ∈ cut
      · have hq' : q ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩
        simp [pinOfCut, hq, hq', fixed']
      · have hq' : q ∉ cut' := fun h => hq (Finset.mem_filter.mp h).2
        simp [pinOfCut, hq, hq']
    have hIsSome (q : Fin _) : (pinOfCut cut fixed q).isSome = decide (q ∈ cut) := by
      by_cases hq : q ∈ cut <;> simp [pinOfCut, hq]
    simp only [unhitBinaryGates, unhitBinaryGatesOnCut, hEqPin,
      unhitBinaryGates_pinOfCut earlier cut' fixed', hIsSome, cut']
    by_cases hOr : u.castSucc ∈ cut ∨ v.castSucc ∈ cut
    · rcases hOr with hu | hv
      · simp [hu]
      · simp [hv]
    · push Not at hOr
      simp [hOr.1, hOr.2]

noncomputable def cutFinsetEquiv {w : Nat} (cut : Finset (Fin w)) :
    ({ u : Fin w // u ∈ cut } → Bool) ≃ Fin (2 ^ cut.card) :=
  Fintype.equivFinOfCardEq (by simp)

/-- **Pinned Cut Reader-Elimination Theorem**: conditioning `source` on any wire set
`cut : Finset (Fin source.wires)` yields an exact `2 ^ cut.card`-branch width-`≤ 3` CNF
certificate in which **every** branch uses at most
`n + unhitBinaryGatesOnCut source.circuit cut` variables (eliminating all `.not` gates and
every binary `AND`/`OR` gate incident to `cut` simultaneously across all branches!). -/
noncomputable def branchingOfPinnedCut {n : Nat} (source : CircuitInstance n)
    (cut : Finset (Fin source.wires)) : BranchingCertificate source where
  branches := 2 ^ cut.card
  vars := fun b =>
    n + (compileSym source.circuit (pinOfCut cut ((cutFinsetEquiv cut).symm b))).activeGates
  formula := fun b =>
    compiledCNF source (pinOfCut cut ((cutFinsetEquiv cut).symm b))
  modelsEquiv := by
    let slice (fixed : { u : Fin source.wires // u ∈ cut } → Bool) :=
      { input : Fin n → Bool //
        source.eval input = true ∧
          ∀ (u : Fin source.wires) (b : Bool),
            pinOfCut cut fixed u = some b → source.circuit.evalWires input u = b }
    let partEquiv : (Σ fixed, slice fixed) ≃ source.Accepting :=
      { toFun := fun s => ⟨s.2.val, s.2.property.1⟩
        invFun := fun input =>
          ⟨fun u => source.circuit.evalWires input.val u.val,
            ⟨input.val, input.property, fun u b hPin => by
              by_cases hu : u ∈ cut
              · simp [pinOfCut, hu] at hPin
                exact hPin
              · simp [pinOfCut, hu] at hPin⟩⟩
        left_inv := fun ⟨fixed, input, hEval, hPins⟩ => by
          have hFixEq : (fun u : { u // u ∈ cut } =>
              source.circuit.evalWires input u.val) = fixed := by
            funext ⟨u, hu⟩
            exact hPins u (fixed ⟨u, hu⟩) (by simp [pinOfCut, hu])
          subst hFixEq
          rfl
        right_inv := fun _ => rfl }
    exact (Equiv.sigmaCongr (cutFinsetEquiv cut).symm fun b =>
      compiledModelsEquiv source
        (pinOfCut cut ((cutFinsetEquiv cut).symm b))).trans partEquiv
  width := fun b _ h => compiledCNF_width source _ h

theorem branchingOfPinnedCut_vars_le {n : Nat} (source : CircuitInstance n)
    (cut : Finset (Fin source.wires))
    (b : Fin (branchingOfPinnedCut source cut).branches) :
    (branchingOfPinnedCut source cut).vars b ≤
      n + unhitBinaryGatesOnCut source.circuit cut := by
  dsimp [branchingOfPinnedCut]
  have hLe := (compileSym source.circuit
    (pinOfCut cut ((cutFinsetEquiv cut).symm b))).active_le
  rw [unhitBinaryGates_pinOfCut] at hLe
  exact Nat.add_le_add_left hLe n

/-- **Hitting-Cut Subexponential `#SAT` Theorem**: if a circuit family `source i` admits wire
cuts `cut i` of width `o(n i)` leaving at most `c * n i * (log (n i + 16)) ^ α` (`α < 1 / 2`)
unhit binary `AND`/`OR` gates, then every branch of `branchingOfPinnedCut (source i) (cut i)`
fits inside a certified `o(n i)` `#3-SAT` log-time budget (`2 ^ o(n i)` deterministic runtime). -/
theorem hitting_cut_subexponential {n : Nat → Nat}
    (source : (i : Nat) → CircuitInstance (n i))
    (cut : (i : Nat) → Finset (Fin (source i).wires))
    (hn : Tendsto n atTop atTop)
    (hCutCard : (fun i => ((cut i).card : ℝ)) =o[atTop] fun i => (n i : ℝ))
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hUnhit : ∀ᶠ i in atTop,
      (unhitBinaryGatesOnCut (source i).circuit (cut i) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => sopLogTimeBudget (n i) (2 ^ (cut i).card) 1
      (n i + unhitBinaryGatesOnCut (source i).circuit (cut i)) C d) =o[atTop]
      fun i => (n i : ℝ) := by
  let β : ℝ := max α 0
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  have hPoly : ∀ᶠ i in atTop, 1 ≤ (n i + 2) ^ 1 :=
    Eventually.of_forall fun _ => by rw [pow_one]; omega
  have hVars : ∀ᶠ i in atTop,
      ((n i + unhitBinaryGatesOnCut (source i).circuit (cut i) : Nat) : ℝ) ≤
        (c + 1) * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by
    filter_upwards [hUnhit, hLogN.eventually_ge_atTop 1] with i hU hLN1
    have hGe1 : 1 ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
      Real.one_le_rpow hLN1 (le_max_right α 0)
    have hRpowLe : (Real.log ((n i : ℝ) + 16)) ^ α ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
      Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left α 0)
    have hUBound : (unhitBinaryGatesOnCut (source i).circuit (cut i) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β :=
      hU.trans (mul_le_mul_of_nonneg_left hRpowLe (by positivity))
    have hNBound : (n i : ℝ) ≤ 1 * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by nlinarith
    push_cast
    linarith
  exact factored_cut_sopLogTimeBudget_isLittleO hn hCutCard 1 hPoly
    (by linarith : 0 ≤ c + 1) (max_lt hα (by norm_num) : β < 1 / 2) hVars C d

end PvsNP
