module

public import PvsNP.ValiantReduction

@[expose] public section

/-!
# Non-CNF Circuit-CSP Compilation & Shallow-vs-Deep $O(n \log n)$ Phase Diagram

Advances the algorithmic `#SAT` frontier in `PvsNP/` past the truth-table CNF block wall
established in `ValiantReduction.lean` (`SkipRing`):

1. **Exact-counting `CircuitCSP` & subcircuit embedding (`embedSub`, `LocalCircuitConstraint`,
   `CircuitCSP`, `CircuitCSPCertificate`)**: replaces truth-table CNF clause expansion of a
   `d`-input cone (`2 ^ d` clauses of width `d + 1`) by a small fan-in-2 local circuit equality
   constraint (`arity = d + 1`, `binaryGateCount < d + 3`).
2. **Universal residual-depth `CircuitCSP` compiler (`compileCircuitCSP`,
   `depthCutCSPCertificate`)**: compiles any circuit + cut with `residualDepth < H` into a
   `CircuitCSP` with `vars ≤ n + keptCount n cut + 1`, `constraintCount ≤ keptCount n cut + 2`,
   constraint arity `≤ 2 ^ H + 1`, and binary gates per constraint `≤ 2 ^ H + 2`.
3. **Valiant-to-Circuit-CSP & exponential representation gap (`valiantCSPCertificate`,
   `csp_vs_cnf_per_block_gap`, `csp_vs_cnf_depth_gap`)**: proves `2 ^ H + 2 < 2 ^ (2 ^ H)` for
   all `H ≥ 2`, separating `CircuitCSP` size per block from truth-table CNF expansion.
4. **Exact $O(n \log n)$ shallow-vs-deep phase diagram (`valiant_deep_nlogn_subexponential`,
   `valiant_shallow_nlogn_wall`, `SkipRing.source_escapes_valiant_shallow_wall`)**:
   - **Deep $O(n \log n)$ regime**: whenever binary depth is `< 2 ^ (k n)` with `k n ≥ c_k * (log n)^γ`
     (`γ > 1 / 2`), Valiant (`t = 1`) cuts down to `n + o(n sqrt(log n))` interface variables (`2 ^ o(n)`).
   - **Shallow $O(n \log n)$ wall**: whenever binary gates are `Ω(n log n)` and depth is `O(log n)`
     (`k n ≤ O(log log n)`), **every** Valiant cut schedule `t ≤ k` leaves `Ω(n log n / log log n)` cut
     wires, escaping `O(n (log n)^α)` for all `α < 1` (`SkipRing` escapes both `StrideContraction` and
     Valiant's shallow budget).
5. **Concrete deep $O(n \log n)$ witness (`DeepSkipChain`)**: bounded-fanout skip-chain circuits with
   `D = n * (Nat.log 2 n + s)` binary gates and skip span `s` that defeat `StrideContraction`
   (`source_escapes_stride_subexponential_window`) yet compress cleanly to **linear** `(2s + 3)n + 1`
   interface variables and `2 ^ o(n)` log-time budget under `valiantCSPCertificate` (`DeepSkipChain.valiant_subexponential`).
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Non-CNF `CircuitCSP` Model & Subcircuit Embedding -/

/-- A local fan-in-2 Boolean circuit constraint over `arity` variables drawn from `Fin v`. -/
structure LocalCircuitConstraint (v : Nat) where
  arity : Nat
  vars : Fin arity → Fin v
  localWires : Nat
  circuit : Circuit arity localWires
  output : Fin localWires

abbrev LocalCone (v : Nat) := LocalCircuitConstraint v

namespace LocalCircuitConstraint

def eval {v : Nat} (con : LocalCircuitConstraint v) (σ : Fin v → Bool) : Bool :=
  con.circuit.evalWires (fun i => σ (con.vars i)) con.output

def castSucc {v : Nat} (con : LocalCircuitConstraint v) : LocalCircuitConstraint (v + 1) where
  arity := con.arity
  vars := fun i => (con.vars i).castSucc
  localWires := con.localWires
  circuit := con.circuit
  output := con.output

@[simp] theorem eval_castSucc {v : Nat} (con : LocalCircuitConstraint v) (σ : Fin (v + 1) → Bool) :
    con.castSucc.eval σ = con.eval (Fin.init σ) := rfl

@[simp] theorem arity_castSucc {v : Nat} (con : LocalCircuitConstraint v) :
    con.castSucc.arity = con.arity := rfl

@[simp] theorem circuit_castSucc {v : Nat} (con : LocalCircuitConstraint v) :
    con.castSucc.circuit = con.circuit := rfl

end LocalCircuitConstraint

/-- Conjunction of local fan-in-2 Boolean circuit constraints over `Fin v`. -/
structure CircuitCSP (v : Nat) where
  constraints : List (LocalCircuitConstraint v)

namespace CircuitCSP

def eval {v : Nat} (csp : CircuitCSP v) (σ : Fin v → Bool) : Bool :=
  csp.constraints.all (fun con => con.eval σ)

def Models {v : Nat} (csp : CircuitCSP v) :=
  { σ : Fin v → Bool // csp.eval σ = true }

def constraintCount {v : Nat} (csp : CircuitCSP v) : Nat :=
  csp.constraints.length

def totalIncidence {v : Nat} (csp : CircuitCSP v) : Nat :=
  (csp.constraints.map (·.arity)).sum

def totalBinaryGates {v : Nat} (csp : CircuitCSP v) : Nat :=
  (csp.constraints.map fun con => binaryGateCount con.circuit).sum

theorem eval_cons {v : Nat} (con : LocalCircuitConstraint v)
    (rest : List (LocalCircuitConstraint v)) (σ : Fin v → Bool) :
    (CircuitCSP.mk (con :: rest)).eval σ = true ↔
      con.eval σ = true ∧ (CircuitCSP.mk rest).eval σ = true := by
  simp [CircuitCSP.eval, Bool.and_eq_true]

theorem eval_map_castSucc {v : Nat} (rest : List (LocalCircuitConstraint v))
    (σ : Fin (v + 1) → Bool) :
    (CircuitCSP.mk (rest.map LocalCircuitConstraint.castSucc)).eval σ =
      (CircuitCSP.mk rest).eval (Fin.init σ) := by
  induction rest with
  | nil => rfl
  | cons con rs ih =>
    simp only [CircuitCSP.eval, List.map_cons, List.all_cons, LocalCircuitConstraint.eval_castSucc]
    congr 1

private theorem list_sum_map_le {α : Type*} (l : List α) (f : α → Nat) (B : Nat)
    (hB : ∀ x ∈ l, f x ≤ B) :
    (l.map f).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := hB x (by simp)
    have hxs := ih fun y hy => hB y (by simp [hy])
    rw [Nat.succ_mul]
    omega

theorem totalIncidence_le {v : Nat} (csp : CircuitCSP v) (A : Nat)
    (hA : ∀ con ∈ csp.constraints, con.arity ≤ A) :
    csp.totalIncidence ≤ csp.constraintCount * A :=
  list_sum_map_le csp.constraints (·.arity) A hA

theorem totalBinaryGates_le {v : Nat} (csp : CircuitCSP v) (G : Nat)
    (hG : ∀ con ∈ csp.constraints, binaryGateCount con.circuit ≤ G) :
    csp.totalBinaryGates ≤ csp.constraintCount * G :=
  list_sum_map_le csp.constraints (fun con => binaryGateCount con.circuit) G hG

end CircuitCSP

/-- Exact-counting Circuit-CSP certificate for a `CircuitInstance n`. -/
structure CircuitCSPCertificate {n : Nat} (source : CircuitInstance n) where
  vars : Nat
  csp : CircuitCSP vars
  modelsEquiv : csp.Models ≃ source.Accepting

namespace CircuitCSPCertificate

theorem exact_count {n : Nat} {source : CircuitInstance n} (cert : CircuitCSPCertificate source) :
    Nat.card cert.csp.Models = Nat.card source.Accepting :=
  Nat.card_congr cert.modelsEquiv

theorem sat_iff {n : Nat} {source : CircuitInstance n} (cert : CircuitCSPCertificate source) :
    (∃ input, source.eval input = true) ↔
      ∃ σ : Fin cert.vars → Bool, cert.csp.eval σ = true := by
  constructor
  · rintro ⟨input, hIn⟩
    obtain ⟨σ, hSat⟩ := cert.modelsEquiv.symm ⟨input, hIn⟩
    exact ⟨σ, hSat⟩
  · rintro ⟨σ, hSat⟩
    obtain ⟨input, hIn⟩ := cert.modelsEquiv ⟨σ, hSat⟩
    exact ⟨input, hIn⟩

end CircuitCSPCertificate

/-- Embedding of `sub : Circuit m w₂` on top of `base : Circuit n w₁` via `mapIn`. -/
structure EmbeddedCircuit {n w₁ m w₂ : Nat} (base : Circuit n w₁)
    (mapIn : Fin m → Fin w₁) (sub : Circuit m w₂) where
  wires : Nat
  circuit : Circuit n wires
  liftOld : Fin w₁ → Fin wires
  liftSub : Fin w₂ → Fin wires
  old_eval : ∀ x u, circuit.evalWires x (liftOld u) = base.evalWires x u
  sub_eval : ∀ x u, circuit.evalWires x (liftSub u) =
    sub.evalWires (fun i => base.evalWires x (mapIn i)) u
  gateCount_eq : circuit.gateCount = base.gateCount + sub.gateCount
  binaryGateCount_eq : binaryGateCount circuit = binaryGateCount base + binaryGateCount sub

def embedSub {n w₁ m : Nat} (base : Circuit n w₁) (mapIn : Fin m → Fin w₁) :
    {w₂ : Nat} → (sub : Circuit m w₂) → EmbeddedCircuit base mapIn sub
  | _, .inputsOnly =>
    { wires := w₁
      circuit := base
      liftOld := fun u => u
      liftSub := mapIn
      old_eval := fun _ _ => rfl
      sub_eval := fun _ _ => rfl
      gateCount_eq := rfl
      binaryGateCount_eq := by dsimp [binaryGateCount, unhitBinaryGates] }
  | w + 1, .snoc earlier (.not a) =>
    let ih := embedSub base mapIn earlier
    { wires := ih.wires + 1
      circuit := ih.circuit.snoc (.not (ih.liftSub a))
      liftOld := fun u => (ih.liftOld u).castSucc
      liftSub := Fin.lastCases (Fin.last ih.wires) (fun q => (ih.liftSub q).castSucc)
      old_eval := fun x u => by
        simp only [Circuit.evalWires, Fin.snoc_castSucc, ih.old_eval]
      sub_eval := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          simp only [Circuit.evalWires, Gate.eval, Fin.snoc_last, ih.sub_eval]
        | cast q =>
          rw [Fin.lastCases_castSucc]
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using ih.sub_eval x q
      gateCount_eq := by
        simp only [Circuit.gateCount, ih.gateCount_eq]
        ring
      binaryGateCount_eq := by
        have h1 : binaryGateCount (ih.circuit.snoc (.not (ih.liftSub a))) =
            binaryGateCount ih.circuit := by
          dsimp [binaryGateCount, unhitBinaryGates]; rfl
        have h2 : binaryGateCount (earlier.snoc (.not a)) = binaryGateCount earlier := by
          dsimp [binaryGateCount, unhitBinaryGates]; rfl
        rw [h1, h2, ih.binaryGateCount_eq] }
  | w + 1, .snoc earlier (.and a b) =>
    let ih := embedSub base mapIn earlier
    { wires := ih.wires + 1
      circuit := ih.circuit.snoc (.and (ih.liftSub a) (ih.liftSub b))
      liftOld := fun u => (ih.liftOld u).castSucc
      liftSub := Fin.lastCases (Fin.last ih.wires) (fun q => (ih.liftSub q).castSucc)
      old_eval := fun x u => by
        simp only [Circuit.evalWires, Fin.snoc_castSucc, ih.old_eval]
      sub_eval := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          simp only [Circuit.evalWires, Gate.eval, Fin.snoc_last, ih.sub_eval]
        | cast q =>
          rw [Fin.lastCases_castSucc]
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using ih.sub_eval x q
      gateCount_eq := by
        simp only [Circuit.gateCount, ih.gateCount_eq]
        ring
      binaryGateCount_eq := by
        have h1 : binaryGateCount (ih.circuit.snoc (.and (ih.liftSub a) (ih.liftSub b))) =
            binaryGateCount ih.circuit + 1 := by
          dsimp [binaryGateCount, unhitBinaryGates]
        have h2 : binaryGateCount (earlier.snoc (.and a b)) = binaryGateCount earlier + 1 := by
          dsimp [binaryGateCount, unhitBinaryGates]
        rw [h1, h2, ih.binaryGateCount_eq]
        ring }
  | w + 1, .snoc earlier (.or a b) =>
    let ih := embedSub base mapIn earlier
    { wires := ih.wires + 1
      circuit := ih.circuit.snoc (.or (ih.liftSub a) (ih.liftSub b))
      liftOld := fun u => (ih.liftOld u).castSucc
      liftSub := Fin.lastCases (Fin.last ih.wires) (fun q => (ih.liftSub q).castSucc)
      old_eval := fun x u => by
        simp only [Circuit.evalWires, Fin.snoc_castSucc, ih.old_eval]
      sub_eval := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          simp only [Circuit.evalWires, Gate.eval, Fin.snoc_last, ih.sub_eval]
        | cast q =>
          rw [Fin.lastCases_castSucc]
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using ih.sub_eval x q
      gateCount_eq := by
        simp only [Circuit.gateCount, ih.gateCount_eq]
        ring
      binaryGateCount_eq := by
        have h1 : binaryGateCount (ih.circuit.snoc (.or (ih.liftSub a) (ih.liftSub b))) =
            binaryGateCount ih.circuit + 1 := by
          dsimp [binaryGateCount, unhitBinaryGates]; rfl
        have h2 : binaryGateCount (earlier.snoc (.or a b)) = binaryGateCount earlier + 1 := by
          dsimp [binaryGateCount, unhitBinaryGates]; rfl
        rw [h1, h2, ih.binaryGateCount_eq]
        ring }

namespace LocalCircuitConstraint

def wire {v : Nat} (u : Fin v) : LocalCone v where
  arity := 1
  vars := fun _ => u
  localWires := 1
  circuit := Circuit.inputsOnly
  output := ⟨0, Nat.zero_lt_one⟩

@[simp] theorem wire_eval {v : Nat} (u : Fin v) (σ : Fin v → Bool) :
    (wire u).eval σ = σ u := rfl

@[simp] theorem wire_arity {v : Nat} (u : Fin v) : (wire u).arity = 1 := rfl

@[simp] theorem wire_binaryGates {v : Nat} (u : Fin v) :
    binaryGateCount (wire u).circuit = 0 := rfl

def notCone {v : Nat} (c : LocalCone v) : LocalCone v where
  arity := c.arity
  vars := c.vars
  localWires := c.localWires + 1
  circuit := c.circuit.snoc (.not c.output)
  output := Fin.last c.localWires

@[simp] theorem notCone_eval {v : Nat} (c : LocalCone v) (σ : Fin v → Bool) :
    c.notCone.eval σ = !(c.eval σ) := by
  simp [notCone, LocalCircuitConstraint.eval, Circuit.evalWires, Gate.eval, Fin.snoc_last]

@[simp] theorem notCone_arity {v : Nat} (c : LocalCone v) : c.notCone.arity = c.arity := rfl

@[simp] theorem notCone_binaryGates {v : Nat} (c : LocalCone v) :
    binaryGateCount c.notCone.circuit = binaryGateCount c.circuit := rfl

def binaryCone {v : Nat} (isAnd : Bool) (c₁ c₂ : LocalCone v) : LocalCone v :=
  let base : Circuit (c₁.arity + c₂.arity) (c₁.arity + c₂.arity) := Circuit.inputsOnly
  let mapL : Fin c₁.arity → Fin (c₁.arity + c₂.arity) := Fin.castAdd c₂.arity
  let embL := embedSub base mapL c₁.circuit
  let mapR : Fin c₂.arity → Fin embL.wires := fun i => embL.liftOld (Fin.natAdd c₁.arity i)
  let embR := embedSub embL.circuit mapR c₂.circuit
  let outL := embR.liftOld (embL.liftSub c₁.output)
  let outR := embR.liftSub c₂.output
  let topGate : Gate embR.wires := if isAnd then .and outL outR else .or outL outR
  { arity := c₁.arity + c₂.arity
    vars := Fin.addCases c₁.vars c₂.vars
    localWires := embR.wires + 1
    circuit := embR.circuit.snoc topGate
    output := Fin.last embR.wires }

theorem binaryCone_eval {v : Nat} (isAnd : Bool) (c₁ c₂ : LocalCone v) (σ : Fin v → Bool) :
    (binaryCone isAnd c₁ c₂).eval σ =
      if isAnd then (c₁.eval σ && c₂.eval σ) else (c₁.eval σ || c₂.eval σ) := by
  dsimp [binaryCone, LocalCircuitConstraint.eval]
  set base : Circuit (c₁.arity + c₂.arity) (c₁.arity + c₂.arity) := Circuit.inputsOnly
  set x : Fin (c₁.arity + c₂.arity) → Bool := fun i => σ (Fin.addCases c₁.vars c₂.vars i)
  set embL := embedSub base (Fin.castAdd c₂.arity) c₁.circuit
  set embR := embedSub embL.circuit (fun i => embL.liftOld (Fin.natAdd c₁.arity i)) c₂.circuit
  have hL : embR.circuit.evalWires x (embR.liftOld (embL.liftSub c₁.output)) = c₁.eval σ := by
    rw [embR.old_eval, embL.sub_eval]
    have hIn : (fun i => base.evalWires x (Fin.castAdd c₂.arity i)) = fun i => σ (c₁.vars i) := by
      funext i
      dsimp [base, Circuit.evalWires, x]
      simp [Fin.addCases_left]
    dsimp only [LocalCircuitConstraint.eval]
    rw [hIn]
  have hR : embR.circuit.evalWires x (embR.liftSub c₂.output) = c₂.eval σ := by
    rw [embR.sub_eval]
    have hIn : (fun i => embL.circuit.evalWires x (embL.liftOld (Fin.natAdd c₁.arity i))) =
        fun i => σ (c₂.vars i) := by
      funext i
      rw [embL.old_eval]
      dsimp [base, Circuit.evalWires, x]
      simp [Fin.addCases_right]
    dsimp only [LocalCircuitConstraint.eval]
    rw [hIn]
  by_cases hA : isAnd = true
  · simp only [hA, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last,
      LocalCircuitConstraint.eval, hL, hR]
  · simp only [hA, Bool.false_eq_true, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last,
      LocalCircuitConstraint.eval, hL, hR]

@[simp] theorem binaryCone_arity {v : Nat} (isAnd : Bool) (c₁ c₂ : LocalCone v) :
    (binaryCone isAnd c₁ c₂).arity = c₁.arity + c₂.arity := rfl

theorem binaryCone_binaryGates {v : Nat} (isAnd : Bool) (c₁ c₂ : LocalCone v) :
    binaryGateCount (binaryCone isAnd c₁ c₂).circuit =
      binaryGateCount c₁.circuit + binaryGateCount c₂.circuit + 1 := by
  dsimp [binaryCone]
  set base : Circuit (c₁.arity + c₂.arity) (c₁.arity + c₂.arity) := Circuit.inputsOnly
  set embL := embedSub base (Fin.castAdd c₂.arity) c₁.circuit
  set embR := embedSub embL.circuit (fun i => embL.liftOld (Fin.natAdd c₁.arity i)) c₂.circuit
  have hTop : binaryGateCount (embR.circuit.snoc
      (if isAnd then .and (embR.liftOld (embL.liftSub c₁.output)) (embR.liftSub c₂.output)
       else .or (embR.liftOld (embL.liftSub c₁.output)) (embR.liftSub c₂.output))) =
      binaryGateCount embR.circuit + 1 := by
    cases isAnd <;> rfl
  have hBase0 : binaryGateCount base = 0 := rfl
  rw [hTop, embR.binaryGateCount_eq, embL.binaryGateCount_eq, hBase0, Nat.zero_add]

/-- Local circuit constraint enforcing `σ y == c.eval (Fin.init σ)` without CNF truth-table
expansion (`arity = c.arity + 1`, `binaryGateCount = binaryGateCount c.circuit + 3`). -/
def xnorConstraint {v : Nat} (c : LocalCone v) (y : Fin (v + 1)) : LocalCircuitConstraint (v + 1) :=
  let m := c.arity
  let emb := embedSub (Circuit.inputsOnly : Circuit (m + 1) (m + 1)) Fin.castSucc c.circuit
  let inY : Fin emb.wires := emb.liftOld (Fin.last m)
  let outC : Fin emb.wires := emb.liftSub c.output
  let c1 := emb.circuit.snoc (.not inY)
  let ny : Fin (emb.wires + 1) := Fin.last emb.wires
  let c2 := c1.snoc (.not outC.castSucc)
  let no : Fin (emb.wires + 2) := Fin.last (emb.wires + 1)
  let c3 := c2.snoc (.and inY.castSucc.castSucc outC.castSucc.castSucc)
  let both1 : Fin (emb.wires + 3) := Fin.last (emb.wires + 2)
  let c4 := c3.snoc (.and ny.castSucc.castSucc no.castSucc)
  let both0 : Fin (emb.wires + 4) := Fin.last (emb.wires + 3)
  let c5 := c4.snoc (.or both1.castSucc both0)
  { arity := m + 1
    vars := Fin.lastCases y (fun i => (c.vars i).castSucc)
    localWires := emb.wires + 5
    circuit := c5
    output := Fin.last (emb.wires + 4) }

theorem xnorConstraint_eval {v : Nat} (c : LocalCone v) (y : Fin (v + 1))
    (σ : Fin (v + 1) → Bool) :
    (c.xnorConstraint y).eval σ = true ↔ σ y = c.eval (Fin.init σ) := by
  dsimp [xnorConstraint, LocalCircuitConstraint.eval]
  set m := c.arity
  set emb := embedSub (Circuit.inputsOnly : Circuit (m + 1) (m + 1)) Fin.castSucc c.circuit
  set x : Fin (m + 1) → Bool := fun i => σ (Fin.lastCases y (fun j => (c.vars j).castSucc) i)
  have hxY : x (Fin.last m) = σ y := by simp [x]
  have hxIn : (fun i : Fin m => x i.castSucc) = fun i => (Fin.init σ) (c.vars i) := by
    funext i
    simp [x, Fin.init]
  have hY : emb.circuit.evalWires x (emb.liftOld (Fin.last m)) = σ y := by
    rw [emb.old_eval]
    exact hxY
  have hC : emb.circuit.evalWires x (emb.liftSub c.output) = c.eval (Fin.init σ) := by
    rw [emb.sub_eval]
    change c.circuit.evalWires (fun i => x i.castSucc) c.output = c.circuit.evalWires _ c.output
    rw [hxIn]
  dsimp only [Circuit.evalWires, Gate.eval, LocalCircuitConstraint.eval] at hC ⊢
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [hY, hC]
  cases h1 : σ y <;> cases h2 : c.circuit.evalWires (fun i => (Fin.init σ) (c.vars i)) c.output <;>
    simp

@[simp] theorem xnorConstraint_arity {v : Nat} (c : LocalCone v) (y : Fin (v + 1)) :
    (c.xnorConstraint y).arity = c.arity + 1 := rfl

theorem xnorConstraint_binaryGates {v : Nat} (c : LocalCone v) (y : Fin (v + 1)) :
    binaryGateCount (c.xnorConstraint y).circuit = binaryGateCount c.circuit + 3 := by
  dsimp [xnorConstraint]
  set m := c.arity
  set emb := embedSub (Circuit.inputsOnly : Circuit (m + 1) (m + 1)) Fin.castSucc c.circuit
  have hEq : binaryGateCount (emb.circuit.snoc (.not (emb.liftOld (Fin.last m)))
      |>.snoc (.not (emb.liftSub c.output).castSucc)
      |>.snoc (.and (emb.liftOld (Fin.last m)).castSucc.castSucc
          (emb.liftSub c.output).castSucc.castSucc)
      |>.snoc (.and (Fin.last emb.wires).castSucc.castSucc (Fin.last (emb.wires + 1)).castSucc)
      |>.snoc (.or (Fin.last (emb.wires + 2)).castSucc (Fin.last (emb.wires + 3)))) =
      binaryGateCount emb.circuit + 3 := by
    dsimp [binaryGateCount, unhitBinaryGates]
    change unhitBinaryGates emb.circuit (fun _ => none) + 1 + 1 + 1 =
      unhitBinaryGates emb.circuit (fun _ => none) + 3
    omega
  have hBase0 : binaryGateCount (Circuit.inputsOnly : Circuit (m + 1) (m + 1)) = 0 := rfl
  rw [hEq, emb.binaryGateCount_eq, hBase0, Nat.zero_add]

def unitTrueConstraint {v : Nat} (u : Fin v) : LocalCircuitConstraint v where
  arity := 1
  vars := fun _ => u
  localWires := 1
  circuit := Circuit.inputsOnly
  output := ⟨0, Nat.zero_lt_one⟩

theorem unitTrueConstraint_eval {v : Nat} (u : Fin v) (σ : Fin v → Bool) :
    (unitTrueConstraint u).eval σ = true ↔ σ u = true := Iff.rfl

@[simp] theorem unitTrueConstraint_arity {v : Nat} (u : Fin v) :
    (unitTrueConstraint u).arity = 1 := rfl

@[simp] theorem unitTrueConstraint_binaryGates {v : Nat} (u : Fin v) :
    binaryGateCount (unitTrueConstraint u).circuit = 0 := rfl

end LocalCircuitConstraint

/-! ### 2. Universal Residual-Depth `CircuitCSP` Compiler -/

/-- Inductive state of `compileCircuitCSP` over `Fin (n + blocks)`. -/
structure CSPState {n w : Nat} (c : Circuit n w) (cut : Fin w → Bool) (H : Nat) where
  blocks : Nat
  blocks_eq : blocks = keptCount n cut
  constraints : List (LocalCircuitConstraint (n + blocks))
  constraints_length : constraints.length = blocks
  constraints_arity : ∀ con ∈ constraints, con.arity ≤ 2 ^ H + 1
  constraints_binaryGates : ∀ con ∈ constraints, binaryGateCount con.circuit ≤ 2 ^ H + 2
  liftAssign : (Fin n → Bool) → (Fin (n + blocks) → Bool)
  lift_prefix : ∀ x (i : Fin n), liftAssign x (Fin.castAdd blocks i) = x i
  constraints_iff : ∀ σ : Fin (n + blocks) → Bool,
    (CircuitCSP.mk constraints).eval σ = true ↔
      σ = liftAssign (fun i => σ (Fin.castAdd blocks i))
  wireIdx : Fin w → Fin (n + blocks)
  wireIdx_eval : ∀ x u, (u.val < n ∨ cut u = true) → liftAssign x (wireIdx u) = c.evalWires x u
  cone : Fin w → LocalCone (n + blocks)
  cone_eval : ∀ x u, (cone u).eval (liftAssign x) = c.evalWires x u
  cone_arity : ∀ u, (cone u).arity ≤ 2 ^ (residualDepth c cut u)
  cone_binaryGates : ∀ u, binaryGateCount (cone u).circuit < 2 ^ (residualDepth c cut u)

private theorem fin_castAdd_succ_eq {n blocks : Nat} (i : Fin n) :
    Fin.castAdd (blocks + 1) i = (Fin.castAdd blocks i).castSucc :=
  Fin.ext rfl

private theorem fin_init_snoc {n : Nat} (f : Fin n → Bool) (y : Bool) :
    Fin.init (Fin.snoc (α := fun _ => Bool) f y) = f := by
  funext i
  simp [Fin.init]

private theorem fin_snoc_init_last {n : Nat} (σ : Fin (n + 1) → Bool) :
    Fin.snoc (Fin.init σ) (σ (Fin.last n)) = σ := by
  funext u
  cases u using Fin.lastCases with
  | last => simp
  | cast q => simp [Fin.init]

def extendCSPState {n w : Nat} {earlier : Circuit n w} (g : Gate w)
    (cut : Fin (w + 1) → Bool) (H : Nat) (hn : 0 < n)
    (prev : CSPState earlier (cut ∘ Fin.castSucc) H)
    (coneLast : LocalCone (n + prev.blocks))
    (hLastEval : ∀ x, coneLast.eval (prev.liftAssign x) = (earlier.snoc g).evalWires x (Fin.last w))
    (hLastArity : coneLast.arity ≤ 2 ^ H)
    (hLastBin : binaryGateCount coneLast.circuit < 2 ^ H)
    (hLastNotCut : ¬(n ≤ w ∧ cut (Fin.last w) = true) →
      coneLast.arity ≤ 2 ^ (residualDepth (earlier.snoc g) cut (Fin.last w)) ∧
      binaryGateCount coneLast.circuit < 2 ^ (residualDepth (earlier.snoc g) cut (Fin.last w))) :
    CSPState (earlier.snoc g) cut H :=
  let nw := n + prev.blocks
  if hKeep : n ≤ w ∧ cut (Fin.last w) = true then
    let newCon := coneLast.xnorConstraint (Fin.last nw)
    let newCons := newCon :: prev.constraints.map LocalCircuitConstraint.castSucc
    let newLift : (Fin n → Bool) → (Fin (n + (prev.blocks + 1)) → Bool) :=
      fun x => Fin.snoc (prev.liftAssign x) ((earlier.snoc g).evalWires x (Fin.last w))
    { blocks := prev.blocks + 1
      blocks_eq := by simp [keptCount_snoc, hKeep, prev.blocks_eq]
      constraints := newCons
      constraints_length := by simp [newCons, prev.constraints_length]
      constraints_arity := by
        intro con hMem
        simp only [newCons, List.mem_cons, List.mem_map] at hMem
        rcases hMem with rfl | ⟨old, hOld, rfl⟩
        · simpa [newCon, LocalCircuitConstraint.xnorConstraint_arity] using
            Nat.add_le_add_right hLastArity 1
        · exact prev.constraints_arity old hOld
      constraints_binaryGates := by
        intro con hMem
        simp only [newCons, List.mem_cons, List.mem_map] at hMem
        rcases hMem with rfl | ⟨old, hOld, rfl⟩
        · rw [LocalCircuitConstraint.xnorConstraint_binaryGates]
          omega
        · exact prev.constraints_binaryGates old hOld
      liftAssign := newLift
      lift_prefix := fun x i => by
        dsimp only [newLift]
        rw [fin_castAdd_succ_eq, Fin.snoc_castSucc, prev.lift_prefix]
      constraints_iff := fun σ => by
        dsimp only [newCons]
        rw [CircuitCSP.eval_cons, CircuitCSP.eval_map_castSucc, prev.constraints_iff (Fin.init σ),
          LocalCircuitConstraint.xnorConstraint_eval]
        constructor
        · rintro ⟨hLastEq, hInit⟩
          let x : Fin n → Bool := fun i => σ (Fin.castAdd (prev.blocks + 1) i)
          have hxInit : (fun i => (Fin.init σ) (Fin.castAdd prev.blocks i)) = x := by
            funext i
            simp [x, Fin.init, fin_castAdd_succ_eq]
          rw [hxInit] at hInit
          have hOut : σ (Fin.last nw) = (earlier.snoc g).evalWires x (Fin.last w) := by
            rw [hLastEq, hInit]
            exact hLastEval x
          calc
            σ = Fin.snoc (Fin.init σ) (σ (Fin.last nw)) := (fin_snoc_init_last σ).symm
            _ = Fin.snoc (prev.liftAssign x) ((earlier.snoc g).evalWires x (Fin.last w)) := by
              rw [hInit, hOut]
        · intro hSig
          let x : Fin n → Bool := fun i => σ (Fin.castAdd (prev.blocks + 1) i)
          have hInit : Fin.init σ = prev.liftAssign x := by
            calc
              Fin.init σ = Fin.init (newLift x) := by rw [← hSig]
              _ = prev.liftAssign x := fin_init_snoc _ _
          have hxInit : (fun i => (Fin.init σ) (Fin.castAdd prev.blocks i)) = x := by
            funext i
            simp [x, Fin.init, fin_castAdd_succ_eq]
          have hLastEq : σ (Fin.last nw) = coneLast.eval (Fin.init σ) := by
            rw [hInit, hLastEval]
            have hL : (newLift x) (Fin.last nw) = (earlier.snoc g).evalWires x (Fin.last w) := by
              dsimp only [newLift]
              exact Fin.snoc_last _ _
            rw [← hL, ← hSig]
          exact ⟨hLastEq, by rwa [hxInit]⟩
      wireIdx := Fin.lastCases (Fin.last nw) (fun q => (prev.wireIdx q).castSucc)
      wireIdx_eval := fun x u hu => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          dsimp only [newLift]
          exact Fin.snoc_last _ _
        | cast q =>
          rw [Fin.lastCases_castSucc]
          dsimp only [newLift]
          rw [Fin.snoc_castSucc]
          have hq : q.val < n ∨ (cut ∘ Fin.castSucc) q = true := by
            simpa [Fin.val_castSucc] using hu
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireIdx_eval x q hq
      cone := Fin.lastCases (LocalCircuitConstraint.wire (Fin.last nw))
        (fun q => (prev.cone q).castSucc)
      cone_eval := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, LocalCircuitConstraint.wire_eval]
          dsimp only [newLift]
          exact Fin.snoc_last _ _
        | cast q =>
          rw [Fin.lastCases_castSucc, LocalCircuitConstraint.eval_castSucc]
          dsimp only [newLift]
          rw [fin_init_snoc, prev.cone_eval x q]
          simp [Circuit.evalWires, Fin.snoc_castSucc]
      cone_arity := fun u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, LocalCircuitConstraint.wire_arity]
          exact Nat.one_le_two_pow
        | cast q =>
          rw [Fin.lastCases_castSucc, LocalCircuitConstraint.arity_castSucc,
            residualDepth_snoc_castSucc]
          exact prev.cone_arity q
      cone_binaryGates := fun u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, LocalCircuitConstraint.wire_binaryGates]
          exact Nat.two_pow_pos _
        | cast q =>
          rw [Fin.lastCases_castSucc, LocalCircuitConstraint.circuit_castSucc,
            residualDepth_snoc_castSucc]
          exact prev.cone_binaryGates q }
  else
    { blocks := prev.blocks
      blocks_eq := by simp [keptCount_snoc, hKeep, prev.blocks_eq]
      constraints := prev.constraints
      constraints_length := prev.constraints_length
      constraints_arity := prev.constraints_arity
      constraints_binaryGates := prev.constraints_binaryGates
      liftAssign := prev.liftAssign
      lift_prefix := prev.lift_prefix
      constraints_iff := prev.constraints_iff
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
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireIdx_eval x q hq
      cone := Fin.lastCases coneLast prev.cone
      cone_eval := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact hLastEval x
        | cast q =>
          rw [Fin.lastCases_castSucc]
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.cone_eval x q
      cone_arity := fun u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact (hLastNotCut hKeep).1
        | cast q =>
          rw [Fin.lastCases_castSucc, residualDepth_snoc_castSucc]
          exact prev.cone_arity q
      cone_binaryGates := fun u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact (hLastNotCut hKeep).2
        | cast q =>
          rw [Fin.lastCases_castSucc, residualDepth_snoc_castSucc]
          exact prev.cone_binaryGates q }

/-- **Universal Residual-Depth `CircuitCSP` Compiler**: compiles any circuit `c` with
`residualDepth c cut u < H` into a `CircuitCSP` over `n + keptCount n cut` variables with
constraint arity `≤ 2 ^ H + 1` and binary gates per constraint `≤ 2 ^ H + 2`. -/
def compileCircuitCSP {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (cut : Fin w → Bool) → (H : Nat) → (0 < H) → (0 < n) →
    (∀ u : Fin w, residualDepth c cut u < H) → CSPState c cut H
  | _, .inputsOnly, cut, H, _, _, _ =>
    { blocks := 0
      blocks_eq := by
        unfold keptCount
        have hEmpty : Finset.univ.filter (fun u : Fin n => n ≤ u.val ∧ cut u = true) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          have := u.isLt
          omega
        rw [hEmpty, Finset.card_empty]
      constraints := []
      constraints_length := rfl
      constraints_arity := fun _ h => by simp at h
      constraints_binaryGates := fun _ h => by simp at h
      liftAssign := fun x => x
      lift_prefix := fun _ _ => rfl
      constraints_iff := fun σ => by
        constructor
        · intro _
          funext i
          rfl
        · intro _
          rfl
      wireIdx := fun u => u
      wireIdx_eval := fun _ _ _ => rfl
      cone := fun u => LocalCircuitConstraint.wire u
      cone_eval := fun _ _ => rfl
      cone_arity := fun _ => Nat.one_le_two_pow
      cone_binaryGates := fun _ => Nat.two_pow_pos _ }
  | w + 1, .snoc earlier (.not a), cut, H, hH, hn, hRes =>
    let prev := compileCircuitCSP earlier (cut ∘ Fin.castSucc) H hH hn fun q => by
      simpa using hRes q.castSucc
    let da := residualDepth earlier (cut ∘ Fin.castSucc) a
    have hda : da < H := by simpa [da] using hRes a.castSucc
    have hPowH : 2 ^ da ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) (le_of_lt hda)
    extendCSPState (.not a) cut H hn prev (prev.cone a).notCone
      (fun x => by
        rw [LocalCircuitConstraint.notCone_eval, prev.cone_eval]
        simp [Circuit.evalWires, Gate.eval, Fin.snoc_last])
      ((prev.cone_arity a).trans hPowH)
      (lt_of_lt_of_le (prev.cone_binaryGates a) hPowH)
      (fun hNotKeep => by
        have hge := earlier.inputs_le_wires
        have hNotCut : cut (Fin.last w) = false := by
          cases hc : cut (Fin.last w)
          · rfl
          · exact absurd ⟨hge, hc⟩ hNotKeep
        simp only [residualDepth_snoc_not_last, hNotCut, Bool.false_eq_true, ↓reduceIte]
        exact ⟨prev.cone_arity a, prev.cone_binaryGates a⟩)
  | w + 1, .snoc earlier (.and a b), cut, H, hH, hn, hRes =>
    let prev := compileCircuitCSP earlier (cut ∘ Fin.castSucc) H hH hn fun q => by
      simpa using hRes q.castSucc
    let da := residualDepth earlier (cut ∘ Fin.castSucc) a
    let db := residualDepth earlier (cut ∘ Fin.castSucc) b
    have hda : da < H := by simpa [da] using hRes a.castSucc
    have hdb : db < H := by simpa [db] using hRes b.castSucc
    have hmLt : max da db + 1 ≤ H := by omega
    have hSumPow : 2 ^ da + 2 ^ db ≤ 2 ^ (max da db + 1) := by
      have h1 : 2 ^ da ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_left da db)
      have h2 : 2 ^ db ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_right da db)
      rw [Nat.pow_succ]
      omega
    have hPowH : 2 ^ (max da db + 1) ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) hmLt
    let coneLast := LocalCircuitConstraint.binaryCone true (prev.cone a) (prev.cone b)
    have hArityM : coneLast.arity ≤ 2 ^ (max da db + 1) := by
      rw [LocalCircuitConstraint.binaryCone_arity]
      exact (Nat.add_le_add (prev.cone_arity a) (prev.cone_arity b)).trans hSumPow
    have hBinM : binaryGateCount coneLast.circuit < 2 ^ (max da db + 1) := by
      rw [LocalCircuitConstraint.binaryCone_binaryGates]
      have ha : binaryGateCount (prev.cone a).circuit < 2 ^ da := prev.cone_binaryGates a
      have hb : binaryGateCount (prev.cone b).circuit < 2 ^ db := prev.cone_binaryGates b
      have h1 : 2 ^ da ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_left da db)
      have h2 : 2 ^ db ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_right da db)
      rw [Nat.pow_succ]
      omega
    extendCSPState (.and a b) cut H hn prev coneLast
      (fun x => by
        dsimp only [coneLast]
        rw [LocalCircuitConstraint.binaryCone_eval]
        simp [prev.cone_eval, Circuit.evalWires, Gate.eval, Fin.snoc_last])
      (hArityM.trans hPowH)
      (lt_of_lt_of_le hBinM hPowH)
      (fun hNotKeep => by
        have hge := earlier.inputs_le_wires
        have hNotCut : cut (Fin.last w) = false := by
          cases hc : cut (Fin.last w)
          · rfl
          · exact absurd ⟨hge, hc⟩ hNotKeep
        simp only [residualDepth_snoc_and_last, hNotCut, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hArityM, hBinM⟩)
  | w + 1, .snoc earlier (.or a b), cut, H, hH, hn, hRes =>
    let prev := compileCircuitCSP earlier (cut ∘ Fin.castSucc) H hH hn fun q => by
      simpa using hRes q.castSucc
    let da := residualDepth earlier (cut ∘ Fin.castSucc) a
    let db := residualDepth earlier (cut ∘ Fin.castSucc) b
    have hda : da < H := by simpa [da] using hRes a.castSucc
    have hdb : db < H := by simpa [db] using hRes b.castSucc
    have hmLt : max da db + 1 ≤ H := by omega
    have hSumPow : 2 ^ da + 2 ^ db ≤ 2 ^ (max da db + 1) := by
      have h1 : 2 ^ da ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_left da db)
      have h2 : 2 ^ db ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_right da db)
      rw [Nat.pow_succ]
      omega
    have hPowH : 2 ^ (max da db + 1) ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) hmLt
    let coneLast := LocalCircuitConstraint.binaryCone false (prev.cone a) (prev.cone b)
    have hArityM : coneLast.arity ≤ 2 ^ (max da db + 1) := by
      rw [LocalCircuitConstraint.binaryCone_arity]
      exact (Nat.add_le_add (prev.cone_arity a) (prev.cone_arity b)).trans hSumPow
    have hBinM : binaryGateCount coneLast.circuit < 2 ^ (max da db + 1) := by
      rw [LocalCircuitConstraint.binaryCone_binaryGates]
      have ha : binaryGateCount (prev.cone a).circuit < 2 ^ da := prev.cone_binaryGates a
      have hb : binaryGateCount (prev.cone b).circuit < 2 ^ db := prev.cone_binaryGates b
      have h1 : 2 ^ da ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_left da db)
      have h2 : 2 ^ db ≤ 2 ^ max da db := Nat.pow_le_pow_right (by decide) (le_max_right da db)
      rw [Nat.pow_succ]
      omega
    extendCSPState (.or a b) cut H hn prev coneLast
      (fun x => by
        dsimp only [coneLast]
        rw [LocalCircuitConstraint.binaryCone_eval]
        simp [prev.cone_eval, Circuit.evalWires, Gate.eval, Fin.snoc_last])
      (hArityM.trans hPowH)
      (lt_of_lt_of_le hBinM hPowH)
      (fun hNotKeep => by
        have hge := earlier.inputs_le_wires
        have hNotCut : cut (Fin.last w) = false := by
          cases hc : cut (Fin.last w)
          · rfl
          · exact absurd ⟨hge, hc⟩ hNotKeep
        simp only [residualDepth_snoc_or_last, hNotCut, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hArityM, hBinM⟩)

/-- Compiles any `CircuitInstance n` equipped with a depth cut (`residualDepth < H`) into an
exact-counting non-CNF `CircuitCSPCertificate`. -/
def depthCutCSPCertificate {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    CircuitCSPCertificate source :=
  let cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  let hRes' : ∀ u : Fin source.wires, residualDepth source.circuit cut' u < H := fun u =>
    lt_of_le_of_lt (residualDepth_le_of_cut_imp source.circuit cut cut'
      (fun v hv => by simp [cut', hv]) u) (hRes u)
  let hn : 0 < n := source.circuit.inputs_pos_of_wire source.output
  let st := compileCircuitCSP source.circuit cut' H hH hn hRes'
  let hOut : source.output.val < n ∨ cut' source.output = true := by
    by_cases hlt : source.output.val < n
    · exact Or.inl hlt
    · right; simp [cut', show n ≤ source.output.val by omega]
  let outCon := LocalCircuitConstraint.unitTrueConstraint (st.wireIdx source.output)
  let fullCSP : CircuitCSP (n + st.blocks) := ⟨outCon :: st.constraints⟩
  { vars := n + st.blocks
    csp := fullCSP
    modelsEquiv :=
      { toFun := fun s =>
          ⟨fun i => s.val (Fin.castAdd st.blocks i), by
            have hAll := (CircuitCSP.eval_cons outCon st.constraints s.val).mp s.property
            have hEq := (st.constraints_iff s.val).mp hAll.2
            have hOutT := (LocalCircuitConstraint.unitTrueConstraint_eval
              (st.wireIdx source.output) s.val).mp hAll.1
            have hLift : st.liftAssign (fun i => s.val (Fin.castAdd st.blocks i))
                (st.wireIdx source.output) = true := by
              rw [← hEq]
              exact hOutT
            rw [st.wireIdx_eval _ source.output hOut] at hLift
            exact hLift⟩
        invFun := fun input =>
          ⟨st.liftAssign input.val, by
            rw [CircuitCSP.eval_cons]
            constructor
            · rw [LocalCircuitConstraint.unitTrueConstraint_eval,
                st.wireIdx_eval input.val source.output hOut]
              exact input.property
            · rw [st.constraints_iff]
              have hx : (fun i => st.liftAssign input.val (Fin.castAdd st.blocks i)) = input.val := by
                funext i
                exact st.lift_prefix input.val i
              rw [hx]⟩
        left_inv := fun s => Subtype.ext <| by
          have hAll := (CircuitCSP.eval_cons outCon st.constraints s.val).mp s.property
          exact ((st.constraints_iff s.val).mp hAll.2).symm
        right_inv := fun input => Subtype.ext <| by
          funext i
          exact st.lift_prefix input.val i } }

theorem depthCutCSPCertificate_vars_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    (depthCutCSPCertificate source cut H hH hRes).vars ≤ n + keptCount n cut + 1 := by
  classical
  dsimp only [depthCutCSPCertificate]
  set cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  set st := compileCircuitCSP source.circuit cut' H hH
    (source.circuit.inputs_pos_of_wire source.output) _
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
  have hBlocks : st.blocks ≤ keptCount n cut + 1 := by
    rw [st.blocks_eq]
    calc
      keptCount n cut'
        ≤ (Finset.univ.filter (fun u : Fin source.wires => n ≤ u.val ∧ cut u = true) ∪
            {source.output}).card := Finset.card_le_card hSub
      _ ≤ keptCount n cut + ({source.output} : Finset (Fin source.wires)).card :=
          Finset.card_union_le _ _
      _ = keptCount n cut + 1 := by simp
  omega

theorem depthCutCSPCertificate_constraintCount_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    (depthCutCSPCertificate source cut H hH hRes).csp.constraintCount ≤ keptCount n cut + 2 := by
  have hV := depthCutCSPCertificate_vars_le source cut H hH hRes
  dsimp only [depthCutCSPCertificate, CircuitCSP.constraintCount] at hV ⊢
  set cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  set st := compileCircuitCSP source.circuit cut' H hH
    (source.circuit.inputs_pos_of_wire source.output) _
  simp only [List.length_cons, st.constraints_length]
  omega

theorem depthCutCSPCertificate_arity_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    ∀ con ∈ (depthCutCSPCertificate source cut H hH hRes).csp.constraints, con.arity ≤ 2 ^ H + 1 := by
  intro con hMem
  let cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  let hRes' : ∀ u : Fin source.wires, residualDepth source.circuit cut' u < H := fun u =>
    lt_of_le_of_lt (residualDepth_le_of_cut_imp source.circuit cut cut'
      (fun v hv => by simp [cut', hv]) u) (hRes u)
  let st := compileCircuitCSP source.circuit cut' H hH
    (source.circuit.inputs_pos_of_wire source.output) hRes'
  have hArity : ∀ c ∈ LocalCircuitConstraint.unitTrueConstraint (st.wireIdx source.output) ::
      st.constraints, c.arity ≤ 2 ^ H + 1 := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hOld
    · simp
    · exact st.constraints_arity c hOld
  exact hArity con hMem

theorem depthCutCSPCertificate_binaryGates_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    ∀ con ∈ (depthCutCSPCertificate source cut H hH hRes).csp.constraints,
      binaryGateCount con.circuit ≤ 2 ^ H + 2 := by
  intro con hMem
  let cut' : Fin source.wires → Bool := fun u => cut u || decide (u = source.output ∧ n ≤ u.val)
  let hRes' : ∀ u : Fin source.wires, residualDepth source.circuit cut' u < H := fun u =>
    lt_of_le_of_lt (residualDepth_le_of_cut_imp source.circuit cut cut'
      (fun v hv => by simp [cut', hv]) u) (hRes u)
  let st := compileCircuitCSP source.circuit cut' H hH
    (source.circuit.inputs_pos_of_wire source.output) hRes'
  have hGates : ∀ c ∈ LocalCircuitConstraint.unitTrueConstraint (st.wireIdx source.output) ::
      st.constraints, binaryGateCount c.circuit ≤ 2 ^ H + 2 := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hOld
    · rw [LocalCircuitConstraint.unitTrueConstraint_binaryGates]
      exact Nat.zero_le _
    · exact st.constraints_binaryGates c hOld
  exact hGates con hMem

theorem depthCutCSPCertificate_incidence_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (H : Nat) (hH : 0 < H)
    (hRes : ∀ u : Fin source.wires, residualDepth source.circuit cut u < H) :
    (depthCutCSPCertificate source cut H hH hRes).csp.totalIncidence ≤
      (keptCount n cut + 2) * (2 ^ H + 1) := by
  have h1 := CircuitCSP.totalIncidence_le (depthCutCSPCertificate source cut H hH hRes).csp
    (2 ^ H + 1) (depthCutCSPCertificate_arity_le source cut H hH hRes)
  have h2 := depthCutCSPCertificate_constraintCount_le source cut H hH hRes
  exact h1.trans (Nat.mul_le_mul_right _ h2)

/-! ### 3. Valiant-to-Circuit-CSP & Exponential Representation Savings Over CNF -/

/-- Compiles any circuit of binary depth `< 2 ^ k` via Valiant's `t`-bit cut into an
exact-counting `CircuitCSP` with `vars ≤ n + 2 * t * binaryGateCount / k + 1` and constraint
arity `≤ 2 ^ (2 ^ (k - t)) + 1`. -/
noncomputable def valiantCSPCertificate {n : Nat} (source : CircuitInstance n)
    (k t : Nat) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ u : Fin source.wires, wireDepth source.circuit u < 2 ^ k) :
    CircuitCSPCertificate source :=
  let hEx := valiantDepthReduction source.circuit k hk hDepth t ht
  depthCutCSPCertificate source (Classical.choose hEx) (2 ^ (k - t)) (Nat.two_pow_pos _)
    (Classical.choose_spec hEx).2

theorem valiantCSPCertificate_vars_le {n : Nat} (source : CircuitInstance n)
    (k t : Nat) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ u : Fin source.wires, wireDepth source.circuit u < 2 ^ k) :
    (valiantCSPCertificate source k t hk ht hDepth).vars ≤
      n + 2 * t * binaryGateCount source.circuit / k + 1 := by
  dsimp only [valiantCSPCertificate]
  have hBound := (Classical.choose_spec (valiantDepthReduction source.circuit k hk hDepth t ht)).1
  exact (depthCutCSPCertificate_vars_le _ _ _ _ _).trans (by omega)

theorem valiantCSPCertificate_arity_le {n : Nat} (source : CircuitInstance n)
    (k t : Nat) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ u : Fin source.wires, wireDepth source.circuit u < 2 ^ k) :
    ∀ con ∈ (valiantCSPCertificate source k t hk ht hDepth).csp.constraints,
      con.arity ≤ 2 ^ (2 ^ (k - t)) + 1 :=
  depthCutCSPCertificate_arity_le source _ (2 ^ (k - t)) (Nat.two_pow_pos _)
    (Classical.choose_spec (valiantDepthReduction source.circuit k hk hDepth t ht)).2

theorem valiantCSPCertificate_binaryGates_le {n : Nat} (source : CircuitInstance n)
    (k t : Nat) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ u : Fin source.wires, wireDepth source.circuit u < 2 ^ k) :
    ∀ con ∈ (valiantCSPCertificate source k t hk ht hDepth).csp.constraints,
      binaryGateCount con.circuit ≤ 2 ^ (2 ^ (k - t)) + 2 :=
  depthCutCSPCertificate_binaryGates_le source _ (2 ^ (k - t)) (Nat.two_pow_pos _)
    (Classical.choose_spec (valiantDepthReduction source.circuit k hk hDepth t ht)).2

/-- Exponential representation savings of `CircuitCSP` over truth-table CNF (`d + 2 < 2 ^ d`
binary gates per constraint vs `2 ^ d` CNF clauses for a `d`-input block). -/
theorem csp_vs_cnf_per_block_gap (d : Nat) (hd : 3 ≤ d) : d + 2 < 2 ^ d := by
  induction d with
  | zero => omega
  | succ m ih =>
    rcases eq_or_lt_of_le hd with hEq | hGt
    · have : m = 2 := by omega
      subst this
      decide
    · have ihm := ih (by omega)
      rw [Nat.pow_succ]
      omega

theorem csp_vs_cnf_depth_gap (H : Nat) (hH : 2 ≤ H) : 2 ^ H + 2 < 2 ^ (2 ^ H) := by
  have h4 : 4 ≤ 2 ^ H := by
    have : 2 ^ 2 ≤ 2 ^ H := Nat.pow_le_pow_right (by decide) hH
    simpa using this
  exact csp_vs_cnf_per_block_gap (2 ^ H) (by omega)

/-! ### 4. Exact Shallow-vs-Deep $O(n \log n)$ Phase Diagram -/

/-- **Positive Deep $O(n \log n)$ Regime**: whenever a `O(n log n)`-gate circuit family has binary
depth `< 2 ^ (k i)` with `k i ≥ c_k * (log n) ^ γ` (`γ > 1 / 2`), Valiant (`t = 1`) cuts down to
`n + O(n * (log n) ^ (1 - γ))` interface variables (`1 - γ < 1 / 2`), yielding `2 ^ o(n)`
variable scaling via `valiantCSPCertificate`. -/
theorem valiant_deep_nlogn_subexponential {n k : Nat → Nat}
    (source : (i : Nat) → CircuitInstance (n i))
    (hn : Tendsto n atTop atTop)
    (hk : ∀ i, 0 < k i)
    (hDepth : ∀ i, ∀ u : Fin (source i).wires, wireDepth (source i).circuit u < 2 ^ (k i))
    {c_g c_k γ : ℝ} (hcg : 0 ≤ c_g) (hck : 0 < c_k) (hγ : 1 / 2 < γ)
    (hGates : ∀ᶠ i in atTop,
      (binaryGateCount (source i).circuit : ℝ) ≤ c_g * (n i : ℝ) * Real.log ((n i : ℝ) + 16))
    (hDeep : ∀ᶠ i in atTop,
      c_k * (Real.log ((n i : ℝ) + 16)) ^ γ ≤ (k i : ℝ))
    (C overheadDeg : ℝ) :
    (fun i => logTimeBudget (n i)
      (valiantCSPCertificate (source i) (k i) 1 (hk i) (hk i) (hDepth i)).vars C overheadDeg)
      =o[atTop] fun i => (n i : ℝ) := by
  let α : ℝ := max (1 - γ) 0
  have hαLt : α < 1 / 2 := max_lt (by linarith) (by norm_num)
  have hαNonneg : 0 ≤ α := le_max_right _ 0
  let cTot : ℝ := 2 * c_g / c_k + 2
  have hcTot : 0 ≤ cTot := by positivity
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  have hBelow : ∀ i, n i ≤ (valiantCSPCertificate (source i) (k i) 1 (hk i) (hk i) (hDepth i)).vars :=
    fun i => Nat.le_add_right _ _
  refine logTimeBudget_isLittleO_of_rpow_log hn hBelow hcTot hαLt ?_ C overheadDeg
  filter_upwards [hGates, hDeep, hnReal.eventually_ge_atTop 1, hLogN.eventually_ge_atTop 1]
    with i hGi hKi hNi1 hLi1
  set L := Real.log ((n i : ℝ) + 16)
  have hVarsNat :
      (valiantCSPCertificate (source i) (k i) 1 (hk i) (hk i) (hDepth i)).vars ≤
        n i + 2 * binaryGateCount (source i).circuit / k i + 1 := by
    simpa using valiantCSPCertificate_vars_le (source i) (k i) 1 (hk i) (hk i) (hDepth i)
  have hVarsCast :
      ((valiantCSPCertificate (source i) (k i) 1 (hk i) (hk i) (hDepth i)).vars : ℝ) ≤
        (n i : ℝ) + (2 * binaryGateCount (source i).circuit / k i : Nat) + 1 := by
    exact_mod_cast hVarsNat
  have hkPos : (0 : ℝ) < (k i : ℝ) := Nat.cast_pos.mpr (hk i)
  have hDivCast :
      ((2 * binaryGateCount (source i).circuit / k i : Nat) : ℝ) ≤
        2 * (binaryGateCount (source i).circuit : ℝ) / (k i : ℝ) := by
    have hMulNat : (2 * binaryGateCount (source i).circuit / k i) * k i ≤
        2 * binaryGateCount (source i).circuit :=
      Nat.div_mul_le_self _ _
    have hMulReal : ((2 * binaryGateCount (source i).circuit / k i : Nat) : ℝ) * (k i : ℝ) ≤
        2 * (binaryGateCount (source i).circuit : ℝ) := by
      exact_mod_cast hMulNat
    exact (le_div_iff₀ hkPos).mpr hMulReal
  have hGateDiv :
      2 * (binaryGateCount (source i).circuit : ℝ) / (k i : ℝ) ≤
        (2 * c_g / c_k) * (n i : ℝ) * L ^ (1 - γ) := by
    have hLPos : 0 < L := by linarith
    have hNum : 2 * (binaryGateCount (source i).circuit : ℝ) ≤ 2 * (c_g * (n i : ℝ) * L) := by
      linarith
    have hDenPos : 0 < c_k * L ^ γ := mul_pos hck (Real.rpow_pos_of_pos hLPos γ)
    have hQuot := div_le_div₀ (by positivity) hNum hDenPos hKi
    have hLSplit : L / L ^ γ = L ^ (1 - γ) := by
      rw [Real.rpow_sub hLPos, Real.rpow_one]
    calc
      2 * (binaryGateCount (source i).circuit : ℝ) / (k i : ℝ)
        ≤ 2 * (c_g * (n i : ℝ) * L) / (c_k * L ^ γ) := hQuot
      _ = (2 * c_g / c_k) * (n i : ℝ) * (L / L ^ γ) := by ring
      _ = (2 * c_g / c_k) * (n i : ℝ) * L ^ (1 - γ) := by rw [hLSplit]
  have hPowGe1 : 1 ≤ L ^ α := Real.one_le_rpow hLi1 hαNonneg
  have hPowMono : L ^ (1 - γ) ≤ L ^ α := Real.rpow_le_rpow_of_exponent_le hLi1 (le_max_left _ 0)
  have h1 : (n i : ℝ) ≤ (n i : ℝ) * L ^ α := by nlinarith
  have h2 : (1 : ℝ) ≤ (n i : ℝ) * L ^ α := by nlinarith
  have h3 : (2 * c_g / c_k) * (n i : ℝ) * L ^ (1 - γ) ≤
      (2 * c_g / c_k) * (n i : ℝ) * L ^ α := by
    have hCoeff : 0 ≤ (2 * c_g / c_k) * (n i : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hPowMono hCoeff
  have hMain : (n i : ℝ) + ((2 * binaryGateCount (source i).circuit / k i : Nat) : ℝ) + 1 ≤
      cTot * (n i : ℝ) * L ^ α := by
    dsimp [cTot]
    linarith
  exact hVarsCast.trans hMain

/-- **Sharp Shallow $O(n \log n)$ Valiant Wall**: if a circuit family has `Ω(n log n)` binary gates
and shallow logarithmic depth (`k i ≤ c_k * log (log n) + d_k`), then **no** Valiant cut schedule
`t i ≥ 1` keeps the cut budget `2 * t i * s i / k i + 1` in `O(n * (log n) ^ α)` for any `α < 1`. -/
theorem valiant_shallow_nlogn_wall {n s k t : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hk : ∀ i, 0 < k i) (ht : ∀ i, 1 ≤ t i)
    {c_g c_k d_k : ℝ} (hcg : 0 < c_g) (hck : 0 ≤ c_k)
    (hGates : ∀ᶠ i in atTop,
      c_g * (n i : ℝ) * Real.log ((n i : ℝ) + 16) ≤ (s i : ℝ))
    (hShallow : ∀ᶠ i in atTop,
      (k i : ℝ) ≤ c_k * Real.log (Real.log ((n i : ℝ) + 16)) + d_k)
    (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((2 * t i * s i / k i + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α) := by
  intro hEv
  let β : ℝ := max α 0
  have hβNonneg : 0 ≤ β := le_max_right α 0
  have hβLt : β < 1 := max_lt hα (by norm_num)
  let δ : ℝ := (1 - β) / 2
  have hδPos : 0 < δ := by dsimp [δ]; linarith
  have hSumExp : δ + (β + δ) = 1 := by dsimp [δ]; ring
  let L : Nat → ℝ := fun i => Real.log ((n i : ℝ) + 16)
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  have hLDelta : Tendsto (fun i => (L i) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδPos).comp hL
  have hLogRatio : (fun i => Real.log (L i) / (L i) ^ δ) =o[atTop] (fun _ => (1 : ℝ)) := by
    have h := (isLittleO_log_rpow_atTop hδPos).comp_tendsto hL
    have hDiv := h.tendsto_div_nhds_zero
    exact (isLittleO_one_iff ℝ).mpr (by simpa [Function.comp_def] using hDiv)
  have hLogLePow : ∀ᶠ i in atTop, Real.log (L i) ≤ (L i) ^ δ := by
    have hBound1 : ∀ᶠ i in atTop, ‖Real.log (L i) / (L i) ^ δ‖ ≤ 1 := by
      simpa using hLogRatio.bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hBound1, hL.eventually_ge_atTop (Real.exp 1), hLDelta.eventually_gt_atTop 0]
      with i hR hLE hLD
    have hLogPos : 0 < Real.log (L i) := by
      have : 1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      linarith [Real.log_le_log (Real.exp_pos 1) hLE]
    have hRatio1 : Real.log (L i) / (L i) ^ δ ≤ 1 := by
      simpa [Real.norm_of_nonneg (div_nonneg hLogPos.le hLD.le)] using hR
    exact (div_le_one hLD).mp hRatio1
  let M : ℝ := c_k + max d_k 0
  let B : ℝ := (max c 0 * M) / (2 * c_g)
  have hFalse : ∀ᶠ (_i : ℕ) in atTop, False := by
    filter_upwards [hGates, hShallow, hEv, hLogLePow, hnReal.eventually_ge_atTop 1,
      hL.eventually_ge_atTop 2, hLDelta.eventually_gt_atTop (max 1 B)] with
        i hGi hKi hEvI hLLe hNi1 hL2 hLD
    have hDivStrict : 2 * (t i : ℝ) * (s i : ℝ) <
        ((2 * t i * s i / k i + 1 : Nat) : ℝ) * (k i : ℝ) := by
      have hNat : 2 * t i * s i < (2 * t i * s i / k i + 1) * k i := by
        have := Nat.lt_div_mul_add (hk i) (a := 2 * t i * s i)
        nlinarith
      exact_mod_cast hNat
    have hkPos : (0 : ℝ) < (k i : ℝ) := Nat.cast_pos.mpr (hk i)
    have htGe1 : (1 : ℝ) ≤ (t i : ℝ) := by exact_mod_cast ht i
    have hLPos : 0 < L i := by linarith
    have hRpowLe : (L i) ^ α ≤ (L i) ^ β :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left α 0)
    have hPowα : 0 ≤ (L i) ^ α := by positivity
    have hRHSBound : ((2 * t i * s i / k i + 1 : Nat) : ℝ) ≤ max c 0 * (n i : ℝ) * (L i) ^ β := by
      have hStep1 : c * (n i : ℝ) * (L i) ^ α ≤ max c 0 * (n i : ℝ) * (L i) ^ α :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left c 0) (by positivity)) hPowα
      have hStep2 : max c 0 * (n i : ℝ) * (L i) ^ α ≤ max c 0 * (n i : ℝ) * (L i) ^ β :=
        mul_le_mul_of_nonneg_left hRpowLe (by positivity)
      exact hEvI.trans (hStep1.trans (by linarith))
    have hkLe : (k i : ℝ) ≤ M * (L i) ^ δ := by
      have hLdGe1 : 1 ≤ (L i) ^ δ := by linarith [le_max_left (1 : ℝ) B]
      have hd : d_k ≤ max d_k 0 * (L i) ^ δ := by
        have h1 : d_k ≤ max d_k 0 := le_max_left d_k 0
        have h2 : max d_k 0 ≤ max d_k 0 * (L i) ^ δ :=
          le_mul_of_one_le_right (le_max_right d_k 0) hLdGe1
        exact h1.trans h2
      calc
        (k i : ℝ) ≤ c_k * Real.log (L i) + d_k := hKi
        _ ≤ c_k * (L i) ^ δ + max d_k 0 * (L i) ^ δ := by
            have := mul_le_mul_of_nonneg_left hLLe hck
            linarith
        _ = M * (L i) ^ δ := by dsimp [M]; ring
    have hLeft : 2 * c_g * (n i : ℝ) * L i ≤ 2 * (t i : ℝ) * (s i : ℝ) := by
      have h1 : 2 * c_g * (n i : ℝ) * L i ≤ 2 * (s i : ℝ) := by linarith
      have h2 : 2 * (s i : ℝ) ≤ 2 * (t i : ℝ) * (s i : ℝ) := by nlinarith
      exact h1.trans h2
    have hChain : 2 * c_g * (n i : ℝ) * L i ≤
        (max c 0 * (n i : ℝ) * (L i) ^ β) * (M * (L i) ^ δ) := by
      have h1 : 2 * (t i : ℝ) * (s i : ℝ) ≤ ((2 * t i * s i / k i + 1 : Nat) : ℝ) * (k i : ℝ) :=
        hDivStrict.le
      have h2 : ((2 * t i * s i / k i + 1 : Nat) : ℝ) * (k i : ℝ) ≤
          (max c 0 * (n i : ℝ) * (L i) ^ β) * (M * (L i) ^ δ) :=
        mul_le_mul hRHSBound hkLe hkPos.le (by positivity)
      exact hLeft.trans (h1.trans h2)
    have hLSplit : L i = (L i) ^ δ * (L i) ^ (β + δ) := by
      rw [← Real.rpow_add hLPos, hSumExp, Real.rpow_one]
    have hCancelN : 2 * c_g * (L i) ^ δ * (L i) ^ (β + δ) ≤
        max c 0 * M * (L i) ^ (β + δ) := by
      have hnPos : (0 : ℝ) < (n i : ℝ) := by positivity
      have hEqL : 2 * c_g * (n i : ℝ) * L i =
          (2 * c_g * (L i) ^ δ * (L i) ^ (β + δ)) * (n i : ℝ) := by
        conv_lhs => rw [hLSplit]
        ring
      have hEqR : (max c 0 * (n i : ℝ) * (L i) ^ β) * (M * (L i) ^ δ) =
          (max c 0 * M * (L i) ^ (β + δ)) * (n i : ℝ) := by
        have hPowAdd : (L i) ^ β * (L i) ^ δ = (L i) ^ (β + δ) :=
          (Real.rpow_add hLPos _ _).symm
        calc
          (max c 0 * (n i : ℝ) * (L i) ^ β) * (M * (L i) ^ δ)
            = (max c 0 * M * ((L i) ^ β * (L i) ^ δ)) * (n i : ℝ) := by ring
          _ = (max c 0 * M * (L i) ^ (β + δ)) * (n i : ℝ) := by rw [hPowAdd]
      rw [hEqL, hEqR] at hChain
      exact le_of_mul_le_mul_right hChain hnPos
    have hPowBD : 0 < (L i) ^ (β + δ) := Real.rpow_pos_of_pos hLPos _
    have hCancelBD : 2 * c_g * (L i) ^ δ ≤ max c 0 * M := by
      have hEq : 2 * c_g * (L i) ^ δ * (L i) ^ (β + δ) =
          (2 * c_g * (L i) ^ δ) * (L i) ^ (β + δ) := by ring
      rw [hEq] at hCancelN
      exact le_of_mul_le_mul_right hCancelN hPowBD
    have hDivCg : (L i) ^ δ ≤ B := by
      dsimp [B]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c_g)).mpr (by linarith)
    linarith [le_max_right (1 : ℝ) B]
  obtain ⟨_, h⟩ := hFalse.exists
  exact h

namespace SkipRing

/-- Concrete instantiation: at logarithmic depth `D = Nat.log 2 n + s`, `SkipRing` escapes **both**
`StrideContraction` and Valiant's cut budget (`< α` log power for all `α < 1`). -/
theorem source_escapes_valiant_shallow_wall (k : Nat → Nat) (s : Nat)
    (hk : Tendsto k atTop atTop) (t : Nat → Nat) (ht : ∀ i, 1 ≤ t i)
    (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((2 * t i * binaryGateCount (source (k i) (Nat.log 2 (k i + 1) + s) s).circuit /
          (Nat.log 2 (Nat.log 2 (k i + 1) + s) + 1) + 1 : Nat) : ℝ) ≤
        c * ((k i + 1 : Nat) : ℝ) * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ α) := by
  let n : Nat → Nat := fun i => k i + 1
  let sg : Nat → Nat := fun i => binaryGateCount (source (k i) (Nat.log 2 (n i) + s) s).circuit
  let kBit : Nat → Nat := fun i => Nat.log 2 (Nat.log 2 (n i) + s) + 1
  have hnNat : Tendsto n atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hk b
      exact ⟨M, fun i hi => by have := hM i hi; dsimp [n]; omega⟩
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnNat
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCgPos : 0 < 1 / (2 * Real.log 2) := by positivity
  have hGates : ∀ᶠ i in atTop,
      (1 / (2 * Real.log 2)) * (n i : ℝ) * Real.log ((n i : ℝ) + 16) ≤ (sg i : ℝ) := by
    filter_upwards [hnNat.eventually_ge_atTop 16] with i hN16
    have hEqSg : sg i = (Nat.log 2 (n i) + s) * n i := by
      simpa [sg, n] using source_binaryGateCount (k i) (Nat.log 2 (n i) + s) s
    have hPowBound : (n i : ℝ) + 16 < (2 : ℝ) ^ (Nat.log 2 (n i) + 2) := by
      have hNatLt : n i < 2 ^ (Nat.log 2 (n i) + 1) :=
        Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n i)
      have hNat2 : n i + 16 < 2 ^ (Nat.log 2 (n i) + 2) := by
        rw [Nat.pow_succ]
        omega
      exact_mod_cast hNat2
    have hLLe : Real.log ((n i : ℝ) + 16) ≤ ((Nat.log 2 (n i) : ℝ) + 2) * Real.log 2 := by
      have hPosL : 0 < (n i : ℝ) + 16 := by positivity
      simpa [Real.log_pow] using Real.log_le_log hPosL hPowBound.le
    have hLogGe4 : 4 ≤ Nat.log 2 (n i) := by
      have hMono := Nat.log_mono_right (b := 2) hN16
      have hLog16 : Nat.log 2 16 = 4 := by decide
      omega
    have hLogRealGe4 : (4 : ℝ) ≤ (Nat.log 2 (n i) : ℝ) := by exact_mod_cast hLogGe4
    have hLin : (Nat.log 2 (n i) : ℝ) + 2 ≤ 2 * (Nat.log 2 (n i) : ℝ) := by linarith
    have hLogDiv : (1 / (2 * Real.log 2)) * Real.log ((n i : ℝ) + 16) ≤ (Nat.log 2 (n i) : ℝ) := by
      calc
        (1 / (2 * Real.log 2)) * Real.log ((n i : ℝ) + 16)
          ≤ (1 / (2 * Real.log 2)) * (((Nat.log 2 (n i) : ℝ) + 2) * Real.log 2) := by
              exact mul_le_mul_of_nonneg_left hLLe (by positivity)
        _ = ((Nat.log 2 (n i) : ℝ) + 2) / 2 := by field_simp
        _ ≤ (Nat.log 2 (n i) : ℝ) := by linarith
    have hSgGe : ((Nat.log 2 (n i) : ℝ)) * (n i : ℝ) ≤ (sg i : ℝ) := by
      rw [hEqSg]
      have hNat : Nat.log 2 (n i) * n i ≤ (Nat.log 2 (n i) + s) * n i :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      have hReal : ((Nat.log 2 (n i) * n i : Nat) : ℝ) ≤
          (((Nat.log 2 (n i) + s) * n i : Nat) : ℝ) := by exact_mod_cast hNat
      simpa using hReal
    calc
      (1 / (2 * Real.log 2)) * (n i : ℝ) * Real.log ((n i : ℝ) + 16)
        = (n i : ℝ) * ((1 / (2 * Real.log 2)) * Real.log ((n i : ℝ) + 16)) := by ring
      _ ≤ (n i : ℝ) * (Nat.log 2 (n i) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hLogDiv (by positivity)
      _ ≤ (sg i : ℝ) := by linarith
  have hShallow : ∀ᶠ i in atTop,
      (kBit i : ℝ) ≤
        (1 / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) +
          ((Real.log ((s : ℝ) + 2) + Real.log (1 / Real.log 2 + 1)) / Real.log 2 + 1) := by
    filter_upwards [hnNat.eventually_ge_atTop 16, hnReal.eventually_ge_atTop (Real.exp 1)] with
        i hN16 hNExp
    have hPowLog : (2 : ℝ) ^ Nat.log 2 (Nat.log 2 (n i) + s) ≤
        ((Nat.log 2 (n i) + s : Nat) : ℝ) := by
      have hNat : 2 ^ Nat.log 2 (Nat.log 2 (n i) + s) ≤ Nat.log 2 (n i) + s :=
        Nat.pow_log_le_self 2 (by
          have h4 : 4 ≤ Nat.log 2 (n i) := by
            have := Nat.log_mono_right (b := 2) hN16
            have h16 : Nat.log 2 16 = 4 := by decide
            omega
          omega)
      exact_mod_cast hNat
    have hNatLogLe : ((Nat.log 2 (n i) : ℝ)) * Real.log 2 ≤ Real.log ((n i : ℝ) + 16) := by
      have h2Pow : (2 : ℝ) ^ Nat.log 2 (n i) ≤ (n i : ℝ) + 16 := by
        have hNat : 2 ^ Nat.log 2 (n i) ≤ n i := Nat.pow_log_le_self 2 (by omega)
        have hReal : ((2 ^ Nat.log 2 (n i) : Nat) : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hNat
        push_cast at hReal
        linarith
      have hPowPos : 0 < (2 : ℝ) ^ Nat.log 2 (n i) := by positivity
      simpa [Real.log_pow] using Real.log_le_log hPowPos h2Pow
    have hSumLe : (Nat.log 2 (n i) : ℝ) + (s : ℝ) ≤
        (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) + ((s : ℝ) + 2) := by
      have hDiv : (Nat.log 2 (n i) : ℝ) ≤ (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) := by
        calc
          (Nat.log 2 (n i) : ℝ)
            = (Nat.log 2 (n i) : ℝ) * Real.log 2 / Real.log 2 := by field_simp
          _ ≤ Real.log ((n i : ℝ) + 16) / Real.log 2 :=
              div_le_div_of_nonneg_right hNatLogLe hLog2Pos.le
          _ = (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) := by ring
      linarith
    have hLPowLe : Real.log ((Nat.log 2 (n i) : ℝ) + s) ≤
        Real.log (Real.log ((n i : ℝ) + 16)) + Real.log ((s : ℝ) + 2) +
          Real.log (1 / Real.log 2 + 1) := by
      have hPos1 : 0 < (Nat.log 2 (n i) : ℝ) + s := by
        have h4 : 4 ≤ Nat.log 2 (n i) := by
          have := Nat.log_mono_right (b := 2) hN16
          have h16 : Nat.log 2 16 = 4 := by decide
          omega
        have h4r : (4 : ℝ) ≤ (Nat.log 2 (n i) : ℝ) := by exact_mod_cast h4
        positivity
      have hL16 : 1 ≤ Real.log ((n i : ℝ) + 16) := by
        have : Real.exp 1 ≤ (n i : ℝ) + 16 := by linarith
        simpa using Real.log_le_log (Real.exp_pos 1) this
      have hProdBound : (Nat.log 2 (n i) : ℝ) + s ≤
          (Real.log ((n i : ℝ) + 16)) * (((s : ℝ) + 2) * (1 / Real.log 2 + 1)) := by
        have hS : (s : ℝ) + 2 ≤ ((s : ℝ) + 2) * Real.log ((n i : ℝ) + 16) :=
          le_mul_of_one_le_right (by positivity) hL16
        have hGe1 : (1 : ℝ) ≤ (s : ℝ) + 2 := by linarith [show (0 : ℝ) ≤ (s : ℝ) by positivity]
        have h1 : (1 / Real.log 2) * Real.log ((n i : ℝ) + 16) ≤
            (Real.log ((n i : ℝ) + 16)) * (((s : ℝ) + 2) * (1 / Real.log 2)) := by
          calc
            (1 / Real.log 2) * Real.log ((n i : ℝ) + 16)
              = 1 * ((1 / Real.log 2) * Real.log ((n i : ℝ) + 16)) := by ring
            _ ≤ ((s : ℝ) + 2) * ((1 / Real.log 2) * Real.log ((n i : ℝ) + 16)) :=
                mul_le_mul_of_nonneg_right hGe1 (by positivity)
            _ = (Real.log ((n i : ℝ) + 16)) * (((s : ℝ) + 2) * (1 / Real.log 2)) := by ring
        linarith
      have hLogMul : Real.log ((Nat.log 2 (n i) : ℝ) + s) ≤
          Real.log (Real.log ((n i : ℝ) + 16) * (((s : ℝ) + 2) * (1 / Real.log 2 + 1))) :=
        Real.log_le_log hPos1 hProdBound
      have hPosA : Real.log ((n i : ℝ) + 16) ≠ 0 := by linarith
      have hInvPos : 1 / Real.log 2 + 1 ≠ 0 := by positivity
      have hPosB : ((s : ℝ) + 2) * (1 / Real.log 2 + 1) ≠ 0 := by positivity
      have hPosS : (s : ℝ) + 2 ≠ 0 := by positivity
      rw [Real.log_mul hPosA hPosB, Real.log_mul hPosS hInvPos] at hLogMul
      linarith
    have hKBit : ((Nat.log 2 (Nat.log 2 (n i) + s) : ℝ)) * Real.log 2 ≤
        Real.log ((Nat.log 2 (n i) : ℝ) + s) := by
      have hPosPow : 0 < (2 : ℝ) ^ Nat.log 2 (Nat.log 2 (n i) + s) := by positivity
      have hLogP := Real.log_le_log hPosPow hPowLog
      simpa [Real.log_pow] using hLogP
    have hFinal : (kBit i : ℝ) = (Nat.log 2 (Nat.log 2 (n i) + s) : ℝ) + 1 := by
      dsimp [kBit]
      push_cast
      ring
    rw [hFinal]
    have hDivBit : (Nat.log 2 (Nat.log 2 (n i) + s) : ℝ) ≤
        (Real.log (Real.log ((n i : ℝ) + 16)) + Real.log ((s : ℝ) + 2) +
          Real.log (1 / Real.log 2 + 1)) / Real.log 2 := by
      rw [le_div_iff₀ hLog2Pos]
      exact hKBit.trans hLPowLe
    calc
      (Nat.log 2 (Nat.log 2 (n i) + s) : ℝ) + 1
        ≤ (Real.log (Real.log ((n i : ℝ) + 16)) + Real.log ((s : ℝ) + 2) +
            Real.log (1 / Real.log 2 + 1)) / Real.log 2 + 1 := by
          linarith
      _ = (1 / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) +
            ((Real.log ((s : ℝ) + 2) + Real.log (1 / Real.log 2 + 1)) / Real.log 2 + 1) := by ring
  exact valiant_shallow_nlogn_wall hnNat (fun _ => Nat.succ_pos _) ht hCgPos (by positivity)
    hGates hShallow c α hα

end SkipRing

/-! ### 5. Concrete Deep $O(n \log n)$ Separation Witness (`DeepSkipChain`) -/

namespace DeepSkipChain

def chainGate (k D s i : Nat) (_hi : i < D) : Gate ((k + 1) + i) :=
  let n := k + 1
  have hnPos : 0 < n := Nat.succ_pos k
  let a : Fin (n + i) := if hi0 : i = 0 then ⟨0, by omega⟩ else ⟨n + i - 1, by omega⟩
  let b : Fin (n + i) :=
    if hs : 0 < s ∧ s ≤ i then ⟨n + i - s, by omega⟩ else ⟨i % n, by
      have hm := Nat.mod_lt i hnPos
      omega⟩
  if i % 2 = 0 then .and a b else .or a b

def buildChain (k s : Nat) : (i : Nat) → Circuit (k + 1) ((k + 1) + i)
  | 0 => Circuit.inputsOnly
  | i + 1 => (buildChain k s i).snoc (chainGate k (i + 1) s i (Nat.lt_succ_self i))

/-- Linear-width deep skip-chain circuit on `n = k + 1` inputs with `D` binary gates and backward
skip span `s`. -/
def source (k D s : Nat) : CircuitInstance (k + 1) where
  wires := (k + 1) + D
  circuit := buildChain k s D
  output := ⟨k + D, by omega⟩

private theorem chainGate_ext (k D₁ D₂ s i : Nat) (h1 : i < D₁) (h2 : i < D₂) :
    chainGate k D₁ s i h1 = chainGate k D₂ s i h2 := rfl

private theorem binaryGateCount_snoc_ite {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    binaryGateCount (c.snoc (if P then .and a b else .or a b)) = binaryGateCount c + 1 := by
  by_cases hP : P
  · rw [ite_eq_left_iff.mpr (fun h => absurd hP h)]; rfl
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hP)]; rfl

private theorem wireDepth_snoc_ite_last {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b : Fin w) :
    wireDepth (c.snoc (if P then .and a b else .or a b)) (Fin.last w) =
      max (wireDepth c a) (wireDepth c b) + 1 := by
  by_cases hP : P
  · rw [ite_eq_left_iff.mpr (fun h => absurd hP h), wireDepth_snoc_and_last]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hP), wireDepth_snoc_or_last]

private theorem maxBinaryReaderDepth_snoc_ite_castSucc {n w : Nat} (c : Circuit n w)
    (P : Prop) [Decidable P] (a b q : Fin w) :
    maxBinaryReaderDepth (c.snoc (if P then .and a b else .or a b)) q.castSucc =
      if q = a ∨ q = b then
        max (maxBinaryReaderDepth c q) (max (wireDepth c a) (wireDepth c b) + 1)
      else maxBinaryReaderDepth c q := by
  by_cases hP : P
  · rw [ite_eq_left_iff.mpr (fun h => absurd hP h), maxBinaryReaderDepth_snoc_and_castSucc]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hP), maxBinaryReaderDepth_snoc_or_castSucc]

theorem source_binaryGateCount (k D s : Nat) :
    binaryGateCount (source k D s).circuit = D := by
  dsimp [source]
  induction D with
  | zero => simp [buildChain, binaryGateCount, unhitBinaryGates]
  | succ D ih =>
    change binaryGateCount ((buildChain k s D).snoc (chainGate k (D + 1) s D (Nat.lt_succ_self D))) =
      D + 1
    dsimp [chainGate]
    rw [binaryGateCount_snoc_ite, ih]

theorem source_wireDepth (k D s : Nat) (u : Fin (source k D s).wires) :
    wireDepth (source k D s).circuit u = if u.val < k + 1 then 0 else u.val - k := by
  dsimp [source]
  induction D with
  | zero =>
    have hu : u.val < k + 1 := u.isLt
    change wireDepth Circuit.inputsOnly u = _
    simp [hu]
  | succ D ih =>
    cases u using Fin.lastCases with
    | cast q =>
      change wireDepth ((buildChain k s D).snoc (chainGate k (D + 1) s D (Nat.lt_succ_self D)))
          q.castSucc = _
      rw [wireDepth_snoc_castSucc]
      simpa [Fin.val_castSucc] using ih q
    | last =>
      change wireDepth ((buildChain k s D).snoc (chainGate k (D + 1) s D (Nat.lt_succ_self D)))
          (Fin.last ((k + 1) + D)) = _
      let n := k + 1
      have hnPos : 0 < n := Nat.succ_pos k
      let a : Fin (n + D) := if hi0 : D = 0 then ⟨0, by omega⟩ else ⟨n + D - 1, by omega⟩
      let b : Fin (n + D) := if hs : 0 < s ∧ s ≤ D then ⟨n + D - s, by omega⟩ else ⟨D % n, by
        have hm := Nat.mod_lt D hnPos; omega⟩
      have haD : wireDepth (buildChain k s D) a = D := by
        rw [ih a]
        by_cases hi0 : D = 0
        · simp [a, hi0]
        · have haVal : a.val = k + D := by dsimp [a, n]; simp [hi0]
          rw [haVal]
          simp [show ¬(k + D < k + 1) by omega]
      have hbLe : wireDepth (buildChain k s D) b ≤ D := by
        rw [ih b]
        have hbLt : b.val < (k + 1) + D := b.isLt
        split_ifs <;> omega
      dsimp [chainGate]
      rw [wireDepth_snoc_ite_last]
      change max (wireDepth (buildChain k s D) a) (wireDepth (buildChain k s D) b) + 1 = _
      rw [haD, max_eq_left hbLe]
      simp only [show ¬((k + 1) + D < k + 1) by omega, ↓reduceIte]
      omega

theorem buildChain_maxBinaryReaderDepth_ge (k D s : Nat) (hs : 0 < s) :
    ∀ u : Fin ((k + 1) + D), k + 1 ≤ u.val → u.val + s < (k + 1) + D →
      u.val - k + s ≤ maxBinaryReaderDepth (buildChain k s D) u := by
  induction D with
  | zero =>
    intro u hGe hLt
    omega
  | succ D ih =>
    intro u hGe hLt
    cases u using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Nat.add_eq] at hLt
      omega
    | cast q =>
      change _ ≤ maxBinaryReaderDepth ((buildChain k s D).snoc
          (chainGate k (D + 1) s D (Nat.lt_succ_self D))) q.castSucc
      have hGeOld : maxBinaryReaderDepth (buildChain k s D) q ≤
          maxBinaryReaderDepth ((buildChain k s D).snoc
            (chainGate k (D + 1) s D (Nat.lt_succ_self D))) q.castSucc :=
        maxBinaryReaderDepth_snoc_castSucc_ge (buildChain k s D) _ q
      simp only [Fin.val_castSucc] at hGe hLt ⊢
      by_cases hOld : q.val + s < (k + 1) + D
      · exact (ih q hGe hOld).trans hGeOld
      · have hHit : q.val + s = (k + 1) + D := by omega
        let n := k + 1
        have hnPos : 0 < n := Nat.succ_pos k
        let a : Fin (n + D) := if hi0 : D = 0 then ⟨0, by omega⟩ else ⟨n + D - 1, by omega⟩
        let b : Fin (n + D) := if hs' : 0 < s ∧ s ≤ D then ⟨n + D - s, by omega⟩ else ⟨D % n, by
          have hm := Nat.mod_lt D hnPos; omega⟩
        have hSD : s ≤ D := by omega
        have hEqB : q = b := by
          apply Fin.ext
          dsimp [b, n]
          simp [hs, hSD]
          omega
        have haD : wireDepth (buildChain k s D) a = D := by
          have := source_wireDepth k D s a
          dsimp [source] at this
          rw [this]
          by_cases hi0 : D = 0
          · simp [a, hi0]
          · have haVal : a.val = k + D := by dsimp [a, n]; simp [hi0]
            rw [haVal]
            simp [show ¬(k + D < k + 1) by omega]
        have hbLe : wireDepth (buildChain k s D) b ≤ D := by
          have := source_wireDepth k D s b
          dsimp [source] at this
          rw [this]
          have hbLt : b.val < (k + 1) + D := b.isLt
          split_ifs <;> omega
        dsimp [chainGate]
        rw [maxBinaryReaderDepth_snoc_ite_castSucc]
        change q.val - k + s ≤ if q = a ∨ q = b then
            max (maxBinaryReaderDepth (buildChain k s D) q)
              (max (wireDepth (buildChain k s D) a) (wireDepth (buildChain k s D) b) + 1)
          else maxBinaryReaderDepth (buildChain k s D) q
        rw [ite_eq_left_iff.mpr (fun hNot => absurd (Or.inr hEqB) hNot), haD, max_eq_left hbLe]
        exact le_trans (by omega) (le_max_right _ _)

theorem source_stride_blocks_ge (k D s h : Nat) (hh : 0 < h) (hLe : h ≤ s) :
    D - s ≤ (strideCertificate (source k D s) h hh).blocks := by
  have hs : 0 < s := lt_of_lt_of_le hh hLe
  let core : Finset (Fin (source k D s).wires) :=
    Finset.univ.filter fun u : Fin (source k D s).wires =>
      k + 1 ≤ u.val ∧ u.val + s < (k + 1) + D
  have hCoreCard : core.card = D - s := by
    by_cases hDs : D ≤ s
    · have hEmpty : core = ∅ := by
        ext u
        simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        omega
      rw [hEmpty, Finset.card_empty, Nat.sub_eq_zero_of_le hDs]
    · let f : Fin (D - s) → Fin (source k D s).wires := fun i =>
        ⟨(k + 1) + i.val, by dsimp [source]; omega⟩
      have hCard : core.card = (Finset.univ : Finset (Fin (D - s))).card := by
        refine (Finset.card_bij (fun i _ => f i) ?_ ?_ ?_).symm
        · intro i _
          simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, f]
          omega
        · intro i₁ _ i₂ _ hEq
          have hv := congrArg Fin.val hEq
          dsimp [f] at hv
          exact Fin.ext (by omega)
        · intro u hu
          obtain ⟨hGe, hLt⟩ := (Finset.mem_filter.mp hu).2
          refine ⟨⟨u.val - (k + 1), by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
          dsimp [f]
          omega
      simpa using hCard
  refine strideCertificate_blocks_ge_min_crossing (source k D s) h hh (D - s) fun r => ?_
  have hSub : core ⊆ crossingWires (source k D s).circuit h r.val := by
    intro u hu
    obtain ⟨hGe, hLt⟩ := (Finset.mem_filter.mp hu).2
    have hD := source_wireDepth k D s u
    have hM := buildChain_maxBinaryReaderDepth_ge k D s hs u hGe hLt
    have hNotLt : ¬(u.val < k + 1) := by omega
    have hDVal : wireDepth (source k D s).circuit u = u.val - k := by
      rw [hD, ite_eq_right_iff.mpr (fun h => absurd h hNotLt)]
    have hMCirc : u.val - k + s ≤ maxBinaryReaderDepth (source k D s).circuit u := hM
    have hPlus : wireDepth (source k D s).circuit u + h ≤
        maxBinaryReaderDepth (source k D s).circuit u := by
      rw [hDVal]
      omega
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
    D - s = core.card := hCoreCard.symm
    _ ≤ (crossingWires (source k D s).circuit h r.val).card := Finset.card_le_card hSub

/-- **`DeepSkipChain` Escapes `StrideContraction`**: at `D = (k + 1) * (Nat.log 2 (k + 1) + s)`
(`O(n log n)` binary gates), `strideCertificate` still requires `Ω(n log n)` blocks. -/
theorem source_escapes_stride_subexponential_window (k : Nat → Nat) (s h : Nat)
    (hh : 0 < h) (hLe : h ≤ s) (hk : Tendsto k atTop atTop) (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((strideCertificate (source (k i) ((k i + 1) * (Nat.log 2 (k i + 1) + s)) s) h hh).blocks : ℝ) ≤
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
  let K : ℝ := (max c 0 + 3) * Real.log 2
  have hK : ∀ᶠ i in atTop, K < (L i) ^ (1 - β) :=
    hLRpow.eventually_gt_atTop K
  have hN16 : ∀ᶠ i in atTop, max 16 s ≤ n i := hnNat.eventually_ge_atTop (max 16 s)
  have hL1 : ∀ᶠ i in atTop, 1 ≤ L i := hL.eventually_ge_atTop 1
  obtain ⟨i, hEvI, hKI, hNMaxI, hL1I⟩ := (hEv.and (hK.and (hN16.and hL1))).exists
  have hN16I : 16 ≤ n i := (le_max_left 16 s).trans hNMaxI
  have hNSI : s ≤ n i := (le_max_right 16 s).trans hNMaxI
  let D := n i * (Nat.log 2 (n i) + s)
  have hGeSub : D - s ≤
      (strideCertificate (source (k i) D s) h hh).blocks :=
    source_stride_blocks_ge (k i) D s h hh hLe
  have hNatLogMul : Nat.log 2 (n i) * n i - s ≤ D - s := by
    refine Nat.sub_le_sub_right ?_ s
    dsimp [D]
    rw [Nat.mul_comm (n i) (Nat.log 2 (n i) + s)]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hSubGe : (Nat.log 2 (n i) : ℝ) * (n i : ℝ) - (s : ℝ) ≤
      ((strideCertificate (source (k i) D s) h hh).blocks : ℝ) := by
    have hNat : Nat.log 2 (n i) * n i - s ≤ (strideCertificate (source (k i) D s) h hh).blocks :=
      hNatLogMul.trans hGeSub
    have hReal : ((Nat.log 2 (n i) * n i - s : Nat) : ℝ) ≤
        ((strideCertificate (source (k i) D s) h hh).blocks : ℝ) := by exact_mod_cast hNat
    have hSubCast : (Nat.log 2 (n i) : ℝ) * (n i : ℝ) - (s : ℝ) ≤
        ((Nat.log 2 (n i) * n i - s : Nat) : ℝ) := by
      have h1 : (Nat.log 2 (n i) : ℝ) * (n i : ℝ) ≤
          ((Nat.log 2 (n i) * n i - s : Nat) : ℝ) + (s : ℝ) := by
        have h1Nat : Nat.log 2 (n i) * n i ≤ (Nat.log 2 (n i) * n i - s) + s := by omega
        exact_mod_cast h1Nat
      linarith
    exact hSubCast.trans hReal
  have hnPos : (0 : ℝ) < (n i : ℝ) := by positivity
  have hRpowLe : (L i) ^ α ≤ (L i) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hL1I (le_max_left α 0)
  have hPow0 : 0 ≤ (L i) ^ α := by positivity
  have hUpper : ((strideCertificate (source (k i) D s) h hh).blocks : ℝ) ≤
      max c 0 * (n i : ℝ) * (L i) ^ β := by
    have h1 : c * (n i : ℝ) * (L i) ^ α ≤ max c 0 * (n i : ℝ) * (L i) ^ α :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left c 0) hnPos.le) hPow0
    have h2 : max c 0 * (n i : ℝ) * (L i) ^ α ≤ max c 0 * (n i : ℝ) * (L i) ^ β :=
      mul_le_mul_of_nonneg_left hRpowLe (by positivity)
    exact hEvI.trans (h1.trans (by linarith))
  have hLogLe : (Nat.log 2 (n i) : ℝ) ≤ max c 0 * (L i) ^ β + 1 := by
    have hsLeN : (s : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hNSI
    have hMul : (Nat.log 2 (n i) : ℝ) * (n i : ℝ) ≤ (max c 0 * (L i) ^ β + 1) * (n i : ℝ) := by
      linarith
    exact le_of_mul_le_mul_right hMul hnPos
  have hPowBound : (n i : ℝ) + 16 < (2 : ℝ) ^ (Nat.log 2 (n i) + 2) := by
    have hNatLt : n i < 2 ^ (Nat.log 2 (n i) + 1) :=
      Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n i)
    have hNat2 : n i + 16 < 2 ^ (Nat.log 2 (n i) + 2) := by
      rw [Nat.pow_succ]
      omega
    exact_mod_cast hNat2
  have hLLe : L i ≤ ((Nat.log 2 (n i) : ℝ) + 2) * Real.log 2 := by
    have hPosL : 0 < (n i : ℝ) + 16 := by positivity
    simpa [L, Real.log_pow] using Real.log_le_log hPosL hPowBound.le
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPowGe1 : 1 ≤ (L i) ^ β := Real.one_le_rpow hL1I hβNonneg
  have hPowPos : 0 < (L i) ^ β := lt_of_lt_of_le (by norm_num) hPowGe1
  have hLUpper : L i ≤ K * (L i) ^ β := by
    calc
      L i ≤ ((Nat.log 2 (n i) : ℝ) + 2) * Real.log 2 := hLLe
      _ ≤ (max c 0 * (L i) ^ β + 3) * Real.log 2 := by nlinarith
      _ ≤ (max c 0 * (L i) ^ β + 3 * (L i) ^ β) * Real.log 2 := by nlinarith
      _ = K * (L i) ^ β := by dsimp [K]; ring
  have hLSplit : L i = (L i) ^ (1 - β) * (L i) ^ β := by
    have hPos : 0 < L i := by linarith
    rw [← Real.rpow_add hPos, sub_add_cancel, Real.rpow_one]
  conv_lhs at hLUpper => rw [hLSplit]
  have hFinal : (L i) ^ (1 - β) ≤ K := le_of_mul_le_mul_right hLUpper hPowPos
  linarith

/-- **`DeepSkipChain` Compresses to Linear Variables Under `valiantCSPCertificate`**: at
`D = (k + 1) * (Nat.log 2 (k + 1) + s)` (`s ≥ 1`), cutting `1` bit (`kBit = Nat.log 2 D + 1`)
achieves `vars ≤ (2 * s + 3) * (k + 1) + 1` (linear in `n`). -/
theorem source_valiant_linear_vars (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let kBit := Nat.log 2 D + 1
    have hD : ∀ u : Fin (source k D s).wires, wireDepth (source k D s).circuit u < 2 ^ kBit := fun u => by
      rw [source_wireDepth]
      have hu : u.val < n + D := u.isLt
      have hLt : (if u.val < k + 1 then 0 else u.val - k) ≤ D := by split_ifs <;> omega
      exact lt_of_le_of_lt hLt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) D)
    (valiantCSPCertificate (source k D s) kBit 1 (Nat.succ_pos _) (Nat.succ_pos _) hD).vars ≤
      (2 * s + 3) * n + 1 := by
  intro n D kBit hD
  have hV := valiantCSPCertificate_vars_le (source k D s) kBit 1 (Nat.succ_pos _)
    (Nat.succ_pos _) hD
  rw [source_binaryGateCount] at hV
  have hnLeD : n ≤ D := by
    have h1 : 1 ≤ Nat.log 2 n + s := by omega
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (Nat.log 2 n + s) := Nat.mul_le_mul_left n h1
  have hLogMono : Nat.log 2 n ≤ Nat.log 2 D := Nat.log_mono_right hnLeD
  have hkGe : Nat.log 2 n + 1 ≤ kBit := Nat.add_le_add_right hLogMono 1
  have hDivLe : 2 * D / kBit ≤ 2 * (s + 1) * n := by
    refine Nat.div_le_of_le_mul ?_
    have hMul1 : 2 * D = 2 * n * (Nat.log 2 n + s) := by dsimp [D]; ring
    have hMul2 : 2 * n * (Nat.log 2 n + s) ≤ 2 * n * kBit + 2 * n * s := by nlinarith
    have hMul3 : 2 * n * s ≤ 2 * n * s * kBit := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    nlinarith
  rw [Nat.mul_one] at hV
  have hV' : (valiantCSPCertificate (source k D s) kBit 1 (Nat.succ_pos _) (Nat.succ_pos _) hD).vars ≤
      n + 2 * D / kBit + 1 := hV
  have hLin : n + 2 * (s + 1) * n + 1 = (2 * s + 3) * n + 1 := by ring
  omega

/-- Complete `2 ^ o(n)` log-time variable scaling theorem for `DeepSkipChain` via
`valiantCSPCertificate`. -/
theorem valiant_subexponential (k : Nat → Nat) (s : Nat) (hs : 1 ≤ s)
    (hk : Tendsto k atTop atTop) (C overheadDeg : ℝ) :
    let D : Nat → Nat := fun i => (k i + 1) * (Nat.log 2 (k i + 1) + s)
    let kBit : Nat → Nat := fun i => Nat.log 2 (D i) + 1
    let hDepth : ∀ i, ∀ u : Fin (source (k i) (D i) s).wires,
        wireDepth (source (k i) (D i) s).circuit u < 2 ^ (kBit i) := fun i u => by
      rw [source_wireDepth]
      have hu : u.val < (k i + 1) + D i := u.isLt
      have hLt : (if u.val < k i + 1 then 0 else u.val - k i) ≤ D i := by split_ifs <;> omega
      exact lt_of_le_of_lt hLt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (D i))
    (fun i => logTimeBudget (k i + 1)
      (valiantCSPCertificate (source (k i) (D i) s) (kBit i) 1
        (Nat.succ_pos _) (Nat.succ_pos _) (hDepth i)).vars C overheadDeg)
      =o[atTop] fun i => ((k i + 1 : Nat) : ℝ) := by
  intro D kBit hDepth
  have hnNat : Tendsto (fun i => k i + 1) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hk b
      exact ⟨M, fun i hi => by have := hM i hi; omega⟩
  exact logTimeBudget_isLittleO hnNat (fun _ => Nat.le_add_right _ _) (2 * s + 4)
    (fun i => by
      have hL := source_valiant_linear_vars (k i) s hs
      have h1 : 1 ≤ k i + 1 := Nat.succ_pos _
      exact hL.trans (by nlinarith))
    C overheadDeg

end DeepSkipChain

end PvsNP
