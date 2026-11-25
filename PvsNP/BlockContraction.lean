module

public import PvsNP.LiteralPropagation

@[expose] public section

/-!
# Bounded-Interface Block Contraction and the Bounded-Fanout Hitting-Cut Wall

Advances the algorithmic `#SAT` frontier in `PvsNP/` beyond both direct Tseitin encoding
(`CompressionTask.lean`) and literal-propagating hitting cuts (`LiteralPropagation.lean`):

1. **Bounded-interface block circuits (`BlockCircuit`, `encodeBlockGate`)**: compiles any
   `BlockCircuit inputs d (inputs + blocks)` whose nodes are arbitrary `d`-input Boolean block
   functions into an exact-counting `(d + 1)`-CNF (`BlockCircuit.encode`, `BlockCircuit.encode_width`,
   `BlockCircuit.encode_size`, `BlockCircuit.acceptingAssignmentsEquiv`).
2. **Subexponential `#(d+1)-SAT` block contraction (`block_contraction_subexponential`)**:
   conditioning/contracting a circuit family into `O(n * (log n) ^ α)` (`α < 1 / 2`)
   bounded-interface blocks of fixed interface size `d` yields a `2 ^ o(n)` deterministic exact
   `#SAT` algorithm, even when internal blocks contain arbitrarily many gates. We also record
   the fixed-width depth-contraction penalty `depth_contraction_ratio_ge`
   (`2 * (h + 1) ≤ (2 ^ h + 1) ^ 2` for `h ≥ 1`).
3. **Universal bounded-fanout obstruction (`binaryGateCount_le_unhit_add_sum_fanout`,
   `binaryGateCount_le_unhit_add_maxFanout`)**: in any circuit `c` of maximum binary fanout `Δ`,
   every wire cut `cut` leaves at least `binaryGateCount c - Δ * cut.card` unhit binary gates,
   forcing `o(n)` hitting cuts to leave `(1 - o(1))` of all gates unhit.
4. **Explicit `Θ(n^2)` max-fanout-`2` separation (`DenseChainBlocks`)**: builds a circuit family
   with `n = 2 * (k + 1)` inputs, `(k + 1) * (L + 2) + k` binary gates, and max fanout `≤ 2`,
   proving that **every** wire cut satisfies `(k + 1) * (L + 2) + k ≤ unhit + 2 * cut.card`
   while `BlockContractionCertificate` contracts the entire family (for any `L k`, including
   `L k = k`) to `≤ 2 * n` variables, width `≤ 3`, and `2 ^ o(n)` deterministic `#SAT` time.
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Constructive Enumeration of `Fin d → Bool` and `d`-Input Block Clauses -/

/-- Complete list of all `2 ^ d` Boolean vectors `Fin d → Bool`. -/
def allBitVecs : (d : Nat) → List (Fin d → Bool)
  | 0 => [Fin.elim0]
  | d + 1 => (allBitVecs d).map (Fin.cons false) ++ (allBitVecs d).map (Fin.cons true)

theorem length_allBitVecs (d : Nat) : (allBitVecs d).length = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [allBitVecs, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem mem_allBitVecs (d : Nat) (a : Fin d → Bool) : a ∈ allBitVecs d := by
  induction d with
  | zero =>
    simp only [allBitVecs, List.mem_singleton]
    exact funext fun i => Fin.elim0 i
  | succ d ih =>
    simp only [allBitVecs, List.mem_append, List.mem_map]
    have hTail : Fin.tail a ∈ allBitVecs d := ih (Fin.tail a)
    cases ha0 : a 0 with
    | false =>
      left
      refine ⟨Fin.tail a, hTail, funext fun i => ?_⟩
      cases i using Fin.cases with
      | zero => simp [ha0]
      | succ j => rfl
    | true =>
      right
      refine ⟨Fin.tail a, hTail, funext fun i => ?_⟩
      cases i using Fin.cases with
      | zero => simp [ha0]
      | succ j => rfl

/-- Helper appending negated literals `(args i != a i)` onto `acc`. -/
def blockRowClauseAux {v : Nat} :
    {k : Nat} → (Fin k → Fin v) → (Fin k → Bool) →
      CNF.Clause (Fin (v + 1)) → CNF.Clause (Fin (v + 1))
  | 0, _, _, acc => acc
  | k + 1, args, a, acc =>
    blockRowClauseAux (fun i : Fin k => args i.succ) (Fin.tail a)
      (acc.add (args 0).castSucc (!(a 0)))

theorem size_blockRowClauseAux {v : Nat} :
    {k : Nat} → (args : Fin k → Fin v) → (a : Fin k → Bool) →
      (acc : CNF.Clause (Fin (v + 1))) →
      (blockRowClauseAux args a acc).size ≤ acc.size + k
  | 0, _, _, acc => by simp [blockRowClauseAux]
  | k + 1, args, a, acc => by
    have ih := size_blockRowClauseAux (fun i : Fin k => args i.succ) (Fin.tail a)
      (acc.add (args 0).castSucc (!(a 0)))
    rw [CNF.Clause.size_add] at ih
    dsimp [blockRowClauseAux]
    omega

theorem eval_blockRowClauseAux {v : Nat} :
    {k : Nat} → (args : Fin k → Fin v) → (a : Fin k → Bool) →
      (acc : CNF.Clause (Fin (v + 1))) → (σ : Fin (v + 1) → Bool) →
      ((blockRowClauseAux args a acc).eval σ = true ↔
        acc.eval σ = true ∨ ∃ i : Fin k, σ (args i).castSucc ≠ a i)
  | 0, _, _, acc, σ => by
    simp [blockRowClauseAux]
  | k + 1, args, a, acc, σ => by
    have ih := eval_blockRowClauseAux (fun i : Fin k => args i.succ) (Fin.tail a)
      (acc.add (args 0).castSucc (!(a 0))) σ
    dsimp [blockRowClauseAux]
    rw [ih, CNF.Clause.eval_add, Bool.or_eq_true, beq_iff_eq]
    have hHead : (σ (args 0).castSucc = !(a 0)) ↔ σ (args 0).castSucc ≠ a 0 := by
      cases σ (args 0).castSucc <;> cases a 0 <;> decide
    constructor
    · rintro ((h0 | hAcc) | ⟨i, hi⟩)
      · exact Or.inr ⟨0, hHead.mp h0⟩
      · exact Or.inl hAcc
      · exact Or.inr ⟨i.succ, hi⟩
    · rintro (hAcc | ⟨i, hi⟩)
      · exact Or.inl (Or.inr hAcc)
      · cases i using Fin.cases with
        | zero => exact Or.inl (Or.inl (hHead.mpr hi))
        | succ j => exact Or.inr ⟨j, hi⟩

/-- Truth-table row clause enforcing `(∀ i, Fin.init σ (args i) = a i) → σ (Fin.last v) = fn a`. -/
def blockRowClause {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool)
    (a : Fin d → Bool) : CNF.Clause (Fin (v + 1)) :=
  blockRowClauseAux args a (CNF.Clause.unit (Fin.last v) (fn a))

theorem blockRowClause_size {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool)
    (a : Fin d → Bool) : (blockRowClause args fn a).size ≤ d + 1 := by
  have hAux := size_blockRowClauseAux args a (CNF.Clause.unit (Fin.last v) (fn a))
  have hUnit : (CNF.Clause.unit (Fin.last v) (fn a)).size = 1 := by
    simp [CNF.Clause.unit_def]
  rw [hUnit] at hAux
  change (blockRowClauseAux args a (CNF.Clause.unit (Fin.last v) (fn a))).size ≤ d + 1
  omega

theorem eval_blockRowClause {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool)
    (a : Fin d → Bool) (σ : Fin (v + 1) → Bool) :
    (blockRowClause args fn a).eval σ = true ↔
      (σ (Fin.last v) = fn a ∨ ∃ i : Fin d, Fin.init σ (args i) ≠ a i) := by
  rw [blockRowClause, eval_blockRowClauseAux, CNF.Clause.eval_unit, beq_iff_eq]
  rfl

/-! ### 2. Exact `d`-Input Block Gate Encoding & `BlockCircuit` -/

/-- Exact truth-table CNF encoding `Fin.last v = fn (fun i => Fin.init σ (args i))`
using `2 ^ d` clauses of width `≤ d + 1` and zero extra variables. -/
def encodeBlockGate {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool) :
    CNF (Fin (v + 1)) :=
  (allBitVecs d).foldl (fun cnf a => cnf.add (blockRowClause args fn a)) CNF.empty

private theorem clauses_size_foldl_add {α ι : Type} (f : ι → CNF.Clause α)
    (xs : List ι) (init : CNF α) :
    (xs.foldl (fun cnf a => cnf.add (f a)) init).clauses.size = init.clauses.size + xs.length := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (init.add (f x))]
    simp only [CNF.add, Array.size_push]
    omega

private theorem mem_clauses_foldl_add {α ι : Type} (f : ι → CNF.Clause α)
    (xs : List ι) (init : CNF α) (cl : CNF.Clause α) :
    cl ∈ (xs.foldl (fun cnf a => cnf.add (f a)) init).clauses ↔
      cl ∈ init.clauses ∨ ∃ a ∈ xs, cl = f a := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (init.add (f x))]
    simp only [CNF.add, Array.mem_push, List.mem_cons]
    constructor
    · rintro ((hInit | rfl) | ⟨a, ha, rfl⟩)
      · exact Or.inl hInit
      · exact Or.inr ⟨x, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨a, Or.inr ha, rfl⟩
    · rintro (hInit | ⟨a, rfl | ha, rfl⟩)
      · exact Or.inl (Or.inl hInit)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨a, ha, rfl⟩

private theorem eval_foldl_add {α ι : Type} (f : ι → CNF.Clause α)
    (xs : List ι) (init : CNF α) (σ : α → Bool) :
    (xs.foldl (fun cnf a => cnf.add (f a)) init).eval σ = true ↔
      init.eval σ = true ∧ ∀ a ∈ xs, (f a).eval σ = true := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (init.add (f x)), CNF.eval_add, Bool.and_eq_true, List.forall_mem_cons]
    constructor
    · rintro ⟨⟨hx, hInit⟩, hXs⟩
      exact ⟨hInit, hx, hXs⟩
    · rintro ⟨hInit, hx, hXs⟩
      exact ⟨⟨hx, hInit⟩, hXs⟩

theorem encodeBlockGate_size {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool) :
    (encodeBlockGate args fn).clauses.size = 2 ^ d := by
  rw [encodeBlockGate, clauses_size_foldl_add, length_allBitVecs]
  simp [CNF.empty]

theorem encodeBlockGate_width {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool)
    {cl : CNF.Clause (Fin (v + 1))} (h : cl ∈ (encodeBlockGate args fn).clauses) :
    cl.size ≤ d + 1 := by
  rw [encodeBlockGate, mem_clauses_foldl_add] at h
  rcases h with hEmpty | ⟨a, -, rfl⟩
  · simp [CNF.empty] at hEmpty
  · exact blockRowClause_size args fn a

theorem eval_encodeBlockGate {v d : Nat} (args : Fin d → Fin v) (fn : (Fin d → Bool) → Bool)
    (σ : Fin (v + 1) → Bool) :
    (encodeBlockGate args fn).eval σ = true ↔
      σ (Fin.last v) = fn (fun i => Fin.init σ (args i)) := by
  rw [encodeBlockGate, eval_foldl_add]
  have hEmpty : (CNF.empty : CNF (Fin (v + 1))).eval σ = true := by simp
  constructor
  · rintro ⟨-, hAll⟩
    have hRow := (eval_blockRowClause args fn (fun i => Fin.init σ (args i)) σ).mp
      (hAll _ (mem_allBitVecs d _))
    rcases hRow with hEq | ⟨i, hi⟩
    · exact hEq
    · exact False.elim (hi rfl)
  · intro hOut
    refine ⟨hEmpty, fun a _ => (eval_blockRowClause args fn a σ).mpr ?_⟩
    by_cases hMatch : (fun i => Fin.init σ (args i)) = a
    · left; rw [← hMatch, hOut]
    · right
      by_contra hAll
      push Not at hAll
      exact hMatch (funext hAll)

/-- DAG circuit whose internal nodes are arbitrary `d`-input Boolean block gates. -/
inductive BlockCircuit (inputs d : Nat) : Nat → Type where
  | inputsOnly : BlockCircuit inputs d inputs
  | snoc {w : Nat} (earlier : BlockCircuit inputs d w)
      (args : Fin d → Fin w) (fn : (Fin d → Bool) → Bool) : BlockCircuit inputs d (w + 1)

namespace BlockCircuit

variable {inputs d wires : Nat}

def blockCount : {w : Nat} → BlockCircuit inputs d w → Nat
  | _, .inputsOnly => 0
  | _, .snoc earlier _ _ => earlier.blockCount + 1

theorem wire_count (bc : BlockCircuit inputs d wires) : wires = inputs + bc.blockCount := by
  induction bc with
  | inputsOnly => simp [blockCount]
  | snoc earlier _ _ ih => simpa [blockCount, ← Nat.add_assoc] using ih

def evalWires : {w : Nat} → BlockCircuit inputs d w → (Fin inputs → Bool) → (Fin w → Bool)
  | _, .inputsOnly, input => input
  | _, .snoc earlier args fn, input =>
    let vals := earlier.evalWires input
    Fin.snoc vals (fn (fun i => vals (args i)))

def restrictInputs : {w : Nat} → BlockCircuit inputs d w → (Fin w → Bool) → (Fin inputs → Bool)
  | _, .inputsOnly, vals => vals
  | _, .snoc earlier _ _, vals => earlier.restrictInputs (Fin.init vals)

@[simp] theorem restrictInputs_evalWires (bc : BlockCircuit inputs d wires)
    (input : Fin inputs → Bool) :
    bc.restrictInputs (bc.evalWires input) = input := by
  induction bc with
  | inputsOnly => rfl
  | snoc earlier _ _ ih => simpa [restrictInputs, evalWires] using ih

def blockConstraints : {w : Nat} → BlockCircuit inputs d w → CNF (Fin w)
  | _, .inputsOnly => .empty
  | _, .snoc earlier args fn =>
    earlier.blockConstraints.relabel Fin.castSucc ++ encodeBlockGate args fn

theorem eval_blockConstraints_iff (bc : BlockCircuit inputs d wires) (vals : Fin wires → Bool) :
    bc.blockConstraints.eval vals = true ↔
      bc.evalWires (bc.restrictInputs vals) = vals := by
  induction bc with
  | inputsOnly => simp [blockConstraints, evalWires, restrictInputs]
  | snoc earlier args fn ih =>
    rw [blockConstraints, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel, eval_encodeBlockGate]
    rw [show vals ∘ Fin.castSucc = Fin.init vals from rfl, ih]
    constructor
    · rintro ⟨hPrefix, hLast⟩
      simp [evalWires, restrictInputs, hPrefix, ← hLast]
    · intro h
      have hPrefix := congrArg Fin.init h
      simp only [evalWires, restrictInputs, Fin.init_snoc] at hPrefix
      refine ⟨hPrefix, ?_⟩
      have hLast := congrFun h (Fin.last _)
      simpa [evalWires, restrictInputs, hPrefix] using hLast.symm

/-- Encode `bc` together with `output = true` as a CNF over `Fin wires`. -/
def encode (bc : BlockCircuit inputs d wires) (output : Fin wires) : CNF (Fin wires) :=
  bc.blockConstraints.add (CNF.Clause.unit output true)

theorem eval_encode_iff (bc : BlockCircuit inputs d wires) (output : Fin wires)
    (vals : Fin wires → Bool) :
    (bc.encode output).eval vals = true ↔
      bc.evalWires (bc.restrictInputs vals) = vals ∧ vals output = true := by
  simp [encode, eval_blockConstraints_iff, and_comm]

/-- Exact bijection between satisfying CNF assignments and accepting inputs of `bc`. -/
def acceptingAssignmentsEquiv (bc : BlockCircuit inputs d wires) (output : Fin wires) :
    Models (bc.encode output) ≃
      { input : Fin inputs → Bool // bc.evalWires input output = true } where
  toFun vals := ⟨bc.restrictInputs vals.val, by
    obtain ⟨hEval, hOut⟩ := (eval_encode_iff bc output vals.val).mp vals.property
    rw [hEval]
    exact hOut⟩
  invFun input := ⟨bc.evalWires input.val, (eval_encode_iff bc output _).mpr
    ⟨by rw [restrictInputs_evalWires], input.property⟩⟩
  left_inv vals := Subtype.ext ((eval_encode_iff bc output vals.val).mp vals.property).1
  right_inv input := Subtype.ext (bc.restrictInputs_evalWires input.val)

theorem blockConstraints_size (bc : BlockCircuit inputs d wires) :
    bc.blockConstraints.clauses.size = bc.blockCount * 2 ^ d := by
  induction bc with
  | inputsOnly =>
    rw [blockConstraints, blockCount, Nat.zero_mul]
    rfl
  | snoc earlier args fn ih =>
    simp only [blockConstraints, CNF.Internal.clauses_append, CNF.relabel, Array.size_append,
      Array.size_map, ih, encodeBlockGate_size, blockCount]
    ring

theorem encode_size (bc : BlockCircuit inputs d wires) (output : Fin wires) :
    (bc.encode output).clauses.size = bc.blockCount * 2 ^ d + 1 := by
  simp [encode, CNF.add, blockConstraints_size]

theorem blockConstraints_width (bc : BlockCircuit inputs d wires)
    {cl : CNF.Clause (Fin wires)} (h : cl ∈ bc.blockConstraints.clauses) :
    cl.size ≤ d + 1 := by
  induction bc with
  | inputsOnly =>
    rw [blockConstraints, show (CNF.empty : CNF (Fin inputs)).clauses = #[] from rfl] at h
    simp at h
  | snoc earlier args fn ih =>
    simp only [blockConstraints, CNF.Internal.clauses_append, Array.mem_append, CNF.relabel,
      Array.mem_map] at h
    rcases h with ⟨prior, hPrior, rfl⟩ | hGate
    · simpa [CNF.Clause.relabel, CNF.Clause.Internal.size_eq_size_atoms] using ih hPrior
    · exact encodeBlockGate_width args fn hGate

theorem encode_width (bc : BlockCircuit inputs d wires) (output : Fin wires)
    {cl : CNF.Clause (Fin wires)} (h : cl ∈ (bc.encode output).clauses) :
    cl.size ≤ d + 1 := by
  simp only [encode, CNF.add, Array.mem_push] at h
  rcases h with hGate | rfl
  · exact bc.blockConstraints_width hGate
  · simp [CNF.Clause.unit_def]

end BlockCircuit

/-! ### 3. Block-Contraction Certificates, Subexponential `#(d+1)-SAT`, and Depth Penalty -/

/-- Exact contraction of `source` into a `d`-interface `BlockCircuit` with `blocks` blocks. -/
structure BlockContractionCertificate {n : Nat} (source : CircuitInstance n) (d : Nat) where
  blocks : Nat
  bc : BlockCircuit n d (n + blocks)
  output : Fin (n + blocks)
  eval_eq : ∀ input, bc.evalWires input output = source.eval input

namespace BlockContractionCertificate

def cnf {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d) : CNF (Fin (n + cert.blocks)) :=
  cert.bc.encode cert.output

def modelsEquiv {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d) :
    Models cert.cnf ≃ source.Accepting :=
  (cert.bc.acceptingAssignmentsEquiv cert.output).trans
    (Equiv.subtypeEquivRight fun input => by rw [cert.eval_eq])

theorem exact_count {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d) :
    Nat.card (Models cert.cnf) = Nat.card source.Accepting :=
  Nat.card_congr cert.modelsEquiv

theorem canonical_count {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d) :
    Nat.card (CanonicalModels (canonicalize cert.cnf)) = Nat.card source.Accepting :=
  Nat.card_congr ((canonicalModelsEquiv cert.cnf).trans cert.modelsEquiv)

theorem clause_count {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d) :
    cert.cnf.clauses.size ≤ cert.blocks * 2 ^ d + 1 := by
  have hBlocks : cert.bc.blockCount = cert.blocks := by
    have hw := cert.bc.wire_count
    omega
  rw [cnf, cert.bc.encode_size, hBlocks]

theorem width {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d)
    {cl : CNF.Clause (Fin (n + cert.blocks))} (h : cl ∈ cert.cnf.clauses) :
    cl.size ≤ d + 1 :=
  cert.bc.encode_width cert.output h

theorem canonical_width {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d)
    (cl : Finset (Fin (n + cert.blocks) × Bool))
    (h : cl ∈ canonicalize cert.cnf) :
    cl.card ≤ d + 1 :=
  canonicalize_width cert.cnf (fun _ hc => cert.width hc) cl h

theorem sat_iff {n d : Nat} {source : CircuitInstance n}
    (cert : BlockContractionCertificate source d) :
    (∃ input, source.eval input = true) ↔
      ∃ σ : Fin (n + cert.blocks) → Bool, cert.cnf.eval σ = true := by
  constructor
  · rintro ⟨input, hIn⟩
    obtain ⟨σ, hSat⟩ := cert.modelsEquiv.symm ⟨input, hIn⟩
    exact ⟨σ, hSat⟩
  · rintro ⟨σ, hSat⟩
    obtain ⟨input, hIn⟩ := cert.modelsEquiv ⟨σ, hSat⟩
    exact ⟨input, hIn⟩

end BlockContractionCertificate

/-- Any circuit family contracting into `O(n * (log n) ^ α)` (`α < 1 / 2`) blocks of fixed
interface size `d` yields a `2 ^ o(n)` exact `#SAT` log-time budget under the fixed-width
`#(d + 1)-SAT` counter, with no restriction on internal gate counts. -/
theorem block_contraction_subexponential {n : Nat → Nat} {d : Nat}
    (source : (i : Nat) → CircuitInstance (n i))
    (cert : (i : Nat) → BlockContractionCertificate (source i) d)
    (hn : Tendsto n atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hBlocks : ∀ᶠ i in atTop,
      ((cert i).blocks : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C overheadDeg : ℝ) :
    (fun i => logTimeBudget (n i) (n i + (cert i).blocks) C overheadDeg) =o[atTop]
      fun i => (n i : ℝ) := by
  let β : ℝ := max α 0
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  apply logTimeBudget_isLittleO_of_rpow_log hn (fun i => Nat.le_add_right _ _)
    (show 0 ≤ c + 1 by linarith) (max_lt hα (by norm_num) : β < 1 / 2)
  filter_upwards [hBlocks, hLogN.eventually_ge_atTop 1] with i hB hLN1
  have hRpowGe1 : 1 ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
    Real.one_le_rpow hLN1 (le_max_right α 0)
  have hRpowLe : (Real.log ((n i : ℝ) + 16)) ^ α ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left α 0)
  have hBBound : ((cert i).blocks : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β :=
    hB.trans (mul_le_mul_of_nonneg_left hRpowLe (by positivity))
  have hNBound : (n i : ℝ) ≤ 1 * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by nlinarith
  push_cast
  linarith

/-- Quantitative width-explosion barrier for naive tree contraction: collapsing a depth-`h`
tree of arity-2 gates without keeping internal narrow interfaces turns width `3` into
`2 ^ h + 1`, scaling the fixed-width counter's `k ^ 2` factor from `O(h)` to `Ω(4 ^ h)`. -/
theorem depth_contraction_ratio_ge (h : Nat) (hh : 1 ≤ h) :
    2 * (h + 1) ≤ (2 ^ h + 1) ^ 2 := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih =>
    have hPow : 2 ≤ 2 ^ h := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hh
    have hSq : (2 ^ (h + 1) + 1) ^ 2 = (2 * 2 ^ h + 1) ^ 2 := by
      rw [pow_succ]; ring
    rw [hSq]
    nlinarith

/-! ### 4. Universal Bounded-Fanout Obstruction to Hitting-Cut Reader Elimination -/

/-- Number of binary (`AND`/`OR`) gates in `c` that directly read wire `u`. -/
def binaryFanout {n : Nat} : {w : Nat} → Circuit n w → Fin w → Nat
  | _, .inputsOnly, _ => 0
  | _, .snoc earlier (.not _), u => Fin.lastCases 0 (fun q => binaryFanout earlier q) u
  | _, .snoc earlier (.and a b), u =>
    Fin.lastCases 0 (fun q => binaryFanout earlier q + if q = a ∨ q = b then 1 else 0) u
  | _, .snoc earlier (.or a b), u =>
    Fin.lastCases 0 (fun q => binaryFanout earlier q + if q = a ∨ q = b then 1 else 0) u

@[simp] theorem binaryFanout_snoc_and_last {n w : Nat} (c : Circuit n w) (a b : Fin w) :
    binaryFanout (c.snoc (.and a b)) (Fin.last w) = 0 := by
  simp [binaryFanout]

@[simp] theorem binaryFanout_snoc_and_castSucc {n w : Nat} (c : Circuit n w) (a b q : Fin w) :
    binaryFanout (c.snoc (.and a b)) q.castSucc =
      binaryFanout c q + if q = a ∨ q = b then 1 else 0 := by
  simp [binaryFanout]

@[simp] theorem binaryFanout_snoc_or_last {n w : Nat} (c : Circuit n w) (a b : Fin w) :
    binaryFanout (c.snoc (.or a b)) (Fin.last w) = 0 := by
  simp [binaryFanout]

@[simp] theorem binaryFanout_snoc_or_castSucc {n w : Nat} (c : Circuit n w) (a b q : Fin w) :
    binaryFanout (c.snoc (.or a b)) q.castSucc =
      binaryFanout c q + if q = a ∨ q = b then 1 else 0 := by
  simp [binaryFanout]

private theorem sum_filter_lastCases {w : Nat} (f : Fin w → Nat) (cut : Finset (Fin (w + 1))) :
    ∑ u ∈ cut, Fin.lastCases 0 f u =
      ∑ q ∈ Finset.univ.filter (fun q : Fin w => q.castSucc ∈ cut), f q := by
  classical
  let cut' := Finset.univ.filter (fun q : Fin w => q.castSucc ∈ cut)
  have hCastInj : Function.Injective (Fin.castSucc : Fin w → Fin (w + 1)) :=
    Fin.castSucc_injective w
  have hImg : cut'.image Fin.castSucc = cut.erase (Fin.last w) := by
    ext u
    simp only [cut', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Fin.castSucc_lt_last q |>.ne, hq⟩
    · rintro ⟨hne, hu⟩
      cases u using Fin.lastCases with
      | last => exact absurd rfl hne
      | cast q => exact ⟨q, hu, rfl⟩
  have hSumImg : ∑ u ∈ cut.erase (Fin.last w), Fin.lastCases 0 f u = ∑ q ∈ cut', f q := by
    rw [← hImg, Finset.sum_image (fun x _ y _ h => hCastInj h)]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Fin.lastCases_castSucc]
  by_cases hLast : Fin.last w ∈ cut
  · rw [← Finset.add_sum_erase cut (Fin.lastCases 0 f) hLast, Fin.lastCases_last, Nat.zero_add,
      hSumImg]
  · conv_lhs => rw [← Finset.erase_eq_of_notMem hLast, hSumImg]

/-- **Universal Bounded-Fanout Obstruction**: every wire cut `cut` leaves all but at most
`∑ u ∈ cut, binaryFanout c u` binary gates unhit. -/
theorem binaryGateCount_le_unhit_add_sum_fanout {n w : Nat} (c : Circuit n w)
    (cut : Finset (Fin w)) :
    binaryGateCount c ≤ unhitBinaryGatesOnCut c cut + ∑ u ∈ cut, binaryFanout c u := by
  induction c with
  | inputsOnly =>
    simp [binaryGateCount, unhitBinaryGates, unhitBinaryGatesOnCut, binaryFanout]
  | snoc earlier g ih =>
    let cut' : Finset (Fin _) := Finset.univ.filter fun q => q.castSucc ∈ cut
    have ih' := ih cut'
    cases g with
    | not a =>
      have hCount : binaryGateCount (earlier.snoc (.not a)) = binaryGateCount earlier := by
        dsimp [binaryGateCount, unhitBinaryGates]; rfl
      have hUnhit : unhitBinaryGatesOnCut (earlier.snoc (.not a)) cut =
          unhitBinaryGatesOnCut earlier cut' := rfl
      have hSum : ∑ u ∈ cut, binaryFanout (earlier.snoc (.not a)) u =
          ∑ q ∈ cut', binaryFanout earlier q := by
        simpa [binaryFanout] using sum_filter_lastCases (binaryFanout earlier) cut
      omega
    | and a b =>
      have hCount : binaryGateCount (earlier.snoc (.and a b)) = binaryGateCount earlier + 1 := by
        dsimp [binaryGateCount, unhitBinaryGates]; rfl
      have hUnhit : unhitBinaryGatesOnCut (earlier.snoc (.and a b)) cut =
          unhitBinaryGatesOnCut earlier cut' +
            if a.castSucc ∈ cut ∨ b.castSucc ∈ cut then 0 else 1 := rfl
      have hSum : ∑ u ∈ cut, binaryFanout (earlier.snoc (.and a b)) u =
          ∑ q ∈ cut', (binaryFanout earlier q + if q = a ∨ q = b then 1 else 0) := by
        simpa [binaryFanout] using sum_filter_lastCases
          (fun q => binaryFanout earlier q + if q = a ∨ q = b then 1 else 0) cut
      rw [hSum, Finset.sum_add_distrib] at *
      by_cases hHit : a.castSucc ∈ cut ∨ b.castSucc ∈ cut
      · have hPos : 1 ≤ ∑ q ∈ cut', (if q = a ∨ q = b then 1 else 0) := by
          rcases hHit with ha | hb
          · have ha' : a ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
            calc 1 = (if a = a ∨ a = b then 1 else 0) := by simp
              _ ≤ ∑ q ∈ cut', (if q = a ∨ q = b then 1 else 0) :=
                Finset.single_le_sum (f := fun q => if q = a ∨ q = b then 1 else 0)
                  (fun _ _ => Nat.zero_le _) ha'
          · have hb' : b ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
            calc 1 = (if b = a ∨ b = b then 1 else 0) := by simp
              _ ≤ ∑ q ∈ cut', (if q = a ∨ q = b then 1 else 0) :=
                Finset.single_le_sum (f := fun q => if q = a ∨ q = b then 1 else 0)
                  (fun _ _ => Nat.zero_le _) hb'
        rw [hCount, hUnhit, ite_eq_left_iff.mpr (fun h => absurd hHit h)]
        omega
      · rw [hCount, hUnhit, ite_eq_right_iff.mpr (fun h => absurd h hHit)]
        omega
    | or a b =>
      have hCount : binaryGateCount (earlier.snoc (.or a b)) = binaryGateCount earlier + 1 := by
        dsimp [binaryGateCount, unhitBinaryGates]; rfl
      have hUnhit : unhitBinaryGatesOnCut (earlier.snoc (.or a b)) cut =
          unhitBinaryGatesOnCut earlier cut' +
            if a.castSucc ∈ cut ∨ b.castSucc ∈ cut then 0 else 1 := rfl
      have hSum : ∑ u ∈ cut, binaryFanout (earlier.snoc (.or a b)) u =
          ∑ q ∈ cut', (binaryFanout earlier q + if q = a ∨ q = b then 1 else 0) := by
        simpa [binaryFanout] using sum_filter_lastCases
          (fun q => binaryFanout earlier q + if q = a ∨ q = b then 1 else 0) cut
      rw [hSum, Finset.sum_add_distrib] at *
      by_cases hHit : a.castSucc ∈ cut ∨ b.castSucc ∈ cut
      · have hPos : 1 ≤ ∑ q ∈ cut', (if q = a ∨ q = b then 1 else 0) := by
          rcases hHit with ha | hb
          · have ha' : a ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
            calc 1 = (if a = a ∨ a = b then 1 else 0) := by simp
              _ ≤ ∑ q ∈ cut', (if q = a ∨ q = b then 1 else 0) :=
                Finset.single_le_sum (f := fun q => if q = a ∨ q = b then 1 else 0)
                  (fun _ _ => Nat.zero_le _) ha'
          · have hb' : b ∈ cut' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
            calc 1 = (if b = a ∨ b = b then 1 else 0) := by simp
              _ ≤ ∑ q ∈ cut', (if q = a ∨ q = b then 1 else 0) :=
                Finset.single_le_sum (f := fun q => if q = a ∨ q = b then 1 else 0)
                  (fun _ _ => Nat.zero_le _) hb'
        rw [hCount, hUnhit, ite_eq_left_iff.mpr (fun h => absurd hHit h)]
        omega
      · rw [hCount, hUnhit, ite_eq_right_iff.mpr (fun h => absurd h hHit)]
        omega

/-- If every wire in `c` has binary fanout `≤ Δ`, any cut of size `k` hits at most `Δ * k`
binary gates. -/
theorem binaryGateCount_le_unhit_add_maxFanout {n w : Nat} (c : Circuit n w) (Δ : Nat)
    (hMax : ∀ u, binaryFanout c u ≤ Δ) (cut : Finset (Fin w)) :
    binaryGateCount c ≤ unhitBinaryGatesOnCut c cut + Δ * cut.card := by
  have hBase := binaryGateCount_le_unhit_add_sum_fanout c cut
  have hSum : ∑ u ∈ cut, binaryFanout c u ≤ Δ * cut.card := by
    calc ∑ u ∈ cut, binaryFanout c u ≤ ∑ _ ∈ cut, Δ := Finset.sum_le_sum fun u _ => hMax u
      _ = Δ * cut.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-! ### 5. Explicit `Θ(n^2)` Max-Fanout-`2` Separation Family (`DenseChainBlocks`) -/

namespace DenseChainBlocks

/-- Alternating `AND`/`OR` step in a 2-wire cascade block. -/
def chainStep (t : Nat) (p1 p0 : Bool) : Bool :=
  if t % 2 = 0 then p1 && p0 else p1 || p0

/-- Pure 2-input Boolean function of an `(L + 2)`-gate block (`g_0 = a ∧ b`,
`g_1 = (a ∧ b) ∨ a`, followed by `L` alternating steps). -/
def chainPair : Nat → Bool → Bool → Bool × Bool
  | 0, a, b => ((a && b) || a, a && b)
  | t + 1, a, b =>
    let p := chainPair t a b
    (chainStep t p.1 p.2, p.1)

def chainOut (L : Nat) (a b : Bool) : Bool :=
  (chainPair L a b).1

def runCascade : Nat → Bool → Bool → Bool × Bool
  | 0, p1, p0 => (p1, p0)
  | t + 1, p1, p0 =>
    let q := runCascade t p1 p0
    (chainStep t q.1 q.2, q.1)

theorem runCascade_pair (L : Nat) (a b : Bool) :
    runCascade L ((a && b) || a) (a && b) = chainPair L a b := by
  induction L with
  | zero => rfl
  | succ t ih => simp [runCascade, chainPair, ih]

/-- Single cascade gate reading the last two wires of `Fin (w + (t + 2))`. -/
def cascadeGate (t w : Nat) : Gate (w + (t + 2)) :=
  let p1 : Fin (w + (t + 2)) := Fin.last (w + (t + 1))
  let p0 : Fin (w + (t + 2)) := (Fin.last (w + t)).castSucc
  if t % 2 = 0 then .and p1 p0 else .or p1 p0

/-- Appends `t` alternating `AND`/`OR` cascade gates, each reading the two latest wires. -/
def appendCascade {inputs : Nat} :
    (t : Nat) → {w : Nat} → Circuit inputs (w + 2) → Circuit inputs (w + (t + 2))
  | 0, _, c => c
  | t + 1, w, c => (appendCascade t c).snoc (cascadeGate t w)

/-- Appends one `(L + 2)`-gate cascade block reading wires `u` and `v`. -/
def appendChainBlock {inputs w : Nat} (c : Circuit inputs w) (u v : Fin w) (L : Nat) :
    Circuit inputs (w + (L + 2)) :=
  appendCascade L ((c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc))

theorem binaryGateCount_appendCascade {inputs : Nat} (t : Nat) {w : Nat}
    (c : Circuit inputs (w + 2)) :
    binaryGateCount (appendCascade t c) = binaryGateCount c + t := by
  induction t with
  | zero => simp [appendCascade]
  | succ t ih =>
    dsimp [appendCascade]
    unfold cascadeGate
    split_ifs <;>
      · simp only [binaryGateCount, unhitBinaryGates]
        change unhitBinaryGates (appendCascade t c) (fun _ => none) + 1 =
          binaryGateCount c + (t + 1)
        change binaryGateCount (appendCascade t c) + 1 = binaryGateCount c + (t + 1)
        omega

theorem binaryGateCount_appendChainBlock {inputs w : Nat} (c : Circuit inputs w)
    (u v : Fin w) (L : Nat) :
    binaryGateCount (appendChainBlock c u v L) = binaryGateCount c + (L + 2) := by
  rw [appendChainBlock, binaryGateCount_appendCascade]
  simp only [binaryGateCount, unhitBinaryGates]
  change unhitBinaryGates c (fun _ => none) + 1 + 1 + L =
    unhitBinaryGates c (fun _ => none) + (L + 2)
  omega

theorem evalWires_appendCascade {inputs : Nat} (t : Nat) {w : Nat}
    (c : Circuit inputs (w + 2)) (x : Fin inputs → Bool) :
    (∀ q : Fin (w + 2),
      (appendCascade t c).evalWires x (Fin.castLE (by omega) q) = c.evalWires x q) ∧
    ((appendCascade t c).evalWires x (Fin.last (w + (t + 1))),
     (appendCascade t c).evalWires x (Fin.last (w + t)).castSucc) =
      runCascade t (c.evalWires x (Fin.last (w + 1))) (c.evalWires x (Fin.last w).castSucc) := by
  induction t with
  | zero =>
    refine ⟨fun q => rfl, ?_⟩
    rfl
  | succ t ih =>
    rcases ih with ⟨hOld, hPair⟩
    have hSnoc : ∀ q : Fin (w + (t + 2)),
        ((appendCascade t c).snoc (cascadeGate t w)).evalWires x q.castSucc =
          (appendCascade t c).evalWires x q := fun q => by
      simp [Circuit.evalWires, Fin.snoc_castSucc]
    refine ⟨fun q => ?_, ?_⟩
    · change ((appendCascade t c).snoc (cascadeGate t w)).evalWires x
          ((Fin.castLE (by omega) q).castSucc) = c.evalWires x q
      rw [hSnoc, hOld q]
    · change (((appendCascade t c).snoc (cascadeGate t w)).evalWires x
          (Fin.last (w + (t + 1 + 1))),
        ((appendCascade t c).snoc (cascadeGate t w)).evalWires x
          (Fin.last (w + (t + 1))).castSucc) = _
      have hLast :
          ((appendCascade t c).snoc (cascadeGate t w)).evalWires x
              (Fin.last (w + (t + 1 + 1))) =
            chainStep t
              ((appendCascade t c).evalWires x (Fin.last (w + (t + 1))))
              ((appendCascade t c).evalWires x (Fin.last (w + t)).castSucc) := by
        change ((appendCascade t c).snoc (cascadeGate t w)).evalWires x
            (Fin.last (w + (t + 2))) = _
        simp only [Circuit.evalWires, Fin.snoc_last, cascadeGate, chainStep]
        split_ifs <;> rfl
      have hPrev :
          ((appendCascade t c).snoc (cascadeGate t w)).evalWires x
              (Fin.last (w + (t + 1))).castSucc =
            (appendCascade t c).evalWires x (Fin.last (w + (t + 1))) :=
        hSnoc (Fin.last (w + (t + 1)))
      rw [hLast, hPrev]
      simp only [runCascade, Prod.mk.injEq]
      exact ⟨congrArg (fun p => chainStep t p.1 p.2) hPair, congrArg Prod.fst hPair⟩

theorem evalWires_appendChainBlock_old {inputs w : Nat} (c : Circuit inputs w)
    (u v : Fin w) (L : Nat) (x : Fin inputs → Bool) (q : Fin w) :
    (appendChainBlock c u v L).evalWires x (Fin.castLE (by omega) q) = c.evalWires x q := by
  have h1 := (evalWires_appendCascade L
    ((c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc)) x).1 q.castSucc.castSucc
  simpa [appendChainBlock, Circuit.evalWires, Fin.snoc_castSucc] using h1

theorem evalWires_appendChainBlock_last {inputs w : Nat} (c : Circuit inputs w)
    (u v : Fin w) (L : Nat) (x : Fin inputs → Bool) :
    (appendChainBlock c u v L).evalWires x (Fin.last (w + (L + 1))) =
      chainOut L (c.evalWires x u) (c.evalWires x v) := by
  have hPair := (evalWires_appendCascade L
    ((c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc)) x).2
  have h1 := congrArg Prod.fst hPair
  have hG0 : ((c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc)).evalWires x
      (Fin.last w).castSucc = (c.evalWires x u && c.evalWires x v) := by
    simp [Circuit.evalWires, Gate.eval, Fin.snoc_castSucc, Fin.snoc_last]
  have hG1 : ((c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc)).evalWires x
      (Fin.last (w + 1)) = ((c.evalWires x u && c.evalWires x v) || c.evalWires x u) := by
    simp [Circuit.evalWires, Gate.eval, Fin.snoc_castSucc, Fin.snoc_last]
  rw [hG0, hG1, runCascade_pair] at h1
  exact h1

theorem binaryFanout_appendCascade_lt {inputs : Nat} (t : Nat) {w : Nat}
    (c : Circuit inputs (w + 2)) (u : Fin (w + (t + 2))) (hu : u.val < w) :
    binaryFanout (appendCascade t c) u = binaryFanout c ⟨u.val, by omega⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    cases u using Fin.lastCases with
    | last => simp at hu
    | cast u' =>
      change binaryFanout ((appendCascade t c).snoc (cascadeGate t w)) u'.castSucc = _
      have hNe : ¬(u' = Fin.last (w + (t + 1)) ∨ u' = (Fin.last (w + t)).castSucc) := by
        simp only [Fin.val_castSucc] at hu
        rintro (rfl | rfl) <;> simp at hu
      by_cases ht : t % 2 = 0
      · simp [cascadeGate, ht, hNe, ih u' hu]
      · simp [cascadeGate, ht, hNe, ih u' hu]

theorem binaryFanout_appendCascade_ge {inputs : Nat} (t : Nat) {w : Nat}
    (c : Circuit inputs (w + 2))
    (hZero1 : binaryFanout c (Fin.last (w + 1)) = 0)
    (hLe0 : binaryFanout c (Fin.last w).castSucc ≤ 1) :
    (∀ u : Fin (w + (t + 2)), w ≤ u.val → binaryFanout (appendCascade t c) u ≤ 2) ∧
    binaryFanout (appendCascade t c) (Fin.last (w + (t + 1))) = 0 ∧
    binaryFanout (appendCascade t c) (Fin.last (w + t)).castSucc ≤ 1 := by
  induction t with
  | zero =>
    dsimp [appendCascade]
    refine ⟨fun u hu => ?_, hZero1, hLe0⟩
    have hCases : u = Fin.last (w + 1) ∨ u = (Fin.last w).castSucc := by
      have := u.isLt
      by_cases h1 : u.val = w + 1
      · left; exact Fin.ext h1
      · right; exact Fin.ext (by simp; omega)
    rcases hCases with rfl | rfl
    · omega
    · exact hLe0.trans (by omega)
  | succ t ih =>
    rcases ih with ⟨ihGe, ihLast, ihPrev⟩
    have hLast0 : binaryFanout (appendCascade (t + 1) c) (Fin.last (w + (t + 1 + 1))) = 0 := by
      change binaryFanout ((appendCascade t c).snoc (cascadeGate t w)) (Fin.last (w + (t + 2))) = 0
      unfold cascadeGate
      split_ifs
      · exact binaryFanout_snoc_and_last _ _ _
      · exact binaryFanout_snoc_or_last _ _ _
    have hPrev1 : binaryFanout (appendCascade (t + 1) c) (Fin.last (w + (t + 1))).castSucc ≤ 1 := by
      change binaryFanout ((appendCascade t c).snoc (cascadeGate t w))
        (Fin.last (w + (t + 1))).castSucc ≤ 1
      unfold cascadeGate
      split_ifs
      · rw [binaryFanout_snoc_and_castSucc, ihLast]; simp
      · rw [binaryFanout_snoc_or_castSucc, ihLast]; simp
    refine ⟨fun u hu => ?_, hLast0, hPrev1⟩
    cases u using Fin.lastCases with
    | last =>
      exact (le_of_eq hLast0).trans (by omega)
    | cast q =>
      have hStep : binaryFanout ((appendCascade t c).snoc (cascadeGate t w)) q.castSucc =
          binaryFanout (appendCascade t c) q +
            if q = Fin.last (w + (t + 1)) ∨ q = (Fin.last (w + t)).castSucc then 1 else 0 := by
        by_cases ht : t % 2 = 0
        · simp [cascadeGate, ht]
        · simp [cascadeGate, ht]
      change binaryFanout ((appendCascade t c).snoc (cascadeGate t w)) q.castSucc ≤ 2
      rw [hStep]
      by_cases hq1 : q = Fin.last (w + (t + 1))
      · rw [hq1]; simp [ihLast]
      · by_cases hq0 : q = (Fin.last (w + t)).castSucc
        · rw [hq0]; simp; omega
        · simp [hq1, hq0]
          exact ihGe q (by simpa using hu)

theorem binaryFanout_appendChainBlock_lt {inputs w : Nat} (c : Circuit inputs w)
    (u v : Fin w) (L : Nat) (huv : u ≠ v) (q : Fin (w + (L + 2))) (hq : q.val < w) :
    binaryFanout (appendChainBlock c u v L) q =
      binaryFanout c ⟨q.val, hq⟩ +
        (if ⟨q.val, hq⟩ = u then 2 else if ⟨q.val, hq⟩ = v then 1 else 0) := by
  set q0 : Fin w := ⟨q.val, hq⟩
  have h1 := binaryFanout_appendCascade_lt L
    ((c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc)) q hq
  rw [appendChainBlock, h1]
  have hq0Cast : (⟨q.val, by omega⟩ : Fin (w + 2)) = q0.castSucc.castSucc := rfl
  rw [hq0Cast, binaryFanout_snoc_or_castSucc, binaryFanout_snoc_and_castSucc]
  have hNeLast : q0.castSucc ≠ Fin.last w := (Fin.castSucc_lt_last q0).ne
  simp only [hNeLast, false_or, Fin.castSucc_inj]
  by_cases hqu : q0 = u
  · subst hqu; simp
  · by_cases hqv : q0 = v
    · subst hqv; simp [hqu]
    · simp [hqu, hqv]

theorem binaryFanout_appendChainBlock_ge {inputs w : Nat} (c : Circuit inputs w)
    (u v : Fin w) (L : Nat) :
    (∀ q : Fin (w + (L + 2)), w ≤ q.val → binaryFanout (appendChainBlock c u v L) q ≤ 2) ∧
    binaryFanout (appendChainBlock c u v L) (Fin.last (w + (L + 1))) = 0 := by
  let mid := (c.snoc (.and u v)).snoc (.or (Fin.last w) u.castSucc)
  have hZero1 : binaryFanout mid (Fin.last (w + 1)) = 0 :=
    binaryFanout_snoc_or_last _ _ _
  have hLe0 : binaryFanout mid (Fin.last w).castSucc ≤ 1 := by
    dsimp [mid]
    rw [binaryFanout_snoc_or_castSucc, binaryFanout_snoc_and_last]
    split_ifs <;> omega
  have hRes := binaryFanout_appendCascade_ge L mid hZero1 hLe0
  exact ⟨hRes.1, hRes.2.1⟩

/-- Recursive wire count after appending blocks `0 .. j`. -/
def stageWires (n L : Nat) : Nat → Nat
  | 0 => n + (L + 2)
  | j + 1 => stageWires n L j + (L + 2) + 1

theorem stageWires_eq (n L j : Nat) :
    stageWires n L j = n + (j + 1) * (L + 2) + j := by
  induction j with
  | zero => simp [stageWires]
  | succ j ih =>
    change stageWires n L j + (L + 2) + 1 = n + (j + 2) * (L + 2) + (j + 1)
    rw [ih]
    ring

theorem stageWires_pos (n L j : Nat) : 0 < stageWires n L j := by
  rw [stageWires_eq]
  have hMul : 1 ≤ (j + 1) * (L + 2) := Nat.mul_pos (Nat.succ_pos j) (by omega)
  omega

/-- Builds blocks `0 .. j` of `DenseChainBlocks`, conjoining their outputs via a chain of
`AND` accumulators. -/
def buildStage (k L : Nat) :
    (j : Nat) → j ≤ k → Circuit (2 * (k + 1)) (stageWires (2 * (k + 1)) L j)
  | 0, _ =>
    let n := 2 * (k + 1)
    let u : Fin n := ⟨0, by omega⟩
    let v : Fin n := ⟨1, by omega⟩
    appendChainBlock Circuit.inputsOnly u v L
  | j + 1, hj =>
    let n := 2 * (k + 1)
    let prev := buildStage k L j (by omega)
    let wPrev := stageWires n L j
    have hwPrev : n + 2 * (j + 1) ≤ wPrev := by
      dsimp only [wPrev]
      rw [stageWires_eq]
      have hMul : (j + 1) * 2 ≤ (j + 1) * (L + 2) := Nat.mul_le_mul_left (j + 1) (by omega)
      omega
    let u : Fin wPrev := ⟨2 * (j + 1), by omega⟩
    let v : Fin wPrev := ⟨2 * (j + 1) + 1, by omega⟩
    let mid : Circuit n (wPrev + (L + 2)) := appendChainBlock prev u v L
    let prevOut : Fin (wPrev + (L + 2)) :=
      Fin.castLE (by omega) ⟨wPrev - 1, Nat.sub_lt (stageWires_pos n L j) zero_lt_one⟩
    let newOut : Fin (wPrev + (L + 2)) := Fin.last (wPrev + (L + 1))
    mid.snoc (.and prevOut newOut)

/-- Concrete `CircuitInstance` for `DenseChainBlocks` with `n = 2 * (k + 1)` inputs and
`(k + 1) * (L + 2) + k` binary gates (all fanout `≤ 2`). -/
def source (k L : Nat) : CircuitInstance (2 * (k + 1)) where
  wires := stageWires (2 * (k + 1)) L k
  circuit := buildStage k L k (le_refl k)
  output := ⟨stageWires (2 * (k + 1)) L k - 1,
    Nat.sub_lt (stageWires_pos (2 * (k + 1)) L k) zero_lt_one⟩

/-- Pure target Boolean function computed by blocks `0 .. j`. -/
def stageTarget (k L : Nat) : (j : Nat) → j ≤ k → (Fin (2 * (k + 1)) → Bool) → Bool
  | 0, _, x => chainOut L (x ⟨0, by omega⟩) (x ⟨1, by omega⟩)
  | j + 1, hj, x =>
    stageTarget k L j (by omega) x &&
      chainOut L (x ⟨2 * (j + 1), by omega⟩) (x ⟨2 * (j + 1) + 1, by omega⟩)

@[simp] theorem binaryGateCount_snoc_and {inputs w : Nat} (c : Circuit inputs w) (a b : Fin w) :
    binaryGateCount (c.snoc (.and a b)) = binaryGateCount c + 1 := rfl

theorem binaryGateCount_buildStage (k L : Nat) :
    ∀ j (hj : j ≤ k),
      binaryGateCount (buildStage k L j hj) = (j + 1) * (L + 2) + j := by
  intro j
  induction j with
  | zero =>
    intro _
    dsimp [buildStage, stageWires]
    rw [binaryGateCount_appendChainBlock]
    simp [binaryGateCount, unhitBinaryGates]
  | succ j ih =>
    intro hj
    dsimp [buildStage, stageWires]
    rw [binaryGateCount_appendChainBlock, ih (by omega)]
    ring

theorem source_binaryGateCount (k L : Nat) :
    binaryGateCount (source k L).circuit = (k + 1) * (L + 2) + k :=
  binaryGateCount_buildStage k L k (le_refl k)

theorem source_quadratic_binaryGates (k : Nat) :
    (k + 1) ^ 2 ≤ binaryGateCount (source k k).circuit := by
  rw [source_binaryGateCount]
  nlinarith

theorem buildStage_inv (k L : Nat) :
    ∀ (j : Nat) (hj : j ≤ k),
      (∀ u : Fin (stageWires (2 * (k + 1)) L j), binaryFanout (buildStage k L j hj) u ≤ 2) ∧
      binaryFanout (buildStage k L j hj)
        ⟨stageWires (2 * (k + 1)) L j - 1,
          Nat.sub_lt (stageWires_pos (2 * (k + 1)) L j) zero_lt_one⟩ = 0 ∧
      (∀ i : Fin (2 * (k + 1)), j < i.val / 2 →
        binaryFanout (buildStage k L j hj)
          ⟨i.val, (by
            have := stageWires_pos (2 * (k + 1)) L j
            rw [stageWires_eq] at *
            have hMul : (j + 1) * 2 ≤ (j + 1) * (L + 2) := Nat.mul_le_mul_left (j + 1) (by omega)
            omega)⟩ = 0) := by
  intro j
  induction j with
  | zero =>
    intro hj0
    dsimp [buildStage]
    let u0 : Fin (2 * (k + 1)) := ⟨0, by omega⟩
    let v0 : Fin (2 * (k + 1)) := ⟨1, by omega⟩
    have huv : u0 ≠ v0 := by intro h; have := congrArg Fin.val h; simp [u0, v0] at this
    have hGe := binaryFanout_appendChainBlock_ge
      (Circuit.inputsOnly (inputs := 2 * (k + 1))) u0 v0 L
    have hLt := fun q hq => binaryFanout_appendChainBlock_lt
      (Circuit.inputsOnly (inputs := 2 * (k + 1))) u0 v0 L huv q hq
    change (∀ u : Fin (2 * (k + 1) + (L + 2)),
        binaryFanout (appendChainBlock Circuit.inputsOnly u0 v0 L) u ≤ 2) ∧
      binaryFanout (appendChainBlock Circuit.inputsOnly u0 v0 L)
        ⟨2 * (k + 1) + (L + 2) - 1, by omega⟩ = 0 ∧
      (∀ i : Fin (2 * (k + 1)), 0 < i.val / 2 →
        binaryFanout (appendChainBlock Circuit.inputsOnly u0 v0 L)
          ⟨i.val, by omega⟩ = 0)
    refine ⟨fun u => ?_, ?_, fun i hi => ?_⟩
    · by_cases hq : u.val < 2 * (k + 1)
      · rw [hLt u hq]
        simp only [binaryFanout]
        split_ifs <;> decide
      · exact hGe.1 u (by omega)
    · have hLastEq :
          (⟨2 * (k + 1) + (L + 2) - 1, by omega⟩ : Fin (2 * (k + 1) + (L + 2))) =
            Fin.last (2 * (k + 1) + (L + 1)) := by
        ext; simp
      rw [hLastEq]
      exact hGe.2
    · rw [hLt _ i.isLt]
      simp only [binaryFanout, Nat.zero_add]
      have hi2 : 2 ≤ i.val := by omega
      have hNe0 : (⟨i.val, i.isLt⟩ : Fin (2 * (k + 1))) ≠ u0 := by
        intro h
        have hv : i.val = 0 := congrArg Fin.val h
        omega
      have hNe1 : (⟨i.val, i.isLt⟩ : Fin (2 * (k + 1))) ≠ v0 := by
        intro h
        have hv : i.val = 1 := congrArg Fin.val h
        omega
      simp [hNe0, hNe1]
  | succ j ih =>
    intro hj
    obtain ⟨ihMax, ihLast0, ihFresh⟩ := ih (by omega)
    let prev := buildStage k L j (by omega)
    let wPrev := stageWires (2 * (k + 1)) L j
    have hwPrev : 2 * (k + 1) + 2 * (j + 1) ≤ wPrev := by
      dsimp only [wPrev]; rw [stageWires_eq]
      have hMul : (j + 1) * 2 ≤ (j + 1) * (L + 2) := Nat.mul_le_mul_left (j + 1) (by omega)
      omega
    let u0 : Fin wPrev := ⟨2 * (j + 1), by omega⟩
    let v0 : Fin wPrev := ⟨2 * (j + 1) + 1, by omega⟩
    let mid := appendChainBlock prev u0 v0 L
    let prevOut : Fin (wPrev + (L + 2)) :=
      Fin.castLE (by omega) ⟨wPrev - 1, Nat.sub_lt (stageWires_pos (2 * (k + 1)) L j) zero_lt_one⟩
    let newOut : Fin (wPrev + (L + 2)) := Fin.last (wPrev + (L + 1))
    have huv : u0 ≠ v0 := by
      intro h; have := congrArg Fin.val h; simp [u0, v0] at this
    have hMidGe := binaryFanout_appendChainBlock_ge prev u0 v0 L
    have hMidLt := fun q hq => binaryFanout_appendChainBlock_lt prev u0 v0 L huv q hq
    have hPrevOutLt : prevOut.val < wPrev := by
      dsimp [prevOut]
      exact Nat.sub_lt (stageWires_pos (2 * (k + 1)) L j) zero_lt_one
    have hPrevOutVal :
        (⟨prevOut.val, hPrevOutLt⟩ : Fin wPrev) =
          ⟨wPrev - 1, Nat.sub_lt (stageWires_pos (2 * (k + 1)) L j) zero_lt_one⟩ := by
      ext; rfl
    have hPrevOutNeU : (⟨prevOut.val, hPrevOutLt⟩ : Fin wPrev) ≠ u0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [u0, prevOut, Fin.val_castLE] at hv
      omega
    have hPrevOutNeV : (⟨prevOut.val, hPrevOutLt⟩ : Fin wPrev) ≠ v0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [v0, prevOut, Fin.val_castLE] at hv
      omega
    have hMidPrevOut : binaryFanout mid prevOut = 0 := by
      rw [hMidLt prevOut hPrevOutLt]
      simp only [hPrevOutNeU, hPrevOutNeV, ↓reduceIte, Nat.add_zero]
      rw [hPrevOutVal]
      exact ihLast0
    have hMidNewOut : binaryFanout mid newOut = 0 := hMidGe.2
    have hMidU0 : binaryFanout mid (Fin.castLE (by omega) u0) ≤ 2 := by
      rw [hMidLt _ u0.isLt]
      have hU0Idx : (⟨(Fin.castLE (by omega) u0 : Fin (wPrev + (L + 2))).val, u0.isLt⟩ : Fin wPrev) =
          u0 := by
        ext; rfl
      rw [hU0Idx]
      have hPrev0 : binaryFanout prev u0 = 0 := ihFresh ⟨2 * (j + 1), by omega⟩ (by simp)
      simp [hPrev0]
    have hMidV0 : binaryFanout mid (Fin.castLE (by omega) v0) ≤ 1 := by
      rw [hMidLt _ v0.isLt]
      have hV0Idx : (⟨(Fin.castLE (by omega) v0 : Fin (wPrev + (L + 2))).val, v0.isLt⟩ : Fin wPrev) =
          v0 := by
        ext; rfl
      rw [hV0Idx]
      have hPrev0 : binaryFanout prev v0 = 0 := ihFresh ⟨2 * (j + 1) + 1, by omega⟩ (by dsimp; omega)
      simp [hPrev0, huv.symm]
    change (∀ u : Fin (wPrev + (L + 2) + 1), binaryFanout (mid.snoc (.and prevOut newOut)) u ≤ 2) ∧
      binaryFanout (mid.snoc (.and prevOut newOut))
        ⟨wPrev + (L + 2) + 1 - 1, by omega⟩ = 0 ∧
      (∀ i : Fin (2 * (k + 1)), j + 1 < i.val / 2 →
        binaryFanout (mid.snoc (.and prevOut newOut)) ⟨i.val, by omega⟩ = 0)
    refine ⟨fun u => ?_, ?_, fun i hi => ?_⟩
    · cases u using Fin.lastCases with
      | last =>
        rw [binaryFanout_snoc_and_last]
        omega
      | cast q =>
        rw [binaryFanout_snoc_and_castSucc]
        by_cases hqPrev : q = prevOut
        · rw [hqPrev, ite_eq_left_iff.mpr (fun h => absurd (Or.inl rfl) h), hMidPrevOut]
          decide
        · by_cases hqNew : q = newOut
          · rw [hqNew, ite_eq_left_iff.mpr (fun h => absurd (Or.inr rfl) h), hMidNewOut]
            decide
          · rw [ite_eq_right_iff.mpr (fun h => absurd h (by push Not; exact ⟨hqPrev, hqNew⟩)),
              Nat.add_zero]
            by_cases hqLt : q.val < wPrev
            · by_cases hqu : (⟨q.val, hqLt⟩ : Fin wPrev) = u0
              · have hQEq : q = Fin.castLE (by omega) u0 :=
                  Fin.ext (show q.val = u0.val from congrArg Fin.val hqu)
                rw [hQEq]; exact hMidU0
              · by_cases hqv : (⟨q.val, hqLt⟩ : Fin wPrev) = v0
                · have hQEq : q = Fin.castLE (by omega) v0 :=
                    Fin.ext (show q.val = v0.val from congrArg Fin.val hqv)
                  rw [hQEq]; exact hMidV0.trans (by decide)
                · rw [hMidLt q hqLt]
                  simp only [hqu, hqv, ↓reduceIte, Nat.add_zero]
                  exact ihMax _
            · exact hMidGe.1 q (by omega)
    · have hLastEq : (⟨wPrev + (L + 2) + 1 - 1, by omega⟩ : Fin (wPrev + (L + 2) + 1)) =
          Fin.last (wPrev + (L + 2)) := by
        ext; simp
      rw [hLastEq]
      exact binaryFanout_snoc_and_last _ _ _
    · let qi : Fin (wPrev + (L + 2)) := ⟨i.val, by omega⟩
      have hCast : (⟨i.val, by omega⟩ : Fin (wPrev + (L + 2) + 1)) = qi.castSucc := rfl
      rw [hCast, binaryFanout_snoc_and_castSucc]
      have hNePrev : qi ≠ prevOut := by
        intro h; have := congrArg Fin.val h
        simp [qi, prevOut] at this
        omega
      have hNeNew : qi ≠ newOut := by
        intro h; have := congrArg Fin.val h
        simp [qi, newOut] at this
        omega
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by push Not; exact ⟨hNePrev, hNeNew⟩)),
        Nat.add_zero]
      have hqiLt : qi.val < wPrev := by dsimp [qi]; omega
      rw [hMidLt qi hqiLt]
      have hNeU : (⟨qi.val, hqiLt⟩ : Fin wPrev) ≠ u0 := by
        intro h; have := congrArg Fin.val h; simp [qi, u0] at this; omega
      have hNeV : (⟨qi.val, hqiLt⟩ : Fin wPrev) ≠ v0 := by
        intro h; have := congrArg Fin.val h; simp [qi, v0] at this; omega
      simp only [hNeU, hNeV, ↓reduceIte, Nat.add_zero]
      exact ihFresh i (by omega)

/-- **Maximum Fanout `≤ 2` Theorem**: every wire in `DenseChainBlocks.source k L` feeds at
most `2` binary gates. -/
theorem source_fanout_le_two (k L : Nat) :
    ∀ u : Fin (source k L).wires, binaryFanout (source k L).circuit u ≤ 2 :=
  (buildStage_inv k L k (le_refl k)).1

/-- **Hitting-Cut Obstruction on `DenseChainBlocks`**: any wire cut `cut` leaves at least
`(k + 1) * (L + 2) + k - 2 * cut.card` binary gates unhit. -/
theorem source_hitting_cut_lower (k L : Nat) (cut : Finset (Fin (source k L).wires)) :
    (k + 1) * (L + 2) + k ≤ unhitBinaryGatesOnCut (source k L).circuit cut + 2 * cut.card := by
  have h := binaryGateCount_le_unhit_add_maxFanout (source k L).circuit 2
    (source_fanout_le_two k L) cut
  rwa [source_binaryGateCount] at h

theorem evalWires_buildStage (k L : Nat) :
    ∀ (j : Nat) (hj : j ≤ k) (x : Fin (2 * (k + 1)) → Bool),
      (∀ i : Fin (2 * (k + 1)),
        (buildStage k L j hj).evalWires x
          ⟨i.val, (by
            have := stageWires_pos (2 * (k + 1)) L j
            rw [stageWires_eq] at *
            have hMul : (j + 1) * 2 ≤ (j + 1) * (L + 2) := Nat.mul_le_mul_left (j + 1) (by omega)
            omega)⟩ = x i) ∧
      (buildStage k L j hj).evalWires x
          ⟨stageWires (2 * (k + 1)) L j - 1,
            Nat.sub_lt (stageWires_pos (2 * (k + 1)) L j) zero_lt_one⟩ =
        stageTarget k L j hj x := by
  intro j
  induction j with
  | zero =>
    intro _ x
    dsimp [buildStage, stageTarget, stageWires]
    refine ⟨fun i => ?_, ?_⟩
    · have hCast : (⟨i.val, by omega⟩ : Fin (2 * (k + 1) + (L + 2))) = Fin.castLE (by omega) i :=
        Fin.ext rfl
      rw [hCast, evalWires_appendChainBlock_old]
      rfl
    · change (appendChainBlock Circuit.inputsOnly ⟨0, by omega⟩ ⟨1, by omega⟩ L).evalWires x
          ⟨2 * (k + 1) + (L + 2) - 1, by omega⟩ = _
      have hLastEq :
          (⟨2 * (k + 1) + (L + 2) - 1, by omega⟩ :
              Fin (2 * (k + 1) + (L + 2))) =
            Fin.last (2 * (k + 1) + (L + 1)) := by
        ext; simp
      rw [hLastEq, evalWires_appendChainBlock_last]
      rfl
  | succ j ih =>
    intro hj x
    obtain ⟨ihIn, ihOut⟩ := ih (by omega) x
    dsimp [buildStage, stageTarget]
    let prev := buildStage k L j (by omega)
    let wPrev := stageWires (2 * (k + 1)) L j
    have hwPrev : 2 * (k + 1) + 2 * (j + 1) ≤ wPrev := by
      dsimp only [wPrev]; rw [stageWires_eq]
      have hMul : (j + 1) * 2 ≤ (j + 1) * (L + 2) := Nat.mul_le_mul_left (j + 1) (by omega)
      omega
    let u0 : Fin wPrev := ⟨2 * (j + 1), by omega⟩
    let v0 : Fin wPrev := ⟨2 * (j + 1) + 1, by omega⟩
    let mid := appendChainBlock prev u0 v0 L
    let prevOut : Fin (wPrev + (L + 2)) :=
      Fin.castLE (by omega) ⟨wPrev - 1, Nat.sub_lt (stageWires_pos (2 * (k + 1)) L j) zero_lt_one⟩
    let newOut : Fin (wPrev + (L + 2)) := Fin.last (wPrev + (L + 1))
    refine ⟨fun i => ?_, ?_⟩
    · let qi : Fin wPrev := ⟨i.val, by omega⟩
      change (mid.snoc (.and prevOut newOut)).evalWires x
          (Fin.castLE (by omega) qi).castSucc = x i
      rw [Circuit.evalWires, Fin.snoc_castSucc, evalWires_appendChainBlock_old]
      exact ihIn i
    · change (mid.snoc (.and prevOut newOut)).evalWires x
          ⟨wPrev + (L + 2) + 1 - 1, by omega⟩ = _
      have hLastEq :
          (⟨wPrev + (L + 2) + 1 - 1, by omega⟩ :
              Fin (wPrev + (L + 2) + 1)) =
            Fin.last (wPrev + (L + 2)) := by
        ext; simp
      rw [hLastEq]
      change (mid.snoc (.and prevOut newOut)).evalWires x (Fin.last (wPrev + (L + 2))) = _
      simp only [Circuit.evalWires, Gate.eval]
      have hPrevVal : mid.evalWires x prevOut = stageTarget k L j (by omega) x := by
        dsimp only [mid, prevOut]
        rw [evalWires_appendChainBlock_old]
        exact ihOut
      have hNewVal : mid.evalWires x newOut =
          chainOut L (x ⟨2 * (j + 1), by omega⟩) (x ⟨2 * (j + 1) + 1, by omega⟩) := by
        dsimp [mid, newOut]
        rw [evalWires_appendChainBlock_last]
        have hu := ihIn ⟨2 * (j + 1), by omega⟩
        have hv := ihIn ⟨2 * (j + 1) + 1, by omega⟩
        change chainOut L (prev.evalWires x u0) (prev.evalWires x v0) = _
        rw [hu, hv]
      rw [hPrevVal, hNewVal, Fin.snoc_last]

theorem source_eval_eq (k L : Nat) (x : Fin (2 * (k + 1)) → Bool) :
    (source k L).eval x = stageTarget k L k (le_refl k) x :=
  (evalWires_buildStage k L k (le_refl k) x).2

/-- 2-input `BlockCircuit` contracting `source k L` into `2 * k + 1` blocks (`≤ 2 * n` wires). -/
def buildBlockCircuit (k L : Nat) :
    (j : Nat) → j ≤ k → BlockCircuit (2 * (k + 1)) 2 (2 * (k + 1) + (2 * j + 1))
  | 0, _ =>
    let n := 2 * (k + 1)
    let args : Fin 2 → Fin n := fun i => if i = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
    BlockCircuit.inputsOnly.snoc args (fun p => chainOut L (p 0) (p 1))
  | j + 1, hj =>
    let n := 2 * (k + 1)
    let prev := buildBlockCircuit k L j (by omega)
    let w1 := n + (2 * j + 1)
    let argsBlock : Fin 2 → Fin w1 := fun i =>
      if i = 0 then ⟨2 * (j + 1), by omega⟩ else ⟨2 * (j + 1) + 1, by omega⟩
    let step1 := prev.snoc argsBlock (fun p => chainOut L (p 0) (p 1))
    let argsAnd : Fin 2 → Fin (w1 + 1) := fun i =>
      if i = 0 then ⟨w1 - 1, by omega⟩ else Fin.last w1
    step1.snoc argsAnd (fun p => p 0 && p 1)

theorem evalWires_buildBlockCircuit (k L : Nat) :
    ∀ (j : Nat) (hj : j ≤ k) (x : Fin (2 * (k + 1)) → Bool),
      (∀ i : Fin (2 * (k + 1)),
        (buildBlockCircuit k L j hj).evalWires x ⟨i.val, by omega⟩ = x i) ∧
      (buildBlockCircuit k L j hj).evalWires x
          (Fin.last (2 * (k + 1) + 2 * j)) =
        stageTarget k L j hj x := by
  intro j
  induction j with
  | zero =>
    intro _ x
    dsimp [buildBlockCircuit, stageTarget]
    refine ⟨fun i => ?_, ?_⟩
    · have hCast : (⟨i.val, by omega⟩ : Fin (2 * (k + 1) + 1)) = i.castSucc := rfl
      rw [hCast, BlockCircuit.evalWires, Fin.snoc_castSucc]
      rfl
    · simp [BlockCircuit.evalWires]
  | succ j ih =>
    intro hj x
    obtain ⟨ihIn, ihOut⟩ := ih (by omega) x
    dsimp [buildBlockCircuit, stageTarget]
    let prev := buildBlockCircuit k L j (by omega)
    let w1 := 2 * (k + 1) + (2 * j + 1)
    let argsBlock : Fin 2 → Fin w1 := fun i =>
      if i = 0 then ⟨2 * (j + 1), by omega⟩ else ⟨2 * (j + 1) + 1, by omega⟩
    let step1 := prev.snoc argsBlock (fun p => chainOut L (p 0) (p 1))
    let argsAnd : Fin 2 → Fin (w1 + 1) := fun i =>
      if i = 0 then ⟨w1 - 1, by omega⟩ else Fin.last w1
    refine ⟨fun i => ?_, ?_⟩
    · have hC1 : (⟨i.val, by omega⟩ : Fin (w1 + 1 + 1)) =
          (⟨i.val, by omega⟩ : Fin (w1 + 1)).castSucc := rfl
      have hC2 : (⟨i.val, by omega⟩ : Fin (w1 + 1)) =
          (⟨i.val, by omega⟩ : Fin w1).castSucc := rfl
      change (step1.snoc argsAnd _).evalWires x _ = x i
      rw [hC1, BlockCircuit.evalWires, Fin.snoc_castSucc]
      change (prev.snoc argsBlock _).evalWires x _ = x i
      rw [hC2, BlockCircuit.evalWires, Fin.snoc_castSucc]
      exact ihIn i
    · have hLastEq : Fin.last (2 * (k + 1) + 2 * (j + 1)) = Fin.last (w1 + 1) := by
        ext; simp [w1]; omega
      rw [hLastEq]
      change (step1.snoc argsAnd (fun p => p 0 && p 1)).evalWires x (Fin.last (w1 + 1)) = _
      simp [BlockCircuit.evalWires]
      have hPrev : step1.evalWires x (argsAnd 0) = stageTarget k L j (by omega) x := by
        have hArg0 : argsAnd 0 = (Fin.last (2 * (k + 1) + 2 * j)).castSucc := by
          ext; simp [argsAnd, w1]
        rw [hArg0]
        change (prev.snoc argsBlock _).evalWires x (Fin.last (2 * (k + 1) + 2 * j)).castSucc = _
        rw [BlockCircuit.evalWires, Fin.snoc_castSucc]
        exact ihOut
      have hNew : step1.evalWires x (argsAnd 1) =
          chainOut L (x ⟨2 * (j + 1), by omega⟩) (x ⟨2 * (j + 1) + 1, by omega⟩) := by
        have hArg1 : argsAnd 1 = Fin.last w1 := by simp [argsAnd]
        rw [hArg1]
        change (prev.snoc argsBlock (fun p => chainOut L (p 0) (p 1))).evalWires x (Fin.last w1) = _
        simp [BlockCircuit.evalWires]
        have hu := ihIn ⟨2 * (j + 1), by omega⟩
        have hv := ihIn ⟨2 * (j + 1) + 1, by omega⟩
        have h0 : prev.evalWires x (argsBlock 0) = x ⟨2 * (j + 1), by omega⟩ := by
          simpa [argsBlock] using hu
        have h1 : prev.evalWires x (argsBlock 1) = x ⟨2 * (j + 1) + 1, by omega⟩ := by
          simpa [argsBlock] using hv
        rw [h0, h1, Fin.snoc_last]
      rw [hPrev, hNew, Fin.snoc_last]

/-- Verified `2`-interface block contraction certificate for `DenseChainBlocks.source k L`
using only `2 * k + 1` blocks (`≤ 2 * n` total variables, width `≤ 3`) regardless of `L`. -/
def blockCertificate (k L : Nat) : BlockContractionCertificate (source k L) 2 where
  blocks := 2 * k + 1
  bc := buildBlockCircuit k L k (le_refl k)
  output := Fin.last (2 * (k + 1) + 2 * k)
  eval_eq x := by
    rw [(evalWires_buildBlockCircuit k L k (le_refl k) x).2, source_eval_eq]

theorem blockCertificate_vars_le (k L : Nat) :
    2 * (k + 1) + (blockCertificate k L).blocks ≤ 2 * (2 * (k + 1)) := by
  dsimp [blockCertificate]
  omega

/-- For **any** internal cascade schedule `L : Nat → Nat` (including `L k = k` with
`≥ (k + 1) ^ 2 = Θ(n^2)` binary gates and max fanout `2`), `DenseChainBlocks.source k (L k)`
runs in `2 ^ o(n)` deterministic exact `#SAT` time via block contraction. -/
theorem subexponential (L : Nat → Nat) (C d : ℝ) :
    (fun k => logTimeBudget (2 * (k + 1)) (2 * (k + 1) + (blockCertificate k (L k)).blocks) C d)
      =o[atTop] fun k => ((2 * (k + 1) : Nat) : ℝ) := by
  have hn : Tendsto (fun k => 2 * (k + 1)) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  refine block_contraction_subexponential (fun k => source k (L k))
    (fun k => blockCertificate k (L k)) hn (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 2) ?_ C d
  filter_upwards with k
  have hB : (blockCertificate k (L k)).blocks ≤ 2 * (k + 1) := by
    dsimp [blockCertificate]; omega
  simpa using (show ((blockCertificate k (L k)).blocks : ℝ) ≤ ((2 * (k + 1) : Nat) : ℝ) by
    exact_mod_cast hB)

end DenseChainBlocks

end PvsNP

