module

public import PvsNP.FormulaCircuit
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

/-!
# Branching and Sum-of-Products 3-CNF Compression via Cut Pinning

Extends single-CNF `CircuitCompressionTask` along two axes:
1. **Branching 3-CNF compression (`BranchingCertificate`)**: partitions `source.Accepting` into
   `R = 2 ^ o(n)` disjoint 3-CNF branches, each within the superlinear
   `O(n * (log n) ^ α)` (`α < 1 / 2`) variable window of the fixed-width exact `#3-SAT` counter.
2. **Sum-of-Products 3-CNF decomposition (`SumOfProductsCertificate`)**: conditions on a wire cut
   of size `k = o(n)` so each branch factors into `M` independent 3-CNF subproblems
   (`|source.Accepting| = ∑_b ∏_j |Models(F_{b,j})|`), solving even `Θ(n ^ 2)`-gate (and general
   `poly(n)`-gate) circuits in `2 ^ o(n)` deterministic time whenever `o(n)` cut wires decouple the
   circuit into factors of at most `O(n * (log n) ^ α)` variables (`α < 1 / 2`).
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Branching and Sum-of-Products Certificates -/

instance {v : Nat} (formula : CNF (Fin v)) : Fintype (Models formula) :=
  Subtype.fintype _

instance {n : Nat} (inst : CircuitInstance n) : Fintype inst.Accepting :=
  Subtype.fintype _

/-- Partitions the accepting inputs of `source` into a disjoint sum of width-`≤ 3` CNF model sets. -/
structure BranchingCertificate {n : Nat} (source : CircuitInstance n) where
  branches : Nat
  vars : Fin branches → Nat
  formula : (b : Fin branches) → CNF (Fin (vars b))
  modelsEquiv : (Σ b : Fin branches, Models (formula b)) ≃ source.Accepting
  width : ∀ b (clause : CNF.Clause (Fin (vars b))), clause ∈ (formula b).clauses → clause.size ≤ 3

namespace BranchingCertificate

theorem exact_count_sum {n : Nat} {source : CircuitInstance n}
    (cert : BranchingCertificate source) :
    Nat.card source.Accepting = ∑ b : Fin cert.branches, Nat.card (Models (cert.formula b)) := by
  classical
  rw [← Nat.card_congr cert.modelsEquiv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Nat.card_eq_fintype_card.symm

theorem canonical_count_sum {n : Nat} {source : CircuitInstance n}
    (cert : BranchingCertificate source) :
    Nat.card source.Accepting =
      ∑ b : Fin cert.branches, Nat.card (CanonicalModels (canonicalize (cert.formula b))) := by
  rw [cert.exact_count_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Nat.card_congr (canonicalModelsEquiv (cert.formula b)).symm

theorem canonical_width {n : Nat} {source : CircuitInstance n}
    (cert : BranchingCertificate source) (b : Fin cert.branches)
    (clause : Finset (Fin (cert.vars b) × Bool))
    (hClause : clause ∈ canonicalize (cert.formula b)) :
    clause.card ≤ 3 :=
  canonicalize_width (cert.formula b) (cert.width b) clause hClause

theorem sat_iff {n : Nat} {source : CircuitInstance n}
    (cert : BranchingCertificate source) :
    (∃ input, source.eval input = true) ↔
      ∃ b : Fin cert.branches, ∃ σ : Fin (cert.vars b) → Bool, (cert.formula b).eval σ = true := by
  constructor
  · rintro ⟨input, hIn⟩
    obtain ⟨b, σ, hSat⟩ := cert.modelsEquiv.symm ⟨input, hIn⟩
    exact ⟨b, σ, hSat⟩
  · rintro ⟨b, σ, hSat⟩
    obtain ⟨input, hIn⟩ := cert.modelsEquiv ⟨b, ⟨σ, hSat⟩⟩
    exact ⟨input, hIn⟩

end BranchingCertificate

/-- Sum-of-products 3-CNF decomposition: `source.Accepting` is in bijection with choices of a
branch `b` together with independent satisfying assignments to each factor `formula b j`. -/
structure SumOfProductsCertificate {n : Nat} (source : CircuitInstance n) where
  branches : Nat
  factors : Fin branches → Nat
  vars : (b : Fin branches) → Fin (factors b) → Nat
  formula : (b : Fin branches) → (j : Fin (factors b)) → CNF (Fin (vars b j))
  modelsEquiv : (Σ b : Fin branches, ∀ j : Fin (factors b), Models (formula b j)) ≃ source.Accepting
  width : ∀ b j (clause : CNF.Clause (Fin (vars b j))),
    clause ∈ (formula b j).clauses → clause.size ≤ 3

/-- Every additive `BranchingCertificate` is a 1-factor `SumOfProductsCertificate`. -/
def BranchingCertificate.toSumOfProducts {n : Nat} {source : CircuitInstance n}
    (cert : BranchingCertificate source) : SumOfProductsCertificate source where
  branches := cert.branches
  factors := fun _ => 1
  vars := fun b _ => cert.vars b
  formula := fun b _ => cert.formula b
  modelsEquiv :=
    (Equiv.sigmaCongrRight fun b =>
      { toFun := fun (f : Fin 1 → Models (cert.formula b)) => f 0
        invFun := fun m (_ : Fin 1) => m
        left_inv := fun f => funext fun j => by rw [Fin.eq_zero j]
        right_inv := fun _ => rfl }).trans cert.modelsEquiv
  width := fun b _ clause h => cert.width b clause h

namespace SumOfProductsCertificate

theorem exact_count_sum_prod {n : Nat} {source : CircuitInstance n}
    (cert : SumOfProductsCertificate source) :
    Nat.card source.Accepting =
      ∑ b : Fin cert.branches, ∏ j : Fin (cert.factors b), Nat.card (Models (cert.formula b j)) := by
  classical
  rw [← Nat.card_congr cert.modelsEquiv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Nat.card_eq_fintype_card.symm

theorem canonical_count_sum_prod {n : Nat} {source : CircuitInstance n}
    (cert : SumOfProductsCertificate source) :
    Nat.card source.Accepting =
      ∑ b : Fin cert.branches,
        ∏ j : Fin (cert.factors b),
          Nat.card (CanonicalModels (canonicalize (cert.formula b j))) := by
  rw [cert.exact_count_sum_prod]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Nat.card_congr (canonicalModelsEquiv (cert.formula b j)).symm

theorem canonical_width {n : Nat} {source : CircuitInstance n}
    (cert : SumOfProductsCertificate source) (b : Fin cert.branches) (j : Fin (cert.factors b))
    (clause : Finset (Fin (cert.vars b j) × Bool))
    (hClause : clause ∈ canonicalize (cert.formula b j)) :
    clause.card ≤ 3 :=
  canonicalize_width (cert.formula b j) (cert.width b j) clause hClause

theorem sat_iff {n : Nat} {source : CircuitInstance n}
    (cert : SumOfProductsCertificate source) :
    (∃ input, source.eval input = true) ↔
      ∃ b : Fin cert.branches,
        ∀ j : Fin (cert.factors b), ∃ σ : Fin (cert.vars b j) → Bool,
          (cert.formula b j).eval σ = true := by
  classical
  constructor
  · rintro ⟨input, hIn⟩
    obtain ⟨b, f⟩ := cert.modelsEquiv.symm ⟨input, hIn⟩
    exact ⟨b, fun j => ⟨(f j).val, (f j).property⟩⟩
  · rintro ⟨b, hAll⟩
    let f : ∀ j : Fin (cert.factors b), Models (cert.formula b j) :=
      fun j => ⟨Classical.choose (hAll j), Classical.choose_spec (hAll j)⟩
    obtain ⟨input, hIn⟩ := cert.modelsEquiv ⟨b, f⟩
    exact ⟨input, hIn⟩

end SumOfProductsCertificate

/-! ### 2. Subexponential Runtime Transfer for Sum-of-Products Compression -/

private theorem le_two_rpow_two_mul_log {K : ℝ} (hK : 1 ≤ K) :
    K ≤ (2 : ℝ) ^ (2 * Real.log K) := by
  have hExp1Le4 : Real.exp 1 ≤ 4 := by
    have hHalf : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
      have h := Real.add_one_le_exp (-1 / 2 : ℝ)
      linarith
    have hPos : 0 < Real.exp (1 / 2) := Real.exp_pos _
    have hProd : (1 / 2 : ℝ) * Real.exp (1 / 2) ≤ 1 := by
      calc
        (1 / 2 : ℝ) * Real.exp (1 / 2) ≤ Real.exp (-1 / 2) * Real.exp (1 / 2) :=
          mul_le_mul_of_nonneg_right hHalf hPos.le
        _ = Real.exp (-1 / 2 + 1 / 2) := (Real.exp_add _ _).symm
        _ = 1 := by norm_num
    have hLe2 : Real.exp (1 / 2) ≤ 2 := by linarith
    calc
      Real.exp 1 = Real.exp (1 / 2 + 1 / 2) := by norm_num
      _ = Real.exp (1 / 2) * Real.exp (1 / 2) := Real.exp_add _ _
      _ ≤ 2 * 2 := mul_le_mul hLe2 hLe2 hPos.le (by norm_num)
      _ = 4 := by norm_num
  have hLog4 : 1 ≤ 2 * Real.log 2 := by
    have h1 : 1 ≤ Real.log 4 := (Real.le_log_iff_exp_le (by norm_num)).mpr hExp1Le4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hLogKNonneg : 0 ≤ Real.log K := Real.log_nonneg hK
  have hMul : Real.log K ≤ Real.log 2 * (2 * Real.log K) := by nlinarith
  calc
    K = Real.exp (Real.log K) := (Real.exp_log (lt_of_lt_of_le zero_lt_one hK)).symm
    _ ≤ Real.exp (Real.log 2 * (2 * Real.log K)) := Real.exp_le_exp.mpr hMul
    _ = (2 : ℝ) ^ (2 * Real.log K) := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm

/-- Combined exponent budget when evaluating up to `R` branches of up to `M` factors each,
with every factor CNF having variable count `v` (within the `#3-SAT` counter budget). -/
noncomputable def sopLogTimeBudget (n R M v : Nat) (C d : ℝ) : ℝ :=
  2 * Real.log (((R + 1) * (M + 1) : Nat) : ℝ) + logTimeBudget n v C d

theorem sop_runtime_le_rpow (n R M v : Nat) (C d : ℝ) :
    (R : ℝ) * (M : ℝ) * (2 : ℝ) ^ logTimeBudget n v C d ≤
      (2 : ℝ) ^ sopLogTimeBudget n R M v C d := by
  let K : ℝ := (((R + 1) * (M + 1) : Nat) : ℝ)
  have hKGe1 : 1 ≤ K := by
    dsimp only [K]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hRMLeK : (R : ℝ) * (M : ℝ) ≤ K := by
    dsimp only [K]
    push_cast
    nlinarith
  have hKRpow : K ≤ (2 : ℝ) ^ (2 * Real.log K) := le_two_rpow_two_mul_log hKGe1
  have hPos : 0 ≤ (2 : ℝ) ^ logTimeBudget n v C d := by positivity
  calc
    (R : ℝ) * (M : ℝ) * (2 : ℝ) ^ logTimeBudget n v C d
      ≤ K * (2 : ℝ) ^ logTimeBudget n v C d :=
        mul_le_mul_of_nonneg_right hRMLeK hPos
    _ ≤ (2 : ℝ) ^ (2 * Real.log K) * (2 : ℝ) ^ logTimeBudget n v C d :=
        mul_le_mul_of_nonneg_right hKRpow hPos
    _ = (2 : ℝ) ^ sopLogTimeBudget n R M v C d := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        rfl

theorem sopLogTimeBudget_isLittleO_of_rpow_log {n R M v : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hBranches : (fun i => Real.log ((R i : ℝ) + 1)) =o[atTop] fun i => (n i : ℝ))
    (hFactors : (fun i => Real.log ((M i : ℝ) + 1)) =o[atTop] fun i => (n i : ℝ))
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hVars : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => sopLogTimeBudget (n i) (R i) (M i) (v i) C d) =o[atTop] fun i => (n i : ℝ) := by
  have hFactorBudget := logTimeBudget_isLittleO_of_rpow_log_any hn hc hα hVars C d
  have hLogProd : (fun i => 2 * Real.log (((R i + 1) * (M i + 1) : Nat) : ℝ)) =o[atTop]
      fun i => (n i : ℝ) := by
    have hSum := (hBranches.add hFactors).const_mul_left 2
    refine hSum.congr' ?_ (Eventually.of_forall fun _ => rfl)
    refine Eventually.of_forall fun i => ?_
    dsimp only
    have hRPos : (0 : ℝ) < (R i : ℝ) + 1 := by positivity
    have hMPos : (0 : ℝ) < (M i : ℝ) + 1 := by positivity
    have hCast : (((R i + 1) * (M i + 1) : Nat) : ℝ) = ((R i : ℝ) + 1) * ((M i : ℝ) + 1) := by
      push_cast; ring
    rw [hCast, Real.log_mul hRPos.ne' hMPos.ne']
  exact hLogProd.add hFactorBudget

theorem subexponential_of_sopLogTimeBudget {n R M v : Nat → Nat} {time : Nat → ℝ} {C d : ℝ}
    (hBudget : (fun i => sopLogTimeBudget (n i) (R i) (M i) (v i) C d) =o[atTop]
      fun i => (n i : ℝ))
    (hTime : ∀ᶠ i in atTop,
      time i ≤ (R i : ℝ) * (M i : ℝ) * (2 : ℝ) ^ logTimeBudget (n i) (v i) C d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, time i ≤ (2 : ℝ) ^ (ε * (n i : ℝ)) := by
  intro ε hε
  filter_upwards [hTime, hBudget.def hε] with i hTi hBi
  have hStep := hTi.trans (sop_runtime_le_rpow (n i) (R i) (M i) (v i) C d)
  apply hStep.trans
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
  have hnNonneg : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hnNonneg] using hBi)

/-! ### 3. Cut-Pinning & Factored-Cut Reductions -/

/-- Canonical enumeration of the `2 ^ k` Boolean assignments to a width-`k` wire cut. -/
noncomputable def cutBranchEquiv (k : Nat) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  Fintype.equivFinOfCardEq (by simp)

/-- **Cut-Residual Branching Theorem**: if fixing a width-`k` wire cut `boundary` reduces
`source` on each branch `fixed : Fin k → Bool` to a residual circuit `residual fixed`, then
`source` admits an exact `2 ^ k`-branch width-`≤ 3` CNF certificate where branch `b` uses
`n + (residual ...).circuit.gateCount` variables. -/
noncomputable def branchingOfCutResiduals {n k : Nat}
    (source : CircuitInstance n) (boundary : Fin k → Fin source.wires)
    (residual : (Fin k → Bool) → CircuitInstance n)
    (hRes : ∀ fixed input, (residual fixed).eval input = true ↔
      source.eval input = true ∧ source.circuit.evalWires input ∘ boundary = fixed) :
    BranchingCertificate source where
  branches := 2 ^ k
  vars := fun b => (residual ((cutBranchEquiv k).symm b)).wires
  formula := fun b => (residual ((cutBranchEquiv k).symm b)).cnf
  modelsEquiv := by
    let partEquiv : (Σ fixed : Fin k → Bool, (residual fixed).Accepting) ≃ source.Accepting :=
      { toFun := fun s => ⟨s.2.val, ((hRes s.1 s.2.val).mp s.2.property).1⟩
        invFun := fun input =>
          ⟨source.circuit.evalWires input.val ∘ boundary,
            ⟨input.val, (hRes _ input.val).mpr ⟨input.property, rfl⟩⟩⟩
        left_inv := fun ⟨fixed, input, hIn⟩ => by
          have hFix := ((hRes fixed input).mp hIn).2
          subst hFix
          rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    exact (Equiv.sigmaCongr (cutBranchEquiv k).symm fun b =>
      (residual ((cutBranchEquiv k).symm b)).circuit.acceptingAssignmentsEquiv
        (residual ((cutBranchEquiv k).symm b)).output).trans partEquiv
  width := fun b _ h =>
    (residual ((cutBranchEquiv k).symm b)).circuit.encode_width
      (residual ((cutBranchEquiv k).symm b)).output h

/-- **Factored-Cut Sum-of-Products Theorem**: if conditioning `source` (on `m * p` inputs) on a
width-`k` wire cut `boundary` decouples acceptance into `m` block-local pod circuits
`pod fixed j : CircuitInstance p`, then `source` admits an exact `2 ^ k`-branch, `m`-factor
`SumOfProductsCertificate` where factor `(b, j)` uses `p + (pod ... j).circuit.gateCount`
variables and width `≤ 3`. -/
noncomputable def sopOfFactoredCut {m p k : Nat}
    (source : CircuitInstance (m * p)) (boundary : Fin k → Fin source.wires)
    (pod : (Fin k → Bool) → Fin m → CircuitInstance p)
    (hFactored : ∀ fixed input,
      (source.eval input = true ∧ source.circuit.evalWires input ∘ boundary = fixed) ↔
        ∀ j : Fin m, (pod fixed j).eval (fun s => input (finProdFinEquiv (j, s))) = true) :
    SumOfProductsCertificate source where
  branches := 2 ^ k
  factors := fun _ => m
  vars := fun b j => (pod ((cutBranchEquiv k).symm b) j).wires
  formula := fun b j => (pod ((cutBranchEquiv k).symm b) j).cnf
  modelsEquiv := by
    let blockAssemble : (Fin m → Fin p → Bool) ≃ (Fin (m * p) → Bool) :=
      { toFun := fun g idx => g (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2
        invFun := fun input j s => input (finProdFinEquiv (j, s))
        left_inv := fun g => funext fun j => funext fun s => by simp
        right_inv := fun input => funext fun idx =>
          congrArg input (finProdFinEquiv.apply_symm_apply idx) }
    let branchSlice (fixed : Fin k → Bool) :=
      { input : Fin (m * p) → Bool //
        ∀ j : Fin m, (pod fixed j).eval (fun s => input (finProdFinEquiv (j, s))) = true }
    let partEquiv : (Σ fixed : Fin k → Bool, branchSlice fixed) ≃ source.Accepting :=
      { toFun := fun s => ⟨s.2.val, ((hFactored s.1 s.2.val).mpr s.2.property).1⟩
        invFun := fun input =>
          ⟨source.circuit.evalWires input.val ∘ boundary,
            ⟨input.val, (hFactored _ input.val).mp ⟨input.property, rfl⟩⟩⟩
        left_inv := fun ⟨fixed, input, hIn⟩ => by
          have hFix := ((hFactored fixed input).mpr hIn).2
          subst hFix
          rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    refine (Equiv.sigmaCongr (cutBranchEquiv k).symm fun b => ?_).trans partEquiv
    let fixed := (cutBranchEquiv k).symm b
    refine (Equiv.piCongrRight fun j =>
      (pod fixed j).circuit.acceptingAssignmentsEquiv (pod fixed j).output).trans ?_
    exact
      { toFun := fun f => ⟨blockAssemble (fun j => (f j).val), fun j => by
          have hBlk : (fun s => blockAssemble (fun j' => (f j').val) (finProdFinEquiv (j, s))) =
              (f j).val := congrFun (blockAssemble.left_inv (fun j' => (f j').val)) j
          change (pod fixed j).eval _ = true
          rw [hBlk]
          exact (f j).property⟩
        invFun := fun s j => ⟨fun idx => s.val (finProdFinEquiv (j, idx)), s.property j⟩
        left_inv := fun f => funext fun j =>
          Subtype.ext (congrFun (blockAssemble.left_inv (fun j' => (f j').val)) j)
        right_inv := fun s => Subtype.ext (blockAssemble.right_inv s.val) }
  width := fun b j _ h =>
    (pod ((cutBranchEquiv k).symm b) j).circuit.encode_width
      (pod ((cutBranchEquiv k).symm b) j).output h

/-- Subexponential `#SAT` transfer for factored cuts: a width-`o(n)` cut (`k i = o(n i)`) into
`m i ≤ (n i) ^ D` factors whose individual pod circuits have at most
`c * n i * (log (n i + 16)) ^ α` gates (`α < 1 / 2`) runs in `2 ^ o(n i)` deterministic time,
even when the unsplit source circuit has `Ω(n i ^ (D + 1))` total gates. -/
theorem factored_cut_sopLogTimeBudget_isLittleO {n k M v : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hCutWidth : (fun i => (k i : ℝ)) =o[atTop] fun i => (n i : ℝ))
    (D : Nat) (hFactorsPoly : ∀ᶠ i in atTop, M i ≤ (n i + 2) ^ D)
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hFactorVars : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => sopLogTimeBudget (n i) (2 ^ k i) (M i) (v i) C d) =o[atTop] fun i => (n i : ℝ) := by
  have hBranches : (fun i => Real.log (((2 ^ k i : Nat) : ℝ) + 1)) =o[atTop]
      fun i => (n i : ℝ) := by
    have hDom : (fun i => Real.log (((2 ^ k i : Nat) : ℝ) + 1)) =O[atTop]
        fun i => (k i : ℝ) + 1 := by
      refine IsBigO.of_bound 2 ?_
      refine Eventually.of_forall fun i => ?_
      have hGe1 : (1 : ℝ) ≤ ((2 ^ k i : Nat) : ℝ) + 1 := by linarith
      have hNonneg : 0 ≤ Real.log (((2 ^ k i : Nat) : ℝ) + 1) := Real.log_nonneg hGe1
      rw [Real.norm_of_nonneg hNonneg, Real.norm_of_nonneg (by positivity)]
      have hLe : ((2 ^ k i : Nat) : ℝ) + 1 ≤ (2 : ℝ) ^ (k i + 1) := by
        push_cast
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k i := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        linarith
      calc
        Real.log (((2 ^ k i : Nat) : ℝ) + 1)
          ≤ Real.log ((2 : ℝ) ^ (k i + 1)) := Real.log_le_log (by positivity) hLe
        _ = ((k i : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
        _ ≤ 2 * ((k i : ℝ) + 1) := by
            have hLog2 : Real.log 2 ≤ 2 :=
              (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
            nlinarith
    have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hn
    have hOneLittleO : (fun _ : Nat => (1 : ℝ)) =o[atTop] fun i => (n i : ℝ) :=
      isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp hnReal))
    exact hDom.trans_isLittleO (hCutWidth.add hOneLittleO)
  have hFactors : (fun i => Real.log ((M i : ℝ) + 1)) =o[atTop] fun i => (n i : ℝ) := by
    have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hn
    have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
    have hShiftBigO : (fun i => (n i : ℝ) + 16) =O[atTop] fun i => (n i : ℝ) := by
      refine IsBigO.of_bound 17 ?_
      filter_upwards [hnReal.eventually_ge_atTop 1] with i hi
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      linarith
    have hLogShift := (Real.isLittleO_log_id_atTop.comp_tendsto hnShift).trans_isBigO hShiftBigO
    have hDom : (fun i => Real.log ((M i : ℝ) + 1)) =O[atTop]
        fun i => Real.log ((n i : ℝ) + 16) := by
      refine IsBigO.of_bound ((D : ℝ) + 1) ?_
      filter_upwards [hFactorsPoly] with i hMi
      have hMGe1 : (1 : ℝ) ≤ (M i : ℝ) + 1 := by linarith
      have hMNonneg : 0 ≤ Real.log ((M i : ℝ) + 1) := Real.log_nonneg hMGe1
      have hLNonneg : 0 ≤ Real.log ((n i : ℝ) + 16) := Real.log_nonneg (by linarith)
      rw [Real.norm_of_nonneg hMNonneg, Real.norm_of_nonneg hLNonneg]
      have hBound : (M i : ℝ) + 1 ≤ ((n i : ℝ) + 16) ^ (D + 1) := by
        have hCast : (M i : ℝ) ≤ ((n i : ℝ) + 2) ^ D := by exact_mod_cast hMi
        have hBase : ((n i : ℝ) + 2) ^ D ≤ ((n i : ℝ) + 16) ^ D := by gcongr; linarith
        have hPow1 : ((n i : ℝ) + 16) ^ D * 16 ≤ ((n i : ℝ) + 16) ^ (D + 1) := by
          rw [pow_succ]
          have : (16 : ℝ) ≤ (n i : ℝ) + 16 := by linarith
          gcongr
        have hPowPos : 1 ≤ ((n i : ℝ) + 16) ^ D := one_le_pow₀ (by linarith)
        nlinarith
      calc
        Real.log ((M i : ℝ) + 1) ≤ Real.log (((n i : ℝ) + 16) ^ (D + 1)) :=
          Real.log_le_log (by positivity) hBound
        _ = ((D : ℝ) + 1) * Real.log ((n i : ℝ) + 16) := by
          rw [Real.log_pow]; push_cast; ring
    exact hDom.trans_isLittleO hLogShift
  exact sopLogTimeBudget_isLittleO_of_rpow_log hn hBranches hFactors hc hα hFactorVars C d

/-! ### 4. Concrete `Θ(n ^ 2)`-Gate Witness Family Solved in `2 ^ o(n)` Time -/

namespace QuadraticHubPods

open BoolFormula

/-- Input count for `k + 1` pods of 2 bits each: `n(k) = 2 * (k + 1)`. -/
abbrev inputCount (k : Nat) : Nat := (k + 1) * 2

/-- Shared hub input coordinate `(0, 0)` broadcast to all `k + 1` pods. -/
def hubCoord (k : Nat) : Fin (inputCount k) :=
  finProdFinEquiv (0, 0)

/-- Single-step mux `(¬h ∧ x) ∨ (h ∧ y)` (4 gates). -/
def muxStep {α : Type} (h x y : α) : BoolFormula α :=
  .binary .or (.binary .and (.not (.var h)) (.var x)) (.binary .and (.var h) (.var y))

/-- Depth-`d` repeated selector pod with `5 * d + 4` gates and mux semantics. -/
def repeatPod {α : Type} : Nat → α → α → α → BoolFormula α
  | 0, h, x, y => muxStep h x y
  | d + 1, h, x, y => .binary .and (muxStep h x y) (repeatPod d h x y)

theorem repeatPod_eval {α : Type} (val : α → Bool) (d : Nat) (h x y : α) :
    (repeatPod d h x y).eval val = (if val h then val y else val x) := by
  have hStep : (muxStep h x y).eval val = (if val h then val y else val x) := by
    simp only [muxStep, eval, BinaryGate.eval]
    cases val h <;> cases val x <;> cases val y <;> rfl
  induction d with
  | zero => exact hStep
  | succ d ih =>
    simp [repeatPod, eval, BinaryGate.eval, hStep, ih]

theorem repeatPod_gateCount {α : Type} (d : Nat) (h x y : α) :
    (repeatPod d h x y).gateCount = 5 * d + 4 := by
  have hStep : (muxStep h x y).gateCount = 4 := rfl
  induction d with
  | zero => exact hStep
  | succ d ih =>
    simp only [repeatPod, gateCount, hStep, ih]
    omega

/-- Conjunction of `m + 1` pod formulas. -/
def conjPods {α : Type} : (m : Nat) → (Fin (m + 1) → BoolFormula α) → BoolFormula α
  | 0, pods => pods 0
  | m + 1, pods => .binary .and (pods 0) (conjPods m (fun j => pods j.succ))

theorem conjPods_eval {α : Type} (val : α → Bool) :
    ∀ (m : Nat) (pods : Fin (m + 1) → BoolFormula α),
      ((conjPods m pods).eval val = true) ↔ ∀ j : Fin (m + 1), (pods j).eval val = true
  | 0, pods => by
    constructor
    · intro h j; rw [Fin.eq_zero j]; exact h
    · intro h; exact h 0
  | m + 1, pods => by
    simp only [conjPods, eval, BinaryGate.eval, Bool.and_eq_true, conjPods_eval val m]
    constructor
    · rintro ⟨h0, hRest⟩ j
      cases j using Fin.cases with
      | zero => exact h0
      | succ j' => exact hRest j'
    · intro hAll
      exact ⟨hAll 0, fun j' => hAll j'.succ⟩

theorem conjPods_gateCount {α : Type} :
    ∀ (m : Nat) (c : Nat) (pods : Fin (m + 1) → BoolFormula α),
      (∀ j, (pods j).gateCount = c) →
      (conjPods m pods).gateCount = (m + 1) * c + m
  | 0, c, pods, hC => by simp [conjPods, hC 0]
  | m + 1, c, pods, hC => by
    simp only [conjPods, gateCount, hC 0, conjPods_gateCount m c _ (fun j => hC j.succ)]
    ring

/-- Full `Θ(n ^ 2)`-gate formula over `inputCount k` inputs. -/
def sourceFormula (k : Nat) : BoolFormula (Fin (inputCount k)) :=
  conjPods k fun j =>
    repeatPod k (hubCoord k)
      (finProdFinEquiv (j, 0))
      (finProdFinEquiv (j, 1))

def sourceCompilation (k : Nat) :=
  (sourceFormula k).compile Circuit.inputsOnly id

/-- Concrete `Θ(n ^ 2)`-gate `CircuitInstance` family. -/
def source (k : Nat) : CircuitInstance (inputCount k) :=
  ⟨(sourceCompilation k).stop, (sourceCompilation k).circuit, (sourceCompilation k).output⟩

/-- Single-wire hub cut inside `source k`. -/
def hubBoundary (k : Nat) : Fin 1 → Fin (source k).wires :=
  fun _ => (sourceCompilation k).embed (hubCoord k)

theorem source_gateCount (k : Nat) :
    (source k).circuit.gateCount = (k + 1) * (5 * k + 4) + k := by
  have hComp := (sourceCompilation k).gate_count
  simp only [source, Circuit.gateCount, zero_add] at hComp ⊢
  rw [hComp, sourceFormula]
  exact conjPods_gateCount k (5 * k + 4) _ fun j => repeatPod_gateCount k _ _ _

/-- `source k` has genuinely quadratic `Θ(n ^ 2)` gate count (`n = 2 * (k + 1)`). -/
theorem source_quadratic_gates (k : Nat) :
    (inputCount k) ^ 2 ≤ (source k).circuit.gateCount ∧
      (source k).circuit.gateCount ≤ 2 * (inputCount k) ^ 2 := by
  rw [source_gateCount, inputCount]
  constructor <;> nlinarith

/-- Local 2-input residual pod formula when the hub bit is pinned to `bit`. -/
def podFormula (bit : Bool) (isZero : Bool) : BoolFormula (Fin 2) :=
  let active : BoolFormula (Fin 2) := if bit then .var 1 else .var 0
  if isZero then
    .binary .and (if bit then .var 0 else .not (.var 0)) active
  else
    active

def podResidual (k : Nat) (fixed : Fin 1 → Bool) (j : Fin (k + 1)) : CircuitInstance 2 :=
  (podFormula (fixed 0) (decide (j.val = 0))).toCircuit id

theorem podResidual_wires_le (k : Nat) (fixed : Fin 1 → Bool) (j : Fin (k + 1)) :
    (podResidual k fixed j).wires ≤ 4 := by
  have hW := Circuit.wire_count (podResidual k fixed j).circuit
  have hG := gateCount_toCircuit (podFormula (fixed 0) (decide (j.val = 0))) id
  change (podResidual k fixed j).circuit.gateCount = _ at hG
  rw [hW, hG]
  cases fixed 0 <;> cases decide (j.val = 0) <;> simp [podFormula, gateCount]

theorem source_factored (k : Nat) (fixed : Fin 1 → Bool) (input : Fin (inputCount k) → Bool) :
    ((source k).eval input = true ∧ (source k).circuit.evalWires input ∘ hubBoundary k = fixed) ↔
      ∀ j : Fin (k + 1),
        (podResidual k fixed j).eval (fun s => input (finProdFinEquiv (j, s))) = true := by
  have hEvalSrc : (source k).eval input = (sourceFormula k).eval input := by
    simpa [source, CircuitInstance.eval, Circuit.evalWires] using
      (sourceCompilation k).output_correct input
  have hHubVal : (source k).circuit.evalWires input (hubBoundary k 0) = input (hubCoord k) := by
    simpa [source, hubBoundary, Circuit.evalWires] using
      (sourceCompilation k).preserves input (hubCoord k)
  have hFunEq : ((source k).circuit.evalWires input ∘ hubBoundary k = fixed) ↔
      input (hubCoord k) = fixed 0 := by
    constructor
    · intro h
      have h0 := congrFun h 0
      simpa [Function.comp_apply, hHubVal] using h0
    · intro h
      funext u
      rw [Fin.eq_zero u]
      simpa [Function.comp_apply, hHubVal] using h
  rw [hEvalSrc, hFunEq, sourceFormula, conjPods_eval]
  simp only [repeatPod_eval]
  constructor
  · rintro ⟨hPods, hHub⟩ j
    rw [podResidual, eval_toCircuit]
    have hj := hPods j
    rw [hHub] at hj
    by_cases hj0 : j.val = 0
    · have hjEq : j = 0 := Fin.ext hj0
      subst hjEq
      have hCoord0 : input (finProdFinEquiv (0, 0)) = fixed 0 := hHub
      cases hBit : fixed 0
      · rw [hBit] at hCoord0 hj
        simp at hj
        exact absurd hCoord0 (by rw [hj]; decide)
      · rw [hBit] at hCoord0 hj
        simp at hj
        simp [podFormula, eval, BinaryGate.eval, hCoord0, hj]
    · simp only [hj0, decide_false]
      cases hBit : fixed 0
      · rw [hBit] at hj; simpa [podFormula, eval] using hj
      · rw [hBit] at hj; simpa [podFormula, eval] using hj
  · intro hAll
    have h0 := hAll 0
    rw [podResidual, eval_toCircuit] at h0
    have hHub : input (hubCoord k) = fixed 0 := by
      dsimp only [hubCoord]
      cases hBit : fixed 0
      · simp [hBit, podFormula, eval, BinaryGate.eval] at h0
      · simp [hBit, podFormula, eval, BinaryGate.eval] at h0
        exact h0.1
    refine ⟨fun j => ?_, hHub⟩
    rw [hHub]
    have hj := hAll j
    rw [podResidual, eval_toCircuit] at hj
    by_cases hj0 : j.val = 0
    · simp only [hj0, decide_true] at hj
      cases hBit : fixed 0
      · simp [hBit, podFormula, eval, BinaryGate.eval] at hj
      · simp [hBit, podFormula, eval, BinaryGate.eval] at hj ⊢
        exact hj.2
    · simp only [hj0, decide_false] at hj
      cases hBit : fixed 0 <;> simpa [hBit, podFormula, eval] using hj

/-- Exact 2-branch, `(k + 1)`-factor Sum-of-Products 3-CNF certificate for the `Θ(n ^ 2)`-gate
`source k` family, reducing every factor to at most 4 variables! -/
noncomputable def sopCertificate (k : Nat) : SumOfProductsCertificate (source k) :=
  sopOfFactoredCut (source k) (hubBoundary k) (podResidual k) (source_factored k)

theorem sopCertificate_var_bound (k : Nat) (b : Fin (sopCertificate k).branches)
    (j : Fin ((sopCertificate k).factors b)) :
    (sopCertificate k).vars b j ≤ 4 :=
  podResidual_wires_le k ((cutBranchEquiv 1).symm b) j

/-- Certified subexponential `2 ^ o(n)` log-time budget for exact `#SAT` on the `Θ(n ^ 2)`-gate
`source k` family via 1-wire cut-pinning and Sum-of-Products factoring. -/
theorem sopCertificate_subexponential (C d : ℝ) :
    (fun k => sopLogTimeBudget (inputCount k) 2 (k + 1) 4 C d) =o[atTop]
      fun k => (inputCount k : ℝ) := by
  have hn : Tendsto inputCount atTop atTop :=
    tendsto_atTop_mono (fun k => by simp [inputCount]; omega) tendsto_id
  have hnReal : Tendsto (fun k => (inputCount k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hCut : (fun _ : Nat => ((1 : Nat) : ℝ)) =o[atTop] fun k => (inputCount k : ℝ) :=
    isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp hnReal))
  have hPoly : ∀ᶠ k in atTop, k + 1 ≤ (inputCount k + 2) ^ 1 :=
    Eventually.of_forall fun k => by rw [pow_one]; dsimp [inputCount]; omega
  have hVars : ∀ᶠ k in atTop,
      (4 : ℝ) ≤ 4 * (inputCount k : ℝ) * (Real.log ((inputCount k : ℝ) + 16)) ^ (0 : ℝ) := by
    refine Eventually.of_forall fun k => ?_
    have hInGe2 : (2 : ℝ) ≤ (inputCount k : ℝ) := by
      have : 2 ≤ inputCount k := by simp [inputCount]
      exact_mod_cast this
    rw [Real.rpow_zero]
    linarith
  simpa using factored_cut_sopLogTimeBudget_isLittleO (k := fun _ => 1) (v := fun _ => 4)
    hn hCut 1 hPoly (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) < 1 / 2) hVars C d

end QuadraticHubPods

end PvsNP
