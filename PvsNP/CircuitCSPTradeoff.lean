module

public import PvsNP.CircuitCSP

@[expose] public section

/-!
# Joint `CircuitCSP` Arity/Incidence Tradeoff, Universal Valiant Wall & DAG-Slice Compiler

Closes the remaining gap between variable-count bounds and end-to-end `CircuitCSP` runtime
(variables + incidence + per-constraint gates), proves a universal Valiant arity-vs-cut-size
obstruction across all circuit depths, and constructs a DAG-preserving (non-tree-unrolling)
compiler beating that wall on `DeepSkipChain`:

1. **Joint `CircuitCSP` complexity & sharp $\sqrt{\log n}$ threshold**:
   - `CircuitCSP.maxArity`, `CircuitCSP.maxBinaryGates`, and `cspIncidenceBudget` jointly track
     `vars`, `totalIncidence ≤ constraintCount * maxArity`, and `totalBinaryGates`.
   - `cspIncidenceBudget_isLittleO_of_rpow_log` and `cspArityBudget_isLittleO_of_rpow_log` prove
     `2 ^ o(n)` deterministic runtime whenever `vars + totalIncidence = O(n (log n)^α)` (`α < 1/2`)
     and `totalBinaryGates = poly(n)`.
   - `countingScale_not_isLittleO_of_sqrt_log` and `cspIncidenceBudget_not_isLittleO_of_sqrt_log`
     prove that `Ω(n sqrt(log n))` variables or incidence already exits the `2 ^ o(n)` regime.
2. **Universal Valiant arity-vs-cut-size wall (`valiant_universal_arity_cut_wall`,
   `valiant_quasipoly_arity_wall`, `valiant_poly_arity_wall`)**:
   - Proves `2 * 1 * s / (k - t + 1) ≤ 2 * t * s / k` (`nat_div_valiant_ge_residual`).
   - Consequently, on **every** `Ω(n log n)`-gate circuit family regardless of depth `2 ^ k`, any
     Valiant cut schedule `t ≤ k` achieving residual worst-case CNF/truth-table arity
     `2 ^ (2 ^ (k - t)) ≤ 2 ^ poly(log n)` (in particular any `poly(n)` arity bound) leaves
     `k - t = O(log log n)` and therefore forces cut size outside `O(n (log n)^α)` for all `α < 1`.
3. **DAG-preserving (non-tree-unrolling) `CircuitCSP` compiler (`extractSubDAG`,
   `SliceCSPState`, `dagSliceCSPCertificate`)**:
   - Extracts shared multi-output DAG slices between cut barriers without tree-unrolling
     `2 ^ H` blowup (`binaryGates_le ≤ sliceGateCount`).
4. **Breaking the generic Valiant wall on `DeepSkipChain` (`DeepSkipChain.sliceCertificate`,
   `DeepSkipChain.sliceCertificate_end_to_end_subexponential`)**:
   - Periodic width-`s` cuts of period `P = s * (Nat.log 2 n + s)` keep `vars ≤ 2n + s + 1`,
     `maxArity ≤ max 2 s + 1`, `totalIncidence ≤ (n + s + 2) * (max 2 s + 1)`, and
     `totalBinaryGates = O(n log n)`, achieving end-to-end `cspIncidenceBudget = o(n)` (`2 ^ o(n)`).
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Joint `CircuitCSP` Complexity & Sharp $\sqrt{\log n}$ Incidence Threshold -/

namespace CircuitCSP

private theorem list_mem_le_foldr_max (l : List Nat) {a : Nat} (ha : a ∈ l) :
    a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.foldr_cons]
    rcases ha with rfl | hxs
    · exact Nat.le_max_left _ _
    · exact (ih hxs).trans (Nat.le_max_right _ _)

private theorem list_foldr_max_le (l : List Nat) (B : Nat) (hB : ∀ a ∈ l, a ≤ B) :
    l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨hB x (by simp), ih fun y hy => hB y (by simp [hy])⟩

/-- Maximum variable arity among all local constraints in `csp`. -/
def maxArity {v : Nat} (csp : CircuitCSP v) : Nat :=
  (csp.constraints.map (·.arity)).foldr max 0

/-- Maximum internal binary gate count among all local constraints in `csp`. -/
def maxBinaryGates {v : Nat} (csp : CircuitCSP v) : Nat :=
  (csp.constraints.map fun con => binaryGateCount con.circuit).foldr max 0

theorem arity_le_maxArity {v : Nat} (csp : CircuitCSP v) (con : LocalCircuitConstraint v)
    (hMem : con ∈ csp.constraints) : con.arity ≤ csp.maxArity :=
  list_mem_le_foldr_max _ (List.mem_map.mpr ⟨con, hMem, rfl⟩)

theorem maxArity_le {v : Nat} (csp : CircuitCSP v) (A : Nat)
    (hA : ∀ con ∈ csp.constraints, con.arity ≤ A) : csp.maxArity ≤ A :=
  list_foldr_max_le _ A fun _ ha => by
    obtain ⟨con, hMem, rfl⟩ := List.mem_map.mp ha
    exact hA con hMem

theorem binaryGates_le_maxBinaryGates {v : Nat} (csp : CircuitCSP v)
    (con : LocalCircuitConstraint v) (hMem : con ∈ csp.constraints) :
    binaryGateCount con.circuit ≤ csp.maxBinaryGates :=
  list_mem_le_foldr_max _ (List.mem_map.mpr ⟨con, hMem, rfl⟩)

theorem maxBinaryGates_le {v : Nat} (csp : CircuitCSP v) (G : Nat)
    (hG : ∀ con ∈ csp.constraints, binaryGateCount con.circuit ≤ G) :
    csp.maxBinaryGates ≤ G :=
  list_foldr_max_le _ G fun _ ha => by
    obtain ⟨con, hMem, rfl⟩ := List.mem_map.mp ha
    exact hG con hMem

theorem totalIncidence_le_maxArity {v : Nat} (csp : CircuitCSP v) :
    csp.totalIncidence ≤ csp.constraintCount * csp.maxArity :=
  csp.totalIncidence_le csp.maxArity fun con hMem => csp.arity_le_maxArity con hMem

theorem totalBinaryGates_le_maxBinaryGates {v : Nat} (csp : CircuitCSP v) :
    csp.totalBinaryGates ≤ csp.constraintCount * csp.maxBinaryGates :=
  csp.totalBinaryGates_le csp.maxBinaryGates fun con hMem =>
    csp.binaryGates_le_maxBinaryGates con hMem

end CircuitCSP

/-- Incidence- and encoding-aware log-time budget for solving/counting a `CircuitCSP`:
charges `C * countingScale (vars + totalIncidence)` for the sparsity/incidence solver stage and
`d * log (n + totalBinaryGates + 16)` for polynomial compiler/constraint-evaluation overhead. -/
noncomputable def cspIncidenceBudget (n v inc totalGates : Nat) (C d : ℝ) : ℝ :=
  C * countingScale (v + inc) + d * Real.log ((n : ℝ) + (totalGates : ℝ) + 16)

/-- Any `CircuitCSP` family whose combined variable + incidence count is
`O(n * (log (n + 16)) ^ α)` (`α < 1 / 2`) and whose total binary gate count is polynomial in `n`
achieves `2 ^ o(n)` deterministic exact `#SAT` runtime. -/
theorem cspIncidenceBudget_isLittleO_of_rpow_log {n v inc totalGates : Nat → Nat}
    (hn : Tendsto n atTop atTop) (hBelow : ∀ i, n i ≤ v i + inc i)
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hInc : ∀ᶠ i in atTop,
      ((v i + inc i : Nat) : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    {Cg : ℝ} (hCg : 0 ≤ Cg) {p : Nat}
    (hGates : ∀ᶠ i in atTop, (totalGates i : ℝ) ≤ Cg * ((n i : ℝ) + 16) ^ p)
    (C d : ℝ) :
    (fun i => cspIncidenceBudget (n i) (v i) (inc i) (totalGates i) C d) =o[atTop]
      fun i => (n i : ℝ) := by
  have hScale : (fun i => countingScale (v i + inc i)) =o[atTop] fun i => (n i : ℝ) :=
    countingScale_isLittleO_of_rpow_log hn hBelow hc hα hInc
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnShift
  have hShiftO : (fun i => (n i : ℝ) + 16) =O[atTop] fun i => (n i : ℝ) := by
    refine IsBigO.of_bound 17 ?_
    filter_upwards [hnReal.eventually_ge_atTop 1] with i hi
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    linarith
  have hLogNo : (fun i => Real.log ((n i : ℝ) + 16)) =o[atTop] fun i => (n i : ℝ) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hnShift).trans_isBigO hShiftO
  have hLogPolyO : (fun i => Real.log ((n i : ℝ) + (totalGates i : ℝ) + 16)) =O[atTop]
      fun i => Real.log ((n i : ℝ) + 16) := by
    refine IsBigO.of_bound (|Real.log (Cg + 1)| + ((p : ℝ) + 1)) ?_
    filter_upwards [hGates, hLogN.eventually_ge_atTop 1] with i hGi hLN1
    have hN16 : (1 : ℝ) ≤ (n i : ℝ) + 16 := by linarith [show (0 : ℝ) ≤ (n i : ℝ) by positivity]
    have hPowP : ((n i : ℝ) + 16) ^ p ≤ ((n i : ℝ) + 16) ^ (p + 1) := by
      calc
        ((n i : ℝ) + 16) ^ p = ((n i : ℝ) + 16) ^ p * 1 := (mul_one _).symm
        _ ≤ ((n i : ℝ) + 16) ^ p * ((n i : ℝ) + 16) :=
            mul_le_mul_of_nonneg_left hN16 (by positivity)
        _ = ((n i : ℝ) + 16) ^ (p + 1) := by ring
    have hSumLe : (n i : ℝ) + (totalGates i : ℝ) + 16 ≤
        (Cg + 1) * ((n i : ℝ) + 16) ^ (p + 1) := by
      have hPow1 : (n i : ℝ) + 16 ≤ ((n i : ℝ) + 16) ^ (p + 1) := by
        have hGe : (1 : ℝ) ≤ ((n i : ℝ) + 16) ^ p := one_le_pow₀ hN16
        calc
          (n i : ℝ) + 16 = ((n i : ℝ) + 16) * 1 := (mul_one _).symm
          _ ≤ ((n i : ℝ) + 16) * ((n i : ℝ) + 16) ^ p :=
              mul_le_mul_of_nonneg_left hGe (by positivity)
          _ = ((n i : ℝ) + 16) ^ (p + 1) := by ring
      calc
        (n i : ℝ) + (totalGates i : ℝ) + 16
          ≤ ((n i : ℝ) + 16) + Cg * ((n i : ℝ) + 16) ^ p := by linarith
        _ ≤ ((n i : ℝ) + 16) ^ (p + 1) + Cg * ((n i : ℝ) + 16) ^ (p + 1) := by
            have := mul_le_mul_of_nonneg_left hPowP hCg
            linarith
        _ = (Cg + 1) * ((n i : ℝ) + 16) ^ (p + 1) := by ring
    have hPos1 : 0 < (n i : ℝ) + (totalGates i : ℝ) + 16 := by positivity
    have hLogPos1 : 0 ≤ Real.log ((n i : ℝ) + (totalGates i : ℝ) + 16) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (totalGates i : ℝ) by positivity])
    have hLogLe : Real.log ((n i : ℝ) + (totalGates i : ℝ) + 16) ≤
        Real.log (Cg + 1) + ((p : ℝ) + 1) * Real.log ((n i : ℝ) + 16) := by
      have h1 := Real.log_le_log hPos1 hSumLe
      have hC1Pos : Cg + 1 ≠ 0 := by positivity
      have hPowPos : ((n i : ℝ) + 16) ^ (p + 1) ≠ 0 := by positivity
      rw [Real.log_mul hC1Pos hPowPos, Real.log_pow] at h1
      push_cast at h1
      exact h1
    rw [Real.norm_of_nonneg hLogPos1, Real.norm_of_nonneg (by linarith)]
    have hAbs : Real.log (Cg + 1) ≤ |Real.log (Cg + 1)| * Real.log ((n i : ℝ) + 16) :=
      calc
        Real.log (Cg + 1) ≤ |Real.log (Cg + 1)| := le_abs_self _
        _ = |Real.log (Cg + 1)| * 1 := (mul_one _).symm
        _ ≤ |Real.log (Cg + 1)| * Real.log ((n i : ℝ) + 16) :=
            mul_le_mul_of_nonneg_left hLN1 (abs_nonneg _)
    nlinarith
  have hLogPoly : (fun i => Real.log ((n i : ℝ) + (totalGates i : ℝ) + 16)) =o[atTop]
      fun i => (n i : ℝ) := hLogPolyO.trans_isLittleO hLogNo
  exact (hScale.const_mul_left C).add (hLogPoly.const_mul_left d)

/-- Certificate-level form of `cspIncidenceBudget_isLittleO_of_rpow_log` splitting `vars` and
`constraintCount * maxArity` into separate sub-`sqrt(log n)` bounds. -/
theorem cspArityBudget_isLittleO_of_rpow_log {n : Nat → Nat} {source : ∀ i, CircuitInstance (n i)}
    (cert : ∀ i, CircuitCSPCertificate (source i))
    (hn : Tendsto n atTop atTop) (hBelow : ∀ i, n i ≤ (cert i).vars + (cert i).csp.totalIncidence)
    {c_v α_v c_inc α_inc : ℝ} (hcv : 0 ≤ c_v) (hαv : α_v < 1 / 2)
    (hcinc : 0 ≤ c_inc) (hαinc : α_inc < 1 / 2)
    (hVars : ∀ᶠ i in atTop,
      ((cert i).vars : ℝ) ≤ c_v * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α_v)
    (hArityInc : ∀ᶠ i in atTop,
      (((cert i).csp.constraintCount * (cert i).csp.maxArity : Nat) : ℝ) ≤
        c_inc * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α_inc)
    {Cg : ℝ} (hCg : 0 ≤ Cg) {p : Nat}
    (hGates : ∀ᶠ i in atTop,
      ((cert i).csp.totalBinaryGates : ℝ) ≤ Cg * ((n i : ℝ) + 16) ^ p)
    (C d : ℝ) :
    (fun i => cspIncidenceBudget (n i) (cert i).vars (cert i).csp.totalIncidence
      (cert i).csp.totalBinaryGates C d) =o[atTop] fun i => (n i : ℝ) := by
  let α := max α_v α_inc
  have hα : α < 1 / 2 := max_lt hαv hαinc
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnShift
  have hInc : ∀ᶠ i in atTop,
      (((cert i).vars + (cert i).csp.totalIncidence : Nat) : ℝ) ≤
        (c_v + c_inc) * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α := by
    filter_upwards [hVars, hArityInc, hLogN.eventually_ge_atTop 1] with i hVi hAi hLN1
    have hIncLe : ((cert i).csp.totalIncidence : ℝ) ≤
        (((cert i).csp.constraintCount * (cert i).csp.maxArity : Nat) : ℝ) := by
      exact_mod_cast (cert i).csp.totalIncidence_le_maxArity
    have hPowV : (Real.log ((n i : ℝ) + 16)) ^ α_v ≤ (Real.log ((n i : ℝ) + 16)) ^ α :=
      Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left _ _)
    have hPowI : (Real.log ((n i : ℝ) + 16)) ^ α_inc ≤ (Real.log ((n i : ℝ) + 16)) ^ α :=
      Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_right _ _)
    have h1 : ((cert i).vars : ℝ) ≤ c_v * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α :=
      hVi.trans (mul_le_mul_of_nonneg_left hPowV (by positivity))
    have h2 : ((cert i).csp.totalIncidence : ℝ) ≤
        c_inc * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α :=
      (hIncLe.trans hAi).trans (mul_le_mul_of_nonneg_left hPowI (by positivity))
    push_cast
    linarith
  exact cspIncidenceBudget_isLittleO_of_rpow_log hn hBelow (add_nonneg hcv hcinc) hα hInc
    hCg hGates C d

/-- **Sharp $\sqrt{\log n}$ Scaling Threshold**: whenever `v i = Ω(n i * sqrt (log (n i + 16)))`,
`countingScale (v i)` is **not** `o(n i)` (escaping `2 ^ o(n)` interpolation-scale runtime). -/
theorem countingScale_not_isLittleO_of_sqrt_log {n v : Nat → Nat}
    (hn : Tendsto n atTop atTop) {c : ℝ} (hc : 0 < c)
    (hLower : ∀ᶠ i in atTop,
      c * (n i : ℝ) * Real.sqrt (Real.log ((n i : ℝ) + 16)) ≤ (v i : ℝ)) :
    ¬ ((fun i => countingScale (v i)) =o[atTop] fun i => (n i : ℝ)) := by
  intro hLittleO
  let ε : ℝ := min (c / 4) (1 / 2)
  have hεPos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hBound : ∀ᶠ i in atTop, ‖countingScale (v i)‖ ≤ ε * ‖(n i : ℝ)‖ :=
    hLittleO.bound hεPos
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnShift
  have hVTop : Tendsto (fun i => (v i : ℝ) + 16) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ (hnReal.const_mul_atTop hc)
    filter_upwards [hLower, hLogN.eventually_ge_atTop 1] with i hLi hLN1
    have hSqrt1 : 1 ≤ Real.sqrt (Real.log ((n i : ℝ) + 16)) := by
      simpa using Real.sqrt_le_sqrt hLN1
    have hProd : c * (n i : ℝ) ≤ c * (n i : ℝ) * Real.sqrt (Real.log ((n i : ℝ) + 16)) := by
      have : 0 ≤ c * (n i : ℝ) := by positivity
      exact le_mul_of_one_le_right this hSqrt1
    linarith
  have hLogV : Tendsto (fun i => Real.log ((v i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hVTop
  have hLogLogV : Tendsto (fun i => Real.log (Real.log ((v i : ℝ) + 16))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLogV
  have hSqrt2Le2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hFalse : ∀ᶠ (_i : ℕ) in atTop, False := by
    filter_upwards [hLower, hBound, hnReal.eventually_ge_atTop 16,
      hLogN.eventually_ge_atTop 2, hLogV.eventually_ge_atTop 2,
      hLogLogV.eventually_ge_atTop 1] with i hLi hBi hN16 hLN2 hLV2 hLLV1
    have hV16Pos : (0 : ℝ) < (v i : ℝ) + 16 := by positivity
    have hSqrtLVPos : 0 < Real.sqrt (Real.log ((v i : ℝ) + 16)) :=
      Real.sqrt_pos.mpr (by linarith)
    have hSqrtLNPos : 0 < Real.sqrt (Real.log ((n i : ℝ) + 16)) :=
      Real.sqrt_pos.mpr (by linarith)
    have hScaleNonneg : 0 ≤ countingScale (v i) := by
      unfold countingScale
      positivity
    have hNormB : countingScale (v i) ≤ ε * (n i : ℝ) := by
      simpa [Real.norm_of_nonneg hScaleNonneg,
        Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n i : ℝ))] using hBi
    have hScaleGe : (v i : ℝ) / Real.sqrt (Real.log ((v i : ℝ) + 16)) ≤ countingScale (v i) := by
      unfold countingScale
      have hSqGe1 : 1 ≤ (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 := by nlinarith
      have hMul : (v i : ℝ) * 1 ≤ (v i : ℝ) * (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 :=
        mul_le_mul_of_nonneg_left hSqGe1 (by positivity)
      rw [mul_one] at hMul
      exact div_le_div_of_nonneg_right hMul hSqrtLVPos.le
    by_cases hVSmall : (v i : ℝ) + 16 ≤ ((n i : ℝ) + 16) ^ 2
    · have hLogVLe : Real.log ((v i : ℝ) + 16) ≤ 2 * Real.log ((n i : ℝ) + 16) := by
        have h1 := Real.log_le_log hV16Pos hVSmall
        rw [Real.log_pow] at h1
        push_cast at h1
        exact h1
      have hSqrtVLe : Real.sqrt (Real.log ((v i : ℝ) + 16)) ≤
          2 * Real.sqrt (Real.log ((n i : ℝ) + 16)) := by
        calc
          Real.sqrt (Real.log ((v i : ℝ) + 16))
            ≤ Real.sqrt (2 * Real.log ((n i : ℝ) + 16)) := Real.sqrt_le_sqrt hLogVLe
          _ = Real.sqrt 2 * Real.sqrt (Real.log ((n i : ℝ) + 16)) :=
              Real.sqrt_mul (by norm_num) _
          _ ≤ 2 * Real.sqrt (Real.log ((n i : ℝ) + 16)) :=
              mul_le_mul_of_nonneg_right hSqrt2Le2 hSqrtLNPos.le
      have hDivGe : (c / 2) * (n i : ℝ) ≤ (v i : ℝ) / Real.sqrt (Real.log ((v i : ℝ) + 16)) := by
        rw [le_div_iff₀ hSqrtLVPos]
        calc
          (c / 2) * (n i : ℝ) * Real.sqrt (Real.log ((v i : ℝ) + 16))
            ≤ (c / 2) * (n i : ℝ) * (2 * Real.sqrt (Real.log ((n i : ℝ) + 16))) :=
                mul_le_mul_of_nonneg_left hSqrtVLe (by positivity)
          _ = c * (n i : ℝ) * Real.sqrt (Real.log ((n i : ℝ) + 16)) := by ring
          _ ≤ (v i : ℝ) := hLi
      have hEpsLe : ε ≤ c / 4 := min_le_left _ _
      nlinarith
    · have hVLt : ((n i : ℝ) + 16) ^ 2 < (v i : ℝ) + 16 := lt_of_not_ge hVSmall
      have hLogVLeV : Real.log ((v i : ℝ) + 16) ≤ (v i : ℝ) + 16 :=
        (Real.log_le_sub_one_of_pos hV16Pos).trans (by linarith)
      have hSqrtVLeV : Real.sqrt (Real.log ((v i : ℝ) + 16)) ≤ Real.sqrt ((v i : ℝ) + 16) :=
        Real.sqrt_le_sqrt hLogVLeV
      have hSqrtVPos : 0 < Real.sqrt ((v i : ℝ) + 16) := Real.sqrt_pos.mpr hV16Pos
      have hVHalf : ((v i : ℝ) + 16) / 2 ≤ (v i : ℝ) := by
        have : (1024 : ℝ) ≤ ((n i : ℝ) + 16) ^ 2 := by nlinarith
        linarith
      have hSqrtGtN : (n i : ℝ) + 16 < Real.sqrt ((v i : ℝ) + 16) :=
        Real.lt_sqrt_of_sq_lt hVLt
      have hDivGe : Real.sqrt ((v i : ℝ) + 16) / 2 ≤
          (v i : ℝ) / Real.sqrt (Real.log ((v i : ℝ) + 16)) := by
        rw [le_div_iff₀ hSqrtLVPos]
        calc
          Real.sqrt ((v i : ℝ) + 16) / 2 * Real.sqrt (Real.log ((v i : ℝ) + 16))
            ≤ Real.sqrt ((v i : ℝ) + 16) / 2 * Real.sqrt ((v i : ℝ) + 16) :=
                mul_le_mul_of_nonneg_left hSqrtVLeV (by positivity)
          _ = (Real.sqrt ((v i : ℝ) + 16)) ^ 2 / 2 := by ring
          _ = ((v i : ℝ) + 16) / 2 := by rw [Real.sq_sqrt hV16Pos.le]
          _ ≤ (v i : ℝ) := hVHalf
      have hEpsLe : ε ≤ 1 / 2 := min_le_right _ _
      nlinarith
  obtain ⟨_, h⟩ := hFalse.exists
  exact h

/-- If a `CircuitCSP` family retains `totalIncidence i ≥ c * n i * sqrt (log (n i + 16))`, then
its positive `cspIncidenceBudget` fails `2 ^ o(n)` runtime. -/
theorem cspIncidenceBudget_not_isLittleO_of_sqrt_log {n v inc totalGates : Nat → Nat}
    (hn : Tendsto n atTop atTop) {c : ℝ} (hc : 0 < c)
    (hLower : ∀ᶠ i in atTop,
      c * (n i : ℝ) * Real.sqrt (Real.log ((n i : ℝ) + 16)) ≤ (inc i : ℝ))
    {C d : ℝ} (hC : 0 < C) (hd : 0 ≤ d) :
    ¬ ((fun i => cspIncidenceBudget (n i) (v i) (inc i) (totalGates i) C d) =o[atTop]
      fun i => (n i : ℝ)) := by
  intro hBud
  have hIncSum : ∀ᶠ i in atTop,
      c * (n i : ℝ) * Real.sqrt (Real.log ((n i : ℝ) + 16)) ≤ ((v i + inc i : Nat) : ℝ) := by
    filter_upwards [hLower] with i hi
    push_cast
    linarith [show (0 : ℝ) ≤ (v i : ℝ) by positivity]
  have hScaleO : (fun i => countingScale (v i + inc i)) =o[atTop] fun i => (n i : ℝ) := by
    have hVTop : Tendsto (fun i => ((v i + inc i : Nat) : ℝ) + 16) atTop atTop := by
      have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hn
      have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
        tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
      have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
        Real.tendsto_log_atTop.comp hnShift
      refine tendsto_atTop_mono' atTop ?_ (hnReal.const_mul_atTop hc)
      filter_upwards [hIncSum, hLogN.eventually_ge_atTop 1] with i hi hLN1
      have hSqrt1 : 1 ≤ Real.sqrt (Real.log ((n i : ℝ) + 16)) := by
        simpa using Real.sqrt_le_sqrt hLN1
      have hProd : c * (n i : ℝ) ≤
          c * (n i : ℝ) * Real.sqrt (Real.log ((n i : ℝ) + 16)) :=
        le_mul_of_one_le_right (by positivity) hSqrt1
      linarith
    have hLogV := Real.tendsto_log_atTop.comp hVTop
    have hBig : (fun i => C * countingScale (v i + inc i)) =O[atTop]
        fun i => cspIncidenceBudget (n i) (v i) (inc i) (totalGates i) C d := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [hLogV.eventually_ge_atTop 1] with i hLV1
      have hCSNonneg : 0 ≤ countingScale (v i + inc i) := by
        unfold countingScale
        have hLLV : 0 ≤ Real.log (Real.log (((v i + inc i : Nat) : ℝ) + 16)) :=
          Real.log_nonneg hLV1
        positivity
      have hDLog : 0 ≤ d * Real.log ((n i : ℝ) + (totalGates i : ℝ) + 16) := by
        have hGe1 : (1 : ℝ) ≤ (n i : ℝ) + (totalGates i : ℝ) + 16 := by
          linarith [show (0 : ℝ) ≤ (n i : ℝ) by positivity,
            show (0 : ℝ) ≤ (totalGates i : ℝ) by positivity]
        exact mul_nonneg hd (Real.log_nonneg hGe1)
      have hMulNonneg : 0 ≤ C * countingScale (v i + inc i) := mul_nonneg hC.le hCSNonneg
      have hSumNonneg : 0 ≤ C * countingScale (v i + inc i) +
          d * Real.log ((n i : ℝ) + (totalGates i : ℝ) + 16) := add_nonneg hMulNonneg hDLog
      unfold cspIncidenceBudget
      rw [Real.norm_of_nonneg hMulNonneg, Real.norm_of_nonneg hSumNonneg]
      linarith
    have hScaled := hBig.trans_isLittleO hBud
    have hDiv := hScaled.const_mul_left (C⁻¹)
    simpa [mul_assoc, hC.ne'] using hDiv
  exact countingScale_not_isLittleO_of_sqrt_log hn hc hIncSum hScaleO

/-! ### 2. Universal Valiant Arity-vs-Cut-Size Wall (All Circuit Depths) -/

/-- Pure `Nat` monotonicity identity showing why cutting down to `r = k - t` residual depth
bits costs at least as much as a single-bit Valiant cut on depth `2 ^ (r + 1)`. -/
theorem nat_div_valiant_ge_residual (s k t : Nat) (hk : 0 < k) (ht : 1 ≤ t) (htLe : t ≤ k) :
    2 * 1 * s / (k - t + 1) ≤ 2 * t * s / k := by
  have hkLe : k ≤ t * (k - t + 1) := by
    have hSum : k = t + (k - t) := by omega
    nlinarith
  let q := 2 * 1 * s / (k - t + 1)
  have hQMul : q * (k - t + 1) ≤ 2 * 1 * s := Nat.div_mul_le_self _ _
  have hMul : q * k ≤ 2 * t * s := by
    calc
      q * k ≤ q * (t * (k - t + 1)) := Nat.mul_le_mul_left q hkLe
      _ = t * (q * (k - t + 1)) := by ring
      _ ≤ t * (2 * 1 * s) := Nat.mul_le_mul_left t hQMul
      _ = 2 * t * s := by ring
  exact (Nat.le_div_iff_mul_le hk).mpr hMul

/-- **Universal Valiant Arity-vs-Cut-Size Wall**: on *any* `Ω(n log n)`-gate circuit family
(regardless of depth `2 ^ k`), **no** Valiant cut schedule `t ≤ k` can keep both the residual
bit-depth `k - t = O(log log n)` and the cut variable budget `2 * t * s / k + 1 = O(n (log n)^α)`
for any `α < 1`. -/
theorem valiant_universal_arity_cut_wall {n s k t : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hk : ∀ i, 0 < k i) (ht : ∀ i, 1 ≤ t i) (htLe : ∀ i, t i ≤ k i)
    {c_g c_r d_r : ℝ} (hcg : 0 < c_g) (hcr : 0 ≤ c_r)
    (hGates : ∀ᶠ i in atTop, c_g * (n i : ℝ) * Real.log ((n i : ℝ) + 16) ≤ (s i : ℝ))
    (hRem : ∀ᶠ i in atTop,
      ((k i - t i : Nat) : ℝ) ≤ c_r * Real.log (Real.log ((n i : ℝ) + 16)) + d_r)
    (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((2 * t i * s i / k i + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α) := by
  intro hEv
  let k' : Nat → Nat := fun i => k i - t i + 1
  let t' : Nat → Nat := fun _ => 1
  have hRemK' : ∀ᶠ i in atTop,
      (k' i : ℝ) ≤ c_r * Real.log (Real.log ((n i : ℝ) + 16)) + (d_r + 1) := by
    filter_upwards [hRem] with i hi
    dsimp [k']
    push_cast
    linarith
  have hEv' : ∀ᶠ i in atTop,
      ((2 * t' i * s i / k' i + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α := by
    filter_upwards [hEv] with i hi
    have hNat : 2 * t' i * s i / k' i + 1 ≤ 2 * t i * s i / k i + 1 :=
      Nat.add_le_add_right (nat_div_valiant_ge_residual (s i) (k i) (t i) (hk i) (ht i) (htLe i)) 1
    have hCast : ((2 * t' i * s i / k' i + 1 : Nat) : ℝ) ≤
        ((2 * t i * s i / k i + 1 : Nat) : ℝ) := by exact_mod_cast hNat
    exact hCast.trans hi
  exact valiant_shallow_nlogn_wall hn (fun _ => Nat.succ_pos _) (fun _ => le_rfl)
    hcg hcr hGates hRemK' c α hα hEv'

/-- Any Valiant cut schedule `t ≤ k` keeping the worst-case block arity bound `2 ^ (2 ^ (k - t))`
at most quasi-polynomial `2 ^ (c_a * (log n)^B)` forces the Valiant cut budget outside
`O(n (log n)^α)` for all `α < 1`. -/
theorem valiant_quasipoly_arity_wall {n s k t : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hk : ∀ i, 0 < k i) (ht : ∀ i, 1 ≤ t i) (htLe : ∀ i, t i ≤ k i)
    {c_g c_a B : ℝ} (hcg : 0 < c_g) (hca : 0 < c_a) (hB : 0 ≤ B)
    (hGates : ∀ᶠ i in atTop, c_g * (n i : ℝ) * Real.log ((n i : ℝ) + 16) ≤ (s i : ℝ))
    (hArity : ∀ᶠ i in atTop,
      ((2 ^ (k i - t i) : Nat) : ℝ) ≤ c_a * (Real.log ((n i : ℝ) + 16)) ^ B)
    (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((2 * t i * s i / k i + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α) := by
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnShift
  have hRem : ∀ᶠ i in atTop,
      ((k i - t i : Nat) : ℝ) ≤
        (B / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) + Real.log c_a / Real.log 2 := by
    filter_upwards [hArity, hLogN.eventually_ge_atTop 2] with i hAi hLN2
    have hPowPos : 0 < ((2 ^ (k i - t i) : Nat) : ℝ) := by positivity
    have hLNPos : 0 < Real.log ((n i : ℝ) + 16) := by linarith
    have hLog := Real.log_le_log hPowPos hAi
    have hLhs : Real.log ((2 ^ (k i - t i) : Nat) : ℝ) =
        ((k i - t i : Nat) : ℝ) * Real.log 2 := by
      push_cast
      exact Real.log_pow 2 (k i - t i)
    have hCaNe : c_a ≠ 0 := hca.ne'
    have hPowNe : (Real.log ((n i : ℝ) + 16)) ^ B ≠ 0 := (Real.rpow_pos_of_pos hLNPos B).ne'
    rw [hLhs, Real.log_mul hCaNe hPowNe, Real.log_rpow hLNPos] at hLog
    calc
      ((k i - t i : Nat) : ℝ)
        ≤ (Real.log c_a + B * Real.log (Real.log ((n i : ℝ) + 16))) / Real.log 2 :=
            (le_div_iff₀ hLog2Pos).mpr hLog
      _ = (B / Real.log 2) * Real.log (Real.log ((n i : ℝ) + 16)) +
            Real.log c_a / Real.log 2 := by ring
  exact valiant_universal_arity_cut_wall hn hk ht htLe hcg (div_nonneg hB hLog2Pos.le)
    hGates hRem c α hα

/-- In particular, **no** Valiant cut schedule `t ≤ k` on an `Ω(n log n)`-gate circuit family
can simultaneously keep the worst-case Valiant constraint arity polynomial (`2 ^ (2 ^ (k - t)) ≤
(n + 16) ^ p`) and cut size in `O(n (log n)^α)` (`α < 1`). -/
theorem valiant_poly_arity_wall {n s k t : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hk : ∀ i, 0 < k i) (ht : ∀ i, 1 ≤ t i) (htLe : ∀ i, t i ≤ k i)
    {c_g : ℝ} (hcg : 0 < c_g) {p : Nat} (hp : 1 ≤ p)
    (hGates : ∀ᶠ i in atTop, c_g * (n i : ℝ) * Real.log ((n i : ℝ) + 16) ≤ (s i : ℝ))
    (hPolyArity : ∀ᶠ i in atTop, ((2 ^ (2 ^ (k i - t i)) : Nat) : ℝ) ≤ ((n i : ℝ) + 16) ^ p)
    (c α : ℝ) (hα : α < 1) :
    ¬ (∀ᶠ i in atTop,
      ((2 * t i * s i / k i + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α) := by
  have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hArity : ∀ᶠ i in atTop,
      ((2 ^ (k i - t i) : Nat) : ℝ) ≤
        ((p : ℝ) / Real.log 2) * (Real.log ((n i : ℝ) + 16)) ^ (1 : ℝ) := by
    filter_upwards [hPolyArity] with i hPi
    have hPowPos : 0 < ((2 ^ (2 ^ (k i - t i)) : Nat) : ℝ) := by positivity
    have hLog := Real.log_le_log hPowPos hPi
    have hLhs : Real.log ((2 ^ (2 ^ (k i - t i)) : Nat) : ℝ) =
        ((2 ^ (k i - t i) : Nat) : ℝ) * Real.log 2 := by
      have hCast : ((2 ^ (2 ^ (k i - t i)) : Nat) : ℝ) = (2 : ℝ) ^ (2 ^ (k i - t i)) := by
        push_cast; rfl
      rw [hCast, Real.log_pow]
    rw [hLhs, Real.log_pow] at hLog
    rw [Real.rpow_one]
    calc
      ((2 ^ (k i - t i) : Nat) : ℝ)
        ≤ ((p : ℝ) * Real.log ((n i : ℝ) + 16)) / Real.log 2 := (le_div_iff₀ hLog2Pos).mpr hLog
      _ = ((p : ℝ) / Real.log 2) * Real.log ((n i : ℝ) + 16) := by ring
  have hpPos : 0 < ((p : ℝ) / Real.log 2) := div_pos (by exact_mod_cast hp) hLog2Pos
  exact valiant_quasipoly_arity_wall hn hk ht htLe hcg hpPos (by norm_num) hGates hArity c α hα

/-! ### 3. Universal DAG-Preserving (Non-Tree-Unrolling) `CircuitCSP` Compiler -/

/-- Closedness condition for extracting a shared multi-output DAG slice between `findAnchor`
(cut barrier / input anchors) and `inSlice` (gates inside the slice). -/
def GatePredecessorClosed {n arity : Nat} :
    {w : Nat} → Circuit n w → (Fin w → Option (Fin arity)) → (Fin w → Bool) → Prop
  | _, .inputsOnly, findAnchor, inSlice =>
    ∀ u : Fin n, inSlice u = true → (findAnchor u).isSome
  | w + 1, .snoc earlier g, findAnchor, inSlice =>
    GatePredecessorClosed earlier (findAnchor ∘ Fin.castSucc) (inSlice ∘ Fin.castSucc) ∧
    (findAnchor (Fin.last w) = none → inSlice (Fin.last w) = true →
      match g with
      | .not a => (findAnchor a.castSucc).isSome ∨ inSlice a.castSucc = true
      | .and a b =>
        ((findAnchor a.castSucc).isSome ∨ inSlice a.castSucc = true) ∧
        ((findAnchor b.castSucc).isSome ∨ inSlice b.castSucc = true)
      | .or a b =>
        ((findAnchor a.castSucc).isSome ∨ inSlice a.castSucc = true) ∧
        ((findAnchor b.castSucc).isSome ∨ inSlice b.castSucc = true))

/-- Result of extracting a shared fan-in-2 sub-DAG from `c : Circuit n w` anchored at
`anchorVar : Fin arity → Fin v` with binary gates bounded by the number of slice gates. -/
structure SubDAGBuild {n w v arity : Nat} (c : Circuit n w) (anchorVar : Fin arity → Fin v)
    (findAnchor : Fin w → Option (Fin arity)) (inSlice : Fin w → Bool)
    (liftAssign : (Fin n → Bool) → (Fin v → Bool)) where
  localWires : Nat
  circuit : Circuit arity localWires
  inputWire : Fin arity → Fin localWires
  inputWire_eval : ∀ x i, circuit.evalWires x (inputWire i) = x i
  binaryGates_le : binaryGateCount circuit ≤
    (Finset.univ.filter fun u : Fin w => n ≤ u.val ∧ findAnchor u = none ∧ inSlice u = true).card
  wireMap : Fin w → Option (Fin localWires)
  wireMap_some : ∀ u, ((findAnchor u).isSome ∨ inSlice u = true) → (wireMap u).isSome
  wireMap_eval : ∀ x u lw, wireMap u = some lw →
    circuit.evalWires (fun i => liftAssign x (anchorVar i)) lw = c.evalWires x u

theorem card_slice_filter_castSucc_le {n w arity : Nat}
    (findAnchor : Fin (w + 1) → Option (Fin arity)) (inSlice : Fin (w + 1) → Bool) :
    (Finset.univ.filter fun q : Fin w =>
      n ≤ q.val ∧ (findAnchor ∘ Fin.castSucc) q = none ∧ (inSlice ∘ Fin.castSucc) q = true).card ≤
      (Finset.univ.filter fun u : Fin (w + 1) =>
        n ≤ u.val ∧ findAnchor u = none ∧ inSlice u = true).card := by
  refine Finset.card_le_card_of_injOn Fin.castSucc ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, Fin.val_castSucc] at hq ⊢
    exact hq
  · intro q₁ _ q₂ _ hEq
    exact Fin.castSucc_injective w hEq

theorem card_slice_filter_castSucc_add_one_le {n w arity : Nat}
    (findAnchor : Fin (w + 1) → Option (Fin arity)) (inSlice : Fin (w + 1) → Bool)
    (hGe : n ≤ w) (hAnc : findAnchor (Fin.last w) = none) (hIn : inSlice (Fin.last w) = true) :
    (Finset.univ.filter fun q : Fin w =>
      n ≤ q.val ∧ (findAnchor ∘ Fin.castSucc) q = none ∧ (inSlice ∘ Fin.castSucc) q = true).card + 1 ≤
      (Finset.univ.filter fun u : Fin (w + 1) =>
        n ≤ u.val ∧ findAnchor u = none ∧ inSlice u = true).card := by
  let S := Finset.univ.filter fun u : Fin (w + 1) =>
    n ≤ u.val ∧ findAnchor u = none ∧ inSlice u = true
  let S₀ := (Finset.univ.filter fun q : Fin w =>
    n ≤ q.val ∧ (findAnchor ∘ Fin.castSucc) q = none ∧ (inSlice ∘ Fin.castSucc) q = true).image
      Fin.castSucc
  have hSub : insert (Fin.last w) S₀ ⊆ S := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, S₀, S] at hu ⊢
    rcases hu with rfl | ⟨q, hPq, rfl⟩
    · exact ⟨hGe, hAnc, hIn⟩
    · exact hPq
  have hNotMem : Fin.last w ∉ S₀ := by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S₀, not_exists,
      not_and]
    intro q _ hEq
    exact Fin.castSucc_ne_last q hEq
  have hCard0 : S₀.card = (Finset.univ.filter fun q : Fin w =>
      n ≤ q.val ∧ (findAnchor ∘ Fin.castSucc) q = none ∧ (inSlice ∘ Fin.castSucc) q = true).card :=
    Finset.card_image_of_injective _ (Fin.castSucc_injective w)
  have hCard1 := Finset.card_le_card hSub
  rw [Finset.card_insert_of_notMem hNotMem, hCard0] at hCard1
  exact hCard1

/-- Extracts a **shared** fan-in-2 sub-DAG from `c` without tree-unrolling duplication: every
internal wire inside `inSlice` is emitted at most once in topological order. -/
def extractSubDAG {n v arity : Nat} (anchorVar : Fin arity → Fin v)
    (liftAssign : (Fin n → Bool) → (Fin v → Bool)) :
    {w : Nat} → (c : Circuit n w) →
    (findAnchor : Fin w → Option (Fin arity)) → (inSlice : Fin w → Bool) →
    (hAnchorEval : ∀ x u i, findAnchor u = some i → liftAssign x (anchorVar i) = c.evalWires x u) →
    GatePredecessorClosed c findAnchor inSlice →
    SubDAGBuild c anchorVar findAnchor inSlice liftAssign
  | _, .inputsOnly, findAnchor, _inSlice, hAnchorEval, hClosed =>
    { localWires := arity
      circuit := Circuit.inputsOnly
      inputWire := fun i => i
      inputWire_eval := fun _ _ => rfl
      binaryGates_le := by simp [binaryGateCount, unhitBinaryGates]
      wireMap := findAnchor
      wireMap_some := fun u hu => by
        rcases hu with hSome | hIn
        · exact hSome
        · exact hClosed u hIn
      wireMap_eval := fun x u lw hEq => hAnchorEval x u lw hEq }
  | w + 1, .snoc earlier (.not a), findAnchor, inSlice, hAnchorEval, hClosed =>
    let prev := extractSubDAG anchorVar liftAssign earlier
      (findAnchor ∘ Fin.castSucc) (inSlice ∘ Fin.castSucc)
      (fun x q i hq => by
        simpa [Circuit.evalWires, Fin.snoc_castSucc] using hAnchorEval x q.castSucc i hq)
      hClosed.1
    match hAnc : findAnchor (Fin.last w) with
    | some idx =>
      { localWires := prev.localWires
        circuit := prev.circuit
        inputWire := prev.inputWire
        inputWire_eval := prev.inputWire_eval
        binaryGates_le := prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
        wireMap := Fin.lastCases (some (prev.inputWire idx)) prev.wireMap
        wireMap_some := fun u hu => by
          cases u using Fin.lastCases with
          | last => simp
          | cast q =>
            rw [Fin.lastCases_castSucc]
            exact prev.wireMap_some q (by simpa using hu)
        wireMap_eval := fun x u lw hEq => by
          cases u using Fin.lastCases with
          | last =>
            rw [Fin.lastCases_last] at hEq
            injection hEq with hLw
            rw [← hLw, prev.inputWire_eval]
            exact hAnchorEval x (Fin.last w) idx hAnc
          | cast q =>
            rw [Fin.lastCases_castSucc] at hEq
            simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireMap_eval x q lw hEq }
    | none =>
      if hIn : inSlice (Fin.last w) = true then
        have hSomeA : (prev.wireMap a).isSome :=
          prev.wireMap_some a (hClosed.2 hAnc hIn)
        let la := (prev.wireMap a).get hSomeA
        let newC := prev.circuit.snoc (.not la)
        { localWires := prev.localWires + 1
          circuit := newC
          inputWire := fun i => (prev.inputWire i).castSucc
          inputWire_eval := fun x i => by
            simp only [newC, Circuit.evalWires, Fin.snoc_castSucc, prev.inputWire_eval]
          binaryGates_le := by
            have hBinEq : binaryGateCount newC = binaryGateCount prev.circuit := by
              dsimp [newC, binaryGateCount, unhitBinaryGates]; rfl
            rw [hBinEq]
            exact prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
          wireMap := Fin.lastCases (some (Fin.last prev.localWires))
            (fun q => (prev.wireMap q).map Fin.castSucc)
          wireMap_some := fun u hu => by
            cases u using Fin.lastCases with
            | last => simp
            | cast q =>
              rw [Fin.lastCases_castSucc]
              simp only [Option.isSome_map]
              exact prev.wireMap_some q (by simpa using hu)
          wireMap_eval := fun x u lw hEq => by
            cases u using Fin.lastCases with
            | last =>
              rw [Fin.lastCases_last] at hEq
              injection hEq with hLw
              rw [← hLw]
              have hEvA := prev.wireMap_eval x a la (Option.some_get hSomeA).symm
              simp only [newC, Circuit.evalWires, Gate.eval, Fin.snoc_last, hEvA]
            | cast q =>
              rw [Fin.lastCases_castSucc] at hEq
              rcases Option.map_eq_some_iff.mp hEq with ⟨lw0, hMap0, rfl⟩
              simpa [newC, Circuit.evalWires, Fin.snoc_castSucc] using
                prev.wireMap_eval x q lw0 hMap0 }
      else
        { localWires := prev.localWires
          circuit := prev.circuit
          inputWire := prev.inputWire
          inputWire_eval := prev.inputWire_eval
          binaryGates_le := prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
          wireMap := Fin.lastCases none prev.wireMap
          wireMap_some := fun u hu => by
            cases u using Fin.lastCases with
            | last =>
              exfalso
              rcases hu with hSome | hTrue
              · simp [hAnc] at hSome
              · exact hIn hTrue
            | cast q =>
              rw [Fin.lastCases_castSucc]
              exact prev.wireMap_some q (by simpa using hu)
          wireMap_eval := fun x u lw hEq => by
            cases u using Fin.lastCases with
            | last => simp at hEq
            | cast q =>
              rw [Fin.lastCases_castSucc] at hEq
              simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireMap_eval x q lw hEq }
  | w + 1, .snoc earlier (.and a b), findAnchor, inSlice, hAnchorEval, hClosed =>
    let prev := extractSubDAG anchorVar liftAssign earlier
      (findAnchor ∘ Fin.castSucc) (inSlice ∘ Fin.castSucc)
      (fun x q i hq => by
        simpa [Circuit.evalWires, Fin.snoc_castSucc] using hAnchorEval x q.castSucc i hq)
      hClosed.1
    match hAnc : findAnchor (Fin.last w) with
    | some idx =>
      { localWires := prev.localWires
        circuit := prev.circuit
        inputWire := prev.inputWire
        inputWire_eval := prev.inputWire_eval
        binaryGates_le := prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
        wireMap := Fin.lastCases (some (prev.inputWire idx)) prev.wireMap
        wireMap_some := fun u hu => by
          cases u using Fin.lastCases with
          | last => simp
          | cast q =>
            rw [Fin.lastCases_castSucc]
            exact prev.wireMap_some q (by simpa using hu)
        wireMap_eval := fun x u lw hEq => by
          cases u using Fin.lastCases with
          | last =>
            rw [Fin.lastCases_last] at hEq
            injection hEq with hLw
            rw [← hLw, prev.inputWire_eval]
            exact hAnchorEval x (Fin.last w) idx hAnc
          | cast q =>
            rw [Fin.lastCases_castSucc] at hEq
            simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireMap_eval x q lw hEq }
    | none =>
      if hIn : inSlice (Fin.last w) = true then
        have hPred := hClosed.2 hAnc hIn
        have hSomeA : (prev.wireMap a).isSome := prev.wireMap_some a hPred.1
        have hSomeB : (prev.wireMap b).isSome := prev.wireMap_some b hPred.2
        let la := (prev.wireMap a).get hSomeA
        let lb := (prev.wireMap b).get hSomeB
        let newC := prev.circuit.snoc (.and la lb)
        { localWires := prev.localWires + 1
          circuit := newC
          inputWire := fun i => (prev.inputWire i).castSucc
          inputWire_eval := fun x i => by
            simp only [newC, Circuit.evalWires, Fin.snoc_castSucc, prev.inputWire_eval]
          binaryGates_le := by
            have hBinEq : binaryGateCount newC = binaryGateCount prev.circuit + 1 := by
              dsimp [newC, binaryGateCount, unhitBinaryGates]
            rw [hBinEq]
            exact (Nat.add_le_add_right prev.binaryGates_le 1).trans
              (card_slice_filter_castSucc_add_one_le findAnchor inSlice earlier.inputs_le_wires hAnc hIn)
          wireMap := Fin.lastCases (some (Fin.last prev.localWires))
            (fun q => (prev.wireMap q).map Fin.castSucc)
          wireMap_some := fun u hu => by
            cases u using Fin.lastCases with
            | last => simp
            | cast q =>
              rw [Fin.lastCases_castSucc]
              simp only [Option.isSome_map]
              exact prev.wireMap_some q (by simpa using hu)
          wireMap_eval := fun x u lw hEq => by
            cases u using Fin.lastCases with
            | last =>
              rw [Fin.lastCases_last] at hEq
              injection hEq with hLw
              rw [← hLw]
              have hEvA := prev.wireMap_eval x a la (Option.some_get hSomeA).symm
              have hEvB := prev.wireMap_eval x b lb (Option.some_get hSomeB).symm
              simp only [newC, Circuit.evalWires, Gate.eval, Fin.snoc_last, hEvA, hEvB]
            | cast q =>
              rw [Fin.lastCases_castSucc] at hEq
              rcases Option.map_eq_some_iff.mp hEq with ⟨lw0, hMap0, rfl⟩
              simpa [newC, Circuit.evalWires, Fin.snoc_castSucc] using
                prev.wireMap_eval x q lw0 hMap0 }
      else
        { localWires := prev.localWires
          circuit := prev.circuit
          inputWire := prev.inputWire
          inputWire_eval := prev.inputWire_eval
          binaryGates_le := prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
          wireMap := Fin.lastCases none prev.wireMap
          wireMap_some := fun u hu => by
            cases u using Fin.lastCases with
            | last =>
              exfalso
              rcases hu with hSome | hTrue
              · simp [hAnc] at hSome
              · exact hIn hTrue
            | cast q =>
              rw [Fin.lastCases_castSucc]
              exact prev.wireMap_some q (by simpa using hu)
          wireMap_eval := fun x u lw hEq => by
            cases u using Fin.lastCases with
            | last => simp at hEq
            | cast q =>
              rw [Fin.lastCases_castSucc] at hEq
              simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireMap_eval x q lw hEq }
  | w + 1, .snoc earlier (.or a b), findAnchor, inSlice, hAnchorEval, hClosed =>
    let prev := extractSubDAG anchorVar liftAssign earlier
      (findAnchor ∘ Fin.castSucc) (inSlice ∘ Fin.castSucc)
      (fun x q i hq => by
        simpa [Circuit.evalWires, Fin.snoc_castSucc] using hAnchorEval x q.castSucc i hq)
      hClosed.1
    match hAnc : findAnchor (Fin.last w) with
    | some idx =>
      { localWires := prev.localWires
        circuit := prev.circuit
        inputWire := prev.inputWire
        inputWire_eval := prev.inputWire_eval
        binaryGates_le := prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
        wireMap := Fin.lastCases (some (prev.inputWire idx)) prev.wireMap
        wireMap_some := fun u hu => by
          cases u using Fin.lastCases with
          | last => simp
          | cast q =>
            rw [Fin.lastCases_castSucc]
            exact prev.wireMap_some q (by simpa using hu)
        wireMap_eval := fun x u lw hEq => by
          cases u using Fin.lastCases with
          | last =>
            rw [Fin.lastCases_last] at hEq
            injection hEq with hLw
            rw [← hLw, prev.inputWire_eval]
            exact hAnchorEval x (Fin.last w) idx hAnc
          | cast q =>
            rw [Fin.lastCases_castSucc] at hEq
            simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireMap_eval x q lw hEq }
    | none =>
      if hIn : inSlice (Fin.last w) = true then
        have hPred := hClosed.2 hAnc hIn
        have hSomeA : (prev.wireMap a).isSome := prev.wireMap_some a hPred.1
        have hSomeB : (prev.wireMap b).isSome := prev.wireMap_some b hPred.2
        let la := (prev.wireMap a).get hSomeA
        let lb := (prev.wireMap b).get hSomeB
        let newC := prev.circuit.snoc (.or la lb)
        { localWires := prev.localWires + 1
          circuit := newC
          inputWire := fun i => (prev.inputWire i).castSucc
          inputWire_eval := fun x i => by
            simp only [newC, Circuit.evalWires, Fin.snoc_castSucc, prev.inputWire_eval]
          binaryGates_le := by
            have hBinEq : binaryGateCount newC = binaryGateCount prev.circuit + 1 := by
              dsimp [newC, binaryGateCount, unhitBinaryGates]; rfl
            rw [hBinEq]
            exact (Nat.add_le_add_right prev.binaryGates_le 1).trans
              (card_slice_filter_castSucc_add_one_le findAnchor inSlice earlier.inputs_le_wires hAnc hIn)
          wireMap := Fin.lastCases (some (Fin.last prev.localWires))
            (fun q => (prev.wireMap q).map Fin.castSucc)
          wireMap_some := fun u hu => by
            cases u using Fin.lastCases with
            | last => simp
            | cast q =>
              rw [Fin.lastCases_castSucc]
              simp only [Option.isSome_map]
              exact prev.wireMap_some q (by simpa using hu)
          wireMap_eval := fun x u lw hEq => by
            cases u using Fin.lastCases with
            | last =>
              rw [Fin.lastCases_last] at hEq
              injection hEq with hLw
              rw [← hLw]
              have hEvA := prev.wireMap_eval x a la (Option.some_get hSomeA).symm
              have hEvB := prev.wireMap_eval x b lb (Option.some_get hSomeB).symm
              simp only [newC, Circuit.evalWires, Gate.eval, Fin.snoc_last, hEvA, hEvB]
            | cast q =>
              rw [Fin.lastCases_castSucc] at hEq
              rcases Option.map_eq_some_iff.mp hEq with ⟨lw0, hMap0, rfl⟩
              simpa [newC, Circuit.evalWires, Fin.snoc_castSucc] using
                prev.wireMap_eval x q lw0 hMap0 }
      else
        { localWires := prev.localWires
          circuit := prev.circuit
          inputWire := prev.inputWire
          inputWire_eval := prev.inputWire_eval
          binaryGates_le := prev.binaryGates_le.trans (card_slice_filter_castSucc_le findAnchor inSlice)
          wireMap := Fin.lastCases none prev.wireMap
          wireMap_some := fun u hu => by
            cases u using Fin.lastCases with
            | last =>
              exfalso
              rcases hu with hSome | hTrue
              · simp [hAnc] at hSome
              · exact hIn hTrue
            | cast q =>
              rw [Fin.lastCases_castSucc]
              exact prev.wireMap_some q (by simpa using hu)
          wireMap_eval := fun x u lw hEq => by
            cases u using Fin.lastCases with
            | last => simp at hEq
            | cast q =>
              rw [Fin.lastCases_castSucc] at hEq
              simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireMap_eval x q lw hEq }

/-- Packages an output wire `lw` of an extracted `SubDAGBuild` as a `LocalCone v`. -/
def SubDAGBuild.toLocalCone {n w v arity : Nat} {c : Circuit n w}
    {anchorVar : Fin arity → Fin v} {findAnchor : Fin w → Option (Fin arity)}
    {inSlice : Fin w → Bool} {liftAssign : (Fin n → Bool) → (Fin v → Bool)}
    (b : SubDAGBuild c anchorVar findAnchor inSlice liftAssign)
    (lw : Fin b.localWires) : LocalCone v where
  arity := arity
  vars := anchorVar
  localWires := b.localWires
  circuit := b.circuit
  output := lw

/-- Generalized slice-compilation state parameterized by arbitrary constraint arity bound `A + 1`
and binary-gate bound `G + 3` (supporting polynomial-size shared DAG slices). -/
structure SliceCSPState {n w : Nat} (c : Circuit n w) (cut : Fin w → Bool) (A G : Nat) where
  blocks : Nat
  blocks_eq : blocks = keptCount n cut
  constraints : List (LocalCircuitConstraint (n + blocks))
  constraints_length : constraints.length = blocks
  constraints_arity : ∀ con ∈ constraints, con.arity ≤ A + 1
  constraints_binaryGates : ∀ con ∈ constraints, binaryGateCount con.circuit ≤ G + 3
  liftAssign : (Fin n → Bool) → (Fin (n + blocks) → Bool)
  lift_prefix : ∀ x (i : Fin n), liftAssign x (Fin.castAdd blocks i) = x i
  constraints_iff : ∀ σ : Fin (n + blocks) → Bool,
    (CircuitCSP.mk constraints).eval σ = true ↔
      σ = liftAssign (fun i => σ (Fin.castAdd blocks i))
  wireIdx : Fin w → Fin (n + blocks)
  wireIdx_eval : ∀ x u, (u.val < n ∨ cut u = true) → liftAssign x (wireIdx u) = c.evalWires x u

theorem fin_castAdd_succ_eq {n blocks : Nat} (i : Fin n) :
    Fin.castAdd (blocks + 1) i = (Fin.castAdd blocks i).castSucc :=
  Fin.ext rfl

theorem fin_init_snoc {n : Nat} (f : Fin n → Bool) (y : Bool) :
    Fin.init (Fin.snoc (α := fun _ => Bool) f y) = f := by
  funext i
  simp [Fin.init]

theorem fin_snoc_init_last {n : Nat} (σ : Fin (n + 1) → Bool) :
    Fin.snoc (Fin.init σ) (σ (Fin.last n)) = σ := by
  funext u
  cases u using Fin.lastCases with
  | last => simp
  | cast q => simp [Fin.init]

/-- Base `SliceCSPState` on `Circuit.inputsOnly`. -/
def emptySliceCSPState {n : Nat} (cut : Fin n → Bool) (A G : Nat) :
    SliceCSPState (Circuit.inputsOnly : Circuit n n) cut A G where
  blocks := 0
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

/-- Bundled cone witnessing `extendSliceCSPState` at a kept cut wire. -/
structure SliceLastCone {n w blocks : Nat} (earlier : Circuit n w) (g : Gate w)
    (liftAssign : (Fin n → Bool) → (Fin (n + blocks) → Bool)) (A G : Nat) where
  cone : LocalCone (n + blocks)
  eval_eq : ∀ x, cone.eval (liftAssign x) = (earlier.snoc g).evalWires x (Fin.last w)
  arity_le : cone.arity ≤ A
  binaryGates_le : binaryGateCount cone.circuit ≤ G

/-- Conditional extension of a `SliceCSPState` across `earlier.snoc g`: only asks for a
`SliceLastCone` of arity `≤ A` and binary gates `≤ G` when `n ≤ w ∧ cut (Fin.last w) = true`. -/
def extendSliceCSPState {n w : Nat} {earlier : Circuit n w} (g : Gate w)
    (cut : Fin (w + 1) → Bool) (A G : Nat) (hn : 0 < n)
    (prev : SliceCSPState earlier (cut ∘ Fin.castSucc) A G)
    (buildCone : (n ≤ w ∧ cut (Fin.last w) = true) →
      SliceLastCone earlier g prev.liftAssign A G) :
    SliceCSPState (earlier.snoc g) cut A G :=
  let nw := n + prev.blocks
  if hKeep : n ≤ w ∧ cut (Fin.last w) = true then
    let pkg := buildCone hKeep
    let coneLast := pkg.cone
    let hLastEval := pkg.eval_eq
    let hLastArity := pkg.arity_le
    let hLastBin := pkg.binaryGates_le
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
          exact Nat.add_le_add_right hLastBin 3
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
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireIdx_eval x q hq }
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
          simpa [Circuit.evalWires, Fin.snoc_castSucc] using prev.wireIdx_eval x q hq }

/-- Wraps any `SliceCSPState` whose cut captures `source.output` into an exact-counting
`CircuitCSPCertificate source`. -/
def dagSliceCSPCertificate {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    CircuitCSPCertificate source :=
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

theorem dagSliceCSPCertificate_vars_eq {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    (dagSliceCSPCertificate source cut A G st hOut).vars = n + keptCount n cut := by
  dsimp [dagSliceCSPCertificate]
  rw [st.blocks_eq]

theorem dagSliceCSPCertificate_constraintCount_eq {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    (dagSliceCSPCertificate source cut A G st hOut).csp.constraintCount =
      keptCount n cut + 1 := by
  dsimp [dagSliceCSPCertificate, CircuitCSP.constraintCount]
  rw [st.constraints_length, st.blocks_eq]

theorem dagSliceCSPCertificate_maxArity_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    (dagSliceCSPCertificate source cut A G st hOut).csp.maxArity ≤ A + 1 := by
  dsimp only [dagSliceCSPCertificate]
  refine CircuitCSP.maxArity_le _ (A + 1) ?_
  intro con hMem
  rcases List.mem_cons.mp hMem with rfl | hOld
  · simp
  · exact st.constraints_arity con hOld

theorem dagSliceCSPCertificate_maxBinaryGates_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    (dagSliceCSPCertificate source cut A G st hOut).csp.maxBinaryGates ≤ G + 3 := by
  dsimp only [dagSliceCSPCertificate]
  refine CircuitCSP.maxBinaryGates_le _ (G + 3) ?_
  intro con hMem
  rcases List.mem_cons.mp hMem with rfl | hOld
  · rw [LocalCircuitConstraint.unitTrueConstraint_binaryGates]
    exact Nat.zero_le _
  · exact st.constraints_binaryGates con hOld

theorem dagSliceCSPCertificate_totalIncidence_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    (dagSliceCSPCertificate source cut A G st hOut).csp.totalIncidence ≤
      (keptCount n cut + 1) * (A + 1) := by
  have h1 := (dagSliceCSPCertificate source cut A G st hOut).csp.totalIncidence_le_maxArity
  have h2 := dagSliceCSPCertificate_constraintCount_eq source cut A G st hOut
  have h3 := dagSliceCSPCertificate_maxArity_le source cut A G st hOut
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_left _ h3)

theorem dagSliceCSPCertificate_totalBinaryGates_le {n : Nat} (source : CircuitInstance n)
    (cut : Fin source.wires → Bool) (A G : Nat)
    (st : SliceCSPState source.circuit cut A G)
    (hOut : source.output.val < n ∨ cut source.output = true) :
    (dagSliceCSPCertificate source cut A G st hOut).csp.totalBinaryGates ≤
      (keptCount n cut + 1) * (G + 3) := by
  have h1 := (dagSliceCSPCertificate source cut A G st hOut).csp.totalBinaryGates_le_maxBinaryGates
  have h2 := dagSliceCSPCertificate_constraintCount_eq source cut A G st hOut
  have h3 := dagSliceCSPCertificate_maxBinaryGates_le source cut A G st hOut
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_left _ h3)

/-! ### 4. Breaking the Generic Valiant Wall on `DeepSkipChain` (End-to-End `2 ^ o(n)`) -/

namespace DeepSkipChain

/-- Periodic width-`s` cut of period `P` ending at gate `D - 1` for `DeepSkipChain.buildChain`. -/
def barrierCutOf (k D s P m : Nat) (u : Fin ((k + 1) + m)) : Bool :=
  decide (k + 1 ≤ u.val ∧ ((u.val - (k + 1)) % P < s ∨ u.val - (k + 1) + 1 = D))

/-- At most `(D / P + 1) * s + 1` cut variables are kept by `barrierCutOf k D s P D`. -/
theorem keptCount_barrierCut_le (k D s P : Nat) (hP : 0 < P) :
    keptCount (k + 1) (barrierCutOf k D s P D) ≤ (D / P + 1) * s + 1 := by
  unfold keptCount
  let S := Finset.univ.filter fun u : Fin ((k + 1) + D) =>
    k + 1 ≤ u.val ∧ barrierCutOf k D s P D u = true
  let SMod := S.filter fun u => (u.val - (k + 1)) % P < s
  let SEnd := S.filter fun u => u.val - (k + 1) + 1 = D
  have hSub : S ⊆ SMod ∪ SEnd := by
    intro u hu
    have hMem := (Finset.mem_filter.mp hu).2
    have hBar := hMem.2
    simp only [barrierCutOf, decide_eq_true_eq] at hBar
    rcases hBar.2 with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, h2⟩)
  have hCardMod : SMod.card ≤ (D / P + 1) * s := by
    by_cases hs0 : s = 0
    · subst hs0
      have hEmpty : SMod = ∅ := by
        ext u
        simp [SMod]
      rw [hEmpty, Finset.card_empty]
      exact Nat.zero_le _
    · have hsPos : 0 < s := Nat.pos_of_ne_zero hs0
      have hMul : (D / P + 1) * s = (Finset.univ : Finset (Fin (D / P + 1) × Fin s)).card := by
        simp
      rw [hMul]
      refine Finset.card_le_card_of_injOn
        (fun u => (⟨((u.val - (k + 1)) / P) % (D / P + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩,
          ⟨((u.val - (k + 1)) % P) % s, Nat.mod_lt _ hsPos⟩))
        ?_ ?_
      · intro u _
        exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro u₁ hu₁ u₂ hu₂ hEq
        have hu1S := (Finset.mem_filter.mp hu₁).1
        have hu2S := (Finset.mem_filter.mp hu₂).1
        have hGe₁ : k + 1 ≤ u₁.val := (Finset.mem_filter.mp hu1S).2.1
        have hGe₂ : k + 1 ≤ u₂.val := (Finset.mem_filter.mp hu2S).2.1
        have hModLt1 : (u₁.val - (k + 1)) % P < s := (Finset.mem_filter.mp hu₁).2
        have hModLt2 : (u₂.val - (k + 1)) % P < s := (Finset.mem_filter.mp hu₂).2
        have hLt1 : u₁.val - (k + 1) < D := by have := u₁.isLt; omega
        have hLt2 : u₂.val - (k + 1) < D := by have := u₂.isLt; omega
        have hDivLt1 : (u₁.val - (k + 1)) / P < D / P + 1 :=
          Nat.div_lt_of_lt_mul (by have hMod := Nat.div_add_mod D P; nlinarith [Nat.mod_lt D hP])
        have hDivLt2 : (u₂.val - (k + 1)) / P < D / P + 1 :=
          Nat.div_lt_of_lt_mul (by have hMod := Nat.div_add_mod D P; nlinarith [Nat.mod_lt D hP])
        have hDivEq' := congrArg (fun p : Fin (D / P + 1) × Fin s => p.1.val) hEq
        have hModEq' := congrArg (fun p : Fin (D / P + 1) × Fin s => p.2.val) hEq
        dsimp at hDivEq' hModEq'
        rw [Nat.mod_eq_of_lt hDivLt1, Nat.mod_eq_of_lt hDivLt2] at hDivEq'
        rw [Nat.mod_eq_of_lt hModLt1, Nat.mod_eq_of_lt hModLt2] at hModEq'
        have hSubEq : u₁.val - (k + 1) = u₂.val - (k + 1) := by
          calc
            u₁.val - (k + 1)
              = P * ((u₁.val - (k + 1)) / P) + (u₁.val - (k + 1)) % P :=
                  (Nat.div_add_mod _ _).symm
            _ = P * ((u₂.val - (k + 1)) / P) + (u₂.val - (k + 1)) % P := by
                  rw [hDivEq', hModEq']
            _ = u₂.val - (k + 1) := Nat.div_add_mod _ _
        exact Fin.ext (by omega)
  have hCardEnd : SEnd.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u₁ hu₁ u₂ hu₂
    have h1 := (Finset.mem_filter.mp hu₁).2
    have h2 := (Finset.mem_filter.mp hu₂).2
    have hGe₁ := ((Finset.mem_filter.mp (Finset.mem_filter.mp hu₁).1).2).1
    have hGe₂ := ((Finset.mem_filter.mp (Finset.mem_filter.mp hu₂).1).2).1
    exact Fin.ext (by omega)
  exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans (by omega))

theorem mem_slice_of_ge (n start s m : Nat) (u : Fin (n + m)) (hGe : n + start ≤ u.val) :
    (if h : n + start ≤ u.val ∧ u.val < n + start + s then
      some (⟨u.val - (n + start), by have := h.1; have := h.2; omega⟩ : Fin s)
    else none).isSome ∨
    decide (n + start + s ≤ u.val) = true := by
  by_cases hLt : u.val < n + start + s
  · left
    simp [hGe, hLt]
  · right
    simp only [decide_eq_true_eq]
    omega

theorem gatePredecessorClosed_slice (k s start : Nat) (hs : 1 ≤ s) :
    ∀ m : Nat, GatePredecessorClosed (buildChain k s m)
      (fun u : Fin ((k + 1) + m) =>
        if h : (k + 1) + start ≤ u.val ∧ u.val < (k + 1) + start + s then
          some (⟨u.val - ((k + 1) + start), by have := h.1; have := h.2; omega⟩ : Fin s)
        else none)
      (fun u : Fin ((k + 1) + m) => decide ((k + 1) + start + s ≤ u.val)) := by
  intro m
  induction m with
  | zero =>
    intro u hu
    simp only [decide_eq_true_eq] at hu
    have := u.isLt
    omega
  | succ m ih =>
    dsimp [buildChain]
    constructor
    · simpa [Function.comp_def, Fin.val_castSucc] using ih
    · intro hAnc hIn
      have hGt : (k + 1) + start + s ≤ (k + 1) + m := by
        simpa [decide_eq_true_eq] using hIn
      have hSm : s ≤ m := by omega
      let n := k + 1
      have hnPos : 0 < n := Nat.succ_pos k
      let a : Fin (n + m) := if hm0 : m = 0 then ⟨0, by omega⟩ else ⟨n + m - 1, by omega⟩
      let b : Fin (n + m) :=
        if hsm : 0 < s ∧ s ≤ m then ⟨n + m - s, by omega⟩
        else ⟨m % n, by have hm := Nat.mod_lt m hnPos; omega⟩
      have haGe : (k + 1) + start ≤ a.castSucc.val := by
        have hm0 : m ≠ 0 := by omega
        have haVal : a.val = n + m - 1 := by dsimp [a]; simp [hm0]
        rw [Fin.val_castSucc, haVal]
        dsimp [n]
        omega
      have hbGe : (k + 1) + start ≤ b.castSucc.val := by
        have hsPos : 0 < s := hs
        have hbVal : b.val = n + m - s := by dsimp [b]; simp [hsPos, hSm]
        rw [Fin.val_castSucc, hbVal]
        dsimp [n]
        omega
      dsimp [chainGate]
      by_cases hm2 : m % 2 = 0
      · simp only [hm2, ↓reduceIte]
        exact ⟨mem_slice_of_ge (k + 1) start s (m + 1) a.castSucc haGe,
          mem_slice_of_ge (k + 1) start s (m + 1) b.castSucc hbGe⟩
      · simp only [hm2, ↓reduceIte]
        exact ⟨mem_slice_of_ge (k + 1) start s (m + 1) a.castSucc haGe,
          mem_slice_of_ge (k + 1) start s (m + 1) b.castSucc hbGe⟩

theorem start_window_bounds (m s P : Nat) (hs : 1 ≤ s) (hSP : s ≤ P) (hSm : s ≤ m) :
    let start := if m % P < s then (m / P - 1) * P else (m / P) * P
    start % P = 0 ∧ start + s ≤ m ∧ m - (start + s) < P := by
  have hP : 0 < P := lt_of_lt_of_le hs hSP
  have hDivMod := Nat.div_add_mod m P
  have hComm : (m / P) * P = P * (m / P) := Nat.mul_comm _ _
  have hModLt := Nat.mod_lt m hP
  dsimp only
  by_cases hmP : m % P < s
  · simp only [hmP, ↓reduceIte]
    have hGeP : P ≤ m := by
      by_contra hLt
      have hLt' : m < P := Nat.lt_of_not_ge hLt
      rw [Nat.mod_eq_of_lt hLt'] at hmP
      omega
    have hDivPos : 1 ≤ m / P := by
      cases hd : m / P with
      | zero => rw [hd, Nat.mul_zero, Nat.zero_add] at hDivMod; omega
      | succ d => exact Nat.succ_pos _
    have hMulSub : (m / P - 1) * P + P = P * (m / P) := by
      cases hd : m / P with
      | zero => omega
      | succ d => simp; ring
    refine ⟨Nat.mul_mod_left _ _, ?_, ?_⟩ <;> omega
  · simp only [hmP, ↓reduceIte]
    refine ⟨Nat.mul_mod_left _ _, ?_, ?_⟩ <;> omega

/-- Inductive DAG-preserving `SliceCSPState` builder for `DeepSkipChain.buildChain k s m` with
barrier cut `barrierCutOf k D s P`, constraint arity `≤ max 2 s + 1`, and per-constraint binary
gates `≤ P + 3`. -/
def buildSliceCSPState (k D s P : Nat) (hs : 1 ≤ s) (hSP : s ≤ P) :
    (m : Nat) → SliceCSPState (buildChain k s m) (barrierCutOf k D s P m) (max 2 s) P
  | 0 => emptySliceCSPState (barrierCutOf k D s P 0) (max 2 s) P
  | m + 1 =>
    let prev : SliceCSPState (buildChain k s m) (barrierCutOf k D s P (m + 1) ∘ Fin.castSucc)
        (max 2 s) P := buildSliceCSPState k D s P hs hSP m
    have hP : 0 < P := lt_of_lt_of_le hs hSP
    extendSliceCSPState (chainGate k (m + 1) s m (Nat.lt_succ_self m))
      (barrierCutOf k D s P (m + 1)) (max 2 s) P (Nat.succ_pos k) prev fun _hKeep =>
      let n := k + 1
      have hnPos : 0 < n := Nat.succ_pos k
      let a : Fin (n + m) := if hm0 : m = 0 then ⟨0, by omega⟩ else ⟨n + m - 1, by omega⟩
      let b : Fin (n + m) :=
        if hsm : 0 < s ∧ s ≤ m then ⟨n + m - s, by omega⟩
        else ⟨m % n, by have hm := Nat.mod_lt m hnPos; omega⟩
      if hmLtS : m < s then
        let cA := LocalCircuitConstraint.wire (prev.wireIdx a)
        let cB := LocalCircuitConstraint.wire (prev.wireIdx b)
        let coneLast := LocalCircuitConstraint.binaryCone (decide (m % 2 = 0)) cA cB
        have haValid : a.val < n ∨ (barrierCutOf k D s P (m + 1) ∘ Fin.castSucc) a = true := by
          by_cases hm0 : m = 0
          · left; simp [a, hm0, n]
          · right
            have hSub : a.val - (k + 1) = m - 1 := by dsimp [a, n]; simp [hm0]; omega
            simp only [Function.comp_apply, barrierCutOf, decide_eq_true_eq, Fin.val_castSucc, hSub]
            constructor
            · dsimp [a, n]; simp [hm0]; omega
            · left
              rw [Nat.mod_eq_of_lt (by omega)]
              omega
        have hbValid : b.val < n ∨ (barrierCutOf k D s P (m + 1) ∘ Fin.castSucc) b = true := by
          left
          have hNot : ¬ (0 < s ∧ s ≤ m) := by omega
          dsimp [b, n]
          simp only [hNot, ↓reduceDIte]
          exact Nat.mod_lt m hnPos
        { cone := coneLast
          eval_eq := fun x => by
            dsimp [coneLast]
            rw [LocalCircuitConstraint.binaryCone_eval]
            simp only [cA, cB, LocalCircuitConstraint.wire_eval, prev.wireIdx_eval x a haValid,
              prev.wireIdx_eval x b hbValid]
            dsimp [buildChain, chainGate]
            by_cases hm2 : m % 2 = 0
            · simp [hm2, Circuit.evalWires, Gate.eval, Fin.snoc_last, a, b, n]
            · simp [hm2, Circuit.evalWires, Gate.eval, Fin.snoc_last, a, b, n]
          arity_le := by
            dsimp [coneLast, cA, cB]
            exact Nat.le_max_left 2 s
          binaryGates_le := by
            have hG := LocalCircuitConstraint.binaryCone_binaryGates (decide (m % 2 = 0)) cA cB
            have hGA : binaryGateCount cA.circuit = 0 := LocalCircuitConstraint.wire_binaryGates _
            have hGB : binaryGateCount cB.circuit = 0 := LocalCircuitConstraint.wire_binaryGates _
            change binaryGateCount (LocalCircuitConstraint.binaryCone (decide (m % 2 = 0)) cA cB).circuit ≤ P
            omega }
      else
        let hSm : s ≤ m := Nat.le_of_not_gt hmLtS
        let start := if m % P < s then (m / P - 1) * P else (m / P) * P
        let hBounds := start_window_bounds m s P hs hSP hSm
        let hStartMod : start % P = 0 := hBounds.1
        let hStartAdd : start + s ≤ m := hBounds.2.1
        let hDiffP : m - (start + s) < P := hBounds.2.2
        let uAnchor : Fin s → Fin (n + m) := fun j =>
          ⟨n + start + j.val, by have := j.isLt; omega⟩
        let anchorVar : Fin s → Fin (n + prev.blocks) := fun j =>
          prev.wireIdx (uAnchor j)
        let findAnchor : Fin (n + m) → Option (Fin s) := fun u =>
          if h : n + start ≤ u.val ∧ u.val < n + start + s then
            some ⟨u.val - (n + start), by have := h.1; have := h.2; omega⟩
          else none
        let inSlice : Fin (n + m) → Bool := fun u => decide (n + start + s ≤ u.val)
        have hAnchorEval : ∀ x u (j : Fin s), findAnchor u = some j →
            prev.liftAssign x (anchorVar j) = (buildChain k s m).evalWires x u := by
          intro x u j hj
          dsimp [findAnchor] at hj
          split_ifs at hj with hU
          injection hj with hjVal
          have hU1 : n + start ≤ u.val := hU.1
          have hU2 : u.val < n + start + s := hU.2
          have hjEq : j.val = u.val - (n + start) := congrArg Fin.val hjVal.symm
          have hIdx : uAnchor j = u := by
            apply Fin.ext
            dsimp [uAnchor]
            omega
          have hBar : (barrierCutOf k D s P (m + 1) ∘ Fin.castSucc) (uAnchor j) = true := by
            simp only [Function.comp_apply, barrierCutOf, decide_eq_true_eq, Fin.val_castSucc, uAnchor]
            refine ⟨by dsimp [n]; omega, Or.inl ?_⟩
            have hSub : n + start + j.val - (k + 1) = start + j.val := by dsimp [n]; omega
            rw [hSub, Nat.add_mod, hStartMod, Nat.zero_add,
              Nat.mod_eq_of_lt (Nat.mod_lt _ hP),
              Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt hSP)]
            exact j.isLt
          dsimp [anchorVar]
          rw [prev.wireIdx_eval x (uAnchor j) (Or.inr hBar), hIdx]
        let sub := extractSubDAG anchorVar prev.liftAssign (buildChain k s m)
          findAnchor inSlice hAnchorEval (gatePredecessorClosed_slice k s start hs m)
        have haGe : n + start ≤ a.val := by
          have hm0 : m ≠ 0 := by omega
          have haVal : a.val = n + m - 1 := by dsimp [a]; simp [hm0]
          omega
        have hbGe : n + start ≤ b.val := by
          have hsPos : 0 < s := hs
          have hbVal : b.val = n + m - s := by dsimp [b]; simp [hsPos, hSm]
          omega
        have haMem : (findAnchor a).isSome ∨ inSlice a = true :=
          mem_slice_of_ge n start s m a haGe
        have hbMem : (findAnchor b).isSome ∨ inSlice b = true :=
          mem_slice_of_ge n start s m b hbGe
        have hSomeA : (sub.wireMap a).isSome := sub.wireMap_some a haMem
        have hSomeB : (sub.wireMap b).isSome := sub.wireMap_some b hbMem
        let la := (sub.wireMap a).get hSomeA
        let lb := (sub.wireMap b).get hSomeB
        let finalGate : Gate sub.localWires := if m % 2 = 0 then .and la lb else .or la lb
        let coneLast : LocalCone (n + prev.blocks) :=
          { arity := s
            vars := anchorVar
            localWires := sub.localWires + 1
            circuit := sub.circuit.snoc finalGate
            output := Fin.last sub.localWires }
        have hFilterLe : (Finset.univ.filter fun u : Fin (n + m) =>
            n ≤ u.val ∧ findAnchor u = none ∧ inSlice u = true).card ≤ m - (start + s) := by
          by_cases hEmpty : m ≤ start + s
          · have hNone : (Finset.univ.filter fun u : Fin (n + m) =>
                n ≤ u.val ∧ findAnchor u = none ∧ inSlice u = true) = ∅ := by
              ext u
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false, not_and]
              intro _ _ hInU
              have hInU' : n + start + s ≤ u.val := by
                simpa [inSlice, decide_eq_true_eq] using hInU
              have := u.isLt
              omega
            rw [hNone, Finset.card_empty]
            exact Nat.zero_le _
          · have hPosDiff : 0 < m - (start + s) := by omega
            have hEqCard : m - (start + s) =
                (Finset.univ : Finset (Fin (m - (start + s)))).card := by simp
            rw [hEqCard]
            refine Finset.card_le_card_of_injOn
              (fun u => ⟨(u.val - (n + start + s)) % (m - (start + s)), Nat.mod_lt _ hPosDiff⟩)
              ?_ ?_
            · intro u _
              exact Finset.mem_coe.mpr (Finset.mem_univ _)
            · intro u₁ hu₁ u₂ hu₂ hEq
              have hu1Mem := (Finset.mem_filter.mp hu₁).2
              have hu2Mem := (Finset.mem_filter.mp hu₂).2
              have hIn1 : n + start + s ≤ u₁.val := by
                simpa [inSlice, decide_eq_true_eq] using hu1Mem.2.2
              have hIn2 : n + start + s ≤ u₂.val := by
                simpa [inSlice, decide_eq_true_eq] using hu2Mem.2.2
              have hLt1 : u₁.val - (n + start + s) < m - (start + s) := by
                have := u₁.isLt; omega
              have hLt2 : u₂.val - (n + start + s) < m - (start + s) := by
                have := u₂.isLt; omega
              have hv : (u₁.val - (n + start + s)) % (m - (start + s)) =
                  (u₂.val - (n + start + s)) % (m - (start + s)) := congrArg Fin.val hEq
              rw [Nat.mod_eq_of_lt hLt1, Nat.mod_eq_of_lt hLt2] at hv
              exact Fin.ext (by omega)
        { cone := coneLast
          eval_eq := fun x => by
            have hEvA := sub.wireMap_eval x a la (Option.some_get hSomeA).symm
            have hEvB := sub.wireMap_eval x b lb (Option.some_get hSomeB).symm
            dsimp [coneLast, LocalCircuitConstraint.eval, finalGate, buildChain, chainGate]
            by_cases hm2 : m % 2 = 0
            · simp only [hm2, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last, hEvA, hEvB]
              rfl
            · simp only [hm2, ↓reduceIte, Circuit.evalWires, Gate.eval, Fin.snoc_last, hEvA, hEvB]
              rfl
          arity_le := by
            dsimp [coneLast]
            exact Nat.le_max_right 2 s
          binaryGates_le := by
            have hBinSnoc : binaryGateCount coneLast.circuit = binaryGateCount sub.circuit + 1 := by
              dsimp [coneLast, finalGate]
              by_cases hm2 : m % 2 = 0 <;> simp only [hm2, ↓reduceIte] <;> rfl
            rw [hBinSnoc]
            exact (Nat.add_le_add_right (sub.binaryGates_le.trans hFilterLe) 1).trans (by omega) }

theorem barrierCutOf_output (k D s P : Nat) (hD : 0 < D) :
    barrierCutOf k D s P D (source k D s).output = true := by
  change decide (k + 1 ≤ k + D ∧ ((k + D - (k + 1)) % P < s ∨ k + D - (k + 1) + 1 = D)) = true
  rw [decide_eq_true_eq]
  exact ⟨by omega, Or.inr (by omega)⟩

/-- Concrete DAG-slice `CircuitCSPCertificate` for `DeepSkipChain.source k D s` with period `P`. -/
def sliceCertificate (k D s P : Nat) (hs : 1 ≤ s) (hSP : s ≤ P) (hD : 0 < D) :
    CircuitCSPCertificate (source k D s) :=
  dagSliceCSPCertificate (source k D s) (barrierCutOf k D s P D) (max 2 s) P
    (buildSliceCSPState k D s P hs hSP D)
    (Or.inr (barrierCutOf_output k D s P hD))

theorem sliceCertificate_vars_le (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let P := s * (Nat.log 2 n + s)
    have hSP : s ≤ P := by
      have h1 : 1 ≤ Nat.log 2 n + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 n + s) := Nat.mul_le_mul_left s h1
    have hD : 0 < D := Nat.mul_pos (Nat.succ_pos k) (by omega)
    (sliceCertificate k D s P hs hSP hD).vars ≤ 2 * n + s + 1 := by
  intro n D P hSP hD
  have hVars := dagSliceCSPCertificate_vars_eq (source k D s) (barrierCutOf k D s P D) (max 2 s) P
    (buildSliceCSPState k D s P hs hSP D)
    (Or.inr (barrierCutOf_output k D s P hD))
  change (dagSliceCSPCertificate (source k D s) (barrierCutOf k D s P D) (max 2 s) P
    (buildSliceCSPState k D s P hs hSP D) _).vars ≤ 2 * n + s + 1
  rw [hVars]
  have hP : 0 < P := lt_of_lt_of_le hs hSP
  have hKept := keptCount_barrierCut_le k D s P hP
  have hDiv : (D / P) * s ≤ n := by
    have hMul : (D / P) * s * P ≤ n * P := by
      calc
        (D / P) * s * P = ((D / P) * P) * s := by ring
        _ ≤ D * s := Nat.mul_le_mul_right s (Nat.div_mul_le_self D P)
        _ = n * P := by dsimp [D, P]; ring
    exact Nat.le_of_mul_le_mul_right hMul hP
  have hKeptLe : keptCount (k + 1) (barrierCutOf k D s P D) ≤ n + s + 1 := by
    have hExpand : (D / P + 1) * s = (D / P) * s + s := by ring
    dsimp only [n] at hDiv ⊢
    omega
  exact (Nat.add_le_add_left hKeptLe (k + 1)).trans (by dsimp only [n]; omega)

theorem sliceCertificate_constraintCount_le (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let P := s * (Nat.log 2 n + s)
    have hSP : s ≤ P := by
      have h1 : 1 ≤ Nat.log 2 n + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 n + s) := Nat.mul_le_mul_left s h1
    have hD : 0 < D := Nat.mul_pos (Nat.succ_pos k) (by omega)
    (sliceCertificate k D s P hs hSP hD).csp.constraintCount ≤ n + s + 2 := by
  intro n D P hSP hD
  have hCnt := dagSliceCSPCertificate_constraintCount_eq (source k D s) (barrierCutOf k D s P D) (max 2 s) P
    (buildSliceCSPState k D s P hs hSP D)
    (Or.inr (barrierCutOf_output k D s P hD))
  change (dagSliceCSPCertificate (source k D s) (barrierCutOf k D s P D) (max 2 s) P
    (buildSliceCSPState k D s P hs hSP D) _).csp.constraintCount ≤ n + s + 2
  rw [hCnt]
  have hP : 0 < P := lt_of_lt_of_le hs hSP
  have hKept := keptCount_barrierCut_le k D s P hP
  have hDiv : (D / P) * s ≤ n := by
    have hMul : (D / P) * s * P ≤ n * P := by
      calc
        (D / P) * s * P = ((D / P) * P) * s := by ring
        _ ≤ D * s := Nat.mul_le_mul_right s (Nat.div_mul_le_self D P)
        _ = n * P := by dsimp [D, P]; ring
    exact Nat.le_of_mul_le_mul_right hMul hP
  have hKeptLe : keptCount (k + 1) (barrierCutOf k D s P D) ≤ n + s + 1 := by
    have hExpand : (D / P + 1) * s = (D / P) * s + s := by ring
    dsimp only [n] at hDiv ⊢
    omega
  exact (Nat.add_le_add_right hKeptLe 1).trans (by dsimp only [n]; omega)

theorem sliceCertificate_maxArity_le (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let P := s * (Nat.log 2 n + s)
    have hSP : s ≤ P := by
      have h1 : 1 ≤ Nat.log 2 n + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 n + s) := Nat.mul_le_mul_left s h1
    have hD : 0 < D := Nat.mul_pos (Nat.succ_pos k) (by omega)
    (sliceCertificate k D s P hs hSP hD).csp.maxArity ≤ max 2 s + 1 := by
  intro n D P hSP hD
  exact dagSliceCSPCertificate_maxArity_le _ _ _ _ _ _

theorem sliceCertificate_maxBinaryGates_le (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let P := s * (Nat.log 2 n + s)
    have hSP : s ≤ P := by
      have h1 : 1 ≤ Nat.log 2 n + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 n + s) := Nat.mul_le_mul_left s h1
    have hD : 0 < D := Nat.mul_pos (Nat.succ_pos k) (by omega)
    (sliceCertificate k D s P hs hSP hD).csp.maxBinaryGates ≤ s * (Nat.log 2 n + s) + 3 := by
  intro n D P hSP hD
  exact dagSliceCSPCertificate_maxBinaryGates_le _ _ _ _ _ _

theorem sliceCertificate_totalIncidence_le (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let P := s * (Nat.log 2 n + s)
    have hSP : s ≤ P := by
      have h1 : 1 ≤ Nat.log 2 n + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 n + s) := Nat.mul_le_mul_left s h1
    have hD : 0 < D := Nat.mul_pos (Nat.succ_pos k) (by omega)
    (sliceCertificate k D s P hs hSP hD).csp.totalIncidence ≤ (n + s + 2) * (max 2 s + 1) := by
  intro n D P hSP hD
  have h1 := (sliceCertificate k D s P hs hSP hD).csp.totalIncidence_le_maxArity
  have h2 := sliceCertificate_constraintCount_le k s hs
  have h3 := sliceCertificate_maxArity_le k s hs
  exact h1.trans (Nat.mul_le_mul h2 h3)

theorem sliceCertificate_totalBinaryGates_le (k s : Nat) (hs : 1 ≤ s) :
    let n := k + 1
    let D := n * (Nat.log 2 n + s)
    let P := s * (Nat.log 2 n + s)
    have hSP : s ≤ P := by
      have h1 : 1 ≤ Nat.log 2 n + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 n + s) := Nat.mul_le_mul_left s h1
    have hD : 0 < D := Nat.mul_pos (Nat.succ_pos k) (by omega)
    (sliceCertificate k D s P hs hSP hD).csp.totalBinaryGates ≤
      (n + s + 2) * (s * (Nat.log 2 n + s) + 3) := by
  intro n D P hSP hD
  have h1 := (sliceCertificate k D s P hs hSP hD).csp.totalBinaryGates_le_maxBinaryGates
  have h2 := sliceCertificate_constraintCount_le k s hs
  have h3 := sliceCertificate_maxBinaryGates_le k s hs
  exact h1.trans (Nat.mul_le_mul h2 h3)

/-- **End-to-End `2 ^ o(n)` Separation on `DeepSkipChain`**: whereas `StrideContraction` fails on
`DeepSkipChain` and generic depth-based Valiant cuts hit the arity-vs-cut-size wall,
`DeepSkipChain.sliceCertificate` keeps `vars + totalIncidence = O(n)` and `totalBinaryGates =
O(n log n)`, proving `cspIncidenceBudget = o(n)`. -/
theorem sliceCertificate_end_to_end_subexponential (k : Nat → Nat) (s : Nat) (hs : 1 ≤ s)
    (hk : Tendsto k atTop atTop) (C d : ℝ) :
    let D : Nat → Nat := fun i => (k i + 1) * (Nat.log 2 (k i + 1) + s)
    let P : Nat → Nat := fun i => s * (Nat.log 2 (k i + 1) + s)
    have hSP : ∀ i, s ≤ P i := fun i => by
      have h1 : 1 ≤ Nat.log 2 (k i + 1) + s := by omega
      calc s = s * 1 := (Nat.mul_one s).symm
        _ ≤ s * (Nat.log 2 (k i + 1) + s) := Nat.mul_le_mul_left s h1
    have hD : ∀ i, 0 < D i := fun i => Nat.mul_pos (Nat.succ_pos (k i)) (by omega)
    (fun i => cspIncidenceBudget (k i + 1)
      (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars
      (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence
      (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalBinaryGates
      C d) =o[atTop] fun i => ((k i + 1 : Nat) : ℝ) := by
  intro D P hSP hD
  have hnNat : Tendsto (fun i => k i + 1) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨M, hM⟩ := Filter.tendsto_atTop_atTop.mp hk b
      exact ⟨M, fun i hi => by have := hM i hi; omega⟩
  have hBelow : ∀ i, k i + 1 ≤
      (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars +
      (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence := fun i => by
    have hVars := dagSliceCSPCertificate_vars_eq (source (k i) (D i) s)
      (barrierCutOf (k i) (D i) s (P i) (D i)) (max 2 s) (P i)
      (buildSliceCSPState (k i) (D i) s (P i) hs (hSP i) (D i))
      (Or.inr (barrierCutOf_output (k i) (D i) s (P i) (hD i)))
    have hGe : k i + 1 ≤ (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars := by
      dsimp only [sliceCertificate]
      rw [hVars]
      exact Nat.le_add_right _ _
    exact hGe.trans (Nat.le_add_right _ _)
  let c : ℝ := ((max 2 s + 1) * (s + 3) + s + 3 : Nat)
  have hcNonneg : 0 ≤ c := by positivity
  have hInc : ∀ᶠ i in atTop,
      (((sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars +
        (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence : Nat) : ℝ) ≤
        c * ((k i + 1 : Nat) : ℝ) * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ (0 : ℝ) := by
    refine Eventually.of_forall fun i => ?_
    have hV : (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars ≤
        2 * (k i + 1) + s + 1 := sliceCertificate_vars_le (k i) s hs
    have hI : (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence ≤
        (k i + 1 + s + 2) * (max 2 s + 1) := sliceCertificate_totalIncidence_le (k i) s hs
    have h1 : 1 ≤ k i + 1 := Nat.succ_pos (k i)
    have hSum : (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars +
        (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence ≤
        ((max 2 s + 1) * (s + 3) + s + 3) * (k i + 1) := by
      have hI' : (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence ≤
          ((k i + 1) * (s + 3)) * (max 2 s + 1) := by
        have hLe : k i + 1 + s + 2 ≤ (k i + 1) * (s + 3) := by nlinarith
        exact hI.trans (Nat.mul_le_mul_right _ hLe)
      nlinarith
    have hCast : (((sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars +
        (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence : Nat) : ℝ) ≤
        c * ((k i + 1 : Nat) : ℝ) := by
      calc
        (((sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).vars +
            (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalIncidence : Nat) : ℝ)
          ≤ ((((max 2 s + 1) * (s + 3) + s + 3) * (k i + 1) : Nat) : ℝ) := by exact_mod_cast hSum
        _ = c * ((k i + 1 : Nat) : ℝ) := by dsimp [c]; push_cast; ring
    simpa [Real.rpow_zero, mul_one] using hCast
  let Cg : ℝ := ((s + 2) * (s * s + s + 3) : Nat)
  have hCgNonneg : 0 ≤ Cg := by positivity
  have hGates : ∀ᶠ i in atTop,
      ((sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalBinaryGates : ℝ) ≤
        Cg * (((k i + 1 : Nat) : ℝ) + 16) ^ 2 := by
    refine Eventually.of_forall fun i => ?_
    have hG : (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalBinaryGates ≤
        (k i + 1 + s + 2) * (s * (Nat.log 2 (k i + 1) + s) + 3) :=
      sliceCertificate_totalBinaryGates_le (k i) s hs
    have h1 : 1 ≤ k i + 1 := Nat.succ_pos (k i)
    have hLogLe : Nat.log 2 (k i + 1) ≤ k i + 1 :=
      (Nat.log_lt_self 2 (Nat.succ_ne_zero (k i))).le
    have hG' : (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalBinaryGates ≤
        (s + 2) * (s * s + s + 3) * (k i + 1 + 16) ^ 2 := by
      have hLeft : k i + 1 + s + 2 ≤ (s + 2) * (k i + 1 + 16) := by nlinarith
      have hRight : s * (Nat.log 2 (k i + 1) + s) + 3 ≤ (s * s + s + 3) * (k i + 1 + 16) := by
        nlinarith
      calc
        (sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalBinaryGates
          ≤ (k i + 1 + s + 2) * (s * (Nat.log 2 (k i + 1) + s) + 3) := hG
        _ ≤ ((s + 2) * (k i + 1 + 16)) * ((s * s + s + 3) * (k i + 1 + 16)) :=
            Nat.mul_le_mul hLeft hRight
        _ = (s + 2) * (s * s + s + 3) * (k i + 1 + 16) ^ 2 := by ring
    calc
      ((sliceCertificate (k i) (D i) s (P i) hs (hSP i) (hD i)).csp.totalBinaryGates : ℝ)
        ≤ (((s + 2) * (s * s + s + 3) * (k i + 1 + 16) ^ 2 : Nat) : ℝ) := by exact_mod_cast hG'
      _ = Cg * (((k i + 1 : Nat) : ℝ) + 16) ^ 2 := by dsimp [Cg]; push_cast; ring
  exact cspIncidenceBudget_isLittleO_of_rpow_log hnNat hBelow hcNonneg (by norm_num : (0 : ℝ) < 1 / 2)
    hInc hCgNonneg (p := 2) hGates C d

end DeepSkipChain

end PvsNP
