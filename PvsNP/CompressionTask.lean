module

public import PvsNP.CircuitCNF
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-- A single-output Circuit-SAT instance with `n` input bits. -/
structure CircuitInstance (n : Nat) where
  wires : Nat
  circuit : Circuit n wires
  output : Fin wires

namespace CircuitInstance

def eval {n : Nat} (instance_ : CircuitInstance n) (input : Fin n → Bool) : Bool :=
  instance_.circuit.evalWires input instance_.output

def Accepting {n : Nat} (instance_ : CircuitInstance n) :=
  { input : Fin n → Bool // instance_.eval input = true }

def cnf {n : Nat} (instance_ : CircuitInstance n) : CNF (Fin instance_.wires) :=
  instance_.circuit.encode instance_.output

end CircuitInstance

/-- Models are counted over every declared variable, including any free variables. -/
def Models {v : Nat} (formula : CNF (Fin v)) :=
  { values : Fin v → Bool // formula.eval values = true }

/-- The set-of-clauses, set-of-literals representation used by the counting theorem. -/
abbrev CanonicalCNF (v : Nat) := Finset (Finset (Fin v × Bool))

def canonicalize {v : Nat} (formula : CNF (Fin v)) : CanonicalCNF v :=
  (formula.clauses.toList.map fun clause => clause.literals.toFinset).toFinset

def CanonicalModels {v : Nat} (formula : CanonicalCNF v) :=
  { values : Fin v → Bool // ∀ clause ∈ formula, ∃ lit ∈ clause, values lit.1 = lit.2 }

/-- Removing duplicate clauses and duplicate literals preserves every full assignment. -/
def canonicalModelsEquiv {v : Nat} (formula : CNF (Fin v)) :
    CanonicalModels (canonicalize formula) ≃ Models formula :=
  Equiv.subtypeEquivRight fun values => by
    rw [← CNF.sat_def, CNF.sat_iff_all_mem_sat]
    simp only [canonicalize, List.mem_toFinset, List.mem_map, CNF.Internal.mem_iff,
      ← Array.mem_toList_iff, CNF.Clause.sat_iff_exists_mem_eq, ← CNF.Clause.mem_literals_iff]
    constructor
    · intro h clause hClause
      simpa only [List.mem_toFinset] using h _ ⟨clause, hClause, rfl⟩
    · rintro h _ ⟨clause, hClause, rfl⟩
      simpa only [List.mem_toFinset] using h clause hClause

theorem canonicalize_width {v width : Nat} (formula : CNF (Fin v))
    (hWidth : ∀ clause ∈ formula.clauses, CNF.Clause.size clause ≤ width)
    (clause : Finset (Fin v × Bool)) (hClause : clause ∈ canonicalize formula) :
    clause.card ≤ width := by
  simp only [canonicalize, List.mem_toFinset, List.mem_map, Array.mem_toList_iff] at hClause
  obtain ⟨old, hOld, rfl⟩ := hClause
  exact (List.toFinset_card_le (l := old.literals)).trans
    (CNF.Clause.length_literals.trans_le (hWidth old hOld))

theorem canonicalize_clause_count_le {v : Nat} (formula : CNF (Fin v)) :
    (canonicalize formula).card ≤ formula.clauses.size := by
  simpa [canonicalize] using
    (List.toFinset_card_le (l := formula.clauses.toList.map fun clause => clause.literals.toFinset))

/-- The interpolation-scale exponent of the fixed-width exact SAT counter. -/
noncomputable def countingScale (v : Nat) : ℝ :=
  (v : ℝ) * (Real.log (Real.log (v + 16))) ^ 2 / Real.sqrt (Real.log (v + 16))

/-- A fixed polynomial in the original input count contributes a logarithmic term. -/
noncomputable def logTimeBudget (n v : Nat) (counterConstant overheadDegree : ℝ) : ℝ :=
  counterConstant * countingScale v + overheadDegree * Real.log ((n : ℝ) + 16)

theorem logTimeBudget_isLittleO_of_countingScale {n v : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hScale : (fun i => countingScale (v i)) =o[atTop] fun i => (n i : ℝ))
    (C d : ℝ) :
    (fun i => logTimeBudget (n i) (v i) C d) =o[atTop] fun i => (n i : ℝ) := by
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hShift : (fun i => (n i : ℝ) + 16) =O[atTop] fun i => (n i : ℝ) := by
    refine IsBigO.of_bound 17 ?_
    filter_upwards [hnReal.eventually_ge_atTop 1] with i hi
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    linarith
  have hLog := (Real.isLittleO_log_id_atTop.comp_tendsto hnShift).trans_isBigO hShift
  exact (hScale.const_mul_left C).add (hLog.const_mul_left d)

theorem logTimeBudget_isLittleO {n v : Nat → Nat} (hn : Tendsto n atTop atTop)
    (hBelow : ∀ i, n i ≤ v i) (c : Nat) (hAbove : ∀ i, v i ≤ c * n i) (C d : ℝ) :
    (fun i => logTimeBudget (n i) (v i) C d) =o[atTop] fun i => (n i : ℝ) := by
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hv : Tendsto (fun i => (v i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun i => by exact_mod_cast (hBelow i).trans (Nat.le_add_right _ _)) hnReal
  have hLogV := Real.tendsto_log_atTop.comp hv
  have hFraction : (fun i => (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 /
      Real.sqrt (Real.log ((v i : ℝ) + 16))) =o[atTop] (fun _ => (1 : ℝ)) := by
    have h := isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)
    have hRatio := (h.comp_tendsto hLogV).tendsto_div_nhds_zero
    apply (isLittleO_one_iff ℝ).mpr
    simpa [Function.comp_def, Real.rpow_natCast, Real.sqrt_eq_rpow] using hRatio
  have hLinear : (fun i => (v i : ℝ)) =O[atTop] fun i => (n i : ℝ) := by
    refine IsBigO.of_bound c (Eventually.of_forall fun i => ?_)
    simpa using (show (v i : ℝ) ≤ (c : ℝ) * (n i : ℝ) by exact_mod_cast hAbove i)
  have hScale : (fun i => countingScale (v i)) =o[atTop] fun i => (n i : ℝ) := by
    simpa [countingScale, mul_div_assoc] using hLinear.mul_isLittleO hFraction
  exact logTimeBudget_isLittleO_of_countingScale hn hScale C d

/-- Any superlinear variable count `v i ≤ c * n i * (log (n i + 16)) ^ α` with `α < 1 / 2`
still keeps `countingScale (v i) = o(n i)`. -/
theorem countingScale_isLittleO_of_rpow_log {n v : Nat → Nat}
    (hn : Tendsto n atTop atTop) (hBelow : ∀ i, n i ≤ v i)
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hAbove : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α) :
    (fun i => countingScale (v i)) =o[atTop] fun i => (n i : ℝ) := by
  let β : ℝ := max α 0
  have hβ0 : 0 ≤ β := le_max_right α 0
  have hβHalf : β < 1 / 2 := max_lt hα (by norm_num)
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnShift
  have hLogLogN : Tendsto (fun i => Real.log (Real.log ((n i : ℝ) + 16))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLogN
  let rem := fun i => (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2 /
    (Real.log ((n i : ℝ) + 16)) ^ (1 / 2 - β)
  have hRemLittleO : rem =o[atTop] (fun _ => (1 : ℝ)) := by
    have h := isLittleO_log_rpow_rpow_atTop 2 (show (0 : ℝ) < 1 / 2 - β by linarith)
    have hRatio := (h.comp_tendsto hLogN).tendsto_div_nhds_zero
    apply (isLittleO_one_iff ℝ).mpr
    simpa [rem, Function.comp_def, Real.rpow_natCast] using hRatio
  have hDom : (fun i => countingScale (v i)) =O[atTop] fun i => (n i : ℝ) * rem i := by
    refine IsBigO.of_bound (4 * c + 1) ?_
    filter_upwards [hAbove, hnShift.eventually_ge_atTop (c + 2),
      hLogN.eventually_ge_atTop 3, hLogLogN.eventually_ge_atTop (Real.log 3)]
      with i hVi hNBig hLN3 hLLN3
    have hLNPos : 0 < Real.log ((n i : ℝ) + 16) := by linarith
    have hLN1 : 1 ≤ Real.log ((n i : ℝ) + 16) := by linarith
    have hRpowLe : (Real.log ((n i : ℝ) + 16)) ^ α ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
      Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left α 0)
    have hRpowLe1 : (Real.log ((n i : ℝ) + 16)) ^ β ≤ Real.log ((n i : ℝ) + 16) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hLN1 (show β ≤ 1 by linarith)
    have hNShiftPos : 0 < (n i : ℝ) + 16 := by positivity
    have hLogLeShift : Real.log ((n i : ℝ) + 16) ≤ (n i : ℝ) + 16 :=
      (Real.log_le_sub_one_of_pos hNShiftPos).trans (by linarith)
    have hViBound : (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β :=
      hVi.trans (mul_le_mul_of_nonneg_left hRpowLe (by positivity))
    have hViCube : (v i : ℝ) + 16 ≤ ((n i : ℝ) + 16) ^ 3 := by
      have h1 : (v i : ℝ) ≤ c * ((n i : ℝ) + 16) * ((n i : ℝ) + 16) := by
        have hNLe : (n i : ℝ) ≤ (n i : ℝ) + 16 := by linarith
        have hBLe : (Real.log ((n i : ℝ) + 16)) ^ β ≤ (n i : ℝ) + 16 :=
          hRpowLe1.trans hLogLeShift
        calc
          (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := hViBound
          _ ≤ c * ((n i : ℝ) + 16) * ((n i : ℝ) + 16) := by gcongr
      have hSqGe1 : 1 ≤ ((n i : ℝ) + 16) * ((n i : ℝ) + 16) := by nlinarith
      nlinarith
    have hVShiftPos : 0 < (v i : ℝ) + 16 := by positivity
    have hLogVLe : Real.log ((v i : ℝ) + 16) ≤ 3 * Real.log ((n i : ℝ) + 16) := by
      calc
        Real.log ((v i : ℝ) + 16) ≤ Real.log (((n i : ℝ) + 16) ^ 3) :=
          Real.log_le_log hVShiftPos hViCube
        _ = 3 * Real.log ((n i : ℝ) + 16) := by rw [Real.log_pow]; norm_num
    have hLogNLeV : Real.log ((n i : ℝ) + 16) ≤ Real.log ((v i : ℝ) + 16) :=
      Real.log_le_log hNShiftPos (by exact_mod_cast Nat.add_le_add_right (hBelow i) 16)
    have hLogVPos : 0 < Real.log ((v i : ℝ) + 16) := lt_of_lt_of_le hLNPos hLogNLeV
    have hLLVLe : Real.log (Real.log ((v i : ℝ) + 16)) ≤
        2 * Real.log (Real.log ((n i : ℝ) + 16)) := by
      calc
        Real.log (Real.log ((v i : ℝ) + 16)) ≤ Real.log (3 * Real.log ((n i : ℝ) + 16)) :=
          Real.log_le_log hLogVPos hLogVLe
        _ = Real.log 3 + Real.log (Real.log ((n i : ℝ) + 16)) :=
          Real.log_mul (by norm_num) (ne_of_gt hLNPos)
        _ ≤ 2 * Real.log (Real.log ((n i : ℝ) + 16)) := by linarith
    have hLLVNonneg : 0 ≤ Real.log (Real.log ((v i : ℝ) + 16)) :=
      Real.log_nonneg (by linarith)
    have hSqLe : (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 ≤
        4 * (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2 := by nlinarith
    have hSqrtGe : Real.sqrt (Real.log ((n i : ℝ) + 16)) ≤
        Real.sqrt (Real.log ((v i : ℝ) + 16)) := Real.sqrt_le_sqrt hLogNLeV
    have hSqrtPos : 0 < Real.sqrt (Real.log ((n i : ℝ) + 16)) := Real.sqrt_pos.mpr hLNPos
    have hScaleNonneg : 0 ≤ countingScale (v i) := by
      unfold countingScale
      positivity
    have hRemNonneg : 0 ≤ rem i := by
      dsimp only [rem]
      positivity
    rw [Real.norm_of_nonneg hScaleNonneg, Real.norm_of_nonneg (by positivity)]
    have hRpowDiv : (Real.log ((n i : ℝ) + 16)) ^ β / Real.sqrt (Real.log ((n i : ℝ) + 16)) =
        1 / (Real.log ((n i : ℝ) + 16)) ^ (1 / 2 - β) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hLNPos]
      apply eq_one_div_of_mul_eq_one_left
      rw [← Real.rpow_add hLNPos]
      norm_num
    calc
      countingScale (v i)
        = (v i : ℝ) * (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 /
            Real.sqrt (Real.log ((v i : ℝ) + 16)) := rfl
      _ ≤ (v i : ℝ) * (4 * (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2) /
            Real.sqrt (Real.log ((n i : ℝ) + 16)) := by
          gcongr
      _ ≤ (c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β) *
            (4 * (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2) /
            Real.sqrt (Real.log ((n i : ℝ) + 16)) := by
          gcongr
      _ = 4 * c * (n i : ℝ) *
            ((Real.log ((n i : ℝ) + 16)) ^ β / Real.sqrt (Real.log ((n i : ℝ) + 16))) *
            (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2 := by ring
      _ = 4 * c * (n i : ℝ) * rem i := by
          rw [hRpowDiv]
          dsimp only [rem]
          ring
      _ ≤ (4 * c + 1) * ((n i : ℝ) * rem i) := by nlinarith
  have hNBigO : (fun i => (n i : ℝ)) =O[atTop] fun i => (n i : ℝ) := isBigO_refl _ _
  exact hDom.trans_isLittleO (by simpa using hNBigO.mul_isLittleO hRemLittleO)

/-- General version without a `n i ≤ v i` lower bound, covering sublinear, linear, and
superlinear factor variable counts `v i ≤ c * n i * (log (n i + 16)) ^ α` (`α < 1 / 2`). -/
theorem countingScale_isLittleO_of_rpow_log_any {n v : Nat → Nat}
    (hn : Tendsto n atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hAbove : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α) :
    (fun i => countingScale (v i)) =o[atTop] fun i => (n i : ℝ) := by
  let vMax : Nat → Nat := fun i => max (v i) (n i)
  have hBelowMax : ∀ i, n i ≤ vMax i := fun i => le_max_right _ _
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num))
        (tendsto_natCast_atTop_atTop.comp hn))
  let β : ℝ := max α 0
  have hAboveMax : ∀ᶠ i in atTop,
      (vMax i : ℝ) ≤ (c + 1) * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by
    filter_upwards [hAbove, hLogN.eventually_ge_atTop 1] with i hVi hLN1
    have hCast : (vMax i : ℝ) = max (v i : ℝ) (n i : ℝ) := by simp [vMax]
    rw [hCast]
    apply max_le
    · have hRpowLe : (Real.log ((n i : ℝ) + 16)) ^ α ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
        Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left α 0)
      have h1 : (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β :=
        hVi.trans (mul_le_mul_of_nonneg_left hRpowLe (by positivity))
      have h2 : 0 ≤ (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by positivity
      linarith
    · have hGe1 : 1 ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
        Real.one_le_rpow hLN1 (le_max_right α 0)
      have h1 : (n i : ℝ) ≤ 1 * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by nlinarith
      have h2 : 0 ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by positivity
      linarith
  have hMaxScale : (fun i => countingScale (vMax i)) =o[atTop] fun i => (n i : ℝ) :=
    countingScale_isLittleO_of_rpow_log hn hBelowMax (by linarith)
      (max_lt hα (by norm_num)) hAboveMax
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hSqrtLittleO : (fun i => Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2) =o[atTop]
      fun i => (n i : ℝ) := by
    have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
    have hLogLittle := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp_tendsto hnShift
    have hSq : (fun i => (Real.log ((n i : ℝ) + 16)) ^ 2) =o[atTop]
        fun i => ((n i : ℝ) + 16) ^ (1 / 2 : ℝ) := by
      have hMul := hLogLittle.mul hLogLittle
      refine hMul.congr' (Eventually.of_forall fun i => by dsimp only [Function.comp_apply]; ring)
        (Eventually.of_forall fun i => ?_)
      dsimp only [Function.comp_apply]
      rw [← Real.rpow_add (by positivity : 0 < (n i : ℝ) + 16)]
      norm_num
    have hShiftSqrt : (fun i => ((n i : ℝ) + 16) ^ (1 / 2 : ℝ)) =O[atTop]
        fun i => Real.sqrt (n i : ℝ) := by
      refine IsBigO.of_bound 2 ?_
      filter_upwards [hnReal.eventually_ge_atTop 16] with i hi
      have hPos1 : 0 ≤ ((n i : ℝ) + 16) ^ (1 / 2 : ℝ) := by positivity
      rw [Real.norm_of_nonneg hPos1, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_eq_rpow]
      have h4 : (n i : ℝ) + 16 ≤ 4 * (n i : ℝ) := by linarith
      calc
        Real.sqrt ((n i : ℝ) + 16) ≤ Real.sqrt (4 * (n i : ℝ)) := Real.sqrt_le_sqrt h4
        _ = 2 * Real.sqrt (n i : ℝ) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
    have hSqN := hSq.trans_isBigO hShiftSqrt
    have hSqrtRefl : (fun i => Real.sqrt (n i : ℝ)) =O[atTop] fun i => Real.sqrt (n i : ℝ) :=
      isBigO_refl _ _
    have hProd := hSqrtRefl.mul_isLittleO hSqN
    refine hProd.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [hnReal.eventually_ge_atTop 0] with i hi
    exact Real.mul_self_sqrt hi
  have hDomSum : (fun i => countingScale (v i)) =O[atTop]
      fun i => countingScale (vMax i) +
        Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2 := by
    have hLog16Pos : 0 < Real.sqrt (Real.log 16) :=
      Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
    refine IsBigO.of_bound (max 2 (1 / Real.sqrt (Real.log 16))) ?_
    filter_upwards [hnReal.eventually_ge_atTop 16] with i hi
    have hScaleNonneg : 0 ≤ countingScale (v i) := by unfold countingScale; positivity
    have hMaxNonneg : 0 ≤ countingScale (vMax i) := by unfold countingScale; positivity
    have hTermNonneg : 0 ≤ Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2 := by positivity
    rw [Real.norm_of_nonneg hScaleNonneg, Real.norm_of_nonneg (by positivity)]
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
    by_cases hSmall : (v i : ℝ) ≤ Real.sqrt (n i : ℝ)
    · have hVLeN : (v i : ℝ) ≤ (n i : ℝ) := by
        have h1 : Real.sqrt (n i : ℝ) ≤ (n i : ℝ) := by
          have hSq := Real.mul_self_sqrt (show (0 : ℝ) ≤ (n i : ℝ) by positivity)
          have hGe1 : 1 ≤ Real.sqrt (n i : ℝ) := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt (by linarith)
          nlinarith
        exact hSmall.trans h1
      have hLogVLeN : Real.log ((v i : ℝ) + 16) ≤ Real.log ((n i : ℝ) + 16) :=
        Real.log_le_log (by positivity) (by linarith)
      have hLLVLe : Real.log (Real.log ((v i : ℝ) + 16)) ≤ Real.log ((n i : ℝ) + 16) := by
        have hLVPos : 0 < Real.log ((v i : ℝ) + 16) := Real.log_pos (by linarith)
        exact ((Real.log_le_sub_one_of_pos hLVPos).trans (by linarith)).trans hLogVLeN
      have hLLVNonneg : 0 ≤ Real.log (Real.log ((v i : ℝ) + 16)) :=
        Real.log_nonneg ((Real.le_log_iff_exp_le (by positivity)).mpr (hExp1Le4.trans (by linarith)))
      have hSqLL : (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 ≤
          (Real.log ((n i : ℝ) + 16)) ^ 2 := by nlinarith
      have hSqrt16 : Real.sqrt (Real.log 16) ≤ Real.sqrt (Real.log ((v i : ℝ) + 16)) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by linarith))
      have hBound1 : countingScale (v i) ≤
          (1 / Real.sqrt (Real.log 16)) *
            (Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2) := by
        calc
          countingScale (v i)
            = (v i : ℝ) * (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 /
                Real.sqrt (Real.log ((v i : ℝ) + 16)) := rfl
          _ ≤ Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2 /
                Real.sqrt (Real.log 16) := by gcongr
          _ = (1 / Real.sqrt (Real.log 16)) *
                (Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2) := by ring
      have hCoeff : 1 / Real.sqrt (Real.log 16) ≤ max 2 (1 / Real.sqrt (Real.log 16)) :=
        le_max_right _ _
      have hStep1 : countingScale (v i) ≤
          max 2 (1 / Real.sqrt (Real.log 16)) *
            (Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2) :=
        hBound1.trans (mul_le_mul_of_nonneg_right hCoeff hTermNonneg)
      have hExtra : 0 ≤ max 2 (1 / Real.sqrt (Real.log 16)) * countingScale (vMax i) :=
        mul_nonneg (le_trans (by norm_num) (le_max_left 2 _)) hMaxNonneg
      linarith
    · push Not at hSmall
      by_cases hGeN : n i ≤ v i
      · have hEq : vMax i = v i := max_eq_left hGeN
        rw [hEq]
        have hCoeff : (2 : ℝ) ≤ max 2 (1 / Real.sqrt (Real.log 16)) := le_max_left _ _
        have hStep1 : 2 * countingScale (v i) ≤
            max 2 (1 / Real.sqrt (Real.log 16)) * countingScale (v i) :=
          mul_le_mul_of_nonneg_right hCoeff hScaleNonneg
        have hExtra : 0 ≤ max 2 (1 / Real.sqrt (Real.log 16)) *
            (Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2) :=
          mul_nonneg (le_trans (by norm_num) (le_max_left 2 _)) hTermNonneg
        linarith
      · push Not at hGeN
        have hEq : vMax i = n i := max_eq_right (le_of_lt hGeN)
        rw [hEq]
        have hNSq : (n i : ℝ) ≤ (v i : ℝ) ^ 2 := by
          have h := mul_le_mul hSmall.le hSmall.le (Real.sqrt_nonneg _) (by positivity)
          rwa [Real.mul_self_sqrt (by positivity), ← sq] at h
        have hPow4 : (n i : ℝ) + 16 ≤ ((v i : ℝ) + 16) ^ 4 := by
          have hV1 : 4 ≤ (v i : ℝ) := by
            have h4 : Real.sqrt 16 = 4 := by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            exact (h4 ▸ Real.sqrt_le_sqrt hi).trans hSmall.le
          nlinarith
        have hLog4 : Real.log ((n i : ℝ) + 16) ≤ 4 * Real.log ((v i : ℝ) + 16) := by
          calc
            Real.log ((n i : ℝ) + 16) ≤ Real.log (((v i : ℝ) + 16) ^ 4) :=
              Real.log_le_log (by positivity) hPow4
            _ = 4 * Real.log ((v i : ℝ) + 16) := by rw [Real.log_pow]; norm_num
        have hSqrtHalf : Real.sqrt (Real.log ((n i : ℝ) + 16)) / 2 ≤
            Real.sqrt (Real.log ((v i : ℝ) + 16)) := by
          have hDiv : Real.log ((n i : ℝ) + 16) / 4 ≤ Real.log ((v i : ℝ) + 16) := by linarith
          have hSqrt4 : Real.sqrt 4 = 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
          calc
            Real.sqrt (Real.log ((n i : ℝ) + 16)) / 2
              = Real.sqrt (Real.log ((n i : ℝ) + 16) / 4) := by
                rw [Real.sqrt_div (le_of_lt (Real.log_pos (by linarith))), hSqrt4]
            _ ≤ Real.sqrt (Real.log ((v i : ℝ) + 16)) := Real.sqrt_le_sqrt hDiv
        have hLogVLeN : Real.log ((v i : ℝ) + 16) ≤ Real.log ((n i : ℝ) + 16) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hGeN.le 16)
        have hLLVLe : Real.log (Real.log ((v i : ℝ) + 16)) ≤
            Real.log (Real.log ((n i : ℝ) + 16)) :=
          Real.log_le_log (Real.log_pos (by linarith)) hLogVLeN
        have hLLVNonneg : 0 ≤ Real.log (Real.log ((v i : ℝ) + 16)) :=
          Real.log_nonneg ((Real.le_log_iff_exp_le (by positivity)).mpr (hExp1Le4.trans (by linarith)))
        have hSqLL : (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 ≤
            (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2 := by nlinarith
        have hVLeN : (v i : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hGeN.le
        have hSqrtNPos : 0 < Real.sqrt (Real.log ((n i : ℝ) + 16)) / 2 := by
          have : 0 < Real.log ((n i : ℝ) + 16) := Real.log_pos (by linarith)
          positivity
        have hBound2 : countingScale (v i) ≤ 2 * countingScale (n i) := by
          calc
            countingScale (v i)
              = (v i : ℝ) * (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 /
                  Real.sqrt (Real.log ((v i : ℝ) + 16)) := rfl
            _ ≤ (n i : ℝ) * (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2 /
                  (Real.sqrt (Real.log ((n i : ℝ) + 16)) / 2) := by
                have hNum : (v i : ℝ) * (Real.log (Real.log ((v i : ℝ) + 16))) ^ 2 ≤
                    (n i : ℝ) * (Real.log (Real.log ((n i : ℝ) + 16))) ^ 2 :=
                  mul_le_mul hVLeN hSqLL (by positivity) (by positivity)
                exact div_le_div₀ (by positivity) hNum hSqrtNPos hSqrtHalf
            _ = 2 * countingScale (n i) := by unfold countingScale; ring
        have hCoeff : (2 : ℝ) ≤ max 2 (1 / Real.sqrt (Real.log 16)) := le_max_left _ _
        have hScaleNNonneg : 0 ≤ countingScale (n i) := by unfold countingScale; positivity
        have hStep2 : 2 * countingScale (n i) ≤
            max 2 (1 / Real.sqrt (Real.log 16)) * countingScale (n i) :=
          mul_le_mul_of_nonneg_right hCoeff hScaleNNonneg
        have hExtra : 0 ≤ max 2 (1 / Real.sqrt (Real.log 16)) *
            (Real.sqrt (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ 2) :=
          mul_nonneg (le_trans (by norm_num) (le_max_left 2 _)) hTermNonneg
        linarith
  exact hDomSum.trans_isLittleO (hMaxScale.add hSqrtLittleO)

theorem logTimeBudget_isLittleO_of_rpow_log_any {n v : Nat → Nat}
    (hn : Tendsto n atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hAbove : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => logTimeBudget (n i) (v i) C d) =o[atTop] fun i => (n i : ℝ) :=
  logTimeBudget_isLittleO_of_countingScale hn
    (countingScale_isLittleO_of_rpow_log_any hn hc hα hAbove) C d

theorem logTimeBudget_isLittleO_of_rpow_log {n v : Nat → Nat}
    (hn : Tendsto n atTop atTop) (hBelow : ∀ i, n i ≤ v i)
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hAbove : ∀ᶠ i in atTop,
      (v i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => logTimeBudget (n i) (v i) C d) =o[atTop] fun i => (n i : ℝ) :=
  logTimeBudget_isLittleO_of_countingScale hn
    (countingScale_isLittleO_of_rpow_log hn hBelow hc hα hAbove) C d

/-- Direct Tseitin encoding of any circuit family with superlinear gate count
`O(n * (log n) ^ α)` (`α < 1 / 2`, e.g. `n * (log n) ^ (1 / 3)`) already runs in
`2 ^ o(n)` deterministic time under the fixed-width `#3-SAT` counter. -/
theorem superlinear_tseitin_isLittleO {n : Nat → Nat}
    (inst : (i : Nat) → CircuitInstance (n i))
    (hn : Tendsto n atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hGates : ∀ᶠ i in atTop,
      ((inst i).circuit.gateCount : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => logTimeBudget (n i) (inst i).wires C d) =o[atTop] fun i => (n i : ℝ) := by
  let β : ℝ := max α 0
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hnShift : Tendsto (fun i => (n i : ℝ) + 16) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnShift
  apply logTimeBudget_isLittleO_of_rpow_log hn
    (fun i => by rw [Circuit.wire_count (inst i).circuit]; exact Nat.le_add_right _ _)
    (show 0 ≤ c + 1 by linarith) (max_lt hα (by norm_num) : β < 1 / 2)
  filter_upwards [hGates, hLogN.eventually_ge_atTop 1] with i hG hLN1
  have hWires : ((inst i).wires : ℝ) = (n i : ℝ) + ((inst i).circuit.gateCount : ℝ) := by
    exact_mod_cast Circuit.wire_count (inst i).circuit
  have hRpowGe1 : 1 ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
    Real.one_le_rpow hLN1 (le_max_right α 0)
  have hRpowLe : (Real.log ((n i : ℝ) + 16)) ^ α ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left α 0)
  have hGBound : ((inst i).circuit.gateCount : ℝ) ≤
      c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β :=
    hG.trans (mul_le_mul_of_nonneg_left hRpowLe (by positivity))
  have hNBound : (n i : ℝ) ≤ 1 * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by nlinarith
  rw [hWires]
  nlinarith

/-- Any runtime bounded by the certified budget is subexponential in the original bit count. -/
theorem subexponential_of_logTimeBudget {n v : Nat → Nat} {time : Nat → ℝ} {C d : ℝ}
    (hBudget : (fun i => logTimeBudget (n i) (v i) C d) =o[atTop] fun i => (n i : ℝ))
    (hTime : ∀ᶠ i in atTop, time i ≤ (2 : ℝ) ^ logTimeBudget (n i) (v i) C d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, time i ≤ (2 : ℝ) ^ (ε * (n i : ℝ)) := by
  intro ε hε
  filter_upwards [hTime, hBudget.def hε] with i hTime_i hBound
  apply hTime_i.trans
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
  have hn : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hBound)

/-- The task uses a family index `i`. Its actual input count is `n i`.
The last field is a bound on the exponent of the composed algorithm, under the
fixed-width counter's runtime bound and polynomial preprocessing/encoding overhead. -/
structure CircuitCompressionTask (n : Nat → Nat)
    (source target : (i : Nat) → CircuitInstance (n i)) : Prop where
  inputsGrow : Tendsto n atTop atTop
  sourceSize : ∃ lower upper : Nat, 0 < lower ∧ 0 < upper ∧
    ∀ i, 2 ≤ n i →
      n i * (n i).log2 ≤ lower * (source i).circuit.gateCount ∧
      (source i).circuit.gateCount ≤ upper * (n i * (n i).log2)
  equivalent : ∀ i input, (target i).eval input = (source i).eval input
  exactCount : ∀ i, Nonempty (Models (target i).cnf ≃ (source i).Accepting)
  variableBound : ∃ c : Nat, ∀ i, (target i).wires ≤ c * n i
  clauses : ∃ c : Nat, ∀ i, (target i).cnf.clauses.size ≤ c * n i
  width : ∀ i (clause : CNF.Clause (Fin (target i).wires)),
    clause ∈ (target i).cnf.clauses → clause.size ≤ 3
  subexponential : ∀ C d : ℝ,
    (fun i => logTimeBudget (n i) (target i).wires C d) =o[atTop] fun i => (n i : ℝ)

end PvsNP
