module

public import Complexity.Computability.MCSP.Magnification
public import Complexity.Foundations.Data.Nat.Asymptotics

/-! Research targets in the pinned CSLib Frontier model of P and NP. -/

@[expose] public section

namespace PvsNP.Frontier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Filter Turing.MultiTapeTM

/-- Gate complexity of deciding exact MCSP with size cutoff `m^k`
on truth tables of length `2^m`. -/
noncomputable def polynomialCutoffGateCount (k m : ℕ) : ℕ :=
  complexity interpretation (single ((GapMCSP.yesSet fun j => j ^ k).slice (2 ^ m)))

/-- The lower bound sufficient for the existing hardness magnification theorem. -/
def PolynomialCutoffLowerBound (k : ℕ) : Prop :=
  ∀ c > 0, ∃ m, 2 ^ m * c * (m + 1) ^ c < polynomialCutoffGateCount k m

theorem p_ne_np_of_polynomialCutoffLowerBound {k : ℕ} (h : PolynomialCutoffLowerBound k) :
    P encBits ≠ NP encBits :=
  Cslib.MCSP.P_ne_NP_of_yesSet_pow_hard k h

/-- An infinitely-often bound of order `N^(1+1/d)` suffices, with the integer
rounding made explicit and `N = 2^m`. -/
theorem p_ne_np_of_superlinear_power_lower_bound {k d : ℕ} (hd : 0 < d)
    (h : ∃ᶠ m in atTop, 2 ^ m * 2 ^ (m / d) ≤ polynomialCutoffGateCount k m) :
    P encBits ≠ NP encBits := by
  apply p_ne_np_of_polynomialCutoffLowerBound (k := k)
  intro c _
  have hDominates := Nat.eventually_mul_add_one_pow_le_pow_div (c + 1) c d
    (show 1 < (2 : ℕ) by decide) hd
  obtain ⟨m, hSize, hGrowth⟩ := (h.and_eventually hDominates).exists
  have hStrict : c * (m + 1) ^ c < (c + 1) * (m + 1) ^ c :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self c) (Nat.pow_pos (Nat.succ_pos m))
  refine ⟨m, ?_⟩
  calc
    2 ^ m * c * (m + 1) ^ c = 2 ^ m * (c * (m + 1) ^ c) := Nat.mul_assoc ..
    _ < 2 ^ m * 2 ^ (m / d) :=
      Nat.mul_lt_mul_of_pos_left (hStrict.trans_le hGrowth) (by positivity)
    _ ≤ polynomialCutoffGateCount k m := hSize

end PvsNP.Frontier
