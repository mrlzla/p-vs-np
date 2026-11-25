module

public import MCSPJuntaRadius

/-! An explicit growing prefix family and a comparison with the coded
radius-four controls. -/

@[expose] public section

namespace PvsNP.Frontier.GrowingPrefix

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates CommunicationCut SuperTwoN PatchedCut PermutedCut
open scoped Classical

private theorem prefix_margin (r : ℕ) (hr : 10 ≤ r) : 2 * r + 9 ≤ 2 ^ r := by
  refine Nat.le_induction (m := 10) (P := fun r _ => 2 * r + 9 ≤ 2 ^ r) (by decide) ?_ r hr
  intro k _ ih
  rw [pow_succ' 2 k]
  omega

private theorem code_patch_budget {r m : ℕ} (hr : 10 ≤ r) (hm : 2 ^ r ≤ m) :
    2 ^ r * (2 * r + 2) + 3 + 5 * m + 13 ≤ m ^ 2 := by
  have hR := (prefix_margin r hr).trans hm
  have h := Nat.mul_le_mul_left m hR
  have hE : m * (2 * r + 9) = (2 * r + 2) * m + 7 * m := by ring
  rw [hE, ← pow_two] at h
  have hd := Nat.mul_le_mul_left (2 * r + 2) hm
  rw [Nat.mul_comm (2 * r + 2) (2 ^ r)] at hd
  omega

theorem patched_prefix_wide_accepted {r s : ℕ} (hr : 10 ≤ r) (hs : 2 ^ r ≤ s)
    (f : BooleanFunction r) (D : Finset (Fin (2 ^ (r + (s + 1))))) (hD : D.card ≤ 4) :
    mcspSquare (r + (s + 1)) (patch D (probe s f)) = true := by
  let c : JuntaRadius.CodeFor r (r + (s + 1)) := (fun j => .inl (Fin.castAdd (s + 1) j), f)
  change mcspSquare (r + (s + 1)) (patch D (MCSP.truthTable _ (JuntaRadius.value c))) = true
  exact JuntaRadius.patched_code_of_budget c D hD (JuntaRadius.value_costFor c)
    (code_patch_budget hr (by omega))

theorem four_power_le_exp (s : ℕ) (hs : 16 ≤ s) : s ^ 4 ≤ 2 ^ s := by
  refine Nat.le_induction (m := 16) (P := fun s _ => s ^ 4 ≤ 2 ^ s) (by decide) ?_ s hs
  intro t ht ih
  have h : 8 * (t + 1) ≤ 9 * t := by omega
  have hPow := Nat.pow_le_pow_left h 4
  rw [mul_pow, mul_pow] at hPow
  have hBase : (9 : ℕ) ^ 4 ≤ 8 ^ 4 * 2 := by decide
  have hScaled : 8 ^ 4 * (t + 1) ^ 4 ≤ 8 ^ 4 * (2 * t ^ 4) := calc
    _ ≤ 9 ^ 4 * t ^ 4 := hPow
    _ ≤ (8 ^ 4 * 2) * t ^ 4 := Nat.mul_le_mul_right _ hBase
    _ = _ := by rw [Nat.mul_assoc]
  have hStep := (Nat.mul_le_mul_left_iff (by decide : 0 < (8 : ℕ) ^ 4)).mp hScaled
  rw [pow_succ' 2 t]
  exact hStep.trans (Nat.mul_le_mul_left 2 ih)

theorem wide_exponent_le {r s : ℕ} (hr : 10 ≤ r) (hs : 2 ^ r ≤ s) :
    wideExponent r s ≤ 100 * s ^ 3 := by
  let m := r + (s + 1)
  have hBig : 1024 ≤ s := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans hs
  have hWidth := (prefix_margin r hr).trans hs
  have hm : m ≤ 2 * s := by dsimp [m]; omega
  have hBits : (m + 1).log2 + 1 ≤ m + 2 := by have := Nat.log2_le_self (m + 1); omega
  have hCoeff : 3 + 4 * ((m + 1).log2 + 1) ≤ 15 * s := by omega
  have hSq : m ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left hm 2
  have hTerm := Nat.mul_le_mul hCoeff hSq
  rw [show (15 * s) * (2 * s) ^ 2 = 60 * s ^ 3 by ring] at hTerm
  have hDesc : descriptionBitBound m ≤ 60 * s ^ 3 + 12 * s := by
    dsimp only [descriptionBitBound]
    omega
  have hCube : s ≤ s ^ 3 :=
    calc
      _ = s * 1 := by rw [Nat.mul_one]
      _ ≤ s * s ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_pos (by omega : 0 < s))
      _ = _ := by ring
  change 2 ^ r + 2 ^ r + (m + 1) * 4 + descriptionBitBound m ≤ _
  omega

private theorem wide_room {r s : ℕ} (hr : 10 ≤ r) (hs : 2 ^ r ≤ s) :
    wideExponent r s < 2 ^ s := by
  have hBig : 1024 ≤ s := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans hs
  have hLt : 100 * s ^ 3 < s ^ 4 := by
    rw [pow_succ' s 3]
    exact Nat.mul_lt_mul_of_pos_right (by omega : 100 < s) (Nat.pow_pos (by omega : 0 < s))
  exact (wide_exponent_le hr hs).trans_lt (hLt.trans_le (four_power_le_exp s (by omega)))

/-- Prefix widths 10, 11, ... are available, with suffix width at least
2^r. On the explicit choice s = 2^r the prefix width grows logarithmically
in the represented arity. -/
theorem exists_growing_selector (r s : ℕ) (hr : 10 ≤ r) (hs : 2 ^ r ≤ s) :
    ∃ h : BooleanFunction s, WideTests (mcspSquare (r + (s + 1))) h := by
  have hGap : wideExponent r s < 2 ^ s - (∅ : Finset (BitString s)).card := by
    simpa only [Finset.card_empty, Nat.sub_zero] using wide_room hr hs
  obtain ⟨h, _, hh⟩ := exists_wide_selector_with ∅ (fun _ => false) hGap (patched_prefix_wide_accepted hr hs)
  exact ⟨h, hh⟩

theorem controlFor_implies_exact {r m : ℕ} (hr : 10 ≤ r) (hm : 2 ^ r ≤ m) {T : BitString (2 ^ m)}
    (ht : JuntaRadius.controlFor r m T = true) : mcspSquare m T = true := by
  obtain ⟨c, D, hD, he⟩ := (JuntaRadius.controlFor_iff T).mp ht
  rw [he]
  exact JuntaRadius.patched_code_of_budget c D hD (JuntaRadius.value_costFor c) (code_patch_budget hr hm)

theorem controlFor_sparse {r m : ℕ} (hr : 10 ≤ r) (hm : 2 ^ r ≤ m) :
    (acceptingTables (JuntaRadius.controlFor r m)).card ≤ 2 ^ descriptionBitBound m := by
  apply le_trans _ (card_accepting_mcspSquare_le m)
  apply Finset.card_le_card
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, controlFor_implies_exact hr hm (Finset.mem_filter.mp hT).2⟩

theorem controlFor_passes_wide_cuts {r s : ℕ} (hr : 10 ≤ r) (hs : 2 ^ r ≤ s)
    {h : BooleanFunction s} (hh : WideTests (mcspSquare (r + (s + 1))) h)
    (e : Equiv.Perm (Fin (r + (s + 1)))) (f g : BooleanFunction r)
    (D : Finset (Fin (2 ^ (r + (s + 1))))) (hD : D.card ≤ 4) :
    JuntaRadius.controlFor r (r + (s + 1)) (patch D (wideMixed h f g ∘ tablePerm e)) =
      true ↔ f = g := by
  constructor
  · intro h
    exact (wide_transport square_comp_tablePerm hh e f g D hD).mp (controlFor_implies_exact hr (by omega) h)
  · intro he
    have hDiag : wideMixed h f g = probe s g := by rw [he, wideMixed, splice_self]
    obtain ⟨c, hc⟩ := JuntaRadius.prefix_code_after_perm g e
    rw [hDiag]
    exact (JuntaRadius.controlFor_iff _).mpr ⟨c, D, hD, congrArg (patch D) hc⟩

#print axioms exists_growing_selector
#print axioms controlFor_passes_wide_cuts


section StartingWidth

theorem patched_andTen_accepted {s : ℕ} (hm : 32 ≤ 10 + s) (D : Finset (Fin (2 ^ (10 + s))))
    (hD : D.card ≤ 4) :
    mcspSquare (10 + s) (patch D (MCSP.truthTable _ (JuntaRadius.andTen (s := s)))) = true := by
  let c : JuntaRadius.CodeFor 10 (10 + s) :=
    (fun j => .inl (Fin.castAdd s j), fun a => decide (∀ j, a j = true))
  have hv : complexity interpretation (single (JuntaRadius.value c)) ≤ 11 :=
    JuntaRadius.andTen_cost
  change mcspSquare (10 + s) (patch D (MCSP.truthTable _ (JuntaRadius.value c))) = true
  refine JuntaRadius.patched_code_of_budget c D hD hv ?_
  have h := Nat.mul_le_mul_right (10 + s) hm
  rw [← pow_two] at h
  omega

/-- At arity 32, every four-flip placement of ten-way AND is already a
separating example for the old nine-slot control. -/
theorem patched_andTen_breaks_nine_32 (D : Finset (Fin (2 ^ 32))) (hD : D.card ≤ 4) :
    let T := patch D (MCSP.truthTable 32 (JuntaRadius.andTen (s := 22)))
    mcspSquare 32 T = true ∧ JuntaRadius.control 32 T = false := by
  refine ⟨patched_andTen_accepted (s := 22) (by decide) D hD, ?_⟩
  exact JuntaRadius.andTen_patch_rejected (s := 22) D (by omega)

private theorem patched_prefix_shannon {k d s : ℕ} (f : BooleanFunction (k + d))
    (D : Finset (Fin (2 ^ (k + d + (s + 1))))) (hD : D.card ≤ 4)
    (hBudget : ShannonSynthesis.bound k d + 5 * (k + d + (s + 1)) + 13 ≤ (k + d + (s + 1)) ^ 2) :
    mcspSquare (k + d + (s + 1)) (patch D (probe s f)) = true := by
  let c : JuntaRadius.CodeFor (k + d) (k + d + (s + 1)) :=
    (fun j => .inl (Fin.castAdd (s + 1) j), f)
  have hv : complexity interpretation (single (JuntaRadius.value c)) ≤ ShannonSynthesis.bound k d :=
    RefinedCut.shannon_lift f (Fin.castAdd (s + 1))
  exact JuntaRadius.patched_code_of_budget c D hD hv hBudget

/-- For ten prefix bits, the checked Shannon circuit bound already fits at
represented arity 43, even with all four flips. -/
theorem exists_ten_selector_43 : ∃ h : BooleanFunction 32, WideTests (mcspSquare 43) h := by
  have hGap : wideExponent 10 32 < 2 ^ 32 - (∅ : Finset (BitString 32)).card := by decide
  obtain ⟨h, _, hh⟩ := exists_wide_selector_with (r := 10) (s := 32) ∅ (fun _ => false) hGap
    (fun f D hD => patched_prefix_shannon (k := 2) (d := 8) (s := 32) f D hD (by decide))
  exact ⟨h, hh⟩

/-- Ten-way AND is a diagonal of the ten-bit family. The nine-slot control
already misses its unpatched form. -/
theorem ten_prefix_breaks_nine_43 :
    ∃ h : BooleanFunction 32, WideTests (mcspSquare 43) h ∧
      ∃ f : BooleanFunction 10, mcspSquare 43 (wideMixed h f f) = true ∧
        JuntaRadius.control 43 (wideMixed h f f) = false := by
  obtain ⟨h, hh⟩ := exists_ten_selector_43
  let f : BooleanFunction 10 := fun z => decide (∀ j, z j = true)
  refine ⟨h, hh, f, ?_⟩
  unfold wideMixed
  rw [splice_self]
  exact JuntaRadius.andTen_separates (s := 33) (by decide)

end StartingWidth

theorem log_width_stage (r : ℕ) (hr : 10 ≤ r) :
    2 ^ r ≤ r + (2 ^ r + 1) ∧ r + (2 ^ r + 1) < 2 ^ (r + 1) ∧
      ∃ h : BooleanFunction (2 ^ r), WideTests (mcspSquare (r + (2 ^ r + 1))) h := by
  have hm := prefix_margin r hr
  exact ⟨by omega, by rw [pow_succ']; omega, exists_growing_selector r (2 ^ r) hr le_rfl⟩

section SlowGrowth

/-- Give the finite circuit constant for each width room to be smaller than
the represented arity by a factor of at least r. -/
noncomputable def slowSuffix (r : ℕ) : ℕ :=
  max (2 ^ r) (r * (JuntaRadius.controlFor_linear r).choose)

noncomputable def slowArity (r : ℕ) : ℕ := r + (slowSuffix r + 1)

theorem slow_bound (r : ℕ) :
    r * complexity interpretation (single (JuntaRadius.controlFor r (slowArity r))) ≤
      slowArity r * 2 ^ slowArity r := by
  have hC := (JuntaRadius.controlFor_linear r).choose_spec (slowArity r)
  have hW : r * (JuntaRadius.controlFor_linear r).choose ≤ slowArity r := by
    have hx : r * (JuntaRadius.controlFor_linear r).choose ≤ slowSuffix r := le_max_right _ _
    have hy : slowSuffix r ≤ slowArity r := by unfold slowArity; omega
    exact hx.trans hy
  calc
    _ ≤ r * ((JuntaRadius.controlFor_linear r).choose * 2 ^ slowArity r) := Nat.mul_le_mul_left _ hC
    _ = (r * (JuntaRadius.controlFor_linear r).choose) * 2 ^ slowArity r := by rw [Nat.mul_assoc]
    _ ≤ _ := Nat.mul_le_mul_right _ hW

/-- An unbounded-width family of patched tests whose sparse control costs at
most (N log₂ N)/r gates. The width may grow much slower than log₂ m. -/
theorem growing_sparse_control_below_nlogn (r : ℕ) (hr : 10 ≤ r) :
    ∃ h : BooleanFunction (slowSuffix r),
      WideTests (mcspSquare (slowArity r)) h ∧
      (acceptingTables (JuntaRadius.controlFor r (slowArity r))).card ≤ 2 ^ descriptionBitBound (slowArity r) ∧
      r * complexity interpretation (single (JuntaRadius.controlFor r (slowArity r))) ≤ slowArity r * 2 ^ slowArity r ∧
      ∀ (e : Equiv.Perm (Fin (slowArity r))) (f g : BooleanFunction r)
        (D : Finset (Fin (2 ^ slowArity r))), D.card ≤ 4 →
        (JuntaRadius.controlFor r (slowArity r) (patch D (wideMixed h f g ∘ tablePerm e)) = true ↔ f = g) := by
  have hs : 2 ^ r ≤ slowSuffix r := le_max_left _ _
  have hm : 2 ^ r ≤ slowArity r := hs.trans (by unfold slowArity; omega)
  obtain ⟨h, hh⟩ := exists_growing_selector r (slowSuffix r) hr hs
  exact ⟨h, hh, controlFor_sparse hr hm, slow_bound r, controlFor_passes_wide_cuts hr hs hh⟩

end SlowGrowth

#print axioms exists_ten_selector_43
#print axioms patched_andTen_accepted
#print axioms patched_andTen_breaks_nine_32
#print axioms ten_prefix_breaks_nine_43
#print axioms log_width_stage
#print axioms growing_sparse_control_below_nlogn

end PvsNP.Frontier.GrowingPrefix
