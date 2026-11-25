module

public import MCSPAdaptivePinning
public import MCSPPinning
public import MCSPOrbitCharge

/-! Pin the leading-00 quarter to zero and keep only the three live quarters
as inputs. The affine forest argument works over those retained addresses. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterBlock

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open SuperTwoN NestedFaces RestrictionCharges FreshCharges AdaptivePinning
open CornerCertificates TwoCornerStructure MonotoneForest

def keptAddress {m : ℕ} (z : BitString (m + 2)) : Bool := z 0 || (Fin.tail z) 0

def keptKey (m : ℕ) (i : Fin (2 ^ (m + 2))) : Bool :=
  keptAddress ((BitString.equivFin (m + 2)).symm i)

private abbrev keptHead := {b : Bool × Bool // (b.1 || b.2) = true}

private theorem keptHead_card : Fintype.card keptHead = 3 := by decide

private def keyEquiv (m : ℕ) :
    { i : Fin (2 ^ (m + 2)) // keptKey m i = true } ≃ keptHead × BitString m where
  toFun i :=
    let z := (BitString.equivFin (m + 2)).symm i.val
    (⟨(z 0, (Fin.tail z) 0), i.property⟩, Fin.tail (Fin.tail z))
  invFun u := ⟨BitString.equivFin (m + 2)
      (Fin.cons u.1.val.1 (Fin.cons u.1.val.2 u.2)), by
    simp only [keptKey, Equiv.symm_apply_apply, keptAddress, Fin.cons_zero, Fin.tail_cons]
    exact u.1.property⟩
  left_inv i := by
    apply Subtype.ext
    simp
  right_inv := by
    rintro ⟨⟨⟨a, b⟩, h⟩, t⟩
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp

theorem keptKeys_card (m : ℕ) :
    Fintype.card { i : Fin (2 ^ (m + 2)) // keptKey m i = true } = 3 * 2 ^ m := by
  rw [Fintype.card_congr (keyEquiv m), Fintype.card_prod, keptHead_card, BitString.card]

noncomputable def freeEquiv (m : ℕ) :
    Fin (3 * 2 ^ m) ≃ { i : Fin (2 ^ (m + 2)) // keptKey m i = true } :=
  (Fintype.equivFinOfCardEq (keptKeys_card m)).symm

noncomputable def labels (m : ℕ) : Fin (3 * 2 ^ m) ↪ BitString (m + 2) :=
  ⟨fun i => (BitString.equivFin (m + 2)).symm (freeEquiv m i).val,
    fun _ _ h => (freeEquiv m).injective (Subtype.ext ((BitString.equivFin _).symm.injective h))⟩

noncomputable def quarterSub (m : ℕ) (i : Fin (2 ^ (m + 2))) : Fin (3 * 2 ^ m) ⊕ Bool :=
  if hi : keptKey m i = true then .inl ((freeEquiv m).symm ⟨i, hi⟩) else .inr false

noncomputable def fill (m : ℕ) (U : BitString (3 * 2 ^ m)) : BitString (2 ^ (m + 2)) :=
  substitute (quarterSub m) U

noncomputable def residual (m : ℕ) (f : BooleanFunction (2 ^ (m + 2))) :
    BooleanFunction (3 * 2 ^ m) := f ∘ fill m

@[simp] theorem fill_at_retained (m : ℕ) (U : BitString (3 * 2 ^ m)) (j : Fin (3 * 2 ^ m)) :
    fill m U (freeEquiv m j).val = U j := by
  have h := (freeEquiv m j).property
  simp [fill, quarterSub, substitute, h]

theorem fill_constant (m : ℕ) (b : Bool) (i : Fin (2 ^ (m + 2))) :
    fill m (fun _ => b) i = (keptKey m i && b) := by
  cases hk : keptKey m i <;> simp [fill, quarterSub, substitute, hk]

theorem fill_zero (m : ℕ) : fill m (fun _ => false) = fun _ => false := by
  funext i
  rw [fill_constant m false i]
  cases keptKey m i <;> rfl

theorem fill_injective (m : ℕ) : Function.Injective (fill m) := by
  intro U V h
  funext j
  simpa using congrFun h (freeEquiv m j).val

theorem residual_sparse (m : ℕ) {f : BooleanFunction (2 ^ (m + 2))} {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) :
    (acceptingTables (residual m f)).card ≤ 2 ^ B := by
  classical
  have hCard : (acceptingTables (residual m f)).card ≤ (acceptingTables f).card := by
    apply Finset.card_le_card_of_injOn (fill m)
    · intro T hT
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2⟩
    · exact (fill_injective m).injOn
  exact hCard.trans hSparse

private theorem affine_fill (m : ℕ) (a : BitString (m + 2)) (b : Bool) :
    (MCSP.truthTable (m + 2)).symm (fill m (fun i => affine a b (labels m i))) =
      fun z => keptAddress z && affine a b z := by
  funext z
  let i := BitString.equivFin (m + 2) z
  have hi : keptKey m i = keptAddress z := by simp [i, keptKey]
  change fill m (fun j => affine a b (labels m j)) i = _
  by_cases h : keptKey m i = true
  · have he : labels m ((freeEquiv m).symm ⟨i, h⟩) = z := by
      change (BitString.equivFin (m + 2)).symm
        (freeEquiv m ((freeEquiv m).symm ⟨i, h⟩)).val = z
      simp [i]
    simp [fill, substitute, quarterSub, h, ← hi, he]
  · have h' := Bool.eq_false_of_not_eq_true h
    simp [fill, substitute, quarterSub, h', ← hi]

theorem residual_affine (m : ℕ) (hm : 5 ≤ m + 2) (a : BitString (m + 2)) (b : Bool) :
    residual m (mcspSquare (m + 2)) (fun i => affine a b (labels m i)) = true := by
  let p : BooleanFunction (m + 2) := fun z => z 0
  let q : BooleanFunction (m + 2) := fun z => z (0 : Fin (m + 1)).succ
  have hp : complexity interpretation (single p) = 0 := complexity_single_proj _
  have hq : complexity interpretation (single q) = 0 := complexity_single_proj _
  have hg : complexity interpretation (single (keptAddress (m := m))) ≤ 1 := by
    have h := complexity_or_le p q
    rw [hp, hq] at h
    exact h
  change mcspSquare (m + 2) (fill m (fun i => affine a b (labels m i))) = true
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, affine_fill]
  have h := complexity_and_le (keptAddress (m := m)) (affine a b)
  have ha := complexity_affine_le a b
  have hCut : 4 * (m + 2) + 3 ≤ (m + 2) ^ 2 := by nlinarith
  exact h.trans (by omega)

theorem reindexed_forest_size {n m B : ℕ} {f : BooleanFunction n} (e : Fin n ↪ BitString m)
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hAff : ∀ a b, f (fun i => affine a b (e i)) = true) :
    18694 * (2 * n) + 10 * n ≤
      18694 * (complexity interpretation (single f) + 2 * B + 1) + 142 * B := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single f)
  have hCorner (b : Bool) : f (fun _ => b) = true := by
    have hev : ∀ z : BitString m, affine (fun _ => false) b z = b := by
      intro z
      have h := congrFun (affine_constant m b) (BitString.equivFin m z)
      simpa only [MCSP.truthTable_apply, Equiv.symm_apply_apply] using h
    simpa only [hev] using hAff (fun _ => false) b
  have h0 : cornerValue c.program false (c.outputs 0) = true :=
    (congrFun (hc _) 0).trans (hCorner false)
  have h1 : cornerValue c.program true (c.outputs 0) = true :=
    (congrFun (hc _) 0).trans (hCorner true)
  have hN0 := card_needInputs_ge_of_sparse c hc hSparse false (hCorner false)
  have hN1 := card_needInputs_ge_of_sparse c hc hSparse true (hCorner true)
  have hAcct := needInputs_add_slack_eq c.program (c.outputs 0) h0 h1
  have hCore := sparse_reindexed_affine_stop_budget e c hc hSparse (hCorner false) (hCorner true) hAff
  have hStop := card_stopGate_le_56_slack c.program (c.outputs 0) h0 h1
  omega

theorem mcsp_quarter_residual_32 :
    6444118523 ≤ complexity interpretation (single (residual 30 (mcspSquare 32))) := by
  have h := reindexed_forest_size (labels 30) (residual_sparse 30 (card_accepting_mcspSquare_le 32))
    (fun a b => residual_affine 30 (by decide) a b)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 18694 * (2 * 3221225472) + 10 * 3221225472 ≤
    18694 * (complexity interpretation (single (residual 30 (mcspSquare 32))) + 2 * 27672 + 1) +
    142 * 27672 at h
  omega

noncomputable def zeroBlock (m : ℕ) : Finset (Fin (2 ^ (m + 2))) :=
  Finset.univ.filter fun i => keptKey m i = false

theorem zeroBlock_card (m : ℕ) : (zeroBlock m).card = 2 ^ m := by
  classical
  let S := (Finset.univ : Finset (Fin (2 ^ (m + 2)))).filter (fun i => keptKey m i = true)
  have hCard : S.card = 3 * 2 ^ m := by
    let e : S ≃ { i : Fin (2 ^ (m + 2)) // keptKey m i = true } :=
      { toFun := fun j => ⟨j.val, (Finset.mem_filter.mp j.property).2⟩
        invFun := fun j => ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    simpa only [Fintype.card_coe, keptKeys_card] using Fintype.card_congr e
  have hSplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 ^ (m + 2))))) (p := fun i => keptKey m i = true)
  have hComplement : Finset.univ.filter (fun i => ¬ keptKey m i = true) = zeroBlock m := by
    ext i
    cases h : keptKey m i <;> simp [zeroBlock, h]
  rw [hComplement, Finset.card_univ, Fintype.card_fin] at hSplit
  have hPow : (2 : ℕ) ^ (m + 2) = 2 ^ m * 4 := pow_add 2 m 2
  change S.card + (zeroBlock m).card = 2 ^ (m + 2) at hSplit
  omega

/-- Partition the original gate indices into aliases or constants, fresh
but dead gates, and gates needed for the quarter residual. -/
theorem quarter_live_budget (m : ℕ)
    {f : BooleanFunction (2 ^ (m + 2))} (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single f)) {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (hFew : B < 3 * 2 ^ m)
    (hZero : residual m f (fun _ => false) = true) :
    complexity interpretation (single (residual m f)) +
      (firstFreshLoss c.program (quarterSub m)).card +
      (deadFresh c.program (quarterSub m) (c.outputs 0)).card ≤ c.size := by
  have hEq : restrictedWire c.program (quarterSub m) (c.outputs 0) = residual m f :=
    restricted_circuit_eq c hc (quarterSub m)
  have hNon : ¬ ∃ b : Bool, residual m f = fun _ => b := by
    rintro ⟨b, hb⟩
    have hbt : b = true := (congrFun hb _).symm.trans hZero
    have hCap := card_masked_le (residual_sparse m hSparse) (fun _ => false) ∅
      (fun y _ => by rw [hb, hbt])
    exact (not_le_of_gt hFew) (by simpa using hCap)
  have hSize := first_dead_and_residual_budget c.program (quarterSub m) (c.outputs 0)
    (by rwa [hEq])
  rwa [hEq] at hSize

theorem quarter_loss_budget (m : ℕ)
    {f : BooleanFunction (2 ^ (m + 2))} (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single f)) {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (hFew : B < 3 * 2 ^ m)
    (hZero : residual m f (fun _ => false) = true) :
    complexity interpretation (single (residual m f)) +
      (firstFreshLoss c.program (quarterSub m)).card ≤ c.size := by
  have h := quarter_live_budget m c hc hSparse hFew hZero
  omega

theorem quarter_fresh_losses (m : ℕ)
    {f : BooleanFunction (2 ^ (m + 2))} (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single f)) {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (hZero : f (fun _ => false) = true) :
    2 ^ m ≤ (nextFreshLoss c.program
      (Sum.inl : Fin (2 ^ (m + 2)) → Fin (2 ^ (m + 2)) ⊕ Bool) (quarterSub m)).card + B := by
  let ρ : Fin (2 ^ (m + 2)) → Fin (2 ^ (m + 2)) ⊕ Bool := Sum.inl
  have hEq : restrictedWire c.program ρ (c.outputs 0) = f :=
    restricted_circuit_eq c hc ρ
  have hPin : ∀ i ∈ zeroBlock m, quarterSub m i = .inr false := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp [quarterSub, hi']
  have h := adaptive_pinned_charge c.program ρ (quarterSub m) (c.outputs 0) hEq
    hSparse hZero (zeroBlock m) hPin
  rwa [zeroBlock_card] at h

theorem mcsp_quarter_fresh_losses_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    1073714152 ≤ (nextFreshLoss c.program
      (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool) (quarterSub 30)).card := by
  have h := quarter_fresh_losses 30 c hc (card_accepting_mcspSquare_le 32)
    (mcspSquare_constant_table 32 (by decide) false)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 1073741824 ≤ _ at h
  omega

theorem mcsp_quarter_certified_losses_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    1073714152 ≤ (firstFreshLoss c.program (quarterSub 30)).card := by
  have hSub : nextFreshLoss c.program (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool)
      (quarterSub 30) ⊆ firstFreshLoss c.program (quarterSub 30) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  exact (mcsp_quarter_fresh_losses_32 c hc).trans (Finset.card_le_card hSub)

private theorem mcsp_quarter_zero_corner_32 :
    residual 30 (mcspSquare 32) (fun _ => false) = true := by
  change mcspSquare 32 (fill 30 (fun _ => false)) = true
  rw [fill_zero]
  exact mcspSquare_constant_table 32 (by decide) false

/-- The resulting lower bound, with each omitted original gate added once. -/
theorem mcsp_quarter_total_32 :
    7517832675 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  have h0 := mcsp_quarter_zero_corner_32
  have hBudget := quarter_loss_budget 30 c hc (card_accepting_mcspSquare_le 32) (by decide) h0
  have hResid := mcsp_quarter_residual_32
  have hLoss := mcsp_quarter_certified_losses_32 c hc
  omega

/-- These many omitted original gates would suffice to improve the current
full-size bound using the certified quarter residual bound. -/
theorem mcsp_quarter_live_beat_threshold_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hLoss : 2148058051 ≤ (firstFreshLoss c.program (quarterSub 30)).card +
      (deadFresh c.program (quarterSub 30) (c.outputs 0)).card) :
    8592176574 ≤ c.size := by
  have h0 := mcsp_quarter_zero_corner_32
  have hBudget := quarter_live_budget 30 c hc (card_accepting_mcspSquare_le 32) (by decide) h0
  have hR := mcsp_quarter_residual_32
  omega

theorem mcsp_quarter_beat_threshold_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hLoss : 2148058051 ≤ (firstFreshLoss c.program (quarterSub 30)).card) :
    8592176574 ≤ c.size :=
  mcsp_quarter_live_beat_threshold_32 c hc (hLoss.trans (Nat.le_add_right _ _))

section Controls

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

private theorem kept_point_32 (a : BitString 9) (z : BitString 23) :
    keptKey 30 (InvariantControl.point (s := 22) a z) = (a 0 || a 1) := by
  change keptKey 30 (BitString.equivFin 32 (Fin.append a z)) = _
  unfold keptKey
  rw [Equiv.symm_apply_apply]
  change (Fin.append a z (Fin.castAdd 23 (0 : Fin 9)) ||
    Fin.append a z (Fin.castAdd 23 (1 : Fin 9))) = _
  rw [Fin.append_left, Fin.append_left]

private theorem kept_position_32 (a : BitString 9) (b : Bool) (z : BitString 22) :
    keptKey 30 (CommunicationCut.position (r := 9) (s := 22) a b z) = (a 0 || a 1) := by
  rw [← InvariantControl.point_cons (r := 9) (s := 22)]
  exact kept_point_32 a (Fin.cons b z)

private theorem split_residual_corners (b : Bool) :
    residual 30 (SplitControl.railControl 9 SplitControl.keep) (fun _ => b) = true := by
  classical
  unfold residual
  rw [Function.comp_apply, SplitControl.railControl, decide_eq_true_eq]
  rintro ⟨a, d⟩
  apply (SampleControls.agreesOn_eq_true _ _).mpr
  intro i hi j hj
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
  rw [fill_constant 30 b, fill_constant 30 b, kept_position_32, kept_position_32]

private theorem invariant_residual_corners (b : Bool) :
    residual 30 (InvariantControl.control 9 22) (fun _ => b) = true := by
  unfold residual
  rw [Function.comp_apply]
  apply (InvariantControl.control_iff (r := 9) (s := 22) _).mpr
  intro a u v _ _ _
  rw [fill_constant 30 b, fill_constant 30 b, kept_point_32, kept_point_32]

private theorem split_sparse_count : (acceptingTables (SplitControl.railControl 9 SplitControl.keep)).card ≤ 2 ^ 5120 := by
  classical
  obtain ⟨u, hu, _⟩ := SplitControl.has_other_retained (fun _ => false)
  have h := SplitControl.railControl_accepting_count_le 9 SplitControl.keep ⟨u, hu⟩
  have hComp : SplitControl.keepᶜ.card = 4 := by
    rw [Finset.card_compl, BitString.card, SplitControl.card_keep]
    decide
  rw [hComp, show (2 ^ 9 * 2 + (2 ^ 9 * 2) * 4 : ℕ) = 5120 by decide] at h
  exact h

/-- A minimum split control cannot lose enough distinct gates to beat
the current MCSP bound by the certified quarter residual estimate. -/
theorem split_quarter_live_loss_upper_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (hMin : c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep))) :
    (firstFreshLoss c.program (quarterSub 30)).card +
      (deadFresh c.program (quarterSub 30) (c.outputs 0)).card ≤ 2147490818 := by
  have hSparse := split_sparse_count
  have hLower := Pinning.complexity_lower_of_sparse_opposite
    (residual 30 (SplitControl.railControl 9 SplitControl.keep)) (fun _ => false)
    (split_residual_corners false) (split_residual_corners true) 5120 (residual_sparse 30 (B := 5120) hSparse)
  have hBudget := quarter_live_budget 30 c hc (B := 5120) hSparse (by decide) (split_residual_corners false)
  obtain ⟨c₀, _, hMin₀, hSize₀, _, _⟩ := SplitControl.minimum_wide_railControl_32
  have hSizes : c.size = c₀.size := hMin.trans hMin₀.symm
  have hSize := (Nat.add_le_add_right hSizes.le 3071).trans hSize₀
  change 6442450944 ≤ _ at hLower
  change c.size + 3071 ≤ 8589934592 at hSize
  omega

theorem split_quarter_loss_upper_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (hMin : c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep))) :
    (firstFreshLoss c.program (quarterSub 30)).card ≤ 2147490818 := by
  have h := split_quarter_live_loss_upper_32 c hc hMin
  omega

private theorem invariant_sparse_count :
    (acceptingTables (InvariantControl.control 9 22)).card ≤ 2 ^ 12800 := by
  have hSparse := OrbitCharge.control32_sparse
  rw [show (2 ^ 9 * 2 + 2 ^ 9 * (22 + 1) : ℕ) = 12800 by decide] at hSparse
  exact hSparse

/-- The same obstruction holds in a minimum permutation-invariant control. -/
theorem invariant_quarter_live_loss_upper_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (InvariantControl.control 9 22)))
    (hMin : c.size = complexity interpretation (single (InvariantControl.control 9 22))) :
    (firstFreshLoss c.program (quarterSub 30)).card +
      (deadFresh c.program (quarterSub 30) (c.outputs 0)).card ≤ 2147490818 := by
  have hSparse := invariant_sparse_count
  have hLower := Pinning.complexity_lower_of_sparse_opposite
    (residual 30 (InvariantControl.control 9 22)) (fun _ => false)
    (invariant_residual_corners false) (invariant_residual_corners true) 12800 (residual_sparse 30 (B := 12800) hSparse)
  have hBudget := quarter_live_budget 30 c hc (B := 12800) hSparse (by decide) (invariant_residual_corners false)
  have hSize := (Nat.add_le_add_right hMin.le 18431).trans OrbitCharge.control32_size
  change c.size + 18431 ≤ 8589934592 at hSize
  change 6442450944 ≤ _ at hLower
  omega

theorem invariant_quarter_loss_upper_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (InvariantControl.control 9 22)))
    (hMin : c.size = complexity interpretation (single (InvariantControl.control 9 22))) :
    (firstFreshLoss c.program (quarterSub 30)).card ≤ 2147490818 := by
  have h := invariant_quarter_live_loss_upper_32 c hc hMin
  omega

private theorem dead_cap_of_total (m : ℕ) {f : BooleanFunction (2 ^ (m + 2))}
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single f)) {B total : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hZero : residual m f (fun _ => false) = true)
    (hTotal : (firstFreshLoss c.program (quarterSub m)).card +
      (deadFresh c.program (quarterSub m) (c.outputs 0)).card ≤ total) :
    (deadFresh c.program (quarterSub m) (c.outputs 0)).card + 2 ^ m ≤ total + B := by
  have h0 : f (fun _ => false) = true := by
    change f (fill m (fun _ => false)) = true at hZero
    rwa [fill_zero] at hZero
  have h := quarter_fresh_losses m c hc hSparse h0
  have hSub : nextFreshLoss c.program (Sum.inl : Fin (2 ^ (m + 2)) → Fin (2 ^ (m + 2)) ⊕ Bool)
      (quarterSub m) ⊆ firstFreshLoss c.program (quarterSub m) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hLoss := Finset.card_le_card hSub
  omega

theorem split_quarter_dead_upper_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (hMin : c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep))) :
    (deadFresh c.program (quarterSub 30) (c.outputs 0)).card ≤ 1073754114 := by
  have h := dead_cap_of_total 30 c hc (B := 5120) split_sparse_count (split_residual_corners false)
    (split_quarter_live_loss_upper_32 c hc hMin)
  change (deadFresh c.program (quarterSub 30) (c.outputs 0)).card + 1073741824 ≤ 2147490818 + 5120 at h
  omega

theorem invariant_quarter_dead_upper_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (InvariantControl.control 9 22)))
    (hMin : c.size = complexity interpretation (single (InvariantControl.control 9 22))) :
    (deadFresh c.program (quarterSub 30) (c.outputs 0)).card ≤ 1073761794 := by
  have h := dead_cap_of_total 30 c hc (B := 12800) invariant_sparse_count
    (invariant_residual_corners false) (invariant_quarter_live_loss_upper_32 c hc hMin)
  change (deadFresh c.program (quarterSub 30) (c.outputs 0)).card + 1073741824 ≤ 2147490818 + 12800 at h
  omega

end Controls

#print axioms reindexed_forest_size
#print axioms mcsp_quarter_residual_32
#print axioms mcsp_quarter_fresh_losses_32
#print axioms quarter_live_budget
#print axioms mcsp_quarter_total_32
#print axioms mcsp_quarter_live_beat_threshold_32
#print axioms split_quarter_live_loss_upper_32
#print axioms invariant_quarter_live_loss_upper_32
#print axioms split_quarter_dead_upper_32
#print axioms invariant_quarter_dead_upper_32

end PvsNP.Frontier.QuarterBlock
