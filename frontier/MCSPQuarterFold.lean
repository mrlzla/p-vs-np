module

public import MCSPQuarterBlock
public import MCSPQuarterProbes

/-! Identify the leading-00 quarter with the leading-01 quarter. The free
entries still support the affine forest bound after this identification. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterFold

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open SuperTwoN NestedFaces RestrictionCharges FreshCharges TwoCornerStructure
open QuarterBlock (keptAddress keptKey freeEquiv labels reindexed_forest_size)

variable {n k : ℕ}

theorem pullback_sparse (fill : BitString k → BitString n) (hInj : Function.Injective fill)
    {f : BooleanFunction n} {B : ℕ} (hSparse : (acceptingTables f).card ≤ 2 ^ B) :
    (acceptingTables (f ∘ fill)).card ≤ 2 ^ B := by
  classical
  apply le_trans _ hSparse
  apply Finset.card_le_card_of_injOn fill
  · intro U hU
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hU).2⟩
  · exact hInj.injOn

private theorem relabel_sparse (parent : Fin n → Fin k) (hSurj : Function.Surjective parent)
    {f : BooleanFunction n} {B : ℕ} (hSparse : (acceptingTables f).card ≤ 2 ^ B) :
    (acceptingTables (fun U : BitString k => f (U ∘ parent))).card ≤ 2 ^ B := by
  apply pullback_sparse (fun U => U ∘ parent) _ hSparse
  intro U V h
  funext j
  obtain ⟨i, rfl⟩ := hSurj j
  exact congrFun h i

def foldAddress {m : ℕ} (z : BitString (m + 2)) : BitString (m + 2) :=
  Fin.cons (z 0) (Fin.cons ((Fin.tail z) 0 || !(z 0)) (Fin.tail (Fin.tail z)))

theorem foldAddress_kept {m : ℕ} (z : BitString (m + 2)) :
    keptAddress (foldAddress z) = true := by
  simp only [keptAddress, foldAddress, Fin.cons_zero, Fin.tail_cons]
  cases z 0 <;> simp

theorem foldAddress_eq_of_kept {m : ℕ} (z : BitString (m + 2))
    (hz : keptAddress z = true) : foldAddress z = z := by
  have hSecond : ((Fin.tail z) 0 || !(z 0)) = (Fin.tail z) 0 := by
    revert hz
    unfold keptAddress
    cases z 0 <;> cases (Fin.tail z) 0 <;> decide
  simp [foldAddress, hSecond]

private def foldCircuit (m : ℕ) : Circuit signature (m + 2) (m + 2) :=
  let p0 : Program signature (m + 2) 0 := .empty
  let p1 := p0.gate ⟨.not, fun _ => .input 0⟩
  let p2 := p1.gate ⟨.or, fun j => if j = 0 then .input (0 : Fin (m + 1)).succ else .gate 0⟩
  ⟨p2, Fin.cons (.input 0) (Fin.cons (.gate 1) (fun i => .input i.succ.succ))⟩

private theorem foldCircuit_eval (m : ℕ) (z : BitString (m + 2)) :
    (foldCircuit m).eval interpretation z = foldAddress z := by
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => ?_)) i <;> rfl

private theorem complexity_affine_comp_le {m : ℕ}
    (d : Circuit signature (m + 2) (m + 2)) (a : BitString (m + 2)) (b : Bool) :
    complexity interpretation (single (affine a b ∘ d.eval interpretation)) ≤ 4 * (m + 2) + 1 + d.size := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (affine a b))
  have hd : (c.comp d).Computes interpretation (single (affine a b ∘ d.eval interpretation)) := by
    intro z
    rw [Circuit.eval_comp]
    exact hc (d.eval interpretation z)
  exact (complexity_le_of_computes (c.comp d) hd).trans (by
    rw [Circuit.size_comp, hsize]
    have h := complexity_affine_le a b
    omega)

noncomputable def foldKey (m : ℕ) (i : Fin (2 ^ (m + 2))) : Fin (3 * 2 ^ m) :=
  let z := foldAddress ((BitString.equivFin (m + 2)).symm i)
  (freeEquiv m).symm ⟨BitString.equivFin (m + 2) z, by
    simpa only [keptKey, Equiv.symm_apply_apply] using foldAddress_kept _⟩

noncomputable def foldSub (m : ℕ) (i : Fin (2 ^ (m + 2))) : Fin (3 * 2 ^ m) ⊕ Bool :=
  .inl (foldKey m i)

noncomputable def residual (m : ℕ) (f : BooleanFunction (2 ^ (m + 2))) :
    BooleanFunction (3 * 2 ^ m) := f ∘ substitute (foldSub m)

@[simp] theorem foldKey_at_retained (m : ℕ) (j : Fin (3 * 2 ^ m)) :
    foldKey m (freeEquiv m j).val = j := by
  unfold foldKey
  apply (freeEquiv m).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  have h := foldAddress_eq_of_kept _ (freeEquiv m j).property
  simp only [h, Equiv.apply_symm_apply]

theorem residual_sparse (m : ℕ) {f : BooleanFunction (2 ^ (m + 2))} {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) :
    (acceptingTables (residual m f)).card ≤ 2 ^ B :=
  relabel_sparse (foldKey m) (fun j => ⟨_, foldKey_at_retained m j⟩) hSparse

private theorem foldCircuit_labels (m : ℕ) (z : BitString (m + 2)) :
    (foldCircuit m).eval interpretation z = labels m (foldKey m (BitString.equivFin (m + 2) z)) := by
  rw [foldCircuit_eval]
  symm
  change (BitString.equivFin (m + 2)).symm (freeEquiv m ((freeEquiv m).symm _)).val = _
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- Gate budget for each affine witness after the unsigned address fold. -/
theorem complexity_fold_affine_le_32 (a : BitString 32) (b : Bool) :
    complexity interpretation (single ((MCSP.truthTable 32).symm
      (fun i => affine a b (labels 30 (foldKey 30 i))))) ≤ 131 := by
  have he : (MCSP.truthTable 32).symm (fun i => affine a b (labels 30 (foldKey 30 i))) =
      affine a b ∘ (foldCircuit 30).eval interpretation := by
    funext z
    change affine a b (labels 30 (foldKey 30 (BitString.equivFin 32 z))) =
      affine a b ((foldCircuit 30).eval interpretation z)
    rw [foldCircuit_labels]
  rw [he]
  exact complexity_affine_comp_le (foldCircuit 30) a b

/-- The fold preserves every table supported on the half with first bit one. -/
theorem fold_preserves_supported_table (m : ℕ) (T : BitString (2 ^ (m + 2)))
    (hZero : ∀ z : BitString (m + 2), z 0 = false → T (BitString.equivFin (m + 2) z) = false) :
    (fun j => T (freeEquiv m j).val) ∘ foldKey m = T := by
  funext i
  obtain ⟨z, rfl⟩ := (BitString.equivFin (m + 2)).surjective i
  have h := foldCircuit_labels m z
  rw [foldCircuit_eval] at h
  have hKey := congrArg (BitString.equivFin (m + 2)) h
  change BitString.equivFin (m + 2) (foldAddress z) =
    BitString.equivFin (m + 2) ((BitString.equivFin (m + 2)).symm
      (freeEquiv m (foldKey m (BitString.equivFin (m + 2) z))).val) at hKey
  rw [Equiv.apply_symm_apply] at hKey
  change T (freeEquiv m (foldKey m (BitString.equivFin (m + 2) z))).val = _
  rw [← hKey]
  cases hz : z 0
  · rw [hZero z hz, hZero (foldAddress z) (by simpa only [foldAddress, Fin.cons_zero] using hz)]
  · rw [foldAddress_eq_of_kept z (by simp only [keptAddress, hz, Bool.true_or])]

theorem fold_preserves_rich_probe (payload : Fin 29 → BitString 26) :
    (fun j => QuarterProbes.probe payload (freeEquiv 30 j).val) ∘ foldKey 30 =
      QuarterProbes.probe payload := by
  apply fold_preserves_supported_table
  intro z hz
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (of_decide_eq_true ht)
  have hEq := (BitString.equivFin 32).injective hj
  have hFirst := congrFun hEq (Fin.castAdd 26 (0 : Fin 6))
  rw [Fin.append_left] at hFirst
  change true = z 0 at hFirst
  rw [hz] at hFirst
  cases hFirst

private theorem residual_affine_of_address_circuit (m : ℕ)
    (parent : Fin (2 ^ (m + 2)) → Fin (3 * 2 ^ m))
    (d : Circuit signature (m + 2) (m + 2))
    (hAddr : ∀ z, d.eval interpretation z = labels m (parent (BitString.equivFin (m + 2) z)))
    (hCost : 4 * (m + 2) + 1 + d.size ≤ (m + 2) ^ 2) (a : BitString (m + 2)) (b : Bool) :
    mcspSquare (m + 2) (fun i => affine a b (labels m (parent i))) = true := by
  have hPullback : (MCSP.truthTable (m + 2)).symm (fun i => affine a b (labels m (parent i))) =
      affine a b ∘ d.eval interpretation := by
    funext z
    change affine a b (labels m (parent (BitString.equivFin (m + 2) z))) =
      affine a b (d.eval interpretation z)
    rw [hAddr]
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hPullback]
  exact (complexity_affine_comp_le d a b).trans hCost

theorem residual_affine (m : ℕ) (hm : 5 ≤ m + 2) (a : BitString (m + 2)) (b : Bool) :
    residual m (mcspSquare (m + 2)) (fun j => affine a b (labels m j)) = true := by
  apply residual_affine_of_address_circuit m (foldKey m) (foldCircuit m) (foldCircuit_labels m) _ a b
  change 4 * (m + 2) + 1 + 2 ≤ (m + 2) ^ 2
  nlinarith

/-- Every surjective identification with an address circuit in the witness
budget gives the same three-quarter lower bound. -/
theorem mcsp_address_circuit_residual_32 (parent : Fin (2 ^ 32) → Fin (3 * 2 ^ 30))
    (hSurj : Function.Surjective parent) (d : Circuit signature 32 32)
    (hAddr : ∀ z, d.eval interpretation z = labels 30 (parent (BitString.equivFin 32 z)))
    (hCost : d.size ≤ 895) :
    6444118523 ≤ complexity interpretation (single (fun U => mcspSquare 32 (U ∘ parent))) := by
  have hSparse := relabel_sparse parent hSurj (card_accepting_mcspSquare_le 32)
  have h := reindexed_forest_size (labels 30) hSparse
    (fun a b => residual_affine_of_address_circuit 30 parent d hAddr (by omega) a b)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 18694 * (2 * 3221225472) + 10 * 3221225472 ≤
    18694 * (complexity interpretation (single (fun U => mcspSquare 32 (U ∘ parent))) + 2 * 27672 + 1) +
    142 * 27672 at h
  omega

theorem mcsp_fold_residual_32 :
    6444118523 ≤ complexity interpretation (single (residual 30 (mcspSquare 32))) :=
  mcsp_address_circuit_residual_32 (foldKey 30) (fun j => ⟨_, foldKey_at_retained 30 j⟩)
    (foldCircuit 30) (foldCircuit_labels 30) (by decide)

theorem mcsp_fold_live_budget_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    6444118523 + (firstFreshLoss c.program (foldSub 30)).card +
      (deadFresh c.program (foldSub 30) (c.outputs 0)).card ≤ c.size := by
  have hEq : restrictedWire c.program (foldSub 30) (c.outputs 0) =
      residual 30 (mcspSquare 32) := restricted_circuit_eq c hc (foldSub 30)
  have hNon : ¬ ∃ b : Bool, restrictedWire c.program (foldSub 30) (c.outputs 0) = fun _ => b := by
    rintro ⟨b, hb⟩
    rw [hEq] at hb
    have hSize : complexity interpretation (single (residual 30 (mcspSquare 32))) ≤ 1 := by
      rw [hb]
      exact (Synthesis.const (s := inputs (3 * 2 ^ 30)) b).complexity_le
    have hLower := mcsp_fold_residual_32
    omega
  have hBudget := first_dead_and_residual_budget c.program (foldSub 30) (c.outputs 0) hNon
  rw [hEq] at hBudget
  have hLower := mcsp_fold_residual_32
  omega

/-- Any identification of inputs onto `k` free variables preserves both constant
corners. For a sparse control this bounds the total distinct gates it can lose. -/
theorem relabel_live_loss_cap (parent : Fin n → Fin k) (hSurj : Function.Surjective parent)
    {f : BooleanFunction n} (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    {B upper : ℕ} (hSparse : (acceptingTables f).card ≤ 2 ^ B) (hFew : B < k)
    (hCorner : ∀ b : Bool, f (fun _ => b) = true) (hSize : c.size ≤ upper) :
    (firstFreshLoss c.program (Sum.inl ∘ parent)).card +
      (deadFresh c.program (Sum.inl ∘ parent) (c.outputs 0)).card + 2 * k ≤ upper + 1 + 2 * B := by
  let f' : BooleanFunction k := fun U => f (U ∘ parent)
  have hSparse' : (acceptingTables f').card ≤ 2 ^ B := relabel_sparse parent hSurj hSparse
  have hLower := Pinning.complexity_lower_of_sparse_opposite f' (fun _ => false)
    (hCorner false) (hCorner true) B hSparse'
  have hEq : restrictedWire c.program (Sum.inl ∘ parent) (c.outputs 0) = f' :=
    restricted_circuit_eq c hc (Sum.inl ∘ parent)
  have hNon : ¬ ∃ b : Bool, f' = fun _ => b := by
    rintro ⟨b, hb⟩
    have ht : b = true := (congrFun hb (fun _ => false)).symm.trans (hCorner false)
    have hCap := card_masked_le hSparse' (fun _ => false) ∅ (fun y _ => by rw [hb, ht])
    exact (not_le_of_gt hFew) (by simpa using hCap)
  have hBudget := first_dead_and_residual_budget c.program (Sum.inl ∘ parent) (c.outputs 0)
    (by rwa [hEq])
  rw [hEq] at hBudget
  omega

theorem split_relabel_live_loss_cap_32 (parent : Fin (2 ^ 32) → Fin (3 * 2 ^ 30))
    (hSurj : Function.Surjective parent) (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (hMin : c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep))) :
    (firstFreshLoss c.program (Sum.inl ∘ parent)).card +
      (deadFresh c.program (Sum.inl ∘ parent) (c.outputs 0)).card ≤ 2147490818 := by
  classical
  obtain ⟨u, hu, _⟩ := SplitControl.has_other_retained (fun _ => false)
  have hSparse := SplitControl.railControl_accepting_count_le 9 SplitControl.keep ⟨u, hu⟩
  have hComp : SplitControl.keepᶜ.card = 4 := by
    rw [Finset.card_compl, BitString.card, SplitControl.card_keep]
    decide
  rw [hComp, show (2 ^ 9 * 2 + (2 ^ 9 * 2) * 4 : ℕ) = 5120 by decide] at hSparse
  have hCorner (b : Bool) : SplitControl.railControl 9 SplitControl.keep (fun _ => b) = true := by
    rw [SplitControl.railControl, decide_eq_true_eq]
    intro key
    exact (SampleControls.agreesOn_eq_true _ _).mpr (fun _ _ _ _ => rfl)
  have hSize := hMin.le.trans (SplitControl.railControl_size_bound 9 SplitControl.keep)
  rw [SplitControl.card_keep] at hSize
  change c.size ≤ 8589931521 at hSize
  have h := relabel_live_loss_cap parent hSurj c hc hSparse (by decide) hCorner hSize
  change _ + _ + 6442450944 ≤ 8589931521 + 1 + 2 * 5120 at h
  omega

theorem invariant_relabel_live_loss_cap_32 (parent : Fin (2 ^ 32) → Fin (3 * 2 ^ 30))
    (hSurj : Function.Surjective parent) (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (InvariantControl.control 9 22)))
    (hMin : c.size = complexity interpretation (single (InvariantControl.control 9 22))) :
    (firstFreshLoss c.program (Sum.inl ∘ parent)).card +
      (deadFresh c.program (Sum.inl ∘ parent) (c.outputs 0)).card ≤ 2147490818 := by
  have hSparse := OrbitCharge.control32_sparse
  rw [show (2 ^ 9 * 2 + 2 ^ 9 * (22 + 1) : ℕ) = 12800 by decide] at hSparse
  have hCorner (b : Bool) : InvariantControl.control 9 22 (fun _ => b) = true := by
    apply (InvariantControl.control_iff (r := 9) (s := 22) _).mpr
    intros
    rfl
  have hSize := (Nat.add_le_add_right hMin.le 18431).trans OrbitCharge.control32_size
  change c.size + 18431 ≤ 8589934592 at hSize
  have hUpper : c.size ≤ 8589916161 := by omega
  have h := relabel_live_loss_cap parent hSurj c hc hSparse (by decide) hCorner hUpper
  change _ + _ + 6442450944 ≤ 8589916161 + 1 + 2 * 12800 at h
  omega

def signPoint : BitString 32 :=
  Fin.append (fun _ : Fin 9 => false)
    (Fin.cons false (Fin.cons true (Fin.cons false (Fin.cons true (fun _ : Fin 19 => false)))))

/-- Copy the neighboring entry on the deleted quarter, complementing the copy
at exactly one address. -/
noncomputable def signedTable (U : BitString (3 * 2 ^ 30)) : BitString (2 ^ 32) :=
  fun i => U (foldKey 30 i) ^^ decide ((BitString.equivFin 32).symm i = signPoint)

noncomputable def signedResidual (f : BooleanFunction (2 ^ 32)) : BooleanFunction (3 * 2 ^ 30) :=
  f ∘ signedTable

@[simp] theorem signedTable_at_retained (U : BitString (3 * 2 ^ 30)) (j : Fin (3 * 2 ^ 30)) :
    signedTable U (freeEquiv 30 j).val = U j := by
  have h : keptAddress ((BitString.equivFin 32).symm (freeEquiv 30 j).val) = true :=
    (freeEquiv 30 j).property
  have hPoint : keptAddress signPoint = false := by decide
  have hNe : (BitString.equivFin 32).symm (freeEquiv 30 j).val ≠ signPoint := by
    intro he
    rw [he, hPoint] at h
    cases h
  simp only [signedTable, hNe, decide_false, Bool.xor_false, foldKey_at_retained]

private theorem signPoint_complexity :
    complexity interpretation (single fun z => decide (z = signPoint)) ≤ 66 := by
  have h := (synthesis_minterm (fun i : Fin 32 => i) signPoint).complexity_le
  exact h.trans (by decide)

theorem mcsp_signed_fold_residual_32 :
    6444118523 ≤ complexity interpretation (single (signedResidual (mcspSquare 32))) := by
  have hSparse : (acceptingTables (signedResidual (mcspSquare 32))).card ≤ 2 ^ 27672 := by
    have h := card_accepting_mcspSquare_le 32
    rw [show descriptionBitBound 32 = 27672 by decide] at h
    apply pullback_sparse signedTable _ h
    intro U V hEq
    funext j
    simpa only [signedTable_at_retained] using congrFun hEq (freeEquiv 30 j).val
  have hAff (a : BitString 32) (b : Bool) :
      mcspSquare 32 (signedTable (fun j => affine a b (labels 30 j))) = true := by
    clear hSparse
    let f := affine a b ∘ (foldCircuit 30).eval interpretation
    let s : BooleanFunction 32 := fun z => decide (z = signPoint)
    have hEq : (MCSP.truthTable 32).symm (signedTable (fun j => affine a b (labels 30 j))) =
        fun z => f z ^^ s z := by
      funext z
      change (affine a b (labels 30 (foldKey 30 (BitString.equivFin 32 z))) ^^
        decide ((BitString.equivFin 32).symm (BitString.equivFin 32 z) = signPoint)) =
        (f z ^^ decide (z = signPoint))
      rw [Equiv.symm_apply_apply, ← foldCircuit_labels]
      rfl
    rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hEq]
    have h := complexity_affine_comp_le (foldCircuit 30) a b
    change complexity interpretation (single f) ≤ 131 at h
    have hPol : complexity interpretation (single s) ≤ 66 := signPoint_complexity
    exact (complexity_xor_le f s).trans (by omega)
  have h := reindexed_forest_size (labels 30) hSparse hAff
  change 18694 * (2 * 3221225472) + 10 * 3221225472 ≤
    18694 * (complexity interpretation (single (signedResidual (mcspSquare 32))) + 2 * 27672 + 1) +
      142 * 27672 at h
  omega

/-- Negate one input before handing the wires to the original circuit. -/
def negateInputCircuit (i : Fin n) : Circuit signature n n :=
  let p : Program signature n 1 := Program.empty.gate ⟨.not, fun _ => .input i⟩
  ⟨p, fun j => if j = i then .gate 0 else .input j⟩

private theorem negateInputCircuit_eval (i j : Fin n) (x : BitString n) :
    (negateInputCircuit i).eval interpretation x j = (if j = i then !x i else x j) := by
  by_cases h : j = i
  · simp [Circuit.eval, negateInputCircuit, h]
    rfl
  · simp [Circuit.eval, negateInputCircuit, h]

def signedCircuit (c : Circuit signature (2 ^ 32) 1) : Circuit signature (2 ^ 32) 1 :=
  c.comp (negateInputCircuit (BitString.equivFin 32 signPoint))

private theorem signedTable_eval (U : BitString (3 * 2 ^ 30)) :
    (negateInputCircuit (BitString.equivFin 32 signPoint)).eval interpretation (substitute (foldSub 30) U) =
      signedTable U := by
  funext i
  rw [negateInputCircuit_eval]
  have hPoint : (BitString.equivFin 32).symm i = signPoint ↔ i = BitString.equivFin 32 signPoint :=
    (BitString.equivFin 32).symm_apply_eq
  by_cases hi : i = BitString.equivFin 32 signPoint
  · subst i
    simp [signedTable, foldSub, substitute]
  · simp [signedTable, hPoint, hi, foldSub, substitute]

/-- Charge the single added NOT once, while counting distinct omitted indices
of the augmented circuit with the existing alias and liveness partition. -/
theorem mcsp_signed_live_budget_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    6444118523 + (firstFreshLoss (signedCircuit c).program (foldSub 30)).card +
      (deadFresh (signedCircuit c).program (foldSub 30) ((signedCircuit c).outputs 0)).card ≤ c.size + 1 := by
  let d := signedCircuit c
  have hEq : restrictedWire d.program (foldSub 30) (d.outputs 0) = signedResidual (mcspSquare 32) := by
    funext U
    change d.eval interpretation (substitute (foldSub 30) U) 0 = mcspSquare 32 (signedTable U)
    simp only [d, signedCircuit, Circuit.eval_comp, signedTable_eval]
    exact congrFun (hc (signedTable U)) 0
  have hNon : ¬ ∃ b : Bool, restrictedWire d.program (foldSub 30) (d.outputs 0) = fun _ => b := by
    rintro ⟨b, hb⟩
    rw [hEq] at hb
    have hSize : complexity interpretation (single (signedResidual (mcspSquare 32))) ≤ 1 := by
      rw [hb]
      exact (Synthesis.const (s := inputs (3 * 2 ^ 30)) b).complexity_le
    have hLower := mcsp_signed_fold_residual_32
    omega
  have h := first_dead_and_residual_budget d.program (foldSub 30) (d.outputs 0) hNon
  rw [hEq] at h
  have hSize : d.size = c.size + 1 := by
    simp only [d, signedCircuit, Circuit.size_comp]
    have hOne : (negateInputCircuit (BitString.equivFin 32 signPoint)).size = 1 := rfl
    omega
  exact (Nat.add_le_add_right (Nat.add_le_add_right mcsp_signed_fold_residual_32 _) _).trans
    (h.trans hSize.le)

theorem mcsp_signed_beat_threshold_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hLoss : 2148058052 ≤ (firstFreshLoss (signedCircuit c).program (foldSub 30)).card +
      (deadFresh (signedCircuit c).program (foldSub 30) ((signedCircuit c).outputs 0)).card) :
    8592176574 ≤ c.size := by
  have h := mcsp_signed_live_budget_32 c hc
  omega

open MonotoneForest (orInputs andInputs orInputs_sound andInputs_sound)

theorem or_root_constant_of_complementary_inputs {g : ℕ} {p : Program signature n g}
    {root : Wire n g} {r : Fin g} {i j : Fin n} (hi : i ∈ orInputs p root r)
    (hj : j ∈ orInputs p root r) {fill : BitString k → BitString n}
    (hPair : ∀ U, fill U i = !(fill U j)) (U : BitString k) :
    p.trace interpretation (fill U) (.gate r) = true := by
  cases h : fill U j
  · exact orInputs_sound hi (fill U) ((hPair U).trans (by rw [h]; rfl))
  · exact orInputs_sound hj (fill U) h

theorem and_root_constant_of_complementary_inputs {g : ℕ} {p : Program signature n g}
    {root : Wire n g} {r : Fin g} {i j : Fin n} (hi : i ∈ andInputs p root r)
    (hj : j ∈ andInputs p root r) {fill : BitString k → BitString n}
    (hPair : ∀ U, fill U i = !(fill U j)) (U : BitString k) :
    p.trace interpretation (fill U) (.gate r) = false := by
  cases h : fill U j
  · exact andInputs_sound hj (fill U) h
  · exact andInputs_sound hi (fill U) ((hPair U).trans (by rw [h]; rfl))

section SignedControls

private def testPrefix (b : Bool) : BitString 9 :=
  Fin.cons false (Fin.cons b (fun _ => false))

private def testSuffix (b : Bool) : BitString 22 :=
  if b then Fin.cons true (Fin.cons false (Fin.cons true (fun _ : Fin 19 => false))) else fun _ => false

private def testAddress (p b : Bool) : BitString 32 :=
  Fin.append (testPrefix p) (Fin.cons false (testSuffix b))

private def testPoint (p b : Bool) : Fin (2 ^ 32) := BitString.equivFin 32 (testAddress p b)

set_option maxRecDepth 4000 in
private theorem test_fold_key (b : Bool) : foldKey 30 (testPoint false b) = foldKey 30 (testPoint true b) := by
  apply (labels 30).injective
  simp only [testPoint, ← foldCircuit_labels, foldCircuit_eval]
  cases b <;> decide

private theorem test_signed_value (U : BitString (3 * 2 ^ 30)) (p b : Bool) :
    signedTable U (testPoint p b) = (U (foldKey 30 (testPoint true b)) ^^ (!p && b)) := by
  unfold signedTable
  have h : decide ((BitString.equivFin 32).symm (testPoint p b) = signPoint) = (!p && b) := by
    simp only [testPoint, Equiv.symm_apply_apply]
    cases p <;> cases b <;> decide
  rw [h]
  cases p
  · rw [test_fold_key]
  · rfl

private theorem test_signed_incompatible (U : BitString (3 * 2 ^ 30))
    (h0 : signedTable U (testPoint false false) = signedTable U (testPoint false true))
    (h1 : signedTable U (testPoint true false) = signedTable U (testPoint true true)) : False := by
  simp only [test_signed_value] at h0 h1
  simp only [Bool.not_true, Bool.not_false, Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true] at h0 h1
  rw [h1] at h0
  generalize U (foldKey 30 (testPoint true true)) = v at h0
  cases v <;> contradiction

private theorem test_keep (b : Bool) : testSuffix b ∈ SplitControl.keep := by
  classical
  simp only [SplitControl.keep, Finset.mem_compl, SplitControl.omitted, Finset.mem_image,
    Finset.mem_univ, true_and]
  rintro ⟨j, hj⟩
  have he := congrArg (BitString.equivFin 22) hj
  change BitString.equivFin 22 ((BitString.equivFin 22).symm (SplitControl.omittedIndex j)) =
    BitString.equivFin 22 (testSuffix b) at he
  rw [Equiv.apply_symm_apply] at he
  have hv := congrArg Fin.val he
  have hBound : (BitString.equivFin 22 (testSuffix b)).val = 0 ∨
      4 < (BitString.equivFin 22 (testSuffix b)).val := by
    cases b
    · exact Or.inl (by decide)
    · exact Or.inr (by decide)
  change j.val + 1 = _ at hv
  omega

private theorem test_in_band (b : Bool) :
    Fin.cons false (testSuffix b) ∈ InvariantControl.retained 23 ∧
      InvariantControl.lowWeight (Fin.cons false (testSuffix b)) = true := by
  classical
  cases b
  · have hz : (Fin.cons false (testSuffix false) : BitString 23) = fun _ => false := by decide
    rw [hz]
    refine ⟨?_, by simp [InvariantControl.lowWeight, InvariantControl.weight]⟩
    simp only [InvariantControl.retained, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨j, hj⟩
    have h := congrFun hj j
    simp [InvariantControl.unit] at h
  · let z : BitString 23 := Fin.cons false (OrbitCharge.suffixForBand true)
    let e : Equiv.Perm (Fin 23) := Equiv.swap 2 3
    have hEq : z ∘ e = Fin.cons false (testSuffix true) := by decide
    obtain ⟨hKeep, hBand⟩ := OrbitCharge.split_pair_in_band true false
    rw [← hEq]
    exact ⟨(InvariantControl.retained_perm z e).mpr hKeep,
      (InvariantControl.lowWeight_perm z e).trans hBand⟩

/-- The signed identification imposes two incompatible equalities on either
control, even though exact MCSP retains its affine witnesses. -/
theorem split_signed_fold_rejects_all (U : BitString (3 * 2 ^ 30)) :
    SplitControl.railControl 9 SplitControl.keep (signedTable U) = false := by
  classical
  apply Bool.eq_false_of_not_eq_true
  intro h
  rw [SplitControl.railControl, decide_eq_true_eq] at h
  have he (p : Bool) : signedTable U (testPoint p false) = signedTable U (testPoint p true) :=
    (SampleControls.agreesOn_eq_true _ _).mp (h (testPrefix p, false)) _
      (SplitControl.position_mem_railBlock _ _ _ (test_keep false)) _
      (SplitControl.position_mem_railBlock _ _ _ (test_keep true))
  exact test_signed_incompatible U (he false) (he true)

set_option maxRecDepth 4000 in
theorem invariant_signed_fold_rejects_all (U : BitString (3 * 2 ^ 30)) :
    InvariantControl.control 9 22 (signedTable U) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  obtain ⟨h0, h0b⟩ := test_in_band false
  obtain ⟨h1, h1b⟩ := test_in_band true
  have he (p : Bool) : signedTable U (testPoint p false) = signedTable U (testPoint p true) := by
    have hx := (InvariantControl.control_iff (r := 9) (s := 22) (signedTable U)).mp h
      (testPrefix p) (Fin.cons false (testSuffix false)) (Fin.cons false (testSuffix true))
      h0 h1 (h0b.trans h1b.symm)
    exact hx
  exact test_signed_incompatible U (he false) (he true)

end SignedControls

#print axioms mcsp_address_circuit_residual_32
#print axioms mcsp_fold_residual_32
#print axioms mcsp_fold_live_budget_32
#print axioms fold_preserves_rich_probe
#print axioms split_relabel_live_loss_cap_32
#print axioms invariant_relabel_live_loss_cap_32
#print axioms mcsp_signed_fold_residual_32
#print axioms mcsp_signed_live_budget_32
#print axioms mcsp_signed_beat_threshold_32
#print axioms or_root_constant_of_complementary_inputs
#print axioms and_root_constant_of_complementary_inputs
#print axioms split_signed_fold_rejects_all
#print axioms invariant_signed_fold_rejects_all

end PvsNP.Frontier.QuarterFold
