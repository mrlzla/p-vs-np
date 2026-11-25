module

public import MCSPQuarterBlock
public import MCSPMinorityResidual

/-! Rich point families sharpen the stopping rule for the quarter-block
zero-pinning schedule. The witness bits all lie outside the deleted block. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterProbes

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open QuarterBlock MinorityResidual AdaptivePinning
open RestrictionCharges FreshCharges NestedFaces

variable {n : ℕ}

/-- If the remaining target bits are inessential, each accepted seed
extends to a whole cube on those bits. Distinct seeds that are zero on the
target block give disjoint cubes. -/
theorem joint_accepted_cube_bound {α : Type*} [Fintype α]
    (f : BooleanFunction n) (S D R : Finset (Fin n)) (hDR : Disjoint D R) (hAll : D ∪ R = S)
    (seed : α → BitString n) (hInj : Function.Injective seed)
    (hZero : ∀ a i, i ∈ S → seed a i = false)
    (hAccept : ∀ a, f (seed a) = true)
    (hNone : ∀ i ∈ R, ¬EssentialAt (fun x => f (substitute (pinZero D) x)) i) :
    Fintype.card α * 2 ^ R.card ≤ (acceptingTables f).card := by
  classical
  let table (z : α × (R → Bool)) : BitString n :=
    fun i => if h : i ∈ R then z.2 ⟨i, h⟩ else seed z.1 i
  have hD : D ⊆ S := hAll ▸ Finset.subset_union_left
  have hR : R ⊆ S := hAll ▸ Finset.subset_union_right
  have hFixed {y : BitString n} (hy : ∀ i ∈ D, y i = false) :
      substitute (pinZero D) y = y := by
    funext i
    by_cases hi : i ∈ D
    · simp [substitute, pinZero, hi, hy i hi]
    · simp [substitute, pinZero, hi]
  have hSeedFixed (a : α) : substitute (pinZero D) (seed a) = seed a :=
    hFixed (fun i hi => hZero a i (hD hi))
  have hTableFixed (z : α × (R → Bool)) : substitute (pinZero D) (table z) = table z := by
    apply hFixed
    intro i hi
    have hn : i ∉ R := fun hm => Finset.disjoint_left.mp hDR hi hm
    simp [table, hn, hZero z.1 i (hD hi)]
  have hTableAccept (z : α × (R → Bool)) : f (table z) = true := by
    have h := eq_of_agree_off (f := fun x => f (substitute (pinZero D) x)) R hNone
      (x := table z) (y := seed z.1) (fun i hi => by simp [table, hi])
    change f (substitute (pinZero D) (table z)) = f (substitute (pinZero D) (seed z.1)) at h
    rw [hTableFixed, hSeedFixed] at h
    exact h.trans (hAccept z.1)
  let into (z : α × (R → Bool)) : ↥(acceptingTables f) :=
    ⟨table z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTableAccept z⟩⟩
  have hi : Function.Injective into := by
    intro u v h
    have he : table u = table v := congrArg Subtype.val h
    apply Prod.ext
    · apply hInj
      funext j
      by_cases hj : j ∈ R
      · exact (hZero u.1 j (hR hj)).trans (hZero v.1 j (hR hj)).symm
      · simpa [table, hj] using congrFun he j
    · funext j
      simpa [table, j.property] using congrFun he j.val
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using
    Fintype.card_le_of_injective into hi

theorem adaptive_pinned_charge_of_family {k l g : ℕ} {α : Type*} [Fintype α]
    (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool)
    (root : Wire n g) {f : BooleanFunction k} {A B : ℕ}
    (hEq : restrictedWire p ρ root = f)
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (h0 : f (fun _ => false) = true)
    (S : Finset (Fin k)) (hPin : ∀ i ∈ S, τ i = .inr false)
    (seed : α → BitString k) (hInj : Function.Injective seed)
    (hCard : Fintype.card α = 2 ^ A)
    (hZero : ∀ a i, i ∈ S → seed a i = false) (hAccept : ∀ a, f (seed a) = true) :
    S.card ≤ (nextFreshLoss p ρ τ).card + (B - A) := by
  refine adaptive_pinned_charge_of_stop p ρ τ root hEq h0 S hPin ?_
  intro D R hDR hAll hNone
  have h := (joint_accepted_cube_bound f S D R hDR hAll seed hInj hZero hAccept hNone).trans hSparse
  rw [hCard, ← pow_add] at h
  have hExp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h
  omega

/-- At arity 32, any table with at most 29 true entries fits the cutoff. -/
theorem point_tables_accepted_32 (D : Finset (Fin (2 ^ 32))) (hD : D.card ≤ 29) :
    mcspSquare 32 (fun i => decide (i ∈ D)) = true := by
  have he : (fun i : Fin (2 ^ 32) => decide (i ∈ D)) =
      MCSP.truthTable 32 (fun z => decide (BitString.equivFin 32 z ∈ D)) := by
    funext i
    rw [MCSP.truthTable_apply, Equiv.apply_symm_apply]
  rw [he, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  apply (point_indicator_complexity_le 32 D).trans
  omega

def markerHead (j : Fin 29) : BitString 6 :=
  Fin.cons true ((BitString.equivFin 5).symm ⟨j.val, by omega⟩)

def marker (j : Fin 29) (z : BitString 26) : Fin (2 ^ 32) :=
  BitString.equivFin 32 (Fin.append (markerHead j) z)

theorem marker_injective : Function.Injective (fun z : Fin 29 × BitString 26 => marker z.1 z.2) := by
  intro u v h
  have hKey : (markerHead u.1, u.2) = (markerHead v.1, v.2) :=
    (Fin.appendEquiv 6 26).injective ((BitString.equivFin 32).injective h)
  have hH := congrArg (fun x : BitString 6 × BitString 26 => Fin.tail x.1) hKey
  simp only [markerHead, Fin.tail_cons] at hH
  have hN := congrArg Fin.val ((BitString.equivFin 5).symm.injective hH)
  have hZ : u.2 = v.2 := congrArg (fun x : BitString 6 × BitString 26 => x.2) hKey
  exact Prod.ext (Fin.ext hN) hZ

private theorem kept_marker (j : Fin 29) (z : BitString 26) : keptKey 30 (marker j z) = true := by
  rw [keptKey, marker, Equiv.symm_apply_apply]
  unfold keptAddress
  have h : (Fin.append (markerHead j) z) 0 = true := by
    change Fin.append (markerHead j) z (Fin.castAdd 26 (0 : Fin 6)) = true
    rw [Fin.append_left]
    rfl
  rw [h]
  rfl

def points (z : Fin 29 → BitString 26) : Finset (Fin (2 ^ 32)) :=
  Finset.univ.image fun j => marker j (z j)

def probe (z : Fin 29 → BitString 26) : BitString (2 ^ 32) := fun i => decide (i ∈ points z)

set_option maxHeartbeats 500000 in
theorem probe_injective : Function.Injective probe := by
  intro u v h
  funext j
  have hMu : marker j (u j) ∈ points u := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hu : probe u (marker j (u j)) = true := decide_eq_true hMu
  have hv : probe v (marker j (u j)) = true := (congrFun h _).symm.trans hu
  have hMv : marker j (u j) ∈ points v := of_decide_eq_true hv
  obtain ⟨k, _, he⟩ := Finset.mem_image.mp hMv
  have hPair : (k, v k) = (j, u j) := marker_injective he
  have hk : k = j := congrArg Prod.fst hPair
  subst k
  exact (congrArg Prod.snd hPair).symm

theorem probe_zero_on_quarter (z : Fin 29 → BitString 26) (i : Fin (2 ^ 32))
    (hi : i ∈ zeroBlock 30) : probe z i = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (of_decide_eq_true ht)
  have hh : keptKey 30 (marker j (z j)) = false := (Finset.mem_filter.mp hi).2
  rw [kept_marker] at hh
  cases hh

theorem probe_accepted (z : Fin 29 → BitString 26) : mcspSquare 32 (probe z) = true :=
  point_tables_accepted_32 (points z) ((Finset.card_image_le).trans (by simp))

theorem rich_quarter_fresh_losses_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    1073714906 ≤ (nextFreshLoss c.program
      (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool) (quarterSub 30)).card := by
  let ρ : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool := Sum.inl
  have hEq : restrictedWire c.program ρ (c.outputs 0) = mcspSquare 32 :=
    restricted_circuit_eq c hc ρ
  have hPin : ∀ i ∈ zeroBlock 30, quarterSub 30 i = .inr false := by
    intro i hi
    have hx : keptKey 30 i = false := (Finset.mem_filter.mp hi).2
    simp [quarterSub, hx]
  have hCard : Fintype.card (Fin 29 → BitString 26) = 2 ^ 754 := by
    rw [Fintype.card_fun, Fintype.card_fin, BitString.card, ← pow_mul]
  have h := adaptive_pinned_charge_of_family c.program ρ (quarterSub 30) (c.outputs 0) hEq
    (card_accepting_mcspSquare_le 32) (mcspSquare_constant_table 32 (by decide) false)
    (zeroBlock 30) hPin probe probe_injective hCard probe_zero_on_quarter probe_accepted
  rw [zeroBlock_card, show descriptionBitBound 32 = 27672 by decide] at h
  dsimp only [ρ] at h
  change 1073741824 ≤ _ at h
  omega

theorem rich_quarter_total_32 :
    7517833429 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  have h0 : residual 30 (mcspSquare 32) (fun _ => false) = true := by
    change mcspSquare 32 (fill 30 (fun _ => false)) = true
    have hEq : fill 30 (fun _ => false) = fun _ => false := by
      funext i
      rw [fill_constant 30 false i]
      cases keptKey 30 i <;> rfl
    rw [hEq]
    exact mcspSquare_constant_table 32 (by decide) false
  have hBudget := quarter_loss_budget 30 c hc (card_accepting_mcspSquare_le 32) (by decide) h0
  have hResid := mcsp_quarter_residual_32
  have hSub : nextFreshLoss c.program (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool)
      (quarterSub 30) ⊆ firstFreshLoss c.program (quarterSub 30) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  have hLoss := (rich_quarter_fresh_losses_32 c hc).trans (Finset.card_le_card hSub)
  omega

section ControlTest

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

def zeroPayloadProbe : BitString (2 ^ 32) := probe (fun _ _ => false)

private def testPrefix : BitString 9 := Fin.append (markerHead 0) (fun _ : Fin 3 => false)

private theorem probe_zero_tail_true :
    zeroPayloadProbe (InvariantControl.point (r := 9) (s := 22) testPrefix (fun _ => false)) = true := by
  have he : InvariantControl.point (r := 9) (s := 22) testPrefix (fun _ => false) =
      marker 0 (fun _ => false) := by decide
  rw [he]
  exact decide_eq_true (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)

private theorem probe_nonzero_tail_false (z : BitString 23) (hz : z ≠ fun _ => false) :
    zeroPayloadProbe (InvariantControl.point (r := 9) (s := 22) testPrefix z) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (of_decide_eq_true h)
  have hKey : Fin.append (markerHead j) (fun _ : Fin 26 => false) = Fin.append testPrefix z :=
    (BitString.equivFin 32).injective hj
  apply hz
  funext i
  have he := congrFun hKey (Fin.natAdd 9 i)
  rw [Fin.append_right] at he
  have hIndex : (Fin.natAdd 9 i : Fin 32) = Fin.natAdd 6 (Fin.natAdd 3 i) := by
    apply Fin.ext
    change 9 + i.val = 6 + (3 + i.val)
    omega
  rw [hIndex, Fin.append_right] at he
  exact he.symm

private theorem split_zero_suffix_kept : (fun _ : Fin 22 => false) ∈ SplitControl.keep := by
  classical
  simp only [SplitControl.keep, Finset.mem_compl, SplitControl.omitted, Finset.mem_image,
    Finset.mem_univ, true_and]
  rintro ⟨j, hj⟩
  have he : SplitControl.omittedIndex j = 0 := by
    have hZero : (BitString.equivFin 22) (fun _ => false) = 0 := by decide
    have he := congrArg (BitString.equivFin 22) hj
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, hZero] using he
  have hv := congrArg Fin.val he
  change j.val + 1 = 0 at hv
  omega

/-- The old split control rejects a sparse marker probe accepted by exact MCSP. -/
theorem split_rejects_rich_probe :
    SplitControl.railControl 9 SplitControl.keep zeroPayloadProbe = false := by
  classical
  obtain ⟨v, hv, hvne⟩ := SplitControl.has_other_retained (fun _ => false)
  apply Bool.eq_false_of_not_eq_true
  intro h
  rw [SplitControl.railControl, decide_eq_true_eq] at h
  have hg := h (testPrefix, false)
  have he := (SampleControls.agreesOn_eq_true _ _).mp hg _
    (SplitControl.position_mem_railBlock SplitControl.keep testPrefix false split_zero_suffix_kept) _
    (SplitControl.position_mem_railBlock SplitControl.keep testPrefix false hv)
  rw [← InvariantControl.point_cons (r := 9) (s := 22),
    ← InvariantControl.point_cons (r := 9) (s := 22)] at he
  have h0 : (Fin.cons false (fun _ : Fin 22 => false)) = fun _ => false := by
    funext j
    refine Fin.cases ?_ (fun _ => ?_) j <;> simp
  have hv' : Fin.cons false v ≠ (fun _ : Fin 23 => false) := by
    intro hEq
    apply hvne
    symm
    have hTail := congrArg Fin.tail hEq
    rw [Fin.tail_cons] at hTail
    exact hTail
  rw [h0, probe_zero_tail_true, probe_nonzero_tail_false _ hv'] at he
  cases he

/-- The permutation-invariant band control also rejects that probe. -/
theorem invariant_rejects_rich_probe :
    InvariantControl.control 9 22 zeroPayloadProbe = false := by
  classical
  let z0 : BitString 23 := fun _ => false
  let z1 : BitString 23 := Fin.cons false (OrbitCharge.suffixForBand true)
  have h0 : z0 ∈ InvariantControl.retained 23 := by
    simp only [InvariantControl.retained, Finset.mem_compl, Finset.mem_image,
      Finset.mem_univ, true_and]
    rintro ⟨j, hj⟩
    have ht : (InvariantControl.unit j : BitString 23) j = true := by
      simp [InvariantControl.unit]
    rw [hj] at ht
    cases ht
  have hB0 : InvariantControl.lowWeight z0 = true := by
    simp [InvariantControl.lowWeight, InvariantControl.weight, z0]
  obtain ⟨h1, hB1⟩ := OrbitCharge.split_pair_in_band true false
  have hz : z1 ≠ z0 := by
    intro h
    have he := congrFun h (1 : Fin 23)
    change true = false at he
    cases he
  apply Bool.eq_false_of_not_eq_true
  intro h
  have he := (InvariantControl.control_iff (r := 9) (s := 22) _).mp h testPrefix z0 z1 h0 h1
    (hB0.trans hB1.symm)
  rw [probe_zero_tail_true, probe_nonzero_tail_false _ hz] at he
  cases he

end ControlTest

#print axioms joint_accepted_cube_bound
#print axioms probe_accepted
#print axioms rich_quarter_fresh_losses_32
#print axioms rich_quarter_total_32
#print axioms split_rejects_rich_probe
#print axioms invariant_rejects_rich_probe

end PvsNP.Frontier.QuarterProbes
