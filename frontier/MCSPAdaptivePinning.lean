module

public import MCSPTwoScaleFresh

/-! Adaptive zero pinning assigns a fresh gate loss to each chosen input. -/

@[expose] public section

namespace PvsNP.Frontier.AdaptivePinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open RestrictionCharges FreshCharges NestedFaces TwoScaleFresh

variable {n k l g : ℕ}

def pinZero (S : Finset (Fin k)) (i : Fin k) : Fin k ⊕ Bool :=
  if i ∈ S then .inr false else .inl i

theorem compose_assoc (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool)
    {a : ℕ} (υ : Fin l → Fin a ⊕ Bool) :
    compose (compose ρ τ) υ = compose ρ (compose τ υ) := by
  funext i
  cases hi : ρ i <;> simp [compose, hi]

theorem compose_pins (D S : Finset (Fin k)) :
    compose (pinZero D) (pinZero S) = pinZero (D ∪ S) := by
  funext i
  by_cases hD : i ∈ D <;> by_cases hS : i ∈ S <;> simp [compose, pinZero, hD, hS]

theorem pins_before (S : Finset (Fin k)) (τ : Fin k → Fin l ⊕ Bool)
    (hPin : ∀ i ∈ S, τ i = .inr false) : compose (pinZero S) τ = τ := by
  funext i
  by_cases h : i ∈ S
  · simp [compose, pinZero, h, hPin i h]
  · simp [compose, pinZero, h]

@[simp] theorem pinZero_zero (S : Finset (Fin k)) :
    substitute (pinZero S) (fun _ => false) = (fun _ => false) := by
  funext i
  by_cases h : i ∈ S <;> simp [substitute, pinZero, h]

/-- If all remaining target slots have become inessential, the original
function accepts the subcube varying those slots. -/
private theorem remaining_card_le {f : BooleanFunction k} {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (h0 : f (fun _ => false) = true)
    (D S : Finset (Fin k)) (hDS : Disjoint D S)
    (hNone : ∀ i ∈ S, ¬ EssentialAt (fun x => f (substitute (pinZero D) x)) i) :
    S.card ≤ B := by
  classical
  let zeros : BitString k := fun _ => false
  let mask (x : BitString k) := restrictTable zeros S x
  have hKeep (x : BitString k) : substitute (pinZero D) (mask x) = mask x := by
    funext i
    by_cases hi : i ∈ D
    · have hs : i ∉ S := fun h => Finset.disjoint_left.mp hDS hi h
      simp [substitute, pinZero, hi, mask, restrictTable, hs, zeros]
    · simp [substitute, pinZero, hi]
  have hNoEss : ∀ i ∈ S, ¬EssentialAt (fun x => f (mask x)) i := by
    intro i hi h
    obtain ⟨x, y, hxy, hne⟩ := h
    apply hNone i hi
    refine ⟨mask x, mask y, ?_, ?_⟩
    · intro j hji
      by_cases hj : j ∈ S <;> simp [mask, restrictTable, hj, hxy j hji]
    · change f (substitute (pinZero D) (mask x)) ≠ f (substitute (pinZero D) (mask y))
      rw [hKeep, hKeep]
      exact hne
  have hempty : essentialPositions (fun x => f (mask x)) S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hp := Finset.mem_filter.mp hi
    exact hNoEss i hp.1 hp.2
  have h := (pow_card_inessential_le f zeros S h0).trans hSparse
  change 2 ^ (S \ essentialPositions (fun x => f (mask x)) S).card ≤ 2 ^ B at h
  rw [hempty, Finset.sdiff_empty] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

/-- Pin essential inputs first. The stopping rule leaves at most B target
slots, and each preceding pin removes at least one fresh original gate. -/
theorem adaptive_stage_charge_of_stop (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) {f : BooleanFunction k} {B : ℕ}
    (hEq : restrictedWire p ρ root = f)
    (h0 : f (fun _ => false) = true) (T S D : Finset (Fin k)) (hDS : Disjoint D S)
    (hTotal : D ∪ S = T)
    (hStop : ∀ P R : Finset (Fin k), Disjoint P R → P ∪ R = T →
      (∀ i ∈ R, ¬EssentialAt (fun x => f (substitute (pinZero P) x)) i) → R.card ≤ B) :
    S.card ≤
      (fresh p (compose ρ (pinZero D)) \ fresh p (compose ρ (pinZero (D ∪ S)))).card + B := by
  classical
  let stage (T : Finset (Fin k)) := compose ρ (pinZero T)
  have step (P Q : Finset (Fin k)) : compose (stage P) (pinZero Q) = stage (P ∪ Q) := by
    change compose (compose ρ (pinZero P)) (pinZero Q) = compose ρ (pinZero (P ∪ Q))
    rw [compose_assoc, compose_pins]
  have mono {P Q : Finset (Fin k)} (h : P ⊆ Q) :
      fresh p (stage Q) ⊆ fresh p (stage P) := by
    have he : compose (stage P) (pinZero Q) = stage Q := by
      rw [step, Finset.union_eq_right.mpr h]
    rw [← he]
    exact fresh_nested p (stage P) (pinZero Q)
  have run (P : Finset (Fin k)) :
      restrictedWire p (stage P) root = fun x => f (substitute (pinZero P) x) := by
    change restrictedWire p (compose ρ (pinZero P)) root = _
    rw [restrictedWire_compose, hEq]
  change S.card ≤ (fresh p (stage D) \ fresh p (stage (D ∪ S))).card + B
  revert D
  refine S.strongInductionOn ?_
  intro R ih D hDR hTotal
  by_cases hex : ∃ i ∈ R, EssentialAt (restrictedWire p (stage D) root) i
  · obtain ⟨i, hi, hEss⟩ := hex
    let P := D ∪ ({i} : Finset (Fin k))
    have heTotal : P ∪ R.erase i = D ∪ R := by
      change (D ∪ ({i} : Finset (Fin k))) ∪ R.erase i = _
      rw [Finset.union_assoc, Finset.singleton_union, Finset.insert_erase hi]
    have hP : Disjoint P (R.erase i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hjR
      rcases Finset.mem_union.mp hj with hjD | hjI
      · exact Finset.disjoint_left.mp hDR hjD (Finset.mem_of_mem_erase hjR)
      · exact (Finset.mem_erase.mp hjR).1 (Finset.mem_singleton.mp hjI)
    have hRest := ih (R.erase i) (Finset.erase_ssubset hi) P hP (heTotal.trans hTotal)
    rw [heTotal, Finset.card_erase_of_mem hi] at hRest
    have hZero : restrictedWire p (stage D) root (fun _ => false) = true := by
      rw [run]
      change f (substitute (pinZero D) (fun _ => false)) = true
      rw [pinZero_zero]
      exact h0
    have hNonproject : restrictedWire p (stage D) root ≠ projection i := by
      intro h
      rw [h] at hZero
      cases hZero
    have hOne := twice_nextFreshLoss_ge p (stage D) (pinZero {i}) root {i}
      (fun j hj => by rwa [Finset.mem_singleton.mp hj])
      (fun j hj => by rwa [Finset.mem_singleton.mp hj])
      (fun j hj => ⟨false, by simp [pinZero, hj]⟩)
    rw [Finset.card_singleton] at hOne
    change 1 ≤ 2 * (fresh p (stage D) \ fresh p (compose (stage D) (pinZero {i}))).card at hOne
    rw [step] at hOne
    change 1 ≤ 2 * (fresh p (stage D) \ fresh p (stage P)).card at hOne
    have hd : D ⊆ P := Finset.subset_union_left
    have hpr : P ⊆ D ∪ R := by
      refine Finset.union_subset Finset.subset_union_left ?_
      exact (Finset.singleton_subset_iff.mpr hi).trans Finset.subset_union_right
    have h₁ := Finset.card_sdiff_add_card_eq_card (mono hd)
    have h₂ := Finset.card_sdiff_add_card_eq_card (mono hpr)
    have h₃ := Finset.card_sdiff_add_card_eq_card (mono (hd.trans hpr))
    have hpos : 0 < R.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  · have hNone : ∀ i ∈ R, ¬ EssentialAt (fun x => f (substitute (pinZero D) x)) i := by
      intro i hi h
      exact hex ⟨i, hi, by rwa [run]⟩
    have h := hStop D R hDR hTotal hNone
    omega

theorem adaptive_stage_charge (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) {f : BooleanFunction k} {B : ℕ}
    (hEq : restrictedWire p ρ root = f) (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (h0 : f (fun _ => false) = true) (S D : Finset (Fin k)) (hDS : Disjoint D S) :
    S.card ≤
      (fresh p (compose ρ (pinZero D)) \ fresh p (compose ρ (pinZero (D ∪ S)))).card + B :=
  adaptive_stage_charge_of_stop p ρ root hEq h0 (D ∪ S) S D hDS rfl
    (fun P R hPR _ hNone => remaining_card_le hSparse h0 P R hPR hNone)

/-- Later wiring or additional substitutions can only lose more fresh gates.
Thus it suffices that the target slots of the final substitution are zero. -/
theorem adaptive_pinned_charge_of_stop (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (root : Wire n g) {f : BooleanFunction k} {B : ℕ}
    (hEq : restrictedWire p ρ root = f)
    (h0 : f (fun _ => false) = true) (S : Finset (Fin k))
    (hPin : ∀ i ∈ S, τ i = .inr false)
    (hStop : ∀ P R : Finset (Fin k), Disjoint P R → P ∪ R = S →
      (∀ i ∈ R, ¬EssentialAt (fun x => f (substitute (pinZero P) x)) i) → R.card ≤ B) :
    S.card ≤ (nextFreshLoss p ρ τ).card + B := by
  classical
  have h := adaptive_stage_charge_of_stop p ρ root hEq h0 S S ∅ (by simp) (by simp) hStop
  have hStart : compose ρ (pinZero ∅) = ρ := by
    funext i
    cases hi : ρ i <;> simp [compose, pinZero, hi]
  rw [hStart, Finset.empty_union] at h
  have he : compose (compose ρ (pinZero S)) τ = compose ρ τ := by
    rw [compose_assoc, pins_before S τ hPin]
  have hsub := fresh_nested p (compose ρ (pinZero S)) τ
  rw [he] at hsub
  have hc : fresh p ρ \ fresh p (compose ρ (pinZero S)) ⊆ nextFreshLoss p ρ τ := by
    intro j hj
    obtain ⟨hFirst, hMiddle⟩ := Finset.mem_sdiff.mp hj
    exact Finset.mem_sdiff.mpr ⟨hFirst, fun hFinal => hMiddle (hsub hFinal)⟩
  exact h.trans (Nat.add_le_add_right (Finset.card_le_card hc) _)

theorem adaptive_pinned_charge (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (root : Wire n g) {f : BooleanFunction k} {B : ℕ}
    (hEq : restrictedWire p ρ root = f) (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (h0 : f (fun _ => false) = true) (S : Finset (Fin k))
    (hPin : ∀ i ∈ S, τ i = .inr false) :
    S.card ≤ (nextFreshLoss p ρ τ).card + B :=
  adaptive_pinned_charge_of_stop p ρ τ root hEq h0 S hPin
    (fun P R hPR _ hNone => remaining_card_le hSparse h0 P R hPR hNone)

private theorem pinned_face_zero (m : ℕ) (i : Fin (2 ^ (m + 1))) (hi : i ∈ pinned (faceSub m)) :
    faceSub m i = .inr false := by
  obtain ⟨b, hb⟩ := (Finset.mem_filter.mp hi).2
  cases h : ((BitString.equivFin (m + 1)).symm i) 0 <;> simp [faceSub, h] at hb ⊢

theorem adaptive_first_face (m : ℕ)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    2 ^ (m + 1) ≤ (firstFreshLoss c.program (faceSub (m + 1))).card + descriptionBitBound (m + 2) := by
  let ρ : Fin (2 ^ (m + 2)) → Fin (2 ^ (m + 2)) ⊕ Bool := Sum.inl
  have hEq : restrictedWire c.program ρ (c.outputs 0) = mcspSquare (m + 2) :=
    restricted_circuit_eq c hc ρ
  have h := adaptive_pinned_charge c.program ρ (faceSub (m + 1)) (c.outputs 0) hEq
    (card_accepting_mcspSquare_le _) (mcspSquare_constant_table _ (by omega) false)
    (pinned (faceSub (m + 1))) (pinned_face_zero (m + 1))
  rw [card_pinned_face] at h
  have hsub : nextFreshLoss c.program ρ (faceSub (m + 1)) ⊆ firstFreshLoss c.program (faceSub (m + 1)) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  exact h.trans (Nat.add_le_add_right (Finset.card_le_card hsub) _)

theorem adaptive_second_face (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    2 ^ m ≤ (nextFreshLoss c.program (faceSub (m + 1)) (faceSub m)).card + descriptionBitBound (m + 2) := by
  have hEq : restrictedWire c.program (faceSub (m + 1)) (c.outputs 0) = middle m :=
    restricted_circuit_eq c hc (faceSub (m + 1))
  have h0 := middle_affine m hm (fun _ => false) false
  rw [affine_constant] at h0
  have h := adaptive_pinned_charge c.program (faceSub (m + 1)) (faceSub m) (c.outputs 0) hEq
    (middle_sparse m) h0 (pinned (faceSub m)) (pinned_face_zero m)
  rwa [card_pinned_face] at h

/-- Combine the improved disjoint charges with the forest lower bound
for the final face. -/
theorem adaptive_two_scale_bound (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    5 * 2 ^ m + 2 ^ m / 2280 ≤ c.size + 5 * descriptionBitBound (m + 2) + 3 := by
  have h1 := adaptive_first_face m c hc
  have h2 := adaptive_second_face m hm c hc
  have hBoth := (two_faces_fresh_budget m hm c hc).2
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := pow_succ' 2 m
  omega

theorem adaptive_second_face_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    1073714152 ≤ (nextFreshLoss c.program (faceSub 31) (faceSub 30)).card := by
  have h := adaptive_second_face 30 (by decide) c hc
  rw [show descriptionBitBound (30 + 2) = 27672 by decide] at h
  change 1073741824 ≤ (nextFreshLoss c.program (faceSub 31) (faceSub 30)).card + 27672 at h
  omega

theorem adaptive_two_scale_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    5369041696 ≤ c.size := by
  have h := adaptive_two_scale_bound 30 (by decide) c hc
  rw [show descriptionBitBound (30 + 2) = 27672 by decide] at h
  rw [show 5 * 2 ^ 30 + (2 : ℕ) ^ 30 / 2280 = 5369180059 by norm_num] at h
  omega

/-- Comparison of the numerical lower bounds at every arity where both apply. -/
theorem adaptive_bound_le_direct (m : ℕ) :
    5 * 2 ^ m + 2 ^ m / 2280 - (5 * descriptionBitBound (m + 2) + 3) ≤
      2 * 2 ^ (m + 2) + 2 ^ (m + 2) / 2280 - (3 * descriptionBitBound (m + 2) + 1) := by
  have hpow : (2 : ℕ) ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  rw [hpow]
  omega

#print axioms adaptive_stage_charge
#print axioms adaptive_pinned_charge
#print axioms adaptive_second_face_32
#print axioms adaptive_two_scale_32
#print axioms adaptive_bound_le_direct

end PvsNP.Frontier.AdaptivePinning
