module

public import MCSPAdaptivePinning
public import MCSPSuperTwoN

/-! Adaptively pin the raw stop inputs left by an affine forest certificate. -/

@[expose] public section

namespace PvsNP.Frontier.ForestPinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates MonotoneForest TwoCornerStructure SuperTwoN
open RestrictionCharges FreshCharges AdaptivePinning NestedFaces

variable {n g : ℕ}

def pinAt (x : BitString n) (P : Finset (Fin n)) (i : Fin n) : Fin n ⊕ Bool :=
  if i ∈ P then .inr (x i) else .inl i

private theorem compose_pinAt (x : BitString n) (P Q : Finset (Fin n)) :
    compose (pinAt x P) (pinAt x Q) = pinAt x (P ∪ Q) := by
  funext i
  by_cases hP : i ∈ P <;> by_cases hQ : i ∈ Q <;> simp [compose, pinAt, hP, hQ]

private theorem substitute_pinAt_eq {x y : BitString n} {P : Finset (Fin n)}
    (h : ∀ i ∈ P, y i = x i) : substitute (pinAt x P) y = y := by
  funext i
  by_cases hi : i ∈ P
  · simp [substitute, pinAt, hi, h i hi]
  · simp [substitute, pinAt, hi]

private def Forces (f : BooleanFunction n) (x : BitString n) (P : Finset (Fin n)) : Prop :=
  ∀ y, (∀ i ∈ P, y i = x i) → f y = true

/-- With base pins fixed, retain an inclusion-minimal subset of the candidate pins. -/
private theorem minimal_extension (f : BooleanFunction n) (x : BitString n)
    (P S : Finset (Fin n)) (hForces : Forces f x (P ∪ S)) :
    ∃ Q ⊆ S, Forces f x (P ∪ Q) ∧ ∀ i ∈ Q, ¬ Forces f x (P ∪ Q.erase i) := by
  classical
  revert hForces
  refine S.strongInductionOn ?_
  intro S ih hForces
  by_cases h : ∃ i ∈ S, Forces f x (P ∪ S.erase i)
  · obtain ⟨i, hi, hForce⟩ := h
    obtain ⟨Q, hQ, hQForce, hMin⟩ := ih (S.erase i) (Finset.erase_ssubset hi) hForce
    exact ⟨Q, hQ.trans (Finset.erase_subset i S), hQForce, hMin⟩
  · exact ⟨S, le_rfl, hForces, fun i hi hForce => h ⟨i, hi, hForce⟩⟩

/-- A pin in a minimal extension stays essential after any subset of the other
selected pins. The witness can be chosen to agree on every other selected bit. -/
private theorem essential_of_minimal {f : BooleanFunction n} {x : BitString n}
    {P Q D : Finset (Fin n)} (hForce : Forces f x (P ∪ Q)) (hD : D ⊆ Q)
    {i : Fin n} (hiD : i ∉ D) (hNot : ¬ Forces f x (P ∪ Q.erase i)) :
    EssentialAt (fun y => f (substitute (pinAt x (P ∪ D)) y)) i := by
  classical
  have hiP : i ∉ P := by
    intro hiP
    apply hNot
    intro y hy
    apply hForce
    intro j hj
    rcases Finset.mem_union.mp hj with hjP | hjQ
    · exact hy j (Finset.mem_union_left _ hjP)
    · by_cases he : j = i
      · subst j
        exact hy i (Finset.mem_union_left _ hiP)
      · exact hy j (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he, hjQ⟩))
  unfold Forces at hNot
  push Not at hNot
  obtain ⟨y, hy, hyFalse⟩ := hNot
  let z := Function.update y i (x i)
  have hzAgree (j : Fin n) (hj : j ∈ P ∪ Q) : z j = x j := by
    by_cases he : j = i
    · subst j
      simp [z]
    · rw [show z j = y j by simp [z, he]]
      apply hy
      rcases Finset.mem_union.mp hj with hjP | hjQ
      · exact Finset.mem_union_left _ hjP
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he, hjQ⟩)
  have hSub : P ∪ D ⊆ P ∪ Q.erase i := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjP | hjD
    · exact Finset.mem_union_left _ hjP
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun he => hiD (he ▸ hjD), hD hjD⟩)
  have hSub' : P ∪ D ⊆ P ∪ Q := fun _ h => by
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (hD h)
  refine ⟨y, z, fun j hj => by simp [z, hj], ?_⟩
  change f (substitute (pinAt x (P ∪ D)) y) ≠ f (substitute (pinAt x (P ∪ D)) z)
  rw [substitute_pinAt_eq (fun j hj => hy j (hSub hj)),
    substitute_pinAt_eq (fun j hj => hzAgree j (hSub' hj)), hForce z hzAgree]
  exact hyFalse

/-- Successive essential pins lose distinct original gate indices. One final
pin may receive a projection directly in an arbitrary accepted assignment. -/
private theorem charge_essential_pins (p : Program signature n g) (root : Wire n g)
    (x : BitString n) (P Q : Finset (Fin n))
    (hEss : ∀ D ⊆ Q, ∀ i ∈ Q, i ∉ D →
      EssentialAt (restrictedWire p (pinAt x (P ∪ D)) root) i) :
    Q.card ≤ (nextFreshLoss p (pinAt x P) (pinAt x Q)).card + 1 := by
  classical
  let F (D : Finset (Fin n)) := fresh p (pinAt x (P ∪ D))
  have hMono {D E : Finset (Fin n)} (h : D ⊆ E) : F E ⊆ F D := by
    have hh := fresh_nested p (pinAt x (P ∪ D)) (pinAt x E)
    rwa [compose_pinAt, Finset.union_assoc, Finset.union_eq_right.mpr h] at hh
  have aux (R : Finset (Fin n)) (D : Finset (Fin n))
      (hD : D ⊆ Q) (hR : R = Q \ D) :
      R.card ≤ (F D \ F Q).card + 1 := by
    revert D
    refine R.strongInductionOn ?_
    intro R ih D hD hR
    by_cases hCard : R.card ≤ 1
    · omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
    have hiQ := Finset.mem_sdiff.mp (hR ▸ hi)
    let E := D ∪ {i}
    have hDE : D ⊆ E := Finset.subset_union_left
    have hE : E ⊆ Q := Finset.union_subset hD (Finset.singleton_subset_iff.mpr hiQ.1)
    have hErase : R.erase i = Q \ E := by
      ext j
      rw [hR]
      simp only [E, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_union,
        Finset.mem_singleton, not_or]
      tauto
    have hRest := ih (R.erase i) (Finset.erase_ssubset hi) E hE hErase
    have hNotProj : restrictedWire p (pinAt x (P ∪ D)) root ≠ projection i := by
      intro hProj
      have hRemain : 0 < (R.erase i).card := by
        rw [Finset.card_erase_of_mem hi]
        omega
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hRemain
      have hjND := Finset.mem_sdiff.mp (hR ▸ Finset.mem_of_mem_erase hj)
      obtain ⟨u, v, huv, hn⟩ := hEss D hD j hjND.1 hjND.2
      rw [hProj] at hn
      exact hn (huv i (Ne.symm (Finset.mem_erase.mp hj).1))
    have hNew := twice_nextFreshLoss_ge p (pinAt x (P ∪ D)) (pinAt x {i}) root {i}
      (fun j hj => by simpa only [Finset.mem_singleton.mp hj] using hEss D hD i hiQ.1 hiQ.2)
      (fun j hj => by rwa [Finset.mem_singleton.mp hj])
      (fun j hj => ⟨x j, by simp [pinAt, hj]⟩)
    rw [Finset.card_singleton] at hNew
    unfold nextFreshLoss at hNew
    rw [compose_pinAt, Finset.union_assoc] at hNew
    change 1 ≤ 2 * (F D \ F E).card at hNew
    have h₁ := Finset.card_sdiff_add_card_eq_card (hMono hDE)
    have h₂ := Finset.card_sdiff_add_card_eq_card (hMono hE)
    have h₃ := Finset.card_sdiff_add_card_eq_card (hMono hD)
    rw [Finset.card_erase_of_mem hi] at hRest
    omega
  have h := aux Q ∅ (Finset.empty_subset _) Finset.sdiff_empty.symm
  simpa only [F, Finset.union_empty, nextFreshLoss, compose_pinAt] using h

/-- Charge the distinct original readers of a subset of the second set of pins. -/
theorem pins_charge_of_readers {p : Program signature n g}
    (x : BitString n) (P Q R : Finset (Fin n)) (J : Finset (Fin g)) (hQR : Q ⊆ R)
    (hQ : ∀ i ∈ Q, ∃ j ∈ J, ∃ a, (p.lines j).wires a = .input i) :
    Q.card ≤ 2 * ((J \ fresh p (pinAt x P)).card +
      (J ∩ nextFreshLoss p (pinAt x P) (pinAt x R)).card) := by
  classical
  let endPin := compose (pinAt x P) (pinAt x R)
  let redundant := J \ fresh p endPin
  let targets := redundant.biUnion fun k => Finset.univ.image (p.lines k).wires
  have hTargets : Q.image (fun i => (.input i : Wire n g)) ⊆ targets := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j, hj, a, ha⟩ := hQ i hi
    have hpin : endPin i = .inr (x i) := by
      dsimp only [endPin]
      rw [compose_pinAt]
      simp [pinAt, Finset.mem_union_right P (hQR hi)]
    let idPin : Fin n → Fin n ⊕ Bool := Sum.inl
    have hArg : restrictedWire p idPin ((p.lines j).wires a) = projection i := by
      rw [ha]
      rfl
    have hDisc := disclosed_of_pinned_projection p idPin endPin j a i (x i) hArg hpin
    change disclosed p endPin j at hDisc
    have hjRed : j ∈ redundant := Finset.mem_sdiff.mpr
      ⟨hj, fun hf => (Finset.mem_filter.mp hf).2 hDisc⟩
    exact Finset.mem_biUnion.mpr ⟨j, hjRed, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩⟩
  have hCard := Finset.card_le_card hTargets
  have hInj : Function.Injective (fun i => (.input i : Wire n g)) :=
    fun _ _ h => by cases h; rfl
  rw [Finset.card_image_of_injective _ hInj] at hCard
  have hCap : targets.card ≤ 2 * redundant.card := calc
    _ ≤ ∑ j ∈ redundant, (Finset.univ.image (p.lines j).wires).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ redundant, 2 := Finset.sum_le_sum fun j _ =>
      Finset.card_image_le.trans (by
        simpa using Program.fanInAtMost_iff.mp p.fanInAtMost_two j)
    _ = _ := by simp [Nat.mul_comm]
  let before := J \ fresh p (pinAt x P)
  let during := J ∩ nextFreshLoss p (pinAt x P) (pinAt x R)
  have hNested := fresh_nested p (pinAt x P) (pinAt x R)
  have hSplit : redundant = before ∪ during := by
    ext j
    simp only [redundant, before, during, nextFreshLoss, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_inter]
    have h := @hNested j
    change j ∈ fresh p endPin → j ∈ fresh p (pinAt x P) at h
    tauto
  have hDisj : Disjoint before during := by
    apply Finset.disjoint_left.mpr
    intro j hj hnew
    exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp (Finset.mem_inter.mp hnew).2).1
  rw [hSplit, Finset.card_union_of_disjoint hDisj] at hCap
  exact hCard.trans hCap

/-- Every raw stop pin occupies an argument of a stop gate that is redundant
by the end of pinning. -/
theorem stop_pins_charge {p : Program signature n g} {root : Wire n g}
    (x : BitString n) (P Q : Finset (Fin n)) (hQ : Q ⊆ stopInputs p root) :
    Q.card ≤ 2 * ((StopGate p root \ fresh p (pinAt x P)).card +
      (StopGate p root ∩ nextFreshLoss p (pinAt x P) (pinAt x Q)).card) := by
  apply pins_charge_of_readers x P Q Q (StopGate p root) (by rfl)
  intro i hi
  obtain ⟨j, hj, hw⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp (hQ hi)).2
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hw
  exact ⟨j, hj, a, ha⟩

/-- An essential coordinate after the forest pins has a direct stop reader
whose restricted output is essential in that coordinate. -/
theorem essential_stop_reader {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} (hMask : IsForestMask p root x P)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {i : Fin n} (hi : EssentialAt (restrictedWire p (pinAt x P) root) i) :
    ∃ j ∈ StopGate p root, (∃ a, (p.lines j).wires a = .input i) ∧
      EssentialAt (restrictedWire p (pinAt x P) (.gate j)) i := by
  classical
  obtain ⟨y, z, hyz, hne⟩ := hi
  by_contra hNo
  apply hne
  symm
  apply hMask.trace_eq h0 h1
  · intro a ha
    simp [substitute, pinAt, ha]
  · intro a ha
    simp [substitute, pinAt, ha]
  · intro j hj
    by_cases hReads : ∃ a, (p.lines j).wires a = .input i
    · right
      by_contra hDiff
      exact hNo ⟨j, hj, hReads, y, z, hyz, Ne.symm hDiff⟩
    · left
      intro a u hu
      have hui : u ≠ i := fun he => hReads ⟨a, he ▸ hu⟩
      by_cases huP : u ∈ P <;> simp [substitute, pinAt, huP, hyz u hui]

/-- Only already-redundant stop gates whose traces still vary can pay for
essential residual input pins. Constant stop gates contribute no charge. -/
theorem stop_pins_charge_nonconstant {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P Q : Finset (Fin n)} (hMask : IsForestMask p root x P)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (hEss : ∀ i ∈ Q, EssentialAt (restrictedWire p (pinAt x P) root) i) :
    Q.card ≤ 2 * (((StopGate p root ∩ surviving p (pinAt x P)) \
      fresh p (pinAt x P)).card +
      (StopGate p root ∩ nextFreshLoss p (pinAt x P) (pinAt x Q)).card) := by
  classical
  let J := StopGate p root ∩ surviving p (pinAt x P)
  have hReaders : ∀ i ∈ Q, ∃ j ∈ J, ∃ a, (p.lines j).wires a = .input i := by
    intro i hi
    obtain ⟨j, hj, hArg, y, z, _, hne⟩ := essential_stop_reader hMask h0 h1 (hEss i hi)
    refine ⟨j, Finset.mem_inter.mpr ⟨hj, ?_⟩, hArg⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, z, hne⟩
  have h := pins_charge_of_readers x P Q Q J (by rfl) hReaders
  dsimp only [J] at h
  have hSub : J ∩ nextFreshLoss p (pinAt x P) (pinAt x Q) ⊆
      StopGate p root ∩ nextFreshLoss p (pinAt x P) (pinAt x Q) := by
    intro j hj
    obtain ⟨hJ, hLoss⟩ := Finset.mem_inter.mp hj
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hJ).1, hLoss⟩
  have hCard := Finset.card_le_card hSub
  dsimp only [J] at hCard
  omega

/-- Preserve the distinction between initially redundant stop gates and
gates made redundant by the forest pins. A minimum original circuit has
at most two initially redundant indices, the reconstruction overhead. -/
theorem early_stop_bound_of_minimum (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (x : BitString n) (P : Finset (Fin n)) :
    (StopGate c.program (c.outputs 0) \ fresh c.program (pinAt x P)).card ≤
      2 + (StopGate c.program (c.outputs 0) ∩
        nextFreshLoss c.program Sum.inl (pinAt x P)).card := by
  classical
  let idPin : Fin n → Fin n ⊕ Bool := Sum.inl
  have hEq : restrictedWire c.program idPin (c.outputs 0) = f :=
    restricted_circuit_eq c hc idPin
  have hSynth := fresh_complexity_le c.program idPin (c.outputs 0)
  rw [hEq, ← hMin] at hSynth
  have hAcct := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (fresh c.program idPin))
  simp only [Finset.card_univ, Fintype.card_fin] at hAcct
  have hInitial : (firstFreshLoss c.program idPin).card ≤ 2 := by
    unfold firstFreshLoss
    omega
  let late := StopGate c.program (c.outputs 0) ∩ nextFreshLoss c.program idPin (pinAt x P)
  have hSub : StopGate c.program (c.outputs 0) \ fresh c.program (pinAt x P) ⊆
      firstFreshLoss c.program idPin ∪ late := by
    intro j hj
    obtain ⟨hStop, hAfter⟩ := Finset.mem_sdiff.mp hj
    by_cases hBefore : j ∈ fresh c.program idPin
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
        ⟨hStop, Finset.mem_sdiff.mpr ⟨hBefore, hAfter⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hBefore⟩)
  exact (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right hInitial _))

/-- The sharper corner-accounting cap applies to all stop gates already
redundant after any forest restriction. -/
theorem early_stop_bound (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (x : BitString n) (P : Finset (Fin n)) :
    (StopGate p root \ fresh p (pinAt x P)).card ≤
      47 * (∑ k : Fin g, unused p root k) + 56 * shared p root :=
  (Finset.card_le_card Finset.sdiff_subset).trans
    (card_stopGate_le_unused_and_shared p root h0 h1)

/-- For the full-size affine forest proof, only the minimal stop-input
extension is pinned. Its fresh losses are separate from any earlier losses
during the forest pins. The stop input wires themselves have a disjoint
fan-in budget with the forest-root wires. -/
theorem affine_adaptive_stop_pins {m B : ℕ} {f : BooleanFunction (2 ^ m)}
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (hAff : ∀ (a : BitString m) (b : Bool), f (MCSP.truthTable m (affine a b)) = true) :
    ∃ (x : BitString (2 ^ m)) (P Q : Finset (Fin (2 ^ m))),
      Q ⊆ stopInputs c.program (c.outputs 0) ∧
      2 ^ m ≤ P.card + Q.card + B ∧
      Q.card ≤ (nextFreshLoss c.program (pinAt x P) (pinAt x Q)).card + 1 ∧
      Q.card ≤ 2 * (((StopGate c.program (c.outputs 0) ∩ surviving c.program (pinAt x P)) \
        fresh c.program (pinAt x P)).card +
        (StopGate c.program (c.outputs 0) ∩ nextFreshLoss c.program (pinAt x P) (pinAt x Q)).card) ∧
      12 * (P.card + Q.card) ≤ 2 * 2 ^ m + 130 * B + 17238 * slack c.program (c.outputs 0) +
        26 * (StopGate c.program (c.outputs 0)).card ∧
      ∃ a b, x = MCSP.truthTable m (affine a b) := by
  classical
  obtain ⟨x, P, hP, hMask, hx, hAffMask⟩ := exists_affine_forest_mask_witness c hc hf0 hf1 hAff
  have h0 : cornerValue c.program false (c.outputs 0) = true := (congrFun (hc _) 0).trans hf0
  have h1 : cornerValue c.program true (c.outputs 0) = true := (congrFun (hc _) 0).trans hf1
  have hAccept : Forces f x (P ∪ stopInputs c.program (c.outputs 0)) := by
    intro y hy
    have he := hMask.trace_eq h0 h1 (fun _ _ => rfl)
      (fun i hi => hy i (Finset.mem_union_left _ hi))
      (fun _ hk => Or.inl fun a i ha => hy i
        (Finset.mem_union_right _ (stopInput_mem_of_wire hk a ha)))
    exact (congrFun (hc y) 0).symm.trans (he.trans ((congrFun (hc x) 0).trans hx))
  obtain ⟨Q, hQ, hQForces, hQMin⟩ := minimal_extension f x P _ hAccept
  have hEss : ∀ D ⊆ Q, ∀ i ∈ Q, i ∉ D →
      EssentialAt (restrictedWire c.program (pinAt x (P ∪ D)) (c.outputs 0)) i := by
    intro D hD i hi hiD
    rw [restricted_circuit_eq c hc]
    exact essential_of_minimal hQForces hD hiD (hQMin i hi)
  have hPin := charge_essential_pins c.program (c.outputs 0) x P Q hEss
  have hEssAtStart : ∀ i ∈ Q, EssentialAt (restrictedWire c.program (pinAt x P) (c.outputs 0)) i := by
    intro i hi
    simpa only [Finset.union_empty] using hEss ∅ (Finset.empty_subset _) i hi (Finset.notMem_empty _)
  have hSparsePins := card_masked_le hSparse x _ hQForces
  have hUnion := Finset.card_union_le P Q
  have hJoint := card_stopInputs_and_roots_le c hc hSparse hf0 hf1
  have hStop := Finset.card_le_card hQ
  exact ⟨x, P, Q, hQ, by omega, hPin, stop_pins_charge_nonconstant hMask h0 h1 hEssAtStart,
    by omega, hAffMask⟩

/-- The joint bound retains the full corner accounting and the exact
affine-slack inequality, with no rounding loss in the statement. -/
theorem mcspSquare_super_twoN_adaptive (m : ℕ) (hm : 5 ≤ m) :
    18694 * (2 * 2 ^ m) + 10 * 2 ^ m ≤
      18694 * (complexity interpretation (single (mcspSquare m)) + 2 * descriptionBitBound m + 1) +
      142 * descriptionBitBound m := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  have hf0 := mcspSquare_constant_table m (by omega) false
  have hf1 := mcspSquare_constant_table m (by omega) true
  have h0 : cornerValue c.program false (c.outputs 0) = true := (congrFun (hc _) 0).trans hf0
  have h1 : cornerValue c.program true (c.outputs 0) = true := (congrFun (hc _) 0).trans hf1
  have hSparse := card_accepting_mcspSquare_le m
  have hNI0 := card_needInputs_ge_of_sparse c hc hSparse false hf0
  have hNI1 := card_needInputs_ge_of_sparse c hc hSparse true hf1
  have hAcct := needInputs_add_slack_eq c.program (c.outputs 0) h0 h1
  obtain ⟨_, _, _, _, hPins, _, _, hBudget, _⟩ :=
    affine_adaptive_stop_pins c hc hSparse hf0 hf1 (mcspSquare_accepts_affine m hm)
  have hStop := card_stopGate_le_56_slack c.program (c.outputs 0) h0 h1
  omega

theorem mcspSquare_32_adaptive :
    8592176548 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := mcspSquare_super_twoN_adaptive 32 (by decide)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 18694 * (2 * 4294967296) + 10 * 4294967296 ≤
    18694 * (complexity interpretation (single (mcspSquare 32)) + 2 * 27672 + 1) + 142 * 27672 at h
  omega

/-- A single truth-table flip of an affine probe fits the quadratic cutoff. -/
theorem mcspSquare_accepts_affine_flip (m : ℕ) (hm : 7 ≤ m)
    (a : BitString m) (b : Bool) (i : Fin (2 ^ m)) :
    mcspSquare m (Function.update (MCSP.truthTable m (affine a b)) i
      (!(MCSP.truthTable m (affine a b) i))) = true := by
  classical
  let w := (BitString.equivFin m).symm i
  let t : BooleanFunction m := fun x => decide (x = w)
  have ht : complexity interpretation (single t) ≤ 2 * m + 1 :=
    (synthesis_minterm (id : Fin m → Fin m) w).complexity_le
  have hXor := complexity_xor_le (affine a b) t
  have hAff := complexity_affine_le a b
  have hEq : MCSP.truthTable m (fun x => affine a b x ^^ t x) =
      Function.update (MCSP.truthTable m (affine a b)) i
        (!(MCSP.truthTable m (affine a b) i)) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [MCSP.truthTable_apply, t, w]
    · have hne : (BitString.equivFin m).symm j ≠ w :=
        fun h => hj ((BitString.equivFin m).symm.injective h)
      simp [MCSP.truthTable_apply, t, hne, Function.update_of_ne hj]
  rw [← hEq, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  have hbudget : 6 * m + 6 ≤ m ^ 2 := by
    nlinarith [Nat.mul_le_mul_right m hm]
  exact hXor.trans (by omega)

/-- Both values at an unpinned coordinate leave a nonconstant MCSP branch
as long as the pinned cube has more than B free positions after that pin. -/
theorem mcspSquare_affine_pin_branches_nonconstant (m : ℕ) (hm : 7 ≤ m)
    (a : BitString m) (b : Bool) (P : Finset (Fin (2 ^ m)))
    (i : Fin (2 ^ m)) (hi : i ∉ P)
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m) (v : Bool) :
    ∃ y z : BitString (2 ^ m),
      (∀ j ∈ P, y j = MCSP.truthTable m (affine a b) j ∧
        z j = MCSP.truthTable m (affine a b) j) ∧
      y i = v ∧ z i = v ∧ mcspSquare m y = true ∧ mcspSquare m z = false := by
  let x := MCSP.truthTable m (affine a b)
  let y := Function.update x i v
  have hy : mcspSquare m y = true := by
    by_cases hv : v = x i
    · have hId : y = x := by
        dsimp [y]
        rw [hv, Function.update_eq_self]
      rw [hId]
      exact mcspSquare_accepts_affine m (by omega) a b
    · have hOpp : v = !(x i) := by cases v <;> cases h : x i <;> simp_all
      change mcspSquare m (Function.update x i v) = true
      rw [hOpp]
      exact mcspSquare_accepts_affine_flip m hm a b i
  have hNot : ∃ z : BitString (2 ^ m), (∀ j ∈ insert i P, z j = y j) ∧ mcspSquare m z = false := by
    by_contra h
    push Not at h
    have hAll : ∀ z : BitString (2 ^ m), (∀ j ∈ insert i P, z j = y j) → mcspSquare m z = true := by
      intro z hz
      exact Bool.eq_true_of_not_eq_false (h z hz)
    have hCount := card_masked_le (card_accepting_mcspSquare_le m) y _ hAll
    rw [Finset.card_insert_of_notMem hi] at hCount
    omega
  obtain ⟨z, hz, hzFalse⟩ := hNot
  have hyi : y i = v := by simp [y]
  exact ⟨y, z, fun j hj => by
    have hjne : j ≠ i := fun h => hi (h ▸ hj)
    have hEq : y j = x j := by simp [y, Function.update_of_ne hjne]
    exact ⟨hEq, (hz j (Finset.mem_insert_of_mem hj)).trans hEq⟩,
    hyi, (hz i (Finset.mem_insert_self ..)).trans hyi, hy, hzFalse⟩

/-- The current cardinal inequalities admit a linear number of essential
stop pins with zero late stop losses, even near the improved slack bound.
This is an arithmetic compatibility test, not a circuit construction. -/
theorem stop_charge_counts_allow_zero (m B : ℕ) :
    ∃ (L H R P Q A D : ℕ),
      L = 561 * 2 ^ m ∧ Q = 1500 * 2 ^ m ∧ D = 0 ∧
      A ≤ H ∧ H ≤ 56 * L ∧
      Q + R ≤ 10 * B + 1326 * L + 2 * H ∧
      12 * P ≤ 13 * R + 2 * 2 ^ (m + 20) ∧
      2 ^ (m + 20) ≤ P + Q + B ∧
      Q ≤ A + 2 * D := by
  have hN : (2 : ℕ) ^ (m + 20) = 1048576 * 2 ^ m := by
    rw [pow_add, mul_comm]
    rfl
  refine ⟨561 * 2 ^ m, 31416 * 2 ^ m, 805218 * 2 ^ m, 1047076 * 2 ^ m,
    1500 * 2 ^ m, 1500 * 2 ^ m, 0, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

#print axioms mcspSquare_32_adaptive

#print axioms stop_pins_charge_nonconstant
#print axioms early_stop_bound_of_minimum
#print axioms stop_charge_counts_allow_zero
#print axioms mcspSquare_affine_pin_branches_nonconstant
#print axioms affine_adaptive_stop_pins

end PvsNP.Frontier.ForestPinning
