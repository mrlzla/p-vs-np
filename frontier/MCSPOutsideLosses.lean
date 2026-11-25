module

public import MCSPFreshBypass

/-! Account for fresh losses outside the stop set in the original corner
certificates and in the residual gate budget. -/

@[expose] public section

namespace PvsNP.Frontier.OutsideLosses

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest
open RestrictionCharges FreshCharges ForestPinning

variable {n g k l : ℕ}

/-- A state belongs to a set of gate indices when its source is one of those gates. -/
def InBlock (S : Finset (Fin g)) (key : Wire n g × Bool) : Prop :=
  match key.1 with
  | .input _ => False
  | .gate j => j ∈ S

instance (S : Finset (Fin g)) (key : Wire n g × Bool) : Decidable (InBlock S key) := by
  rcases key with ⟨w, b⟩
  cases w <;> unfold InBlock <;> infer_instance

noncomputable def requested (p : Program signature n g) (root : Wire n g)
    (S : Finset (Fin g)) : Finset (Wire n g × Bool) :=
  S.biUnion (req p root)

/-- States needed by remaining gates and supplied by the removed block. -/
noncomputable def entering (p : Program signature n g) (root : Wire n g)
    (S : Finset (Fin g)) : Finset (Wire n g × Bool) := open scoped Classical in
  (requested p root (Finset.univ \ S)).filter (InBlock S)

/-- States needed by the removed block and supplied by remaining gates or by inputs. -/
noncomputable def leaving (p : Program signature n g) (root : Wire n g)
    (S : Finset (Fin g)) : Finset (Wire n g × Bool) := open scoped Classical in
  (requested p root S).filter fun key => ¬ InBlock S key

private theorem outside_req_disjoint {p : Program signature n g} {root : Wire n g}
    {i j : Fin g} (hi : i ∉ StopGate p root) (hne : i ≠ j) :
    Disjoint (req p root i) (req p root j) := by
  apply Finset.disjoint_left.mpr
  intro key h1 h2
  exact stopGate_not_hasRepeat hi ⟨key, h1, mem_repeatStates_of_ne hne h1 h2⟩

private theorem output_not_inBlock {p : Program signature n g} {root : Wire n g}
    {S : Finset (Fin g)} (hS : ∀ j ∈ S, j ∉ StopGate p root) :
    ¬ InBlock S (root, true) := by
  intro h
  cases root with
  | input i => exact h
  | gate j =>
    have hn := not_badFlip_of_not_cutGate
      (fun hc => hS j h (cutGate_subset_stopGate _ _ hc))
    exact (not_s0_s1_of_not_badFlip hn).2.1 NeedCorner.output

private theorem card_block_states (p : Program signature n g) (root : Wire n g)
    (S : Finset (Fin g)) :
    ((stateSet (Need p root)).filter (InBlock S)).card =
      ∑ j ∈ S, (valSet p root j).card := by
  classical
  let toState (z : Σ _ : Fin g, Bool) : Wire n g × Bool := (.gate z.1, z.2)
  have hi : Function.Injective toState := by
    rintro ⟨j, b⟩ ⟨u, c⟩ h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
    have he : j = u := by injection h1
    have hb : b = c := h2
    subst u
    subst c
    rfl
  have he : (S.sigma (valSet p root)).image toState =
      (stateSet (Need p root)).filter (InBlock S) := by
    ext key
    constructor
    · intro hk
      obtain ⟨⟨j, b⟩, hz, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hJ, hb⟩ := Finset.mem_sigma.mp hz
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩, hJ⟩
    · rintro hk
      obtain ⟨hN, hB⟩ := Finset.mem_filter.mp hk
      rcases key with ⟨w, b⟩
      cases w with
      | input i => exact hB.elim
      | gate j =>
        exact Finset.mem_image.mpr ⟨⟨j, b⟩, Finset.mem_sigma.mpr
          ⟨hB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hN).2⟩⟩, rfl⟩
  rw [← he, Finset.card_image_of_injective _ hi, Finset.card_sigma]

/-- A clean block has no unused capacity or repeated requests. Its gate count
equals its net demand across the original certificate boundary. Internal
states cancel, regardless of how the block was chosen. -/
theorem outside_block_balance (p : Program signature n g) (root : Wire n g)
    (S : Finset (Fin g)) (hS : ∀ j ∈ S, j ∉ StopGate p root) :
    S.card + (entering p root S).card = (leaving p root S).card := by
  classical
  let inner := requested p root S
  let outer := requested p root (Finset.univ \ S)
  let closed := inner.filter (InBlock S)
  have hDisj : Disjoint inner outer := by
    apply Finset.disjoint_left.mpr
    intro key hi ho
    obtain ⟨i, hiS, hiReq⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨j, hjS, hjReq⟩ := Finset.mem_biUnion.mp ho
    have hij : i ≠ j := fun he => (Finset.mem_sdiff.mp hjS).2 (he ▸ hiS)
    exact Finset.disjoint_left.mp (outside_req_disjoint (hS i hiS) hij) hiReq hjReq
  have hUnion : allArgs p root = inner ∪ outer := by
    ext key
    constructor
    · intro hk
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hk
      by_cases h : j ∈ S
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, h, hj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩, hj⟩)
    · intro hk
      rcases Finset.mem_union.mp hk with hk | hk <;>
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hk <;>
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hStates : (stateSet (Need p root)).filter (InBlock S) =
      closed ∪ entering p root S := by
    ext key
    simp only [stateSet_need_eq, hUnion, closed, entering, outer, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨rfl | h, hIn⟩
      · exact (output_not_inBlock hS hIn).elim
      · exact h.elim (fun h => Or.inl ⟨h, hIn⟩) (fun h => Or.inr ⟨h, hIn⟩)
    · rintro (⟨h, hIn⟩ | ⟨h, hIn⟩)
      · exact ⟨Or.inr (Or.inl h), hIn⟩
      · exact ⟨Or.inr (Or.inr h), hIn⟩
  have hStatesDisj : Disjoint closed (entering p root S) :=
    hDisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hStateCard := card_block_states p root S
  rw [hStates, Finset.card_union_of_disjoint hStatesDisj] at hStateCard
  have hReqCard : inner.card = ∑ j ∈ S, (req p root j).card := by
    exact Finset.card_biUnion fun i hi j _ hne => outside_req_disjoint (hS i hi) hne
  have hBal : (∑ j ∈ S, (req p root j).card) =
      (∑ j ∈ S, (valSet p root j).card) + S.card := calc
    _ = ∑ j ∈ S, ((valSet p root j).card + 1) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hNotBad := not_badGates_of_not_cutGate
        (fun h => hS j hj (cutGate_subset_stopGate _ _ h))
      have hUnused : unused p root j = 0 := by
        by_contra hne
        exact hNotBad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
      have hLe := card_req_le p root j
      unfold unused at hUnused
      omega
    _ = _ := by simp [Finset.sum_add_distrib]
  have hDiff : inner \ closed = leaving p root S := by
    ext key
    simp only [closed, leaving, inner, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  have hSplit := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset (InBlock S) inner)
  change (inner \ closed).card + closed.card = inner.card at hSplit
  rw [hDiff] at hSplit
  omega

/-- The original clean fresh losses carry their exact net boundary demand.
They cannot be put alongside the unadjusted corner ledger as an extra term. -/
theorem outside_fresh_loss_balance (p : Program signature n g) (root : Wire n g)
    (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) :
    let S := nextFreshLoss p ρ τ \ StopGate p root
    S.card + (entering p root S).card = (leaving p root S).card :=
  outside_block_balance p root _ (fun _ hj => (Finset.mem_sdiff.mp hj).2)

/-- The old corner ledger and an explicitly adjusted outside charge
give equivalent lower-bound statements for the full circuit. -/
theorem adjusted_full_size_bound_iff (p : Program signature n g) (root : Wire n g)
    (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) (b : ℕ) :
    let S := nextFreshLoss p ρ τ \ StopGate p root
    b + S.card + (entering p root S).card ≤ g + (leaving p root S).card ↔ b ≤ g := by
  have h := outside_fresh_loss_balance p root ρ τ
  dsimp only at h ⊢
  omega

private theorem split_later_losses_card (p : Program signature n g) (root : Wire n g)
    (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) :
    (nextFreshLoss p ρ τ \ StopGate p root).card +
      (nextFreshLoss p ρ τ ∩ StopGate p root).card = (nextFreshLoss p ρ τ).card := by
  have hSplit := Finset.card_sdiff_add_card_eq_card
    (show nextFreshLoss p ρ τ ∩ StopGate p root ⊆ nextFreshLoss p ρ τ from Finset.inter_subset_left)
  have hRem : nextFreshLoss p ρ τ \ (nextFreshLoss p ρ τ ∩ StopGate p root) =
      nextFreshLoss p ρ τ \ StopGate p root := by
    rw [Finset.inter_comm, Finset.sdiff_inter_self_right]
  rw [hRem] at hSplit
  exact hSplit

/-- Any lower bound on the later fresh losses also bounds the original
boundary demand of their clean part, with the stop losses kept separate. -/
theorem late_loss_boundary_credit (p : Program signature n g) (root : Wire n g)
    (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) (b : ℕ)
    (hb : b ≤ (nextFreshLoss p ρ τ).card) :
    let S := nextFreshLoss p ρ τ \ StopGate p root
    b + (entering p root S).card ≤
      (nextFreshLoss p ρ τ ∩ StopGate p root).card + (leaving p root S).card := by
  have hSplit := split_later_losses_card p root ρ τ
  have h := outside_fresh_loss_balance p root ρ τ
  dsimp only at h ⊢
  omega

/-- Both loss sets can be added to a lower bound for the residual circuit.
The initial redundancy set is also disjoint from the later two sets. -/
theorem residual_and_split_losses_budget (p : Program signature n g) (root : Wire n g)
    (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) :
    complexity interpretation (single (restrictedWire p (compose ρ τ) root)) +
      (firstFreshLoss p ρ).card +
      (nextFreshLoss p ρ τ ∩ StopGate p root).card +
      (nextFreshLoss p ρ τ \ StopGate p root).card ≤ g + 2 := by
  have hInit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (fresh p ρ))
  simp only [Finset.card_univ, Fintype.card_fin] at hInit
  change (firstFreshLoss p ρ).card + (fresh p ρ).card = g at hInit
  have hNext := Finset.card_sdiff_add_card_eq_card (fresh_nested p ρ τ)
  change (nextFreshLoss p ρ τ).card + (fresh p (compose ρ τ)).card =
    (fresh p ρ).card at hNext
  have hSplit := split_later_losses_card p root ρ τ
  have hSize := fresh_complexity_le p (compose ρ τ) root
  omega

/-- For the minimum escape control, the outside loss of gate 5 deletes no
raw-input request. It trades two outward gate states for one inward state,
so the old certificates already account for the full unit. -/
theorem escape_outside_boundary :
    (5 : Fin 9) ∈ nextFreshLoss FreshBypass.escapeProgram
      (pinAt FreshBypass.escapeX {2}) (pinAt FreshBypass.escapeX {1}) \
      StopGate FreshBypass.escapeProgram (.gate 8) ∧
    leaving FreshBypass.escapeProgram (.gate 8) {5} = {(.gate 3, false), (.gate 4, false)} ∧
    (entering FreshBypass.escapeProgram (.gate 8) {5}).card = 1 := by
  classical
  have hLeave : leaving FreshBypass.escapeProgram (.gate 8) {5} =
      {(.gate 3, false), (.gate 4, false)} := by
    unfold leaving requested
    rw [Finset.singleton_biUnion, FreshBypass.escape_five_requests]
    ext key
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, by rcases h with rfl | rfl <;> decide⟩⟩
  have hBal := outside_block_balance FreshBypass.escapeProgram (.gate 8) {5}
    (fun j hj => by
      have he : j = 5 := Finset.mem_singleton.mp hj
      rw [he]
      exact FreshBypass.escape_five_not_stop)
  rw [hLeave] at hBal
  have hCount : ({(.gate 3, false), (.gate 4, false)} : Finset (Wire 8 9 × Bool)).card = 2 := by
    decide
  rw [Finset.card_singleton, hCount] at hBal
  exact ⟨FreshBypass.escape_outside_loss, hLeave, by omega⟩

#print axioms outside_fresh_loss_balance
#print axioms adjusted_full_size_bound_iff
#print axioms late_loss_boundary_credit
#print axioms residual_and_split_losses_budget
#print axioms escape_outside_boundary

end PvsNP.Frontier.OutsideLosses
