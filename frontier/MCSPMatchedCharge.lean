module

public import MCSPMatchedSignals
public import MCSPSplitPinning

/-! Account for repeated certificate requests for states of matched source wires. -/

@[expose] public section

namespace PvsNP.Frontier.MatchedCharge

open Cslib Cslib.Circuits Cslib.Circuits.Boolean MultiCertificates CommunicationCut

variable {n g : ℕ}

noncomputable def requestedStates (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) : Finset (Wire n g × Bool) :=
  Finset.univ.biUnion (requestedArguments p root sample)

noncomputable def readers (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (state : Wire n g × Bool) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k => state ∈ requestedArguments p root sample k

/-- A state with (d) distinct certificate readers contributes (d-1) repeats. -/
theorem sharedRequests_eq_sum (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) :
    sharedRequests p root sample =
      ∑ state ∈ requestedStates p root sample, ((readers p root sample state).card - 1) := by
  classical
  let A := requestedStates p root sample
  let args := requestedArguments p root sample
  let count := fun state => (readers p root sample state).card
  have hsub (k : Fin g) : args k ⊆ A := fun z hz =>
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hz⟩
  have hTotal : (∑ k : Fin g, (args k).card) = ∑ z ∈ A, count z := calc
    _ = ∑ k : Fin g, ∑ z ∈ A, if z ∈ args k then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      have hFilter : A.filter (fun z => z ∈ args k) = args k := by
        ext z
        exact ⟨fun hz => (Finset.mem_filter.mp hz).2,
          fun hz => Finset.mem_filter.mpr ⟨hsub k hz, hz⟩⟩
      rw [hFilter]
      simp
    _ = ∑ z ∈ A, ∑ k : Fin g, if z ∈ args k then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_filter]
      simp [count, readers, args]
  have hpos (z : Wire n g × Bool) (hz : z ∈ A) : 0 < count z := by
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hz
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hDifference : (∑ z ∈ A, (count z - 1)) + A.card = ∑ z ∈ A, count z := by
    calc
      _ = ∑ z ∈ A, ((count z - 1) + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl fun z hz => Nat.sub_add_cancel (hpos z hz)
  change (∑ k : Fin g, (args k).card) - A.card = ∑ z ∈ A, (count z - 1)
  omega

/-- Reuse charge tracked only at the selected sources. Multiple repetitions of the
same state are counted by their actual distinct readers. -/
noncomputable def matchedRepeats (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (W : Finset (Wire n g)) : ℕ := open scoped Classical in
  ∑ state ∈ (requestedStates p root sample).filter (fun state => state.1 ∈ W),
    ((readers p root sample state).card - 1)

theorem matchedRepeats_le (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (W : Finset (Wire n g)) :
    matchedRepeats p root sample W ≤ sharedRequests p root sample := by
  classical
  rw [sharedRequests_eq_sum]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

noncomputable def matchedMargin (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (W : Finset (Wire n g)) : ℤ :=
  ((matchedRepeats p root sample W + ∑ k : Fin g, unused p root sample k : ℕ) : ℤ) -
    ((∑ k : Fin g, excess p root sample k : ℕ) : ℤ)

theorem matchedMargin_le (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (W : Finset (Wire n g)) :
    matchedMargin p root sample W ≤ netMargin p root sample := by
  have h := matchedRepeats_le p root sample W
  unfold matchedMargin netMargin
  omega

/-- The net charge required to pass the old loss with the current counting bound. -/
theorem square32_strict_of_matched_margin
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (mcspSquare 32)))
    (sample : Finset (BitString (2 ^ 32))) (h₀ : (fun _ => false) ∈ sample)
    (h₁ : (fun _ => true) ∈ sample) (W : Finset (Wire (2 ^ 32) c.size))
    (hcharge : 55346 ≤ matchedMargin c.program (c.outputs 0) sample W) :
    2 * 2 ^ 32 + 1 ≤ c.size := by
  have h := hcharge.trans (matchedMargin_le c.program (c.outputs 0) sample W)
  have hCount := mcspSquare_sample_bound 32 (by decide) c hc sample h₀ h₁
  rw [show descriptionBitBound 32 = 27672 by decide] at hCount
  unfold netMargin at h
  omega

/-- Counting each matched state at most once can give at most two units per wire. -/
theorem unit_per_state_budget (W : Finset (Wire n g)) (A : Finset (Wire n g × Bool))
    (hA : ∀ z ∈ A, z.1 ∈ W) : A.card ≤ 2 * W.card := by
  have hSub : A ⊆ W ×ˢ (Finset.univ : Finset Bool) := fun z hz =>
    Finset.mem_product.mpr ⟨hA z hz, Finset.mem_univ _⟩
  simpa [Finset.card_product, Nat.mul_comm] using Finset.card_le_card hSub

/-- Every corner-containing pool on a split-control circuit inside the verified size
budget has net charge at most 5122, even counting repeats on every source. -/
theorem splitControl32_margin_cap (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (hsize : c.size + 3071 ≤ 2 * 2 ^ 32)
    (sample : Finset (BitString (2 ^ 32))) (h₀ : (fun _ => false) ∈ sample)
    (h₁ : (fun _ => true) ∈ sample) : netMargin c.program (c.outputs 0) sample ≤ 5122 := by
  have lo (b : Bool) (hb : (fun _ => b) ∈ sample) :=
    SplitControl.railControl_inputStates_card 9 SplitControl.keep
      (fun u _ => SplitControl.has_other_retained u) c hc sample b hb
  have hFalse := lo false h₀
  have hTrue := lo true h₁
  rw [SplitControl.card_keep] at hFalse hTrue
  norm_num at hFalse hTrue
  rw [netMargin_eq]
  omega

/-- The same verified mask can have a wide non-certifying matching in a minimum
split-control circuit and still fall far short of the gate-charge threshold. -/
theorem splitControl32_noncertifying_charge_test :
    ∃ h : BooleanFunction 22, h ∉ badSelectors 9 22 ∧
      (∀ f g : RefinedCut.Coordinate → Bool,
        mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g) ∧
      (∀ f g : RefinedCut.Coordinate → Bool,
        SplitControl.railControl 9 SplitControl.keep
          (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g) ∧
      ∃ c : Circuit signature (2 ^ 32) 1,
        c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)) ∧
        c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep)) ∧
        (∃ choose : BitString 9 × Bool → Wire (2 ^ 32) c.size, Function.Injective choose ∧
          ∀ a, choose a ∈ MatchedSignals.varyingSources c.program
            (MatchedSignals.supportOwner c.program (mask 9 h)) (Downstream.railLabel 9 22) a ∧
            MatchedSignals.BothOutcomes c.program (SplitControl.railControl 9 SplitControl.keep) (choose a)) ∧
        ∀ (sample : Finset (BitString (2 ^ 32))) (_ : (fun _ => false) ∈ sample)
          (_ : (fun _ => true) ∈ sample) (W : Finset (Wire (2 ^ 32) c.size)),
          matchedMargin c.program (c.outputs 0) sample W ≤ 5122 := by
  obtain ⟨h, hh, hEq⟩ := RefinedCut.exists_refined_equality_cut
  obtain ⟨c, hc, hmin, hsize, _, _⟩ := SplitControl.minimum_wide_railControl_32
  exact ⟨h, hh, hEq, MatchedSignals.splitControl32_refined_equality hh,
    c, hc, hmin, MatchedSignals.splitControl32_noncertifying_matching hh c hc,
    fun sample h₀ h₁ W => (matchedMargin_le c.program (c.outputs 0) sample W).trans
      (splitControl32_margin_cap c hc hsize sample h₀ h₁)⟩

#print axioms square32_strict_of_matched_margin
#print axioms splitControl32_noncertifying_charge_test

end PvsNP.Frontier.MatchedCharge
