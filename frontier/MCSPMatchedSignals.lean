module

public import MCSPRefinedCut

/-! A cut whose matched signals genuinely vary and whose individual values do not decide MCSP. -/

@[expose] public section

namespace PvsNP.Frontier.MatchedSignals

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut

variable {n g : ℕ} {ι : Type*}

/-- Give a gate to the true side if any of its supporting inputs is on that side. -/
noncomputable def supportOwner (p : Program signature n g) (mask : BitString n) (w : Wire n g) :
    Bool := open scoped Classical in decide (∃ i ∈ p.wireSupport w, mask i = true)

theorem supportOwner_input (p : Program signature n g) (mask : BitString n) (i : Fin n) :
    supportOwner p mask (.input i) = mask i := by
  classical
  apply Bool.eq_iff_iff.mpr
  change decide (∃ j ∈ ({i} : Finset (Fin n)), mask j = true) = true ↔ _
  simp

theorem crossing_support_on_false_side (p : Program signature n g) (mask : BitString n)
    {w : Wire n g} (hw : w ∈ crossingWires p (supportOwner p mask)) :
    ∀ i ∈ p.wireSupport w, mask i = false := by
  classical
  obtain ⟨k, a, hsource, hne⟩ := (Finset.mem_filter.mp hw).2
  intro i hi
  cases hbit : mask i
  · rfl
  · have hfrom : supportOwner p mask w = true := decide_eq_true ⟨i, hi, hbit⟩
    have hdest : supportOwner p mask (.gate k) = true := by
      apply decide_eq_true
      refine ⟨i, ?_, hbit⟩
      change i ∈ p.trace (supportInterpretation signature n) (fun j => {j}) (.gate k)
      rw [p.trace_gate]
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hsource ▸ hi⟩
    exact (hne (hfrom.trans hdest.symm)).elim

/-- A probe signal actually depends on the indexed coordinate. -/
def ChangesAt (f : (ι → Bool) → Bool) (i : ι) : Prop :=
  ∃ x y : ι → Bool, (∀ j ≠ i, x j = y j) ∧ f x ≠ f y

private theorem equal_off_of_no_changes (f : (ι → Bool) → Bool) (J : Finset ι)
    (h : ∀ i ∈ J, ¬ChangesAt f i) {x y : ι → Bool} (hxy : ∀ i ∉ J, x i = y i) :
    f x = f y := by
  classical
  induction J using Finset.induction_on generalizing x with
  | empty =>
    have hEq : x = y := funext fun i => hxy i (by simp)
    rw [hEq]
  | @insert i S _ ih =>
    let z := Function.update x i (y i)
    have heq : f x = f z := by
      by_contra hn
      exact h i (Finset.mem_insert_self ..) ⟨x, z, fun j hj => by simp [z, Function.update_of_ne hj], hn⟩
    apply heq.trans
    apply ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [z]
    · simpa [z, Function.update_of_ne hji] using hxy j (by simp [hji, hj])

noncomputable def varyingSources (p : Program signature n g) (owner : Wire n g → Bool)
    (label : Fin n → ι) (a : ι) : Finset (Wire n g) := open scoped Classical in
  (crossingWires p owner).filter fun w => ChangesAt (fun x => p.trace interpretation (x ∘ label) w) a

theorem exists_varying_matching [Finite ι] (f : BooleanFunction n) (label : Fin n → ι)
    (selector : BitString n) (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (heq : ∀ a b : ι → Bool, f (splice selector (a ∘ label) (b ∘ label)) = true ↔ a = b)
    (owner : Wire n c.size → Bool) (howner : ∀ i, owner (.input i) = selector i) :
    ∃ choose : ι → Wire n c.size, Function.Injective choose ∧
      ∀ a, choose a ∈ varyingSources c.program owner label a := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp
  intro J
  let W := J.biUnion (varyingSources c.program owner label)
  let extend (a : J → Bool) (j : ι) := if hj : j ∈ J then a ⟨j, hj⟩ else false
  let send (a : J → Bool) (w : W) := c.program.trace interpretation (extend a ∘ label) w.val
  have hinj : Function.Injective send := by
    intro a b hsend
    have hagree (w : Wire n c.size) (hw : w ∈ crossingWires c.program owner) :
        c.program.trace interpretation (extend a ∘ label) w =
          c.program.trace interpretation (extend b ∘ label) w := by
      by_cases h : w ∈ W
      · exact congrFun hsend ⟨w, h⟩
      · apply equal_off_of_no_changes (fun x => c.program.trace interpretation (x ∘ label) w) J
        · intro i hi hchange
          exact h (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hw, hchange⟩⟩)
        · intro i hi
          simp [extend, hi]
    have hTrace := trace_splice_of_agree_crossing c.program owner selector
      (extend a ∘ label) (extend b ∘ label) howner hagree (c.outputs 0)
    have accept (d : J → Bool) : f (extend d ∘ label) = true := by
      simpa using (heq (extend d) (extend d)).mpr rfl
    have hMixed : f (splice selector (extend a ∘ label) (extend b ∘ label)) = true := by
      have heval := congrFun (hc (splice selector (extend a ∘ label) (extend b ∘ label))) 0
      change c.program.trace interpretation _ (c.outputs 0) = f _ at heval
      rw [← heval, hTrace]
      cases hside : owner (c.outputs 0)
      · exact (congrFun (hc _) 0).trans (accept b)
      · exact (congrFun (hc _) 0).trans (accept a)
    have h := (heq (extend a) (extend b)).mp hMixed
    funext j
    simpa [extend, j.property] using congrFun h j.val
  have hcard : 2 ^ J.card ≤ 2 ^ W.card := by
    simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using
      Fintype.card_le_of_injective send hinj
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hcard

def BothOutcomes (p : Program signature n g) (f : BooleanFunction n) (w : Wire n g) : Prop :=
  ∀ b d : Bool, ∃ x : BitString n, p.trace interpretation x w = b ∧ f x = d

/-- Both polarities of a matched one-sided signal occur on acceptance and on rejection. -/
theorem varying_source_has_both_outcomes (p : Program signature n g) (f : BooleanFunction n)
    (label : Fin n → ι) (mask : BitString n)
    (heq : ∀ a b : ι → Bool, f (splice mask (a ∘ label) (b ∘ label)) = true ↔ a = b)
    {w : Wire n g} {i : ι} (hw : w ∈ varyingSources p (supportOwner p mask) label i) :
    BothOutcomes p f w := by
  classical
  obtain ⟨hcross, a, b, _, hchange⟩ := Finset.mem_filter.mp hw
  have hne : a ≠ b := fun he => hchange (congrArg (fun t => p.trace interpretation (t ∘ label) w) he)
  have traceFalse (u v : ι → Bool) :
      p.trace interpretation (splice mask (u ∘ label) (v ∘ label)) w =
        p.trace interpretation (v ∘ label) w := by
    apply p.trace_congr interpretation
    intro j hj
    simp [splice, crossing_support_on_false_side p mask hcross j hj]
  intro polarity outcome
  have realize (u v : ι → Bool) (hn : u ≠ v)
      (hv : p.trace interpretation (v ∘ label) w = polarity) :
      ∃ x : BitString n, p.trace interpretation x w = polarity ∧ f x = outcome := by
    cases outcome
    · refine ⟨splice mask (u ∘ label) (v ∘ label), (traceFalse u v).trans hv, ?_⟩
      exact Bool.eq_false_of_not_eq_true (fun ht => hn ((heq u v).mp ht))
    · exact ⟨v ∘ label, hv, by simpa using (heq v v).mpr rfl⟩
  by_cases h : p.trace interpretation (a ∘ label) w = polarity
  · exact realize b a hne.symm h
  · apply realize a b hne
    cases ha : p.trace interpretation (a ∘ label) w <;>
      cases hb : p.trace interpretation (b ∘ label) w <;>
      cases polarity <;> simp_all

theorem exact_square32_noncertifying_matching :
    ∃ h : BooleanFunction 22, h ∉ badSelectors 9 22 ∧
      ∀ (c : Circuit signature (2 ^ 32) 1)
        (_ : c.Computes interpretation (single (mcspSquare 32))),
        ∃ choose : RefinedCut.Coordinate → Wire (2 ^ 32) c.size, Function.Injective choose ∧
          ∀ a, choose a ∈ varyingSources c.program (supportOwner c.program (mask 9 h)) RefinedCut.label a ∧
            BothOutcomes c.program (mcspSquare 32) (choose a) := by
  obtain ⟨h, hh, hEq⟩ := RefinedCut.exists_refined_equality_cut
  refine ⟨h, hh, fun c hc => ?_⟩
  obtain ⟨choose, hchoose, hw⟩ := exists_varying_matching _ RefinedCut.label (mask 9 h) c hc hEq
    (supportOwner c.program (mask 9 h)) (supportOwner_input c.program (mask 9 h))
  exact ⟨choose, hchoose, fun a => ⟨hw a, varying_source_has_both_outcomes _ _ _ _ hEq (hw a)⟩⟩

/-- Putting every gate on the true side yields a valid matching made entirely of input wires. -/
theorem exact_square32_input_only_matching :
    ∃ h : BooleanFunction 22, h ∉ badSelectors 9 22 ∧
      ∀ (c : Circuit signature (2 ^ 32) 1)
        (_ : c.Computes interpretation (single (mcspSquare 32))),
        ∃ choose : RefinedCut.Coordinate → Wire (2 ^ 32) c.size, Function.Injective choose ∧
          ∀ a, (∃ i, choose a = .input i) ∧ choose a ∈ varyingSources c.program
            (Wire.elim (mask 9 h) (fun _ => true)) RefinedCut.label a := by
  classical
  obtain ⟨h, hh, hEq⟩ := RefinedCut.exists_refined_equality_cut
  refine ⟨h, hh, fun c hc => ?_⟩
  let owner : Wire (2 ^ 32) c.size → Bool := Wire.elim (mask 9 h) (fun _ => true)
  obtain ⟨choose, hinj, hw⟩ := exists_varying_matching _ RefinedCut.label (mask 9 h) c hc hEq
    owner (fun _ => rfl)
  refine ⟨choose, hinj, fun a => ⟨?_, hw a⟩⟩
  obtain ⟨k, j, _, hcross⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp (hw a)).1).2
  cases he : choose a with
  | input i => exact ⟨i, rfl⟩
  | gate i => exact (hcross (by rw [he]; rfl)).elim

theorem splitControl32_noncertifying_matching {h : BooleanFunction 22} (hh : h ∉ badSelectors 9 22)
    (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep))) :
    ∃ choose : BitString 9 × Bool → Wire (2 ^ 32) c.size, Function.Injective choose ∧
      ∀ a, choose a ∈ varyingSources c.program (supportOwner c.program (mask 9 h))
        (Downstream.railLabel 9 22) a ∧
          BothOutcomes c.program (SplitControl.railControl 9 SplitControl.keep) (choose a) := by
  have hEq := Downstream.splitControl_equality_by_rail (r := 9) SplitControl.keep h
    (SplitControl.good_selector_varies hh)
  obtain ⟨choose, hchoose, hw⟩ := exists_varying_matching _ (Downstream.railLabel 9 22) (mask 9 h)
    c hc hEq (supportOwner c.program (mask 9 h)) (supportOwner_input c.program (mask 9 h))
  exact ⟨choose, hchoose, fun a => ⟨hw a, varying_source_has_both_outcomes _ _ _ _ hEq (hw a)⟩⟩

/-- The split control also realizes the very same probes used by the exact 544-wire cut. -/
theorem splitControl32_refined_equality {h : BooleanFunction 22} (hh : h ∉ badSelectors 9 22)
    (f g : RefinedCut.Coordinate → Bool) :
    SplitControl.railControl 9 SplitControl.keep
      (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g := by
  let lift (z : RefinedCut.Coordinate → Bool) (p : BitString 9 × Bool) := z (RefinedCut.pick p.1 p.2)
  have hLift (z : RefinedCut.Coordinate → Bool) : z ∘ RefinedCut.label = lift z ∘ Downstream.railLabel 9 22 := rfl
  rw [hLift f, hLift g, Downstream.splitControl_equality_by_rail _ _ (SplitControl.good_selector_varies hh)]
  constructor
  · intro hEq
    funext q
    obtain ⟨p, hp⟩ := RefinedCut.pick_surjective q
    change RefinedCut.pick p.1 p.2 = q at hp
    have h := congrFun hEq p
    change f (RefinedCut.pick p.1 p.2) = g (RefinedCut.pick p.1 p.2) at h
    rwa [hp] at h
  · rintro rfl
    rfl

#print axioms exact_square32_noncertifying_matching
#print axioms exact_square32_input_only_matching
#print axioms splitControl32_noncertifying_matching
#print axioms splitControl32_refined_equality

end PvsNP.Frontier.MatchedSignals
