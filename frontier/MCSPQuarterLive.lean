module

public import MCSPQuarterProbes

/-! Count fresh but dead gates after the quarter restriction, separately from
semantic losses, and apply the same budget to exact MCSP and the controls. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterLive

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open QuarterBlock QuarterProbes FreshCharges RestrictionCharges

variable {n : ℕ}

/-- A minimum circuit for a nonconstant function has every original gate
fresh and live before pinning. Its new dead set cannot count old dead code. -/
theorem minimum_full_cone (c : Circuit signature n 1) {f : BooleanFunction n}
    (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (hNon : ¬∃ b : Bool, f = fun _ => b) :
    liveFresh c.program (Sum.inl : Fin n → Fin n ⊕ Bool) (c.outputs 0) = Finset.univ := by
  let ρ : Fin n → Fin n ⊕ Bool := Sum.inl
  have he : restrictedWire c.program ρ (c.outputs 0) = f :=
    NestedFaces.restricted_circuit_eq c hc ρ
  have h := live_fresh_complexity_le c.program ρ (c.outputs 0) (by rwa [he])
  rw [he, ← hMin] at h
  apply Finset.eq_univ_of_card
  simpa only [Fintype.card_fin] using le_antisymm
    (by simpa using Finset.card_le_univ (liveFresh c.program ρ (c.outputs 0))) h

/-- Add the dead fresh gates to the old quarter-block estimate, once each. -/
theorem mcsp_quarter_plus_dead_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    7517833429 + (deadFresh c.program (quarterSub 30) (c.outputs 0)).card ≤ c.size := by
  have h0 : residual 30 (mcspSquare 32) (fun _ => false) = true := by
    change mcspSquare 32 (fill 30 (fun _ => false)) = true
    rw [fill_zero]
    exact mcspSquare_constant_table 32 (by decide) false
  have hBudget := quarter_live_budget 30 c hc (card_accepting_mcspSquare_le 32) (by decide) h0
  have hR := mcsp_quarter_residual_32
  have hSub : nextFreshLoss c.program (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool)
      (quarterSub 30) ⊆ firstFreshLoss c.program (quarterSub 30) := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hj).2⟩
  have hLoss := (rich_quarter_fresh_losses_32 c hc).trans (Finset.card_le_card hSub)
  omega

theorem mcsp_quarter_dead_threshold_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hDead : 1074343145 ≤ (deadFresh c.program (quarterSub 30) (c.outputs 0)).card) :
    8592176574 ≤ c.size := by
  have h := mcsp_quarter_plus_dead_32 c hc
  omega

/- A genuinely new dead index on a concrete leading-00 quarter. -/

def toyProgram : Program signature 4 3 :=
  let p0 : Program signature 4 0 := .empty
  let p1 := p0.gate ⟨.or, fun a => if a = 0 then .input 1 else .input 2⟩
  let p2 := p1.gate ⟨.and, fun a => if a = 0 then .input 0 else .gate 0⟩
  p2.gate ⟨.or, fun a => if a = 0 then .gate 1 else .input 3⟩

def toyRoot : Wire 4 3 := .gate 2

private theorem test_kept_0 : keptKey 0 (0 : Fin 4) = false := by decide
private theorem test_kept_1 : keptKey 0 (1 : Fin 4) = true := by decide
private theorem test_kept_2 : keptKey 0 (2 : Fin 4) = true := by decide
private theorem test_kept_3 : keptKey 0 (3 : Fin 4) = true := by decide

private noncomputable def testSlot (i : Fin 4) (hi : keptKey 0 i = true) :
    Fin (3 * 2 ^ 0) := (freeEquiv 0).symm ⟨i, hi⟩

private theorem testSlot_ne : testSlot 1 test_kept_1 ≠ testSlot 2 test_kept_2 := by
  intro h
  have he : (1 : Fin 4) = 2 := congrArg Subtype.val ((freeEquiv 0).symm.injective h)
  exact (by decide : ¬ (1 : Fin 4) = 2) he

private theorem test_at_kept (x : BitString (3 * 2 ^ 0)) (i : Fin 4) (hi : keptKey 0 i = true) :
    substitute (quarterSub 0) x i = x (testSlot i hi) := by
  simp [quarterSub, substitute, hi, testSlot]

private theorem test_at_pinned (x : BitString (3 * 2 ^ 0)) :
    substitute (quarterSub 0) x 0 = false := by
  simp [quarterSub, substitute, test_kept_0]

private theorem test_gate_zero (x : BitString (3 * 2 ^ 0)) :
    restrictedWire toyProgram (quarterSub 0) (.gate 0) x =
      (x (testSlot 1 test_kept_1) || x (testSlot 2 test_kept_2)) := by
  change (substitute (quarterSub 0) x 1 || substitute (quarterSub 0) x 2) = _
  rw [test_at_kept x 1 test_kept_1, test_at_kept x 2 test_kept_2]

private theorem test_gate_one :
    restrictedWire toyProgram (quarterSub 0) (.gate 1) = fun _ => false := by
  funext x
  change (substitute (quarterSub 0) x 0 &&
    (substitute (quarterSub 0) x 1 || substitute (quarterSub 0) x 2)) = false
  rw [test_at_pinned]
  rfl

private theorem test_output :
    restrictedWire toyProgram (quarterSub 0) toyRoot = projection (testSlot 3 test_kept_3) := by
  funext x
  change (restrictedWire toyProgram (quarterSub 0) (.gate 1) x ||
      substitute (quarterSub 0) x 3) = x (testSlot 3 test_kept_3)
  rw [test_gate_one, test_at_kept x 3 test_kept_3]
  rfl

private theorem test_zero_is_fresh : (0 : Fin 3) ∈ fresh toyProgram (quarterSub 0) := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, ht, _⟩)
  · have h0 := congrFun hb (fun _ => false)
    have h1 := congrFun hb (fun _ => true)
    rw [test_gate_zero] at h0 h1
    exact (by decide : ¬ (false : Bool) = true) (h0.trans h1.symm)
  · have ha := congrFun hi (fun j => decide (j = testSlot 1 test_kept_1))
    have hb := congrFun hi (fun j => decide (j = testSlot 2 test_kept_2))
    rw [test_gate_zero] at ha hb
    have ha' : i = testSlot 1 test_kept_1 := by
      simpa [projection] using ha.symm
    have hb' : i = testSlot 2 test_kept_2 := by
      simpa [projection, Bool.or_comm] using hb.symm
    exact testSlot_ne (ha'.symm.trans hb')
  · exact (by omega : ¬ t < (0 : Fin 3)) ht

private theorem toy_fresh_set : fresh toyProgram (quarterSub 0) = {(0 : Fin 3)} := by
  classical
  ext j
  constructor
  · intro hj
    fin_cases j
    · exact Finset.mem_singleton_self _
    · exact ((Finset.mem_filter.mp hj).2 (Or.inl ⟨false, test_gate_one⟩)).elim
    · exact ((Finset.mem_filter.mp hj).2 (Or.inr (Or.inl ⟨_, test_output⟩))).elim
  · intro hj
    rw [Finset.mem_singleton.mp hj]
    exact test_zero_is_fresh

/-- On a four-entry control, the OR stays fresh after fixing the first
quarter to zero. The output is a projection, so that OR is now dead. -/
theorem toy_quarter_dead_count :
    (deadFresh toyProgram (quarterSub 0) toyRoot).card = 1 := by
  rw [deadFresh, liveFresh_empty_of_projection toyProgram (quarterSub 0) toyRoot test_output,
    Finset.sdiff_empty, toy_fresh_set, Finset.card_singleton]

def toyCircuit : Circuit signature 4 1 := ⟨toyProgram, fun _ => toyRoot⟩

def toyFunction (x : BitString 4) : Bool := (x 0 && (x 1 || x 2)) || x 3

private theorem toy_computes : toyCircuit.Computes interpretation (single toyFunction) := by
  intro x
  rfl

private theorem toy_essential : ∀ i : Fin 4, EssentialAt toyFunction i := by
  intro i
  fin_cases i
  · let u : BitString 4 := fun j => decide (j = 1)
    exact ⟨u, Function.update u 0 true, fun _ hn => (Function.update_of_ne hn _ _).symm, by decide⟩
  · let u : BitString 4 := fun j => decide (j = 0)
    exact ⟨u, Function.update u 1 true, fun _ hn => (Function.update_of_ne hn _ _).symm, by decide⟩
  · let u : BitString 4 := fun j => decide (j = 0)
    exact ⟨u, Function.update u 2 true, fun _ hn => (Function.update_of_ne hn _ _).symm, by decide⟩
  · let u : BitString 4 := fun _ => false
    exact ⟨u, Function.update u 3 true, fun _ hn => (Function.update_of_ne hn _ _).symm, by decide⟩

theorem toy_minimum : toyCircuit.size = complexity interpretation (single toyFunction) := by
  classical
  apply le_antisymm _ (complexity_le_of_computes toyCircuit toy_computes)
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single toyFunction)
  have hAll : WireAccounting.inputs c.program (c.outputs 0) = Finset.univ := by
    exact Finset.eq_univ_of_forall fun i => WireAccounting.essential_mem_inputs hc (toy_essential i)
  have h := WireAccounting.inputs_add_charges_le c.program (c.outputs 0)
  rw [hAll, Finset.card_univ, Fintype.card_fin] at h
  change 3 ≤ complexity interpretation (single toyFunction)
  omega

/-- All three gates originally feed the output in this minimum control.
After the pin, two become redundant by equality and the third is fresh
but dead. -/
theorem toy_quarter_counts :
    (liveFresh toyProgram (Sum.inl : Fin 4 → Fin 4 ⊕ Bool) toyRoot).card = 3 ∧
    (firstFreshLoss toyProgram (quarterSub 0)).card = 2 ∧
    (deadFresh toyProgram (quarterSub 0) toyRoot).card = 1 := by
  have hNon : ¬∃ b : Bool, toyFunction = fun _ => b := by
    rintro ⟨b, hb⟩
    have h0 := congrFun hb (fun _ => false)
    have h1 := congrFun hb (fun _ => true)
    change false = b at h0
    change true = b at h1
    cases h0.trans h1.symm
  have hL := minimum_full_cone toyCircuit toy_computes toy_minimum hNon
  change liveFresh toyProgram (Sum.inl : Fin 4 → Fin 4 ⊕ Bool) toyRoot = Finset.univ at hL
  refine ⟨by rw [hL, Finset.card_univ, Fintype.card_fin], ?_, toy_quarter_dead_count⟩
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (fresh toyProgram (quarterSub 0)))
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  change (firstFreshLoss toyProgram (quarterSub 0)).card +
    (fresh toyProgram (quarterSub 0)).card = 3 at hSplit
  rw [toy_fresh_set, Finset.card_singleton] at hSplit
  omega

#print axioms minimum_full_cone
#print axioms mcsp_quarter_plus_dead_32
#print axioms mcsp_quarter_dead_threshold_32
#print axioms toy_quarter_counts

end PvsNP.Frontier.QuarterLive
