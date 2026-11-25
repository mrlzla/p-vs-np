module

public import MCSPQuarterLive
public import MCSPMinimumAliasControl

/-! A closed fresh region can be charged as dead. Minimum size and sparsity
alone permit an empty such region, even with two opposite accepted corners. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterDeadFrontier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open QuarterBlock FreshCharges RestrictionCharges
open CornerCertificates TwoCornerStructure MonotoneForest

variable {n k g : ℕ}

/-- A proposed region of fresh indices is dead when the output and every
fresh reader outside the region use representatives outside it. -/
theorem closed_region_subset_dead (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g) (S : Finset (Fin g))
    (hFresh : S ⊆ fresh p ρ)
    (hOutput : ∀ j ∈ S, ¬ Represents p ρ root j)
    (hBoundary : ∀ j ∈ fresh p ρ, j ∉ S →
      ∀ (a : Fin (signature.Arity (p.lines j).op)) t, t ∈ S →
        ¬ Represents p ρ ((p.lines j).wires a) t) :
    S ⊆ deadFresh p ρ root := by
  have hOutside {j : Fin g} (hj : ResidualLive p ρ root j) : j ∉ S := by
    induction hj with
    | output h => exact fun hm => hOutput _ hm h
    | argument hLive a hRep ih =>
      exact fun hm => hBoundary _ (residualLive_mem_fresh hLive) ih a _ hm hRep
  intro j hj
  exact Finset.mem_sdiff.mpr ⟨hFresh hj, fun hl => (hOutside (mem_liveFresh_iff.mp hl)) hj⟩

/-- The actual dead set satisfies the same separation condition, so the
closed-region test characterizes the largest eligible set. -/
theorem dead_region_closed (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g) :
    let S := deadFresh p ρ root
    (∀ j ∈ S, ¬ Represents p ρ root j) ∧
    (∀ j ∈ fresh p ρ, j ∉ S →
      ∀ (a : Fin (signature.Arity (p.lines j).op)) t, t ∈ S →
        ¬ Represents p ρ ((p.lines j).wires a) t) := by
  dsimp only
  classical
  constructor
  · intro j hj hRep
    exact (Finset.mem_sdiff.mp hj).2 (mem_liveFresh_iff.mpr (ResidualLive.output hRep))
  · intro j hj hn a t ht hRep
    have hLive : j ∈ liveFresh p ρ root := by
      by_contra h
      exact hn (Finset.mem_sdiff.mpr ⟨hj, h⟩)
    have hT := ResidualLive.argument (mem_liveFresh_iff.mp hLive) a hRep
    exact (Finset.mem_sdiff.mp ht).2 (mem_liveFresh_iff.mpr hT)

/-- Both controls fail the dead-only target even if they are given their
entire certified allowance of fresh but dead gates. -/
theorem split_dead_below_target (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (hMin : c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep))) :
    (deadFresh c.program (quarterSub 30) (c.outputs 0)).card < 1074343145 :=
  lt_of_le_of_lt (split_quarter_dead_upper_32 c hc hMin) (by decide)

theorem invariant_dead_below_target (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (InvariantControl.control 9 22)))
    (hMin : c.size = complexity interpretation (single (InvariantControl.control 9 22))) :
    (deadFresh c.program (quarterSub 30) (c.outputs 0)).card < 1074343145 :=
  lt_of_le_of_lt (invariant_quarter_dead_upper_32 c hc hMin) (by decide)

/-- A closed region this large would close the gap in the exact-MCSP
quarter calculation. -/
theorem exact_mcsp_closed_region_target (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (S : Finset (Fin c.size))
    (hSize : 1074343145 ≤ S.card)
    (hFresh : S ⊆ fresh c.program (quarterSub 30))
    (hOutput : ∀ j ∈ S, ¬ Represents c.program (quarterSub 30) (c.outputs 0) j)
    (hBoundary : ∀ j ∈ fresh c.program (quarterSub 30), j ∉ S →
      ∀ (a : Fin (signature.Arity (c.program.lines j).op)) t, t ∈ S →
        ¬ Represents c.program (quarterSub 30) ((c.program.lines j).wires a) t) :
    8592176574 ≤ c.size :=
  QuarterLive.mcsp_quarter_dead_threshold_32 c hc
    (hSize.trans (Finset.card_le_card
      (closed_region_subset_dead c.program (quarterSub 30) (c.outputs 0) S hFresh hOutput hBoundary)))

/-! A minimum sparse control with no fresh but dead gates under the pin. -/

/-- If both constant tables are accepted and flipping any individual entry
of either corner rejects, the original corner ledger charges at least 2n
gates. The output gate itself lies in the stop set, so slack is positive. -/
theorem opposite_corners_all_pivotal_lower {f : BooleanFunction n}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hCorner : ∀ b : Bool, f (fun _ => b) = true)
    (hPivot : ∀ (b : Bool) (i : Fin n),
      f (Function.update (fun _ => b) i (!b)) = false) :
    2 * n ≤ c.size := by
  classical
  let p := c.program
  let root := c.outputs 0
  have hRoot (b : Bool) : cornerValue p b root = true := (congrFun (hc _) 0).trans (hCorner b)
  have hNeed (b : Bool) : needInputs p root b = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    have ha : ∀ j ∈ needInputs p root b, Function.update (fun _ => b) i (!b) j = b := by
      intro j hj
      have hn : j ≠ i := fun he => hi (he ▸ hj)
      exact Function.update_of_ne hn _ _
    have hh := agrees_on_needCorner p root b (hRoot b) (Function.update (fun _ => b) i (!b)) ha
    have hEq := congrFun (hc (Function.update (fun _ => b) i (!b))) 0
    exact Bool.noConfusion ((hPivot b i).symm.trans (hEq.symm.trans hh))
  have hLedger := needInputs_add_slack_eq p root (hRoot false) (hRoot true)
  rw [hNeed false, hNeed true, Finset.card_univ, Fintype.card_fin] at hLedger
  have hSlack : 1 ≤ slack p root := by
    cases hr : root with
    | input i =>
      have h := hRoot false
      rw [hr, cornerValue_input] at h
      cases h
    | gate j =>
      have hStop : j ∈ StopGate p root := by
        by_contra h
        have hNo := not_s0_s1_of_not_badFlip
          (not_badFlip_of_not_cutGate (fun hb => h (cutGate_subset_stopGate _ _ hb)))
        exact hNo.2.1 (hr ▸ NeedCorner.output)
      have hPos := Finset.card_pos.mpr ⟨j, hStop⟩
      have h := card_stopGate_le_56_slack p root (hRoot false) (hRoot true)
      change 1 ≤ slack p (.gate j)
      rw [← hr]
      omega
  omega

def chainedProgram : Program signature 4 8 :=
  let p0 : Program signature 4 0 := .empty
  let p1 := p0.gate ⟨.or, fun a => if a = 0 then .input 0 else .input 1⟩
  let p2 := p1.gate ⟨.or, fun a => if a = 0 then .gate 0 else .input 2⟩
  let p3 := p2.gate ⟨.or, fun a => if a = 0 then .gate 1 else .input 3⟩
  let p4 := p3.gate ⟨.and, fun a => if a = 0 then .input 0 else .input 1⟩
  let p5 := p4.gate ⟨.and, fun a => if a = 0 then .gate 3 else .input 2⟩
  let p6 := p5.gate ⟨.and, fun a => if a = 0 then .gate 4 else .input 3⟩
  let p7 := p6.gate ⟨.not, fun _ => .gate 2⟩
  p7.gate ⟨.or, fun a => if a = 0 then .gate 6 else .gate 5⟩

def chainedCircuit : Circuit signature 4 1 := ⟨chainedProgram, fun _ => .gate 7⟩

def allEqual4 (x : BitString 4) : Bool :=
  (!((x 0 || x 1) || x 2 || x 3)) || ((x 0 && x 1) && x 2 && x 3)

theorem chained_computes : chainedCircuit.Computes interpretation (single allEqual4) := by
  intro x
  rfl

theorem chained_minimum : chainedCircuit.size = complexity interpretation (single allEqual4) := by
  apply le_antisymm _ (complexity_le_of_computes chainedCircuit chained_computes)
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single allEqual4)
  rw [← hSize]
  change 2 * 4 ≤ c.size
  exact opposite_corners_all_pivotal_lower c hc
    (fun b => by cases b <;> decide) (fun b i => by cases b <;> fin_cases i <;> decide)

theorem chained_accepting_count :
    (acceptingTables allEqual4).card = 2 := by
  decide

private theorem kept0 : keptKey 0 (0 : Fin 4) = false := by decide

private theorem pinned_read (y : BitString (3 * 2 ^ 0)) :
    substitute (quarterSub 0) y (0 : Fin 4) = false := by
  simp [substitute, quarterSub, kept0]

private noncomputable def slot (i : Fin 3) : Fin (3 * 2 ^ 0) :=
  (freeEquiv 0).symm ⟨i.succ, by fin_cases i <;> decide⟩

private theorem slot_injective : Function.Injective slot := by
  intro i j h
  have he : i.succ = j.succ := congrArg Subtype.val ((freeEquiv 0).symm.injective h)
  exact Fin.succ_injective _ he

private theorem read_slot (y : BitString (3 * 2 ^ 0)) (i : Fin 3) :
    substitute (quarterSub 0) y i.succ = y (slot i) := by
  have hi : keptKey 0 i.succ = true := by fin_cases i <;> decide
  simp [substitute, quarterSub, hi, slot]

set_option maxHeartbeats 800000 in
private theorem gate0_projection :
    restrictedWire chainedProgram (quarterSub 0) (.gate 0) = projection (slot 0) := by
  funext y
  change (substitute (quarterSub 0) y 0 || substitute (quarterSub 0) y 1) = y (slot 0)
  rw [pinned_read, show (1 : Fin 4) = (0 : Fin 3).succ by decide, read_slot]
  rfl

private theorem gate3_constant :
    restrictedWire chainedProgram (quarterSub 0) (.gate 3) = fun _ => false := by
  funext y
  change (substitute (quarterSub 0) y 0 && substitute (quarterSub 0) y 1) = false
  rw [pinned_read]
  rfl

private theorem gate4_constant :
    restrictedWire chainedProgram (quarterSub 0) (.gate 4) = fun _ => false := by
  funext y
  change (restrictedWire chainedProgram (quarterSub 0) (.gate 3) y &&
    substitute (quarterSub 0) y 2) = false
  rw [gate3_constant]
  rfl

private theorem gate5_constant :
    restrictedWire chainedProgram (quarterSub 0) (.gate 5) = fun _ => false := by
  funext y
  change (restrictedWire chainedProgram (quarterSub 0) (.gate 4) y &&
    substitute (quarterSub 0) y 3) = false
  rw [gate4_constant]
  rfl

private theorem gate7_alias :
    restrictedWire chainedProgram (quarterSub 0) (.gate 7) =
      restrictedWire chainedProgram (quarterSub 0) (.gate 6) := by
  funext y
  change (restrictedWire chainedProgram (quarterSub 0) (.gate 6) y ||
    restrictedWire chainedProgram (quarterSub 0) (.gate 5) y) = _
  rw [gate5_constant, Bool.or_false]

private theorem chained_fresh_upper :
    (fresh chainedProgram (quarterSub 0)).card ≤ 3 := by
  classical
  have hSub : fresh chainedProgram (quarterSub 0) ⊆ ({1, 2, 6} : Finset (Fin 8)) := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    fin_cases j
    · exact (h (Or.inr (Or.inl ⟨_, gate0_projection⟩))).elim
    · decide
    · decide
    · exact (h (Or.inl ⟨false, gate3_constant⟩)).elim
    · exact (h (Or.inl ⟨false, gate4_constant⟩)).elim
    · exact (h (Or.inl ⟨false, gate5_constant⟩)).elim
    · decide
    · exact (h (Or.inr (Or.inr ⟨6, by decide, gate7_alias⟩))).elim
  exact (Finset.card_le_card hSub).trans (by decide)

private noncomputable def norResidual (y : BitString (3 * 2 ^ 0)) : Bool :=
  !((y (slot 0) || y (slot 1)) || y (slot 2))

private theorem chained_residual :
    restrictedWire chainedProgram (quarterSub 0) (.gate 7) = norResidual := by
  rw [gate7_alias]
  funext y
  change (!((substitute (quarterSub 0) y 0 || substitute (quarterSub 0) y 1) ||
    substitute (quarterSub 0) y 2 || substitute (quarterSub 0) y 3)) = norResidual y
  rw [pinned_read]
  have h1 : (1 : Fin 4) = (0 : Fin 3).succ := by decide
  have h2 : (2 : Fin 4) = (1 : Fin 3).succ := by decide
  have h3 : (3 : Fin 4) = (2 : Fin 3).succ := by decide
  rw [h1, h2, h3, read_slot, read_slot, read_slot]
  rfl

private theorem norResidual_lower :
    3 ≤ complexity interpretation (single norResidual) := by
  classical
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single norResidual)
  rw [← hSize]
  apply MinimumAliasControl.nonmonotone_full_support_lower c hc
  · intro i
    obtain ⟨j, rfl⟩ := (Finite.surjective_of_injective slot_injective) i
    refine ⟨fun _ => false, Function.update (fun _ => false) (slot j) true,
      ?_, ?_⟩
    · intro k hk
      change false = Function.update (fun _ : Fin (3 * 2 ^ 0) => false) (slot j) true k
      rw [Function.update_of_ne hk]
    · have h (a : Fin 3) :
          Function.update (fun _ => false) (slot j) true (slot a) = decide (a = j) := by
        by_cases he : a = j
        · subst a; simp
        · simp [Function.update_of_ne (fun h => he (slot_injective h)) _ _, he]
      unfold norResidual
      simp only [h]
      fin_cases j <;> decide
  · intro h
    have hle : (fun _ : Fin (3 * 2 ^ 0) => false) ≤ fun _ => true := by
      intro i
      change (false : Bool) ≤ true
      decide
    have hn := h hle
    change (true : Bool) ≤ false at hn
    exact (by decide : ¬ (true : Bool) ≤ false) hn

/-- A minimum circuit with sparse acceptance and both corners can leave
zero fresh but dead gates under the exact same leading-zero restriction. -/
theorem chained_zero_dead :
    (deadFresh chainedProgram (quarterSub 0) (.gate 7)).card = 0 := by
  have hNon : ¬∃ b : Bool, restrictedWire chainedProgram (quarterSub 0) (.gate 7) = fun _ => b := by
    rw [chained_residual]
    rintro ⟨b, hb⟩
    have h0 := congrFun hb (fun _ => false)
    have h1 := congrFun hb (fun _ => true)
    change true = b at h0
    change false = b at h1
    cases h0.trans h1.symm
  have hCost := live_fresh_complexity_le chainedProgram (quarterSub 0) (.gate 7) hNon
  rw [chained_residual] at hCost
  have hPart := Finset.card_sdiff_add_card_eq_card
    (liveFresh_subset_fresh chainedProgram (quarterSub 0) (.gate 7))
  change (deadFresh chainedProgram (quarterSub 0) (.gate 7)).card +
    (liveFresh chainedProgram (quarterSub 0) (.gate 7)).card =
    (fresh chainedProgram (quarterSub 0)).card at hPart
  have hF := chained_fresh_upper
  have hR := norResidual_lower
  omega

#print axioms closed_region_subset_dead
#print axioms dead_region_closed
#print axioms split_dead_below_target
#print axioms invariant_dead_below_target
#print axioms exact_mcsp_closed_region_target
#print axioms opposite_corners_all_pivotal_lower
#print axioms chained_accepting_count
#print axioms chained_minimum
#print axioms chained_zero_dead

end PvsNP.Frontier.QuarterDeadFrontier
