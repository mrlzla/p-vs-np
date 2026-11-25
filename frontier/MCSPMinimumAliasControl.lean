module

public import MCSPMinimumAliases

/-! A minimum two-corner circuit with a stop-gate alias after the forest pins. -/

@[expose] public section

namespace PvsNP.Frontier.MinimumAliasControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN
open ForestPinning RestrictionCharges FreshCharges StopMatching

variable {n : ℕ}

private theorem monotone_op (op : Op) (hNot : op ≠ .not)
    {u v : Fin (signature.Arity op) → Bool} (h : ∀ i, u i ≤ v i) :
    interpretation op u ≤ interpretation op v := by
  cases op with
  | const b => exact le_rfl
  | not => exact (hNot rfl).elim
  | and =>
    have h0 := h 0
    have h1 := h 1
    cases hu0 : u 0 <;> cases hu1 : u 1 <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;>
      simp_all [interpretation]
  | or =>
    have h0 := h 0
    have h1 := h 1
    cases hu0 : u 0 <;> cases hu1 : u 1 <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;>
      simp_all [interpretation]

/-- All essential inputs cost at least n-1 binary gates, and a nonmonotone
output needs at least one live NOT. -/
theorem nonmonotone_full_support_lower (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hEss : ∀ i, EssentialAt f i) (hNon : ¬ Monotone f) : n ≤ c.size := by
  classical
  let p := c.program
  let root := c.outputs 0
  have hRead : WireAccounting.inputs p root = Finset.univ := by
    ext i
    exact ⟨fun _ => Finset.mem_univ _, fun _ => WireAccounting.essential_mem_inputs hc (hEss i)⟩
  have hLiveNot : ∃ j ∈ WireAccounting.gates p root, (p.lines j).op = .not := by
    by_contra h
    apply hNon
    intro x y hxy
    have hTrace (w : Wire n c.size) : WireAccounting.Live p root w →
        p.trace interpretation x w ≤ p.trace interpretation y w := by
      refine p.wire_induction (P := fun w => WireAccounting.Live p root w →
        p.trace interpretation x w ≤ p.trace interpretation y w) ?_ ?_ w
      · intro i _
        exact hxy i
      · intro j ih hj
        rw [p.trace_gate, p.trace_gate]
        apply monotone_op (p.lines j).op (fun hop =>
          h ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hop⟩)
        intro a
        exact ih a (WireAccounting.Live.argument hj a)
    have he := hTrace root WireAccounting.Live.output
    change c.eval interpretation x 0 ≤ c.eval interpretation y 0 at he
    rwa [hc x, hc y] at he
  obtain ⟨j, hj, hop⟩ := hLiveNot
  let G := WireAccounting.gates p root
  have hSum : ∑ k ∈ G, signature.Arity (p.lines k).op < 2 * G.card := by
    have hOther : ∑ k ∈ G.erase j, signature.Arity (p.lines k).op ≤ 2 * (G.erase j).card := by
      calc
        _ ≤ ∑ _k ∈ G.erase j, 2 := Finset.sum_le_sum fun k _ =>
          Program.fanInAtMost_iff.mp p.fanInAtMost_two k
        _ = _ := by simp [Nat.mul_comm]
    have hSplit := Finset.sum_erase_add G (fun k => signature.Arity (p.lines k).op) hj
    rw [hop, show signature.Arity Op.not = 1 by rfl] at hSplit
    have hGpos : 0 < G.card := Finset.card_pos.mpr ⟨j, hj⟩
    rw [Finset.card_erase_of_mem hj] at hOther
    dsimp only [G] at hOther hGpos hSplit ⊢
    omega
  have hMissing : 0 < WireAccounting.missingPins p root := by
    unfold WireAccounting.missingPins WireAccounting.pins
    rw [Finset.card_sigma]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_pos_of_lt hSum
  have hAcct := WireAccounting.inputs_add_charges_le p root
  rw [hRead, Finset.card_univ, Fintype.card_fin] at hAcct
  omega

def program : Program signature 4 4 :=
  let p0 : Program signature 4 0 := .empty
  let p1 := p0.gate ⟨.or, fun a => if a = 0 then .input 0 else .input 1⟩
  let p2 := p1.gate ⟨.and, fun a => if a = 0 then .input 2 else .gate 0⟩
  let p3 := p2.gate ⟨.not, fun _ => .gate 1⟩
  p3.gate ⟨.or, fun a => if a = 0 then .gate 2 else .input 3⟩

def circuit : Circuit signature 4 1 := ⟨program, fun _ => .gate 3⟩

def decision (x : BitString 4) : Bool := (!(x 2 && (x 0 || x 1))) || x 3

theorem computes : circuit.Computes interpretation (single decision) := by
  intro x
  rfl

theorem minimum : circuit.size = complexity interpretation (single decision) := by
  apply le_antisymm _ (complexity_le_of_computes circuit computes)
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single decision)
  rw [← hsize]
  change 4 ≤ c.size
  apply nonmonotone_full_support_lower c hc
  · intro i
    fin_cases i
    · let x : BitString 4 := fun j => decide (j = 2)
      exact ⟨x, Function.update x 0 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 4 := fun j => decide (j = 2)
      exact ⟨x, Function.update x 1 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 4 := fun j => decide (j = 0)
      exact ⟨x, Function.update x 2 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 4 := fun j => decide (j = 0 ∨ j = 2)
      exact ⟨x, Function.update x 3 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
  · intro h
    let x : BitString 4 := fun j => decide (j = 2)
    let y := Function.update x 0 true
    have hxy : x ≤ y := by decide
    have hFalse : ¬ decision x ≤ decision y := by decide
    exact hFalse (h hxy)

private def allowed (b : Bool) : Wire 4 4 → Prop
  | .input _ => True
  | .gate k => if b then k = 3 else k ≠ 0

private instance (b : Bool) (w : Wire 4 4) : Decidable (allowed b w) := by
  cases w <;> unfold allowed <;> split <;> infer_instance

private theorem allowed_corner (b : Bool) {key : Wire 4 4 × Bool}
    (h : NeedCorner program (.gate 3) b key) : allowed b key.1 := by
  have hStep : ∀ (b : Bool) (k : Fin 4) (key : Wire 4 4 × Bool),
      allowed b (.gate k) → key ∈ cornerArguments program k b → allowed b key.1 := by decide
  induction h with
  | output => cases b <;> decide
  | @argument k h key ha ih => exact hStep b k key ih ha

private theorem stop_zero : (0 : Fin 4) ∈ StopGate program (.gate 3) := by
  classical
  have h0 (v : Bool) : ¬ NeedCorner program (.gate 3) false (.gate 0, v) := fun h =>
    (by decide : ¬ allowed false (.gate 0)) (allowed_corner false h)
  have h1 (v : Bool) : ¬ NeedCorner program (.gate 3) true (.gate 0, v) := fun h =>
    (by decide : ¬ allowed true (.gate 0)) (allowed_corner true h)
  have hReq : req program (.gate 3) 0 = ∅ := by simp [req, reqCorner, h0, h1]
  have hBad : (0 : Fin 4) ∈ badGates program (.gate 3) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp [unused, hReq]⟩
  exact cutGate_subset_stopGate _ _ (by
    by_contra h
    exact (not_badGates_of_not_cutGate h) hBad)

theorem corners (b : Bool) : cornerValue program b (.gate 3) = true := by
  cases b <;> decide

private theorem all_stops (k : Fin 4) : k ∈ StopGate program (.gate 3) := by
  classical
  have hShape :
      ∀ k : Fin 4, ((program.lines k).op = .and → k = 1) ∧
        ((program.lines k).op = .or → k = 0 ∨ k = 3) := by decide
  by_contra hStop
  have hNoAnd (hop : (program.lines k).op = .and)
      (hNeed : NeedCorner program (.gate 3) true (.gate k, true)) : False := by
    have hk := (hShape k).1 hop
    subst k
    exact (by decide : ¬ allowed true (.gate 1)) (allowed_corner true hNeed)
  have hNoOr (hop : (program.lines k).op = .or)
      (hNeed : NeedCorner program (.gate 3) false (.gate k, false)) : False := by
    rcases (hShape k).2 hop with hk | hk
    · exact hStop (hk ▸ stop_zero)
    · subst k
      have hEq := needCorner_eq_cornerValue (corners false) hNeed
      rw [corners] at hEq
      cases hEq
  have hFour := four_way_of_not_badFlip (corners false) (corners true)
    (not_badFlip_of_not_cutGate (fun h => hStop (cutGate_subset_stopGate _ _ h)))
  rcases hFour with h | h | h | h
  · exact hNoAnd h.1 h.2.2
  · exact hNoOr h.1 h.2.1
  · exact hNoAnd h.1 h.2.2
  · exact hNoOr h.1 h.2.1

theorem forest_mask : IsForestMask program (.gate 3) (fun _ => false) {1} := by
  exact ⟨fun r hr => ((stopGate_outside_forest (all_stops r)).1 r (ORMember.self hr)).elim,
    fun r hr => ((stopGate_outside_forest (all_stops r)).2 r (ANDMember.self hr)).elim⟩

theorem target_still_essential :
    EssentialAt (restrictedWire program (pinAt (fun _ => false) {1}) (.gate 3)) (0 : Fin 4) := by
  let x : BitString 4 := fun j => decide (j = 2)
  exact ⟨x, Function.update x 0 true, fun i hi => by simp [Function.update_of_ne hi], by decide⟩

/-- A two-corner minimum circuit can have an early varying direct stop
reader. The pinned input turns a genuine OR gate into a projection. -/
theorem minimum_has_early_stop_reader :
    (⟨0, by decide⟩ : Fin circuit.size) ∈ earlyReaders circuit.program (circuit.outputs 0)
      (fun _ => false) ({1} : Finset (Fin 4)) {0} := by
  classical
  change (0 : Fin 4) ∈ earlyReaders program (.gate 3) (fun _ => false) {1} {0}
  have hEq : restrictedWire program (pinAt (fun _ => false) {1}) (.gate 0) = projection 0 := by
    funext x
    change (substitute (pinAt (fun _ => false) {1}) x 0 ||
      substitute (pinAt (fun _ => false) {1}) x 1) = x 0
    simp [substitute, pinAt]
  have hVar : (0 : Fin 4) ∈ surviving program (pinAt (fun _ => false) {1}) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold varies
    rw [hEq]
    exact ⟨fun _ => false, fun _ => true, by decide⟩
  have hOld : (0 : Fin 4) ∉ fresh program (pinAt (fun _ => false) {1}) :=
    fun h => (Finset.mem_filter.mp h).2 (Or.inr (Or.inl ⟨0, hEq⟩))
  have hReads : Reads program 0 0 := ⟨⟨0, by decide⟩, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
    ⟨Finset.mem_inter.mpr ⟨stop_zero, hVar⟩, hOld⟩, 0, by simp, hReads⟩

#print axioms minimum
#print axioms minimum_has_early_stop_reader
#print axioms forest_mask
#print axioms target_still_essential

end PvsNP.Frontier.MinimumAliasControl
