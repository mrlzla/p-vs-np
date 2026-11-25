module

public import MCSPEarliestFresh

/-! Addressing the `IsPairFunnel` gap from `MCSPEarliestFresh.lean`:
1. Exact De Morgan duality on programs, circuits, and `mcspSquare m`, excluding
   all complementary pair funnels `(i, compIdx m i)`.
2. `S_m`-stabilizer orbit bounds excluding all weight-large pair funnels on
   `mcspSquare m` (`P = ∅`) and concrete middle-weight exclusions at `m = 32`.
3. The sharp `affineBlockAtMostOne` barrier demonstrating that truth-table sparsity,
   all affine tables, all 1-bit affine flips, and nonconstant 1-bit branches are
   consistent with controlling pair funnels on adaptive affine masks `starMask m`
   and sub-`2N` residual complexity (`m = 14` and `m = 32`). -/

@[expose] public section

namespace PvsNP.Frontier.PairFunnelGap

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN
open ForestPinning RestrictionCharges FreshCharges PairSeparation PermutedCut
open MinimumAliases EarliestFresh

/-! ### Part A: Exact De Morgan Duality & Complementary Pair Funnel Exclusion -/

/-- Dual De Morgan operator: swaps `.and`/`.or`, flips constants, preserves `.not`. -/
def dualOp : Op → Op
  | .const b => .const (!b)
  | .not => .not
  | .and => .or
  | .or => .and

theorem signature_arity_dualOp (op : Op) : signature.Arity (dualOp op) = signature.Arity op := by
  cases op <;> rfl

/-- Dualize a line's operator while preserving its input wires. -/
def dualLine {n g : ℕ} (l : Line signature n g) : Line signature n g :=
  ⟨dualOp l.op, fun a => l.wires (Fin.cast (signature_arity_dualOp l.op) a)⟩

/-- Dualize every gate in a De Morgan program without adding any gates. -/
def dualProgram {n : ℕ} : {g : ℕ} → Program signature n g → Program signature n g
  | _, .empty => .empty
  | _, .gate p line => .gate (dualProgram p) (dualLine line)

private theorem interpretation_dualOp (op : Op)
    (u : Fin (signature.Arity (dualOp op)) → Bool)
    (v : Fin (signature.Arity op) → Bool)
    (h : ∀ a : Fin (signature.Arity op),
      u (Fin.cast (signature_arity_dualOp op).symm a) = !(v a)) :
    interpretation (dualOp op) u = !(interpretation op v) := by
  cases op with
  | const b => rfl
  | not =>
    have h0 := h 0
    let a0 : Fin (signature.Arity (dualOp Op.not)) := ⟨0, by decide⟩
    change (!(u a0)) = !(!(v 0))
    have ha : u a0 = !(v 0) := by simpa [a0, Fin.cast] using h0
    rw [ha]
  | and =>
    have h0 := h 0
    have h1 := h 1
    let a0 : Fin (signature.Arity (dualOp Op.and)) := ⟨0, by decide⟩
    let a1 : Fin (signature.Arity (dualOp Op.and)) := ⟨1, by decide⟩
    change (u a0 || u a1) = !(v 0 && v 1)
    have ha0 : u a0 = !(v 0) := by simpa [a0, Fin.cast] using h0
    have ha1 : u a1 = !(v 1) := by simpa [a1, Fin.cast] using h1
    rw [ha0, ha1, Bool.not_and]
  | or =>
    have h0 := h 0
    have h1 := h 1
    let a0 : Fin (signature.Arity (dualOp Op.or)) := ⟨0, by decide⟩
    let a1 : Fin (signature.Arity (dualOp Op.or)) := ⟨1, by decide⟩
    change (u a0 && u a1) = !(v 0 || v 1)
    have ha0 : u a0 = !(v 0) := by simpa [a0, Fin.cast] using h0
    have ha1 : u a1 = !(v 1) := by simpa [a1, Fin.cast] using h1
    rw [ha0, ha1, Bool.not_or]

private theorem dualProgram_eval {n : ℕ} :
    ∀ {g : ℕ} (p : Program signature n g) (x : BitString n) (j : Fin g),
      (dualProgram p).eval interpretation x j = !(p.eval interpretation (fun k => !(x k)) j)
  | _, .empty, _, j => Fin.elim0 j
  | _, .gate p line, x, j => by
    cases j using Fin.lastCases with
    | last =>
      dsimp only [dualProgram]
      rw [Program.eval_gate_last, Program.eval_gate_last]
      change interpretation (dualOp line.op)
          (fun a => (dualProgram p).trace interpretation x
            (line.wires (Fin.cast (signature_arity_dualOp line.op) a))) =
        !(interpretation line.op
          (fun a => p.trace interpretation (fun k => !(x k)) (line.wires a)))
      apply interpretation_dualOp
      intro a
      have hArg : (dualProgram p).trace interpretation x (line.wires a) =
          !(p.trace interpretation (fun k => !(x k)) (line.wires a)) := by
        cases hW : line.wires a with
        | input k => simp [Program.trace]
        | gate u => exact dualProgram_eval p x u
      have hCast : Fin.cast (signature_arity_dualOp line.op)
          (Fin.cast (signature_arity_dualOp line.op).symm a) = a := by
        ext; rfl
      rw [hCast]
      exact hArg
    | cast k =>
      dsimp only [dualProgram]
      rw [Program.eval_gate_castSucc, Program.eval_gate_castSucc]
      exact dualProgram_eval p x k

theorem dualProgram_trace {n g : ℕ} (p : Program signature n g) (x : BitString n) (w : Wire n g) :
    (dualProgram p).trace interpretation x w = !(p.trace interpretation (fun k => !(x k)) w) := by
  cases w with
  | input k => simp [Program.trace]
  | gate j => exact dualProgram_eval p x j

/-- Dualize a De Morgan circuit at the exact same gate count. -/
def dualCircuit {n o : ℕ} (c : Circuit signature n o) : Circuit signature n o :=
  ⟨dualProgram c.program, c.outputs⟩

/-- De Morgan dual of a Boolean function: `dualFn f x = !(f (fun k => !(x k)))`. -/
def dualFn {n : ℕ} (f : BooleanFunction n) : BooleanFunction n :=
  fun x => !(f (fun k => !(x k)))

theorem dualFn_dualFn {n : ℕ} (f : BooleanFunction n) : dualFn (dualFn f) = f := by
  funext x
  simp [dualFn]

theorem dualFn_complexity_le {n : ℕ} (f : BooleanFunction n) :
    complexity interpretation (single (dualFn f)) ≤ complexity interpretation (single f) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  have hd : (dualCircuit c).Computes interpretation (single (dualFn f)) := by
    intro x
    funext o
    have hcEval : c.program.trace interpretation (fun k => !(x k)) (c.outputs o) =
        f (fun k => !(x k)) := congrFun (hc (fun k => !(x k))) o
    change (dualProgram c.program).trace interpretation x (c.outputs o) = !(f (fun k => !(x k)))
    rw [dualProgram_trace, hcEval]
  exact (complexity_le_of_computes (dualCircuit c) hd).trans (by simp [dualCircuit, hSize])

theorem complexity_dualFn {n : ℕ} (f : BooleanFunction n) :
    complexity interpretation (single (dualFn f)) = complexity interpretation (single f) :=
  le_antisymm (dualFn_complexity_le f)
    (by simpa only [dualFn_dualFn] using dualFn_complexity_le (dualFn f))

/-- Truth-table index obtained by complementing every input bit of the `m`-bit key. -/
def compIdx (m : ℕ) (i : Fin (2 ^ m)) : Fin (2 ^ m) :=
  BitString.equivFin m (fun k => !((BitString.equivFin m).symm i k))

theorem compIdx_involutive (m : ℕ) (i : Fin (2 ^ m)) : compIdx m (compIdx m i) = i := by
  dsimp [compIdx]
  rw [Equiv.symm_apply_apply]
  have hFun : (fun k : Fin m => !(!((BitString.equivFin m).symm i k))) = (BitString.equivFin m).symm i := by
    funext k; simp
  rw [hFun, Equiv.apply_symm_apply]

theorem compIdx_ne_self {m : ℕ} (hm : 1 ≤ m) (i : Fin (2 ^ m)) : compIdx m i ≠ i := by
  intro hEq
  have hVec := congrArg (BitString.equivFin m).symm hEq
  dsimp [compIdx] at hVec
  rw [Equiv.symm_apply_apply] at hVec
  have h0 := congrFun hVec ⟨0, hm⟩
  cases hBit : (BitString.equivFin m).symm i ⟨0, hm⟩ <;> simp_all

/-- Dualize a truth table by complementing its outputs at complemented input assignments. -/
def dualTable (m : ℕ) (T : BitString (2 ^ m)) : BitString (2 ^ m) :=
  fun i => !(T (compIdx m i))

private theorem truthTable_symm_apply {m : ℕ} (U : BitString (2 ^ m)) (y : BitString m) :
    (MCSP.truthTable m).symm U y = U (BitString.equivFin m y) := by
  have h := congrFun ((MCSP.truthTable m).apply_symm_apply U) (BitString.equivFin m y)
  rw [MCSP.truthTable_apply, Equiv.symm_apply_apply] at h
  exact h

/-- Exact `mcspSquare m` invariance under truth-table De Morgan duality. -/
theorem mcspSquare_dualTable (m : ℕ) (T : BitString (2 ^ m)) :
    mcspSquare m (dualTable m T) = mcspSquare m T := by
  apply Bool.eq_iff_iff.mpr
  simp only [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff]
  have hFn : (MCSP.truthTable m).symm (dualTable m T) = dualFn ((MCSP.truthTable m).symm T) := by
    funext x
    simp only [dualFn, truthTable_symm_apply, dualTable, compIdx, Equiv.symm_apply_apply]
  rw [hFn, complexity_dualFn]

/-- No complementary pair `(i, compIdx m i)` can form an `IsPairFunnel` of `mcspSquare m`
under any duality-closed partial mask `P`. -/
theorem mcspSquare_no_comp_funnel {m : ℕ} (_hm : 1 ≤ m) (P : Finset (Fin (2 ^ m)))
    (x : BitString (2 ^ m)) (hPClosed : ∀ u, u ∈ P ↔ compIdx m u ∈ P)
    (hXDual : ∀ u ∈ P, x (compIdx m u) = !(x u))
    {i : Fin (2 ^ m)} (hi : i ∈ essMask (mcspSquare m) x P) (v : Bool) :
    ¬ IsPairFunnel (fun z => mcspSquare m (substitute (pinAt x P) z)) i (compIdx m i) v := by
  classical
  let j := compIdx m i
  have hEssI : EssentialAt (fun z => mcspSquare m (substitute (pinAt x P) z)) i :=
    (Finset.mem_filter.mp hi).2
  rintro ⟨hij, h12, h13⟩
  have hji : j ≠ i := hij.symm
  have hDualSub (w : BitString (2 ^ m)) :
      dualTable m (substitute (pinAt x P) w) = substitute (pinAt x P) (dualTable m w) := by
    funext u
    by_cases huP : u ∈ P
    · have hcuP : compIdx m u ∈ P := (hPClosed u).mp huP
      simp [dualTable, substitute, pinAt, huP, hcuP, hXDual u huP]
    · have hcuP : compIdx m u ∉ P := fun h => huP ((hPClosed u).mpr h)
      simp [dualTable, substitute, pinAt, huP, hcuP]
  have hDualUpd (w : BitString (2 ^ m)) (q : Fin (2 ^ m)) (b : Bool) :
      dualTable m (Function.update w q b) = Function.update (dualTable m w) (compIdx m q) (!b) := by
    funext u
    by_cases hu : u = compIdx m q
    · subst hu
      simp [dualTable, compIdx_involutive]
    · have hcu : compIdx m u ≠ q := fun h => hu (by rw [← h, compIdx_involutive])
      simp [dualTable, Function.update_of_ne hu, Function.update_of_ne hcu]
  have hUpdComm (f : BitString (2 ^ m)) (a b : Fin (2 ^ m)) (v1 v2 : Bool) (hab : a ≠ b) :
      Function.update (Function.update f a v1) b v2 =
        Function.update (Function.update f b v2) a v1 := by
    funext u
    by_cases hua : u = a
    · subst hua; simp [Function.update_of_ne hab]
    · by_cases hub : u = b
      · subst hub; simp [Function.update_of_ne hua]
      · simp [Function.update_of_ne hua, Function.update_of_ne hub]
  obtain ⟨y, z, hyz, hne⟩ := hEssI
  have hCorner (w : BitString (2 ^ m)) (b : Bool) :
      mcspSquare m (substitute (pinAt x P) (Function.update w i b)) =
        mcspSquare m (substitute (pinAt x P) (Function.update (Function.update w i b) j (w j))) := by
    congr 2
    funext u
    by_cases huJ : u = j
    · subst huJ
      rw [Function.update_self, Function.update_of_ne hji]
    · rw [Function.update_of_ne huJ]
  have hAllEq (w : BitString (2 ^ m)) :
      mcspSquare m (substitute (pinAt x P) (Function.update (Function.update w i (!v)) j (!v))) =
        mcspSquare m (substitute (pinAt x P) (Function.update (Function.update w i v) j v)) := by
    let T00 := substitute (pinAt x P) (Function.update (Function.update w i (!v)) j (!v))
    have hD1 : dualTable m T00 =
        substitute (pinAt x P) (Function.update (Function.update (dualTable m w) i v) j v) := by
      dsimp only [T00]
      rw [hDualSub, hDualUpd, hDualUpd]
      congr 1
      have hjEq : compIdx m j = i := by dsimp [j]; exact compIdx_involutive m i
      rw [hjEq, Bool.not_not]
      exact hUpdComm (dualTable m w) j i v v hji
    have hF1 : mcspSquare m (substitute (pinAt x P) (Function.update (Function.update (dualTable m w) i v) j v)) =
        mcspSquare m (substitute (pinAt x P) (Function.update (Function.update (dualTable m w) i v) j (!v))) :=
      (h13 (dualTable m w)).symm
    let T10 := substitute (pinAt x P) (Function.update (Function.update w i v) j (!v))
    have hD2 : dualTable m T10 =
        substitute (pinAt x P) (Function.update (Function.update (dualTable m w) i v) j (!v)) := by
      dsimp only [T10]
      rw [hDualSub, hDualUpd, hDualUpd]
      congr 1
      have hjEq : compIdx m j = i := by dsimp [j]; exact compIdx_involutive m i
      rw [hjEq, Bool.not_not]
      exact hUpdComm (dualTable m w) j i (!v) v hji
    have hStep1 : mcspSquare m T00 = mcspSquare m T10 := by
      rw [← mcspSquare_dualTable m T00, hD1, hF1, ← hD2, mcspSquare_dualTable m T10]
    have hStep2 : mcspSquare m T10 =
        mcspSquare m (substitute (pinAt x P) (Function.update (Function.update w i v) j v)) :=
      h13 w
    exact hStep1.trans hStep2
  have hStep (w : BitString (2 ^ m)) (b : Bool) :
      mcspSquare m (substitute (pinAt x P) (Function.update w i b)) =
        mcspSquare m (substitute (pinAt x P) (Function.update (Function.update w i v) j v)) := by
    rw [hCorner w b]
    by_cases hbv : b = v
    · subst hbv
      by_cases hwj : w j = b
      · rw [hwj]
      · have hwj' : w j = !b := by revert hwj; cases w j <;> cases b <;> decide
        rw [hwj']
        exact h13 w
    · have hbv' : b = !v := by revert hbv; cases b <;> cases v <;> decide
      by_cases hwj : w j = v
      · rw [hbv', hwj]
        exact (h12 w).symm.trans (h13 w)
      · have hwj' : w j = !v := by revert hwj; cases w j <;> cases v <;> decide
        rw [hbv', hwj']
        exact hAllEq w
  have hyEq : Function.update y i (y i) = y := Function.update_eq_self i y
  have hzEq : Function.update y i (z i) = z := by
    funext u
    by_cases hu : u = i
    · subst hu; simp
    · simp [Function.update_of_ne hu, hyz u hu]
  apply hne
  change mcspSquare m (substitute (pinAt x P) y) = mcspSquare m (substitute (pinAt x P) z)
  rw [← hyEq, ← hzEq, hStep y (y i), hStep y (z i)]

theorem mcspSquare_no_comp_funnel_empty {m : ℕ} (hm : 1 ≤ m) {i : Fin (2 ^ m)}
    (hi : EssentialAt (mcspSquare m) i) (v : Bool) :
    ¬ IsPairFunnel (mcspSquare m) i (compIdx m i) v := by
  have hId : (fun z => mcspSquare m (substitute (pinAt (fun _ => false) ∅) z)) = mcspSquare m := by
    funext z
    congr 1
  have hEss : i ∈ essMask (mcspSquare m) (fun _ => false) ∅ := by
    classical
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.notMem_empty _⟩, ?_⟩
    rw [hId]
    exact hi
  have hNo := mcspSquare_no_comp_funnel hm ∅ (fun _ => false)
    (fun _ => by simp) (fun _ h => (Finset.notMem_empty _ h).elim) hEss v
  rwa [hId] at hNo

/-! ### Part B: Shared 3-Part Equivalence Helper & `S_m`-Stabilizer Orbit Exclusion -/

private noncomputable def finsetEquivOfCard {α β : Type*} [Fintype α] [Fintype β]
    (S : Finset α) (T : Finset β) (h : S.card = T.card) : {x // x ∈ S} ≃ {y // y ∈ T} :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using h)

private noncomputable def equivOfThreeDisjoint {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A1 A2 A3 : Finset α) (B1 B2 B3 : Finset β)
    (hA12 : Disjoint A1 A2) (hA13 : Disjoint A1 A3) (hA23 : Disjoint A2 A3)
    (hB12 : Disjoint B1 B2) (hB13 : Disjoint B1 B3) (hB23 : Disjoint B2 B3)
    (hC1 : A1.card = B1.card) (hC2 : A2.card = B2.card) (hC3 : A3.card = B3.card)
    (hTot : Fintype.card α = Fintype.card β) :
    { e : α ≃ β //
      (∀ a, a ∈ A1 ↔ e a ∈ B1) ∧ (∀ a, a ∈ A2 ↔ e a ∈ B2) ∧ (∀ a, a ∈ A3 ↔ e a ∈ B3) } := by
  classical
  let A4 := Finset.univ \ (A1 ∪ A2 ∪ A3)
  let B4 := Finset.univ \ (B1 ∪ B2 ∪ B3)
  have hU12 : Disjoint (A1 ∪ A2) A3 := Finset.disjoint_union_left.mpr ⟨hA13, hA23⟩
  have hV12 : Disjoint (B1 ∪ B2) B3 := Finset.disjoint_union_left.mpr ⟨hB13, hB23⟩
  have hCA : (A1 ∪ A2 ∪ A3).card = A1.card + A2.card + A3.card := by
    rw [Finset.card_union_of_disjoint hU12, Finset.card_union_of_disjoint hA12]
  have hCB : (B1 ∪ B2 ∪ B3).card = B1.card + B2.card + B3.card := by
    rw [Finset.card_union_of_disjoint hV12, Finset.card_union_of_disjoint hB12]
  have hSA := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A1 ∪ A2 ∪ A3))
  have hSB := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (B1 ∪ B2 ∪ B3))
  simp only [Finset.card_univ] at hSA hSB
  have hC4 : A4.card = B4.card := by
    dsimp only [A4, B4]
    omega
  let e1 := finsetEquivOfCard A1 B1 hC1
  let e2 := finsetEquivOfCard A2 B2 hC2
  let e3 := finsetEquivOfCard A3 B3 hC3
  let e4 := finsetEquivOfCard A4 B4 hC4
  let toF (a : α) : β :=
    if h1 : a ∈ A1 then (e1 ⟨a, h1⟩).1
    else if h2 : a ∈ A2 then (e2 ⟨a, h2⟩).1
    else if h3 : a ∈ A3 then (e3 ⟨a, h3⟩).1
    else (e4 ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2, h3]⟩⟩).1
  let invF (b : β) : α :=
    if h1 : b ∈ B1 then (e1.symm ⟨b, h1⟩).1
    else if h2 : b ∈ B2 then (e2.symm ⟨b, h2⟩).1
    else if h3 : b ∈ B3 then (e3.symm ⟨b, h3⟩).1
    else (e4.symm ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2, h3]⟩⟩).1
  have hLeft : ∀ a : α, invF (toF a) = a := by
    intro a
    by_cases h1 : a ∈ A1
    · have hb1 : toF a ∈ B1 := by dsimp [toF]; rw [dite_eq_left h1]; exact (e1 ⟨a, h1⟩).2
      dsimp only [invF]; rw [dite_eq_left hb1]
      have hSub : (⟨toF a, hb1⟩ : {y // y ∈ B1}) = e1 ⟨a, h1⟩ := by
        ext; dsimp [toF]; rw [dite_eq_left h1]
      rw [hSub, Equiv.symm_apply_apply]
    · by_cases h2 : a ∈ A2
      · have hB : toF a ∈ B2 := by dsimp [toF]; rw [dite_eq_right h1, dite_eq_left h2]; exact (e2 ⟨a, h2⟩).2
        have hn1 : toF a ∉ B1 := Finset.disjoint_right.mp hB12 hB
        dsimp only [invF]; rw [dite_eq_right hn1, dite_eq_left hB]
        have hSub : (⟨toF a, hB⟩ : {y // y ∈ B2}) = e2 ⟨a, h2⟩ := by
          ext; dsimp [toF]; rw [dite_eq_right h1, dite_eq_left h2]
        rw [hSub, Equiv.symm_apply_apply]
      · by_cases h3 : a ∈ A3
        · have hB : toF a ∈ B3 := by
            dsimp [toF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]; exact (e3 ⟨a, h3⟩).2
          have hn1 : toF a ∉ B1 := Finset.disjoint_right.mp hB13 hB
          have hn2 : toF a ∉ B2 := Finset.disjoint_right.mp hB23 hB
          dsimp only [invF]; rw [dite_eq_right hn1, dite_eq_right hn2, dite_eq_left hB]
          have hSub : (⟨toF a, hB⟩ : {y // y ∈ B3}) = e3 ⟨a, h3⟩ := by
            ext; dsimp [toF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
          rw [hSub, Equiv.symm_apply_apply]
        · have hA4 : a ∈ A4 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2, h3]⟩
          have hB : toF a ∈ B4 := by
            dsimp [toF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]; exact (e4 ⟨a, hA4⟩).2
          have hNotU := (Finset.mem_sdiff.mp hB).2
          simp only [Finset.mem_union, not_or] at hNotU
          dsimp only [invF]; rw [dite_eq_right hNotU.1.1, dite_eq_right hNotU.1.2, dite_eq_right hNotU.2]
          have hSub : (⟨toF a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hNotU]⟩⟩ : {y // y ∈ B4}) =
              e4 ⟨a, hA4⟩ := by
            ext; dsimp [toF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
          rw [hSub, Equiv.symm_apply_apply]
  have hRight : ∀ b : β, toF (invF b) = b := by
    intro b
    by_cases h1 : b ∈ B1
    · have ha1 : invF b ∈ A1 := by dsimp [invF]; rw [dite_eq_left h1]; exact (e1.symm ⟨b, h1⟩).2
      dsimp only [toF]; rw [dite_eq_left ha1]
      have hSub : (⟨invF b, ha1⟩ : {x // x ∈ A1}) = e1.symm ⟨b, h1⟩ := by
        ext; dsimp [invF]; rw [dite_eq_left h1]
      rw [hSub, Equiv.apply_symm_apply]
    · by_cases h2 : b ∈ B2
      · have hA : invF b ∈ A2 := by dsimp [invF]; rw [dite_eq_right h1, dite_eq_left h2]; exact (e2.symm ⟨b, h2⟩).2
        have hn1 : invF b ∉ A1 := Finset.disjoint_right.mp hA12 hA
        dsimp only [toF]; rw [dite_eq_right hn1, dite_eq_left hA]
        have hSub : (⟨invF b, hA⟩ : {x // x ∈ A2}) = e2.symm ⟨b, h2⟩ := by
          ext; dsimp [invF]; rw [dite_eq_right h1, dite_eq_left h2]
        rw [hSub, Equiv.apply_symm_apply]
      · by_cases h3 : b ∈ B3
        · have hA : invF b ∈ A3 := by
            dsimp [invF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]; exact (e3.symm ⟨b, h3⟩).2
          have hn1 : invF b ∉ A1 := Finset.disjoint_right.mp hA13 hA
          have hn2 : invF b ∉ A2 := Finset.disjoint_right.mp hA23 hA
          dsimp only [toF]; rw [dite_eq_right hn1, dite_eq_right hn2, dite_eq_left hA]
          have hSub : (⟨invF b, hA⟩ : {x // x ∈ A3}) = e3.symm ⟨b, h3⟩ := by
            ext; dsimp [invF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_left h3]
          rw [hSub, Equiv.apply_symm_apply]
        · have hB4 : b ∈ B4 := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2, h3]⟩
          have hA : invF b ∈ A4 := by
            dsimp [invF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]; exact (e4.symm ⟨b, hB4⟩).2
          have hNotU := (Finset.mem_sdiff.mp hA).2
          simp only [Finset.mem_union, not_or] at hNotU
          dsimp only [toF]; rw [dite_eq_right hNotU.1.1, dite_eq_right hNotU.1.2, dite_eq_right hNotU.2]
          have hSub : (⟨invF b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hNotU]⟩⟩ : {x // x ∈ A4}) =
              e4.symm ⟨b, hB4⟩ := by
            ext; dsimp [invF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right h3]
          rw [hSub, Equiv.apply_symm_apply]
  refine ⟨⟨toF, invF, hLeft, hRight⟩, ?_, ?_, ?_⟩
  · intro a
    constructor
    · intro h1; dsimp [toF]; rw [dite_eq_left h1]; exact (e1 ⟨a, h1⟩).2
    · intro hB1
      by_contra hn1
      by_cases h2 : a ∈ A2
      · have hB2 : toF a ∈ B2 := by dsimp [toF]; rw [dite_eq_right hn1, dite_eq_left h2]; exact (e2 ⟨a, h2⟩).2
        exact (Finset.disjoint_left.mp hB12 hB1) hB2
      · by_cases h3 : a ∈ A3
        · have hB3 : toF a ∈ B3 := by
            dsimp [toF]; rw [dite_eq_right hn1, dite_eq_right h2, dite_eq_left h3]; exact (e3 ⟨a, h3⟩).2
          exact (Finset.disjoint_left.mp hB13 hB1) hB3
        · have hB4 : toF a ∈ B4 := by
            dsimp [toF]; rw [dite_eq_right hn1, dite_eq_right h2, dite_eq_right h3]
            exact (e4 _).2
          exact (Finset.mem_sdiff.mp hB4).2 (Finset.mem_union_left _ (Finset.mem_union_left _ hB1))
  · intro a
    constructor
    · intro h2
      have hn1 : a ∉ A1 := Finset.disjoint_right.mp hA12 h2
      dsimp [toF]; rw [dite_eq_right hn1, dite_eq_left h2]; exact (e2 ⟨a, h2⟩).2
    · intro hB2
      by_contra hn2
      by_cases h1 : a ∈ A1
      · have hB1 : toF a ∈ B1 := by dsimp [toF]; rw [dite_eq_left h1]; exact (e1 ⟨a, h1⟩).2
        exact (Finset.disjoint_left.mp hB12 hB1) hB2
      · by_cases h3 : a ∈ A3
        · have hB3 : toF a ∈ B3 := by
            dsimp [toF]; rw [dite_eq_right h1, dite_eq_right hn2, dite_eq_left h3]; exact (e3 ⟨a, h3⟩).2
          exact (Finset.disjoint_left.mp hB23 hB2) hB3
        · have hB4 : toF a ∈ B4 := by
            dsimp [toF]; rw [dite_eq_right h1, dite_eq_right hn2, dite_eq_right h3]
            exact (e4 _).2
          exact (Finset.mem_sdiff.mp hB4).2 (Finset.mem_union_left _ (Finset.mem_union_right _ hB2))
  · intro a
    constructor
    · intro h3
      have hn1 : a ∉ A1 := Finset.disjoint_right.mp hA13 h3
      have hn2 : a ∉ A2 := Finset.disjoint_right.mp hA23 h3
      dsimp [toF]; rw [dite_eq_right hn1, dite_eq_right hn2, dite_eq_left h3]; exact (e3 ⟨a, h3⟩).2
    · intro hB3
      by_contra hn3
      by_cases h1 : a ∈ A1
      · have hB1 : toF a ∈ B1 := by dsimp [toF]; rw [dite_eq_left h1]; exact (e1 ⟨a, h1⟩).2
        exact (Finset.disjoint_left.mp hB13 hB1) hB3
      · by_cases h2 : a ∈ A2
        · have hB2 : toF a ∈ B2 := by dsimp [toF]; rw [dite_eq_right h1, dite_eq_left h2]; exact (e2 ⟨a, h2⟩).2
          exact (Finset.disjoint_left.mp hB23 hB2) hB3
        · have hB4 : toF a ∈ B4 := by
            dsimp [toF]; rw [dite_eq_right h1, dite_eq_right h2, dite_eq_right hn3]
            exact (e4 _).2
          exact (Finset.mem_sdiff.mp hB4).2 (Finset.mem_union_right _ hB3)

/-- Bit positions where key `i` has value `false`. -/
def bitZeroSet (m : ℕ) (i : Fin (2 ^ m)) : Finset (Fin m) :=
  Finset.univ.filter fun k => (BitString.equivFin m).symm i k = false

/-- Bit positions where key `i` has value `true`. -/
def bitOneSet (m : ℕ) (i : Fin (2 ^ m)) : Finset (Fin m) :=
  Finset.univ.filter fun k => (BitString.equivFin m).symm i k = true

/-- Coordinates in `bitZeroSet m i` where key `j` flips to `true`. -/
def diffZeroSet (m : ℕ) (i j : Fin (2 ^ m)) : Finset (Fin m) :=
  (bitZeroSet m i).filter fun k => (BitString.equivFin m).symm j k = true

/-- Coordinates in `bitOneSet m i` where key `j` flips to `false`. -/
def diffOneSet (m : ℕ) (i j : Fin (2 ^ m)) : Finset (Fin m) :=
  (bitOneSet m i).filter fun k => (BitString.equivFin m).symm j k = false

/-- `S_m`-stabilizer orbit bound: any pair funnel `(i, j)` of `mcspSquare m` (`m ≥ 7`) has
stabilizer orbit size at most `descriptionBitBound m`. -/
theorem mcspSquare_funnel_orbit_le (m : ℕ) (hm : 7 ≤ m)
    (i j : Fin (2 ^ m)) (v : Bool) (hFunnel : IsPairFunnel (mcspSquare m) i j v) :
    Nat.choose (bitZeroSet m i).card (diffZeroSet m i j).card *
      Nat.choose (bitOneSet m i).card (diffOneSet m i j).card ≤ descriptionBitBound m := by
  classical
  obtain ⟨hij, h12, h13⟩ := hFunnel
  have hNotEssJ : ¬ EssentialAt (fun z => mcspSquare m (Function.update z i v)) j := by
    rintro ⟨y, z, hyz, hne⟩
    have hjCorner (w : BitString (2 ^ m)) :
        mcspSquare m (Function.update w i v) =
          mcspSquare m (Function.update (Function.update w i v) j v) := by
      have hSub : Function.update w i v =
          Function.update (Function.update w i v) j (w j) := by
        funext u
        by_cases huj : u = j
        · subst huj; simp [Function.update_of_ne hij.symm]
        · simp [Function.update_of_ne huj]
      have hLHS : mcspSquare m (Function.update w i v) =
          mcspSquare m (Function.update (Function.update w i v) j (w j)) :=
        congrArg (mcspSquare m) hSub
      rw [hLHS]
      cases hwj : w j
      · cases v
        · rfl
        · exact h13 w
      · cases v
        · exact h13 w
        · rfl
    apply hne
    dsimp only
    rw [hjCorner y, hjCorner z]
    congr 1
    funext u
    by_cases huj : u = j
    · subst huj; simp
    · by_cases hui : u = i
      · subst hui; simp [Function.update_of_ne huj]
      · simp [Function.update_of_ne huj, Function.update_of_ne hui, hyz u huj]
  let Z := bitZeroSet m i
  let O := bitOneSet m i
  let DZ := diffZeroSet m i j
  let DO := diffOneSet m i j
  let pairs := Z.powersetCard DZ.card ×ˢ O.powersetCard DO.card
  let targetVec (ab : Finset (Fin m) × Finset (Fin m)) : BitString m :=
    fun k => if k ∈ Z then decide (k ∈ ab.1) else decide (k ∉ ab.2)
  let targetIdx (ab : Finset (Fin m) × Finset (Fin m)) : Fin (2 ^ m) :=
    BitString.equivFin m (targetVec ab)
  let center : BitString (2 ^ m) := Function.update (fun _ => !v) i v
  have hCenterAcc : mcspSquare m center = true := by
    have hFlip := mcspSquare_accepts_affine_flip m hm (fun _ => false) (!v) i
    have hDotZero : ∀ {n : ℕ} (z : BitString n), dot (fun _ => false) z = false := by
      intro n z
      induction n with
      | zero => rfl
      | succ n ih =>
        change ((false && z 0) ^^ dot (fun _ => false) (Fin.tail z)) = false
        simpa using ih (Fin.tail z)
    have hAffConst : MCSP.truthTable m (affine (fun _ => false) (!v)) = fun _ => !v := by
      funext u
      simp [MCSP.truthTable_apply, affine, hDotZero]
    rw [hAffConst] at hFlip
    simpa [center] using hFlip
  let W := Finset.univ.erase i
  let ignored := W \ essentialPositions (fun z => mcspSquare m (restrictTable center W z)) W
  have hMaps : ∀ ab ∈ pairs, targetIdx ab ∈ ignored := by
    intro ab hab
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hab
    have hASub : ab.1 ⊆ Z := (Finset.mem_powersetCard.mp hA).1
    have hACard : ab.1.card = DZ.card := (Finset.mem_powersetCard.mp hA).2
    have hBSub : ab.2 ⊆ O := (Finset.mem_powersetCard.mp hB).1
    have hBCard : ab.2.card = DO.card := (Finset.mem_powersetCard.mp hB).2
    have hDZSub : DZ ⊆ Z := Finset.filter_subset ..
    have hDOSub : DO ⊆ O := Finset.filter_subset ..
    have hZA : (Z \ ab.1).card = (Z \ DZ).card := by
      have h1 := Finset.card_sdiff_add_card_eq_card hASub
      have h2 := Finset.card_sdiff_add_card_eq_card hDZSub
      omega
    have hDisjZO : Disjoint Z O := Finset.disjoint_left.mpr fun k hk1 hk2 => by
      have hF := (Finset.mem_filter.mp hk1).2
      have hT := (Finset.mem_filter.mp hk2).2
      rw [hF] at hT; cases hT
    have hA12 : Disjoint ab.1 (Z \ ab.1) := disjoint_sdiff_self_right
    have hA13 : Disjoint ab.1 ab.2 := hDisjZO.mono hASub hBSub
    have hA23 : Disjoint (Z \ ab.1) ab.2 := hDisjZO.mono Finset.sdiff_subset hBSub
    have hB12 : Disjoint DZ (Z \ DZ) := disjoint_sdiff_self_right
    have hB13 : Disjoint DZ DO := hDisjZO.mono hDZSub hDOSub
    have hB23 : Disjoint (Z \ DZ) DO := hDisjZO.mono Finset.sdiff_subset hDOSub
    obtain ⟨e, he1, he2, he3⟩ := equivOfThreeDisjoint ab.1 (Z \ ab.1) ab.2 DZ (Z \ DZ) DO
      hA12 hA13 hA23 hB12 hB13 hB23 hACard hZA hBCard rfl
    have heI : tablePerm e i = i := by
      apply (BitString.equivFin m).symm.injective
      rw [tablePerm, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
      funext k
      change (BitString.equivFin m).symm i (e k) = (BitString.equivFin m).symm i k
      by_cases hkZ : k ∈ Z
      · have heInZ : e k ∈ Z := by
          by_cases hkA : k ∈ ab.1
          · exact hDZSub ((he1 k).mp hkA)
          · exact Finset.sdiff_subset ((he2 k).mp (Finset.mem_sdiff.mpr ⟨hkZ, hkA⟩))
        rw [(Finset.mem_filter.mp hkZ).2, (Finset.mem_filter.mp heInZ).2]
      · have hkO : k ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Bool.eq_true_of_not_eq_false (fun h => hkZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))⟩
        have heInO : e k ∈ O := by
          by_cases heZ : e k ∈ Z
          · exfalso
            by_cases heDZ : e k ∈ DZ
            · exact hkZ (hASub ((he1 k).mpr heDZ))
            · exact hkZ (Finset.sdiff_subset ((he2 k).mpr (Finset.mem_sdiff.mpr ⟨heZ, heDZ⟩)))
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Bool.eq_true_of_not_eq_false (fun h => heZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))⟩
        rw [(Finset.mem_filter.mp hkO).2, (Finset.mem_filter.mp heInO).2]
    have heJ : tablePerm e j = targetIdx ab := by
      apply (BitString.equivFin m).symm.injective
      rw [tablePerm, Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
      dsimp only [targetIdx]
      rw [Equiv.symm_apply_apply]
      funext k
      change (BitString.equivFin m).symm j (e k) = targetVec ab k
      by_cases hkZ : k ∈ Z
      · simp only [targetVec, hkZ, ite_true]
        by_cases hkA : k ∈ ab.1
        · have heDZ : e k ∈ DZ := (he1 k).mp hkA
          simp [hkA, (Finset.mem_filter.mp heDZ).2]
        · have heZND : e k ∈ Z \ DZ := (he2 k).mp (Finset.mem_sdiff.mpr ⟨hkZ, hkA⟩)
          have heJFalse : (BitString.equivFin m).symm j (e k) ≠ true := fun hT =>
            (Finset.mem_sdiff.mp heZND).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp heZND).1, hT⟩)
          simp [hkA, Bool.eq_false_of_not_eq_true heJFalse]
      · simp only [targetVec, hkZ, ite_false]
        by_cases hkB : k ∈ ab.2
        · have heDO : e k ∈ DO := (he3 k).mp hkB
          simp [hkB, (Finset.mem_filter.mp heDO).2]
        · have heO : e k ∈ O := by
            by_cases heZ : e k ∈ Z
            · exfalso
              by_cases heDZ : e k ∈ DZ
              · exact hkZ (hASub ((he1 k).mpr heDZ))
              · exact hkZ (Finset.sdiff_subset ((he2 k).mpr (Finset.mem_sdiff.mpr ⟨heZ, heDZ⟩)))
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                Bool.eq_true_of_not_eq_false (fun h => heZ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))⟩
          have heNDO : e k ∉ DO := fun h => hkB ((he3 k).mpr h)
          have heJTrue : (BitString.equivFin m).symm j (e k) = true := by
            by_contra hNF
            exact heNDO (Finset.mem_filter.mpr ⟨heO, Bool.eq_false_of_not_eq_true hNF⟩)
          simp [hkB, heJTrue]
    have hNeI : targetIdx ab ≠ i := by
      rw [← heJ, ← heI]
      exact fun hEq => hij ((tablePerm e).injective hEq).symm
    have hRestrictEq (z : BitString (2 ^ m)) :
        restrictTable center W z = Function.update z i v := by
      funext u
      by_cases hu : u = i
      · subst hu; simp [W, restrictTable, center]
      · simp [W, restrictTable, hu]
    have hNotEssTarget : ¬ EssentialAt (fun z => mcspSquare m (restrictTable center W z)) (targetIdx ab) := by
      intro ⟨y, z, hyz, hne⟩
      apply hNotEssJ
      refine ⟨y ∘ tablePerm e, z ∘ tablePerm e, ?_, ?_⟩
      · intro u hu
        have hNeU : tablePerm e u ≠ targetIdx ab := by
          rw [← heJ]
          exact fun hEq => hu ((tablePerm e).injective hEq)
        exact hyz (tablePerm e u) hNeU
      · have hTrans (w : BitString (2 ^ m)) :
            Function.update (w ∘ tablePerm e) i v = Function.update w (tablePerm e i) v ∘ tablePerm e := by
          funext u
          by_cases hu : tablePerm e u = tablePerm e i
          · have hui : u = i := (tablePerm e).injective hu
            subst hui; simp
          · have hui : u ≠ i := fun h => hu (congrArg _ h)
            simp [Function.update_of_ne hu, Function.update_of_ne hui]
        have hTrans' (w : BitString (2 ^ m)) :
            Function.update (w ∘ tablePerm e) i v = Function.update w i v ∘ tablePerm e := by
          simpa [heI] using hTrans w
        have hY := square_comp_tablePerm e (Function.update y i v)
        have hZ := square_comp_tablePerm e (Function.update z i v)
        rw [← hTrans' y] at hY
        rw [← hTrans' z] at hZ
        change mcspSquare m (Function.update (y ∘ tablePerm e) i v) ≠
          mcspSquare m (Function.update (z ∘ tablePerm e) i v)
        rw [hY, hZ]
        simpa [hRestrictEq] using hne
    have hMemW : targetIdx ab ∈ W := Finset.mem_erase.mpr ⟨hNeI, Finset.mem_univ _⟩
    exact Finset.mem_sdiff.mpr ⟨hMemW, fun hf => hNotEssTarget (Finset.mem_filter.mp hf).2⟩
  have hInj : Set.InjOn targetIdx (pairs : Set (Finset (Fin m) × Finset (Fin m))) := by
    intro ab1 h1 ab2 h2 hEq
    have hA1 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h1).1).1
    have hB1 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h1).2).1
    have hA2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h2).1).1
    have hB2 := (Finset.mem_powersetCard.mp (Finset.mem_product.mp h2).2).1
    have hVec : targetVec ab1 = targetVec ab2 := (BitString.equivFin m).injective hEq
    apply Prod.ext
    · ext k
      by_cases hkZ : k ∈ Z
      · have hkv := congrFun hVec k
        simpa [targetVec, hkZ] using hkv
      · have hk1 : k ∉ ab1.1 := fun h => hkZ (hA1 h)
        have hk2 : k ∉ ab2.1 := fun h => hkZ (hA2 h)
        simp [hk1, hk2]
    · ext k
      by_cases hkZ : k ∈ Z
      · have hkO : k ∉ O := fun hO => by
          have h1' := (Finset.mem_filter.mp hkZ).2
          have h2' := (Finset.mem_filter.mp hO).2
          rw [h1'] at h2'; cases h2'
        have hk1 : k ∉ ab1.2 := fun h => hkO (hB1 h)
        have hk2 : k ∉ ab2.2 := fun h => hkO (hB2 h)
        simp [hk1, hk2]
      · have hkv := congrFun hVec k
        simpa [targetVec, hkZ] using hkv
  have hCardLe : pairs.card ≤ ignored.card := Finset.card_le_card_of_injOn targetIdx hMaps hInj
  have hPow := (pow_card_inessential_le (mcspSquare m) center W hCenterAcc).trans
    (card_accepting_mcspSquare_le m)
  have hIgnLe : ignored.card ≤ descriptionBitBound m :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPow
  have hPairsCard : pairs.card =
      Nat.choose Z.card DZ.card * Nat.choose O.card DO.card := by
    simp [pairs, Finset.card_product, Finset.card_powersetCard]
  exact hPairsCard ▸ hCardLe.trans hIgnLe

theorem mcspSquare_no_large_orbit_funnel {m : ℕ} (hm : 7 ≤ m)
    {i j : Fin (2 ^ m)} (v : Bool)
    (hLarge : descriptionBitBound m <
      Nat.choose (bitZeroSet m i).card (diffZeroSet m i j).card *
        Nat.choose (bitOneSet m i).card (diffOneSet m i j).card) :
    ¬ IsPairFunnel (mcspSquare m) i j v :=
  fun hF => not_lt_of_ge (mcspSquare_funnel_orbit_le m hm i j v hF) hLarge

theorem mcspSquare_32_no_weight5_zero_funnel (j : Fin (2 ^ 32)) (v : Bool)
    (hwLo : 5 ≤ (Finset.univ.filter fun k : Fin 32 => (BitString.equivFin 32).symm j k = true).card)
    (hwHi : (Finset.univ.filter fun k : Fin 32 => (BitString.equivFin 32).symm j k = true).card ≤ 27) :
    ¬ IsPairFunnel (mcspSquare 32) (BitString.equivFin 32 (fun _ => false)) j v := by
  let i0 := BitString.equivFin 32 (fun _ => false)
  have hZ : bitZeroSet 32 i0 = Finset.univ := by
    ext k; simp [bitZeroSet, i0, Equiv.symm_apply_apply]
  have hO : bitOneSet 32 i0 = ∅ := by
    ext k; simp [bitOneSet, i0, Equiv.symm_apply_apply]
  have hDO : diffOneSet 32 i0 j = ∅ := by
    ext k; simp [diffOneSet, hO]
  have hDZ : diffZeroSet 32 i0 j =
      Finset.univ.filter fun k : Fin 32 => (BitString.equivFin 32).symm j k = true := by
    ext k; simp [diffZeroSet, hZ]
  let w := (Finset.univ.filter fun k : Fin 32 => (BitString.equivFin 32).symm j k = true).card
  have hWLe : w ≤ 32 := (Finset.card_le_univ _).trans (by simp)
  have hChooseAll : ∀ k : Fin 33, 5 ≤ k.val → k.val ≤ 27 → 27672 < Nat.choose 32 k.val := by
    decide
  have hChoose : descriptionBitBound 32 < Nat.choose 32 w := by
    rw [show descriptionBitBound 32 = 27672 by decide]
    exact hChooseAll ⟨w, by omega⟩ hwLo hwHi
  apply mcspSquare_no_large_orbit_funnel (m := 32) (by decide) v
  rw [hZ, hO, hDO, hDZ, Finset.card_univ, Fintype.card_fin, Finset.card_empty]
  simpa using hChoose

/-! ### Part C: Sharp Affine-Basis Funnel Barrier (`affineBlockAtMostOne`) -/

/-- Affine star of `m + 1` points centered at `c : BitString m` and its `m` neighbors. -/
def starSet (m : ℕ) (c : BitString m) : Finset (BitString m) :=
  insert c (Finset.univ.image fun t : Fin m => Function.update c t (!(c t)))

private theorem dot_zero_left : ∀ {m : ℕ} (z : BitString m), dot (fun _ => false) z = false
  | 0, _ => rfl
  | _ + 1, z => by
    have hEq : dot (fun _ => false) z =
        ((false && z 0) ^^ dot (fun _ => false) (Fin.tail z)) := rfl
    rw [hEq]
    simp [dot_zero_left (Fin.tail z)]

private theorem dot_update_not : ∀ {m : ℕ} (a c : BitString m) (t : Fin m),
    dot a (Function.update c t (!(c t))) = (dot a c ^^ a t)
  | 0, _, _, t => Fin.elim0 t
  | m + 1, a, c, t => by
    cases t using Fin.cases with
    | zero =>
      have hTail : Fin.tail (Function.update c 0 (!(c 0))) = Fin.tail c := by
        funext k; simp [Fin.tail]
      have hLHS : dot a (Function.update c 0 (!(c 0))) =
          ((a 0 && !(c 0)) ^^ dot (Fin.tail a) (Fin.tail (Function.update c 0 (!(c 0))))) := rfl
      have hRHS : dot a c = ((a 0 && c 0) ^^ dot (Fin.tail a) (Fin.tail c)) := rfl
      rw [hLHS, hRHS, hTail]
      generalize a 0 = ha
      generalize c 0 = hc
      generalize dot (Fin.tail a) (Fin.tail c) = hd
      cases ha <;> cases hc <;> cases hd <;> rfl
    | succ t' =>
      have h0 : Function.update c t'.succ (!(c t'.succ)) 0 = c 0 := by
        simp [Function.update_of_ne (Fin.succ_ne_zero t').symm]
      have hTail : Fin.tail (Function.update c t'.succ (!(c t'.succ))) =
          Function.update (Fin.tail c) t' (!(Fin.tail c t')) := by
        funext k
        simp only [Fin.tail]
        by_cases hk : k = t'
        · subst hk; simp
        · simp [Fin.tail, hk, Fin.succ_inj.ne.mpr hk]
      have hLHS : dot a (Function.update c t'.succ (!(c t'.succ))) =
          ((a 0 && Function.update c t'.succ (!(c t'.succ)) 0) ^^
            dot (Fin.tail a) (Fin.tail (Function.update c t'.succ (!(c t'.succ))))) := rfl
      have hRHS : dot a c = ((a 0 && c 0) ^^ dot (Fin.tail a) (Fin.tail c)) := rfl
      rw [hLHS, hRHS, h0, hTail, dot_update_not (Fin.tail a) (Fin.tail c) t']
      simp [Fin.tail]

theorem affine_eq_zero_of_zero_on_star {m : ℕ} {a : BitString m} {b0 : Bool}
    (c : BitString m) (hStar : ∀ u ∈ starSet m c, affine a b0 u = false) :
    a = (fun _ => false) ∧ b0 = false := by
  have hC : affine a b0 c = false := hStar c (Finset.mem_insert_self ..)
  have haZero : a = fun _ => false := by
    funext t
    have hT := hStar (Function.update c t (!(c t)))
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩))
    simp only [affine, dot_update_not] at hT
    simp only [affine] at hC
    cases hb : b0 <;> cases hd : dot a c <;> cases ha : a t <;> simp_all
  refine ⟨haZero, ?_⟩
  subst haZero
  simpa [affine, dot_zero_left] using hC

theorem card_starSet (m : ℕ) (c : BitString m) : (starSet m c).card = m + 1 := by
  classical
  have hcNotMem : c ∉ Finset.univ.image (fun t : Fin m => Function.update c t (!(c t))) := by
    intro hm
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hm
    have hv := congrFun ht t
    cases h : c t <;> simp_all
  have hInj : Function.Injective (fun t : Fin m => Function.update c t (!(c t))) := by
    intro t1 t2 hEq
    by_contra hne
    have hv := congrFun hEq t1
    simp [Function.update_of_ne hne] at hv
  rw [starSet, Finset.card_insert_of_notMem hcNotMem, Finset.card_image_of_injective _ hInj,
    Finset.card_univ, Fintype.card_fin]

private def hammingWeight {m : ℕ} (u : BitString m) : ℕ :=
  (Finset.univ.filter fun k => u k = true).card

private theorem hammingWeight_update_not {m : ℕ} (c : BitString m) (t : Fin m) :
    hammingWeight (Function.update c t (!(c t))) =
      if c t = true then hammingWeight c - 1 else hammingWeight c + 1 := by
  let S := Finset.univ.filter fun k => c k = true
  let S' := Finset.univ.filter fun k => Function.update c t (!(c t)) k = true
  change S'.card = if c t = true then S.card - 1 else S.card + 1
  by_cases hct : c t = true
  · have hEq : S' = S.erase t := by
      ext k
      by_cases hkt : k = t
      · subst hkt; simp [S', hct]
      · simp [S', S, hkt]
    have htS : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hct⟩
    rw [hEq, Finset.card_erase_of_mem htS]
    simp [hct]
  · have hEq : S' = insert t S := by
      ext k
      by_cases hkt : k = t
      · subst hkt; simp [S', Bool.eq_false_of_not_eq_true hct]
      · simp [S', S, hkt]
    have htNotS : t ∉ S := fun hm => hct (Finset.mem_filter.mp hm).2
    rw [hEq, Finset.card_insert_of_notMem htNotS]
    simp [hct]

/-- All-false center of the first affine star. -/
def starCenter0 (m : ℕ) : BitString m := fun _ => false

/-- All-true center of the second affine star. -/
def starCenter1 (m : ℕ) : BitString m := fun _ => true

/-- Weight-3 center of the third affine star. -/
def starCenter2 (m : ℕ) : BitString m := fun k => decide (k.val < 3)

private theorem starSets_pairwise_disjoint {m : ℕ} (hm : 6 ≤ m) :
    Disjoint (starSet m (starCenter0 m)) (starSet m (starCenter1 m)) ∧
    Disjoint (starSet m (starCenter0 m)) (starSet m (starCenter2 m)) ∧
    Disjoint (starSet m (starCenter1 m)) (starSet m (starCenter2 m)) := by
  have hw0 : ∀ u ∈ starSet m (starCenter0 m), hammingWeight u ≤ 1 := by
    intro u hu
    have hc0 : hammingWeight (starCenter0 m) = 0 := by
      simp [hammingWeight, starCenter0]
    rcases Finset.mem_insert.mp hu with rfl | hIm
    · omega
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hIm
      rw [hammingWeight_update_not]
      simp [starCenter0, hc0]
  have hw1 : ∀ u ∈ starSet m (starCenter1 m), m - 1 ≤ hammingWeight u := by
    intro u hu
    have hc1 : hammingWeight (starCenter1 m) = m := by
      simp [hammingWeight, starCenter1]
    rcases Finset.mem_insert.mp hu with rfl | hIm
    · omega
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hIm
      rw [hammingWeight_update_not]
      simp [starCenter1, hc1]
  have hw2 : ∀ u ∈ starSet m (starCenter2 m), 2 ≤ hammingWeight u ∧ hammingWeight u ≤ 4 := by
    intro u hu
    have hc2 : hammingWeight (starCenter2 m) = 3 := by
      have hEq : (Finset.univ.filter fun k : Fin m => starCenter2 m k = true) =
          {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, starCenter2, decide_eq_true_eq]
        constructor
        · intro hk
          have h012 : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
          rcases h012 with h | h | h
          · left; exact Fin.ext h
          · right; left; exact Fin.ext h
          · right; right; exact Fin.ext h
        · rintro (rfl | rfl | rfl) <;> dsimp <;> omega
      dsimp only [hammingWeight]
      rw [hEq, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [Fin.ext_iff]
      · simp [Fin.ext_iff]
    rcases Finset.mem_insert.mp hu with rfl | hIm
    · omega
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hIm
      rw [hammingWeight_update_not]
      split_ifs <;> omega
  refine ⟨Finset.disjoint_left.mpr fun u h0 h1 => ?_,
    Finset.disjoint_left.mpr fun u h0 h2 => ?_,
    Finset.disjoint_left.mpr fun u h1 h2 => ?_⟩
  · have := hw0 u h0; have := hw1 u h1; omega
  · have := hw0 u h0; have := hw2 u h2; omega
  · have := hw1 u h1; have := hw2 u h2; omega

/-- Index set of the affine star centered at `c`. -/
def starIdx (m : ℕ) (c : BitString m) : Finset (Fin (2 ^ m)) :=
  (starSet m c).image (BitString.equivFin m)

/-- Three-star affine mask of size `3 * (m + 1)`. -/
def starMask (m : ℕ) : Finset (Fin (2 ^ m)) :=
  starIdx m (starCenter0 m) ∪ starIdx m (starCenter1 m) ∪ starIdx m (starCenter2 m)

private theorem disjoint_image_inj {α β : Type*} [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) {s t : Finset α}
    (hst : Disjoint s t) : Disjoint (s.image f) (t.image f) := by
  refine Finset.disjoint_left.mpr fun b hbs hbt => ?_
  obtain ⟨a1, ha1, rfl⟩ := Finset.mem_image.mp hbs
  obtain ⟨a2, ha2, hEq⟩ := Finset.mem_image.mp hbt
  rw [hf hEq] at ha2
  exact Finset.disjoint_left.mp hst ha1 ha2

theorem card_starMask {m : ℕ} (hm : 6 ≤ m) : (starMask m).card = 3 * (m + 1) := by
  obtain ⟨hd01, hd02, hd12⟩ := starSets_pairwise_disjoint hm
  have hI01 : Disjoint (starIdx m (starCenter0 m)) (starIdx m (starCenter1 m)) :=
    disjoint_image_inj (BitString.equivFin m).injective hd01
  have hI02 : Disjoint (starIdx m (starCenter0 m)) (starIdx m (starCenter2 m)) :=
    disjoint_image_inj (BitString.equivFin m).injective hd02
  have hI12 : Disjoint (starIdx m (starCenter1 m)) (starIdx m (starCenter2 m)) :=
    disjoint_image_inj (BitString.equivFin m).injective hd12
  have hU12 : Disjoint (starIdx m (starCenter0 m) ∪ starIdx m (starCenter1 m))
      (starIdx m (starCenter2 m)) := Finset.disjoint_union_left.mpr ⟨hI02, hI12⟩
  rw [starMask, Finset.card_union_of_disjoint hU12, Finset.card_union_of_disjoint hI01]
  simp [starIdx, Finset.card_image_of_injective _ (BitString.equivFin m).injective, card_starSet]
  omega

/-- First `m + 1` coordinates of block `r` inside `Fin (K * b)`. -/
def blockPrefix (m K b : ℕ) (hm1 : m + 1 ≤ b) (r : Fin K) : Finset (Fin (K * b)) :=
  Finset.univ.image fun t : Fin (m + 1) => finProdFinEquiv (r, ⟨t.val, lt_of_lt_of_le t.isLt hm1⟩)

theorem exists_starBlockEquiv {m K b : ℕ} (hm : 6 ≤ m) (hK : 6 ≤ K) (hm1 : m + 1 ≤ b)
    (hMul : K * b = 2 ^ m) :
    ∃ e : Fin (K * b) ≃ Fin (2 ^ m),
      (∀ i ∈ starMask m, (finProdFinEquiv.symm (e.symm i)).1.val < 3) ∧
      (starIdx m (starCenter0 m) = (blockPrefix m K b hm1 ⟨0, by omega⟩).image e) ∧
      (starIdx m (starCenter1 m) = (blockPrefix m K b hm1 ⟨1, by omega⟩).image e) ∧
      (starIdx m (starCenter2 m) = (blockPrefix m K b hm1 ⟨2, by omega⟩).image e) := by
  classical
  let r0 : Fin K := ⟨0, by omega⟩
  let r1 : Fin K := ⟨1, by omega⟩
  let r2 : Fin K := ⟨2, by omega⟩
  let A0 := blockPrefix m K b hm1 r0
  let A1 := blockPrefix m K b hm1 r1
  let A2 := blockPrefix m K b hm1 r2
  let B0 := starIdx m (starCenter0 m)
  let B1 := starIdx m (starCenter1 m)
  let B2 := starIdx m (starCenter2 m)
  have hBlkCard (r : Fin K) : (blockPrefix m K b hm1 r).card = m + 1 := by
    rw [blockPrefix, Finset.card_image_of_injective]
    · simp
    · intro t1 t2 hEq
      have hp := congrArg Prod.snd (finProdFinEquiv.injective hEq)
      exact Fin.ext (by simpa using congrArg Fin.val hp)
  have hBlkDisj {r r' : Fin K} (hrr' : r ≠ r') :
      Disjoint (blockPrefix m K b hm1 r) (blockPrefix m K b hm1 r') := by
    refine Finset.disjoint_left.mpr fun q hq hq' => ?_
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨t', _, hEq⟩ := Finset.mem_image.mp hq'
    exact hrr' (congrArg Prod.fst (finProdFinEquiv.injective hEq)).symm
  obtain ⟨hd01, hd02, hd12⟩ := starSets_pairwise_disjoint hm
  have hB01 : Disjoint B0 B1 := disjoint_image_inj (BitString.equivFin m).injective hd01
  have hB02 : Disjoint B0 B2 := disjoint_image_inj (BitString.equivFin m).injective hd02
  have hB12 : Disjoint B1 B2 := disjoint_image_inj (BitString.equivFin m).injective hd12
  have hStarC (c : BitString m) : (starIdx m c).card = m + 1 := by
    rw [starIdx, Finset.card_image_of_injective _ (BitString.equivFin m).injective, card_starSet]
  have hC0 : A0.card = B0.card := (hBlkCard r0).trans (hStarC _).symm
  have hC1 : A1.card = B1.card := (hBlkCard r1).trans (hStarC _).symm
  have hC2 : A2.card = B2.card := (hBlkCard r2).trans (hStarC _).symm
  have hA01 : Disjoint A0 A1 := hBlkDisj (by intro h; have := congrArg Fin.val h; simp [r0, r1] at this)
  have hA02 : Disjoint A0 A2 := hBlkDisj (by intro h; have := congrArg Fin.val h; simp [r0, r2] at this)
  have hA12 : Disjoint A1 A2 := hBlkDisj (by intro h; have := congrArg Fin.val h; simp [r1, r2] at this)
  have hTot : Fintype.card (Fin (K * b)) = Fintype.card (Fin (2 ^ m)) := by
    simp [hMul]
  obtain ⟨e, he0, he1, he2⟩ := equivOfThreeDisjoint A0 A1 A2 B0 B1 B2
    hA01 hA02 hA12 hB01 hB02 hB12 hC0 hC1 hC2 hTot
  have hImg (A : Finset (Fin (K * b))) (B : Finset (Fin (2 ^ m)))
      (heAB : ∀ q, q ∈ A ↔ e q ∈ B) : B = A.image e := by
    ext i
    rw [Finset.mem_image]
    constructor
    · intro hi
      refine ⟨e.symm i, (heAB (e.symm i)).mpr (by simpa using hi), e.apply_symm_apply i⟩
    · rintro ⟨q, hq, rfl⟩
      exact (heAB q).mp hq
  have hBlkFst (r : Fin K) {q : Fin (K * b)} (hq : q ∈ blockPrefix m K b hm1 r) :
      (finProdFinEquiv.symm q).1 = r := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hq
    simp
  refine ⟨e, ?_, hImg A0 B0 he0, hImg A1 B1 he1, hImg A2 B2 he2⟩
  intro i hi
  have hMem : i ∈ B0 ∨ i ∈ B1 ∨ i ∈ B2 := by
    simpa [starMask, B0, B1, B2, or_assoc] using hi
  rcases hMem with h0 | h1 | h2
  · have hq : e.symm i ∈ A0 := (he0 (e.symm i)).mpr (by simpa using h0)
    rw [hBlkFst r0 hq]; dsimp [r0]; omega
  · have hq : e.symm i ∈ A1 := (he1 (e.symm i)).mpr (by simpa using h1)
    rw [hBlkFst r1 hq]; dsimp [r1]; omega
  · have hq : e.symm i ∈ A2 := (he2 (e.symm i)).mpr (by simpa using h2)
    rw [hBlkFst r2 hq]; dsimp [r2]; omega

/-- Entrywise XOR of two `n`-bit truth tables. -/
def xorTable {n : ℕ} (T1 T2 : BitString n) : BitString n :=
  fun i => T1 i ^^ T2 i

/-- Affine-invariant block-at-most-one barrier function: accepts truth tables `T` whose XOR
with some affine table passes `blockAtMostOne K b` along `e`. -/
noncomputable def affineBlockAtMostOne (m K b : ℕ) (e : Fin (K * b) ≃ Fin (2 ^ m)) :
    BooleanFunction (2 ^ m) := open scoped Classical in
  fun T => decide (∃ (a : BitString m) (b0 : Bool),
    blockAtMostOne K b (fun q => xorTable T (MCSP.truthTable m (affine a b0)) (e q)) = true)

theorem affineBlockAtMostOne_accepts_affine (m K b : ℕ) (e : Fin (K * b) ≃ Fin (2 ^ m))
    (a : BitString m) (b0 : Bool) :
    affineBlockAtMostOne m K b e (MCSP.truthTable m (affine a b0)) = true := by
  classical
  simp only [affineBlockAtMostOne, decide_eq_true_eq]
  refine ⟨a, b0, ?_⟩
  have hZero : (fun q => xorTable (MCSP.truthTable m (affine a b0))
      (MCSP.truthTable m (affine a b0)) (e q)) = fun _ => false := by
    funext q
    simp [xorTable]
  rw [hZero]
  exact blockAtMostOne_zero K b

theorem affineBlockAtMostOne_accepts_affine_flip (m K b : ℕ) (e : Fin (K * b) ≃ Fin (2 ^ m))
    (a : BitString m) (b0 : Bool) (i : Fin (2 ^ m)) :
    affineBlockAtMostOne m K b e
      (Function.update (MCSP.truthTable m (affine a b0)) i
        (!(MCSP.truthTable m (affine a b0) i))) = true := by
  simp only [affineBlockAtMostOne, decide_eq_true_eq]
  refine ⟨a, b0, ?_⟩
  let y := fun q : Fin (K * b) =>
    xorTable (Function.update (MCSP.truthTable m (affine a b0)) i
      (!(MCSP.truthTable m (affine a b0) i))) (MCSP.truthTable m (affine a b0)) (e q)
  by_cases hKB : 0 < K ∧ 0 < b
  · let q0 := e.symm i
    let r0 := (finProdFinEquiv.symm q0).1
    have hSub : (Finset.univ.filter fun r : Fin K => blockOr K b r y = true) ⊆ {r0} := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockOr, decide_eq_true_eq] at hr
      obtain ⟨s, hs⟩ := hr
      have hEqI : e (finProdFinEquiv (r, s)) = i := by
        by_contra hne
        have hF : y (finProdFinEquiv (r, s)) = false := by
          simp [y, xorTable, Function.update_of_ne hne]
        rw [hF] at hs
        cases hs
      have hqEq : finProdFinEquiv (r, s) = q0 := e.injective (hEqI.trans (e.apply_symm_apply i).symm)
      have hp := congrArg finProdFinEquiv.symm hqEq
      simp only [Equiv.symm_apply_apply] at hp
      exact Finset.mem_singleton.mpr (congrArg Prod.fst hp)
    have hCard : (Finset.univ.filter fun r : Fin K => blockOr K b r y = true).card ≤ 1 :=
      (Finset.card_le_card hSub).trans (Finset.card_singleton _).le
    show blockAtMostOne K b y = true
    rw [blockAtMostOne, decide_eq_true_eq]
    exact hCard
  · have hK0 : K = 0 ∨ b = 0 := by omega
    rcases hK0 with rfl | rfl
    · simp [blockAtMostOne]
    · simp [blockAtMostOne, blockOr]

theorem affineBlockAtMostOne_accepting_card (m K b : ℕ) (e : Fin (K * b) ≃ Fin (2 ^ m)) :
    (acceptingTables (affineBlockAtMostOne m K b e)).card ≤ 2 ^ (m + 1) * (1 + K * 2 ^ b) := by
  classical
  let dec := (Finset.univ : Finset (BitString m × Bool)) ×ˢ acceptingTables (blockAtMostOne K b)
  let Φ (p : (BitString m × Bool) × BitString (K * b)) : BitString (2 ^ m) :=
    fun i => p.2 (e.symm i) ^^ MCSP.truthTable m (affine p.1.1 p.1.2) i
  have hSub : acceptingTables (affineBlockAtMostOne m K b e) ⊆ dec.image Φ := by
    intro T hT
    have hAcc : affineBlockAtMostOne m K b e T = true := (Finset.mem_filter.mp hT).2
    simp only [affineBlockAtMostOne, decide_eq_true_eq] at hAcc
    obtain ⟨a, b0, hy⟩ := hAcc
    let y : BitString (K * b) := fun q => xorTable T (MCSP.truthTable m (affine a b0)) (e q)
    have hyAcc : y ∈ acceptingTables (blockAtMostOne K b) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    refine Finset.mem_image.mpr ⟨((a, b0), y), Finset.mem_product.mpr ⟨Finset.mem_univ _, hyAcc⟩, ?_⟩
    funext i
    dsimp [Φ, y, xorTable]
    rw [e.apply_symm_apply, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
  have hCardAff : (Finset.univ : Finset (BitString m × Bool)).card = 2 ^ (m + 1) := by
    simp [BitString, Fintype.card_prod, Fintype.card_bool, pow_succ']
    ring
  calc
    (acceptingTables (affineBlockAtMostOne m K b e)).card ≤ (dec.image Φ).card :=
      Finset.card_le_card hSub
    _ ≤ dec.card := Finset.card_image_le
    _ = (Finset.univ : Finset (BitString m × Bool)).card *
        (acceptingTables (blockAtMostOne K b)).card := Finset.card_product ..
    _ ≤ 2 ^ (m + 1) * (1 + K * 2 ^ b) := by
      rw [hCardAff]
      exact Nat.mul_le_mul_left _ (blockAtMostOne_accepting_card K b)

theorem affineBlockAtMostOne_branches_nonconstant {m K b B : ℕ}
    (e : Fin (K * b) ≃ Fin (2 ^ m))
    (hSparse : (acceptingTables (affineBlockAtMostOne m K b e)).card ≤ 2 ^ B)
    (a : BitString m) (b0 : Bool) (Q : Finset (Fin (2 ^ m)))
    (i : Fin (2 ^ m)) (hi : i ∉ Q) (hFree : Q.card + B + 1 < 2 ^ m) (v : Bool) :
    ∃ y z : BitString (2 ^ m),
      affineBlockAtMostOne m K b e
          (substitute (branchPin (MCSP.truthTable m (affine a b0)) Q i v) y) ≠
        affineBlockAtMostOne m K b e
          (substitute (branchPin (MCSP.truthTable m (affine a b0)) Q i v) z) := by
  let x := MCSP.truthTable m (affine a b0)
  let center := Function.update x i v
  have hCenterAcc : affineBlockAtMostOne m K b e center = true := by
    by_cases hv : v = x i
    · have hId : center = x := by dsimp [center]; rw [hv, Function.update_eq_self]
      rw [hId]
      exact affineBlockAtMostOne_accepts_affine m K b e a b0
    · have hOpp : v = !(x i) := by cases v <;> cases h : x i <;> simp_all
      dsimp only [center]
      rw [hOpp]
      exact affineBlockAtMostOne_accepts_affine_flip m K b e a b0 i
  have hCenterSub : substitute (branchPin x Q i v) center = center := by
    funext u
    by_cases hui : u = i
    · subst hui; simp [substitute, branchPin, pinAt, center]
    · by_cases huQ : u ∈ Q
      · simp [substitute, branchPin, pinAt, hui, huQ, center]
      · simp [substitute, branchPin, pinAt, hui, huQ]
  have hNotAllTrue : ∃ z : BitString (2 ^ m),
      affineBlockAtMostOne m K b e (substitute (branchPin x Q i v) z) = false := by
    by_contra h
    push Not at h
    have hForce : ∀ z : BitString (2 ^ m), (∀ u ∈ insert i Q, z u = center u) →
        affineBlockAtMostOne m K b e z = true := by
      intro z hz
      have hSubZ : substitute (branchPin x Q i v) z = z := by
        funext u
        by_cases hui : u = i
        · subst hui
          have h1 := hz u (Finset.mem_insert_self ..)
          simpa [center, substitute, branchPin, pinAt] using h1.symm
        · by_cases huQ : u ∈ Q
          · have h1 := hz u (Finset.mem_insert_of_mem huQ)
            simpa [center, substitute, branchPin, pinAt, hui, huQ,
              Function.update_of_ne hui] using h1.symm
          · simp [substitute, branchPin, pinAt, hui, huQ]
      rw [← hSubZ]
      exact Bool.eq_true_of_not_eq_false (h z)
    have hCount := card_masked_le hSparse center (insert i Q) hForce
    rw [Finset.card_insert_of_notMem hi] at hCount
    omega
  obtain ⟨z, hzF⟩ := hNotAllTrue
  refine ⟨center, z, ?_⟩
  rw [hCenterSub, hCenterAcc, hzF]
  decide

theorem affineBlockAtMostOne_pin_eq_blockAtMostOne {m K b : ℕ} (_hm : 6 ≤ m) (hK : 6 ≤ K)
    (hm1 : m + 1 ≤ b) (e : Fin (K * b) ≃ Fin (2 ^ m))
    (hImg0 : starIdx m (starCenter0 m) = (blockPrefix m K b hm1 ⟨0, by omega⟩).image e)
    (hImg1 : starIdx m (starCenter1 m) = (blockPrefix m K b hm1 ⟨1, by omega⟩).image e)
    (hImg2 : starIdx m (starCenter2 m) = (blockPrefix m K b hm1 ⟨2, by omega⟩).image e)
    (z : BitString (2 ^ m)) :
    affineBlockAtMostOne m K b e (substitute (pinAt (fun _ => false) (starMask m)) z) =
      blockAtMostOne K b (fun q => substitute (pinAt (fun _ => false) (starMask m)) z (e q)) := by
  classical
  let T' := substitute (pinAt (fun _ => false) (starMask m)) z
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hAcc
    simp only [affineBlockAtMostOne, decide_eq_true_eq] at hAcc
    obtain ⟨a, b0, hBlock⟩ := hAcc
    let act := Finset.univ.filter fun r : Fin K =>
      blockOr K b r (fun q => xorTable T' (MCSP.truthTable m (affine a b0)) (e q)) = true
    have hCardLe : act.card ≤ 1 := by
      simpa [blockAtMostOne, act] using hBlock
    let r0 : Fin K := ⟨0, by omega⟩
    let r1 : Fin K := ⟨1, by omega⟩
    let r2 : Fin K := ⟨2, by omega⟩
    have hThree : ({r0, r1, r2} : Finset (Fin K)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [r1, r2, Fin.ext_iff]
      · simp [r0, r1, r2, Fin.ext_iff]
    have hNotAll : ∃ r ∈ ({r0, r1, r2} : Finset (Fin K)), r ∉ act := by
      by_contra hAll
      push Not at hAll
      have hSub : ({r0, r1, r2} : Finset (Fin K)) ⊆ act := hAll
      have := (Finset.card_le_card hSub).trans hCardLe
      omega
    obtain ⟨r, hrMem, hrNotAct⟩ := hNotAll
    have hrFalse : ∀ s : Fin b,
        xorTable T' (MCSP.truthTable m (affine a b0)) (e (finProdFinEquiv (r, s))) = false := by
      intro s
      by_contra hTrue
      have hXT : xorTable T' (MCSP.truthTable m (affine a b0)) (e (finProdFinEquiv (r, s))) = true :=
        Bool.eq_true_of_not_eq_false hTrue
      exact hrNotAct (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simp only [blockOr, decide_eq_true_eq]; exact ⟨s, hXT⟩⟩)
    have hZeroOnStar (c : BitString m)
        (hcIdx : starIdx m c = (blockPrefix m K b hm1 r).image e)
        (hcMask : starIdx m c ⊆ starMask m) :
        a = (fun _ => false) ∧ b0 = false := by
      apply affine_eq_zero_of_zero_on_star c
      intro u hu
      have hiIdx : BitString.equivFin m u ∈ starIdx m c := Finset.mem_image.mpr ⟨u, hu, rfl⟩
      have hiMask : BitString.equivFin m u ∈ starMask m := hcMask hiIdx
      rw [hcIdx, Finset.mem_image] at hiIdx
      obtain ⟨q, hqPref, hEqQ⟩ := hiIdx
      rw [blockPrefix, Finset.mem_image] at hqPref
      obtain ⟨t, _, rfl⟩ := hqPref
      have hTZero : T' (e (finProdFinEquiv (r, ⟨t.val, lt_of_lt_of_le t.isLt hm1⟩))) = false := by
        dsimp only [T']
        rw [hEqQ]
        simp [substitute, pinAt, hiMask]
      have hX := hrFalse ⟨t.val, lt_of_lt_of_le t.isLt hm1⟩
      rw [xorTable, hTZero, hEqQ] at hX
      simpa [MCSP.truthTable_apply, Equiv.symm_apply_apply] using hX
    have hAB : a = (fun _ => false) ∧ b0 = false := by
      rcases Finset.mem_insert.mp hrMem with rfl | hr12
      · exact hZeroOnStar (starCenter0 m) hImg0
          (by unfold starMask; exact Finset.subset_union_left.trans Finset.subset_union_left)
      · rcases Finset.mem_insert.mp hr12 with rfl | hr2
        · exact hZeroOnStar (starCenter1 m) hImg1
            (by unfold starMask; exact Finset.subset_union_right.trans Finset.subset_union_left)
        · rcases Finset.mem_singleton.mp hr2 with rfl
          exact hZeroOnStar (starCenter2 m) hImg2
            (by unfold starMask; exact Finset.subset_union_right)
    rcases hAB with ⟨rfl, rfl⟩
    have hAffZero : MCSP.truthTable m (affine (fun _ => false) false) = fun _ => false := by
      funext u
      simp [MCSP.truthTable_apply, affine, dot_zero_left]
    have hXEq : (fun q => xorTable T' (MCSP.truthTable m (affine (fun _ => false) false)) (e q)) =
        fun q => T' (e q) := by
      funext q
      rw [xorTable, hAffZero]
      simp
    rwa [hXEq] at hBlock
  · intro hBlock
    simp only [affineBlockAtMostOne, decide_eq_true_eq]
    refine ⟨fun _ => false, false, ?_⟩
    have hAffZero : MCSP.truthTable m (affine (fun _ => false) false) = fun _ => false := by
      funext u
      simp [MCSP.truthTable_apply, affine, dot_zero_left]
    rw [hAffZero]
    simpa [xorTable] using hBlock

theorem affineBlockAtMostOne_has_essential_funnel {m K b : ℕ} (hm : 6 ≤ m) (hK : 6 ≤ K)
    (hm1 : m + 1 ≤ b) (e : Fin (K * b) ≃ Fin (2 ^ m))
    (hMaskBlk : ∀ i ∈ starMask m, (finProdFinEquiv.symm (e.symm i)).1.val < 3)
    (hImg0 : starIdx m (starCenter0 m) = (blockPrefix m K b hm1 ⟨0, by omega⟩).image e)
    (hImg1 : starIdx m (starCenter1 m) = (blockPrefix m K b hm1 ⟨1, by omega⟩).image e)
    (hImg2 : starIdx m (starCenter2 m) = (blockPrefix m K b hm1 ⟨2, by omega⟩).image e)
    (r : Fin K) (hr : 3 ≤ r.val) {s1 s2 : Fin b} (hne : s1 ≠ s2) :
    let i := e (finProdFinEquiv (r, s1))
    let j := e (finProdFinEquiv (r, s2))
    let fPin : BooleanFunction (2 ^ m) := fun z =>
      affineBlockAtMostOne m K b e (substitute (pinAt (fun _ => false) (starMask m)) z)
    i ∈ essMask (affineBlockAtMostOne m K b e) (fun _ => false) (starMask m) ∧
    j ∈ essMask (affineBlockAtMostOne m K b e) (fun _ => false) (starMask m) ∧
    IsPairFunnel fPin i j true := by
  classical
  dsimp only
  let ρ := pinAt (fun _ => false) (starMask m)
  let i := e (finProdFinEquiv (r, s1))
  let j := e (finProdFinEquiv (r, s2))
  let fPin : BooleanFunction (2 ^ m) := fun z => affineBlockAtMostOne m K b e (substitute ρ z)
  have hFreeBlock (r' : Fin K) (hr' : 3 ≤ r'.val) (s : Fin b) :
      e (finProdFinEquiv (r', s)) ∉ starMask m := by
    intro hMem
    have hLt := hMaskBlk _ hMem
    simp only [Equiv.symm_apply_apply] at hLt
    omega
  have hEssOfBlock (r' : Fin K) (hr' : 3 ≤ r'.val) (s : Fin b) :
      e (finProdFinEquiv (r', s)) ∈ essMask (affineBlockAtMostOne m K b e) (fun _ => false) (starMask m) := by
    let idx := e (finProdFinEquiv (r', s))
    have hNotMask : idx ∉ starMask m := hFreeBlock r' hr' s
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hNotMask⟩, ?_⟩
    let rOther : Fin K := if r'.val = 3 then ⟨4, by omega⟩ else ⟨3, by omega⟩
    have hrOther3 : 3 ≤ rOther.val := by
      dsimp [rOther]; split_ifs <;> dsimp <;> omega
    have hrOtherNe : rOther ≠ r' := by
      intro hEq
      have hv := congrArg Fin.val hEq
      by_cases h3 : r'.val = 3
      · simp [rOther, h3] at hv
      · simp [rOther, h3] at hv
        exact h3 hv.symm
    let s0 : Fin b := ⟨0, by omega⟩
    let idxOther := e (finProdFinEquiv (rOther, s0))
    let y : BitString (2 ^ m) := fun u => decide (u = idxOther)
    let z : BitString (2 ^ m) := fun u => decide (u = idxOther ∨ u = idx)
    have hAgree : ∀ u ≠ idx, y u = z u := by
      intro u hu
      simp [y, z, hu]
    have hEqPin (w : BitString (2 ^ m)) :
        affineBlockAtMostOne m K b e (substitute ρ w) =
          blockAtMostOne K b (fun q => substitute ρ w (e q)) :=
      affineBlockAtMostOne_pin_eq_blockAtMostOne hm hK hm1 e hImg0 hImg1 hImg2 w
    have hYTrue : blockAtMostOne K b (fun q => substitute ρ y (e q)) = true := by
      have hSub : (Finset.univ.filter fun blk : Fin K =>
          blockOr K b blk (fun q => substitute ρ y (e q)) = true) ⊆ {rOther} := by
        intro blk hblk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockOr, decide_eq_true_eq] at hblk
        obtain ⟨sb, hsb⟩ := hblk
        have hNotM : e (finProdFinEquiv (blk, sb)) ∉ starMask m := by
          intro hm'
          have hSubY : substitute ρ y (e (finProdFinEquiv (blk, sb))) = false := by
            simp [ρ, substitute, pinAt, hm']
          rw [hSubY] at hsb; cases hsb
        have hEqO : e (finProdFinEquiv (blk, sb)) = idxOther := by
          by_contra hne
          have hYF : substitute ρ y (e (finProdFinEquiv (blk, sb))) = false := by
            simp [ρ, substitute, pinAt, hNotM, y, hne]
          rw [hYF] at hsb; cases hsb
        have hp := congrArg (fun u => (finProdFinEquiv.symm (e.symm u)).1) hEqO
        simp only [idxOther, Equiv.symm_apply_apply] at hp
        exact Finset.mem_singleton.mpr hp
      have hC := (Finset.card_le_card hSub).trans (Finset.card_singleton _).le
      simpa [blockAtMostOne] using hC
    have hZFalse : blockAtMostOne K b (fun q => substitute ρ z (e q)) = false := by
      let act := Finset.univ.filter fun blk : Fin K =>
        blockOr K b blk (fun q => substitute ρ z (e q)) = true
      have hO : rOther ∈ act := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [blockOr, decide_eq_true_eq]
        refine ⟨s0, ?_⟩
        have hN := hFreeBlock rOther hrOther3 s0
        simp [ρ, substitute, pinAt, hN, z, idxOther]
      have hR : r' ∈ act := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [blockOr, decide_eq_true_eq]
        refine ⟨s, ?_⟩
        simp [ρ, substitute, pinAt, hNotMask, z, idx]
      have hTwo : 1 < act.card := Finset.one_lt_card.mpr ⟨rOther, hO, r', hR, hrOtherNe⟩
      have hNotLe : ¬ act.card ≤ 1 := by omega
      simpa [blockAtMostOne, act] using hNotLe
    refine ⟨y, z, hAgree, ?_⟩
    change affineBlockAtMostOne m K b e (substitute ρ y) ≠
      affineBlockAtMostOne m K b e (substitute ρ z)
    rw [hEqPin y, hEqPin z, hYTrue, hZFalse]
    decide
  refine ⟨hEssOfBlock r hr s1, hEssOfBlock r hr s2, ?_⟩
  have hij : i ≠ j := fun h => hne (congrArg Prod.snd (finProdFinEquiv.injective (e.injective h)))
  have hSubUpdate (z : BitString (2 ^ m)) (a b : Bool) :
      (fun q => substitute ρ (Function.update (Function.update z i a) j b) (e q)) =
        Function.update (Function.update (fun q => substitute ρ z (e q))
          (finProdFinEquiv (r, s1)) a) (finProdFinEquiv (r, s2)) b := by
    funext q
    by_cases hq2 : q = finProdFinEquiv (r, s2)
    · subst hq2
      have hNotM : j ∉ starMask m := hFreeBlock r hr s2
      change substitute ρ (Function.update (Function.update z i a) j b) j =
        Function.update (Function.update (fun q => substitute ρ z (e q))
          (finProdFinEquiv (r, s1)) a) (finProdFinEquiv (r, s2)) b (finProdFinEquiv (r, s2))
      simp [ρ, substitute, pinAt, hNotM]
    · by_cases hq1 : q = finProdFinEquiv (r, s1)
      · subst hq1
        have hNotM : i ∉ starMask m := hFreeBlock r hr s1
        change substitute ρ (Function.update (Function.update z i a) j b) i =
          Function.update (Function.update (fun q => substitute ρ z (e q))
            (finProdFinEquiv (r, s1)) a) (finProdFinEquiv (r, s2)) b (finProdFinEquiv (r, s1))
        simp [ρ, substitute, pinAt, hNotM, hij, hq2]
      · have hNe1 : e q ≠ i := fun h => hq1 (e.injective h)
        have hNe2 : e q ≠ j := fun h => hq2 (e.injective h)
        by_cases hm' : e q ∈ starMask m
        · simp [ρ, substitute, pinAt, hm', hq2, hq1]
        · simp [ρ, substitute, pinAt, hm', hNe2, hNe1, hq2, hq1]
  have hPinEq (w : BitString (2 ^ m)) :
      fPin w = blockAtMostOne K b (fun q => substitute ρ w (e q)) :=
    affineBlockAtMostOne_pin_eq_blockAtMostOne hm hK hm1 e hImg0 hImg1 hImg2 w
  refine ⟨hij, ?_, ?_⟩
  · intro z
    change fPin (Function.update (Function.update z i true) j (!true)) =
      fPin (Function.update (Function.update z i (!true)) j true)
    rw [hPinEq, hPinEq, hSubUpdate z true (!true), hSubUpdate z (!true) true]
    exact (blockAtMostOne_has_funnel r hne).2.1 (fun q => substitute ρ z (e q))
  · intro z
    change fPin (Function.update (Function.update z i true) j (!true)) =
      fPin (Function.update (Function.update z i true) j true)
    rw [hPinEq, hPinEq, hSubUpdate z true (!true), hSubUpdate z true true]
    exact (blockAtMostOne_has_funnel r hne).2.2 (fun q => substitute ρ z (e q))

theorem affineBlockAtMostOne_pin_complexity_le {m K b : ℕ} (hm : 6 ≤ m) (hK : 6 ≤ K)
    (hm1 : m + 1 ≤ b) (e : Fin (K * b) ≃ Fin (2 ^ m))
    (hImg0 : starIdx m (starCenter0 m) = (blockPrefix m K b hm1 ⟨0, by omega⟩).image e)
    (hImg1 : starIdx m (starCenter1 m) = (blockPrefix m K b hm1 ⟨1, by omega⟩).image e)
    (hImg2 : starIdx m (starCenter2 m) = (blockPrefix m K b hm1 ⟨2, by omega⟩).image e) :
    complexity interpretation (single fun z =>
      affineBlockAtMostOne m K b e (substitute (pinAt (fun _ => false) (starMask m)) z)) ≤
        K * b + 2 * K - 1 := by
  have hb1 : 1 ≤ b := by omega
  obtain ⟨c, hc, hCSize⟩ := exists_computes_size_eq_complexity (I := interpretation)
    (f := single (blockAtMostOne K b))
  have hCLe := hCSize.symm ▸ blockAtMostOne_complexity_le (K := K) (b := b) (by omega) hb1
  let wCirc : Circuit signature (2 ^ m) (K * b) := Circuit.wiring signature (fun q => e q)
  let d : Circuit signature (2 ^ m) 1 := c.comp wCirc
  have hdComp : d.Computes interpretation (single fun z => blockAtMostOne K b (fun q => z (e q))) := by
    intro z
    funext o
    have hEval : d.eval interpretation z o = c.eval interpretation (wCirc.eval interpretation z) o := by
      simp [d]
    rw [hEval, hc]
    rfl
  let ρ := pinAt (fun _ => false) (starMask m)
  have hRes : restrictedWire d.program ρ (d.outputs 0) = fun z =>
      affineBlockAtMostOne m K b e (substitute ρ z) := by
    rw [NestedFaces.restricted_circuit_eq d hdComp ρ]
    funext z
    exact (affineBlockAtMostOne_pin_eq_blockAtMostOne hm hK hm1 e hImg0 hImg1 hImg2 z).symm
  have hFresh := fresh_complexity_le d.program ρ (d.outputs 0)
  rw [hRes] at hFresh
  have hCardLe : (fresh d.program ρ).card ≤ d.size :=
    (Finset.card_le_univ _).trans (by simp)
  have hdSize : d.size = c.size := by
    simp [d, wCirc, Circuit.size_comp, Circuit.size_wiring]
  dsimp only [ρ] at hFresh hCardLe
  omega

/-- Concrete `m = 14` (`N = 16384`) barrier: `affineBlockAtMostOne 14 1024 16 e` satisfies
`mcspSquare 14` sparsity (`≤ 2 ^ descriptionBitBound 14`), accepts all affine tables and
all 1-bit affine flips, keeps all small 1-bit branches nonconstant, and at the `45`-bit
affine mask `starMask 14` exhibits an essential `IsPairFunnel` with residual complexity
`≤ 18431 < 25286 = 2 * (2 ^ 14 - descriptionBitBound 14 - 1)`. -/
theorem affineBlockAtMostOne_barrier_at_14 :
    ∃ e : Fin (1024 * 16) ≃ Fin (2 ^ 14),
      let f := affineBlockAtMostOne 14 1024 16 e
      (acceptingTables f).card ≤ 2 ^ descriptionBitBound 14 ∧
      (∀ a b0, f (MCSP.truthTable 14 (affine a b0)) = true) ∧
      (∀ a b0 i, f (Function.update (MCSP.truthTable 14 (affine a b0)) i
        (!(MCSP.truthTable 14 (affine a b0) i))) = true) ∧
      (∀ a b0 Q i, i ∉ Q → Q.card + descriptionBitBound 14 + 1 < 2 ^ 14 → ∀ v : Bool,
        ∃ y z, f (substitute (branchPin (MCSP.truthTable 14 (affine a b0)) Q i v) y) ≠
          f (substitute (branchPin (MCSP.truthTable 14 (affine a b0)) Q i v) z)) ∧
      (starMask 14).card = 45 ∧
      (∃ i ∈ essMask f (fun _ => false) (starMask 14),
        ∃ j ∈ essMask f (fun _ => false) (starMask 14),
          IsPairFunnel (fun z => f (substitute (pinAt (fun _ => false) (starMask 14)) z)) i j true) ∧
      complexity interpretation (single fun z => f (substitute (pinAt (fun _ => false) (starMask 14)) z)) ≤ 18431 ∧
      18431 < 2 * (2 ^ 14 - descriptionBitBound 14 - 1) := by
  obtain ⟨e, hMaskBlk, hImg0, hImg1, hImg2⟩ :=
    exists_starBlockEquiv (m := 14) (K := 1024) (b := 16) (by decide) (by decide) (by decide) (by decide)
  have hB14 : descriptionBitBound 14 = 3740 := by decide
  have hSparseSmall : (acceptingTables (affineBlockAtMostOne 14 1024 16 e)).card ≤ 2 ^ 42 :=
    (affineBlockAtMostOne_accepting_card 14 1024 16 e).trans (by decide)
  have hSparse : (acceptingTables (affineBlockAtMostOne 14 1024 16 e)).card ≤
      2 ^ descriptionBitBound 14 :=
    hSparseSmall.trans (Nat.pow_le_pow_right (by decide) (by rw [hB14]; decide))
  have hFunnel := affineBlockAtMostOne_has_essential_funnel (m := 14) (K := 1024) (b := 16)
    (by decide) (by decide) (by decide) e hMaskBlk hImg0 hImg1 hImg2 ⟨3, by decide⟩ (by decide)
    (s1 := ⟨0, by decide⟩) (s2 := ⟨1, by decide⟩) (by decide)
  have hComp := (affineBlockAtMostOne_pin_complexity_le (m := 14) (K := 1024) (b := 16)
    (by decide) (by decide) (by decide) e hImg0 hImg1 hImg2).trans
    (by decide : 1024 * 16 + 2 * 1024 - 1 ≤ 18431)
  refine ⟨e, hSparse, affineBlockAtMostOne_accepts_affine 14 1024 16 e,
    affineBlockAtMostOne_accepts_affine_flip 14 1024 16 e, ?_,
    card_starMask (m := 14) (by decide), ⟨_, hFunnel.1, _, hFunnel.2.1, hFunnel.2.2⟩, hComp, ?_⟩
  · intro a b0 Q i hi hFree v
    exact affineBlockAtMostOne_branches_nonconstant e hSparse a b0 Q i hi hFree v
  · rw [hB14]; decide

/-- Concrete `m = 32` (`N = 2 ^ 32`) barrier: `affineBlockAtMostOne 32 (2 ^ 26) 64 e`
satisfies `mcspSquare 32` sparsity (`≤ 2 ^ 27672`), accepts all affine tables and 1-bit affine
flips, keeps all small 1-bit branches nonconstant, and at the `99`-bit affine mask `starMask 32`
exhibits an essential `IsPairFunnel` with residual complexity
`≤ 4429185023 < 8589879246 = 2 * (2 ^ 32 - descriptionBitBound 32 - 1)`. -/
theorem affineBlockAtMostOne_barrier_at_32 :
    ∃ e : Fin ((2 ^ 26) * 64) ≃ Fin (2 ^ 32),
      let f := affineBlockAtMostOne 32 (2 ^ 26) 64 e
      (acceptingTables f).card ≤ 2 ^ descriptionBitBound 32 ∧
      (∀ a b0, f (MCSP.truthTable 32 (affine a b0)) = true) ∧
      (∀ a b0 i, f (Function.update (MCSP.truthTable 32 (affine a b0)) i
        (!(MCSP.truthTable 32 (affine a b0) i))) = true) ∧
      (∀ a b0 Q i, i ∉ Q → Q.card + descriptionBitBound 32 + 1 < 2 ^ 32 → ∀ v : Bool,
        ∃ y z, f (substitute (branchPin (MCSP.truthTable 32 (affine a b0)) Q i v) y) ≠
          f (substitute (branchPin (MCSP.truthTable 32 (affine a b0)) Q i v) z)) ∧
      (starMask 32).card = 99 ∧
      (∃ i ∈ essMask f (fun _ => false) (starMask 32),
        ∃ j ∈ essMask f (fun _ => false) (starMask 32),
          IsPairFunnel (fun z => f (substitute (pinAt (fun _ => false) (starMask 32)) z)) i j true) ∧
      complexity interpretation (single fun z => f (substitute (pinAt (fun _ => false) (starMask 32)) z)) ≤ 4429185023 ∧
      4429185023 < 2 * (2 ^ 32 - descriptionBitBound 32 - 1) := by
  obtain ⟨e, hMaskBlk, hImg0, hImg1, hImg2⟩ :=
    exists_starBlockEquiv (m := 32) (K := 2 ^ 26) (b := 64) (by decide) (by decide) (by decide) (by decide)
  have hB32 : descriptionBitBound 32 = 27672 := by decide
  have hStepSmall : 2 ^ (32 + 1) * (1 + 2 ^ 26 * 2 ^ 64) ≤ 2 ^ 124 := by
    have h1 : 1 + 2 ^ 26 * 2 ^ 64 ≤ 2 ^ 91 := by decide
    calc
      2 ^ (32 + 1) * (1 + 2 ^ 26 * 2 ^ 64) ≤ 2 ^ 33 * 2 ^ 91 := Nat.mul_le_mul_left _ h1
      _ = 2 ^ 124 := by rw [← pow_add]
  have hSparseSmall : (acceptingTables (affineBlockAtMostOne 32 (2 ^ 26) 64 e)).card ≤ 2 ^ 124 :=
    (affineBlockAtMostOne_accepting_card 32 (2 ^ 26) 64 e).trans hStepSmall
  have hSparse : (acceptingTables (affineBlockAtMostOne 32 (2 ^ 26) 64 e)).card ≤
      2 ^ descriptionBitBound 32 :=
    hSparseSmall.trans (Nat.pow_le_pow_right (by decide) (by rw [hB32]; decide))
  have hFunnel := affineBlockAtMostOne_has_essential_funnel (m := 32) (K := 2 ^ 26) (b := 64)
    (by decide) (by decide) (by decide) e hMaskBlk hImg0 hImg1 hImg2 ⟨3, by decide⟩ (by decide)
    (s1 := ⟨0, by decide⟩) (s2 := ⟨1, by decide⟩) (by decide)
  have hComp := (affineBlockAtMostOne_pin_complexity_le (m := 32) (K := 2 ^ 26) (b := 64)
    (by decide) (by decide) (by decide) e hImg0 hImg1 hImg2).trans
    (by decide : (2 ^ 26) * 64 + 2 * (2 ^ 26) - 1 ≤ 4429185023)
  refine ⟨e, hSparse, affineBlockAtMostOne_accepts_affine 32 (2 ^ 26) 64 e,
    affineBlockAtMostOne_accepts_affine_flip 32 (2 ^ 26) 64 e, ?_,
    card_starMask (m := 32) (by decide), ⟨_, hFunnel.1, _, hFunnel.2.1, hFunnel.2.2⟩, hComp, ?_⟩
  · intro a b0 Q i hi hFree v
    exact affineBlockAtMostOne_branches_nonconstant e hSparse a b0 Q i hi hFree v
  · rw [hB32]; decide

#print axioms mcspSquare_dualTable
#print axioms mcspSquare_no_comp_funnel
#print axioms mcspSquare_no_comp_funnel_empty
#print axioms mcspSquare_funnel_orbit_le
#print axioms mcspSquare_no_large_orbit_funnel
#print axioms mcspSquare_32_no_weight5_zero_funnel
#print axioms affineBlockAtMostOne_accepts_affine
#print axioms affineBlockAtMostOne_accepts_affine_flip
#print axioms affineBlockAtMostOne_accepting_card
#print axioms affineBlockAtMostOne_branches_nonconstant
#print axioms affineBlockAtMostOne_pin_eq_blockAtMostOne
#print axioms affineBlockAtMostOne_has_essential_funnel
#print axioms affineBlockAtMostOne_pin_complexity_le
#print axioms affineBlockAtMostOne_barrier_at_14
#print axioms affineBlockAtMostOne_barrier_at_32

end PvsNP.Frontier.PairFunnelGap