module

public import MCSPFreshBypass
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Unconditional earliest-fresh-gate dichotomy (discharging the joint-reader
wiring hypothesis via pair funnels), an iterated effective-mask lower bound,
exact MCSP instantiation, and a parametric `blockAtMostOne` sharpness control. -/

@[expose] public section

namespace PvsNP.Frontier.EarliestFresh

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN
open ForestPinning RestrictionCharges FreshCharges PairSeparation StopMatching
open MinimumAliases FreshBypass

variable {n k l g : ℕ}

/-! ### Part A: Effective Mask (`effMask`) and `IsPairFunnel` -/

/-- Free inputs outside `P` on which `f` constrained by `pinAt x P` still depends. -/
noncomputable def essMask (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) : Finset (Fin n) := open scoped Classical in
  (Finset.univ \ P).filter fun i =>
    EssentialAt (fun z => f (substitute (pinAt x P) z)) i

/-- Free inputs outside `P` that have already become inessential under `pinAt x P`. -/
noncomputable def inessMask (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ \ P) \ essMask f x P

/-- Effective mask adding all inessential coordinates under `pinAt x P` to `P`. -/
noncomputable def effMask (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) : Finset (Fin n) :=
  P ∪ inessMask f x P

/-- Pair `(i, j)` forms a funnel at controlling value `v` when `(v, !v)`, `(!v, v)`,
and `(v, v)` all leave `f` identically unchanged for every assignment to the remaining coordinates. -/
def IsPairFunnel (f : BooleanFunction n) (i j : Fin n) (v : Bool) : Prop :=
  i ≠ j ∧
  (∀ z, f (Function.update (Function.update z i v) j (!v)) =
        f (Function.update (Function.update z i (!v)) j v)) ∧
  (∀ z, f (Function.update (Function.update z i v) j (!v)) =
        f (Function.update (Function.update z i v) j v))

theorem not_mem_effMask_iff (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) (i : Fin n) :
    i ∉ effMask f x P ↔ i ∈ essMask f x P := by
  classical
  by_cases hiP : i ∈ P <;> by_cases hEss : i ∈ essMask f x P
  · exfalso
    have hSub := (Finset.mem_filter.mp hEss).1
    exact (Finset.mem_sdiff.mp hSub).2 hiP
  · have hiEff : i ∈ effMask f x P := Finset.mem_union_left _ hiP
    exact ⟨fun h => (h hiEff).elim, fun h => (hEss h).elim⟩
  · have hiNotIness : i ∉ inessMask f x P := fun h => (Finset.mem_sdiff.mp h).2 hEss
    have hiNotEff : i ∉ effMask f x P := by
      intro hiEff
      rcases Finset.mem_union.mp hiEff with hP | hI
      · exact hiP hP
      · exact hiNotIness hI
    exact ⟨fun _ => hEss, fun _ => hiNotEff⟩
  · have hiIness : i ∈ inessMask f x P :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiP⟩, hEss⟩
    have hiEff : i ∈ effMask f x P := Finset.mem_union_right _ hiIness
    exact ⟨fun h => (h hiEff).elim, fun h => (hEss h).elim⟩

theorem subset_effMask (f : BooleanFunction n) (x : BitString n) (P : Finset (Fin n)) :
    P ⊆ effMask f x P :=
  Finset.subset_union_left

private theorem eq_of_not_essential {h : BooleanFunction n} {q : Fin n}
    (hNot : ¬ EssentialAt h q) (z : BitString n) (v : Bool) :
    h (Function.update z q v) = h z := by
  by_contra hne
  exact hNot ⟨Function.update z q v, z, fun u hu => by simp [Function.update_of_ne hu], hne⟩

private theorem substitute_pinAt_insert_eq (x : BitString n) (Q : Finset (Fin n))
    (q : Fin n) (z : BitString n) :
    substitute (pinAt x (insert q Q)) z =
      substitute (pinAt x Q) (Function.update z q (x q)) := by
  funext u
  by_cases hu : u = q
  · subst hu
    by_cases hQ : u ∈ Q <;> simp [substitute, pinAt, hQ]
  · by_cases hQ : u ∈ Q <;> simp [substitute, pinAt, hu, hQ]

private theorem substitute_pinAt_union_iness (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) :
    ∀ S : Finset (Fin n), S ⊆ inessMask f x P → ∀ z : BitString n,
      f (substitute (pinAt x (P ∪ S)) z) = f (substitute (pinAt x P) z) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ z
    simp
  | @insert q S hqS ih =>
    intro hSub z
    have hqIn : q ∈ inessMask f x P := hSub (Finset.mem_insert_self ..)
    have hqNotEss : ¬ EssentialAt (fun w => f (substitute (pinAt x P) w)) q := by
      classical
      intro hEss
      have hFree : q ∈ Finset.univ \ P := (Finset.mem_sdiff.mp hqIn).1
      exact (Finset.mem_sdiff.mp hqIn).2 (Finset.mem_filter.mpr ⟨hFree, hEss⟩)
    have hS : S ⊆ inessMask f x P :=
      Finset.Subset.trans (Finset.subset_insert q S) hSub
    rw [Finset.union_insert, substitute_pinAt_insert_eq, ih hS]
    exact eq_of_not_essential hqNotEss z (x q)

/-- Pinning all inessential coordinates in `inessMask f x P` to `x` leaves the restricted
function identically equal to `pinAt x P`. -/
theorem eval_substitute_effMask (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) (z : BitString n) :
    f (substitute (pinAt x (effMask f x P)) z) = f (substitute (pinAt x P) z) :=
  substitute_pinAt_union_iness f x P (inessMask f x P) Finset.Subset.rfl z

theorem ess_of_not_mem_effMask {f : BooleanFunction n} {x : BitString n}
    {P : Finset (Fin n)} {i : Fin n} (hi : i ∉ effMask f x P) :
    EssentialAt (fun z => f (substitute (pinAt x (effMask f x P)) z)) i := by
  classical
  have hiEss : i ∈ essMask f x P := (not_mem_effMask_iff f x P i).mp hi
  have hFun : (fun z => f (substitute (pinAt x (effMask f x P)) z)) =
      fun z => f (substitute (pinAt x P) z) :=
    funext fun z => eval_substitute_effMask f x P z
  rw [hFun]
  exact (Finset.mem_filter.mp hiEss).2

private theorem compose_pinAt_subset (x : BitString n) {P Q : Finset (Fin n)} (hPQ : P ⊆ Q) :
    compose (pinAt x P) (pinAt x Q) = pinAt x Q := by
  funext u
  by_cases hP : u ∈ P
  · simp [compose, pinAt, hP, hPQ hP]
  · by_cases hQ : u ∈ Q <;> simp [compose, pinAt, hP, hQ]

theorem effMask_mono (f : BooleanFunction n) (x : BitString n) {P Q : Finset (Fin n)}
    (hPQ : P ⊆ Q) : effMask f x P ⊆ effMask f x Q := by
  classical
  intro i hi
  rcases Finset.mem_union.mp hi with hiP | hiI
  · exact Finset.mem_union_left _ (hPQ hiP)
  · by_cases hiQ : i ∈ Q
    · exact Finset.mem_union_left _ hiQ
    · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiQ⟩, ?_⟩)
      intro hiEssQ
      have hNotEssP : ¬ EssentialAt (fun w => f (substitute (pinAt x P) w)) i := by
        intro hEss
        exact (Finset.mem_sdiff.mp hiI).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hiI).1, hEss⟩)
      obtain ⟨y, z, hyz, hne⟩ := (Finset.mem_filter.mp hiEssQ).2
      apply hNotEssP
      refine ⟨substitute (pinAt x Q) y, substitute (pinAt x Q) z, ?_, ?_⟩
      · intro u hu
        by_cases huQ : u ∈ Q
        · simp [substitute, pinAt, huQ]
        · simp [substitute, pinAt, huQ, hyz u hu]
      · simpa only [← substitute_compose, compose_pinAt_subset x hPQ] using hne

/-- The accepting truth-table count bounds the size of `inessMask f x P` by `B`. -/
theorem card_inessMask_le {f : BooleanFunction n} {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) {x : BitString n} (hx : f x = true)
    (P : Finset (Fin n)) : (inessMask f x P).card ≤ B := by
  classical
  let gMap (U : Finset (Fin n)) : BitString n := fun u => if u ∈ U then !x u else x u
  have hInj : Set.InjOn gMap ((inessMask f x P).powerset : Set (Finset (Fin n))) := by
    intro U hU V hV hEq
    ext u
    have hu := congrFun hEq u
    by_cases h1 : u ∈ U <;> by_cases h2 : u ∈ V <;> simp [gMap, h1, h2] at hu ⊢
  have hAcc : ∀ U ∈ (inessMask f x P).powerset, gMap U ∈ acceptingTables f := by
    intro U hU
    have hUP : Disjoint U P := Finset.disjoint_left.mpr fun u hu hP =>
      (Finset.mem_sdiff.mp ((Finset.mem_sdiff.mp (Finset.mem_powerset.mp hU hu)).1)).2 hP
    have hUE : U ⊆ effMask f x P := (Finset.mem_powerset.mp hU).trans Finset.subset_union_right
    have hSubP : substitute (pinAt x P) (gMap U) = gMap U := by
      funext u
      by_cases huP : u ∈ P
      · have huU : u ∉ U := Finset.disjoint_right.mp hUP huP
        simp [substitute, pinAt, huP, gMap, huU]
      · simp [substitute, pinAt, huP]
    have hSubEff : substitute (pinAt x (effMask f x P)) (gMap U) = x := by
      funext u
      by_cases huE : u ∈ effMask f x P
      · simp [substitute, pinAt, huE]
      · have huU : u ∉ U := fun h => huE (hUE h)
        simp [substitute, pinAt, huE, gMap, huU]
    have hEval : f (gMap U) = true := by
      rw [← hSubP, ← eval_substitute_effMask f x P (gMap U), hSubEff]
      exact hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEval⟩
  have hPowCard : 2 ^ (inessMask f x P).card ≤ (acceptingTables f).card := by
    simpa [Finset.card_powerset] using Finset.card_le_card_of_injOn gMap hAcc hInj
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hPowCard.trans hSparse)

theorem effMask_fresh_step_loss (p : Program signature n g) (f : BooleanFunction n)
    (x : BitString n) (P : Finset (Fin n)) {r : Fin n} (hr : r ∈ essMask f x P) :
    nextFreshLoss p (pinAt x (effMask f x P)) (pinAt x {r}) ⊆
      fresh p (pinAt x (effMask f x P)) \ fresh p (pinAt x (effMask f x (insert r P))) := by
  intro k hk
  obtain ⟨hkStart, hkNotMid⟩ := Finset.mem_sdiff.mp hk
  refine Finset.mem_sdiff.mpr ⟨hkStart, fun hkEnd => hkNotMid ?_⟩
  have hSubMid : insert r (effMask f x P) ⊆ effMask f x (insert r P) := by
    intro u hu
    rcases Finset.mem_insert.mp hu with huEq | huE
    · subst huEq
      exact subset_effMask f x (insert u P) (Finset.mem_insert_self ..)
    · exact effMask_mono f x (Finset.subset_insert r P) huE
  have hComp1 : compose (pinAt x (effMask f x P)) (pinAt x {r}) =
      pinAt x (insert r (effMask f x P)) := by
    funext u
    by_cases hur : u = r
    · subst hur
      by_cases huE : u ∈ effMask f x P <;> simp [compose, pinAt, huE]
    · by_cases huE : u ∈ effMask f x P <;> simp [compose, pinAt, hur, huE]
  have hComp2 : compose (pinAt x (insert r (effMask f x P))) (pinAt x (effMask f x (insert r P))) =
      pinAt x (effMask f x (insert r P)) :=
    compose_pinAt_subset x hSubMid
  rw [hComp1]
  rw [← hComp2] at hkEnd
  exact fresh_nested p (pinAt x (insert r (effMask f x P))) (pinAt x (effMask f x (insert r P))) hkEnd

/-! ### Part B: Unconditional Earliest-Fresh-Gate Dichotomy -/

private theorem interpretation_const' {op : Op} {b : Bool} (h : op = .const b)
    (u : Fin (signature.Arity op) → Bool) : interpretation op u = b := by
  subst h; rfl

private theorem interpretation_not' {op : Op} (h : op = .not)
    (u : Fin (signature.Arity op) → Bool) :
    interpretation op u = !(u ⟨0, by rw [h]; decide⟩) := by
  subst h; rfl

private theorem interpretation_and' {op : Op} (h : op = .and)
    (u : Fin (signature.Arity op) → Bool) :
    interpretation op u = (u ⟨0, by rw [h]; decide⟩ && u ⟨1, by rw [h]; decide⟩) := by
  subst h; rfl

private theorem interpretation_or' {op : Op} (h : op = .or)
    (u : Fin (signature.Arity op) → Bool) :
    interpretation op u = (u ⟨0, by rw [h]; decide⟩ || u ⟨1, by rw [h]; decide⟩) := by
  subst h; rfl

private theorem fin_one_eq {k : ℕ} (hk : k = 1) (a : Fin k) :
    a = ⟨0, hk ▸ by decide⟩ := by
  subst hk
  fin_cases a
  rfl

private theorem fin_two_cases {k : ℕ} (hk : k = 2) (a : Fin k) :
    a = ⟨0, hk ▸ by decide⟩ ∨ a = ⟨1, hk ▸ by decide⟩ := by
  subst hk
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem absorbed_eval' (op : Op) (args : Fin (signature.Arity op) → Bool)
    (a : Fin (signature.Arity op)) (v : Bool)
    (hop : (op = .and ∧ v = false) ∨ (op = .or ∧ v = true)) (ha : args a = v) :
    interpretation op args = v := by
  rcases hop with ⟨hOp, rfl⟩ | ⟨hOp, rfl⟩
  · have hAr : signature.Arity op = 2 := by rw [hOp]
    rcases fin_two_cases hAr a with rfl | rfl <;> rw [interpretation_and' hOp] <;> simp [ha]
  · have hAr : signature.Arity op = 2 := by rw [hOp]
    rcases fin_two_cases hAr a with rfl | rfl <;> rw [interpretation_or' hOp] <;> simp [ha]

private theorem const_of_restricted_proj_pin (p : Program signature n g)
    (ρ : Fin n → Fin n ⊕ Bool) (τ : Fin n → Fin n ⊕ Bool)
    {u : Fin g} {a : Fin (signature.Arity (p.lines u).op)} {i : Fin n} {v : Bool}
    (hop : ((p.lines u).op = .and ∧ v = false) ∨ ((p.lines u).op = .or ∧ v = true))
    (hProj : restrictedWire p ρ ((p.lines u).wires a) = projection i)
    (hTau : τ i = .inr v) :
    restrictedWire p (compose ρ τ) (.gate u) = fun _ => v := by
  funext y
  rw [restrictedWire_compose]
  change p.trace interpretation (substitute ρ (substitute τ y)) (.gate u) = v
  rw [p.trace_gate]
  apply absorbed_eval' (p.lines u).op _ a v hop
  have hW : restrictedWire p ρ ((p.lines u).wires a) (substitute τ y) = v := by
    rw [hProj]
    change substitute τ y i = v
    simp [substitute, hTau]
  exact hW

private theorem const_of_restricted_proj_not_pin (p : Program signature n g)
    (ρ : Fin n → Fin n ⊕ Bool) (τ : Fin n → Fin n ⊕ Bool)
    {u : Fin g} {a : Fin (signature.Arity (p.lines u).op)} {i : Fin n} {v : Bool}
    (hop : (p.lines u).op = .not)
    (hProj : restrictedWire p ρ ((p.lines u).wires a) = projection i)
    (hTau : τ i = .inr v) :
    restrictedWire p (compose ρ τ) (.gate u) = fun _ => !v := by
  funext y
  rw [restrictedWire_compose]
  change p.trace interpretation (substitute ρ (substitute τ y)) (.gate u) = !v
  rw [p.trace_gate, interpretation_not' hop]
  have hAr : signature.Arity (p.lines u).op = 1 := by rw [hop]
  have ha : a = ⟨0, by rw [hop]; decide⟩ := fin_one_eq hAr a
  have hW : restrictedWire p ρ ((p.lines u).wires ⟨0, by rw [hop]; decide⟩) (substitute τ y) = v := by
    rw [← ha, hProj]
    change substitute τ y i = v
    simp [substitute, hTau]
  change Bool.not (restrictedWire p ρ ((p.lines u).wires ⟨0, by rw [hop]; decide⟩) (substitute τ y)) = !v
  rw [hW]

private theorem disclosed_of_wire_eq (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (j : Fin g) (t : Fin (signature.Arity (p.lines j).op))
    (hEq : restrictedWire p ρ (.gate j) = restrictedWire p ρ ((p.lines j).wires t)) :
    disclosed p ρ j := by
  cases hWire : (p.lines j).wires t with
  | gate u =>
    exact Or.inr (Or.inr ⟨u, p.lt_of_lines_wires_eq_gate j t u hWire, hWire ▸ hEq⟩)
  | input r =>
    rw [hWire] at hEq
    cases hρ : ρ r with
    | inl v => exact Or.inr (Or.inl ⟨v, hEq.trans (funext fun _ => substitute_inl hρ)⟩)
    | inr v => exact Or.inl ⟨v, hEq.trans (funext fun _ => substitute_inr hρ)⟩

/-- Any gate with a restricted-constant input is `disclosed` under that restriction. -/
theorem disclosed_of_const_arg (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (j : Fin g) (a : Fin (signature.Arity (p.lines j).op)) (b : Bool)
    (harg : restrictedWire p ρ ((p.lines j).wires a) = fun _ => b) :
    disclosed p ρ j := by
  cases hOp : (p.lines j).op with
  | const v =>
    exact Or.inl ⟨v, funext fun x => (p.trace_gate _ _ j).trans (interpretation_const' hOp _)⟩
  | not =>
    have hAr : signature.Arity (p.lines j).op = 1 := by rw [hOp]
    have ha : a = ⟨0, by rw [hOp]; decide⟩ := fin_one_eq hAr a
    refine Or.inl ⟨!b, funext fun x => ?_⟩
    change p.trace interpretation (substitute ρ x) (.gate j) = !b
    rw [p.trace_gate, interpretation_not' hOp]
    have hW := congrFun harg x
    rw [ha] at hW
    exact congrArg Bool.not hW
  | and =>
    have hAr : signature.Arity (p.lines j).op = 2 := by rw [hOp]
    let a0 : Fin (signature.Arity (p.lines j).op) := ⟨0, by rw [hOp]; decide⟩
    let a1 : Fin (signature.Arity (p.lines j).op) := ⟨1, by rw [hOp]; decide⟩
    rcases fin_two_cases hAr a with rfl | rfl <;> cases b
    · refine Or.inl ⟨false, funext fun x => ?_⟩
      change p.trace interpretation (substitute ρ x) (.gate j) = false
      rw [p.trace_gate, interpretation_and' hOp]
      have h0 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) = false :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) &&
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) = false
      rw [h0, Bool.false_and]
    · apply disclosed_of_wire_eq p ρ j a1
      funext x
      change p.trace interpretation (substitute ρ x) (.gate j) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)
      rw [p.trace_gate, interpretation_and' hOp]
      have h0 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) = true :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) &&
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)
      rw [h0, Bool.true_and]
    · refine Or.inl ⟨false, funext fun x => ?_⟩
      change p.trace interpretation (substitute ρ x) (.gate j) = false
      rw [p.trace_gate, interpretation_and' hOp]
      have h1 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a1) = false :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) &&
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) = false
      rw [h1, Bool.and_false]
    · apply disclosed_of_wire_eq p ρ j a0
      funext x
      change p.trace interpretation (substitute ρ x) (.gate j) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a0)
      rw [p.trace_gate, interpretation_and' hOp]
      have h1 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a1) = true :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) &&
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a0)
      rw [h1, Bool.and_true]
  | or =>
    have hAr : signature.Arity (p.lines j).op = 2 := by rw [hOp]
    let a0 : Fin (signature.Arity (p.lines j).op) := ⟨0, by rw [hOp]; decide⟩
    let a1 : Fin (signature.Arity (p.lines j).op) := ⟨1, by rw [hOp]; decide⟩
    rcases fin_two_cases hAr a with rfl | rfl <;> cases b
    · apply disclosed_of_wire_eq p ρ j a1
      funext x
      change p.trace interpretation (substitute ρ x) (.gate j) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)
      rw [p.trace_gate, interpretation_or' hOp]
      have h0 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) = false :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) ||
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)
      rw [h0, Bool.false_or]
    · refine Or.inl ⟨true, funext fun x => ?_⟩
      change p.trace interpretation (substitute ρ x) (.gate j) = true
      rw [p.trace_gate, interpretation_or' hOp]
      have h0 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) = true :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) ||
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) = true
      rw [h0, Bool.true_or]
    · apply disclosed_of_wire_eq p ρ j a0
      funext x
      change p.trace interpretation (substitute ρ x) (.gate j) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a0)
      rw [p.trace_gate, interpretation_or' hOp]
      have h1 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a1) = false :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) ||
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) =
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a0)
      rw [h1, Bool.or_false]
    · refine Or.inl ⟨true, funext fun x => ?_⟩
      change p.trace interpretation (substitute ρ x) (.gate j) = true
      rw [p.trace_gate, interpretation_or' hOp]
      have h1 : p.trace interpretation (substitute ρ x) ((p.lines j).wires a1) = true :=
        congrFun harg x
      change (p.trace interpretation (substitute ρ x) ((p.lines j).wires a0) ||
        p.trace interpretation (substitute ρ x) ((p.lines j).wires a1)) = true
      rw [h1, Bool.or_true]

private theorem disclosed_of_const_wire_compose (p : Program signature n g)
    (ρ : Fin n → Fin n ⊕ Bool) (τ : Fin n → Fin n ⊕ Bool) {u m : Fin g}
    {a : Fin (signature.Arity (p.lines m).op)} {v : Bool}
    (hRead : restrictedWire p ρ ((p.lines m).wires a) = restrictedWire p ρ (.gate u))
    (hConst : restrictedWire p (compose ρ τ) (.gate u) = fun _ => v) :
    disclosed p (compose ρ τ) m := by
  apply disclosed_of_const_arg p (compose ρ τ) m a v
  rw [restrictedWire_compose, hRead, ← restrictedWire_compose, hConst]

private theorem not_essential_restrictedWire_mem {p : Program signature n g}
    {x : BitString n} {P : Finset (Fin n)} {r : Fin n} (hr : r ∈ P) (w : Wire n g) :
    ¬ EssentialAt (restrictedWire p (pinAt x P) w) r := by
  rintro ⟨y, z, ha, hne⟩
  apply hne
  change p.trace interpretation (substitute (pinAt x P) y) w =
    p.trace interpretation (substitute (pinAt x P) z) w
  congr 1
  funext u
  by_cases hur : u = r
  · subst hur; simp [substitute, pinAt, hr]
  · by_cases huP : u ∈ P <;> simp [substitute, pinAt, huP, ha u hur]

private theorem wire_proj_not_mem {p : Program signature n g} {x : BitString n}
    {P : Finset (Fin n)} {w : Wire n g} {i : Fin n}
    (hProj : restrictedWire p (pinAt x P) w = projection i) : i ∉ P := by
  intro hi
  apply not_essential_restrictedWire_mem hi w
  rw [hProj]
  refine ⟨fun _ => false, Function.update (fun _ => false) i true, ?_, ?_⟩
  · intro u hu
    simp [Function.update_of_ne hu]
  · simp [projection]

private theorem disclosed_lt_min_fresh_const_or_proj (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (u : Fin g)
    (huMin : ∀ t : Fin g, t < u → t ∉ fresh p ρ) :
    ∀ m : ℕ, ∀ t : Fin g, t.val ≤ m → t < u →
      (∃ b : Bool, restrictedWire p ρ (.gate t) = fun _ => b) ∨
      (∃ i : Fin k, restrictedWire p ρ (.gate t) = projection i) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro t htLe htu
    have htNotFresh : t ∉ fresh p ρ := huMin t htu
    have htDisc : disclosed p ρ t := by
      by_contra hNotDisc
      exact htNotFresh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNotDisc⟩)
    rcases htDisc with hb | hi | ⟨q, hqt, hEq⟩
    · exact Or.inl hb
    · exact Or.inr hi
    · have hIH := ih q.val (by omega) q le_rfl (lt_trans hqt htu)
      rcases hIH with ⟨b, hb⟩ | ⟨i, hi⟩
      · exact Or.inl ⟨b, hEq.trans hb⟩
      · exact Or.inr ⟨i, hEq.trans hi⟩

private theorem essential_argument' (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (t : Fin g) (i : Fin k) (hEss : EssentialAt (restrictedWire p ρ (.gate t)) i) :
    ∃ a : Fin (signature.Arity (p.lines t).op),
      EssentialAt (restrictedWire p ρ ((p.lines t).wires a)) i := by
  by_contra hNo
  push Not at hNo
  obtain ⟨y, z, hyz, hne⟩ := hEss
  apply hne
  change p.trace interpretation (substitute ρ y) (.gate t) =
    p.trace interpretation (substitute ρ z) (.gate t)
  rw [p.trace_gate, p.trace_gate]
  congr 1
  funext a
  by_contra hArgNe
  exact hNo a ⟨y, z, hyz, hArgNe⟩

private theorem not_essential_input_of_ne {p : Program signature n g} (ρ : Fin n → Fin k ⊕ Bool)
    {r : Fin n} {i : Fin k} (hNotInl : ρ r ≠ .inl i) :
    ¬ EssentialAt (restrictedWire p ρ (.input r)) i := by
  rintro ⟨y, z, hyz, hne⟩
  apply hne
  change substitute ρ y r = substitute ρ z r
  cases hρ : ρ r with
  | inl v =>
    have hvi : v ≠ i := fun hEq => hNotInl (hEq ▸ hρ)
    simp [substitute, hρ, hyz v hvi]
  | inr b => simp [substitute, hρ]

private theorem downstream_fresh_of_unique_reader {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} {u : Fin g} {i : Fin n}
    (hi : i ∉ P)
    (hEss : EssentialAt (restrictedWire p (pinAt x P) root) i)
    (hRootNotProj : restrictedWire p (pinAt x P) root ≠ projection i)
    (hRootNotU : restrictedWire p (pinAt x P) root ≠ restrictedWire p (pinAt x P) (.gate u))
    (hUniq : ∀ w ∈ fresh p (pinAt x P), w ≠ u → ∀ a,
      restrictedWire p (pinAt x P) ((p.lines w).wires a) ≠ projection i) :
    ∃ m ∈ fresh p (pinAt x P), m ≠ u ∧
      ∃ a, restrictedWire p (pinAt x P) ((p.lines m).wires a) = restrictedWire p (pinAt x P) (.gate u) := by
  classical
  by_contra hNo
  push Not at hNo
  let ρ := pinAt x P
  let fu := restrictedWire p ρ (.gate u)
  have hGateNotEss : ∀ m : ℕ, ∀ t : Fin g, t.val ≤ m →
      restrictedWire p ρ (.gate t) ≠ projection i →
      restrictedWire p ρ (.gate t) ≠ fu →
      ¬ EssentialAt (restrictedWire p ρ (.gate t)) i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro t htLe htNotProj htNotFu htEss
      by_cases htu : t = u
      · exact htNotFu (htu ▸ rfl)
      · by_cases htFresh : t ∈ fresh p ρ
        · obtain ⟨a, haEss⟩ := essential_argument' p ρ t i htEss
          cases hWire : (p.lines t).wires a with
          | input r =>
            by_cases hri : r = i
            · subst hri
              have hEqProj : restrictedWire p ρ ((p.lines t).wires a) = projection r := by
                rw [hWire]
                funext z
                change substitute ρ z r = z r
                simp [ρ, substitute, pinAt, hi]
              exact hUniq t htFresh htu a hEqProj
            · have hNotInl : ρ r ≠ .inl i := by
                by_cases hrP : r ∈ P <;> simp [ρ, pinAt, hrP, hri]
              rw [hWire] at haEss
              exact not_essential_input_of_ne ρ hNotInl haEss
          | gate q =>
            have hqt : q < t := p.lt_of_lines_wires_eq_gate t a q hWire
            have hqNotProj : restrictedWire p ρ (.gate q) ≠ projection i := by
              intro hEq
              exact hUniq t htFresh htu a (hWire ▸ hEq)
            have hqNotFu : restrictedWire p ρ (.gate q) ≠ fu := by
              intro hEq
              exact hNo t htFresh htu a (hWire ▸ hEq)
            rw [hWire] at haEss
            exact ih q.val (by omega) q le_rfl hqNotProj hqNotFu haEss
        · have htDisc : disclosed p ρ t := by
            by_contra hNotDisc
            exact htFresh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNotDisc⟩)
          rcases htDisc with ⟨b, hb⟩ | ⟨r, hr⟩ | ⟨q, hqt, hEq⟩
          · rw [hb] at htEss
            obtain ⟨_, _, _, hn⟩ := htEss
            exact hn rfl
          · have hri : r ≠ i := fun hEq => htNotProj (hr.trans (congrArg projection hEq))
            rw [hr] at htEss
            obtain ⟨y, z, hyz, hne⟩ := htEss
            exact hne (hyz r hri)
          · exact ih q.val (by omega) q le_rfl (hEq ▸ htNotProj) (hEq ▸ htNotFu) (hEq ▸ htEss)
  cases hRoot : root with
  | input r =>
    by_cases hri : r = i
    · subst hri
      apply hRootNotProj
      funext z
      rw [hRoot]
      change substitute ρ z r = z r
      simp [ρ, substitute, pinAt, hi]
    · have hNotInl : ρ r ≠ .inl i := by
        by_cases hrP : r ∈ P <;> simp [ρ, pinAt, hrP, hri]
      rw [hRoot] at hEss
      exact not_essential_input_of_ne ρ hNotInl hEss
  | gate t =>
    rw [hRoot] at hEss hRootNotProj hRootNotU
    exact hGateNotEss t.val t le_rfl hRootNotProj hRootNotU hEss

private theorem pair_funnel_of_unique_binary_readers {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} {u : Fin g} {i j : Fin n} {v : Bool}
    {a0 a1 : Fin (signature.Arity (p.lines u).op)}
    (hop : ((p.lines u).op = .and ∧ v = false) ∨ ((p.lines u).op = .or ∧ v = true))
    (hne : i ≠ j)
    (ha0 : restrictedWire p (pinAt x P) ((p.lines u).wires a0) = projection i)
    (ha1 : restrictedWire p (pinAt x P) ((p.lines u).wires a1) = projection j)
    (hUniqI : ∀ w ∈ fresh p (pinAt x P), w ≠ u → ∀ a,
      restrictedWire p (pinAt x P) ((p.lines w).wires a) ≠ projection i)
    (hUniqJ : ∀ w ∈ fresh p (pinAt x P), w ≠ u → ∀ a,
      restrictedWire p (pinAt x P) ((p.lines w).wires a) ≠ projection j)
    (hRootI : restrictedWire p (pinAt x P) root ≠ projection i)
    (hRootJ : restrictedWire p (pinAt x P) root ≠ projection j) :
    IsPairFunnel (restrictedWire p (pinAt x P) root) i j v := by
  classical
  refine ⟨hne, ?_⟩
  let ρ := pinAt x P
  let z1 (z : BitString n) := Function.update (Function.update z i v) j (!v)
  let z2 (z : BitString n) := Function.update (Function.update z i (!v)) j v
  let z3 (z : BitString n) := Function.update (Function.update z i v) j v
  have hAgreeNonIJ (z : BitString n) (r : Fin n) (hri : r ≠ i) (hrj : r ≠ j) :
      z1 z r = z2 z r ∧ z1 z r = z3 z r := by
    simp [z1, z2, z3, Function.update_of_ne hri, Function.update_of_ne hrj]
  have hGateEq : ∀ (z : BitString n) (m : ℕ) (t : Fin g), t.val ≤ m →
      restrictedWire p ρ (.gate t) ≠ projection i →
      restrictedWire p ρ (.gate t) ≠ projection j →
      restrictedWire p ρ (.gate t) (z1 z) = restrictedWire p ρ (.gate t) (z2 z) ∧
      restrictedWire p ρ (.gate t) (z1 z) = restrictedWire p ρ (.gate t) (z3 z) := by
    intro z m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro t htLe htI htJ
      have wireEq (w : Wire n g) (hOrd : ∀ q : Fin g, w = .gate q → q.val < m)
          (hwI : restrictedWire p ρ w ≠ projection i)
          (hwJ : restrictedWire p ρ w ≠ projection j) :
          restrictedWire p ρ w (z1 z) = restrictedWire p ρ w (z2 z) ∧
          restrictedWire p ρ w (z1 z) = restrictedWire p ρ w (z3 z) := by
        cases hW : w with
        | input r =>
          by_cases hrP : r ∈ P
          · have hEq (y : BitString n) : restrictedWire p ρ (.input r) y = x r := by
              change substitute ρ y r = x r
              simp [ρ, substitute, pinAt, hrP]
            simp [hEq]
          · have hri : r ≠ i := by
              intro hEq; subst hEq; apply hwI; rw [hW]
              funext y; change substitute ρ y r = y r; simp [ρ, substitute, pinAt, hrP]
            have hrj : r ≠ j := by
              intro hEq; subst hEq; apply hwJ; rw [hW]
              funext y; change substitute ρ y r = y r; simp [ρ, substitute, pinAt, hrP]
            have hEq (y : BitString n) : restrictedWire p ρ (.input r) y = y r := by
              change substitute ρ y r = y r
              simp [ρ, substitute, pinAt, hrP]
            simpa [hEq] using hAgreeNonIJ z r hri hrj
        | gate q =>
          rw [hW] at hwI hwJ
          exact ih q.val (hOrd q hW) q le_rfl hwI hwJ
      by_cases htu : t = u
      · subst htu
        have hVal (y : BitString n) {a : Fin (signature.Arity (p.lines t).op)} {r : Fin n}
            (ha : restrictedWire p ρ ((p.lines t).wires a) = projection r)
            (hy : y r = v) :
            restrictedWire p ρ (.gate t) y = v := by
          change p.trace interpretation (substitute ρ y) (.gate t) = v
          rw [p.trace_gate]
          apply absorbed_eval' (p.lines t).op _ a v hop
          change restrictedWire p ρ ((p.lines t).wires a) y = v
          rw [ha]
          exact hy
        have hz1 : restrictedWire p ρ (.gate t) (z1 z) = v :=
          hVal (z1 z) ha0 (by simp [z1, Function.update_of_ne hne])
        have hz2 : restrictedWire p ρ (.gate t) (z2 z) = v :=
          hVal (z2 z) ha1 (by simp [z2])
        have hz3 : restrictedWire p ρ (.gate t) (z3 z) = v :=
          hVal (z3 z) ha0 (by simp [z3, Function.update_of_ne hne])
        rw [hz1, hz2, hz3]
        exact ⟨rfl, rfl⟩
      · by_cases htFresh : t ∈ fresh p ρ
        · have hArgs : ∀ a : Fin (signature.Arity (p.lines t).op),
              restrictedWire p ρ ((p.lines t).wires a) (z1 z) =
                restrictedWire p ρ ((p.lines t).wires a) (z2 z) ∧
              restrictedWire p ρ ((p.lines t).wires a) (z1 z) =
                restrictedWire p ρ ((p.lines t).wires a) (z3 z) := by
            intro a
            apply wireEq ((p.lines t).wires a)
            · intro q hq
              exact lt_of_lt_of_le (p.lt_of_lines_wires_eq_gate t a q hq) htLe
            · exact hUniqI t htFresh htu a
            · exact hUniqJ t htFresh htu a
          have hFun12 : (fun a => restrictedWire p ρ ((p.lines t).wires a) (z1 z)) =
              (fun a => restrictedWire p ρ ((p.lines t).wires a) (z2 z)) :=
            funext fun a => (hArgs a).1
          have hFun13 : (fun a => restrictedWire p ρ ((p.lines t).wires a) (z1 z)) =
              (fun a => restrictedWire p ρ ((p.lines t).wires a) (z3 z)) :=
            funext fun a => (hArgs a).2
          constructor <;>
          · change p.trace interpretation (substitute ρ (z1 z)) (.gate t) =
              p.trace interpretation (substitute ρ _) (.gate t)
            rw [p.trace_gate, p.trace_gate]
            first | exact congrArg (interpretation (p.lines t).op) hFun12 |
              exact congrArg (interpretation (p.lines t).op) hFun13
        · have htDisc : disclosed p ρ t := by
            by_contra hNotDisc
            exact htFresh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNotDisc⟩)
          rcases htDisc with ⟨b, hb⟩ | ⟨r, hr⟩ | ⟨q, hqt, hEq⟩
          · simp [hb]
          · have hri : r ≠ i := fun hEq => htI (hr.trans (congrArg projection hEq))
            have hrj : r ≠ j := fun hEq => htJ (hr.trans (congrArg projection hEq))
            simpa [hr, projection] using hAgreeNonIJ z r hri hrj
          · have hIH := ih q.val (by omega) q le_rfl (hEq ▸ htI) (hEq ▸ htJ)
            simpa [hEq] using hIH
  have hWireEq (z : BitString n) :
      restrictedWire p ρ root (z1 z) = restrictedWire p ρ root (z2 z) ∧
      restrictedWire p ρ root (z1 z) = restrictedWire p ρ root (z3 z) := by
    cases hRoot : root with
    | input r =>
      by_cases hrP : r ∈ P
      · have hEq (y : BitString n) : restrictedWire p ρ (.input r) y = x r := by
          change substitute ρ y r = x r
          simp [ρ, substitute, pinAt, hrP]
        simp [hEq]
      · have hri : r ≠ i := by
          intro hEq; subst hEq; apply hRootI
          rw [hRoot]; funext y; change substitute ρ y r = y r; simp [ρ, substitute, pinAt, hrP]
        have hrj : r ≠ j := by
          intro hEq; subst hEq; apply hRootJ
          rw [hRoot]; funext y; change substitute ρ y r = y r; simp [ρ, substitute, pinAt, hrP]
        have hEq (y : BitString n) : restrictedWire p ρ (.input r) y = y r := by
          change substitute ρ y r = y r
          simp [ρ, substitute, pinAt, hrP]
        simpa [hEq] using hAgreeNonIJ z r hri hrj
    | gate t =>
      rw [hRoot] at hRootI hRootJ
      exact hGateEq z t.val t le_rfl hRootI hRootJ
  exact ⟨fun z => (hWireEq z).1, fun z => (hWireEq z).2⟩

/-- Unconditional earliest-fresh-gate dichotomy (no minimality, `IsForestMask`, or `StopGate` needed):
at any mask leaving a non-empty free set where every free coordinate is essential and all
one-bit branches remain nonconstant, either pinning some free coordinate to `x` loses at least 2
fresh gates, or there is a unique binary reader yielding a pair funnel `IsPairFunnel` and forcing
at least 2 fresh losses on the controlling flip `Update x i v`. -/
theorem earliest_fresh_double_loss_or_funnel {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)}
    (hFree : (Finset.univ \ P).Nonempty)
    (hEss : ∀ i ∉ P, EssentialAt (restrictedWire p (pinAt x P) root) i)
    (hNonConst : ∀ i ∉ P, ∀ v : Bool,
      ∃ y z, restrictedWire p (branchPin x P i v) root y ≠
        restrictedWire p (branchPin x P i v) root z) :
    (∃ i ∉ P, 2 ≤ (nextFreshLoss p (pinAt x P) (pinAt x {i})).card) ∨
    (∃ i ∉ P, ∃ j ∉ P, ∃ v : Bool, x i = !v ∧ x j = !v ∧
      IsPairFunnel (restrictedWire p (pinAt x P) root) i j v ∧
      2 ≤ (nextFreshLoss p (pinAt x P) (pinAt (Function.update x i v) {i})).card) := by
  classical
  let ρ := pinAt x P
  have hRootNotProj : ∀ i ∉ P, restrictedWire p ρ root ≠ projection i := by
    intro i hi hProj
    obtain ⟨y, z, hne⟩ := hNonConst i hi true
    apply hne
    have hEq (w : BitString n) : restrictedWire p (branchPin x P i true) root w = true := by
      rw [branchPin_compose x P i true hi, restrictedWire_compose, hProj]
      change substitute (pinAt (Function.update x i true) {i}) w i = true
      simp [substitute, pinAt]
    rw [hEq y, hEq z]
  obtain ⟨i0, hi0Mem⟩ := hFree
  have hi0 : i0 ∉ P := (Finset.mem_sdiff.mp hi0Mem).2
  have hFreshNE : (fresh p ρ).Nonempty := by
    obtain ⟨f0, hf0, _, _⟩ :=
      first_projection_reader p ρ root i0 (hEss i0 hi0) (hRootNotProj i0 hi0)
    exact ⟨f0, hf0⟩
  let u := (fresh p ρ).min' hFreshNE
  have huFresh : u ∈ fresh p ρ := Finset.min'_mem (fresh p ρ) hFreshNE
  have huNotDisc : ¬ disclosed p ρ u := (Finset.mem_filter.mp huFresh).2
  have huMin : ∀ t : Fin g, t < u → t ∉ fresh p ρ := by
    intro t htu htFresh
    exact (not_lt_of_ge (Finset.min'_le (fresh p ρ) t htFresh)) htu
  have hArgProj : ∀ a : Fin (signature.Arity (p.lines u).op),
      ∃ i : Fin n, i ∉ P ∧ restrictedWire p ρ ((p.lines u).wires a) = projection i := by
    intro a
    cases hWire : (p.lines u).wires a with
    | input r =>
      by_cases hrP : r ∈ P
      · exfalso
        apply huNotDisc
        refine disclosed_of_const_arg p ρ u a (x r) ?_
        rw [hWire]
        funext z
        change substitute ρ z r = x r
        simp [ρ, substitute, pinAt, hrP]
      · refine ⟨r, hrP, ?_⟩
        funext z
        change substitute ρ z r = z r
        simp [ρ, substitute, pinAt, hrP]
    | gate t =>
      have htu : t < u := p.lt_of_lines_wires_eq_gate u a t hWire
      rcases disclosed_lt_min_fresh_const_or_proj p ρ u huMin t.val t le_rfl htu with
        ⟨b, hb⟩ | ⟨i, hi⟩
      · exfalso
        exact huNotDisc (disclosed_of_const_arg p ρ u a b (hWire ▸ hb))
      · have hiP : i ∉ P := wire_proj_not_mem (hWire ▸ hi)
        exact ⟨i, hiP, hWire ▸ hi⟩
  have hTwoLossOfFanout : ∀ {i : Fin n} (hi : i ∉ P) {a : Fin (signature.Arity (p.lines u).op)},
      restrictedWire p ρ ((p.lines u).wires a) = projection i →
      ∀ (w : Fin g), w ∈ fresh p ρ → w ≠ u →
      (∃ b, restrictedWire p ρ ((p.lines w).wires b) = projection i) →
      ∀ (v : Bool),
      2 ≤ (nextFreshLoss p ρ (pinAt (Function.update x i v) {i})).card := by
    intro i hi a ha w hw hwne ⟨b, hb⟩ v
    have hLossU := disclosed_of_pinned_projection p ρ (pinAt (Function.update x i v) {i})
      u a i v ha (by simp [pinAt])
    have hLossW := disclosed_of_pinned_projection p ρ (pinAt (Function.update x i v) {i})
      w b i v hb (by simp [pinAt])
    exact Finset.one_lt_card.mpr
      ⟨u, Finset.mem_sdiff.mpr ⟨huFresh, fun hu => (Finset.mem_filter.mp hu).2 hLossU⟩,
       w, Finset.mem_sdiff.mpr ⟨hw, fun hw' => (Finset.mem_filter.mp hw').2 hLossW⟩,
       hwne.symm⟩
  cases hOp : (p.lines u).op with
  | const b =>
    exfalso
    apply huNotDisc
    exact Or.inl ⟨b, funext fun z => (p.trace_gate _ _ u).trans (interpretation_const' hOp _)⟩
  | not =>
    let a0 : Fin (signature.Arity (p.lines u).op) := ⟨0, by rw [hOp]; decide⟩
    obtain ⟨i, hi, ha0⟩ := hArgProj a0
    have hUFun : restrictedWire p ρ (.gate u) = fun z => !(z i) := by
      funext z
      change p.trace interpretation (substitute ρ z) (.gate u) = !(z i)
      rw [p.trace_gate, interpretation_not' hOp]
      have h0 := congrFun ha0 z
      change restrictedWire p ρ ((p.lines u).wires a0) z = z i at h0
      exact congrArg Bool.not h0
    have hRootNotU : restrictedWire p ρ root ≠ restrictedWire p ρ (.gate u) := by
      intro hRootEq
      obtain ⟨y, z, hne⟩ := hNonConst i hi true
      apply hne
      have hEq (w : BitString n) : restrictedWire p (branchPin x P i true) root w = false := by
        rw [branchPin_compose x P i true hi, restrictedWire_compose, hRootEq, hUFun]
        change (!(substitute (pinAt (Function.update x i true) {i}) w i)) = false
        simp [substitute, pinAt]
      rw [hEq y, hEq z]
    left
    refine ⟨i, hi, ?_⟩
    by_cases hOther : ∃ w ∈ fresh p ρ, w ≠ u ∧ ∃ b, restrictedWire p ρ ((p.lines w).wires b) = projection i
    · obtain ⟨w, hw, hwne, hb⟩ := hOther
      simpa only [Function.update_eq_self] using hTwoLossOfFanout hi ha0 w hw hwne hb (x i)
    · push Not at hOther
      obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
        downstream_fresh_of_unique_reader hi (hEss i hi) (hRootNotProj i hi) hRootNotU hOther
      have hConstU : restrictedWire p (compose ρ (pinAt x {i})) (.gate u) = fun _ => !(x i) :=
        const_of_restricted_proj_not_pin p ρ (pinAt x {i}) hOp ha0 (by simp [pinAt])
      have hLossU : u ∈ nextFreshLoss p ρ (pinAt x {i}) := by
        have hd := disclosed_of_pinned_projection p ρ (pinAt x {i}) u a0 i (x i) ha0 (by simp [pinAt])
        exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
      have hLossM : m ∈ nextFreshLoss p ρ (pinAt x {i}) := by
        have hd := disclosed_of_const_wire_compose p ρ (pinAt x {i}) hReadM hConstU
        exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
      exact Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩
  | and =>
    let a0 : Fin (signature.Arity (p.lines u).op) := ⟨0, by rw [hOp]; decide⟩
    let a1 : Fin (signature.Arity (p.lines u).op) := ⟨1, by rw [hOp]; decide⟩
    obtain ⟨i, hi, ha0⟩ := hArgProj a0
    obtain ⟨j, hj, ha1⟩ := hArgProj a1
    have hij : i ≠ j := by
      intro hEq
      subst hEq
      apply huNotDisc
      refine Or.inr (Or.inl ⟨i, funext fun z => ?_⟩)
      change p.trace interpretation (substitute ρ z) (.gate u) = z i
      rw [p.trace_gate, interpretation_and' hOp]
      have h0 : p.trace interpretation (substitute ρ z) ((p.lines u).wires a0) = z i :=
        congrFun ha0 z
      have h1 : p.trace interpretation (substitute ρ z) ((p.lines u).wires a1) = z i :=
        congrFun ha1 z
      change (p.trace interpretation (substitute ρ z) ((p.lines u).wires a0) &&
        p.trace interpretation (substitute ρ z) ((p.lines u).wires a1)) = z i
      rw [h0, h1, Bool.and_self]
    have hRootNotU : restrictedWire p ρ root ≠ restrictedWire p ρ (.gate u) := by
      intro hRootEq
      obtain ⟨y, z, hne⟩ := hNonConst i hi false
      apply hne
      have hEq (w : BitString n) : restrictedWire p (branchPin x P i false) root w = false := by
        rw [branchPin_compose x P i false hi, restrictedWire_compose, hRootEq,
          ← restrictedWire_compose]
        exact congrFun (const_of_restricted_proj_pin p ρ (pinAt (Function.update x i false) {i})
          (Or.inl ⟨hOp, rfl⟩) ha0 (by simp [pinAt])) w
      rw [hEq y, hEq z]
    by_cases hOtherI : ∃ w ∈ fresh p ρ, w ≠ u ∧ ∃ b, restrictedWire p ρ ((p.lines w).wires b) = projection i
    · obtain ⟨w, hw, hwne, hb⟩ := hOtherI
      left; refine ⟨i, hi, ?_⟩
      simpa only [Function.update_eq_self] using hTwoLossOfFanout hi ha0 w hw hwne hb (x i)
    · by_cases hOtherJ : ∃ w ∈ fresh p ρ, w ≠ u ∧ ∃ b, restrictedWire p ρ ((p.lines w).wires b) = projection j
      · obtain ⟨w, hw, hwne, hb⟩ := hOtherJ
        left; refine ⟨j, hj, ?_⟩
        simpa only [Function.update_eq_self] using hTwoLossOfFanout hj ha1 w hw hwne hb (x j)
      · push Not at hOtherI hOtherJ
        by_cases hxi : x i = false
        · obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
            downstream_fresh_of_unique_reader hi (hEss i hi) (hRootNotProj i hi) hRootNotU hOtherI
          have hConstU : restrictedWire p (compose ρ (pinAt x {i})) (.gate u) = fun _ => false :=
            const_of_restricted_proj_pin p ρ (pinAt x {i}) (Or.inl ⟨hOp, rfl⟩) ha0
              (by simp [pinAt, hxi])
          have hLossU : u ∈ nextFreshLoss p ρ (pinAt x {i}) := by
            have hd := disclosed_of_pinned_projection p ρ (pinAt x {i}) u a0 i (x i) ha0 (by simp [pinAt])
            exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
          have hLossM : m ∈ nextFreshLoss p ρ (pinAt x {i}) := by
            have hd := disclosed_of_const_wire_compose p ρ (pinAt x {i}) hReadM hConstU
            exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
          left; exact ⟨i, hi, Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩⟩
        · by_cases hxj : x j = false
          · obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
              downstream_fresh_of_unique_reader hj (hEss j hj) (hRootNotProj j hj) hRootNotU hOtherJ
            have hConstU : restrictedWire p (compose ρ (pinAt x {j})) (.gate u) = fun _ => false :=
              const_of_restricted_proj_pin p ρ (pinAt x {j}) (Or.inl ⟨hOp, rfl⟩) ha1
                (by simp [pinAt, hxj])
            have hLossU : u ∈ nextFreshLoss p ρ (pinAt x {j}) := by
              have hd := disclosed_of_pinned_projection p ρ (pinAt x {j}) u a1 j (x j) ha1 (by simp [pinAt])
              exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            have hLossM : m ∈ nextFreshLoss p ρ (pinAt x {j}) := by
              have hd := disclosed_of_const_wire_compose p ρ (pinAt x {j}) hReadM hConstU
              exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            left; exact ⟨j, hj, Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩⟩
          · have hxiT : x i = true := Bool.eq_true_of_not_eq_false hxi
            have hxjT : x j = true := Bool.eq_true_of_not_eq_false hxj
            have hFunnel : IsPairFunnel (restrictedWire p ρ root) i j false :=
              pair_funnel_of_unique_binary_readers (Or.inl ⟨hOp, rfl⟩) hij ha0 ha1 hOtherI hOtherJ
                (hRootNotProj i hi) (hRootNotProj j hj)
            obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
              downstream_fresh_of_unique_reader hi (hEss i hi) (hRootNotProj i hi) hRootNotU hOtherI
            have hConstU : restrictedWire p (compose ρ (pinAt (Function.update x i false) {i})) (.gate u) =
                fun _ => false :=
              const_of_restricted_proj_pin p ρ (pinAt (Function.update x i false) {i})
                (Or.inl ⟨hOp, rfl⟩) ha0 (by simp [pinAt])
            have hLossU : u ∈ nextFreshLoss p ρ (pinAt (Function.update x i false) {i}) := by
              have hd := disclosed_of_pinned_projection p ρ (pinAt (Function.update x i false) {i})
                u a0 i false ha0 (by simp [pinAt])
              exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            have hLossM : m ∈ nextFreshLoss p ρ (pinAt (Function.update x i false) {i}) := by
              have hd := disclosed_of_const_wire_compose p ρ (pinAt (Function.update x i false) {i})
                hReadM hConstU
              exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            right
            exact ⟨i, hi, j, hj, false, hxiT, hxjT, hFunnel,
              Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩⟩
  | or =>
    let a0 : Fin (signature.Arity (p.lines u).op) := ⟨0, by rw [hOp]; decide⟩
    let a1 : Fin (signature.Arity (p.lines u).op) := ⟨1, by rw [hOp]; decide⟩
    obtain ⟨i, hi, ha0⟩ := hArgProj a0
    obtain ⟨j, hj, ha1⟩ := hArgProj a1
    have hij : i ≠ j := by
      intro hEq
      subst hEq
      apply huNotDisc
      refine Or.inr (Or.inl ⟨i, funext fun z => ?_⟩)
      change p.trace interpretation (substitute ρ z) (.gate u) = z i
      rw [p.trace_gate, interpretation_or' hOp]
      have h0 : p.trace interpretation (substitute ρ z) ((p.lines u).wires a0) = z i :=
        congrFun ha0 z
      have h1 : p.trace interpretation (substitute ρ z) ((p.lines u).wires a1) = z i :=
        congrFun ha1 z
      change (p.trace interpretation (substitute ρ z) ((p.lines u).wires a0) ||
        p.trace interpretation (substitute ρ z) ((p.lines u).wires a1)) = z i
      rw [h0, h1, Bool.or_self]
    have hRootNotU : restrictedWire p ρ root ≠ restrictedWire p ρ (.gate u) := by
      intro hRootEq
      obtain ⟨y, z, hne⟩ := hNonConst i hi true
      apply hne
      have hEq (w : BitString n) : restrictedWire p (branchPin x P i true) root w = true := by
        rw [branchPin_compose x P i true hi, restrictedWire_compose, hRootEq,
          ← restrictedWire_compose]
        exact congrFun (const_of_restricted_proj_pin p ρ (pinAt (Function.update x i true) {i})
          (Or.inr ⟨hOp, rfl⟩) ha0 (by simp [pinAt])) w
      rw [hEq y, hEq z]
    by_cases hOtherI : ∃ w ∈ fresh p ρ, w ≠ u ∧ ∃ b, restrictedWire p ρ ((p.lines w).wires b) = projection i
    · obtain ⟨w, hw, hwne, hb⟩ := hOtherI
      left; refine ⟨i, hi, ?_⟩
      simpa only [Function.update_eq_self] using hTwoLossOfFanout hi ha0 w hw hwne hb (x i)
    · by_cases hOtherJ : ∃ w ∈ fresh p ρ, w ≠ u ∧ ∃ b, restrictedWire p ρ ((p.lines w).wires b) = projection j
      · obtain ⟨w, hw, hwne, hb⟩ := hOtherJ
        left; refine ⟨j, hj, ?_⟩
        simpa only [Function.update_eq_self] using hTwoLossOfFanout hj ha1 w hw hwne hb (x j)
      · push Not at hOtherI hOtherJ
        by_cases hxi : x i = true
        · obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
            downstream_fresh_of_unique_reader hi (hEss i hi) (hRootNotProj i hi) hRootNotU hOtherI
          have hConstU : restrictedWire p (compose ρ (pinAt x {i})) (.gate u) = fun _ => true :=
            const_of_restricted_proj_pin p ρ (pinAt x {i}) (Or.inr ⟨hOp, rfl⟩) ha0
              (by simp [pinAt, hxi])
          have hLossU : u ∈ nextFreshLoss p ρ (pinAt x {i}) := by
            have hd := disclosed_of_pinned_projection p ρ (pinAt x {i}) u a0 i (x i) ha0 (by simp [pinAt])
            exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
          have hLossM : m ∈ nextFreshLoss p ρ (pinAt x {i}) := by
            have hd := disclosed_of_const_wire_compose p ρ (pinAt x {i}) hReadM hConstU
            exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
          left; exact ⟨i, hi, Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩⟩
        · by_cases hxj : x j = true
          · obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
              downstream_fresh_of_unique_reader hj (hEss j hj) (hRootNotProj j hj) hRootNotU hOtherJ
            have hConstU : restrictedWire p (compose ρ (pinAt x {j})) (.gate u) = fun _ => true :=
              const_of_restricted_proj_pin p ρ (pinAt x {j}) (Or.inr ⟨hOp, rfl⟩) ha1
                (by simp [pinAt, hxj])
            have hLossU : u ∈ nextFreshLoss p ρ (pinAt x {j}) := by
              have hd := disclosed_of_pinned_projection p ρ (pinAt x {j}) u a1 j (x j) ha1 (by simp [pinAt])
              exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            have hLossM : m ∈ nextFreshLoss p ρ (pinAt x {j}) := by
              have hd := disclosed_of_const_wire_compose p ρ (pinAt x {j}) hReadM hConstU
              exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            left; exact ⟨j, hj, Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩⟩
          · have hxiF : x i = false := Bool.eq_false_of_not_eq_true hxi
            have hxjF : x j = false := Bool.eq_false_of_not_eq_true hxj
            have hFunnel : IsPairFunnel (restrictedWire p ρ root) i j true :=
              pair_funnel_of_unique_binary_readers (Or.inr ⟨hOp, rfl⟩) hij ha0 ha1 hOtherI hOtherJ
                (hRootNotProj i hi) (hRootNotProj j hj)
            obtain ⟨m, hmFresh, hmne, aM, hReadM⟩ :=
              downstream_fresh_of_unique_reader hi (hEss i hi) (hRootNotProj i hi) hRootNotU hOtherI
            have hConstU : restrictedWire p (compose ρ (pinAt (Function.update x i true) {i})) (.gate u) =
                fun _ => true :=
              const_of_restricted_proj_pin p ρ (pinAt (Function.update x i true) {i})
                (Or.inr ⟨hOp, rfl⟩) ha0 (by simp [pinAt])
            have hLossU : u ∈ nextFreshLoss p ρ (pinAt (Function.update x i true) {i}) := by
              have hd := disclosed_of_pinned_projection p ρ (pinAt (Function.update x i true) {i})
                u a0 i true ha0 (by simp [pinAt])
              exact Finset.mem_sdiff.mpr ⟨huFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            have hLossM : m ∈ nextFreshLoss p ρ (pinAt (Function.update x i true) {i}) := by
              have hd := disclosed_of_const_wire_compose p ρ (pinAt (Function.update x i true) {i})
                hReadM hConstU
              exact Finset.mem_sdiff.mpr ⟨hmFresh, fun h => (Finset.mem_filter.mp h).2 hd⟩
            right
            exact ⟨i, hi, j, hj, true, hxiF, hxjF, hFunnel,
              Finset.one_lt_card.mpr ⟨u, hLossU, m, hLossM, hmne.symm⟩⟩

/-! ### Part C: Iterated Effective-Fresh Adaptive Bound & Exact MCSP Instantiation -/

private theorem branch_nonconst_effMask (f : BooleanFunction n) (x : BitString n)
    (P : Finset (Fin n)) {i : Fin n} (hi : i ∉ effMask f x P) (v : Bool)
    (hBranch : ∃ y z, f (substitute (branchPin x P i v) y) ≠
      f (substitute (branchPin x P i v) z)) :
    ∃ y z, f (substitute (branchPin x (effMask f x P) i v) y) ≠
      f (substitute (branchPin x (effMask f x P) i v) z) := by
  have hiP : i ∉ P := fun h => hi (subset_effMask f x P h)
  let τ := pinAt (Function.update x i v) {i}
  have hFun : (fun y => f (substitute (branchPin x (effMask f x P) i v) y)) =
      fun y => f (substitute (branchPin x P i v) y) := by
    funext y
    rw [branchPin_compose x (effMask f x P) i v hi, branchPin_compose x P i v hiP,
      substitute_compose, substitute_compose]
    exact eval_substitute_effMask f x P (substitute τ y)
  rcases hBranch with ⟨y, z, hne⟩
  exact ⟨y, z, by rw [congrFun hFun y, congrFun hFun z]; exact hne⟩

/-- Unconditional iterated adaptive fresh-gate bound when pair funnels are absent on the
effective masks: every pinned coordinate pays at least 2 distinct fresh gates, giving
`2 * (n - B - 1) ≤ c.size`. -/
theorem adaptive_eff_noFunnel_bound (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    {x : BitString n} {B : ℕ} (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hx : f x = true)
    (hBranch : ∀ P : Finset (Fin n), P.card + B + 1 < n → ∀ i ∉ P, ∀ v : Bool,
      ∃ y z, f (substitute (branchPin x P i v) y) ≠
        f (substitute (branchPin x P i v) z))
    (hNoFunnel : ∀ P : Finset (Fin n), P.card + B + 1 < n →
      ∀ i ∈ essMask f x P, ∀ j ∈ essMask f x P, ∀ v : Bool,
        x i = !v → x j = !v →
        ¬ IsPairFunnel (fun z => f (substitute (pinAt x P) z)) i j v) :
    2 * (n - B - 1) ≤ c.size := by
  classical
  let E := effMask f x
  let F := fun P : Finset (Fin n) => fresh c.program (pinAt x (E P))
  have hStep : ∀ t : ℕ, t ≤ n - B - 1 →
      ∃ P : Finset (Fin n), P.card = t ∧ 2 * t ≤ (F ∅ \ F P).card := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨∅, Finset.card_empty, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨P, hPcard, hCharged⟩ := ih (by omega)
      have hFreeP : P.card + B + 1 < n := by omega
      have hIness : (inessMask f x P).card ≤ B := card_inessMask_le hSparse hx P
      have hECard : (E P).card ≤ P.card + B :=
        (Finset.card_union_le P (inessMask f x P)).trans (Nat.add_le_add_left hIness _)
      have hFreeE : (Finset.univ \ E P).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hEmp
        have hEq : (Finset.univ : Finset (Fin n)) \ E P = ∅ := hEmp
        have hSub : Finset.univ ⊆ E P := Finset.sdiff_eq_empty_iff_subset.mp hEq
        have hLe := Finset.card_le_card hSub
        simp only [Finset.card_univ, Fintype.card_fin] at hLe
        omega
      have hEssE : ∀ i ∉ E P, EssentialAt (restrictedWire c.program (pinAt x (E P)) (c.outputs 0)) i := by
        intro i hi
        rw [NestedFaces.restricted_circuit_eq c hc (pinAt x (E P))]
        exact ess_of_not_mem_effMask hi
      have hBranchE : ∀ i ∉ E P, ∀ v : Bool,
          ∃ y z, restrictedWire c.program (branchPin x (E P) i v) (c.outputs 0) y ≠
            restrictedWire c.program (branchPin x (E P) i v) (c.outputs 0) z := by
        intro i hi v
        rw [NestedFaces.restricted_circuit_eq c hc]
        exact branch_nonconst_effMask f x P hi v
          (hBranch P hFreeP i (fun h => hi (subset_effMask f x P h)) v)
      rcases earliest_fresh_double_loss_or_funnel hFreeE hEssE hBranchE with
        ⟨r, hrNotE, hTwo⟩ | ⟨i, hiNotE, j, hjNotE, v, hxi, hxj, hFunnel, _⟩
      · have hrEss : r ∈ essMask f x P := (not_mem_effMask_iff f x P r).mp hrNotE
        have hrP : r ∉ P := fun h => hrNotE (subset_effMask f x P h)
        refine ⟨insert r P, by rw [Finset.card_insert_of_notMem hrP, hPcard], ?_⟩
        have hInc1 : F (insert r P) ⊆ F P := by
          have hComp : compose (pinAt x (E P)) (pinAt x (E (insert r P))) = pinAt x (E (insert r P)) :=
            compose_pinAt_subset x (effMask_mono f x (Finset.subset_insert r P))
          intro k hk
          dsimp only [F] at hk ⊢
          rw [← hComp] at hk
          exact fresh_nested c.program (pinAt x (E P)) (pinAt x (E (insert r P))) hk
        have hInc0 : F P ⊆ F ∅ := by
          have hComp : compose (pinAt x (E ∅)) (pinAt x (E P)) = pinAt x (E P) :=
            compose_pinAt_subset x (effMask_mono f x (Finset.empty_subset P))
          intro k hk
          dsimp only [F] at hk ⊢
          rw [← hComp] at hk
          exact fresh_nested c.program (pinAt x (E ∅)) (pinAt x (E P)) hk
        have hStepSub := effMask_fresh_step_loss c.program f x P hrEss
        have hTwo' : 2 ≤ (F P \ F (insert r P)).card := hTwo.trans (Finset.card_le_card hStepSub)
        have hSplit1 := Finset.card_sdiff_add_card_eq_card hInc1
        have hSplit0 := Finset.card_sdiff_add_card_eq_card hInc0
        have hSplit01 := Finset.card_sdiff_add_card_eq_card (hInc1.trans hInc0)
        omega
      · exfalso
        have hRW : restrictedWire c.program (pinAt x (E P)) (c.outputs 0) =
            fun z => f (substitute (pinAt x P) z) := by
          rw [NestedFaces.restricted_circuit_eq c hc]
          funext z
          exact eval_substitute_effMask f x P z
        rw [hRW] at hFunnel
        exact hNoFunnel P hFreeP i ((not_mem_effMask_iff f x P i).mp hiNotE)
          j ((not_mem_effMask_iff f x P j).mp hjNotE) v hxi hxj hFunnel
  obtain ⟨P, _, hBound⟩ := hStep (n - B - 1) le_rfl
  have hSubUniv : F ∅ \ F P ⊆ Finset.univ := Finset.subset_univ _
  have hCardLe : (F ∅ \ F P).card ≤ c.size :=
    (Finset.card_le_card hSubUniv).trans (by simp)
  exact hBound.trans hCardLe

/-- Discharging `hJoint` for exact `mcspSquare m` (`m ≥ 7`): at any affine-pinned mask `P`
with `P.card + descriptionBitBound m + 1 < 2 ^ m`, an arbitrary circuit either loses at least
two fresh gates when pinning some `i ∈ essMask` to `x i`, or exhibits a pair funnel `IsPairFunnel`
between two `essMask` coordinates whose controlling flip loses at least two fresh gates. -/
theorem mcspSquare_earliest_fresh_dichotomy (m : ℕ) (hm : 7 ≤ m)
    (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (a : BitString m) (b : Bool) (P : Finset (Fin (2 ^ m)))
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m) :
    let x := MCSP.truthTable m (affine a b)
    (∃ i ∈ essMask (mcspSquare m) x P,
      2 ≤ (nextFreshLoss c.program (pinAt x (effMask (mcspSquare m) x P)) (pinAt x {i})).card) ∨
    (∃ i ∈ essMask (mcspSquare m) x P, ∃ j ∈ essMask (mcspSquare m) x P, ∃ v : Bool,
      x i = !v ∧ x j = !v ∧
      IsPairFunnel (fun z => mcspSquare m (substitute (pinAt x P) z)) i j v ∧
      2 ≤ (nextFreshLoss c.program (pinAt x (effMask (mcspSquare m) x P))
        (pinAt (Function.update x i v) {i})).card) := by
  classical
  dsimp only
  let x := MCSP.truthTable m (affine a b)
  let E := effMask (mcspSquare m) x P
  have hx : mcspSquare m x = true := mcspSquare_accepts_affine m (by omega) a b
  have hIness : (inessMask (mcspSquare m) x P).card ≤ descriptionBitBound m :=
    card_inessMask_le (card_accepting_mcspSquare_le m) hx P
  have hECard : E.card ≤ P.card + descriptionBitBound m :=
    (Finset.card_union_le P (inessMask (mcspSquare m) x P)).trans (Nat.add_le_add_left hIness _)
  have hFreeE : (Finset.univ \ E).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmp
    have hSub : Finset.univ ⊆ E := Finset.sdiff_eq_empty_iff_subset.mp hEmp
    have hLe := Finset.card_le_card hSub
    simp only [Finset.card_univ, Fintype.card_fin] at hLe
    omega
  have hEssE : ∀ i ∉ E, EssentialAt (restrictedWire c.program (pinAt x E) (c.outputs 0)) i := by
    intro i hi
    rw [NestedFaces.restricted_circuit_eq c hc]
    exact ess_of_not_mem_effMask hi
  have hBranchE : ∀ i ∉ E, ∀ v : Bool,
      ∃ y z, restrictedWire c.program (branchPin x E i v) (c.outputs 0) y ≠
        restrictedWire c.program (branchPin x E i v) (c.outputs 0) z := by
    intro i hi v
    have hiP : i ∉ P := fun h => hi (subset_effMask (mcspSquare m) x P h)
    obtain ⟨y, z, hAgree, hyi, hzi, hyT, hzF⟩ :=
      mcspSquare_affine_pin_branches_nonconstant m hm a b P i hiP hFree v
    have hSub (w : BitString (2 ^ m)) (hw : ∀ q ∈ P, w q = x q) (hwi : w i = v) :
        substitute (branchPin x P i v) w = w := by
      funext q
      by_cases hqi : q = i
      · subst hqi; simp [substitute, branchPin, pinAt, hwi]
      · by_cases hqP : q ∈ P
        · simp [substitute, branchPin, pinAt, hqi, hqP, hw q hqP]
        · simp [substitute, branchPin, pinAt, hqi, hqP]
    rw [NestedFaces.restricted_circuit_eq c hc]
    apply branch_nonconst_effMask (mcspSquare m) x P hi v
    refine ⟨y, z, ?_⟩
    rw [hSub y (fun q hq => (hAgree q hq).1) hyi, hSub z (fun q hq => (hAgree q hq).2) hzi,
      hyT, hzF]
    decide
  rcases earliest_fresh_double_loss_or_funnel hFreeE hEssE hBranchE with
    ⟨i, hi, hTwo⟩ | ⟨i, hi, j, hj, v, hxi, hxj, hFunnel, hTwo⟩
  · exact Or.inl ⟨i, (not_mem_effMask_iff (mcspSquare m) x P i).mp hi, hTwo⟩
  · have hRW : restrictedWire c.program (pinAt x E) (c.outputs 0) =
        fun z => mcspSquare m (substitute (pinAt x P) z) := by
      rw [NestedFaces.restricted_circuit_eq c hc]
      funext z
      exact eval_substitute_effMask (mcspSquare m) x P z
    rw [hRW] at hFunnel
    exact Or.inr ⟨i, (not_mem_effMask_iff (mcspSquare m) x P i).mp hi,
      j, (not_mem_effMask_iff (mcspSquare m) x P j).mp hj, v, hxi, hxj, hFunnel, hTwo⟩

/-- If exact `mcspSquare m` (`m ≥ 7`) avoids pair funnels at controlling flips along
affine effective masks, it immediately requires at least `2 * (2^m - B - 1)` De Morgan gates. -/
theorem mcspSquare_noFunnel_twoN (m : ℕ) (hm : 7 ≤ m)
    (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (a : BitString m) (b : Bool)
    (hNoFunnel : ∀ P : Finset (Fin (2 ^ m)), P.card + descriptionBitBound m + 1 < 2 ^ m →
      ∀ i ∈ essMask (mcspSquare m) (MCSP.truthTable m (affine a b)) P,
      ∀ j ∈ essMask (mcspSquare m) (MCSP.truthTable m (affine a b)) P,
      ∀ v : Bool,
        MCSP.truthTable m (affine a b) i = !v →
        MCSP.truthTable m (affine a b) j = !v →
        ¬ IsPairFunnel (fun z => mcspSquare m (substitute (pinAt (MCSP.truthTable m (affine a b)) P) z)) i j v) :
    2 * (2 ^ m - descriptionBitBound m - 1) ≤ c.size := by
  let x := MCSP.truthTable m (affine a b)
  refine adaptive_eff_noFunnel_bound c hc (card_accepting_mcspSquare_le m)
    (mcspSquare_accepts_affine m (by omega) a b) ?_ hNoFunnel
  intro P hFree i hi v
  obtain ⟨y, z, hAgree, hyi, hzi, hyT, hzF⟩ :=
    mcspSquare_affine_pin_branches_nonconstant m hm a b P i hi hFree v
  have hSub (w : BitString (2 ^ m)) (hw : ∀ q ∈ P, w q = x q) (hwi : w i = v) :
      substitute (branchPin x P i v) w = w := by
    funext q
    by_cases hqi : q = i
    · subst hqi; simp [substitute, branchPin, pinAt, hwi]
    · by_cases hqP : q ∈ P
      · simp [substitute, branchPin, pinAt, hqi, hqP, hw q hqP]
      · simp [substitute, branchPin, pinAt, hqi, hqP]
  refine ⟨y, z, ?_⟩
  rw [hSub y (fun q hq => (hAgree q hq).1) hyi, hSub z (fun q hq => (hAgree q hq).2) hzi,
    hyT, hzF]
  decide

/-! ### Part D: Parametric Sharpness Control (`blockAtMostOne`) -/

/-- Disjunction of block `r` (`b` variables) inside a `K * b`-bit input. -/
def blockOr (K b : ℕ) (r : Fin K) : BooleanFunction (K * b) :=
  fun x => decide (∃ s : Fin b, x (finProdFinEquiv (r, s)) = true)

/-- Accepts truth tables where at most one of the `K` blocks of size `b` is active. -/
def blockAtMostOne (K b : ℕ) : BooleanFunction (K * b) :=
  fun x => decide ((Finset.univ.filter fun r : Fin K => blockOr K b r x = true).card ≤ 1)

theorem blockAtMostOne_zero (K b : ℕ) : blockAtMostOne K b (fun _ => false) = true := by
  have hEmp : (Finset.univ.filter fun r : Fin K => blockOr K b r (fun _ => false) = true) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    simp [blockOr] at hr
  simp [blockAtMostOne, hEmp]

theorem blockAtMostOne_accepting_card (K b : ℕ) :
    (acceptingTables (blockAtMostOne K b)).card ≤ 1 + K * 2 ^ b := by
  classical
  let singleBlock (r : Fin K) (y : BitString b) : BitString (K * b) :=
    fun i => let q := finProdFinEquiv.symm i; if q.1 = r then y q.2 else false
  let cover : Finset (BitString (K * b)) :=
    insert (fun _ => false)
      (Finset.univ.biUnion fun r : Fin K => (Finset.univ : Finset (BitString b)).image (singleBlock r))
  have hSub : acceptingTables (blockAtMostOne K b) ⊆ cover := by
    intro x hx
    have hxTrue : blockAtMostOne K b x = true := (Finset.mem_filter.mp hx).2
    let act := Finset.univ.filter fun r : Fin K => blockOr K b r x = true
    have hCard : act.card ≤ 1 := by
      simpa [blockAtMostOne, act] using hxTrue
    by_cases hEmp : act = ∅
    · have hZero : x = fun _ => false := by
        funext i
        obtain ⟨⟨r, s⟩, hi⟩ := finProdFinEquiv.surjective i
        rw [← hi]
        by_contra hTrue
        have hxT : x (finProdFinEquiv (r, s)) = true := Bool.eq_true_of_not_eq_false hTrue
        have hrAct : r ∈ act := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simp only [blockOr, decide_eq_true_eq]; exact ⟨s, hxT⟩⟩
        rw [hEmp] at hrAct
        cases hrAct
      subst hZero
      exact Finset.mem_insert_self ..
    · have hOne : act.card = 1 := by
        have hPos : 0 < act.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmp)
        omega
      obtain ⟨r, hrEq⟩ := Finset.card_eq_one.mp hOne
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, ?_⟩)
      refine Finset.mem_image.mpr ⟨fun s => x (finProdFinEquiv (r, s)), Finset.mem_univ _, ?_⟩
      funext i
      obtain ⟨⟨r', s'⟩, hi⟩ := finProdFinEquiv.surjective i
      rw [← hi]
      simp only [singleBlock, Equiv.symm_apply_apply]
      by_cases hrr' : r' = r
      · subst hrr'; simp
      · simp only [hrr', ite_false]
        by_contra hNeF
        have hxT : x (finProdFinEquiv (r', s')) = true := by
          cases hVal : x (finProdFinEquiv (r', s')) <;> simp_all
        have hr'Act : r' ∈ act := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by simp only [blockOr, decide_eq_true_eq]; exact ⟨s', hxT⟩⟩
        rw [hrEq, Finset.mem_singleton] at hr'Act
        exact hrr' hr'Act
  calc
    (acceptingTables (blockAtMostOne K b)).card ≤ cover.card := Finset.card_le_card hSub
    _ ≤ 1 + (Finset.univ.biUnion fun r : Fin K =>
        (Finset.univ : Finset (BitString b)).image (singleBlock r)).card :=
      (Finset.card_insert_le ..).trans (by omega)
    _ ≤ 1 + ∑ r : Fin K, ((Finset.univ : Finset (BitString b)).image (singleBlock r)).card :=
      Nat.add_le_add_left Finset.card_biUnion_le 1
    _ ≤ 1 + ∑ _r : Fin K, 2 ^ b := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro r _
      exact (Finset.card_image_le).trans (by simp [Fintype.card_fin])
    _ = 1 + K * 2 ^ b := by simp [Finset.sum_const, smul_eq_mul]

/-- Every one-bit branch of `blockAtMostOne K b` stays nonconstant once `3 ≤ K` and `1 ≤ b`. -/
theorem blockAtMostOne_branches_nonconstant {K b : ℕ} (hK : 3 ≤ K) (hb : 1 ≤ b)
    (i : Fin (K * b)) (v : Bool) :
    ∃ y z, blockAtMostOne K b (substitute (branchPin (fun _ => false) ∅ i v) y) ≠
      blockAtMostOne K b (substitute (branchPin (fun _ => false) ∅ i v) z) := by
  let q := finProdFinEquiv.symm i
  let r0 := q.1
  let ρ := branchPin (fun _ => false) ∅ i v
  let sZ : Fin b := ⟨0, hb⟩
  have hY : blockAtMostOne K b (substitute ρ (fun _ => false)) = true := by
    have hSub : (Finset.univ.filter fun r : Fin K =>
        blockOr K b r (substitute ρ (fun _ => false)) = true) ⊆ {r0} := by
      intro r hr
      obtain ⟨s, hs⟩ := by simpa [blockOr] using (Finset.mem_filter.mp hr).2
      have hIsI : finProdFinEquiv (r, s) = i := by
        by_contra hne
        have hFalse : substitute ρ (fun _ => false) (finProdFinEquiv (r, s)) = false := by
          simp [ρ, substitute, branchPin, pinAt, hne]
        rw [hFalse] at hs
        cases hs
      have hPair : (r, s) = q :=
        (finProdFinEquiv.symm_apply_apply (r, s)).symm.trans (congrArg finProdFinEquiv.symm hIsI)
      exact Finset.mem_singleton.mpr (congrArg Prod.fst hPair)
    have hCard : (Finset.univ.filter fun r : Fin K =>
        blockOr K b r (substitute ρ (fun _ => false)) = true).card ≤ 1 :=
      (Finset.card_le_card hSub).trans (by simp)
    simpa [blockAtMostOne] using hCard
  have hRestCard : 1 < (Finset.univ.erase r0).card := by
    have hEr := Finset.card_erase_of_mem (Finset.mem_univ r0)
    rw [Finset.card_univ, Fintype.card_fin] at hEr
    omega
  obtain ⟨r1, hr1, r2, hr2, hr12⟩ := Finset.one_lt_card.mp hRestCard
  have hr10 : r1 ≠ r0 := (Finset.mem_erase.mp hr1).1
  have hr20 : r2 ≠ r0 := (Finset.mem_erase.mp hr2).1
  let i1 := finProdFinEquiv (r1, sZ)
  let i2 := finProdFinEquiv (r2, sZ)
  have hi1 : i1 ≠ i := by
    intro hEq
    have hPair : (r1, sZ) = q :=
      (finProdFinEquiv.symm_apply_apply (r1, sZ)).symm.trans (congrArg finProdFinEquiv.symm hEq)
    exact hr10 (congrArg Prod.fst hPair)
  have hi2 : i2 ≠ i := by
    intro hEq
    have hPair : (r2, sZ) = q :=
      (finProdFinEquiv.symm_apply_apply (r2, sZ)).symm.trans (congrArg finProdFinEquiv.symm hEq)
    exact hr20 (congrArg Prod.fst hPair)
  let z : BitString (K * b) := fun k => decide (k = i1 ∨ k = i2)
  have hZ : blockAtMostOne K b (substitute ρ z) = false := by
    let act := Finset.univ.filter fun r : Fin K => blockOr K b r (substitute ρ z) = true
    have hSub1 : substitute ρ z i1 = true := by
      have hPin : ρ i1 = .inl i1 := by simp [ρ, branchPin, pinAt, hi1]
      change Sum.elim z id (ρ i1) = true
      rw [hPin]
      simp [z]
    have hSub2 : substitute ρ z i2 = true := by
      have hPin : ρ i2 = .inl i2 := by simp [ρ, branchPin, pinAt, hi2]
      change Sum.elim z id (ρ i2) = true
      rw [hPin]
      simp [z]
    have hr1Mem : r1 ∈ act := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simp only [blockOr, decide_eq_true_eq]; exact ⟨sZ, hSub1⟩⟩
    have hr2Mem : r2 ∈ act := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simp only [blockOr, decide_eq_true_eq]; exact ⟨sZ, hSub2⟩⟩
    have hTwo : 1 < act.card := Finset.one_lt_card.mpr ⟨r1, hr1Mem, r2, hr2Mem, hr12⟩
    have hNotLe : ¬ act.card ≤ 1 := by omega
    simpa [blockAtMostOne, act] using hNotLe
  exact ⟨fun _ => false, z, by rw [hY, hZ]; decide⟩

theorem blockAtMostOne_has_funnel {K b : ℕ} (r : Fin K) {s1 s2 : Fin b} (hne : s1 ≠ s2) :
    IsPairFunnel (blockAtMostOne K b) (finProdFinEquiv (r, s1)) (finProdFinEquiv (r, s2)) true := by
  let i := finProdFinEquiv (r, s1)
  let j := finProdFinEquiv (r, s2)
  have hij : i ≠ j := fun h => hne (congrArg Prod.snd (finProdFinEquiv.injective h))
  refine ⟨hij, ?_, ?_⟩
  · intro z
    let z1 := Function.update (Function.update z i true) j false
    let z2 := Function.update (Function.update z i false) j true
    change blockAtMostOne K b z1 = blockAtMostOne K b z2
    have hEq : (Finset.univ.filter fun r' : Fin K => blockOr K b r' z1 = true) =
        (Finset.univ.filter fun r' : Fin K => blockOr K b r' z2 = true) := by
      ext r'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hr' : r' = r
      · subst hr'
        have hz1 : blockOr K b r' z1 = true := by
          simp only [blockOr, decide_eq_true_eq]
          have hzi : z1 i = true := by
            dsimp only [z1]
            rw [Function.update_of_ne hij, Function.update_self]
          exact ⟨s1, hzi⟩
        have hz2 : blockOr K b r' z2 = true := by
          simp only [blockOr, decide_eq_true_eq]
          have hzj : z2 j = true := by
            dsimp only [z2]
            rw [Function.update_self]
          exact ⟨s2, hzj⟩
        simp [hz1, hz2]
      · have hSame (s : Fin b) : z1 (finProdFinEquiv (r', s)) = z2 (finProdFinEquiv (r', s)) := by
          have hni : finProdFinEquiv (r', s) ≠ i := fun h =>
            hr' (congrArg Prod.fst (finProdFinEquiv.injective h))
          have hnj : finProdFinEquiv (r', s) ≠ j := fun h =>
            hr' (congrArg Prod.fst (finProdFinEquiv.injective h))
          simp [z1, z2, Function.update_of_ne hni, Function.update_of_ne hnj]
        simp [blockOr, hSame]
    simp only [blockAtMostOne, hEq]
  · intro z
    let z1 := Function.update (Function.update z i true) j false
    let z3 := Function.update (Function.update z i true) j true
    change blockAtMostOne K b z1 = blockAtMostOne K b z3
    have hEq : (Finset.univ.filter fun r' : Fin K => blockOr K b r' z1 = true) =
        (Finset.univ.filter fun r' : Fin K => blockOr K b r' z3 = true) := by
      ext r'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hr' : r' = r
      · subst hr'
        have hz1 : blockOr K b r' z1 = true := by
          simp only [blockOr, decide_eq_true_eq]
          have hzi : z1 i = true := by
            dsimp only [z1]
            rw [Function.update_of_ne hij, Function.update_self]
          exact ⟨s1, hzi⟩
        have hz3 : blockOr K b r' z3 = true := by
          simp only [blockOr, decide_eq_true_eq]
          have hzi : z3 i = true := by
            dsimp only [z3]
            rw [Function.update_of_ne hij, Function.update_self]
          exact ⟨s1, hzi⟩
        simp [hz1, hz3]
      · have hSame (s : Fin b) : z1 (finProdFinEquiv (r', s)) = z3 (finProdFinEquiv (r', s)) := by
          have hni : finProdFinEquiv (r', s) ≠ i := fun h =>
            hr' (congrArg Prod.fst (finProdFinEquiv.injective h))
          have hnj : finProdFinEquiv (r', s) ≠ j := fun h =>
            hr' (congrArg Prod.fst (finProdFinEquiv.injective h))
          simp [z1, z3, Function.update_of_ne hni, Function.update_of_ne hnj]
        simp [blockOr, hSame]
    simp only [blockAtMostOne, hEq]

private noncomputable def prefBlockOr (K b : ℕ) (r : Fin K) (k : ℕ) : BooleanFunction (K * b) :=
  fun x => decide (∃ s : Fin b, s.val < k ∧ x (finProdFinEquiv (r, s)) = true)

private theorem synth_prefBlockOr {K b : ℕ} (hb : 1 ≤ b) (r : Fin K) :
    ∀ k : ℕ, 1 ≤ k → k ≤ b →
      Synthesis interpretation (inputs (K * b)) {prefBlockOr K b r k} (k - 1) := by
  intro k hk1
  induction k with
  | zero => omega
  | succ k ih =>
    intro hkb
    by_cases hk0 : k = 0
    · subst hk0
      have hFun : prefBlockOr K b r 1 = fun x => x (finProdFinEquiv (r, ⟨0, hb⟩)) := by
        funext x
        simp only [prefBlockOr]
        cases hx : x (finProdFinEquiv (r, ⟨0, hb⟩))
        · simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro s hs
          have hs0 : s = ⟨0, hb⟩ := Fin.ext (by dsimp; omega)
          simpa [hs0] using hx
        · simp only [decide_eq_true_eq]
          exact ⟨⟨0, hb⟩, by dsimp; omega, hx⟩
      rw [hFun]
      exact Synthesis.of_mem ⟨finProdFinEquiv (r, ⟨0, hb⟩), rfl⟩
    · have hkPos : 1 ≤ k := by omega
      have hIH := ih hkPos (by omega)
      let nextVar : BooleanFunction (K * b) := fun x => x (finProdFinEquiv (r, ⟨k, hkb⟩))
      have hNext : Synthesis interpretation (inputs (K * b)) {nextVar} 0 :=
        Synthesis.of_mem ⟨finProdFinEquiv (r, ⟨k, hkb⟩), rfl⟩
      have hBin := Synthesis.binary hIH hNext (op := Op.or)
      have hEq : (fun x => interpretation Op.or (fun i =>
          if i.val = 0 then prefBlockOr K b r k x else nextVar x)) = prefBlockOr K b r (k + 1) := by
        funext x
        change (prefBlockOr K b r k x || nextVar x) = prefBlockOr K b r (k + 1) x
        cases hPrev : prefBlockOr K b r k x <;> cases hCur : nextVar x <;>
          simp only [Bool.or_true, Bool.or_false]
        · symm
          simp only [prefBlockOr, decide_eq_false_iff_not, not_exists, not_and]
          intro s hs hxS
          have hlt : s.val < k ∨ s.val = k := by omega
          rcases hlt with hs' | hsEq
          · have : prefBlockOr K b r k x = true := by
              simp [prefBlockOr]; exact ⟨s, hs', hxS⟩
            simp_all
          · have : s = ⟨k, hkb⟩ := Fin.ext hsEq
            subst this
            simp [nextVar] at hCur
            simp_all
        · symm
          simp only [prefBlockOr, decide_eq_true_eq]
          exact ⟨⟨k, hkb⟩, by dsimp; omega, hCur⟩
        · symm
          simp only [prefBlockOr, decide_eq_true_eq] at hPrev ⊢
          obtain ⟨s, hs, hxS⟩ := hPrev
          exact ⟨s, by omega, hxS⟩
        · symm
          simp only [prefBlockOr, decide_eq_true_eq]
          exact ⟨⟨k, hkb⟩, by dsimp; omega, hCur⟩
      rw [hEq] at hBin
      simpa [Nat.sub_add_cancel hkPos] using hBin

private noncomputable def prefOr (K b k : ℕ) : BooleanFunction (K * b) :=
  fun x => decide (∃ r : Fin K, r.val < k ∧ blockOr K b r x = true)

private noncomputable def prefTwo (K b k : ℕ) : BooleanFunction (K * b) :=
  fun x => decide (2 ≤ (Finset.univ.filter fun r : Fin K => r.val < k ∧ blockOr K b r x = true).card)

private theorem synth_pref_two_blocks {K b : ℕ} :
    ∀ d : ℕ, d + 2 ≤ K →
      Synthesis interpretation (Set.range (blockOr K b))
        {prefOr K b (d + 2), prefTwo K b (d + 2)} (2 + 3 * d) := by
  intro d
  induction d with
  | zero =>
    intro hK
    let r0 : Fin K := ⟨0, by omega⟩
    let r1 : Fin K := ⟨1, by omega⟩
    let g0 := blockOr K b r0
    let g1 := blockOr K b r1
    have hr01 : ∀ r : Fin K, r.val < 2 → r = r0 ∨ r = r1 := fun r hr => by
      by_cases h0 : r.val = 0
      · exact Or.inl (Fin.ext (by dsimp [r0]; exact h0))
      · exact Or.inr (Fin.ext (by dsimp [r1]; omega))
    have h0 : g0 ∈ Set.range (blockOr K b) := ⟨r0, rfl⟩
    have h1 : g1 ∈ Set.range (blockOr K b) := ⟨r1, rfl⟩
    have h0s : Synthesis interpretation (Set.range (blockOr K b)) {g0} 0 := Synthesis.of_mem h0
    have h1s : Synthesis interpretation (Set.range (blockOr K b)) {g1} 0 := Synthesis.of_mem h1
    have hOr := Synthesis.binary h0s h1s Op.or
    have hAnd := Synthesis.binary h0s h1s Op.and
    have hOrEq : (fun x => interpretation Op.or (fun i => if i.val = 0 then g0 x else g1 x)) =
        prefOr K b 2 := by
      funext x
      change (g0 x || g1 x) = decide (∃ r : Fin K, r.val < 2 ∧ blockOr K b r x = true)
      cases hg0 : g0 x <;> cases hg1 : g1 x
      · have hNo : ¬ ∃ r : Fin K, r.val < 2 ∧ blockOr K b r x = true := by
          rintro ⟨r, hr, hTrue⟩
          rcases hr01 r hr with hEq | hEq <;> rw [hEq] at hTrue
          · change g0 x = true at hTrue; rw [hg0] at hTrue; cases hTrue
          · change g1 x = true at hTrue; rw [hg1] at hTrue; cases hTrue
        rw [decide_eq_false_iff_not.mpr hNo]; rfl
      · rw [decide_eq_true_eq.mpr ⟨r1, by dsimp [r1]; omega, hg1⟩]; rfl
      · rw [decide_eq_true_eq.mpr ⟨r0, by dsimp [r0]; omega, hg0⟩]; rfl
      · rw [decide_eq_true_eq.mpr ⟨r0, by dsimp [r0]; omega, hg0⟩]; rfl
    have hTwoEq : (fun x => interpretation Op.and (fun i => if i.val = 0 then g0 x else g1 x)) =
        prefTwo K b 2 := by
      funext x
      let C2 := Finset.univ.filter fun r : Fin K => r.val < 2 ∧ blockOr K b r x = true
      change (g0 x && g1 x) = decide (2 ≤ C2.card)
      cases hg0 : g0 x <;> cases hg1 : g1 x
      · have hSub1 : C2 ⊆ ∅ := fun r hr => by
          have hr1 := (Finset.mem_filter.mp hr).2
          rcases hr01 r hr1.1 with hEq | hEq
          · have hT := hr1.2; rw [hEq] at hT; change g0 x = true at hT; rw [hg0] at hT; cases hT
          · have hT := hr1.2; rw [hEq] at hT; change g1 x = true at hT; rw [hg1] at hT; cases hT
        have hC : C2.card = 0 := Finset.card_eq_zero.mpr (Finset.subset_empty.mp hSub1)
        rw [decide_eq_false_iff_not.mpr (by omega : ¬ 2 ≤ C2.card)]; rfl
      · have hSub1 : C2 ⊆ {r1} := fun r hr => by
          have hr1 := (Finset.mem_filter.mp hr).2
          rcases hr01 r hr1.1 with hEq | hEq
          · exfalso; have hT := hr1.2; rw [hEq] at hT; change g0 x = true at hT; rw [hg0] at hT; cases hT
          · exact Finset.mem_singleton.mpr hEq
        have hC : C2.card ≤ 1 := (Finset.card_le_card hSub1).trans (by rw [Finset.card_singleton])
        rw [decide_eq_false_iff_not.mpr (by omega : ¬ 2 ≤ C2.card)]; rfl
      · have hSub1 : C2 ⊆ {r0} := fun r hr => by
          have hr1 := (Finset.mem_filter.mp hr).2
          rcases hr01 r hr1.1 with hEq | hEq
          · exact Finset.mem_singleton.mpr hEq
          · exfalso; have hT := hr1.2; rw [hEq] at hT; change g1 x = true at hT; rw [hg1] at hT; cases hT
        have hC : C2.card ≤ 1 := (Finset.card_le_card hSub1).trans (by rw [Finset.card_singleton])
        rw [decide_eq_false_iff_not.mpr (by omega : ¬ 2 ≤ C2.card)]; rfl
      · have hTwo : 2 ≤ C2.card := by
          apply Finset.one_lt_card.mpr
          refine ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [r0]; omega, hg0⟩,
            r1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [r1]; omega, hg1⟩, ?_⟩
          intro hEq
          have := congrArg Fin.val hEq
          simp [r0, r1] at this
        rw [decide_eq_true_eq.mpr hTwo]; rfl
    rw [hOrEq] at hOr
    rw [hTwoEq] at hAnd
    refine (hOr.union hAnd).mono Set.Subset.rfl ?_ (by decide)
    intro f hf
    rcases hf with rfl | rfl <;> simp
  | succ d ih =>
    intro hK
    have hIH := ih (by omega)
    let k := d + 2
    let rk : Fin K := ⟨k, by omega⟩
    let gk := blockOr K b rk
    let S := Set.range (blockOr K b)
    let S1 := S ∪ {prefOr K b k, prefTwo K b k}
    let both : BooleanFunction (K * b) := fun x =>
      interpretation Op.and (fun i => if i.val = 0 then prefOr K b k x else gk x)
    have hMemOr : prefOr K b k ∈ S1 := Set.mem_union_right _ (Set.mem_insert ..)
    have hMemTwo : prefTwo K b k ∈ S1 := Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)
    have hMemGk : gk ∈ S1 := Set.mem_union_left _ ⟨rk, rfl⟩
    have hMemOrS : Synthesis interpretation S1 {prefOr K b k} 0 := Synthesis.of_mem hMemOr
    have hMemGkS : Synthesis interpretation S1 {gk} 0 := Synthesis.of_mem hMemGk
    have hStep1 : Synthesis interpretation S1 {both} 1 :=
      Synthesis.binary hMemOrS hMemGkS Op.and
    have hStep2 : Synthesis interpretation (S1 ∪ {both}) {prefOr K b (k + 1)} 1 := by
      have hOr2 : Synthesis interpretation (S1 ∪ {both}) {prefOr K b k} 0 :=
        Synthesis.of_mem (Set.mem_union_left _ hMemOr)
      have hGk2 : Synthesis interpretation (S1 ∪ {both}) {gk} 0 :=
        Synthesis.of_mem (Set.mem_union_left _ hMemGk)
      have h := Synthesis.binary hOr2 hGk2 Op.or
      have hOrEq : (fun x => interpretation Op.or (fun i =>
          if i.val = 0 then prefOr K b k x else gk x)) = prefOr K b (k + 1) := by
        funext x
        change (prefOr K b k x || gk x) = decide (∃ r : Fin K, r.val < k + 1 ∧ blockOr K b r x = true)
        cases hP : prefOr K b k x <;> cases hG : gk x
        · have hNo : ¬ ∃ r : Fin K, r.val < k + 1 ∧ blockOr K b r x = true := by
            rintro ⟨r, hlt, hrTrue⟩
            have hrk : r.val < k ∨ r.val = k := by omega
            rcases hrk with hlt' | hEq
            · have hT : prefOr K b k x = true := by
                simp only [prefOr, decide_eq_true_eq]
                exact ⟨r, hlt', hrTrue⟩
              rw [hT] at hP
              cases hP
            · have hEqRk : r = rk := Fin.ext (by dsimp [rk]; exact hEq)
              rw [hEqRk] at hrTrue
              change gk x = true at hrTrue
              rw [hG] at hrTrue
              cases hrTrue
          rw [decide_eq_false_iff_not.mpr hNo]; rfl
        · rw [decide_eq_true_eq.mpr ⟨rk, by dsimp [rk]; omega, hG⟩]; rfl
        · simp only [prefOr, decide_eq_true_eq] at hP
          obtain ⟨r, hr, hTr⟩ := hP
          rw [decide_eq_true_eq.mpr ⟨r, by omega, hTr⟩]; rfl
        · rw [decide_eq_true_eq.mpr ⟨rk, by dsimp [rk]; omega, hG⟩]; rfl
      rwa [hOrEq] at h
    have hStep3 : Synthesis interpretation ((S1 ∪ {both}) ∪ {prefOr K b (k + 1)})
        {prefTwo K b (k + 1)} 1 := by
      have hTwo3 : Synthesis interpretation ((S1 ∪ {both}) ∪ {prefOr K b (k + 1)})
          {prefTwo K b k} 0 :=
        Synthesis.of_mem (Set.mem_union_left _ (Set.mem_union_left _ hMemTwo))
      have hBoth3 : Synthesis interpretation ((S1 ∪ {both}) ∪ {prefOr K b (k + 1)}) {both} 0 :=
        Synthesis.of_mem (Set.mem_union_left _ (Set.mem_union_right _ rfl))
      have h := Synthesis.binary hTwo3 hBoth3 Op.or
      have hTwoEq : (fun x => interpretation Op.or (fun i =>
          if i.val = 0 then prefTwo K b k x else both x)) = prefTwo K b (k + 1) := by
        funext x
        let Ck := Finset.univ.filter fun r : Fin K => r.val < k ∧ blockOr K b r x = true
        let Ck1 := Finset.univ.filter fun r : Fin K => r.val < k + 1 ∧ blockOr K b r x = true
        change (prefTwo K b k x || (prefOr K b k x && gk x)) = decide (2 ≤ Ck1.card)
        by_cases hG : gk x = true
        · have hNotMem : rk ∉ Ck := fun hm => by
            have := (Finset.mem_filter.mp hm).2.1
            dsimp [rk] at this
            omega
          have hIns : Ck1 = insert rk Ck := by
            ext r
            simp only [Ck1, Ck, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, hrT⟩
              by_cases hEq : r.val = k
              · left; exact Fin.ext (by dsimp [rk]; exact hEq)
              · right; exact ⟨by omega, hrT⟩
            · rintro (hEq | ⟨hlt, hrT⟩)
              · rw [hEq]; exact ⟨by dsimp [rk]; omega, hG⟩
              · exact ⟨by omega, hrT⟩
          have hCard1 : Ck1.card = Ck.card + 1 := by
            rw [hIns, Finset.card_insert_of_notMem hNotMem]
          have hNonEmp : prefOr K b k x = true ↔ 1 ≤ Ck.card := by
            constructor
            · intro hPr
              simp only [prefOr, decide_eq_true_eq] at hPr
              obtain ⟨r, hr, hrT⟩ := hPr
              exact Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hrT⟩⟩
            · intro hPos
              obtain ⟨r, hr⟩ := Finset.card_pos.mp hPos
              have hr2 := (Finset.mem_filter.mp hr).2
              simp only [prefOr, decide_eq_true_eq]
              exact ⟨r, hr2.1, hr2.2⟩
          have hCk2_T : prefTwo K b k x = true → 2 ≤ Ck.card := fun hT => by
            simpa [prefTwo, Ck] using hT
          cases hT2 : prefTwo K b k x <;> cases hT1 : prefOr K b k x
          · have hCk0 : Ck.card = 0 := by
              by_contra hPos
              have h1 : prefOr K b k x = true := hNonEmp.mpr (by omega)
              rw [h1] at hT1
              cases hT1
            rw [hG, decide_eq_false_iff_not.mpr (by omega : ¬ 2 ≤ Ck1.card)]
            rfl
          · have hCkPos : 1 ≤ Ck.card := hNonEmp.mp hT1
            rw [hG, decide_eq_true_eq.mpr (by omega : 2 ≤ Ck1.card)]
            rfl
          · have hCk2 : 2 ≤ Ck.card := hCk2_T hT2
            rw [hG, decide_eq_true_eq.mpr (by omega : 2 ≤ Ck1.card)]
            rfl
          · have hCk2 : 2 ≤ Ck.card := hCk2_T hT2
            rw [hG, decide_eq_true_eq.mpr (by omega : 2 ≤ Ck1.card)]
            rfl
        · have hGF : gk x = false := Bool.eq_false_of_not_eq_true hG
          have hSame : Ck1 = Ck := by
            ext r
            simp only [Ck1, Ck, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hrT⟩
              have hne : r.val ≠ k := by
                intro hEq
                have hEqRk : r = rk := Fin.ext (by dsimp [rk]; exact hEq)
                rw [hEqRk] at hrT
                simp_all [gk]
              exact ⟨by omega, hrT⟩
            · rintro ⟨hlt, hrT⟩
              exact ⟨by omega, hrT⟩
          have hCkEq : Ck1.card = Ck.card := congrArg Finset.card hSame
          cases hT2 : prefTwo K b k x
          · have hNot2 : ¬ 2 ≤ Ck.card := by simpa [prefTwo, Ck] using hT2
            rw [hGF, decide_eq_false_iff_not.mpr (by omega : ¬ 2 ≤ Ck1.card)]
            simp
          · have hLe2 : 2 ≤ Ck.card := by simpa [prefTwo, Ck] using hT2
            rw [hGF, decide_eq_true_eq.mpr (by omega : 2 ≤ Ck1.card)]
            simp
      rwa [hTwoEq] at h
    have hChain := hStep1.comp (hStep2.comp hStep3)
    have hNarrow : Synthesis interpretation S1 {prefOr K b (k + 1), prefTwo K b (k + 1)} 3 := by
      refine hChain.mono Set.Subset.rfl ?_ (by decide)
      intro f hf
      rcases hf with rfl | rfl
      · exact Set.mem_union_right _ (Set.mem_union_left _ rfl)
      · exact Set.mem_union_right _ (Set.mem_union_right _ rfl)
    exact (hIH.trans hNarrow).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- Exact De Morgan circuit size upper bound `K * b + 2 * K - 3` for `blockAtMostOne K b`
when `2 ≤ K` and `1 ≤ b`. -/
theorem blockAtMostOne_complexity_le {K b : ℕ} (hK : 2 ≤ K) (hb : 1 ≤ b) :
    complexity interpretation (single (blockAtMostOne K b)) ≤ K * b + 2 * K - 3 := by
  have hStage1 : Synthesis interpretation (inputs (K * b)) (Set.range (blockOr K b)) (K * (b - 1)) := by
    have hFam := Synthesis.family (fun r : Fin K => blockOr K b r) (fun _ => b - 1) (fun r => by
      have h := synth_prefBlockOr hb r b hb le_rfl
      have hEq : prefBlockOr K b r b = blockOr K b r := by
        funext x
        simp [prefBlockOr, blockOr]
      rwa [hEq] at h)
    simpa [Finset.sum_const, smul_eq_mul, Finset.card_fin] using hFam
  have hStage2 : Synthesis interpretation (Set.range (blockOr K b))
      {prefTwo K b K} (2 + 3 * (K - 2)) := by
    have h := synth_pref_two_blocks (K := K) (b := b) (K - 2) (by omega)
    rw [Nat.sub_add_cancel hK] at h
    exact h.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)) le_rfl
  have hStage12 : Synthesis interpretation (inputs (K * b)) {prefTwo K b K}
      (K * (b - 1) + (2 + 3 * (K - 2))) :=
    hStage1.trans (hStage2.mono Set.subset_union_right Set.Subset.rfl le_rfl)
  have hStage3 := Synthesis.unary hStage12 (op := Op.not)
  have hFinalEq : (fun x => interpretation Op.not (fun _ => prefTwo K b K x)) = blockAtMostOne K b := by
    funext x
    change (!(prefTwo K b K x)) = blockAtMostOne K b x
    have hFilter : (Finset.univ.filter fun r : Fin K => r.val < K ∧ blockOr K b r x = true) =
        Finset.univ.filter fun r : Fin K => blockOr K b r x = true := by
      ext r
      simp
    simp only [prefTwo, blockAtMostOne, hFilter]
    by_cases h2 : 2 ≤ (Finset.univ.filter fun r : Fin K => blockOr K b r x = true).card
    · have hNot1 : ¬ (Finset.univ.filter fun r : Fin K => blockOr K b r x = true).card ≤ 1 := by omega
      simp [h2, hNot1]
    · have hLe1 : (Finset.univ.filter fun r : Fin K => blockOr K b r x = true).card ≤ 1 := by omega
      simp [h2, hLe1]
  rw [hFinalEq] at hStage3
  obtain ⟨c, hc, hSize⟩ := hStage3.exists_circuit
  have hComp := complexity_le_of_computes c hc
  have hArith : K * (b - 1) + (2 + 3 * (K - 2)) + 1 ≤ K * b + 2 * K - 3 := by
    have hMul : K * (b - 1) + K = K * b := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hb]
    omega
  omega

/-- At `K = 8, b = 8`, `blockAtMostOne 8 8` has accepting sparsity `≤ 2 ^ 12` and all its one-bit
branches are nonconstant, yet its De Morgan complexity is at most `77`, strictly below
`2 * (64 - 12 - 1) = 102`, demonstrating sharpness of the pair-funnel hypothesis. -/
theorem blockAtMostOne_beats_twoN_at_8_8 :
    (acceptingTables (blockAtMostOne 8 8)).card ≤ 2 ^ 12 ∧
    complexity interpretation (single (blockAtMostOne 8 8)) ≤ 77 ∧
    77 < 2 * (8 * 8 - 12 - 1) := by
  have hCard := (blockAtMostOne_accepting_card 8 8).trans (by decide : 1 + 8 * 2 ^ 8 ≤ 2 ^ 12)
  have hComp := (blockAtMostOne_complexity_le (K := 8) (b := 8) (by decide) (by decide)).trans
    (by decide : 8 * 8 + 2 * 8 - 3 ≤ 77)
  exact ⟨hCard, hComp, by decide⟩

#print axioms eval_substitute_effMask
#print axioms card_inessMask_le
#print axioms earliest_fresh_double_loss_or_funnel
#print axioms adaptive_eff_noFunnel_bound
#print axioms mcspSquare_earliest_fresh_dichotomy
#print axioms mcspSquare_noFunnel_twoN
#print axioms blockAtMostOne_accepting_card
#print axioms blockAtMostOne_branches_nonconstant
#print axioms blockAtMostOne_has_funnel
#print axioms blockAtMostOne_complexity_le
#print axioms blockAtMostOne_beats_twoN_at_8_8

end PvsNP.Frontier.EarliestFresh
