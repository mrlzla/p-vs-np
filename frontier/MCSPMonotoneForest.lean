module

public import MCSPTwoCornerStructure

/-!
Monotone OR/AND forest decomposition for sparse two-corner circuits.

Starting from `TwoCornerStructure`, this file formalizes:
* Local anomaly cut sets `HasRepeat`, `EnteredByOtherBad`, `CutNode`, `cutInputs`.
* Monochromatic dual segments `segEdge`, `SegAnc`, `segTopOR`, `segTopAND`.
* Corner-bypassing demand predicates `AltNeed1` / `AltNeed0`, their soundness,
  and their linear `H1` / `H0` leaf bounds.
* Sparse bounds (`≤ O(B + slack)`) on `segTopOR`, `segTopAND`, `TransOA`, `TransAO`,
  `U_pure1`, and `U_pure0`.
* Isolated monotone `.or` / `.and` components `orInputs` / `andInputs` with soundness,
  size-`≤ 1` filters `SmallOR` / `SmallAND`, `StructuredInput`, and `clean_case2_structure`.
-/

@[expose] public section

namespace PvsNP.Frontier.MonotoneForest

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure

open scoped Classical

variable {n g : ℕ}

/-! ### Helper lemmas on `Op`, arities, and `selectedPins` -/

private theorem op_card_wires_le (op : Op) (wires : Fin (signature.Arity op) → Wire n g) :
    (Finset.univ.image wires).card ≤ 2 := by
  have h1 : (Finset.univ.image wires).card ≤
      (Finset.univ : Finset (Fin (signature.Arity op))).card := Finset.card_image_le
  have h2 : (Finset.univ : Finset (Fin (signature.Arity op))).card = signature.Arity op := by
    simp
  have h3 : signature.Arity op ≤ 2 := by
    cases op <;> simp
  omega

private theorem op_selectedPins_card_le (op : Op) (v : Fin (signature.Arity op) → Bool) :
    (selectedPins op v).card ≤ 2 := by
  have h1 : (selectedPins op v).card ≤
      (Finset.univ : Finset (Fin (signature.Arity op))).card := Finset.card_le_univ _
  have h2 : (Finset.univ : Finset (Fin (signature.Arity op))).card = signature.Arity op := by
    simp
  have h3 : signature.Arity op ≤ 2 := by
    cases op <;> simp
  omega

private theorem op_selectedPins_card_le_one (op : Op) (v : Fin (signature.Arity op) → Bool)
    (h : ¬ (op = .and ∧ interpretation op v = true) ∧
      ¬ (op = .or ∧ interpretation op v = false)) :
    (selectedPins op v).card ≤ 1 := by
  cases op with
  | const b => simp [selectedPins]
  | not =>
    have h1 : (selectedPins .not v).card ≤
        (Finset.univ : Finset (Fin (signature.Arity .not))).card := Finset.card_le_univ _
    simpa [signature] using h1
  | and =>
    have hF : interpretation .and v = false :=
      Bool.eq_false_iff.mpr fun hT => h.1 ⟨rfl, hT⟩
    cases h0 : v 0 with
    | false => simp [selectedPins, h0]
    | true =>
      have h1 : v 1 = false := by
        cases h1' : v 1 <;> simp_all [interpretation]
      simp [selectedPins, h0, h1]
  | or =>
    have hT : interpretation .or v = true :=
      Bool.eq_true_of_not_eq_false fun hF => h.2 ⟨rfl, hF⟩
    cases h0 : v 0 with
    | true => simp [selectedPins, h0]
    | false =>
      have h1 : v 1 = true := by
        cases h1' : v 1 <;> simp_all [interpretation]
      simp [selectedPins, h0, h1]

private theorem op_selectedPins_nonempty (op : Op) (hOp : op = .and ∨ op = .or)
    (v : Fin (signature.Arity op) → Bool) :
    (selectedPins op v).Nonempty := by
  rcases hOp with rfl | rfl
  · cases h0 : v 0 <;> cases h1 : v 1 <;> simp [selectedPins, h0, h1]
  · cases h0 : v 0 <;> cases h1 : v 1 <;> simp [selectedPins, h0, h1]

private theorem op_argStates_snd_eq (op : Op) (hOp : op = .and ∨ op = .or)
    (wires : Fin (signature.Arity op) → Wire n g) (v : Fin (signature.Arity op) → Bool)
    {key : Wire n g × Bool}
    (hKey : key ∈ argumentStates op wires v) :
    key.2 = interpretation op v := by
  rcases hOp with rfl | rfl
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hKey
    cases hv0 : v 0 <;> cases hv1 : v 1 <;> fin_cases a <;>
      simp [selectedPins, interpretation, hv0, hv1] at ha ⊢
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hKey
    cases hv0 : v 0 <;> cases hv1 : v 1 <;> fin_cases a <;>
      simp [selectedPins, interpretation, hv0, hv1] at ha ⊢

private theorem op_and_eq_false (op : Op) (hOp : op = .and)
    (wires : Fin (signature.Arity op) → Wire n g) (y : Wire n g → Bool)
    {a : Fin (signature.Arity op)} (hy : y (wires a) = false) :
    interpretation op (fun s => y (wires s)) = false := by
  subst hOp
  fin_cases a <;> simp_all [interpretation]

private theorem op_or_eq_true (op : Op) (hOp : op = .or)
    (wires : Fin (signature.Arity op) → Wire n g) (y : Wire n g → Bool)
    {a : Fin (signature.Arity op)} (hy : y (wires a) = true) :
    interpretation op (fun s => y (wires s)) = true := by
  subst hOp
  fin_cases a <;> simp_all [interpretation]

private theorem wire_in_req_of_not_badGates {p : Program signature n g} {root : Wire n g}
    {k : Fin g} (hnb : k ∉ badGates p root) (a : Fin (signature.Arity (p.lines k).op)) :
    ∃ v : Bool, ((p.lines k).wires a, v) ∈ req p root k := by
  classical
  have hS := not_bad_structure p root hnb
  have hInj : Function.Injective (p.lines k).wires := by
    intro x y hxy
    by_contra hne
    exact hS.2.2.2 x y hne hxy
  have hCardWires : (Finset.univ.image (p.lines k).wires).card = 2 := by
    rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin]
    rcases hS.1 with hOp | hOp <;> rw [hOp]
  have hSubWires : (req p root k).image Prod.fst ⊆ Finset.univ.image (p.lines k).wires := by
    intro w hw
    obtain ⟨key, hKey, rfl⟩ := Finset.mem_image.mp hw
    rcases Finset.mem_union.mp hKey with hL | hR
    · by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
      · simp only [reqCorner, hg, ite_true, cornerArguments] at hL
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hL
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
      · simp [reqCorner, hg] at hL
    · by_cases hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
      · simp only [reqCorner, hg, ite_true, cornerArguments] at hR
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hR
        exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
      · simp [reqCorner, hg] at hR
  have hSndVal : ∀ key ∈ req p root k, key.2 ∈ valSet p root k := by
    intro key hKey
    have hVal : Need p root (.gate k, key.2) := by
      rcases Finset.mem_union.mp hKey with hL | hR
      · by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
        · simp only [reqCorner, hg, ite_true, cornerArguments] at hL
          have hEq := op_argStates_snd_eq (p.lines k).op hS.1 (p.lines k).wires
            (fun s => cornerValue p false ((p.lines k).wires s)) hL
          rw [← cornerValue_gate] at hEq
          exact Or.inl (hEq ▸ hg)
        · simp [reqCorner, hg] at hL
      · by_cases hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
        · simp only [reqCorner, hg, ite_true, cornerArguments] at hR
          have hEq := op_argStates_snd_eq (p.lines k).op hS.1 (p.lines k).wires
            (fun s => cornerValue p true ((p.lines k).wires s)) hR
          rw [← cornerValue_gate] at hEq
          exact Or.inr (hEq ▸ hg)
        · simp [reqCorner, hg] at hR
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hVal⟩
  have hFstGe2 : 2 ≤ ((req p root k).image Prod.fst).card := by
    by_contra hLt
    have hLe1 : ((req p root k).image Prod.fst).card ≤ 1 := by omega
    have hProd : req p root k ⊆ ((req p root k).image Prod.fst) ×ˢ (valSet p root k) := by
      intro key hKey
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨key, hKey, rfl⟩, hSndVal key hKey⟩
    have hCardLe := (Finset.card_le_card hProd).trans_eq (Finset.card_product _ _)
    have hMul : ((req p root k).image Prod.fst).card * (valSet p root k).card ≤
        1 * (valSet p root k).card := Nat.mul_le_mul_right _ hLe1
    omega
  have hEq : (req p root k).image Prod.fst = Finset.univ.image (p.lines k).wires :=
    Finset.eq_of_subset_of_card_le hSubWires (by rw [hCardWires]; exact hFstGe2)
  have hMem : (p.lines k).wires a ∈ (req p root k).image Prod.fst := by
    rw [hEq]; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  obtain ⟨key, hKey, hFst⟩ := Finset.mem_image.mp hMem
  exact ⟨key.2, hFst ▸ by cases key; exact hKey⟩

private theorem corner_arg_mem_reqCorner {p : Program signature n g} {root : Wire n g} {b : Bool}
    {k : Fin g} (hk : NeedCorner p root b (.gate k, cornerValue p b (.gate k)))
    {a : Fin (signature.Arity (p.lines k).op)}
    (ha : a ∈ selectedPins (p.lines k).op (fun s => cornerValue p b ((p.lines k).wires s))) :
    ((p.lines k).wires a, cornerValue p b ((p.lines k).wires a)) ∈ reqCorner p root b k := by
  classical
  simp only [reqCorner, hk, ite_true, cornerArguments, argumentStates]
  exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

private theorem needCorner_child_of_reqCorner {p : Program signature n g} {root : Wire n g} {b : Bool}
    {k : Fin g} {w : Wire n g} {v : Bool} (hMem : (w, v) ∈ reqCorner p root b k) :
    NeedCorner p root b (w, v) := by
  by_cases hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k))
  · simp only [reqCorner, hg, ite_true] at hMem
    exact NeedCorner.argument hg hMem
  · simp [reqCorner, hg] at hMem

private theorem needCorner_parent_of_ne_root {p : Program signature n g} {root : Wire n g} {b : Bool}
    {key : Wire n g × Bool} (h : NeedCorner p root b key) (hNe : key ≠ (root, true)) :
    ∃ p' : Fin g, key ∈ reqCorner p root b p' := by
  cases h with
  | output => exact (hNe rfl).elim
  | @argument p' hp' _ ha' =>
    exact ⟨p', by simp only [reqCorner, hp', ite_true]; exact ha'⟩

private theorem reqCorner_subset_req_left {p : Program signature n g} {root : Wire n g} {k : Fin g} :
    reqCorner p root false k ⊆ req p root k := Finset.subset_union_left

private theorem reqCorner_subset_req_right {p : Program signature n g} {root : Wire n g} {k : Fin g} :
    reqCorner p root true k ⊆ req p root k := Finset.subset_union_right

private theorem card_selectedPins_of_not_badFlip {p : Program signature n g} {root : Wire n g}
    {k : Fin g} (hk : k ∉ badFlip p root) :
    (NeedCorner p root true (.gate k, cornerValue p true (.gate k)) →
      (selectedPins (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s))).Nonempty) ∧
    (NeedCorner p root false (.gate k, cornerValue p false (.gate k)) →
      (selectedPins (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s))).Nonempty) := by
  have hnb := (not_s0_s1_of_not_badFlip hk).1
  have hOp := (not_bad_structure p root hnb).1
  exact ⟨fun _ => op_selectedPins_nonempty (p.lines k).op hOp _,
    fun _ => op_selectedPins_nonempty (p.lines k).op hOp _⟩

/-! ### Cleanliness cut sets: `HasRepeat`, `EnteredByOtherBad`, `CutNode`, `cutInputs` -/

/-- Gate `k` requests a state belonging to `repeatStates p root`. -/
def HasRepeat (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  ∃ s ∈ req p root k, s ∈ repeatStates p root

/-- Clean dual gate `k` whose `dualChild` is a gate in `otherBad p root`. -/
def EnteredByOtherBad (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  k ∈ goodDual p root ∧ ∃ j ∈ otherBad p root, dualChild p k = .gate j

/-- Direct wires of `badGates p root` (the only gates allowed to omit wires from `req`). -/
noncomputable def badGatesTargets (p : Program signature n g) (root : Wire n g) :
    Finset (Wire n g) := open scoped Classical in
  (badGates p root).biUnion fun m => Finset.univ.image (p.lines m).wires

/-- Unused gates with opcode `.not` (arity 1, saving 1 target wire per gate). -/
noncomputable def badNot (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (badGates p root).filter fun m => (p.lines m).op = .not

/-- Base local-anomaly gates: `otherBad` or requesting a repeated state. -/
noncomputable def CutGate (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in
  otherBad p root ∪ Finset.univ.filter (HasRepeat p root)

/-- Stop gates: `CutGate` plus gates whose wires are targeted by `badGates`. -/
noncomputable def StopGate (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in
  CutGate p root ∪ Finset.univ.filter fun k => (.gate k : Wire n g) ∈ badGatesTargets p root

/-- Full local cut condition blocking segment membership. -/
def CutNode (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  k ∈ StopGate p root ∨ EnteredByOtherBad p root k

/-- Cut endpoints carrying the value requested by the indicated corner. -/
noncomputable def cornerCutNodes (p : Program signature n g) (root : Wire n g) (b : Bool) :
    Finset (Fin g) :=
  Finset.univ.filter fun k => CutNode p root k ∧ cornerValue p b (.gate k) = b

/-- These are the only cut endpoints that can be used with both corner values. -/
noncomputable def dualCutNodes (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  cornerCutNodes p root false ∩ cornerCutNodes p root true

theorem cornerCutNodes_subset (p : Program signature n g) (root : Wire n g) (b : Bool) :
    cornerCutNodes p root b ⊆ Finset.univ.filter (CutNode p root) :=
  fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.1⟩

theorem dualCutNodes_subset (p : Program signature n g) (root : Wire n g) :
    dualCutNodes p root ⊆ Finset.univ.filter (CutNode p root) :=
  Finset.inter_subset_left.trans (cornerCutNodes_subset p root false)

theorem card_cornerCutNodes_add (p : Program signature n g) (root : Wire n g) :
    (cornerCutNodes p root false).card + (cornerCutNodes p root true).card ≤
      (Finset.univ.filter (CutNode p root)).card + (dualCutNodes p root).card := by
  rw [← Finset.card_union_add_card_inter]
  exact Nat.add_le_add_right (Finset.card_le_card
    (Finset.union_subset (cornerCutNodes_subset p root false) (cornerCutNodes_subset p root true))) _

/-- Input coordinates touched by `repeatStates` or `StopGate` wires. -/
noncomputable def cutInputs (p : Program signature n g) (root : Wire n g) : Finset (Fin n) :=
  open scoped Classical in
  Finset.univ.filter fun i =>
    ((.input i : Wire n g), false) ∈ repeatStates p root ∨
    ((.input i : Wire n g), true) ∈ repeatStates p root ∨
    ∃ k ∈ StopGate p root, ∃ a, (p.lines k).wires a = .input i

theorem card_hasRepeat_le (p : Program signature n g) (root : Wire n g) :
    (Finset.univ.filter (HasRepeat p root)).card ≤ 2 * shared p root := by
  classical
  let V := Finset.univ.filter (HasRepeat p root)
  have hInter : ∀ k ∈ V, 1 ≤ (req p root k ∩ repeatStates p root).card := by
    intro k hk
    obtain ⟨s, hs1, hs2⟩ := (Finset.mem_filter.mp hk).2
    exact Finset.card_pos.mpr ⟨s, Finset.mem_inter.mpr ⟨hs1, hs2⟩⟩
  have hMul := mul_card_le_of_inter_req p root V (repeatStates p root) 1 hInter
  have hRep := card_repeatStates_le_shared p root
  rw [one_mul] at hMul
  dsimp only [V] at hMul
  omega

theorem card_enteredByOtherBad_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (Finset.univ.filter (EnteredByOtherBad p root)).card ≤
      (otherBad p root).card + shared p root := by
  classical
  let V := Finset.univ.filter (EnteredByOtherBad p root)
  let S := (otherBad p root).image fun j : Fin g => ((.gate j : Wire n g), true)
  have hS : S.card ≤ (otherBad p root).card := Finset.card_image_le
  have hInter : ∀ k ∈ V, 1 ≤ (req p root k ∩ S).card := by
    intro k hk
    obtain ⟨hkG, j, hjB, hjD⟩ := (Finset.mem_filter.mp hk).2
    have hnb : k ∉ badGates p root :=
      (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG).2)).1
    have hDual := (goodDual_iff.mp hkG).1
    have hMem : (dualChild p k, true) ∈ req p root k := by
      rcases hDual with hDA | hDO
      · exact (dualAND_children h0 h1 hnb hDA).2.2.2.1
      · exact (dualOR_children h0 h1 hnb hDO).2.2.1
    rw [hjD] at hMem
    exact Finset.card_pos.mpr ⟨(.gate j, true),
      Finset.mem_inter.mpr ⟨hMem, Finset.mem_image.mpr ⟨j, hjB, rfl⟩⟩⟩
  have hMul := mul_card_le_of_inter_req p root V S 1 hInter
  rw [one_mul] at hMul
  dsimp only [V] at hMul
  omega

theorem card_badGatesTargets_le (p : Program signature n g) (root : Wire n g) :
    (badGatesTargets p root).card ≤ 2 * (badGates p root).card := by
  classical
  calc
    (badGatesTargets p root).card ≤
        ∑ m ∈ badGates p root, (Finset.univ.image (p.lines m).wires).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ badGates p root, 2 := Finset.sum_le_sum fun m _ => op_card_wires_le _ _
    _ = 2 * (badGates p root).card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]

theorem card_cutGate_le_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (CutGate p root).card ≤ 56 * slack p root := by
  have h1' : (CutGate p root).card ≤ (otherBad p root).card +
      (Finset.univ.filter (HasRepeat p root)).card := Finset.card_union_le ..
  have hOB := card_otherBad_le_slack p root h0 h1
  have hHR := card_hasRepeat_le p root
  have hSh : shared p root ≤ slack p root := by unfold slack; omega
  omega

theorem card_stopGate_le_unused_and_shared (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (StopGate p root).card ≤ 47 * (∑ k : Fin g, unused p root k) + 56 * shared p root := by
  classical
  let gateTargets := Finset.univ.filter fun k : Fin g =>
    (.gate k : Wire n g) ∈ badGatesTargets p root
  have hInj : Function.Injective (fun k : Fin g => (.gate k : Wire n g)) :=
    fun _ _ h => by cases h; rfl
  have hSub : gateTargets.image (fun k : Fin g => (.gate k : Wire n g)) ⊆ badGatesTargets p root := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hk).2
  have hGT : gateTargets.card ≤ (badGatesTargets p root).card := by
    rw [← Finset.card_image_of_injective gateTargets hInj]
    exact Finset.card_le_card hSub
  have hU : (StopGate p root).card ≤ (CutGate p root).card + gateTargets.card :=
    Finset.card_union_le ..
  have hCG : (CutGate p root).card ≤ (otherBad p root).card +
      (Finset.univ.filter (HasRepeat p root)).card := Finset.card_union_le ..
  have hOther := card_otherBad_le p root h0 h1
  have hRepeat := card_hasRepeat_le p root
  have hBT := card_badGatesTargets_le p root
  have hBG := card_badGates_le p root
  omega

theorem card_stopGate_le_56_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (StopGate p root).card ≤ 56 * slack p root := by
  have h := card_stopGate_le_unused_and_shared p root h0 h1
  unfold slack
  omega

theorem card_stopGate_le_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (StopGate p root).card ≤ 58 * slack p root :=
  (card_stopGate_le_56_slack p root h0 h1).trans (by omega)

theorem card_cutNode_le_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (Finset.univ.filter (CutNode p root)).card ≤ 113 * slack p root := by
  classical
  have hSub : Finset.univ.filter (CutNode p root) ⊆
      StopGate p root ∪ Finset.univ.filter (EnteredByOtherBad p root) := by
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with hS | hE
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩)
  have hU := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  have hSG := card_stopGate_le_slack p root h0 h1
  have hEB := card_enteredByOtherBad_le p root h0 h1
  have hOB := card_otherBad_le_slack p root h0 h1
  have hSh : shared p root ≤ slack p root := by unfold slack; omega
  omega

theorem card_badGatesTargets_add_badNot_le (p : Program signature n g) (root : Wire n g) :
    (badGatesTargets p root).card + (badNot p root).card ≤ 2 * (badGates p root).card := by
  classical
  have hNotSub : badNot p root ⊆ badGates p root := Finset.filter_subset _ _
  have hSplit : (badNot p root).card + (badGates p root \ badNot p root).card =
      (badGates p root).card := by
    rw [add_comm]
    exact Finset.card_sdiff_add_card_eq_card hNotSub
  have hBound (m : Fin g) : (Finset.univ.image (p.lines m).wires).card ≤
      if m ∈ badNot p root then 1 else 2 := by
    by_cases hm : m ∈ badNot p root
    · simp only [hm, ite_true]
      have hOp : (p.lines m).op = .not := (Finset.mem_filter.mp hm).2
      refine Finset.card_image_le.trans ?_
      simp [hOp]
    · simp only [hm, ite_false]
      exact op_card_wires_le _ _
  have hSplitSum : (∑ m ∈ badGates p root, if m ∈ badNot p root then 1 else 2) =
      (∑ _m ∈ badNot p root, 1) + ∑ _m ∈ badGates p root \ badNot p root, 2 := by
    rw [← Finset.sum_sdiff hNotSub (f := fun m => if m ∈ badNot p root then 1 else 2), add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun m hm => by simp [hm]
    · exact Finset.sum_congr rfl fun m hm => by simp [(Finset.mem_sdiff.mp hm).2]
  have hCalc : (badGatesTargets p root).card + (badNot p root).card ≤
      ((∑ _m ∈ badNot p root, 1) + ∑ _m ∈ badGates p root \ badNot p root, 2) +
        (badNot p root).card := by
    calc
      (badGatesTargets p root).card + (badNot p root).card ≤
          (∑ m ∈ badGates p root, (Finset.univ.image (p.lines m).wires).card) +
            (badNot p root).card := add_le_add Finset.card_biUnion_le le_rfl
      _ ≤ (∑ m ∈ badGates p root, if m ∈ badNot p root then 1 else 2) + (badNot p root).card :=
        add_le_add (Finset.sum_le_sum fun m _ => hBound m) le_rfl
      _ = _ := by rw [hSplitSum]
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hCalc
  omega

theorem card_enteredByOtherBad_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    2 * (Finset.univ.filter (EnteredByOtherBad p root)).card ≤
      4 * (badGates p root).card + 5 * shared p root := by
  classical
  let V := Finset.univ.filter (EnteredByOtherBad p root)
  let ST := (dualOtherBad p root).image fun j : Fin g => ((.gate j : Wire n g), true)
  let SF := (dualOtherBad p root).image fun j : Fin g => ((.gate j : Wire n g), false)
  have hST : ST.card ≤ (dualOtherBad p root).card := Finset.card_image_le
  have hSF : SF.card ≤ (dualOtherBad p root).card := Finset.card_image_le
  have hST_bool : ∀ s ∈ ST, s.2 = true := fun s hs => by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hs; rfl
  have hSF_bool : ∀ s ∈ SF, s.2 = false := fun s hs => by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hs; rfl
  have hMemBoth : ∀ k ∈ V,
      1 ≤ (req p root k ∩ ST).card ∧ 1 ≤ (req p root k ∩ SF).card := by
    intro k hk
    obtain ⟨hkG, j, hjB, hjD⟩ := (Finset.mem_filter.mp hk).2
    have hnb : k ∉ badGates p root :=
      (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG).2)).1
    have hDual := (goodDual_iff.mp hkG).1
    have hMemT : (dualChild p k, true) ∈ req p root k := by
      rcases hDual with hDA | hDO
      · exact (dualAND_children h0 h1 hnb hDA).2.2.2.1
      · exact (dualOR_children h0 h1 hnb hDO).2.2.1
    have hMemF : (dualChild p k, false) ∈ req p root k := by
      rcases hDual with hDA | hDO
      · exact (dualAND_children h0 h1 hnb hDA).2.2.1
      · exact (dualOR_children h0 h1 hnb hDO).2.2.2.1
    have hjV0 : cornerValue p false (.gate j) = false := by
      rw [← hjD]
      rcases hDual with hDA | hDO
      · exact (dualAND_children h0 h1 hnb hDA).2.2.2.2.2.2.2.2.1
      · exact (dualOR_children h0 h1 hnb hDO).2.2.2.2.2.2.2.2.2.1
    have hjV1 : cornerValue p true (.gate j) = true := by
      rw [← hjD]
      rcases hDual with hDA | hDO
      · exact (dualAND_children h0 h1 hnb hDA).2.2.2.2.2.2.2.2.2.1
      · exact (dualOR_children h0 h1 hnb hDO).2.2.2.2.2.2.2.2.1
    have hjDualOB : j ∈ dualOtherBad p root := Finset.mem_filter.mpr ⟨hjB, hjV0, hjV1⟩
    rw [hjD] at hMemT hMemF
    exact ⟨Finset.card_pos.mpr ⟨(.gate j, true),
        Finset.mem_inter.mpr ⟨hMemT, Finset.mem_image.mpr ⟨j, hjDualOB, rfl⟩⟩⟩,
      Finset.card_pos.mpr ⟨(.gate j, false),
        Finset.mem_inter.mpr ⟨hMemF, Finset.mem_image.mpr ⟨j, hjDualOB, rfl⟩⟩⟩⟩
  have hSumT := sum_card_inter_req_le_bool p root true V ST hST_bool
  have hSumF := sum_card_inter_req_le_bool p root false V SF hSF_bool
  have hV_leT : V.card ≤ ∑ k ∈ V, (req p root k ∩ ST).card := by
    calc
      V.card = ∑ _k ∈ V, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => (hMemBoth k hk).1
  have hV_leF : V.card ≤ ∑ k ∈ V, (req p root k ∩ SF).card := by
    calc
      V.card = ∑ _k ∈ V, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => (hMemBoth k hk).2
  have hShAdd := sharedBool_add p root
  have hDualOB := card_dualOtherBad_le_tight p root h0 h1
  dsimp only [V] at hV_leT hV_leF hSumT hSumF
  omega

theorem card_stopGate_add_badNot_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (StopGate p root).card + (badNot p root).card ≤
      11 * (badGates p root).card + 7 * shared p root := by
  classical
  let gateTargets := Finset.univ.filter fun k : Fin g =>
    (.gate k : Wire n g) ∈ badGatesTargets p root
  have hInj : Function.Injective (fun k : Fin g => (.gate k : Wire n g)) :=
    fun _ _ h => by cases h; rfl
  have hSub : gateTargets.image (fun k : Fin g => (.gate k : Wire n g)) ⊆ badGatesTargets p root := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hk).2
  have hGT : gateTargets.card ≤ (badGatesTargets p root).card := by
    rw [← Finset.card_image_of_injective gateTargets hInj]
    exact Finset.card_le_card hSub
  have hU : (StopGate p root).card ≤ (CutGate p root).card + gateTargets.card :=
    Finset.card_union_le ..
  have hCG : (CutGate p root).card ≤ (otherBad p root).card +
      (Finset.univ.filter (HasRepeat p root)).card := Finset.card_union_le ..
  have hOther := card_otherBad_le_tight p root h0 h1
  have hRepeat := card_hasRepeat_le p root
  have hBT := card_badGatesTargets_add_badNot_le p root
  omega

theorem card_cutNode_add_badNot_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    2 * (Finset.univ.filter (CutNode p root)).card + 2 * (badNot p root).card ≤
      26 * (badGates p root).card + 19 * shared p root := by
  classical
  have hSub : Finset.univ.filter (CutNode p root) ⊆
      StopGate p root ∪ Finset.univ.filter (EnteredByOtherBad p root) := by
    intro k hk
    rcases (Finset.mem_filter.mp hk).2 with hS | hE
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩)
  have hU := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  have hSG := card_stopGate_add_badNot_le_tight p root h0 h1
  have hEB := card_enteredByOtherBad_le_tight p root h0 h1
  omega

/-- A cut endpoint carrying both corner values is a dual anomaly, a repeat
reader, a target of a bad gate, or a good dual reader of an anomaly. -/
theorem card_dualCutNodes_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    2 * (dualCutNodes p root).card ≤
      12 * (badGates p root).card + 13 * shared p root := by
  let repeatedReaders := Finset.univ.filter (HasRepeat p root)
  let targets := Finset.univ.filter fun k : Fin g => (.gate k : Wire n g) ∈ badGatesTargets p root
  let entered := Finset.univ.filter (EnteredByOtherBad p root)
  have hSub : dualCutNodes p root ⊆ dualOtherBad p root ∪ repeatedReaders ∪ targets ∪ entered := by
    intro k hk
    obtain ⟨hf,ht⟩ := Finset.mem_inter.mp hk
    obtain ⟨hc,hf⟩ := (Finset.mem_filter.mp hf).2
    have ht := (Finset.mem_filter.mp ht).2.2
    rcases hc with hStop | hE
    · rcases Finset.mem_union.mp hStop with hCut | hT
      · rcases Finset.mem_union.mp hCut with hOther | hR
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨hOther,hf,ht⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hR))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hT)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE⟩)
  have hTargets : targets.card ≤ (badGatesTargets p root).card := by
    rw [← Finset.card_image_of_injective targets (f := (Wire.gate : Fin g → Wire n g))
      (fun _ _ h => Wire.gate.inj h)]
    exact Finset.card_le_card (by
      rintro _ hw
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hk).2)
  have hBound : (dualCutNodes p root).card ≤
      (dualOtherBad p root).card + repeatedReaders.card + targets.card + entered.card := by
    calc
      _ ≤ (dualOtherBad p root ∪ repeatedReaders ∪ targets ∪ entered).card := Finset.card_le_card hSub
      _ ≤ _ := by
        have h1' := Finset.card_union_le (dualOtherBad p root ∪ repeatedReaders ∪ targets) entered
        have h2' := Finset.card_union_le (dualOtherBad p root ∪ repeatedReaders) targets
        have h3' := Finset.card_union_le (dualOtherBad p root) repeatedReaders
        omega
  have hDual := card_dualOtherBad_le_tight p root h0 h1
  have hRepeat : repeatedReaders.card ≤ 2 * shared p root := card_hasRepeat_le p root
  have hBadTargets := card_badGatesTargets_le p root
  have hEntered : 2 * entered.card ≤ 4 * (badGates p root).card + 5 * shared p root :=
    card_enteredByOtherBad_le_tight p root h0 h1
  omega

theorem card_cutInputs_le_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (cutInputs p root).card ≤ 117 * slack p root := by
  classical
  let repIn : Finset (Fin n) := (repeatStates p root).biUnion fun s =>
    match s.1 with | .input i => {i} | .gate _ => ∅
  let stopIn : Finset (Fin n) := (StopGate p root).biUnion fun k =>
    (Finset.univ.biUnion fun a =>
      match (p.lines k).wires a with | .input i => {i} | .gate _ => ∅)
  have hSub : cutInputs p root ⊆ repIn ∪ stopIn := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with hF | hT | ⟨k, hk, a, ha⟩
    · exact Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨((.input i : Wire n g), false), hF, by simp⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨((.input i : Wire n g), true), hT, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k, hk, Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, by simp [ha]⟩⟩)
  have hRep : repIn.card ≤ (repeatStates p root).card := by
    calc
      repIn.card ≤ ∑ s ∈ repeatStates p root,
          (match s.1 with | .input i => ({i} : Finset (Fin n)) | .gate _ => ∅).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ repeatStates p root, 1 := by
        refine Finset.sum_le_sum fun s _ => ?_
        cases s.1 <;> simp
      _ = (repeatStates p root).card := by simp
  have hStop : stopIn.card ≤ 2 * (StopGate p root).card := by
    have hK (k : Fin g) : (Finset.univ.biUnion fun a =>
        match (p.lines k).wires a with | .input i => ({i} : Finset (Fin n)) | .gate _ => ∅).card ≤ 2 := by
      calc
        _ ≤ ∑ _a : Fin (signature.Arity (p.lines k).op), 1 := by
          refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun a _ => ?_)
          cases (p.lines k).wires a <;> simp
        _ ≤ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
          cases (p.lines k).op <;> simp
    calc
      stopIn.card ≤ ∑ k ∈ StopGate p root, _ := Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ StopGate p root, 2 := Finset.sum_le_sum fun k _ => hK k
      _ = 2 * (StopGate p root).card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
  have hU := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  have hRS := card_repeatStates_le_shared p root
  have hSh : shared p root ≤ slack p root := by unfold slack; omega
  have hSG := card_stopGate_le_slack p root h0 h1
  omega

theorem stopGate_not_otherBad {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ StopGate p root) : k ∉ otherBad p root :=
  fun h => hk (Finset.mem_union_left _ (Finset.mem_union_left _ h))

theorem stopGate_not_hasRepeat {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ StopGate p root) : ¬ HasRepeat p root k :=
  fun h => hk (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))

theorem cutGate_not_otherBad {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ CutGate p root) : k ∉ otherBad p root :=
  fun h => hk (Finset.mem_union_left _ h)

theorem cutGate_not_hasRepeat {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ CutGate p root) : ¬ HasRepeat p root k :=
  fun h => hk (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))

theorem cutGate_subset_stopGate (p : Program signature n g) (root : Wire n g) :
    CutGate p root ⊆ StopGate p root := Finset.subset_union_left

theorem not_badFlip_of_not_cutGate {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ CutGate p root) : k ∉ badFlip p root :=
  not_badFlip_of_not_otherBad (cutGate_not_otherBad hk)

theorem not_badGates_of_not_cutGate {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ CutGate p root) : k ∉ badGates p root :=
  (not_s0_s1_of_not_badFlip (not_badFlip_of_not_cutGate hk)).1

theorem not_mem_badGatesTargets_of_not_stopGate {p : Program signature n g} {root : Wire n g}
    {k : Fin g} (hk : k ∉ StopGate p root) : (.gate k : Wire n g) ∉ badGatesTargets p root := by
  classical
  intro hMem
  exact hk (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMem⟩))

theorem not_cutGate_of_not_cutNode {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : ¬ CutNode p root k) : k ∉ CutGate p root :=
  fun h => hk (Or.inl (cutGate_subset_stopGate p root h))

theorem not_stopGate_of_not_cutNode {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : ¬ CutNode p root k) : k ∉ StopGate p root :=
  fun h => hk (Or.inl h)

theorem req_unique_parent {p : Program signature n g} {root : Wire n g}
    {k1 k2 : Fin g} (h1 : ¬ HasRepeat p root k1) {key : Wire n g × Bool}
    (hm1 : key ∈ req p root k1) (hm2 : key ∈ req p root k2) : k1 = k2 := by
  by_contra hne
  exact h1 ⟨key, hm1, mem_repeatStates_of_ne hne hm1 hm2⟩

/-! ### Monochromatic dual segments: `segEdge`, `SegAnc`, `segTopOR`, `segTopAND` -/

/-- Clean monochromatic `dualChild` step inside `goodDual` avoiding `CutNode`. -/
def segEdge (p : Program signature n g) (root : Wire n g) (k j : Fin g) : Prop :=
  k ∈ goodDual p root ∧ j ∈ goodDual p root ∧
  ¬ CutNode p root k ∧ ¬ CutNode p root j ∧
  (p.lines k).op = (p.lines j).op ∧ dualChild p k = .gate j

/-- Reflexive-transitive closure of `segEdge`. -/
def SegAnc (p : Program signature n g) (root : Wire n g) (t k : Fin g) : Prop :=
  Relation.ReflTransGen (segEdge p root) t k

/-- Top gates of clean monochromatic `DualOR` segments. -/
noncomputable def segTopOR (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in
  (goodDual p root).filter fun k =>
    (p.lines k).op = .or ∧ ¬ CutNode p root k ∧ ¬ ∃ u, segEdge p root u k

/-- Top gates of clean monochromatic `DualAND` segments. -/
noncomputable def segTopAND (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in
  (goodDual p root).filter fun k =>
    (p.lines k).op = .and ∧ ¬ CutNode p root k ∧ ¬ ∃ u, segEdge p root u k

theorem segEdge_lt {p : Program signature n g} {root : Wire n g} {k j : Fin g}
    (h : segEdge p root k j) : j.val < k.val := by
  have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp h.1).2)).1
  have hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or := (not_bad_structure p root hnb).1
  have hPre := dualChild_precedes (p := p) (k := k) hOp
  rw [h.2.2.2.2.2] at hPre
  exact Nat.succ_lt_succ_iff.mp hPre

theorem dualAND_reqCorner_sideChild {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hnb : k ∉ badGates p root) (hDA : IsDualAND p root k) :
    (sideChild p k, true) ∈ reqCorner p root true k := by
  have hC := dualAND_children h0 h1 hnb hDA
  rcases Finset.mem_union.mp hC.2.2.2.2.1 with hF | hT
  · rw [hC.2.1, Finset.mem_singleton] at hF
    exact False.elim (by cases congrArg Prod.snd hF)
  · exact hT

theorem dualOR_reqCorner_sideChild {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hnb : k ∉ badGates p root) (hDO : IsDualOR p root k) :
    (sideChild p k, false) ∈ reqCorner p root false k := by
  have hC := dualOR_children h0 h1 hnb hDO
  rcases Finset.mem_union.mp hC.2.2.2.2.1 with hF | hT
  · exact hF
  · rw [hC.2.1, Finset.mem_singleton] at hT
    exact False.elim (by cases congrArg Prod.snd hT)

theorem segEdge_req_dualChild {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∈ goodDual p root) :
    (dualChild p k, false) ∈ reqCorner p root false k ∧
      (dualChild p k, true) ∈ reqCorner p root true k := by
  have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hk).2)).1
  rcases (goodDual_iff.mp hk).1 with hDA | hDO
  · have hC := dualAND_children h0 h1 hnb hDA
    have hM0 : (dualChild p k, false) ∈ reqCorner p root false k := by
      rw [hC.2.1]; exact Finset.mem_singleton_self _
    have hM1 : (dualChild p k, true) ∈ reqCorner p root true k := by
      rcases Finset.mem_union.mp hC.2.2.2.1 with hF | hT
      · rw [hC.2.1, Finset.mem_singleton] at hF
        exact False.elim (by cases congrArg Prod.snd hF)
      · exact hT
    exact ⟨hM0, hM1⟩
  · have hC := dualOR_children h0 h1 hnb hDO
    have hM1 : (dualChild p k, true) ∈ reqCorner p root true k := by
      rw [hC.2.1]; exact Finset.mem_singleton_self _
    have hM0 : (dualChild p k, false) ∈ reqCorner p root false k := by
      rcases Finset.mem_union.mp hC.2.2.2.1 with hF | hT
      · exact hF
      · rw [hC.2.1, Finset.mem_singleton] at hT
        exact False.elim (by cases congrArg Prod.snd hT)
    exact ⟨hM0, hM1⟩

theorem segEdge_unique_parent {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k1 k2 j : Fin g} (h1E : segEdge p root k1 j) (h2E : segEdge p root k2 j) : k1 = k2 := by
  have hMem1 : ((.gate j : Wire n g), true) ∈ req p root k1 :=
    Finset.mem_union_right _ (h1E.2.2.2.2.2 ▸ (segEdge_req_dualChild h0 h1 h1E.1).2)
  have hMem2 : ((.gate j : Wire n g), true) ∈ req p root k2 :=
    Finset.mem_union_right _ (h2E.2.2.2.2.2 ▸ (segEdge_req_dualChild h0 h1 h2E.1).2)
  exact req_unique_parent (stopGate_not_hasRepeat (not_stopGate_of_not_cutNode h1E.2.2.1)) hMem1 hMem2

theorem segAnc_lt_or_eq {p : Program signature n g} {root : Wire n g} {t k : Fin g}
    (h : SegAnc p root t k) : k.val ≤ t.val := by
  induction h with
  | refl => exact le_rfl
  | tail _ hEdge ih => exact (segEdge_lt hEdge).le.trans ih

theorem segAnc_goodDual {p : Program signature n g} {root : Wire n g} {t k : Fin g}
    (hT : t ∈ goodDual p root ∧ ¬ CutNode p root t) (h : SegAnc p root t k) :
    k ∈ goodDual p root ∧ ¬ CutNode p root k ∧ (p.lines t).op = (p.lines k).op := by
  induction h with
  | refl => exact ⟨hT.1, hT.2, rfl⟩
  | tail _ hEdge ih => exact ⟨hEdge.2.1, hEdge.2.2.2.1, ih.2.2.trans hEdge.2.2.2.2.1⟩

private theorem exists_segTop_anc_aux (p : Program signature n g) (root : Wire n g) :
    ∀ d : ℕ, ∀ k : Fin g, g - k.val ≤ d → k ∈ goodDual p root → ¬ CutNode p root k →
      ∃ t : Fin g, (t ∈ segTopOR p root ∨ t ∈ segTopAND p root) ∧ SegAnc p root t k := by
  intro d
  induction d with
  | zero =>
    intro k hk _ _
    have : k.val < g := k.isLt
    omega
  | succ d ih =>
    intro k hk hkG hkC
    classical
    by_cases hParent : ∃ u, segEdge p root u k
    · obtain ⟨u, hu⟩ := hParent
      have hLt := segEdge_lt hu
      have huDist : g - u.val ≤ d := by
        have hltg : u.val < g := u.isLt
        omega
      obtain ⟨t, htMem, htAnc⟩ := ih u huDist hu.1 hu.2.2.1
      exact ⟨t, htMem, Relation.ReflTransGen.tail htAnc hu⟩
    · refine ⟨k, ?_, Relation.ReflTransGen.refl⟩
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG).2)).1
      rcases (not_bad_structure p root hnb).1 with hOp | hOp
      · exact Or.inr (Finset.mem_filter.mpr ⟨hkG, hOp, hkC, hParent⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨hkG, hOp, hkC, hParent⟩)

theorem exists_segTop_anc {p : Program signature n g} {root : Wire n g}
    {k : Fin g} (hkG : k ∈ goodDual p root) (hkC : ¬ CutNode p root k) :
    ∃ t : Fin g, (t ∈ segTopOR p root ∨ t ∈ segTopAND p root) ∧ SegAnc p root t k :=
  exists_segTop_anc_aux p root (g - k.val) k le_rfl hkG hkC

theorem segTop_anc_unique {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {t1 t2 k : Fin g}
    (ht1 : t1 ∈ segTopOR p root ∨ t1 ∈ segTopAND p root)
    (ht2 : t2 ∈ segTopOR p root ∨ t2 ∈ segTopAND p root)
    (h1A : SegAnc p root t1 k) (h2A : SegAnc p root t2 k) : t1 = t2 := by
  classical
  have hNoPar : ∀ t, t ∈ segTopOR p root ∨ t ∈ segTopAND p root → ¬ ∃ u, segEdge p root u t := by
    intro t ht
    rcases ht with hO | hA
    · exact (Finset.mem_filter.mp hO).2.2.2
    · exact (Finset.mem_filter.mp hA).2.2.2
  have h : ∀ a k, SegAnc p root a k → ∀ b, SegAnc p root b k →
      (¬ ∃ u, segEdge p root u a) → (¬ ∃ u, segEdge p root u b) → a = b := by
    intro a k ha
    induction ha with
    | refl =>
      intro b hb hna _
      rcases Relation.ReflTransGen.cases_tail hb with rfl | ⟨c, _, hc⟩
      · rfl
      · exact (hna ⟨c, hc⟩).elim
    | @tail u v _ huv ih =>
      intro b hb hna hnb
      rcases Relation.ReflTransGen.cases_tail hb with rfl | ⟨u2, hu2b, hu2v⟩
      · exact (hnb ⟨u, huv⟩).elim
      · have hEq : u = u2 := segEdge_unique_parent h0 h1 huv hu2v
        subst hEq
        exact ih b hu2b hna hnb
  exact h t1 k h1A t2 h2A (hNoPar t1 ht1) (hNoPar t2 ht2)

theorem segTopOR_goodDual {p : Program signature n g} {root : Wire n g} {t : Fin g}
    (ht : t ∈ segTopOR p root) :
    t ∈ goodDual p root ∧ IsDualOR p root t ∧ ¬ CutNode p root t ∧ ¬ ∃ u, segEdge p root u t := by
  classical
  obtain ⟨htG, hOp, hC, hN⟩ := Finset.mem_filter.mp ht
  have hD : IsDualOR p root t := by
    rcases (goodDual_iff.mp htG).1 with hA | hO
    · exfalso; rw [hA.1] at hOp; cases hOp
    · exact hO
  exact ⟨htG, hD, hC, hN⟩

theorem segTopAND_goodDual {p : Program signature n g} {root : Wire n g} {t : Fin g}
    (ht : t ∈ segTopAND p root) :
    t ∈ goodDual p root ∧ IsDualAND p root t ∧ ¬ CutNode p root t ∧ ¬ ∃ u, segEdge p root u t := by
  classical
  obtain ⟨htG, hOp, hC, hN⟩ := Finset.mem_filter.mp ht
  have hD : IsDualAND p root t := by
    rcases (goodDual_iff.mp htG).1 with hA | hO
    · exact hA
    · exfalso; rw [hO.1] at hOp; cases hOp
  exact ⟨htG, hD, hC, hN⟩

/-! ### Corner-bypassing demand predicates `AltNeed1` and `AltNeed0` -/

/-- Alternate `1`-corner demand replacing `DualOR` children in `S` with `sideChild`. -/
inductive AltNeed1 (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Wire n g → Prop where
  | output : AltNeed1 p root S root
  | branchS {k : Fin g} (hk : AltNeed1 p root S (.gate k)) (hkS : k ∈ S) :
      AltNeed1 p root S (sideChild p k)
  | branchRest {k : Fin g} (hk : AltNeed1 p root S (.gate k)) (hkS : k ∉ S)
      {a : Fin (signature.Arity (p.lines k).op)}
      (ha : a ∈ selectedPins (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s))) :
      AltNeed1 p root S ((p.lines k).wires a)

/-- Alternate `0`-corner demand replacing `DualAND` children in `S` with `sideChild`. -/
inductive AltNeed0 (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Wire n g → Prop where
  | output : AltNeed0 p root S root
  | branchS {k : Fin g} (hk : AltNeed0 p root S (.gate k)) (hkS : k ∈ S) :
      AltNeed0 p root S (sideChild p k)
  | branchRest {k : Fin g} (hk : AltNeed0 p root S (.gate k)) (hkS : k ∉ S)
      {a : Fin (signature.Arity (p.lines k).op)}
      (ha : a ∈ selectedPins (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s))) :
      AltNeed0 p root S ((p.lines k).wires a)

noncomputable def altNeed1_inputs (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Finset (Fin n) := open scoped Classical in
  Finset.univ.filter fun i => AltNeed1 p root S (.input i)

noncomputable def altNeed0_inputs (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Finset (Fin n) := open scoped Classical in
  Finset.univ.filter fun i => AltNeed0 p root S (.input i)

theorem altNeed1_sound (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (S : Finset (Fin g)) (hS : ∀ k ∈ S, k ∈ goodDual p root ∧ (p.lines k).op = .or)
    (y : BitString n) (hAgree : ∀ i ∈ altNeed1_inputs p root S, y i = true) :
    p.trace interpretation y root = true := by
  classical
  have hTrace : ∀ w, AltNeed1 p root S w → p.trace interpretation y w = cornerValue p true w := by
    intro w
    refine p.wire_induction (P := fun w => AltNeed1 p root S w →
      p.trace interpretation y w = cornerValue p true w) ?_ ?_ w
    · intro i hi
      rw [cornerValue_input]
      exact hAgree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro k ih hk
      by_cases hkS : k ∈ S
      · obtain ⟨hkG, hOp⟩ := hS k hkS
        have hDOR : IsDualOR p root k := by
          rcases (goodDual_iff.mp hkG).1 with hA | hO
          · exfalso; rw [hA.1] at hOp; cases hOp
          · exact hO
        have hSideT : cornerValue p true (sideChild p k) = true :=
          ((goodDual_sideChild_val h0 h1 hkG).1 hDOR).2
        have hGateT : cornerValue p true (.gate k) = true :=
          (needCorner_eq_cornerValue h1 hDOR.2.2).symm
        obtain ⟨a, ha⟩ := sideChild_is_wire (p := p) (k := k) (Or.inr hOp)
        have hChildAlt : AltNeed1 p root S ((p.lines k).wires a) := by
          rw [ha]; exact AltNeed1.branchS hk hkS
        have hChildVal : p.trace interpretation y ((p.lines k).wires a) = true := by
          rw [ih a hChildAlt, ha, hSideT]
        rw [p.trace_gate, hGateT]
        exact op_or_eq_true (p.lines k).op hOp (p.lines k).wires _ hChildVal
      · rw [p.trace_gate, cornerValue_gate]
        apply agrees_of_selectedPins
        intro a ha
        exact ih a (AltNeed1.branchRest hk hkS ha)
  exact (hTrace root AltNeed1.output).trans h1

theorem altNeed0_sound (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (S : Finset (Fin g)) (hS : ∀ k ∈ S, k ∈ goodDual p root ∧ (p.lines k).op = .and)
    (y : BitString n) (hAgree : ∀ i ∈ altNeed0_inputs p root S, y i = false) :
    p.trace interpretation y root = true := by
  classical
  have hTrace : ∀ w, AltNeed0 p root S w → p.trace interpretation y w = cornerValue p false w := by
    intro w
    refine p.wire_induction (P := fun w => AltNeed0 p root S w →
      p.trace interpretation y w = cornerValue p false w) ?_ ?_ w
    · intro i hi
      rw [cornerValue_input]
      exact hAgree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro k ih hk
      by_cases hkS : k ∈ S
      · obtain ⟨hkG, hOp⟩ := hS k hkS
        have hDAND : IsDualAND p root k := by
          rcases (goodDual_iff.mp hkG).1 with hA | hO
          · exact hA
          · exfalso; rw [hO.1] at hOp; cases hOp
        have hSideF : cornerValue p false (sideChild p k) = false :=
          ((goodDual_sideChild_val h0 h1 hkG).2 hDAND).1
        have hGateF : cornerValue p false (.gate k) = false :=
          (needCorner_eq_cornerValue h0 hDAND.2.1).symm
        obtain ⟨a, ha⟩ := sideChild_is_wire (p := p) (k := k) (Or.inl hOp)
        have hChildAlt : AltNeed0 p root S ((p.lines k).wires a) := by
          rw [ha]; exact AltNeed0.branchS hk hkS
        have hChildVal : p.trace interpretation y ((p.lines k).wires a) = false := by
          rw [ih a hChildAlt, ha, hSideF]
        rw [p.trace_gate, hGateF]
        exact op_and_eq_false (p.lines k).op hOp (p.lines k).wires _ hChildVal
      · rw [p.trace_gate, cornerValue_gate]
        apply agrees_of_selectedPins
        intro a ha
        exact ih a (AltNeed0.branchRest hk hkS ha)
  exact (hTrace root AltNeed0.output).trans h0

/-- Outside-`NeedCorner 1` gates visited by `AltNeed1`. -/
noncomputable def H1 (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Finset (Fin g) := open scoped Classical in
  Finset.univ.filter fun k =>
    AltNeed1 p root S (.gate k) ∧ ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k))

/-- Outside-`NeedCorner 0` gates visited by `AltNeed0`. -/
noncomputable def H0 (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Finset (Fin g) := open scoped Classical in
  Finset.univ.filter fun k =>
    AltNeed0 p root S (.gate k) ∧ ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k))

/-- Frontier wires where `AltNeed1` re-enters `NeedCorner 1` from `S` or `H1`. -/
noncomputable def Boundary1 (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Finset (Wire n g) := open scoped Classical in
  Finset.univ.filter fun w =>
    NeedCorner p root true (w, cornerValue p true w) ∧
      ((∃ t ∈ S, AltNeed1 p root S (.gate t) ∧ sideChild p t = w) ∨
       ∃ k ∈ H1 p root S, k ∉ S ∧
         ∃ a ∈ selectedPins (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s)),
           (p.lines k).wires a = w)

/-- Frontier wires where `AltNeed0` re-enters `NeedCorner 0` from `S` or `H0`. -/
noncomputable def Boundary0 (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Finset (Wire n g) := open scoped Classical in
  Finset.univ.filter fun w =>
    NeedCorner p root false (w, cornerValue p false w) ∧
      ((∃ t ∈ S, AltNeed0 p root S (.gate t) ∧ sideChild p t = w) ∨
       ∃ k ∈ H0 p root S, k ∉ S ∧
         ∃ a ∈ selectedPins (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s)),
           (p.lines k).wires a = w)

private theorem h1_branch_in_badFlip_or_Z1 {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {S : Finset (Fin g)} {k : Fin g} (hk : k ∈ H1 p root S)
    (hDeg : ¬ (¬ ((p.lines k).op = .and ∧ cornerValue p true (.gate k) = true) ∧
      ¬ ((p.lines k).op = .or ∧ cornerValue p true (.gate k) = false))) :
    k ∈ badFlip p root ∪ Z1 p root := by
  classical
  have hNotN1 : ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k)) :=
    (Finset.mem_filter.mp hk).2.2
  by_cases hbf : k ∈ badFlip p root
  · exact Finset.mem_union_left _ hbf
  · apply Finset.mem_union_right
    rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
    · exact (hNotN1 ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)).elim
    · exact (hNotN1 ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)).elim
    · exact (hNotN1 ((needCorner_eq_cornerValue h1 hPA.2.2).symm ▸ hPA.2.2)).elim
    · have hV : cornerValue p true (.gate k) = false := by
        by_contra hNotF
        have hT : cornerValue p true (.gate k) = true := Bool.eq_true_of_not_eq_false hNotF
        apply hDeg
        refine ⟨?_, ?_⟩
        · intro hC; rw [hPO.1] at hC; cases hC.1
        · intro hC; rw [hT] at hC; cases hC.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPO.2.1, hV⟩

private theorem h0_branch_in_badFlip_or_Z0 {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {S : Finset (Fin g)} {k : Fin g} (hk : k ∈ H0 p root S)
    (hDeg : ¬ (¬ ((p.lines k).op = .and ∧ cornerValue p false (.gate k) = true) ∧
      ¬ ((p.lines k).op = .or ∧ cornerValue p false (.gate k) = false))) :
    k ∈ badFlip p root ∪ Z0 p root := by
  classical
  have hNotN0 : ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k)) :=
    (Finset.mem_filter.mp hk).2.2
  by_cases hbf : k ∈ badFlip p root
  · exact Finset.mem_union_left _ hbf
  · apply Finset.mem_union_right
    rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
    · exact (hNotN0 ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)).elim
    · exact (hNotN0 ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)).elim
    · have hV : cornerValue p false (.gate k) = true := by
        by_contra hNotT
        have hF : cornerValue p false (.gate k) = false := Bool.eq_false_iff.mpr hNotT
        apply hDeg
        refine ⟨?_, ?_⟩
        · intro hC; rw [hF] at hC; cases hC.2
        · intro hC; rw [hPA.1] at hC; cases hC.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPA.2.2, hV⟩
    · exact (hNotN0 ((needCorner_eq_cornerValue h0 hPO.2.1).symm ▸ hPO.2.1)).elim

theorem altNeed1_leaf_and_boundary_card (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (S : Finset (Fin g)) :
    (altNeed1_inputs p root S \ needInputs p root true).card + (Boundary1 p root S).card ≤
      (S.filter fun t => AltNeed1 p root S (.gate t)).card +
        (H1 p root S ∩ (badFlip p root ∪ Z1 p root)).card := by
  classical
  let sHit := S.filter fun t => AltNeed1 p root S (.gate t)
  let leafExtra := altNeed1_inputs p root S \ needInputs p root true
  let outS : Finset (Wire n g) := sHit.image (sideChild p)
  let outH (k : Fin g) : Finset (Wire n g) :=
    if k ∈ S then {sideChild p k}
    else (selectedPins (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s))).image
      (p.lines k).wires
  let target : Finset (Wire n g) :=
    (H1 p root S).image Wire.gate ∪ Boundary1 p root S ∪ leafExtra.image Wire.input
  have hSub : target ⊆ outS ∪ (H1 p root S).biUnion outH := by
    intro w hw
    have hEntry : ∀ u : Wire n g, AltNeed1 p root S u →
        ¬ NeedCorner p root true (u, cornerValue p true u) → u ∈ outS ∪ (H1 p root S).biUnion outH := by
      intro u hu hnu
      cases hu with
      | output => exact (hnu (h1.symm ▸ NeedCorner.output)).elim
      | @branchS t ht htS =>
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htS, ht⟩, rfl⟩)
      | @branchRest k hk hkS a ha =>
        have hkNotNeed1 : ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := by
          intro hkN1
          exact hnu (needCorner_child_of_reqCorner (corner_arg_mem_reqCorner hkN1 ha))
        have hkH1 : k ∈ H1 p root S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hkNotNeed1⟩
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨k, hkH1, by simp [outH, hkS]; exact ⟨a, ha, rfl⟩⟩)
    rcases Finset.mem_union.mp hw with hL | hLeaf
    · rcases Finset.mem_union.mp hL with hGate | hBnd
      · obtain ⟨k, hkH1, rfl⟩ := Finset.mem_image.mp hGate
        obtain ⟨_, hkAlt, hkNN1⟩ := Finset.mem_filter.mp hkH1
        exact hEntry (.gate k) hkAlt hkNN1
      · obtain ⟨hN1, hDisj⟩ := (Finset.mem_filter.mp hBnd).2
        rcases hDisj with ⟨t, htS, htAlt, rfl⟩ | ⟨k, hkH1, hkNS, a, ha, rfl⟩
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htS, htAlt⟩, rfl⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨k, hkH1, by simp [outH, hkNS]; exact ⟨a, ha, rfl⟩⟩)
    · obtain ⟨i, hiEx, rfl⟩ := Finset.mem_image.mp hLeaf
      obtain ⟨hiAlt, hiNN⟩ := Finset.mem_sdiff.mp hiEx
      have hiA : AltNeed1 p root S (.input i) := (Finset.mem_filter.mp hiAlt).2
      have hiN1 : ¬ NeedCorner p root true (.input i, true) :=
        fun hN => hiNN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN⟩)
      exact hEntry (.input i) hiA hiN1
  have hDisj1 : Disjoint ((H1 p root S).image Wire.gate) (Boundary1 p root S) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw1
    exact (Finset.mem_filter.mp hk).2.2 (Finset.mem_filter.mp hw2).2.1
  have hDisj2 : Disjoint ((H1 p root S).image Wire.gate ∪ Boundary1 p root S)
      (leafExtra.image Wire.input) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨i, hiEx, rfl⟩ := Finset.mem_image.mp hw2
    rcases Finset.mem_union.mp hw1 with hG | hB
    · obtain ⟨k, _, hEq⟩ := Finset.mem_image.mp hG; cases hEq
    · have hN1 := (Finset.mem_filter.mp hB).2.1
      rw [cornerValue_input] at hN1
      exact (Finset.mem_sdiff.mp hiEx).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN1⟩)
  have hTargetCard : target.card = (H1 p root S).card + (Boundary1 p root S).card + leafExtra.card := by
    dsimp only [target]
    rw [Finset.card_union_of_disjoint hDisj2, Finset.card_union_of_disjoint hDisj1,
      Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)]
  have hOutHCard (k : Fin g) (hk : k ∈ H1 p root S) :
      (outH k).card ≤ 1 + if k ∈ badFlip p root ∪ Z1 p root then 1 else 0 := by
    dsimp only [outH]
    by_cases hkS : k ∈ S
    · simp [hkS]
    · simp only [hkS, ite_false]
      have hImgLe : ((selectedPins (p.lines k).op _).image (p.lines k).wires).card ≤
          (selectedPins (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s))).card :=
        Finset.card_image_le
      by_cases hDeg : ¬ ((p.lines k).op = .and ∧ cornerValue p true (.gate k) = true) ∧
          ¬ ((p.lines k).op = .or ∧ cornerValue p true (.gate k) = false)
      · have hDeg' : ¬ ((p.lines k).op = .and ∧
              interpretation (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s)) = true) ∧
            ¬ ((p.lines k).op = .or ∧
              interpretation (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s)) = false) := by
          simpa [← cornerValue_gate] using hDeg
        have hLe1 := op_selectedPins_card_le_one (p.lines k).op _ hDeg'
        exact hImgLe.trans (hLe1.trans (Nat.le_add_right 1 _))
      · have hkBZ := h1_branch_in_badFlip_or_Z1 h0 h1 hk hDeg
        have hLe2 := op_selectedPins_card_le (p.lines k).op
          (fun s => cornerValue p true ((p.lines k).wires s))
        split_ifs
        exact hImgLe.trans hLe2
  have hRhsCard : (outS ∪ (H1 p root S).biUnion outH).card ≤
      sHit.card + (H1 p root S).card + (H1 p root S ∩ (badFlip p root ∪ Z1 p root)).card := by
    have hU := Finset.card_union_le outS ((H1 p root S).biUnion outH)
    have hS1 : outS.card ≤ sHit.card := Finset.card_image_le
    have hB1 : ((H1 p root S).biUnion outH).card ≤ ∑ k ∈ H1 p root S, (outH k).card :=
      Finset.card_biUnion_le
    have hSum : ∑ k ∈ H1 p root S, (outH k).card ≤
        (H1 p root S).card + (H1 p root S ∩ (badFlip p root ∪ Z1 p root)).card := by
      calc
        ∑ k ∈ H1 p root S, (outH k).card ≤
            ∑ k ∈ H1 p root S, (1 + if k ∈ badFlip p root ∪ Z1 p root then 1 else 0) :=
          Finset.sum_le_sum hOutHCard
        _ = (∑ _k ∈ H1 p root S, 1) +
            ∑ k ∈ H1 p root S, (if k ∈ badFlip p root ∪ Z1 p root then 1 else 0) :=
          Finset.sum_add_distrib
        _ = (H1 p root S).card + (H1 p root S ∩ (badFlip p root ∪ Z1 p root)).card := by
          congr 1
          · simp
          · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
              Finset.filter_mem_eq_inter]
    omega
  have hLe := (Finset.card_le_card hSub).trans hRhsCard
  rw [hTargetCard] at hLe
  dsimp only [sHit, leafExtra] at hLe
  omega

theorem altNeed0_leaf_and_boundary_card (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (S : Finset (Fin g)) :
    (altNeed0_inputs p root S \ needInputs p root false).card + (Boundary0 p root S).card ≤
      (S.filter fun t => AltNeed0 p root S (.gate t)).card +
        (H0 p root S ∩ (badFlip p root ∪ Z0 p root)).card := by
  classical
  let sHit := S.filter fun t => AltNeed0 p root S (.gate t)
  let leafExtra := altNeed0_inputs p root S \ needInputs p root false
  let outS : Finset (Wire n g) := sHit.image (sideChild p)
  let outH (k : Fin g) : Finset (Wire n g) :=
    if k ∈ S then {sideChild p k}
    else (selectedPins (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s))).image
      (p.lines k).wires
  let target : Finset (Wire n g) :=
    (H0 p root S).image Wire.gate ∪ Boundary0 p root S ∪ leafExtra.image Wire.input
  have hSub : target ⊆ outS ∪ (H0 p root S).biUnion outH := by
    intro w hw
    have hEntry : ∀ u : Wire n g, AltNeed0 p root S u →
        ¬ NeedCorner p root false (u, cornerValue p false u) → u ∈ outS ∪ (H0 p root S).biUnion outH := by
      intro u hu hnu
      cases hu with
      | output => exact (hnu (h0.symm ▸ NeedCorner.output)).elim
      | @branchS t ht htS =>
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htS, ht⟩, rfl⟩)
      | @branchRest k hk hkS a ha =>
        have hkNotNeed0 : ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := by
          intro hkN0
          exact hnu (needCorner_child_of_reqCorner (corner_arg_mem_reqCorner hkN0 ha))
        have hkH0 : k ∈ H0 p root S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hkNotNeed0⟩
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨k, hkH0, by simp [outH, hkS]; exact ⟨a, ha, rfl⟩⟩)
    rcases Finset.mem_union.mp hw with hL | hLeaf
    · rcases Finset.mem_union.mp hL with hGate | hBnd
      · obtain ⟨k, hkH0, rfl⟩ := Finset.mem_image.mp hGate
        obtain ⟨_, hkAlt, hkNN0⟩ := Finset.mem_filter.mp hkH0
        exact hEntry (.gate k) hkAlt hkNN0
      · obtain ⟨hN0, hDisj⟩ := (Finset.mem_filter.mp hBnd).2
        rcases hDisj with ⟨t, htS, htAlt, rfl⟩ | ⟨k, hkH0, hkNS, a, ha, rfl⟩
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨htS, htAlt⟩, rfl⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨k, hkH0, by simp [outH, hkNS]; exact ⟨a, ha, rfl⟩⟩)
    · obtain ⟨i, hiEx, rfl⟩ := Finset.mem_image.mp hLeaf
      obtain ⟨hiAlt, hiNN⟩ := Finset.mem_sdiff.mp hiEx
      have hiA : AltNeed0 p root S (.input i) := (Finset.mem_filter.mp hiAlt).2
      have hiN0 : ¬ NeedCorner p root false (.input i, false) :=
        fun hN => hiNN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN⟩)
      exact hEntry (.input i) hiA hiN0
  have hDisj1 : Disjoint ((H0 p root S).image Wire.gate) (Boundary0 p root S) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw1
    exact (Finset.mem_filter.mp hk).2.2 (Finset.mem_filter.mp hw2).2.1
  have hDisj2 : Disjoint ((H0 p root S).image Wire.gate ∪ Boundary0 p root S)
      (leafExtra.image Wire.input) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨i, hiEx, rfl⟩ := Finset.mem_image.mp hw2
    rcases Finset.mem_union.mp hw1 with hG | hB
    · obtain ⟨k, _, hEq⟩ := Finset.mem_image.mp hG; cases hEq
    · have hN0 := (Finset.mem_filter.mp hB).2.1
      rw [cornerValue_input] at hN0
      exact (Finset.mem_sdiff.mp hiEx).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hN0⟩)
  have hTargetCard : target.card = (H0 p root S).card + (Boundary0 p root S).card + leafExtra.card := by
    dsimp only [target]
    rw [Finset.card_union_of_disjoint hDisj2, Finset.card_union_of_disjoint hDisj1,
      Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl),
      Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)]
  have hOutHCard (k : Fin g) (hk : k ∈ H0 p root S) :
      (outH k).card ≤ 1 + if k ∈ badFlip p root ∪ Z0 p root then 1 else 0 := by
    dsimp only [outH]
    by_cases hkS : k ∈ S
    · simp [hkS]
    · simp only [hkS, ite_false]
      have hImgLe : ((selectedPins (p.lines k).op _).image (p.lines k).wires).card ≤
          (selectedPins (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s))).card :=
        Finset.card_image_le
      by_cases hDeg : ¬ ((p.lines k).op = .and ∧ cornerValue p false (.gate k) = true) ∧
          ¬ ((p.lines k).op = .or ∧ cornerValue p false (.gate k) = false)
      · have hDeg' : ¬ ((p.lines k).op = .and ∧
              interpretation (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s)) = true) ∧
            ¬ ((p.lines k).op = .or ∧
              interpretation (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s)) = false) := by
          simpa [← cornerValue_gate] using hDeg
        have hLe1 := op_selectedPins_card_le_one (p.lines k).op _ hDeg'
        exact hImgLe.trans (hLe1.trans (Nat.le_add_right 1 _))
      · have hkBZ := h0_branch_in_badFlip_or_Z0 h0 h1 hk hDeg
        have hLe2 := op_selectedPins_card_le (p.lines k).op
          (fun s => cornerValue p false ((p.lines k).wires s))
        split_ifs
        exact hImgLe.trans hLe2
  have hRhsCard : (outS ∪ (H0 p root S).biUnion outH).card ≤
      sHit.card + (H0 p root S).card + (H0 p root S ∩ (badFlip p root ∪ Z0 p root)).card := by
    have hU := Finset.card_union_le outS ((H0 p root S).biUnion outH)
    have hS1 : outS.card ≤ sHit.card := Finset.card_image_le
    have hB1 : ((H0 p root S).biUnion outH).card ≤ ∑ k ∈ H0 p root S, (outH k).card :=
      Finset.card_biUnion_le
    have hSum : ∑ k ∈ H0 p root S, (outH k).card ≤
        (H0 p root S).card + (H0 p root S ∩ (badFlip p root ∪ Z0 p root)).card := by
      calc
        ∑ k ∈ H0 p root S, (outH k).card ≤
            ∑ k ∈ H0 p root S, (1 + if k ∈ badFlip p root ∪ Z0 p root then 1 else 0) :=
          Finset.sum_le_sum hOutHCard
        _ = (∑ _k ∈ H0 p root S, 1) +
            ∑ k ∈ H0 p root S, (if k ∈ badFlip p root ∪ Z0 p root then 1 else 0) :=
          Finset.sum_add_distrib
        _ = (H0 p root S).card + (H0 p root S ∩ (badFlip p root ∪ Z0 p root)).card := by
          congr 1
          · simp
          · rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
              Finset.filter_mem_eq_inter]
    omega
  have hLe := (Finset.card_le_card hSub).trans hRhsCard
  rw [hTargetCard] at hLe
  dsimp only [sHit, leafExtra] at hLe
  omega

theorem altNeed1_extra_inputs_card (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (S : Finset (Fin g)) :
    (altNeed1_inputs p root S \ needInputs p root true).card ≤
      S.card + 3 * (badFlip p root).card + shared p root := by
  have h := altNeed1_leaf_and_boundary_card p root h0 h1 S
  have hS : (S.filter fun t => AltNeed1 p root S (.gate t)).card ≤ S.card :=
    Finset.card_filter_le _ _
  have hI : (H1 p root S ∩ (badFlip p root ∪ Z1 p root)).card ≤ (badFlip p root ∪ Z1 p root).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hU : (badFlip p root ∪ Z1 p root).card ≤ (badFlip p root).card + (Z1 p root).card :=
    Finset.card_union_le ..
  have hZ := card_Z1_le p root h0 h1
  omega

theorem altNeed0_extra_inputs_card (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (S : Finset (Fin g)) :
    (altNeed0_inputs p root S \ needInputs p root false).card ≤
      S.card + 3 * (badFlip p root).card + shared p root := by
  have h := altNeed0_leaf_and_boundary_card p root h0 h1 S
  have hS : (S.filter fun t => AltNeed0 p root S (.gate t)).card ≤ S.card :=
    Finset.card_filter_le _ _
  have hI : (H0 p root S ∩ (badFlip p root ∪ Z0 p root)).card ≤ (badFlip p root ∪ Z0 p root).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hU : (badFlip p root ∪ Z0 p root).card ≤ (badFlip p root).card + (Z0 p root).card :=
    Finset.card_union_le ..
  have hZ := card_Z0_le p root h0 h1
  omega

/-! ### ReachesCut sets (`PureH0Bad`, `PureH1Bad`) and dual-chain bounds -/

inductive ReachesCut1 (p : Program signature n g) (root : Wire n g) : Wire n g → Prop where
  | hit {k : Fin g} (hk : k ∈ CutGate p root) : ReachesCut1 p root (.gate k)
  | step {k : Fin g} (hNotNeed1 : ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k)))
      (hNotCut : k ∉ CutGate p root)
      {a : Fin (signature.Arity (p.lines k).op)}
      (ha : a ∈ selectedPins (p.lines k).op (fun s => cornerValue p true ((p.lines k).wires s)))
      (hChild : ReachesCut1 p root ((p.lines k).wires a)) : ReachesCut1 p root (.gate k)

inductive ReachesCut0 (p : Program signature n g) (root : Wire n g) : Wire n g → Prop where
  | hit {k : Fin g} (hk : k ∈ CutGate p root) : ReachesCut0 p root (.gate k)
  | step {k : Fin g} (hNotNeed0 : ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k)))
      (hNotCut : k ∉ CutGate p root)
      {a : Fin (signature.Arity (p.lines k).op)}
      (ha : a ∈ selectedPins (p.lines k).op (fun s => cornerValue p false ((p.lines k).wires s)))
      (hChild : ReachesCut0 p root ((p.lines k).wires a)) : ReachesCut0 p root (.gate k)

inductive CleanZeroPath (p : Program signature n g) (root : Wire n g) (m : Fin g) :
    ℕ → Wire n g → Prop where
  | base (hm : m ∈ CutGate p root) : CleanZeroPath p root m 0 (.gate m)
  | step {d : ℕ} {k : Fin g} {w : Wire n g}
      (hNotNeed1 : ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k)))
      (hNotCut : k ∉ CutGate p root)
      (hMem0 : (w, false) ∈ reqCorner p root false k)
      (hPrev : CleanZeroPath p root m d w) : CleanZeroPath p root m (d + 1) (.gate k)

inductive CleanOnePath (p : Program signature n g) (root : Wire n g) (m : Fin g) :
    ℕ → Wire n g → Prop where
  | base (hm : m ∈ CutGate p root) : CleanOnePath p root m 0 (.gate m)
  | step {d : ℕ} {k : Fin g} {w : Wire n g}
      (hNotNeed0 : ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k)))
      (hNotCut : k ∉ CutGate p root)
      (hMem1 : (w, true) ∈ reqCorner p root true k)
      (hPrev : CleanOnePath p root m d w) : CleanOnePath p root m (d + 1) (.gate k)

private theorem reachesCut1_to_cleanZeroPath {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {w : Wire n g} (h : ReachesCut1 p root w) :
    ∃ m d, CleanZeroPath p root m d w := by
  induction h with
  | @hit k hk => exact ⟨k, 0, CleanZeroPath.base hk⟩
  | @step k hNotN1 hNotC a _ _ ih =>
    obtain ⟨m, d, hd⟩ := ih
    have hbf := not_badFlip_of_not_cutGate hNotC
    have hPure : IsPureOR0 p root k := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exact (hNotN1 ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)).elim
      · exact (hNotN1 ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)).elim
      · exact (hNotN1 ((needCorner_eq_cornerValue h1 hPA.2.2).symm ▸ hPA.2.2)).elim
      · exact hPO
    have hnb := (not_s0_s1_of_not_badFlip hbf).1
    have hMem0 : ((p.lines k).wires a, false) ∈ reqCorner p root false k :=
      (pureOR0_children h0 hnb hPure a).1
    exact ⟨m, d + 1, CleanZeroPath.step hNotN1 hNotC hMem0 hd⟩

private theorem reachesCut0_to_cleanOnePath {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {w : Wire n g} (h : ReachesCut0 p root w) :
    ∃ m d, CleanOnePath p root m d w := by
  induction h with
  | @hit k hk => exact ⟨k, 0, CleanOnePath.base hk⟩
  | @step k hNotN0 hNotC a _ _ ih =>
    obtain ⟨m, d, hd⟩ := ih
    have hbf := not_badFlip_of_not_cutGate hNotC
    have hPure : IsPureAND1 p root k := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exact (hNotN0 ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)).elim
      · exact (hNotN0 ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)).elim
      · exact hPA
      · exact (hNotN0 ((needCorner_eq_cornerValue h0 hPO.2.1).symm ▸ hPO.2.1)).elim
    have hnb := (not_s0_s1_of_not_badFlip hbf).1
    have hMem1 : ((p.lines k).wires a, true) ∈ reqCorner p root true k :=
      (pureAND1_children h1 hnb hPure a).1
    exact ⟨m, d + 1, CleanOnePath.step hNotN0 hNotC hMem1 hd⟩

private theorem cleanZeroPath_unique {p : Program signature n g} {root : Wire n g} {m : Fin g} :
    ∀ d {w1 w2}, CleanZeroPath p root m d w1 → CleanZeroPath p root m d w2 → w1 = w2 := by
  intro d
  induction d with
  | zero =>
    intro w1 w2 h1 h2
    cases h1; cases h2; rfl
  | succ d ih =>
    intro w1 w2 h1 h2
    cases h1 with
    | @step _ k1 u1 _ hk1 hr1 hp1 =>
      cases h2 with
      | @step _ k2 u2 _ _ hr2 hp2 =>
        have hu : u1 = u2 := ih hp1 hp2
        subst hu
        have hEq : k1 = k2 := req_unique_parent (cutGate_not_hasRepeat hk1)
          (Finset.mem_union_left _ hr1) (Finset.mem_union_left _ hr2)
        subst hEq; rfl

private theorem cleanOnePath_unique {p : Program signature n g} {root : Wire n g} {m : Fin g} :
    ∀ d {w1 w2}, CleanOnePath p root m d w1 → CleanOnePath p root m d w2 → w1 = w2 := by
  intro d
  induction d with
  | zero =>
    intro w1 w2 h1 h2
    cases h1; cases h2; rfl
  | succ d ih =>
    intro w1 w2 h1 h2
    cases h1 with
    | @step _ k1 u1 _ hk1 hr1 hp1 =>
      cases h2 with
      | @step _ k2 u2 _ _ hr2 hp2 =>
        have hu : u1 = u2 := ih hp1 hp2
        subst hu
        have hEq : k1 = k2 := req_unique_parent (cutGate_not_hasRepeat hk1)
          (Finset.mem_union_right _ hr1) (Finset.mem_union_right _ hr2)
        subst hEq; rfl

noncomputable def PureH0Bad (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in
  (segTopOR p root).filter fun t => ReachesCut1 p root (sideChild p t)

noncomputable def PureH1Bad (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in
  (segTopAND p root).filter fun t => ReachesCut0 p root (sideChild p t)

private theorem cleanZeroPath_base_need {p : Program signature n g} {root : Wire n g}
    {m : Fin g} : ∀ {d : ℕ} {w : Wire n g},
    CleanZeroPath p root m d w → NeedCorner p root false (w, false) →
    NeedCorner p root false (.gate m, false)
  | _, _, .base _, hw => hw
  | _, _, .step _ _ hMem0 hPrev, _ =>
    cleanZeroPath_base_need hPrev (needCorner_child_of_reqCorner hMem0)

private theorem cleanOnePath_base_need {p : Program signature n g} {root : Wire n g}
    {m : Fin g} : ∀ {d : ℕ} {w : Wire n g},
    CleanOnePath p root m d w → NeedCorner p root true (w, true) →
    NeedCorner p root true (.gate m, true)
  | _, _, .base _, hw => hw
  | _, _, .step _ _ hMem1 hPrev, _ =>
    cleanOnePath_base_need hPrev (needCorner_child_of_reqCorner hMem1)

theorem card_pureH0Bad_le_sdiff_S0 (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (PureH0Bad p root).card ≤ (CutGate p root \ S0 p root).card := by
  classical
  have hEx : ∀ t ∈ PureH0Bad p root,
      ∃ m d, m ∈ CutGate p root \ S0 p root ∧ CleanZeroPath p root m d (sideChild p t) := by
    intro t ht
    obtain ⟨m, d, hd⟩ := reachesCut1_to_cleanZeroPath h0 h1 (Finset.mem_filter.mp ht).2
    have hCutMem : ∀ {d0} {w0}, CleanZeroPath p root m d0 w0 → m ∈ CutGate p root := by
      intro d0 w0 hw0
      induction hw0 with
      | base h => exact h
      | step _ _ _ _ ih => exact ih
    have htG := segTopOR_goodDual (Finset.mem_filter.mp ht).1
    have hnb := (not_s0_s1_of_not_badFlip
      (not_badFlip_of_not_otherBad (goodDual_iff.mp htG.1).2)).1
    have hmNeed : NeedCorner p root false (.gate m, false) :=
      cleanZeroPath_base_need hd (dualOR_children h0 h1 hnb htG.2.1).2.2.2.2.2.2.2.1
    have hmNotS0 : m ∉ S0 p root := fun hmS0 => by
      have hF := (needCorner_eq_cornerValue h0 hmNeed).symm
      have hT := (needCorner_eq_cornerValue h0 (Finset.mem_filter.mp hmS0).2).symm
      rw [hF] at hT; cases hT
    exact ⟨m, d, Finset.mem_sdiff.mpr ⟨hCutMem hd, hmNotS0⟩, hd⟩
  choose mOf hmProp using fun t (ht : t ∈ PureH0Bad p root) => hEx t ht
  let mFun (t : Fin g) : Fin g := if ht : t ∈ PureH0Bad p root then mOf t ht else t
  have hmFun {t} (ht : t ∈ PureH0Bad p root) : mFun t = mOf t ht := by
    simp only [mFun]
    split_ifs
    rfl
  refine Finset.card_le_card_of_injOn mFun
    (fun t ht => by rw [hmFun ht]; obtain ⟨_, hm, _⟩ := hmProp t ht; exact hm) ?_
  intro t1 ht1 t2 ht2 hEq
  have hEq' : mOf t1 ht1 = mOf t2 ht2 := by
    rwa [hmFun ht1, hmFun ht2] at hEq
  obtain ⟨d1, _, hd1⟩ := hmProp t1 ht1
  obtain ⟨d2, _, hd2⟩ := hmProp t2 ht2
  rw [← hEq'] at hd2
  have hMain : ∀ dA dB (a b : Fin g), a ∈ segTopOR p root → b ∈ segTopOR p root →
      CleanZeroPath p root (mOf t1 ht1) dA (sideChild p a) →
      CleanZeroPath p root (mOf t1 ht1) dB (sideChild p b) →
      dA ≤ dB → a = b := by
    intro dA dB a b ha hb hPA hPB hle
    have haG := segTopOR_goodDual ha
    have hbG := segTopOR_goodDual hb
    have haNotC : a ∉ CutGate p root := not_cutGate_of_not_cutNode haG.2.2.1
    have haSide : (sideChild p a, false) ∈ reqCorner p root false a := by
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp haG.1).2)).1
      exact dualOR_reqCorner_sideChild h0 h1 hnb haG.2.1
    have hbSide : (sideChild p b, false) ∈ reqCorner p root false b := by
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hbG.1).2)).1
      exact dualOR_reqCorner_sideChild h0 h1 hnb hbG.2.1
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hStep : ∀ {m dSub} {z : Wire n g}, CleanZeroPath p root m dSub z →
          ∀ dTarget, dTarget < dSub →
          ∃ k w, ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k)) ∧
            (w, false) ∈ reqCorner p root false k ∧ CleanZeroPath p root m dTarget w := by
        intro m dSub z hz
        induction hz with
        | base _ => intro _ hLt; omega
        | @step d k w hkN _ hkR hkP ih =>
          intro dTarget hLt
          by_cases hEqD : dTarget = d
          · subst hEqD; exact ⟨k, w, hkN, hkR, hkP⟩
          · exact ih dTarget (by omega)
      obtain ⟨k, w, hkN, hkR, hwP⟩ := hStep hPB dA hlt
      have hwEq : w = sideChild p a := cleanZeroPath_unique dA hwP hPA
      rw [hwEq] at hkR
      have hEqKa : a = k := req_unique_parent (cutGate_not_hasRepeat haNotC)
        (reqCorner_subset_req_left haSide) (reqCorner_subset_req_left hkR)
      subst hEqKa
      have hVal := (needCorner_eq_cornerValue h1 haG.2.1.2.2).symm
      exact hkN (hVal.symm ▸ haG.2.1.2.2)
    · subst heq
      have hwEq : sideChild p a = sideChild p b := cleanZeroPath_unique dA hPA hPB
      rw [hwEq] at haSide
      exact req_unique_parent (cutGate_not_hasRepeat haNotC)
        (reqCorner_subset_req_left haSide) (reqCorner_subset_req_left hbSide)
  by_cases hle : d1 ≤ d2
  · exact hMain d1 d2 t1 t2 (Finset.mem_filter.mp ht1).1 (Finset.mem_filter.mp ht2).1 hd1 hd2 hle
  · exact (hMain d2 d1 t2 t1 (Finset.mem_filter.mp ht2).1 (Finset.mem_filter.mp ht1).1
      hd2 hd1 (Nat.le_of_not_ge hle)).symm

theorem card_pureH0Bad_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (PureH0Bad p root).card ≤ (CutGate p root).card :=
  (card_pureH0Bad_le_sdiff_S0 p root h0 h1).trans (Finset.card_le_card Finset.sdiff_subset)

theorem card_pureH1Bad_le_sdiff_S1 (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (PureH1Bad p root).card ≤ (CutGate p root \ S1 p root).card := by
  classical
  have hEx : ∀ t ∈ PureH1Bad p root,
      ∃ m d, m ∈ CutGate p root \ S1 p root ∧ CleanOnePath p root m d (sideChild p t) := by
    intro t ht
    obtain ⟨m, d, hd⟩ := reachesCut0_to_cleanOnePath h0 h1 (Finset.mem_filter.mp ht).2
    have hCutMem : ∀ {d0} {w0}, CleanOnePath p root m d0 w0 → m ∈ CutGate p root := by
      intro d0 w0 hw0
      induction hw0 with
      | base h => exact h
      | step _ _ _ _ ih => exact ih
    have htG := segTopAND_goodDual (Finset.mem_filter.mp ht).1
    have hnb := (not_s0_s1_of_not_badFlip
      (not_badFlip_of_not_otherBad (goodDual_iff.mp htG.1).2)).1
    have hmNeed : NeedCorner p root true (.gate m, true) :=
      cleanOnePath_base_need hd (dualAND_children h0 h1 hnb htG.2.1).2.2.2.2.2.2.2.1
    have hmNotS1 : m ∉ S1 p root := fun hmS1 => by
      have hT := (needCorner_eq_cornerValue h1 hmNeed).symm
      have hF := (needCorner_eq_cornerValue h1 (Finset.mem_filter.mp hmS1).2).symm
      rw [hT] at hF; cases hF
    exact ⟨m, d, Finset.mem_sdiff.mpr ⟨hCutMem hd, hmNotS1⟩, hd⟩
  choose mOf hmProp using fun t (ht : t ∈ PureH1Bad p root) => hEx t ht
  let mFun (t : Fin g) : Fin g := if ht : t ∈ PureH1Bad p root then mOf t ht else t
  have hmFun {t} (ht : t ∈ PureH1Bad p root) : mFun t = mOf t ht := by
    simp only [mFun]
    split_ifs
    rfl
  refine Finset.card_le_card_of_injOn mFun
    (fun t ht => by rw [hmFun ht]; obtain ⟨_, hm, _⟩ := hmProp t ht; exact hm) ?_
  intro t1 ht1 t2 ht2 hEq
  have hEq' : mOf t1 ht1 = mOf t2 ht2 := by
    rwa [hmFun ht1, hmFun ht2] at hEq
  obtain ⟨d1, _, hd1⟩ := hmProp t1 ht1
  obtain ⟨d2, _, hd2⟩ := hmProp t2 ht2
  rw [← hEq'] at hd2
  have hMain : ∀ dA dB (a b : Fin g), a ∈ segTopAND p root → b ∈ segTopAND p root →
      CleanOnePath p root (mOf t1 ht1) dA (sideChild p a) →
      CleanOnePath p root (mOf t1 ht1) dB (sideChild p b) →
      dA ≤ dB → a = b := by
    intro dA dB a b ha hb hPA hPB hle
    have haG := segTopAND_goodDual ha
    have hbG := segTopAND_goodDual hb
    have haNotC : a ∉ CutGate p root := not_cutGate_of_not_cutNode haG.2.2.1
    have haSide : (sideChild p a, true) ∈ reqCorner p root true a := by
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp haG.1).2)).1
      exact dualAND_reqCorner_sideChild h0 h1 hnb haG.2.1
    have hbSide : (sideChild p b, true) ∈ reqCorner p root true b := by
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hbG.1).2)).1
      exact dualAND_reqCorner_sideChild h0 h1 hnb hbG.2.1
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hStep : ∀ {m dSub} {z : Wire n g}, CleanOnePath p root m dSub z →
          ∀ dTarget, dTarget < dSub →
          ∃ k w, ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k)) ∧
            (w, true) ∈ reqCorner p root true k ∧ CleanOnePath p root m dTarget w := by
        intro m dSub z hz
        induction hz with
        | base _ => intro _ hLt; omega
        | @step d k w hkN _ hkR hkP ih =>
          intro dTarget hLt
          by_cases hEqD : dTarget = d
          · subst hEqD; exact ⟨k, w, hkN, hkR, hkP⟩
          · exact ih dTarget (by omega)
      obtain ⟨k, w, hkN, hkR, hwP⟩ := hStep hPB dA hlt
      have hwEq : w = sideChild p a := cleanOnePath_unique dA hwP hPA
      rw [hwEq] at hkR
      have hEqKa : a = k := req_unique_parent (cutGate_not_hasRepeat haNotC)
        (reqCorner_subset_req_right haSide) (reqCorner_subset_req_right hkR)
      subst hEqKa
      have hVal := (needCorner_eq_cornerValue h0 haG.2.1.2.1).symm
      exact hkN (hVal.symm ▸ haG.2.1.2.1)
    · subst heq
      have hwEq : sideChild p a = sideChild p b := cleanOnePath_unique dA hPA hPB
      rw [hwEq] at haSide
      exact req_unique_parent (cutGate_not_hasRepeat haNotC)
        (reqCorner_subset_req_right haSide) (reqCorner_subset_req_right hbSide)
  by_cases hle : d1 ≤ d2
  · exact hMain d1 d2 t1 t2 (Finset.mem_filter.mp ht1).1 (Finset.mem_filter.mp ht2).1 hd1 hd2 hle
  · exact (hMain d2 d1 t2 t1 (Finset.mem_filter.mp ht2).1 (Finset.mem_filter.mp ht1).1
      hd2 hd1 (Nat.le_of_not_ge hle)).symm

theorem card_pureH1Bad_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (PureH1Bad p root).card ≤ (CutGate p root).card :=
  (card_pureH1Bad_le_sdiff_S1 p root h0 h1).trans (Finset.card_le_card Finset.sdiff_subset)

theorem card_pureH0Bad_add_pureH1Bad_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (PureH0Bad p root).card + (PureH1Bad p root).card ≤
      10 * (badGates p root).card + 11 * shared p root := by
  classical
  have hSub0 : CutGate p root \ S0 p root ⊆
      (otherBad p root \ S0 p root) ∪ Finset.univ.filter (HasRepeat p root) := by
    intro k hk
    obtain ⟨hkC, hns0⟩ := Finset.mem_sdiff.mp hk
    rcases Finset.mem_union.mp hkC with hOB | hR
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hOB, hns0⟩)
    · exact Finset.mem_union_right _ hR
  have hSub1 : CutGate p root \ S1 p root ⊆
      (otherBad p root \ S1 p root) ∪ Finset.univ.filter (HasRepeat p root) := by
    intro k hk
    obtain ⟨hkC, hns1⟩ := Finset.mem_sdiff.mp hk
    rcases Finset.mem_union.mp hkC with hOB | hR
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hOB, hns1⟩)
    · exact Finset.mem_union_right _ hR
  have hP0 := (card_pureH0Bad_le_sdiff_S0 p root h0 h1).trans
    ((Finset.card_le_card hSub0).trans (Finset.card_union_le ..))
  have hP1 := (card_pureH1Bad_le_sdiff_S1 p root h0 h1).trans
    ((Finset.card_le_card hSub1).trans (Finset.card_union_le ..))
  have hOB := card_otherBad_sdiff_S0_add_S1_le_tight p root h0 h1
  have hHR := card_hasRepeat_le p root
  omega

theorem h1_disjoint_cutGate {p : Program signature n g} {root : Wire n g}
    (h1 : cornerValue p true root = true) :
    ∀ {w}, AltNeed1 p root (segTopOR p root \ PureH0Bad p root) w →
      ¬ NeedCorner p root true (w, cornerValue p true w) → ¬ ReachesCut1 p root w := by
  intro w hw hNotN1 hReach
  induction hw with
  | output => exact hNotN1 (h1.symm ▸ NeedCorner.output)
  | @branchS k _ hkS =>
    have hkNotBad := (Finset.mem_sdiff.mp hkS).2
    exact hkNotBad (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hkS).1, hReach⟩)
  | @branchRest k _ _ a ha ih =>
    have hkNotN1 : ¬ NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := by
      intro hkN1
      exact hNotN1 (needCorner_child_of_reqCorner (corner_arg_mem_reqCorner hkN1 ha))
    have hkNotCut : k ∉ CutGate p root :=
      fun hkC => (ih hkNotN1) (ReachesCut1.hit hkC)
    exact (ih hkNotN1) (ReachesCut1.step hkNotN1 hkNotCut ha hReach)

theorem h0_disjoint_cutGate {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) :
    ∀ {w}, AltNeed0 p root (segTopAND p root \ PureH1Bad p root) w →
      ¬ NeedCorner p root false (w, cornerValue p false w) → ¬ ReachesCut0 p root w := by
  intro w hw hNotN0 hReach
  induction hw with
  | output => exact hNotN0 (h0.symm ▸ NeedCorner.output)
  | @branchS k _ hkS =>
    have hkNotBad := (Finset.mem_sdiff.mp hkS).2
    exact hkNotBad (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hkS).1, hReach⟩)
  | @branchRest k _ _ a ha ih =>
    have hkNotN0 : ¬ NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := by
      intro hkN0
      exact hNotN0 (needCorner_child_of_reqCorner (corner_arg_mem_reqCorner hkN0 ha))
    have hkNotCut : k ∉ CutGate p root :=
      fun hkC => (ih hkNotN0) (ReachesCut0.hit hkC)
    exact (ih hkNotN0) (ReachesCut0.step hkNotN0 hkNotCut ha hReach)

/-- Strictly below `S` along clean `goodDual` `dualChild` edges. -/
inductive BelowDualChain (p : Program signature n g) (root : Wire n g) (S : Finset (Fin g)) :
    Wire n g → Prop where
  | direct {t : Fin g} (ht : t ∈ S) : BelowDualChain p root S (dualChild p t)
  | step {k : Fin g} (hkPrev : BelowDualChain p root S (.gate k))
      (hkG : k ∈ goodDual p root) (hkC : ¬ CutNode p root k) :
      BelowDualChain p root S (dualChild p k)

theorem altNeed1_avoids_belowDualChain {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (hS : ∀ t ∈ segTopOR p root \ PureH0Bad p root, t ∈ segTopOR p root)
    {w : Wire n g} (hw : AltNeed1 p root (segTopOR p root \ PureH0Bad p root) w) :
    ¬ BelowDualChain p root (segTopOR p root \ PureH0Bad p root) w := by
  let S := segTopOR p root \ PureH0Bad p root
  have hParent : ∀ u, BelowDualChain p root S u →
      ∃ g0 : Fin g, g0 ∈ goodDual p root ∧ ¬ CutNode p root g0 ∧
        dualChild p g0 = u ∧ (g0 ∈ S ∨ BelowDualChain p root S (.gate g0)) := by
    intro u hu
    cases hu with
    | @direct t ht =>
      have htG := segTopOR_goodDual (hS t ht)
      exact ⟨t, htG.1, htG.2.2.1, rfl, Or.inl ht⟩
    | @step k hkPrev hkG hkC =>
      exact ⟨k, hkG, hkC, rfl, Or.inr hkPrev⟩
  have hDualVals : ∀ u, BelowDualChain p root S u →
      NeedCorner p root false (u, false) ∧ NeedCorner p root true (u, true) ∧
      cornerValue p false u = false ∧ cornerValue p true u = true := by
    intro u hu
    obtain ⟨g0, hgG, _, rfl, _⟩ := hParent u hu
    have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hgG).2)).1
    rcases (goodDual_iff.mp hgG).1 with hDA | hDO
    · have hC := dualAND_children h0 h1 hnb hDA
      exact ⟨hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2.1⟩
    · have hC := dualOR_children h0 h1 hnb hDO
      exact ⟨hC.2.2.2.2.2.2.1, hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1⟩
  induction hw with
  | output =>
    intro hB
    have hF := (hDualVals root hB).2.2.1
    rw [h0] at hF
    cases hF
  | @branchS k _ hkS ih =>
    intro hB
    obtain ⟨g0, hgG, _, hEq, hgKind⟩ := hParent (sideChild p k) hB
    have hkG' := segTopOR_goodDual (hS k hkS)
    have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG'.1).2)).1
    have hkSide : (sideChild p k, false) ∈ reqCorner p root false k :=
      dualOR_reqCorner_sideChild h0 h1 hnb hkG'.2.1
    have hkNotR : ¬ HasRepeat p root k :=
      stopGate_not_hasRepeat (not_stopGate_of_not_cutNode hkG'.2.2.1)
    have hgReq := hEq ▸ (segEdge_req_dualChild h0 h1 hgG).1
    have hEqKg : k = g0 := req_unique_parent hkNotR
      (reqCorner_subset_req_left hkSide) (reqCorner_subset_req_left hgReq)
    subst hEqKg
    rcases hgKind with _ | hPrev
    · exact (dualChild_ne_sideChild hnb) hEq
    · exact ih hPrev
  | @branchRest k hk hkS a ha ih =>
    intro hB
    obtain ⟨g0, hgG, hgC, hEq, hgKind⟩ := hParent ((p.lines k).wires a) hB
    have hgNotR : ¬ HasRepeat p root g0 :=
      stopGate_not_hasRepeat (not_stopGate_of_not_cutNode hgC)
    by_cases hkN1 : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
    · have hkR1 := corner_arg_mem_reqCorner hkN1 ha
      have hv : cornerValue p true ((p.lines k).wires a) = true := (hDualVals _ hB).2.2.2
      rw [hv] at hkR1
      have hgR1 := hEq ▸ (segEdge_req_dualChild h0 h1 hgG).2
      have hEqKg : g0 = k := req_unique_parent hgNotR
        (reqCorner_subset_req_right hgR1) (reqCorner_subset_req_right hkR1)
      subst hEqKg
      rcases hgKind with hkInS | hPrev
      · exact hkS hkInS
      · exact ih hPrev
    · have hkNotCut : k ∉ CutGate p root := fun hkC =>
        h1_disjoint_cutGate h1 hk hkN1 (ReachesCut1.hit hkC)
      have hkPure : IsPureOR0 p root k := by
        rcases four_way_of_not_badFlip h0 h1 (not_badFlip_of_not_cutGate hkNotCut) with
          hDA | hDO | hPA | hPO
        · exact (hkN1 ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)).elim
        · exact (hkN1 ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)).elim
        · exact (hkN1 ((needCorner_eq_cornerValue h1 hPA.2.2).symm ▸ hPA.2.2)).elim
        · exact hPO
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_cutGate hkNotCut)).1
      have hkR0 : ((p.lines k).wires a, false) ∈ reqCorner p root false k :=
        (pureOR0_children h0 hnb hkPure a).1
      have hgR0 := hEq ▸ (segEdge_req_dualChild h0 h1 hgG).1
      have hEqKg : g0 = k := req_unique_parent hgNotR
        (reqCorner_subset_req_left hgR0) (reqCorner_subset_req_left hkR0)
      subst hEqKg
      rcases (goodDual_iff.mp hgG).1 with hDA | hDO
      · exact hkN1 ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)
      · exact hkN1 ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)

theorem altNeed0_avoids_belowDualChain {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (hS : ∀ t ∈ segTopAND p root \ PureH1Bad p root, t ∈ segTopAND p root)
    {w : Wire n g} (hw : AltNeed0 p root (segTopAND p root \ PureH1Bad p root) w) :
    ¬ BelowDualChain p root (segTopAND p root \ PureH1Bad p root) w := by
  let S := segTopAND p root \ PureH1Bad p root
  have hParent : ∀ u, BelowDualChain p root S u →
      ∃ g0 : Fin g, g0 ∈ goodDual p root ∧ ¬ CutNode p root g0 ∧
        dualChild p g0 = u ∧ (g0 ∈ S ∨ BelowDualChain p root S (.gate g0)) := by
    intro u hu
    cases hu with
    | @direct t ht =>
      have htG := segTopAND_goodDual (hS t ht)
      exact ⟨t, htG.1, htG.2.2.1, rfl, Or.inl ht⟩
    | @step k hkPrev hkG hkC =>
      exact ⟨k, hkG, hkC, rfl, Or.inr hkPrev⟩
  have hDualVals : ∀ u, BelowDualChain p root S u →
      NeedCorner p root false (u, false) ∧ NeedCorner p root true (u, true) ∧
      cornerValue p false u = false ∧ cornerValue p true u = true := by
    intro u hu
    obtain ⟨g0, hgG, _, rfl, _⟩ := hParent u hu
    have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hgG).2)).1
    rcases (goodDual_iff.mp hgG).1 with hDA | hDO
    · have hC := dualAND_children h0 h1 hnb hDA
      exact ⟨hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2.1⟩
    · have hC := dualOR_children h0 h1 hnb hDO
      exact ⟨hC.2.2.2.2.2.2.1, hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1⟩
  induction hw with
  | output =>
    intro hB
    have hF := (hDualVals root hB).2.2.1
    rw [h0] at hF
    cases hF
  | @branchS k _ hkS ih =>
    intro hB
    obtain ⟨g0, hgG, _, hEq, hgKind⟩ := hParent (sideChild p k) hB
    have hkG' := segTopAND_goodDual (hS k hkS)
    have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG'.1).2)).1
    have hkSide : (sideChild p k, true) ∈ reqCorner p root true k :=
      dualAND_reqCorner_sideChild h0 h1 hnb hkG'.2.1
    have hkNotR : ¬ HasRepeat p root k :=
      stopGate_not_hasRepeat (not_stopGate_of_not_cutNode hkG'.2.2.1)
    have hgReq := hEq ▸ (segEdge_req_dualChild h0 h1 hgG).2
    have hEqKg : k = g0 := req_unique_parent hkNotR
      (reqCorner_subset_req_right hkSide) (reqCorner_subset_req_right hgReq)
    subst hEqKg
    rcases hgKind with _ | hPrev
    · exact (dualChild_ne_sideChild hnb) hEq
    · exact ih hPrev
  | @branchRest k hk hkS a ha ih =>
    intro hB
    obtain ⟨g0, hgG, hgC, hEq, hgKind⟩ := hParent ((p.lines k).wires a) hB
    have hgNotR : ¬ HasRepeat p root g0 :=
      stopGate_not_hasRepeat (not_stopGate_of_not_cutNode hgC)
    by_cases hkN0 : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
    · have hkR0 := corner_arg_mem_reqCorner hkN0 ha
      have hv : cornerValue p false ((p.lines k).wires a) = false := (hDualVals _ hB).2.2.1
      rw [hv] at hkR0
      have hgR0 := hEq ▸ (segEdge_req_dualChild h0 h1 hgG).1
      have hEqKg : g0 = k := req_unique_parent hgNotR
        (reqCorner_subset_req_left hgR0) (reqCorner_subset_req_left hkR0)
      subst hEqKg
      rcases hgKind with hkInS | hPrev
      · exact hkS hkInS
      · exact ih hPrev
    · have hkNotCut : k ∉ CutGate p root := fun hkC =>
        h0_disjoint_cutGate h0 hk hkN0 (ReachesCut0.hit hkC)
      have hkPure : IsPureAND1 p root k := by
        rcases four_way_of_not_badFlip h0 h1 (not_badFlip_of_not_cutGate hkNotCut) with
          hDA | hDO | hPA | hPO
        · exact (hkN0 ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)).elim
        · exact (hkN0 ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)).elim
        · exact hPA
        · exact (hkN0 ((needCorner_eq_cornerValue h0 hPO.2.1).symm ▸ hPO.2.1)).elim
      have hnb := (not_s0_s1_of_not_badFlip (not_badFlip_of_not_cutGate hkNotCut)).1
      have hkR1 : ((p.lines k).wires a, true) ∈ reqCorner p root true k :=
        (pureAND1_children h1 hnb hkPure a).1
      have hgR1 := hEq ▸ (segEdge_req_dualChild h0 h1 hgG).2
      have hEqKg : g0 = k := req_unique_parent hgNotR
        (reqCorner_subset_req_right hgR1) (reqCorner_subset_req_right hkR1)
      subst hEqKg
      rcases (goodDual_iff.mp hgG).1 with hDA | hDO
      · exact hkN0 ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)
      · exact hkN0 ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)

/-- Multi-step clean `dualChild` chain inside `goodDual \ CutNode` ending at `z`. -/
inductive DualSteps (p : Program signature n g) (root : Wire n g) :
    ℕ → Fin g → Wire n g → Prop where
  | zero {k : Fin g} {z : Wire n g} (hkG : k ∈ goodDual p root) (hkC : ¬ CutNode p root k)
      (hChild : dualChild p k = z) : DualSteps p root 0 k z
  | succ {d : ℕ} {k j : Fin g} {z : Wire n g}
      (hkG : k ∈ goodDual p root) (hkC : ¬ CutNode p root k)
      (hChild : dualChild p k = .gate j) (hNext : DualSteps p root d j z) :
      DualSteps p root (d + 1) k z

private theorem dualSteps_unique {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) {z : Wire n g} :
    ∀ d {k1 k2 : Fin g}, DualSteps p root d k1 z → DualSteps p root d k2 z → k1 = k2 := by
  intro d
  induction d with
  | zero =>
    intro k1 k2 h1s h2s
    cases h1s with
    | zero hk1G hk1C hc1 =>
      cases h2s with
      | zero hk2G _ hc2 =>
        have hM1 : (z, true) ∈ req p root k1 :=
          Finset.mem_union_right _ (hc1 ▸ (segEdge_req_dualChild h0 h1 hk1G).2)
        have hM2 : (z, true) ∈ req p root k2 :=
          Finset.mem_union_right _ (hc2 ▸ (segEdge_req_dualChild h0 h1 hk2G).2)
        exact req_unique_parent (stopGate_not_hasRepeat (not_stopGate_of_not_cutNode hk1C)) hM1 hM2
  | succ d ih =>
    intro k1 k2 h1s h2s
    cases h1s with
    | @succ _ _ j1 _ hk1G hk1C hc1 hn1 =>
      cases h2s with
      | @succ _ _ j2 _ hk2G _ hc2 hn2 =>
        have hj : j1 = j2 := ih hn1 hn2
        subst hj
        have hM1 : ((.gate j1 : Wire n g), true) ∈ req p root k1 :=
          Finset.mem_union_right _ (hc1 ▸ (segEdge_req_dualChild h0 h1 hk1G).2)
        have hM2 : ((.gate j1 : Wire n g), true) ∈ req p root k2 :=
          Finset.mem_union_right _ (hc2 ▸ (segEdge_req_dualChild h0 h1 hk2G).2)
        exact req_unique_parent (stopGate_not_hasRepeat (not_stopGate_of_not_cutNode hk1C)) hM1 hM2

private theorem dualSteps_to_belowDualChain {p : Program signature n g} {root : Wire n g}
    {S : Finset (Fin g)} {d : ℕ} {k : Fin g} {z : Wire n g}
    (hkS : k ∈ S) (h : DualSteps p root d k z) : BelowDualChain p root S z := by
  induction d generalizing k with
  | zero =>
    cases h with
    | zero _ _ hc => rw [← hc]; exact BelowDualChain.direct hkS
  | succ d _ =>
    cases h with
    | @succ _ _ j _ _ _ hc hn =>
      have hMid : ∀ (d0 : ℕ) {a : Fin g} {z0 : Wire n g},
          DualSteps p root d0 a z0 → BelowDualChain p root S (.gate a) → BelowDualChain p root S z0 := by
        intro d0
        induction d0 with
        | zero =>
          intro a z0 ha hBa
          cases ha with
          | zero haG haC hca => rw [← hca]; exact BelowDualChain.step hBa haG haC
        | succ d0 ih0 =>
          intro a z0 ha hBa
          cases ha with
          | @succ _ _ b _ haG haC hcb hnb =>
            exact ih0 hnb (hcb ▸ BelowDualChain.step hBa haG haC)
      exact hMid d hn (hc ▸ BelowDualChain.direct hkS)

private theorem exists_dualSteps_leaf {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    ∀ m : ℕ, ∀ k : Fin g, k.val ≤ m → k ∈ goodDual p root → ¬ CutNode p root k →
      ∃ d z, DualSteps p root d k z ∧
        ((∃ i, z = .input i) ∨ ∃ c, CutNode p root c ∧ z = .gate c) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hk hkG hkC
    cases hChild : dualChild p k with
    | input i =>
      exact ⟨0, .input i, DualSteps.zero hkG hkC hChild, Or.inl ⟨i, rfl⟩⟩
    | gate j =>
      by_cases hjC : CutNode p root j
      · exact ⟨0, .gate j, DualSteps.zero hkG hkC hChild, Or.inr ⟨j, hjC, rfl⟩⟩
      · have hjG : j ∈ goodDual p root := by
          have hjReq := segEdge_req_dualChild h0 h1 hkG
          have hN0 := needCorner_child_of_reqCorner hjReq.1
          have hN1 := needCorner_child_of_reqCorner hjReq.2
          rw [hChild] at hN0 hN1
          have hjNotOB : j ∉ otherBad p root :=
            fun hOB => hkC (Or.inr ⟨hkG, j, hOB, hChild⟩)
          rcases not_otherBad_decomp h0 h1 hjNotOB with hGD | hPA | hPO
          · exact hGD.2
          · exact (hPA.2.1 hN0).elim
          · exact (hPO.2.2 hN1).elim
        have hjLt : j.val < k.val := by
          have hnb := (not_s0_s1_of_not_badFlip
            (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG).2)).1
          have hPre := dualChild_precedes (p := p) (k := k) (not_bad_structure p root hnb).1
          rw [hChild] at hPre
          exact Nat.succ_lt_succ_iff.mp hPre
        obtain ⟨d, z, hds, hz⟩ := ih j.val (by omega) j le_rfl hjG hjC
        exact ⟨d + 1, z, DualSteps.succ hkG hkC hChild hds, hz⟩

private theorem dualSteps_needCorner {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    ∀ {d k z}, DualSteps p root d k z →
      NeedCorner p root false (z, false) ∧ NeedCorner p root true (z, true) := by
  intro d k z h
  induction h with
  | zero hkG _ hc =>
    rw [← hc]
    have hr := segEdge_req_dualChild h0 h1 hkG
    exact ⟨needCorner_child_of_reqCorner hr.1, needCorner_child_of_reqCorner hr.2⟩
  | succ _ _ _ _ ih => exact ih

private theorem belowDualChain_mono {p : Program signature n g} {root : Wire n g}
    {S1 S2 : Finset (Fin g)} (hSub : S1 ⊆ S2) {w : Wire n g}
    (h : BelowDualChain p root S1 w) : BelowDualChain p root S2 w := by
  induction h with
  | direct ht => exact BelowDualChain.direct (hSub ht)
  | step _ hkG hkC ih => exact BelowDualChain.step ih hkG hkC

private theorem dualSteps_below_of_lt {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {z : Wire n g} :
    ∀ dB dA (a b : Fin g), dA < dB → DualSteps p root dA a z → DualSteps p root dB b z →
      BelowDualChain p root {b} (.gate a) := by
  intro dB
  induction dB with
  | zero => intro _ _ _ hLt; omega
  | succ d' ih =>
    intro dA a b hLt hA hB
    cases hB with
    | @succ _ _ j _ hbG hbC hbc hnj =>
      have hjG : j ∈ goodDual p root := by cases hnj <;> assumption
      have hjC : ¬ CutNode p root j := by cases hnj <;> assumption
      have hLift : ∀ u, BelowDualChain p root {j} u → BelowDualChain p root {b} u := by
        intro u hu
        induction hu with
        | direct hjMem =>
          rw [Finset.mem_singleton] at hjMem
          subst hjMem
          exact BelowDualChain.step (hbc ▸ BelowDualChain.direct (Finset.mem_singleton_self b)) hjG hjC
        | step _ hmG hmC ihU => exact BelowDualChain.step ihU hmG hmC
      by_cases hEq : dA = d'
      · subst hEq
        have haEqJ : a = j := dualSteps_unique h0 h1 dA hA hnj
        subst haEqJ
        exact hbc ▸ BelowDualChain.direct (Finset.mem_singleton_self b)
      · exact hLift _ (ih dA a j (by omega) hA hnj)

theorem card_altNeed1_compl_le_of_sparse {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (S : Finset (Fin c.size)) (hS : ∀ k ∈ S, k ∈ goodDual c.program (c.outputs 0) ∧
      (c.program.lines k).op = .or) :
    (Finset.univ \ altNeed1_inputs c.program (c.outputs 0) S).card ≤ B := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let fixed := altNeed1_inputs p root S
  let free := Finset.univ \ fixed
  let embed (u : free → Bool) (i : Fin n) : Bool :=
    if hi : i ∈ free then u ⟨i, hi⟩ else true
  have hAcc (u : free → Bool) : embed u ∈ acceptingTables f := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hTrace := altNeed1_sound p root h0 h1 S hS (embed u) fun i hi => by
      have hNot : i ∉ free := fun h => (Finset.mem_sdiff.mp h).2 hi
      simp [embed, hNot]
    change c.eval interpretation (embed u) 0 = true at hTrace
    rw [hc] at hTrace
    exact hTrace
  let into (u : free → Bool) : acceptingTables f := ⟨embed u, hAcc u⟩
  have hInj : Function.Injective into := by
    intro u v huv
    funext i
    simpa [into, embed, i.property] using congrFun (congrArg Subtype.val huv) i.val
  have hCard := (Fintype.card_le_of_injective into hInj).trans
    (by simpa [Fintype.card_coe] using hSparse)
  simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] at hCard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hCard

theorem card_altNeed0_compl_le_of_sparse {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true)
    (S : Finset (Fin c.size)) (hS : ∀ k ∈ S, k ∈ goodDual c.program (c.outputs 0) ∧
      (c.program.lines k).op = .and) :
    (Finset.univ \ altNeed0_inputs c.program (c.outputs 0) S).card ≤ B := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let fixed := altNeed0_inputs p root S
  let free := Finset.univ \ fixed
  let embed (u : free → Bool) (i : Fin n) : Bool :=
    if hi : i ∈ free then u ⟨i, hi⟩ else false
  have hAcc (u : free → Bool) : embed u ∈ acceptingTables f := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hTrace := altNeed0_sound p root h0 h1 S hS (embed u) fun i hi => by
      have hNot : i ∉ free := fun h => (Finset.mem_sdiff.mp h).2 hi
      simp [embed, hNot]
    change c.eval interpretation (embed u) 0 = true at hTrace
    rw [hc] at hTrace
    exact hTrace
  let into (u : free → Bool) : acceptingTables f := ⟨embed u, hAcc u⟩
  have hInj : Function.Injective into := by
    intro u v huv
    funext i
    simpa [into, embed, i.property] using congrFun (congrArg Subtype.val huv) i.val
  have hCard := (Fintype.card_le_of_injective into hInj).trans
    (by simpa [Fintype.card_coe] using hSparse)
  simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] at hCard
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hCard

private theorem dualSteps_endpoint_values {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {d : ℕ} {k : Fin g} {w : Wire n g} (h : DualSteps p root d k w) :
    cornerValue p false w = false ∧ cornerValue p true w = true := by
  induction h with
  | zero hk _ hw =>
    obtain ⟨hf,ht⟩ := segEdge_req_dualChild h0 h1 hk
    rw [hw] at hf ht
    exact ⟨(needCorner_eq_cornerValue h0 (needCorner_child_of_reqCorner hf)).symm,
      (needCorner_eq_cornerValue h1 (needCorner_child_of_reqCorner ht)).symm⟩
  | succ _ _ _ _ ih => exact ih

private theorem card_sHit1_le_dualCutNodes {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    let p := c.program
    let root := c.outputs 0
    let S := segTopOR p root \ PureH0Bad p root
    (S.filter fun t => AltNeed1 p root S (.gate t)).card ≤
      B + (dualCutNodes p root).card := by
  classical
  intro p root S
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let sHit := S.filter fun t => AltNeed1 p root S (.gate t)
  have hS : ∀ t ∈ S, t ∈ goodDual p root ∧ (p.lines t).op = .or := by
    intro t ht
    have htG := segTopOR_goodDual (Finset.mem_sdiff.mp ht).1
    exact ⟨htG.1, htG.2.1.1⟩
  have hSSub : ∀ t ∈ S, t ∈ segTopOR p root := fun t ht => (Finset.mem_sdiff.mp ht).1
  have hEx : ∀ t ∈ sHit, ∃ d z, DualSteps p root d t z ∧
      ((∃ i, z = .input i) ∨ ∃ c0, CutNode p root c0 ∧ z = .gate c0) := by
    intro t ht
    have htG := segTopOR_goodDual ((Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).1)
    exact exists_dualSteps_leaf h0 h1 t.val t le_rfl htG.1 htG.2.2.1
  choose dOf zOf hDZ using fun t (ht : t ∈ sHit) => hEx t ht
  let zFun (t : Fin c.size) : Wire n c.size := if ht : t ∈ sHit then zOf t ht else root
  have hzFun {t} (ht : t ∈ sHit) : zFun t = zOf t ht := by
    simp only [zFun]
    split_ifs
    rfl
  let cutSet := dualCutNodes p root
  let dropped := Finset.univ \ altNeed1_inputs p root S
  let targ := dropped.image Wire.input ∪ cutSet.image Wire.gate
  have hMaps : ∀ t ∈ sHit, zFun t ∈ targ := by
    intro t ht
    rw [hzFun ht]
    obtain ⟨hds, hLeaf⟩ := hDZ t ht
    have hBelow := dualSteps_to_belowDualChain (Finset.mem_filter.mp ht).1 hds
    have hNotAlt := fun hA => altNeed1_avoids_belowDualChain h0 h1 hSSub hA hBelow
    rcases hLeaf with ⟨i, hi⟩ | ⟨c0, hc0, hEqc⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨i, ?_, hi.symm⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hiAlt =>
        hNotAlt (hi ▸ (Finset.mem_filter.mp hiAlt).2)⟩
    · apply Finset.mem_union_right
      obtain ⟨hf,ht⟩ := dualSteps_endpoint_values h0 h1 hds
      rw [hEqc] at hf ht
      exact Finset.mem_image.mpr ⟨c0, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc0,hf⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc0,ht⟩⟩, hEqc.symm⟩
  have hInj : Set.InjOn zFun sHit := by
    intro t1 ht1 t2 ht2 hEq
    have hEq' : zOf t1 ht1 = zOf t2 ht2 := by
      rwa [hzFun ht1, hzFun ht2] at hEq
    obtain ⟨hds1, _⟩ := hDZ t1 ht1
    obtain ⟨hds2, _⟩ := hDZ t2 ht2
    rw [← hEq'] at hds2
    rcases lt_trichotomy (dOf t1 ht1) (dOf t2 ht2) with hlt | heq | hgt
    · have hB := belowDualChain_mono (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp ht2).1)
        (dualSteps_below_of_lt h0 h1 _ _ t1 t2 hlt hds1 hds2)
      exact False.elim (altNeed1_avoids_belowDualChain h0 h1 hSSub (Finset.mem_filter.mp ht1).2 hB)
    · exact dualSteps_unique h0 h1 (dOf t1 ht1) hds1 (heq ▸ hds2)
    · have hB := belowDualChain_mono (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp ht1).1)
        (dualSteps_below_of_lt h0 h1 _ _ t2 t1 hgt hds2 hds1)
      exact False.elim (altNeed1_avoids_belowDualChain h0 h1 hSSub (Finset.mem_filter.mp ht2).2 hB)
  have hCardLe := Finset.card_le_card_of_injOn zFun hMaps hInj
  have hTargLe : targ.card ≤ dropped.card + cutSet.card :=
    (Finset.card_union_le ..).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  have hDropLe := card_altNeed1_compl_le_of_sparse c hc hSparse hf0 hf1 S hS
  dsimp only [sHit, cutSet, dropped, p, root] at hCardLe hTargLe ⊢
  omega

theorem card_sHit1_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    let p := c.program
    let root := c.outputs 0
    let S := segTopOR p root \ PureH0Bad p root
    (S.filter fun t => AltNeed1 p root S (.gate t)).card ≤ B + 113 * slack p root := by
  intro p root _
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  exact (card_sHit1_le_dualCutNodes c hc hSparse hf0 hf1).trans (add_le_add le_rfl
    ((Finset.card_le_card (dualCutNodes_subset p root)).trans (card_cutNode_le_slack p root h0 h1)))

private theorem card_sHit0_le_dualCutNodes {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    let p := c.program
    let root := c.outputs 0
    let S := segTopAND p root \ PureH1Bad p root
    (S.filter fun t => AltNeed0 p root S (.gate t)).card ≤
      B + (dualCutNodes p root).card := by
  classical
  intro p root S
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let sHit := S.filter fun t => AltNeed0 p root S (.gate t)
  have hS : ∀ t ∈ S, t ∈ goodDual p root ∧ (p.lines t).op = .and := by
    intro t ht
    have htG := segTopAND_goodDual (Finset.mem_sdiff.mp ht).1
    exact ⟨htG.1, htG.2.1.1⟩
  have hSSub : ∀ t ∈ S, t ∈ segTopAND p root := fun t ht => (Finset.mem_sdiff.mp ht).1
  have hEx : ∀ t ∈ sHit, ∃ d z, DualSteps p root d t z ∧
      ((∃ i, z = .input i) ∨ ∃ c0, CutNode p root c0 ∧ z = .gate c0) := by
    intro t ht
    have htG := segTopAND_goodDual ((Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).1)
    exact exists_dualSteps_leaf h0 h1 t.val t le_rfl htG.1 htG.2.2.1
  choose dOf zOf hDZ using fun t (ht : t ∈ sHit) => hEx t ht
  let zFun (t : Fin c.size) : Wire n c.size := if ht : t ∈ sHit then zOf t ht else root
  have hzFun {t} (ht : t ∈ sHit) : zFun t = zOf t ht := by
    simp only [zFun]
    split_ifs
    rfl
  let cutSet := dualCutNodes p root
  let dropped := Finset.univ \ altNeed0_inputs p root S
  let targ := dropped.image Wire.input ∪ cutSet.image Wire.gate
  have hMaps : ∀ t ∈ sHit, zFun t ∈ targ := by
    intro t ht
    rw [hzFun ht]
    obtain ⟨hds, hLeaf⟩ := hDZ t ht
    have hBelow := dualSteps_to_belowDualChain (Finset.mem_filter.mp ht).1 hds
    have hNotAlt := fun hA => altNeed0_avoids_belowDualChain h0 h1 hSSub hA hBelow
    rcases hLeaf with ⟨i, hi⟩ | ⟨c0, hc0, hEqc⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨i, ?_, hi.symm⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hiAlt =>
        hNotAlt (hi ▸ (Finset.mem_filter.mp hiAlt).2)⟩
    · apply Finset.mem_union_right
      obtain ⟨hf,ht⟩ := dualSteps_endpoint_values h0 h1 hds
      rw [hEqc] at hf ht
      exact Finset.mem_image.mpr ⟨c0, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc0,hf⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc0,ht⟩⟩, hEqc.symm⟩
  have hInj : Set.InjOn zFun sHit := by
    intro t1 ht1 t2 ht2 hEq
    have hEq' : zOf t1 ht1 = zOf t2 ht2 := by
      rwa [hzFun ht1, hzFun ht2] at hEq
    obtain ⟨hds1, _⟩ := hDZ t1 ht1
    obtain ⟨hds2, _⟩ := hDZ t2 ht2
    rw [← hEq'] at hds2
    rcases lt_trichotomy (dOf t1 ht1) (dOf t2 ht2) with hlt | heq | hgt
    · have hB := belowDualChain_mono (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp ht2).1)
        (dualSteps_below_of_lt h0 h1 _ _ t1 t2 hlt hds1 hds2)
      exact False.elim (altNeed0_avoids_belowDualChain h0 h1 hSSub (Finset.mem_filter.mp ht1).2 hB)
    · exact dualSteps_unique h0 h1 (dOf t1 ht1) hds1 (heq ▸ hds2)
    · have hB := belowDualChain_mono (Finset.singleton_subset_iff.mpr (Finset.mem_filter.mp ht1).1)
        (dualSteps_below_of_lt h0 h1 _ _ t2 t1 hgt hds2 hds1)
      exact False.elim (altNeed0_avoids_belowDualChain h0 h1 hSSub (Finset.mem_filter.mp ht2).2 hB)
  have hCardLe := Finset.card_le_card_of_injOn zFun hMaps hInj
  have hTargLe : targ.card ≤ dropped.card + cutSet.card :=
    (Finset.card_union_le ..).trans (add_le_add Finset.card_image_le Finset.card_image_le)
  have hDropLe := card_altNeed0_compl_le_of_sparse c hc hSparse hf0 hf1 S hS
  dsimp only [sHit, cutSet, dropped, p, root] at hCardLe hTargLe ⊢
  omega

theorem card_sHit0_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    let p := c.program
    let root := c.outputs 0
    let S := segTopAND p root \ PureH1Bad p root
    (S.filter fun t => AltNeed0 p root S (.gate t)).card ≤ B + 113 * slack p root := by
  intro p root _
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  exact (card_sHit0_le_dualCutNodes c hc hSparse hf0 hf1).trans (add_le_add le_rfl
    ((Finset.card_le_card (dualCutNodes_subset p root)).trans (card_cutNode_le_slack p root h0 h1)))

/-! ### Part 2: `Dropped1`/`0`, leaf bounds, `segTopOR`/`segTopAND`, and monotone OR/AND forest -/

private theorem selectedPins_false_child_true (op : Op)
    (v : Fin (signature.Arity op) → Bool) (a : Fin (signature.Arity op))
    (ha : a ∈ selectedPins op v) (hEval : interpretation op v = false) (hVa : v a = true) :
    op = .not := by
  cases op with
  | const _ => simp [selectedPins] at ha
  | not => rfl
  | and =>
    fin_cases a <;>
      cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]
  | or =>
    fin_cases a <;>
      cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]

private theorem selectedPins_true_child_false (op : Op)
    (v : Fin (signature.Arity op) → Bool) (a : Fin (signature.Arity op))
    (ha : a ∈ selectedPins op v) (hEval : interpretation op v = true) (hVa : v a = false) :
    op = .not := by
  cases op with
  | const _ => simp [selectedPins] at ha
  | not => rfl
  | and =>
    fin_cases a <;>
      cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]
  | or =>
    fin_cases a <;>
      cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]

private theorem det_refTrans_total {α : Type*} (R : α → α → Prop)
    (hDet : ∀ {u v1 v2}, R u v1 → R u v2 → v1 = v2)
    {s w1 w2 : α} (h1 : Relation.ReflTransGen R s w1) (h2 : Relation.ReflTransGen R s w2) :
    Relation.ReflTransGen R w1 w2 ∨ Relation.ReflTransGen R w2 w1 := by
  induction h1 using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl h2
  | @head a b hStep hTail ih =>
    rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨c, hStep2, hTail2⟩
    · exact Or.inr (Relation.ReflTransGen.head hStep hTail)
    · have hEq : b = c := hDet hStep hStep2
      subst hEq
      exact ih hTail2

private theorem exists_segTopOR_of_goodDual {p : Program signature n g} {root : Wire n g} :
    ∀ d : ℕ, ∀ k : Fin g, g - k.val ≤ d →
      k ∈ goodDual p root → (p.lines k).op = .or → ¬ CutNode p root k →
      ∃ t ∈ segTopOR p root, SegAnc p root t k := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk hkG hOp hkC
    by_cases hPar : ∃ u, segEdge p root u k
    · obtain ⟨u, huk⟩ := hPar
      have huNb := (not_s0_s1_of_not_badFlip
        (not_badFlip_of_not_otherBad (goodDual_iff.mp huk.1).2)).1
      have hPre := dualChild_precedes (p := p) (k := u) (not_bad_structure p root huNb).1
      rw [huk.2.2.2.2.2] at hPre
      have hLt : k.val < u.val := Nat.succ_lt_succ_iff.mp hPre
      have hGu : u.val < g := u.isLt
      obtain ⟨t, htMem, htAnc⟩ := ih (g - u.val) (by omega) u (le_rfl)
        huk.1 (huk.2.2.2.2.1.trans hOp) huk.2.2.1
      exact ⟨t, htMem, Relation.ReflTransGen.tail htAnc huk⟩
    · refine ⟨k, Finset.mem_filter.mpr ⟨hkG, hOp, hkC, hPar⟩, Relation.ReflTransGen.refl⟩

private theorem exists_segTopAND_of_goodDual {p : Program signature n g} {root : Wire n g} :
    ∀ d : ℕ, ∀ k : Fin g, g - k.val ≤ d →
      k ∈ goodDual p root → (p.lines k).op = .and → ¬ CutNode p root k →
      ∃ t ∈ segTopAND p root, SegAnc p root t k := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk hkG hOp hkC
    by_cases hPar : ∃ u, segEdge p root u k
    · obtain ⟨u, huk⟩ := hPar
      have huNb := (not_s0_s1_of_not_badFlip
        (not_badFlip_of_not_otherBad (goodDual_iff.mp huk.1).2)).1
      have hPre := dualChild_precedes (p := p) (k := u) (not_bad_structure p root huNb).1
      rw [huk.2.2.2.2.2] at hPre
      have hLt : k.val < u.val := Nat.succ_lt_succ_iff.mp hPre
      have hGu : u.val < g := u.isLt
      obtain ⟨t, htMem, htAnc⟩ := ih (g - u.val) (by omega) u (le_rfl)
        huk.1 (huk.2.2.2.2.1.trans hOp) huk.2.2.1
      exact ⟨t, htMem, Relation.ReflTransGen.tail htAnc huk⟩
    · refine ⟨k, Finset.mem_filter.mpr ⟨hkG, hOp, hkC, hPar⟩, Relation.ReflTransGen.refl⟩

private theorem segAnc_dualChild_input_eq {p : Program signature n g} {root : Wire n g}
    (_h0 : cornerValue p false root = true) (_h1 : cornerValue p true root = true) :
    ∀ m : ℕ, ∀ u k1 k2 : Fin g, ∀ i1 i2 : Fin n, u.val ≤ m →
      SegAnc p root u k1 → SegAnc p root u k2 →
      dualChild p k1 = .input i1 → dualChild p k2 = .input i2 → k1 = k2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro u k1 k2 i1 i2 hu h1A h2A hd1 hd2
    rcases Relation.ReflTransGen.cases_head h1A with rfl | ⟨v1, huv1, hv1⟩ <;>
      rcases Relation.ReflTransGen.cases_head h2A with heq2 | ⟨v2, huv2, hv2⟩
    · exact heq2
    · rw [huv2.2.2.2.2.2] at hd1; cases hd1
    · rw [← heq2, huv1.2.2.2.2.2] at hd2; cases hd2
    · have hvEq : v1 = v2 := by
        have := huv1.2.2.2.2.2.symm.trans huv2.2.2.2.2.2
        cases this
        rfl
      subst hvEq
      have huNb := (not_s0_s1_of_not_badFlip
        (not_badFlip_of_not_otherBad (goodDual_iff.mp huv1.1).2)).1
      have hPre := dualChild_precedes (p := p) (k := u) (not_bad_structure p root huNb).1
      rw [huv1.2.2.2.2.2] at hPre
      have hLt : v1.val < u.val := Nat.succ_lt_succ_iff.mp hPre
      exact ih v1.val (by omega) v1 k1 k2 i1 i2 le_rfl hv1 hv2 hd1 hd2

/-! #### Clean 1-corner leaves and `segTopOR` bound -/

noncomputable def Dropped1 (p : Program signature n g) (root : Wire n g) : Finset (Fin n) :=
  Finset.univ \ altNeed1_inputs p root (segTopOR p root \ PureH0Bad p root)

noncomputable def Dropped0 (p : Program signature n g) (root : Wire n g) : Finset (Fin n) :=
  Finset.univ \ altNeed0_inputs p root (segTopAND p root \ PureH1Bad p root)

def CleanNode1 (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  NeedCorner p root true (.gate k, true) ∧
  ¬ AltNeed1 p root (segTopOR p root \ PureH0Bad p root) (.gate k) ∧
  ¬ CutNode p root k

def CleanNode0 (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  NeedCorner p root false (.gate k, false) ∧
  ¬ AltNeed0 p root (segTopAND p root \ PureH1Bad p root) (.gate k) ∧
  ¬ CutNode p root k

private noncomputable def cleanChild1 (p : Program signature n g) (root : Wire n g) (k : Fin g) :
    Finset (Wire n g) :=
  (reqCorner p root true k).image Prod.fst

private noncomputable def cleanChild0 (p : Program signature n g) (root : Wire n g) (k : Fin g) :
    Finset (Wire n g) :=
  (reqCorner p root false k).image Prod.fst

private def PureStep1 (p : Program signature n g) (root : Wire n g) (u v : Wire n g) : Prop :=
  let S := segTopOR p root \ PureH0Bad p root
  ∃ j : Fin g, u = .gate j ∧ AltNeed1 p root S (.gate j) ∧
    ¬ NeedCorner p root true (.gate j, cornerValue p true (.gate j)) ∧
    cornerValue p true (.gate j) = true ∧ (p.lines j).op = .or ∧ j ∉ S ∧
    ∃ a ∈ selectedPins (p.lines j).op (fun s => cornerValue p true ((p.lines j).wires s)),
      (p.lines j).wires a = v

private def PureReach1 (p : Program signature n g) (root : Wire n g) (u v : Wire n g) : Prop :=
  Relation.ReflTransGen (PureStep1 p root) u v

private def PureStep0 (p : Program signature n g) (root : Wire n g) (u v : Wire n g) : Prop :=
  let S := segTopAND p root \ PureH1Bad p root
  ∃ j : Fin g, u = .gate j ∧ AltNeed0 p root S (.gate j) ∧
    ¬ NeedCorner p root false (.gate j, cornerValue p false (.gate j)) ∧
    cornerValue p false (.gate j) = false ∧ (p.lines j).op = .and ∧ j ∉ S ∧
    ∃ a ∈ selectedPins (p.lines j).op (fun s => cornerValue p false ((p.lines j).wires s)),
      (p.lines j).wires a = v

private def PureReach0 (p : Program signature n g) (root : Wire n g) (u v : Wire n g) : Prop :=
  Relation.ReflTransGen (PureStep0 p root) u v

private noncomputable def altEntry1 (p : Program signature n g) (root : Wire n g) : Finset (Wire n g) :=
  let S := segTopOR p root \ PureH0Bad p root
  Finset.univ.filter fun w =>
    AltNeed1 p root S w ∧
      ∃ k : Fin g, ¬ CutNode p root k ∧ ¬ AltNeed1 p root S (.gate k) ∧
        (w, true) ∈ reqCorner p root true k

private noncomputable def altEntry0 (p : Program signature n g) (root : Wire n g) : Finset (Wire n g) :=
  let S := segTopAND p root \ PureH1Bad p root
  Finset.univ.filter fun w =>
    AltNeed0 p root S w ∧
      ∃ k : Fin g, ¬ CutNode p root k ∧ ¬ AltNeed0 p root S (.gate k) ∧
        (w, false) ∈ reqCorner p root false k

private noncomputable def subtreeLeaves1 (p : Program signature n g) (root : Wire n g) :
    Finset (Wire n g) :=
  (Dropped1 p root).image Wire.input ∪
    (cornerCutNodes p root true).image Wire.gate ∪
    altEntry1 p root

private noncomputable def subtreeLeaves0 (p : Program signature n g) (root : Wire n g) :
    Finset (Wire n g) :=
  (Dropped0 p root).image Wire.input ∪
    (cornerCutNodes p root false).image Wire.gate ∪
    altEntry0 p root

private theorem selectedPins_card_le_one_of_op (op : Op) (v : Fin (signature.Arity op) → Bool)
    (h : (op = .and ∧ interpretation op v = false) ∨ (op = .or ∧ interpretation op v = true)) :
    (selectedPins op v).card ≤ 1 := by
  refine op_selectedPins_card_le_one op v ?_
  rcases h with ⟨rfl, hf⟩ | ⟨rfl, ht⟩
  · simp [hf]
  · simp [ht]

private theorem pureStep1_det {p : Program signature n g} {root u v1 v2 : Wire n g}
    (h1 : PureStep1 p root u v1) (h2 : PureStep1 p root u v2) : v1 = v2 := by
  rcases h1 with ⟨j1, hEq1, _, _, hVal1, hOp1, _, a1, ha1, rfl⟩
  rcases h2 with ⟨j2, hEq2, _, _, _, _, _, a2, ha2, rfl⟩
  have hj : j1 = j2 := by cases hEq1.symm.trans hEq2; rfl
  subst hj
  have hCard : (selectedPins (p.lines j1).op
      (fun s => cornerValue p true ((p.lines j1).wires s))).card ≤ 1 := by
    have hEval : interpretation (p.lines j1).op
        (fun s => cornerValue p true ((p.lines j1).wires s)) = true := by
      simpa [cornerValue_gate] using hVal1
    exact selectedPins_card_le_one_of_op (p.lines j1).op _ (Or.inr ⟨hOp1, hEval⟩)
  have haEq : a1 = a2 := Finset.card_le_one.mp hCard a1 ha1 a2 ha2
  rw [haEq]

private theorem pureStep0_det {p : Program signature n g} {root u v1 v2 : Wire n g}
    (h1 : PureStep0 p root u v1) (h2 : PureStep0 p root u v2) : v1 = v2 := by
  rcases h1 with ⟨j1, hEq1, _, _, hVal1, hOp1, _, a1, ha1, rfl⟩
  rcases h2 with ⟨j2, hEq2, _, _, _, _, _, a2, ha2, rfl⟩
  have hj : j1 = j2 := by cases hEq1.symm.trans hEq2; rfl
  subst hj
  have hCard : (selectedPins (p.lines j1).op
      (fun s => cornerValue p false ((p.lines j1).wires s))).card ≤ 1 := by
    have hEval : interpretation (p.lines j1).op
        (fun s => cornerValue p false ((p.lines j1).wires s)) = false := by
      simpa [cornerValue_gate] using hVal1
    exact selectedPins_card_le_one_of_op (p.lines j1).op _ (Or.inl ⟨hOp1, hEval⟩)
  have haEq : a1 = a2 := Finset.card_le_one.mp hCard a1 ha1 a2 ha2
  rw [haEq]

private theorem altNeed1_pureReach {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {u : Wire n g}
    (hu : AltNeed1 p root (segTopOR p root \ PureH0Bad p root) u) :
    ¬ NeedCorner p root true (u, cornerValue p true u) →
      ∃ r ∈ (segTopOR p root \ PureH0Bad p root).filter
          (fun t => AltNeed1 p root (segTopOR p root \ PureH0Bad p root) (.gate t)),
        PureReach1 p root (sideChild p r) u ∧ cornerValue p true u = true := by
  let S := segTopOR p root \ PureH0Bad p root
  let sHit := S.filter fun t => AltNeed1 p root S (.gate t)
  induction hu with
  | output =>
    intro hNotN
    exact (hNotN (h1.symm ▸ NeedCorner.output)).elim
  | @branchS r hr hrS =>
    intro _
    have hrG := segTopOR_goodDual (Finset.mem_sdiff.mp hrS).1
    exact ⟨r, Finset.mem_filter.mpr ⟨hrS, hr⟩, Relation.ReflTransGen.refl,
      ((goodDual_sideChild_val h0 h1 hrG.1).1 hrG.2.1).2⟩
  | @branchRest j hj hjS a ha ih =>
    intro hNotNu
    have hNotNj : ¬ NeedCorner p root true (.gate j, cornerValue p true (.gate j)) := by
      intro hjN
      exact hNotNu (needCorner_child_of_reqCorner (corner_arg_mem_reqCorner hjN ha))
    obtain ⟨r, hrMem, hReach, hValj⟩ := ih hNotNj
    have hNotReach : ¬ ReachesCut1 p root (.gate j) := h1_disjoint_cutGate h1 hj hNotNj
    have hjNotCut : j ∉ CutGate p root := fun hjC => hNotReach (ReachesCut1.hit hjC)
    have hbf := not_badFlip_of_not_cutGate hjNotCut
    have hjPure : IsPureOR0 p root j := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exact (hNotNj ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)).elim
      · exact (hNotNj ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)).elim
      · exact (hNotNj ((needCorner_eq_cornerValue h1 hPA.2.2).symm ▸ hPA.2.2)).elim
      · exact hPO
    have hEval : interpretation (p.lines j).op
        (fun s => cornerValue p true ((p.lines j).wires s)) = true := by
      simpa [cornerValue_gate] using hValj
    have hValChild : cornerValue p true ((p.lines j).wires a) = true := by
      by_contra hFalse
      have hF := Bool.eq_false_iff.mpr hFalse
      have hNot := selectedPins_true_child_false (p.lines j).op
        (fun s => cornerValue p true ((p.lines j).wires s)) a ha hEval hF
      rw [hjPure.1] at hNot; cases hNot
    have hStep : PureStep1 p root (.gate j) ((p.lines j).wires a) :=
      ⟨j, rfl, hj, hNotNj, hValj, hjPure.1, hjS, a, ha, rfl⟩
    exact ⟨r, hrMem, Relation.ReflTransGen.tail hReach hStep, hValChild⟩

private theorem altNeed0_pureReach {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {u : Wire n g}
    (hu : AltNeed0 p root (segTopAND p root \ PureH1Bad p root) u) :
    ¬ NeedCorner p root false (u, cornerValue p false u) →
      ∃ r ∈ (segTopAND p root \ PureH1Bad p root).filter
          (fun t => AltNeed0 p root (segTopAND p root \ PureH1Bad p root) (.gate t)),
        PureReach0 p root (sideChild p r) u ∧ cornerValue p false u = false := by
  let S := segTopAND p root \ PureH1Bad p root
  induction hu with
  | output =>
    intro hNotN
    exact (hNotN (h0.symm ▸ NeedCorner.output)).elim
  | @branchS r hr hrS =>
    intro _
    have hrG := segTopAND_goodDual (Finset.mem_sdiff.mp hrS).1
    exact ⟨r, Finset.mem_filter.mpr ⟨hrS, hr⟩, Relation.ReflTransGen.refl,
      ((goodDual_sideChild_val h0 h1 hrG.1).2 hrG.2.1).1⟩
  | @branchRest j hj hjS a ha ih =>
    intro hNotNu
    have hNotNj : ¬ NeedCorner p root false (.gate j, cornerValue p false (.gate j)) := by
      intro hjN
      exact hNotNu (needCorner_child_of_reqCorner (corner_arg_mem_reqCorner hjN ha))
    obtain ⟨r, hrMem, hReach, hValj⟩ := ih hNotNj
    have hNotReach : ¬ ReachesCut0 p root (.gate j) := h0_disjoint_cutGate h0 hj hNotNj
    have hjNotCut : j ∉ CutGate p root := fun hjC => hNotReach (ReachesCut0.hit hjC)
    have hbf := not_badFlip_of_not_cutGate hjNotCut
    have hjPure : IsPureAND1 p root j := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exact (hNotNj ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)).elim
      · exact (hNotNj ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)).elim
      · exact hPA
      · exact (hNotNj ((needCorner_eq_cornerValue h0 hPO.2.1).symm ▸ hPO.2.1)).elim
    have hEval : interpretation (p.lines j).op
        (fun s => cornerValue p false ((p.lines j).wires s)) = false := by
      simpa [cornerValue_gate] using hValj
    have hValChild : cornerValue p false ((p.lines j).wires a) = false := by
      by_contra hTrue
      have hT := Bool.eq_true_of_not_eq_false hTrue
      have hNot := selectedPins_false_child_true (p.lines j).op
        (fun s => cornerValue p false ((p.lines j).wires s)) a ha hEval hT
      rw [hjPure.1] at hNot; cases hNot
    have hStep : PureStep0 p root (.gate j) ((p.lines j).wires a) :=
      ⟨j, rfl, hj, hNotNj, hValj, hjPure.1, hjS, a, ha, rfl⟩
    exact ⟨r, hrMem, Relation.ReflTransGen.tail hReach hStep, hValChild⟩

private theorem card_altEntry1_le_sHit {f : BooleanFunction n}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    let p := c.program
    let root := c.outputs 0
    let S := segTopOR p root \ PureH0Bad p root
    let sHit := S.filter fun t => AltNeed1 p root S (.gate t)
    (altEntry1 p root).card ≤ sHit.card + (badNot p root).card := by
  classical
  intro p root S sHit
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let badNotWires : Finset (Wire n c.size) :=
    (badNot p root).biUnion fun k => Finset.univ.image (p.lines k).wires
  let fromPure := (altEntry1 p root).filter fun w =>
    ∃ r ∈ sHit, PureReach1 p root (sideChild p r) w
  have hSub : altEntry1 p root ⊆ fromPure ∪ badNotWires := by
    intro w hw
    obtain ⟨hwAlt, k, hkNotC, hkNotAlt, hkReq⟩ := (Finset.mem_filter.mp hw).2
    have hwN : NeedCorner p root true (w, true) := needCorner_child_of_reqCorner hkReq
    have hwVal : cornerValue p true w = true := (needCorner_eq_cornerValue h1 hwN).symm
    cases hwAlt with
    | output =>
      exact (root_notMem_allArgs p root
        (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, reqCorner_subset_req_right hkReq⟩)).elim
    | @branchS r hr hrS =>
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hw, r, Finset.mem_filter.mpr ⟨hrS, hr⟩, Relation.ReflTransGen.refl⟩
    | @branchRest k1 hk1 hk1S a ha =>
      by_cases hNk1 : NeedCorner p root true (.gate k1, cornerValue p true (.gate k1))
      · by_cases hVk1 : cornerValue p true (.gate k1) = true
        · have hk1Req : ((p.lines k1).wires a, true) ∈ reqCorner p root true k1 := by
            simpa [hVk1, hwVal] using corner_arg_mem_reqCorner hNk1 ha
          have hkEq : k = k1 := req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hkNotC))
            (reqCorner_subset_req_right hkReq) (reqCorner_subset_req_right hk1Req)
          exact (hkNotAlt (hkEq ▸ hk1)).elim
        · have hFk1 : cornerValue p true (.gate k1) = false := Bool.eq_false_iff.mpr hVk1
          have hEval : interpretation (p.lines k1).op
              (fun s => cornerValue p true ((p.lines k1).wires s)) = false := by
            simpa [cornerValue_gate] using hFk1
          have hOpNot := selectedPins_false_child_true (p.lines k1).op
            (fun s => cornerValue p true ((p.lines k1).wires s)) a ha hEval hwVal
          have hk1Bad : k1 ∈ badGates p root := by
            by_contra hnb
            rcases (not_bad_structure p root hnb).1 with hOp | hOp <;> (rw [hOpNot] at hOp; cases hOp)
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨k1, Finset.mem_filter.mpr ⟨hk1Bad, hOpNot⟩,
            Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
      · obtain ⟨r, hrMem, hReach, _⟩ := altNeed1_pureReach h0 h1 hk1 hNk1
        have hEval : interpretation (p.lines k1).op
            (fun s => cornerValue p true ((p.lines k1).wires s)) = true := by
          have hNotReach := h1_disjoint_cutGate h1 hk1 hNk1
          have hk1NotCut : k1 ∉ CutGate p root := fun hkC => hNotReach (ReachesCut1.hit hkC)
          have hbf := not_badFlip_of_not_cutGate hk1NotCut
          have hjPure : IsPureOR0 p root k1 := by
            rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
            · exact (hNk1 ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)).elim
            · exact (hNk1 ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)).elim
            · exact (hNk1 ((needCorner_eq_cornerValue h1 hPA.2.2).symm ▸ hPA.2.2)).elim
            · exact hPO
          by_contra hF
          have hF' := Bool.eq_false_iff.mpr hF
          have hOpNot := selectedPins_false_child_true (p.lines k1).op _ a ha hF' hwVal
          rw [hjPure.1] at hOpNot; cases hOpNot
        have hVk1T : cornerValue p true (.gate k1) = true := by
          rw [cornerValue_gate]; exact hEval
        have hNotReach := h1_disjoint_cutGate h1 hk1 hNk1
        have hk1NotCut : k1 ∉ CutGate p root := fun hkC => hNotReach (ReachesCut1.hit hkC)
        have hbf := not_badFlip_of_not_cutGate hk1NotCut
        have hjPure : IsPureOR0 p root k1 := by
          rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
          · exact (hNk1 ((needCorner_eq_cornerValue h1 hDA.2.2).symm ▸ hDA.2.2)).elim
          · exact (hNk1 ((needCorner_eq_cornerValue h1 hDO.2.2).symm ▸ hDO.2.2)).elim
          · exact (hNk1 ((needCorner_eq_cornerValue h1 hPA.2.2).symm ▸ hPA.2.2)).elim
          · exact hPO
        have hStep : PureStep1 p root (.gate k1) ((p.lines k1).wires a) :=
          ⟨k1, rfl, hk1, hNk1, hVk1T, hjPure.1, hk1S, a, ha, rfl⟩
        apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨hw, r, hrMem, Relation.ReflTransGen.tail hReach hStep⟩
  have hExPure : ∀ w ∈ fromPure, ∃ r ∈ sHit, PureReach1 p root (sideChild p r) w :=
    fun _ hw => (Finset.mem_filter.mp hw).2
  choose rOf hrProp using fun w (hw : w ∈ fromPure) => hExPure w hw
  have hFromPureLe : fromPure.card ≤ sHit.card := by
    by_cases hEmpty : fromPure = ∅
    · simp [hEmpty]
    · obtain ⟨w0, hw0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let rDef : Fin c.size := rOf w0 hw0
      let rFun (w : Wire n c.size) : Fin c.size := if hw : w ∈ fromPure then rOf w hw else rDef
      have hrFun {w} (hw : w ∈ fromPure) : rFun w = rOf w hw := by
        simp only [rFun]; split_ifs; rfl
      refine Finset.card_le_card_of_injOn rFun
        (fun w hw => by rw [hrFun hw]; exact (hrProp w hw).1) ?_
      intro w1 hw1 w2 hw2 hEq
      have hEq' : rOf w1 hw1 = rOf w2 hw2 := by rwa [hrFun hw1, hrFun hw2] at hEq
      have hR1 := (hrProp w1 hw1).2
      have hR2 := (hrProp w2 hw2).2
      rw [← hEq'] at hR2
      have hN1 : NeedCorner p root true (w1, cornerValue p true w1) := by
        obtain ⟨k1, _, _, _, hkReq1⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw1).1).2
        have hNW1 := needCorner_child_of_reqCorner hkReq1
        rwa [← needCorner_eq_cornerValue h1 hNW1]
      have hN2 : NeedCorner p root true (w2, cornerValue p true w2) := by
        obtain ⟨k2, _, _, _, hkReq2⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw2).1).2
        have hNW2 := needCorner_child_of_reqCorner hkReq2
        rwa [← needCorner_eq_cornerValue h1 hNW2]
      have hNoOut : ∀ {u v}, NeedCorner p root true (u, cornerValue p true u) →
          ¬ PureStep1 p root u v := by
        intro u v hNu hStep
        rcases hStep with ⟨j, rfl, _, hNotN, _, _, _, _, _, _⟩
        exact hNotN hNu
      rcases det_refTrans_total (PureStep1 p root) pureStep1_det hR1 hR2 with h12 | h21
      · rcases Relation.ReflTransGen.cases_head h12 with rfl | ⟨v, hStep, _⟩
        · rfl
        · exact (hNoOut hN1 hStep).elim
      · rcases Relation.ReflTransGen.cases_head h21 with hEqW | ⟨v, hStep, _⟩
        · exact hEqW.symm
        · exact (hNoOut hN2 hStep).elim
  have hBadNotLe : badNotWires.card ≤ (badNot p root).card := by
    calc
      badNotWires.card ≤ ∑ k ∈ badNot p root, (Finset.univ.image (p.lines k).wires).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ badNot p root, 1 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hOp : (p.lines k).op = .not := (Finset.mem_filter.mp hk).2
        refine Finset.card_image_le.trans ?_
        simp [hOp]
      _ = (badNot p root).card := by simp
  have hSubLe := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  dsimp only [p, root, S, sHit] at hSubLe hFromPureLe hBadNotLe ⊢
  omega

private theorem card_altEntry1_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (altEntry1 c.program (c.outputs 0)).card ≤ B + 114 * slack c.program (c.outputs 0) := by
  have hAE := card_altEntry1_le_sHit c hc hf0 hf1
  have hSHit := card_sHit1_le c hc hSparse hf0 hf1
  have hBadNot : (badNot c.program (c.outputs 0)).card ≤ (badGates c.program (c.outputs 0)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hBG := card_badGates_le_slack c.program (c.outputs 0)
  dsimp only at hAE hSHit
  omega

private theorem card_altEntry0_le_sHit {f : BooleanFunction n}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    let p := c.program
    let root := c.outputs 0
    let S := segTopAND p root \ PureH1Bad p root
    let sHit := S.filter fun t => AltNeed0 p root S (.gate t)
    (altEntry0 p root).card ≤ sHit.card + (badNot p root).card := by
  classical
  intro p root S sHit
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let badNotWires : Finset (Wire n c.size) :=
    (badNot p root).biUnion fun k => Finset.univ.image (p.lines k).wires
  let fromPure := (altEntry0 p root).filter fun w =>
    ∃ r ∈ sHit, PureReach0 p root (sideChild p r) w
  have hSub : altEntry0 p root ⊆ fromPure ∪ badNotWires := by
    intro w hw
    obtain ⟨hwAlt, k, hkNotC, hkNotAlt, hkReq⟩ := (Finset.mem_filter.mp hw).2
    have hwN : NeedCorner p root false (w, false) := needCorner_child_of_reqCorner hkReq
    have hwVal : cornerValue p false w = false := (needCorner_eq_cornerValue h0 hwN).symm
    cases hwAlt with
    | output =>
      rw [h0] at hwVal
      cases hwVal
    | @branchS r hr hrS =>
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hw, r, Finset.mem_filter.mpr ⟨hrS, hr⟩, Relation.ReflTransGen.refl⟩
    | @branchRest k1 hk1 hk1S a ha =>
      by_cases hNk1 : NeedCorner p root false (.gate k1, cornerValue p false (.gate k1))
      · by_cases hVk1 : cornerValue p false (.gate k1) = false
        · have hk1Req : ((p.lines k1).wires a, false) ∈ reqCorner p root false k1 := by
            simpa [hVk1, hwVal] using corner_arg_mem_reqCorner hNk1 ha
          have hkEq : k = k1 := req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hkNotC))
            (reqCorner_subset_req_left hkReq) (reqCorner_subset_req_left hk1Req)
          exact (hkNotAlt (hkEq ▸ hk1)).elim
        · have hTk1 : cornerValue p false (.gate k1) = true := Bool.eq_true_of_not_eq_false hVk1
          have hEval : interpretation (p.lines k1).op
              (fun s => cornerValue p false ((p.lines k1).wires s)) = true := by
            simpa [cornerValue_gate] using hTk1
          have hOpNot := selectedPins_true_child_false (p.lines k1).op
            (fun s => cornerValue p false ((p.lines k1).wires s)) a ha hEval hwVal
          have hk1Bad : k1 ∈ badGates p root := by
            by_contra hnb
            rcases (not_bad_structure p root hnb).1 with hOp | hOp <;> (rw [hOpNot] at hOp; cases hOp)
          apply Finset.mem_union_right
          exact Finset.mem_biUnion.mpr ⟨k1, Finset.mem_filter.mpr ⟨hk1Bad, hOpNot⟩,
            Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
      · obtain ⟨r, hrMem, hReach, _⟩ := altNeed0_pureReach h0 h1 hk1 hNk1
        have hEval : interpretation (p.lines k1).op
            (fun s => cornerValue p false ((p.lines k1).wires s)) = false := by
          have hNotReach := h0_disjoint_cutGate h0 hk1 hNk1
          have hk1NotCut : k1 ∉ CutGate p root := fun hkC => hNotReach (ReachesCut0.hit hkC)
          have hbf := not_badFlip_of_not_cutGate hk1NotCut
          have hjPure : IsPureAND1 p root k1 := by
            rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
            · exact (hNk1 ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)).elim
            · exact (hNk1 ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)).elim
            · exact hPA
            · exact (hNk1 ((needCorner_eq_cornerValue h0 hPO.2.1).symm ▸ hPO.2.1)).elim
          by_contra hT
          have hT' := Bool.eq_true_of_not_eq_false hT
          have hOpNot := selectedPins_true_child_false (p.lines k1).op _ a ha hT' hwVal
          rw [hjPure.1] at hOpNot; cases hOpNot
        have hVk1F : cornerValue p false (.gate k1) = false := by
          rw [cornerValue_gate]; exact hEval
        have hNotReach := h0_disjoint_cutGate h0 hk1 hNk1
        have hk1NotCut : k1 ∉ CutGate p root := fun hkC => hNotReach (ReachesCut0.hit hkC)
        have hbf := not_badFlip_of_not_cutGate hk1NotCut
        have hjPure : IsPureAND1 p root k1 := by
          rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
          · exact (hNk1 ((needCorner_eq_cornerValue h0 hDA.2.1).symm ▸ hDA.2.1)).elim
          · exact (hNk1 ((needCorner_eq_cornerValue h0 hDO.2.1).symm ▸ hDO.2.1)).elim
          · exact hPA
          · exact (hNk1 ((needCorner_eq_cornerValue h0 hPO.2.1).symm ▸ hPO.2.1)).elim
        have hStep : PureStep0 p root (.gate k1) ((p.lines k1).wires a) :=
          ⟨k1, rfl, hk1, hNk1, hVk1F, hjPure.1, hk1S, a, ha, rfl⟩
        apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨hw, r, hrMem, Relation.ReflTransGen.tail hReach hStep⟩
  have hExPure : ∀ w ∈ fromPure, ∃ r ∈ sHit, PureReach0 p root (sideChild p r) w :=
    fun _ hw => (Finset.mem_filter.mp hw).2
  choose rOf hrProp using fun w (hw : w ∈ fromPure) => hExPure w hw
  have hFromPureLe : fromPure.card ≤ sHit.card := by
    by_cases hEmpty : fromPure = ∅
    · simp [hEmpty]
    · obtain ⟨w0, hw0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let rDef : Fin c.size := rOf w0 hw0
      let rFun (w : Wire n c.size) : Fin c.size := if hw : w ∈ fromPure then rOf w hw else rDef
      have hrFun {w} (hw : w ∈ fromPure) : rFun w = rOf w hw := by
        simp only [rFun]; split_ifs; rfl
      refine Finset.card_le_card_of_injOn rFun
        (fun w hw => by rw [hrFun hw]; exact (hrProp w hw).1) ?_
      intro w1 hw1 w2 hw2 hEq
      have hEq' : rOf w1 hw1 = rOf w2 hw2 := by rwa [hrFun hw1, hrFun hw2] at hEq
      have hR1 := (hrProp w1 hw1).2
      have hR2 := (hrProp w2 hw2).2
      rw [← hEq'] at hR2
      have hN1 : NeedCorner p root false (w1, cornerValue p false w1) := by
        obtain ⟨k1, _, _, _, hkReq1⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw1).1).2
        have hNW1 := needCorner_child_of_reqCorner hkReq1
        rwa [← needCorner_eq_cornerValue h0 hNW1]
      have hN2 : NeedCorner p root false (w2, cornerValue p false w2) := by
        obtain ⟨k2, _, _, _, hkReq2⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw2).1).2
        have hNW2 := needCorner_child_of_reqCorner hkReq2
        rwa [← needCorner_eq_cornerValue h0 hNW2]
      have hNoOut : ∀ {u v}, NeedCorner p root false (u, cornerValue p false u) →
          ¬ PureStep0 p root u v := by
        intro u v hNu hStep
        rcases hStep with ⟨j, rfl, _, hNotN, _, _, _, _, _, _⟩
        exact hNotN hNu
      rcases det_refTrans_total (PureStep0 p root) pureStep0_det hR1 hR2 with h12 | h21
      · rcases Relation.ReflTransGen.cases_head h12 with rfl | ⟨v, hStep, _⟩
        · rfl
        · exact (hNoOut hN1 hStep).elim
      · rcases Relation.ReflTransGen.cases_head h21 with hEqW | ⟨v, hStep, _⟩
        · exact hEqW.symm
        · exact (hNoOut hN2 hStep).elim
  have hBadNotLe : badNotWires.card ≤ (badNot p root).card := by
    calc
      badNotWires.card ≤ ∑ k ∈ badNot p root, (Finset.univ.image (p.lines k).wires).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ badNot p root, 1 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hOp : (p.lines k).op = .not := (Finset.mem_filter.mp hk).2
        refine Finset.card_image_le.trans ?_
        simp [hOp]
      _ = (badNot p root).card := by simp
  have hSubLe := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  dsimp only [p, root, S, sHit] at hSubLe hFromPureLe hBadNotLe ⊢
  omega

private theorem card_altEntry0_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (altEntry0 c.program (c.outputs 0)).card ≤ B + 114 * slack c.program (c.outputs 0) := by
  have hAE := card_altEntry0_le_sHit c hc hf0 hf1
  have hSHit := card_sHit0_le c hc hSparse hf0 hf1
  have hBadNot : (badNot c.program (c.outputs 0)).card ≤ (badGates c.program (c.outputs 0)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hBG := card_badGates_le_slack c.program (c.outputs 0)
  dsimp only at hAE hSHit
  omega

private theorem cleanNode1_props {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : CleanNode1 p root k) :
    (k ∉ badGates p root ∧ k ∉ badFlip p root ∧ ¬ HasRepeat p root k) ∧
      ((p.lines k).op = .and → (cleanChild1 p root k).card = 2) ∧
      ((p.lines k).op = .or → k ∈ goodDual p root ∧
        (cleanChild1 p root k).card = 1 ∧ dualChild p k ∈ cleanChild1 p root k) := by
  have hkNotC := not_cutGate_of_not_cutNode hk.2.2
  have hbf := not_badFlip_of_not_cutGate hkNotC
  have hnb := (not_s0_s1_of_not_badFlip hbf).1
  have hhr := cutGate_not_hasRepeat hkNotC
  refine ⟨⟨hnb, hbf, hhr⟩, ?_, ?_⟩
  · intro hOp
    have hVal : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hk.1).symm
    have hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := hVal.symm ▸ hk.1
    have hEval : interpretation (p.lines k).op
        (fun s => cornerValue p true ((p.lines k).wires s)) = true := by
      simpa [cornerValue_gate] using hVal
    have hEqSet : cleanChild1 p root k = Finset.univ.image (p.lines k).wires := by
      ext w
      simp only [cleanChild1, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨w0, v0⟩, hbReq, rfl⟩
        simp only [reqCorner, hg, ite_true, cornerArguments] at hbReq
        obtain ⟨a, _, hEq⟩ := Finset.mem_image.mp hbReq
        exact ⟨a, congrArg Prod.fst hEq⟩
      · rintro ⟨a, rfl⟩
        have hPin : a ∈ selectedPins (p.lines k).op
            (fun s => cornerValue p true ((p.lines k).wires s)) := by
          have hMem : ∀ (op : Op) (v : Fin (signature.Arity op) → Bool)
              (_ : op = .and) (_ : interpretation op v = true)
              (s : Fin (signature.Arity op)), s ∈ selectedPins op v := by
            intro op v hop hv s
            subst hop
            cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]
          exact hMem _ _ hOp hEval a
        refine ⟨((p.lines k).wires a, cornerValue p true ((p.lines k).wires a)), ?_, rfl⟩
        simp only [reqCorner, hg, ite_true, cornerArguments]
        exact Finset.mem_image.mpr ⟨a, hPin, rfl⟩
    have hInj : Function.Injective (p.lines k).wires := by
      intro a0 a1 hEq
      by_contra hne
      exact (not_bad_structure p root hnb).2.2.2 a0 a1 hne hEq
    rw [hEqSet, Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin, hOp]
  · intro hOp
    have hDOR : IsDualOR p root k := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exfalso; rw [hDA.1] at hOp; cases hOp
      · exact hDO
      · exfalso; rw [hPA.1] at hOp; cases hOp
      · exact (hPO.2.2 hk.1).elim
    have hkG : k ∈ goodDual p root := goodDual_iff.mpr ⟨Or.inr hDOR, cutGate_not_otherBad hkNotC⟩
    have hDualMem : (dualChild p k, true) ∈ reqCorner p root true k :=
      (segEdge_req_dualChild h0 h1 hkG).2
    have hInClean : dualChild p k ∈ cleanChild1 p root k :=
      Finset.mem_image.mpr ⟨(dualChild p k, true), hDualMem, rfl⟩
    have hVal : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hk.1).symm
    have hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := hVal.symm ▸ hk.1
    have hEval : interpretation (p.lines k).op
        (fun s => cornerValue p true ((p.lines k).wires s)) = true := by
      simpa [cornerValue_gate] using hVal
    have hCardLeOne : (cleanChild1 p root k).card ≤ 1 := by
      refine Finset.card_image_le.trans ?_
      simp only [reqCorner, hg, ite_true, cornerArguments]
      refine Finset.card_image_le.trans
        (selectedPins_card_le_one_of_op (p.lines k).op _ (Or.inr ⟨hOp, hEval⟩))
    have hCardPos : 1 ≤ (cleanChild1 p root k).card := Finset.card_pos.mpr ⟨_, hInClean⟩
    exact ⟨hkG, by omega, hInClean⟩

private theorem cleanNode0_props {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : CleanNode0 p root k) :
    (k ∉ badGates p root ∧ k ∉ badFlip p root ∧ ¬ HasRepeat p root k) ∧
      ((p.lines k).op = .or → (cleanChild0 p root k).card = 2) ∧
      ((p.lines k).op = .and → k ∈ goodDual p root ∧
        (cleanChild0 p root k).card = 1 ∧ dualChild p k ∈ cleanChild0 p root k) := by
  have hkNotC := not_cutGate_of_not_cutNode hk.2.2
  have hbf := not_badFlip_of_not_cutGate hkNotC
  have hnb := (not_s0_s1_of_not_badFlip hbf).1
  have hhr := cutGate_not_hasRepeat hkNotC
  refine ⟨⟨hnb, hbf, hhr⟩, ?_, ?_⟩
  · intro hOp
    have hVal : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hk.1).symm
    have hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := hVal.symm ▸ hk.1
    have hEval : interpretation (p.lines k).op
        (fun s => cornerValue p false ((p.lines k).wires s)) = false := by
      simpa [cornerValue_gate] using hVal
    have hEqSet : cleanChild0 p root k = Finset.univ.image (p.lines k).wires := by
      ext w
      simp only [cleanChild0, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨w0, v0⟩, hbReq, rfl⟩
        simp only [reqCorner, hg, ite_true, cornerArguments] at hbReq
        obtain ⟨a, _, hEq⟩ := Finset.mem_image.mp hbReq
        exact ⟨a, congrArg Prod.fst hEq⟩
      · rintro ⟨a, rfl⟩
        have hPin : a ∈ selectedPins (p.lines k).op
            (fun s => cornerValue p false ((p.lines k).wires s)) := by
          have hMem : ∀ (op : Op) (v : Fin (signature.Arity op) → Bool)
              (_ : op = .or) (_ : interpretation op v = false)
              (s : Fin (signature.Arity op)), s ∈ selectedPins op v := by
            intro op v hop hv s
            subst hop
            cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]
          exact hMem _ _ hOp hEval a
        refine ⟨((p.lines k).wires a, cornerValue p false ((p.lines k).wires a)), ?_, rfl⟩
        simp only [reqCorner, hg, ite_true, cornerArguments]
        exact Finset.mem_image.mpr ⟨a, hPin, rfl⟩
    have hInj : Function.Injective (p.lines k).wires := by
      intro a0 a1 hEq
      by_contra hne
      exact (not_bad_structure p root hnb).2.2.2 a0 a1 hne hEq
    rw [hEqSet, Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin, hOp]
  · intro hOp
    have hDA : IsDualAND p root k := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exact hDA
      · exfalso; rw [hDO.1] at hOp; cases hOp
      · exact (hPA.2.1 hk.1).elim
      · exfalso; rw [hPO.1] at hOp; cases hOp
    have hkG : k ∈ goodDual p root := goodDual_iff.mpr ⟨Or.inl hDA, cutGate_not_otherBad hkNotC⟩
    have hDualMem : (dualChild p k, false) ∈ reqCorner p root false k :=
      (segEdge_req_dualChild h0 h1 hkG).1
    have hInClean : dualChild p k ∈ cleanChild0 p root k :=
      Finset.mem_image.mpr ⟨(dualChild p k, false), hDualMem, rfl⟩
    have hVal : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hk.1).symm
    have hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := hVal.symm ▸ hk.1
    have hEval : interpretation (p.lines k).op
        (fun s => cornerValue p false ((p.lines k).wires s)) = false := by
      simpa [cornerValue_gate] using hVal
    have hCardLeOne : (cleanChild0 p root k).card ≤ 1 := by
      refine Finset.card_image_le.trans ?_
      simp only [reqCorner, hg, ite_true, cornerArguments]
      refine Finset.card_image_le.trans
        (selectedPins_card_le_one_of_op (p.lines k).op _ (Or.inl ⟨hOp, hEval⟩))
    have hCardPos : 1 ≤ (cleanChild0 p root k).card := Finset.card_pos.mpr ⟨_, hInClean⟩
    exact ⟨hkG, by omega, hInClean⟩

private theorem cleanNode1_req_true {p : Program signature n g} {root : Wire n g}
    (h1 : cornerValue p true root = true) {k : Fin g} (hk : CleanNode1 p root k)
    {key : Wire n g × Bool} (hKey : key ∈ reqCorner p root true k) : key.2 = true := by
  have hnb := (not_s0_s1_of_not_badFlip
    (not_badFlip_of_not_cutGate (not_cutGate_of_not_cutNode hk.2.2))).1
  have hVal : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hk.1).symm
  have hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := hVal.symm ▸ hk.1
  simp only [reqCorner, hg, ite_true, cornerArguments] at hKey
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hKey
  have hEval : interpretation (p.lines k).op
      (fun s => cornerValue p true ((p.lines k).wires s)) = true := by
    simpa [cornerValue_gate] using hVal
  rcases (not_bad_structure p root hnb).1 with hOp | hOp
  · by_contra hF
    have hF' : cornerValue p true ((p.lines k).wires a) = false := Bool.eq_false_iff.mpr hF
    have hAll : ∀ (op : Op) (v : Fin (signature.Arity op) → Bool)
        (_ : op = .and) (_ : interpretation op v = true)
        (s : Fin (signature.Arity op)), v s = true := by
      intro op v hop hv s; subst hop
      fin_cases s <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [interpretation]
    rw [hAll _ _ hOp hEval a] at hF'; cases hF'
  · by_contra hF
    have hF' : cornerValue p true ((p.lines k).wires a) = false := Bool.eq_false_iff.mpr hF
    have hNot := selectedPins_true_child_false (p.lines k).op _ a ha hEval hF'
    rw [hOp] at hNot; cases hNot

private theorem cleanNode0_req_false {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) {k : Fin g} (hk : CleanNode0 p root k)
    {key : Wire n g × Bool} (hKey : key ∈ reqCorner p root false k) : key.2 = false := by
  have hnb := (not_s0_s1_of_not_badFlip
    (not_badFlip_of_not_cutGate (not_cutGate_of_not_cutNode hk.2.2))).1
  have hVal : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hk.1).symm
  have hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := hVal.symm ▸ hk.1
  simp only [reqCorner, hg, ite_true, cornerArguments] at hKey
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hKey
  have hEval : interpretation (p.lines k).op
      (fun s => cornerValue p false ((p.lines k).wires s)) = false := by
    simpa [cornerValue_gate] using hVal
  rcases (not_bad_structure p root hnb).1 with hOp | hOp
  · by_contra hT
    have hT' : cornerValue p false ((p.lines k).wires a) = true := Bool.eq_true_of_not_eq_false hT
    have hNot := selectedPins_false_child_true (p.lines k).op _ a ha hEval hT'
    rw [hOp] at hNot; cases hNot
  · by_contra hT
    have hT' : cornerValue p false ((p.lines k).wires a) = true := Bool.eq_true_of_not_eq_false hT
    have hAll : ∀ (op : Op) (v : Fin (signature.Arity op) → Bool)
        (_ : op = .or) (_ : interpretation op v = false)
        (s : Fin (signature.Arity op)), v s = false := by
      intro op v hop hv s; subst hop
      fin_cases s <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [interpretation]
    rw [hAll _ _ hOp hEval a] at hT'; cases hT'

private theorem card_segTopOR_exact {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (segTopOR c.program (c.outputs 0)).card ≤
      (PureH0Bad c.program (c.outputs 0)).card + 3 * B +
        2 * (cornerCutNodes c.program (c.outputs 0) true).card +
        (dualCutNodes c.program (c.outputs 0)).card +
        2 * (badNot c.program (c.outputs 0)).card := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let S1 := segTopOR p root \ PureH0Bad p root
  let sHit1 := S1.filter fun t => AltNeed1 p root S1 (.gate t)
  let A1 := Finset.univ.filter fun k : Fin c.size => CleanNode1 p root k ∧ (p.lines k).op = .and
  let O1 := Finset.univ.filter fun k : Fin c.size => CleanNode1 p root k ∧ (p.lines k).op = .or
  let leaves := subtreeLeaves1 p root
  let edges : Finset (Fin c.size × Wire n c.size) :=
    (A1 ∪ O1).biUnion fun k => (cleanChild1 p root k).image fun w => (k, w)
  have hCleanReq : ∀ k w, CleanNode1 p root k → w ∈ cleanChild1 p root k →
      (w, true) ∈ reqCorner p root true k := by
    intro k w hk hw
    obtain ⟨⟨w0, v0⟩, hbReq, hEq⟩ := Finset.mem_image.mp hw
    have hv : v0 = true := cleanNode1_req_true h1 hk hbReq
    dsimp only at hEq
    subst hEq; subst hv
    exact hbReq
  have hDisjAO : Disjoint A1 O1 := by
    rw [Finset.disjoint_left]
    intro k hA hO
    have h1A := (Finset.mem_filter.mp hA).2.2
    have h1O := (Finset.mem_filter.mp hO).2.2
    rw [h1A] at h1O; cases h1O
  have hDisjEdges : ∀ k1 ∈ A1 ∪ O1, ∀ k2 ∈ A1 ∪ O1, k1 ≠ k2 →
      Disjoint ((cleanChild1 p root k1).image fun w => (k1, w))
        ((cleanChild1 p root k2).image fun w => (k2, w)) := by
    intro k1 _ k2 _ hne
    rw [Finset.disjoint_left]
    intro kw h1' h2'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1'
    obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2'
    exact hne (congrArg Prod.fst hEq).symm
  have hEdgesLhs : edges.card = 2 * A1.card + O1.card := by
    dsimp only [edges]
    rw [Finset.card_biUnion (fun k1 hk1 k2 hk2 hne => hDisjEdges k1 hk1 k2 hk2 hne),
      Finset.sum_union hDisjAO]
    have hSumA : ∑ k ∈ A1, ((cleanChild1 p root k).image fun w => (k, w)).card = 2 * A1.card := by
      calc
        _ = ∑ _k ∈ A1, 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
          exact (cleanNode1_props h0 h1 (Finset.mem_filter.mp hk).2.1).2.1
            (Finset.mem_filter.mp hk).2.2
        _ = 2 * A1.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hSumO : ∑ k ∈ O1, ((cleanChild1 p root k).image fun w => (k, w)).card = O1.card := by
      calc
        _ = ∑ _k ∈ O1, 1 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
          exact ((cleanNode1_props h0 h1 (Finset.mem_filter.mp hk).2.1).2.2
            (Finset.mem_filter.mp hk).2.2).2.1
        _ = O1.card := by simp
    rw [hSumA, hSumO]
  have hEdgesInj : Set.InjOn Prod.snd (edges : Set (Fin c.size × Wire n c.size)) := by
    intro kw1 h1' kw2 h2' hEq
    obtain ⟨k1', hk1AO, hM1⟩ := Finset.mem_biUnion.mp h1'
    obtain ⟨w1', hw1C, rfl⟩ := Finset.mem_image.mp hM1
    obtain ⟨k2', hk2AO, hM2⟩ := Finset.mem_biUnion.mp h2'
    obtain ⟨w2', hw2C, rfl⟩ := Finset.mem_image.mp hM2
    dsimp only at hEq
    rcases hEq with rfl
    have hk1Clean : CleanNode1 p root k1' := by
      rcases Finset.mem_union.mp hk1AO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have hk2Clean : CleanNode1 p root k2' := by
      rcases Finset.mem_union.mp hk2AO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have hReq1 := hCleanReq k1' w1' hk1Clean hw1C
    have hReq2 := hCleanReq k2' w1' hk2Clean hw2C
    have hk1Eq := req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hk1Clean.2.2))
      (reqCorner_subset_req_right hReq1) (reqCorner_subset_req_right hReq2)
    subst hk1Eq
    rfl
  have hEdgesMaps : ∀ kw ∈ edges, kw.2 ∈ (A1 ∪ O1).image Wire.gate ∪ leaves := by
    intro kw hkw
    obtain ⟨k', hkAO, hM⟩ := Finset.mem_biUnion.mp hkw
    obtain ⟨w', hwC, rfl⟩ := Finset.mem_image.mp hM
    have hkClean : CleanNode1 p root k' := by
      rcases Finset.mem_union.mp hkAO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have hwReq := hCleanReq k' w' hkClean hwC
    have hwN := needCorner_child_of_reqCorner hwReq
    cases w' with
    | input i =>
      apply Finset.mem_union_right
      by_cases hiA : i ∈ altNeed1_inputs p root S1
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hiA).2, k', hkClean.2.2, hkClean.2.1, hwReq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiA⟩, rfl⟩
    | gate j =>
      by_cases hjC : CutNode p root j
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjC,
          (needCorner_eq_cornerValue h1 hwN).symm⟩, rfl⟩
      · by_cases hjAlt : AltNeed1 p root S1 (.gate j)
        · apply Finset.mem_union_right
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hjAlt, k', hkClean.2.2, hkClean.2.1, hwReq⟩
        · have hjClean : CleanNode1 p root j := ⟨hwN, hjAlt, hjC⟩
          have hjNb := (cleanNode1_props h0 h1 hjClean).1.1
          apply Finset.mem_union_left
          refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
          rcases (not_bad_structure p root hjNb).1 with hjAnd | hjOr
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjAnd⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjOr⟩)
  let hitWires : Finset (Wire n c.size) := sHit1.image (dualChild p)
  have hHitWiresCard : hitWires.card = sHit1.card := by
    refine Finset.card_image_of_injOn fun t1 ht1 t2 ht2 hEq => ?_
    have ht1G := segTopOR_goodDual (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht1).1).1
    have ht2G := segTopOR_goodDual (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht2).1).1
    have hReq1 := (segEdge_req_dualChild h0 h1 ht1G.1).2
    have hReq2 := (segEdge_req_dualChild h0 h1 ht2G.1).2
    rw [hEq] at hReq1
    exact req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode ht1G.2.2.1))
      (reqCorner_subset_req_right hReq1) (reqCorner_subset_req_right hReq2)
  have hHitMaps : hitWires ⊆ (A1 ∪ O1).image Wire.gate ∪ leaves := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
    have htS1 : t ∈ S1 := (Finset.mem_filter.mp ht).1
    have htG := segTopOR_goodDual (Finset.mem_sdiff.mp htS1).1
    have hSSub : ∀ r ∈ S1, r ∈ segTopOR p root := fun r hr => (Finset.mem_sdiff.mp hr).1
    have hNotAlt : ¬ AltNeed1 p root S1 (dualChild p t) := fun hA =>
      altNeed1_avoids_belowDualChain h0 h1 hSSub hA (BelowDualChain.direct htS1)
    have hwReq := (segEdge_req_dualChild h0 h1 htG.1).2
    have hwN := needCorner_child_of_reqCorner hwReq
    cases hChild : dualChild p t with
    | input i =>
      apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hiA => ?_⟩, rfl⟩
      exact hNotAlt (hChild ▸ (Finset.mem_filter.mp hiA).2)
    | gate j =>
      by_cases hjC : CutNode p root j
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjC,
          (needCorner_eq_cornerValue h1 (hChild ▸ hwN)).symm⟩, rfl⟩
      · have hjClean : CleanNode1 p root j :=
          ⟨hChild ▸ hwN, fun hjAlt => hNotAlt (hChild ▸ hjAlt), hjC⟩
        have hjNb := (cleanNode1_props h0 h1 hjClean).1.1
        apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        rcases (not_bad_structure p root hjNb).1 with hjAnd | hjOr
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjAnd⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjOr⟩)
  have hEdgesDisjHit : Disjoint (edges.image Prod.snd) hitWires := by
    rw [Finset.disjoint_left]
    intro w hwE hwH
    obtain ⟨kw, hkw, rfl⟩ := Finset.mem_image.mp hwE
    obtain ⟨k', hkAO, hM⟩ := Finset.mem_biUnion.mp hkw
    obtain ⟨w', hwC, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hwH
    have hkClean : CleanNode1 p root k' := by
      rcases Finset.mem_union.mp hkAO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have htG := segTopOR_goodDual (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).1
    have hReqK := hCleanReq k' w' hkClean hwC
    have hReqT := hEq ▸ (segEdge_req_dualChild h0 h1 htG.1).2
    have hkEq : k' = t := req_unique_parent
      (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hkClean.2.2))
      (reqCorner_subset_req_right hReqK) (reqCorner_subset_req_right hReqT)
    subst hkEq
    exact hkClean.2.1 (Finset.mem_filter.mp ht).2
  have hEdgesImgCard : (edges.image Prod.snd).card = edges.card :=
    Finset.card_image_of_injOn hEdgesInj
  have hSubAll : edges.image Prod.snd ∪ hitWires ⊆ (A1 ∪ O1).image Wire.gate ∪ leaves := by
    refine Finset.union_subset (fun w hw => ?_) hHitMaps
    obtain ⟨kw, hkw, rfl⟩ := Finset.mem_image.mp hw
    exact hEdgesMaps kw hkw
  have hJointEdges : edges.card + sHit1.card ≤ A1.card + O1.card + leaves.card := by
    have h1' := Finset.card_le_card hSubAll
    rw [Finset.card_union_of_disjoint hEdgesDisjHit, hEdgesImgCard, hHitWiresCard] at h1'
    have h2' : ((A1 ∪ O1).image (Wire.gate : Fin c.size → Wire n c.size) ∪ leaves).card ≤
        ((A1 ∪ O1).image (Wire.gate : Fin c.size → Wire n c.size)).card + leaves.card :=
      Finset.card_union_le ..
    have h3' : ((A1 ∪ O1).image (Wire.gate : Fin c.size → Wire n c.size)).card ≤ (A1 ∪ O1).card :=
      Finset.card_image_le
    have h4' : (A1 ∪ O1).card ≤ A1.card + O1.card := Finset.card_union_le ..
    omega
  have hAHitLe : A1.card + sHit1.card ≤ leaves.card := by omega
  have hSegOpOR : ∀ {u v : Fin c.size}, (p.lines u).op = .or →
      SegAnc p root u v → (p.lines v).op = .or := by
    intro u v hu hA
    induction hA with
    | refl => exact hu
    | @tail a b _ hab ih => exact (ih.symm.trans hab.2.2.2.2.1).symm
  have hExBot : ∀ t ∈ S1, ∃ k : Fin c.size,
      SegAnc p root t k ∧ k ∈ goodDual p root ∧ ¬ CutNode p root k ∧ (p.lines k).op = .or ∧
        dualChild p k ∈ A1.image Wire.gate ∪ leaves := by
    intro t htS1
    have htG := segTopOR_goodDual (Finset.mem_sdiff.mp htS1).1
    let segSet := Finset.univ.filter fun k : Fin c.size =>
      SegAnc p root t k ∧ (k = t ∨ CleanNode1 p root k)
    have htSeg : t ∈ segSet :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl, Or.inl rfl⟩
    obtain ⟨k, hkSeg, hkMin⟩ := Finset.exists_min_image segSet Fin.val ⟨t, htSeg⟩
    obtain ⟨hkAnc, hkState⟩ := (Finset.mem_filter.mp hkSeg).2
    have hkOp : (p.lines k).op = .or := hSegOpOR htG.2.1.1 hkAnc
    have hkG : k ∈ goodDual p root := by
      rcases hkState with rfl | hkClean
      · exact htG.1
      · exact ((cleanNode1_props h0 h1 hkClean).2.2 hkOp).1
    have hkNotC : ¬ CutNode p root k := by
      rcases hkState with rfl | hkClean
      · exact htG.2.2.1
      · exact hkClean.2.2
    have hkNotAltOfNe : k ≠ t → ¬ AltNeed1 p root S1 (.gate k) := by
      intro hne
      rcases hkState with rfl | hkClean
      · exact (hne rfl).elim
      · exact hkClean.2.1
    have hwReq : (dualChild p k, true) ∈ reqCorner p root true k :=
      (segEdge_req_dualChild h0 h1 hkG).2
    have hwN := needCorner_child_of_reqCorner hwReq
    have hNotCleanIfAlt (hAlt : AltNeed1 p root S1 (dualChild p k)) : CleanNode1 p root k := by
      rcases hkState with rfl | hkClean
      · exfalso
        have hSSub : ∀ r ∈ S1, r ∈ segTopOR p root := fun r hr => (Finset.mem_sdiff.mp hr).1
        exact altNeed1_avoids_belowDualChain h0 h1 hSSub hAlt (BelowDualChain.direct htS1)
      · exact hkClean
    refine ⟨k, hkAnc, hkG, hkNotC, hkOp, ?_⟩
    cases hChild : dualChild p k with
    | input i =>
      apply Finset.mem_union_right
      by_cases hiA : i ∈ altNeed1_inputs p root S1
      · have hkClean := hNotCleanIfAlt (hChild ▸ (Finset.mem_filter.mp hiA).2)
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hiA).2, k, hkNotC, hkClean.2.1, hChild ▸ hwReq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiA⟩, rfl⟩
    | gate j =>
      by_cases hjC : CutNode p root j
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjC,
          (needCorner_eq_cornerValue h1 (hChild ▸ hwN)).symm⟩, rfl⟩
      · by_cases hjAlt : AltNeed1 p root S1 (.gate j)
        · have hkClean := hNotCleanIfAlt (hChild ▸ hjAlt)
          apply Finset.mem_union_right
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hjAlt, k, hkNotC, hkClean.2.1, hChild ▸ hwReq⟩
        · have hjClean : CleanNode1 p root j := ⟨hChild ▸ hwN, hjAlt, hjC⟩
          have hjProps := cleanNode1_props h0 h1 hjClean
          rcases (not_bad_structure p root hjProps.1.1).1 with hjAnd | hjOr
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjAnd⟩, rfl⟩)
          · exfalso
            have hjG := (hjProps.2.2 hjOr).1
            have hkSegEdge : segEdge p root k j :=
              ⟨hkG, hjG, hkNotC, hjC, hkOp.trans hjOr.symm, hChild⟩
            have hjMem : j ∈ segSet := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hkAnc hkSegEdge, Or.inr hjClean⟩
            have hLe := hkMin j hjMem
            have hkNb := (not_s0_s1_of_not_badFlip
              (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG).2)).1
            have hPre := dualChild_precedes (p := p) (k := k) (not_bad_structure p root hkNb).1
            rw [hChild] at hPre
            have hLt : j.val < k.val := Nat.succ_lt_succ_iff.mp hPre
            omega
  choose botOf hBotProp using fun t (ht : t ∈ S1) => hExBot t ht
  have hS1Le : S1.card ≤ (A1.image Wire.gate ∪ leaves).card := by
    by_cases hEmpty : S1 = ∅
    · simp [hEmpty]
    · obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let fDef := dualChild p (botOf t0 ht0)
      let fBot (t : Fin c.size) : Wire n c.size :=
        if ht : t ∈ S1 then dualChild p (botOf t ht) else fDef
      have hfBot {t} (ht : t ∈ S1) : fBot t = dualChild p (botOf t ht) := by
        simp only [fBot]; split_ifs; rfl
      refine Finset.card_le_card_of_injOn fBot
        (fun t ht => by rw [hfBot ht]; exact (hBotProp t ht).2.2.2.2) ?_
      intro t1 ht1 t2 ht2 hEq
      have hEq' : dualChild p (botOf t1 ht1) = dualChild p (botOf t2 ht2) := by
        rwa [hfBot ht1, hfBot ht2] at hEq
      obtain ⟨hAnc1, hkG1, hkNotC1, _, _⟩ := hBotProp t1 ht1
      obtain ⟨hAnc2, hkG2, _, _, _⟩ := hBotProp t2 ht2
      have hReq1 := (segEdge_req_dualChild h0 h1 hkG1).2
      have hReq2 := (segEdge_req_dualChild h0 h1 hkG2).2
      rw [hEq'] at hReq1
      have hBotEq : botOf t1 ht1 = botOf t2 ht2 :=
        req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hkNotC1))
          (reqCorner_subset_req_right hReq1) (reqCorner_subset_req_right hReq2)
      rw [hBotEq] at hAnc1
      exact segTop_anc_unique h0 h1
        (Or.inl (Finset.mem_sdiff.mp ht1).1)
        (Or.inl (Finset.mem_sdiff.mp ht2).1)
        hAnc1 hAnc2
  have hLeavesCard : leaves.card ≤ B + (cornerCutNodes p root true).card +
      sHit1.card + (badNot p root).card := by
    have hD1 : (Dropped1 p root).card ≤ B := by
      simpa [Dropped1, p, root] using
        card_altNeed1_compl_le_of_sparse c hc hSparse hf0 hf1 S1
          (fun t ht => by have hg := segTopOR_goodDual (Finset.mem_sdiff.mp ht).1; exact ⟨hg.1, hg.2.1.1⟩)
    have hAE := card_altEntry1_le_sHit c hc hf0 hf1
    let d1W : Finset (Wire n c.size) := (Dropped1 p root).image Wire.input
    let cnW : Finset (Wire n c.size) := (cornerCutNodes p root true).image Wire.gate
    have hU1 : leaves.card ≤ (d1W ∪ cnW).card + (altEntry1 p root).card :=
      Finset.card_union_le (d1W ∪ cnW) (altEntry1 p root)
    have hU2 : (d1W ∪ cnW).card ≤ d1W.card + cnW.card := Finset.card_union_le d1W cnW
    have hI1 : d1W.card ≤ (Dropped1 p root).card := Finset.card_image_le
    have hI2 : cnW.card ≤ (cornerCutNodes p root true).card := Finset.card_image_le
    dsimp only [p, root, S1, sHit1] at hAE hU1 hI2 ⊢
    omega
  have hAUL : (A1.image Wire.gate ∪ leaves).card ≤ A1.card + leaves.card :=
    (Finset.card_union_le ..).trans (add_le_add Finset.card_image_le le_rfl)
  have hHit : sHit1.card ≤ B + (dualCutNodes p root).card :=
    card_sHit1_le_dualCutNodes c hc hSparse hf0 hf1
  have hSplitSeg : (segTopOR p root).card ≤ (PureH0Bad p root).card + S1.card := by
    have hSub : segTopOR p root ⊆ PureH0Bad p root ∪ S1 := fun k hk => by
      by_cases hP : k ∈ PureH0Bad p root
      · exact Finset.mem_union_left _ hP
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hk, hP⟩)
    exact (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  dsimp only [p, root, S1, sHit1] at hAHitLe hS1Le hLeavesCard hHit hSplitSeg ⊢
  omega

private theorem card_segTopOR_tight {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (segTopOR c.program (c.outputs 0)).card ≤ 5 * B + 623 * slack c.program (c.outputs 0) := by
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  have hEx := card_segTopOR_exact c hc hSparse hf0 hf1
  have hPure := (card_pureH0Bad_le p root h0 h1).trans (card_cutGate_le_slack p root h0 h1)
  have hCut := card_cutNode_le_slack p root h0 h1
  have hCorner := Finset.card_le_card (cornerCutNodes_subset p root true)
  have hDual := Finset.card_le_card (dualCutNodes_subset p root)
  have hBadNot : (badNot p root).card ≤ slack p root :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (card_badGates_le_slack p root)
  dsimp only [p, root] at hEx hPure hCut hCorner hDual hBadNot ⊢
  omega

theorem card_segTopOR_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (segTopOR c.program (c.outputs 0)).card ≤ 5 * B + 663 * slack c.program (c.outputs 0) :=
  (card_segTopOR_tight c hc hSparse hf0 hf1).trans (by omega)

private theorem card_segTopAND_exact {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (segTopAND c.program (c.outputs 0)).card ≤
      (PureH1Bad c.program (c.outputs 0)).card + 3 * B +
        2 * (cornerCutNodes c.program (c.outputs 0) false).card +
        (dualCutNodes c.program (c.outputs 0)).card +
        2 * (badNot c.program (c.outputs 0)).card := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let S0 := segTopAND p root \ PureH1Bad p root
  let sHit0 := S0.filter fun t => AltNeed0 p root S0 (.gate t)
  let A0 := Finset.univ.filter fun k : Fin c.size => CleanNode0 p root k ∧ (p.lines k).op = .or
  let O0 := Finset.univ.filter fun k : Fin c.size => CleanNode0 p root k ∧ (p.lines k).op = .and
  let leaves := subtreeLeaves0 p root
  let edges : Finset (Fin c.size × Wire n c.size) :=
    (A0 ∪ O0).biUnion fun k => (cleanChild0 p root k).image fun w => (k, w)
  have hCleanReq : ∀ k w, CleanNode0 p root k → w ∈ cleanChild0 p root k →
      (w, false) ∈ reqCorner p root false k := by
    intro k w hk hw
    obtain ⟨⟨w0, v0⟩, hbReq, hEq⟩ := Finset.mem_image.mp hw
    have hv : v0 = false := cleanNode0_req_false h0 hk hbReq
    dsimp only at hEq
    subst hEq; subst hv
    exact hbReq
  have hDisjAO : Disjoint A0 O0 := by
    rw [Finset.disjoint_left]
    intro k hA hO
    have h1A := (Finset.mem_filter.mp hA).2.2
    have h1O := (Finset.mem_filter.mp hO).2.2
    rw [h1A] at h1O; cases h1O
  have hDisjEdges : ∀ k1 ∈ A0 ∪ O0, ∀ k2 ∈ A0 ∪ O0, k1 ≠ k2 →
      Disjoint ((cleanChild0 p root k1).image fun w => (k1, w))
        ((cleanChild0 p root k2).image fun w => (k2, w)) := by
    intro k1 _ k2 _ hne
    rw [Finset.disjoint_left]
    intro kw h1' h2'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1'
    obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2'
    exact hne (congrArg Prod.fst hEq).symm
  have hEdgesLhs : edges.card = 2 * A0.card + O0.card := by
    dsimp only [edges]
    rw [Finset.card_biUnion (fun k1 hk1 k2 hk2 hne => hDisjEdges k1 hk1 k2 hk2 hne),
      Finset.sum_union hDisjAO]
    have hSumA : ∑ k ∈ A0, ((cleanChild0 p root k).image fun w => (k, w)).card = 2 * A0.card := by
      calc
        _ = ∑ _k ∈ A0, 2 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
          exact (cleanNode0_props h0 h1 (Finset.mem_filter.mp hk).2.1).2.1
            (Finset.mem_filter.mp hk).2.2
        _ = 2 * A0.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hSumO : ∑ k ∈ O0, ((cleanChild0 p root k).image fun w => (k, w)).card = O0.card := by
      calc
        _ = ∑ _k ∈ O0, 1 := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
          exact ((cleanNode0_props h0 h1 (Finset.mem_filter.mp hk).2.1).2.2
            (Finset.mem_filter.mp hk).2.2).2.1
        _ = O0.card := by simp
    rw [hSumA, hSumO]
  have hEdgesInj : Set.InjOn Prod.snd (edges : Set (Fin c.size × Wire n c.size)) := by
    intro kw1 h1' kw2 h2' hEq
    obtain ⟨k1', hk1AO, hM1⟩ := Finset.mem_biUnion.mp h1'
    obtain ⟨w1', hw1C, rfl⟩ := Finset.mem_image.mp hM1
    obtain ⟨k2', hk2AO, hM2⟩ := Finset.mem_biUnion.mp h2'
    obtain ⟨w2', hw2C, rfl⟩ := Finset.mem_image.mp hM2
    dsimp only at hEq
    rcases hEq with rfl
    have hk1Clean : CleanNode0 p root k1' := by
      rcases Finset.mem_union.mp hk1AO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have hk2Clean : CleanNode0 p root k2' := by
      rcases Finset.mem_union.mp hk2AO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have hReq1 := hCleanReq k1' w1' hk1Clean hw1C
    have hReq2 := hCleanReq k2' w1' hk2Clean hw2C
    have hk1Eq := req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hk1Clean.2.2))
      (reqCorner_subset_req_left hReq1) (reqCorner_subset_req_left hReq2)
    subst hk1Eq
    rfl
  have hEdgesMaps : ∀ kw ∈ edges, kw.2 ∈ (A0 ∪ O0).image Wire.gate ∪ leaves := by
    intro kw hkw
    obtain ⟨k', hkAO, hM⟩ := Finset.mem_biUnion.mp hkw
    obtain ⟨w', hwC, rfl⟩ := Finset.mem_image.mp hM
    have hkClean : CleanNode0 p root k' := by
      rcases Finset.mem_union.mp hkAO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have hwReq := hCleanReq k' w' hkClean hwC
    have hwN := needCorner_child_of_reqCorner hwReq
    cases w' with
    | input i =>
      apply Finset.mem_union_right
      by_cases hiA : i ∈ altNeed0_inputs p root S0
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hiA).2, k', hkClean.2.2, hkClean.2.1, hwReq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiA⟩, rfl⟩
    | gate j =>
      by_cases hjC : CutNode p root j
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjC,
          (needCorner_eq_cornerValue h0 hwN).symm⟩, rfl⟩
      · by_cases hjAlt : AltNeed0 p root S0 (.gate j)
        · apply Finset.mem_union_right
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hjAlt, k', hkClean.2.2, hkClean.2.1, hwReq⟩
        · have hjClean : CleanNode0 p root j := ⟨hwN, hjAlt, hjC⟩
          have hjNb := (cleanNode0_props h0 h1 hjClean).1.1
          apply Finset.mem_union_left
          refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
          rcases (not_bad_structure p root hjNb).1 with hjAnd | hjOr
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjAnd⟩)
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjOr⟩)
  let hitWires : Finset (Wire n c.size) := sHit0.image (dualChild p)
  have hHitWiresCard : hitWires.card = sHit0.card := by
    refine Finset.card_image_of_injOn fun t1 ht1 t2 ht2 hEq => ?_
    have ht1G := segTopAND_goodDual (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht1).1).1
    have ht2G := segTopAND_goodDual (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht2).1).1
    have hReq1 := (segEdge_req_dualChild h0 h1 ht1G.1).1
    have hReq2 := (segEdge_req_dualChild h0 h1 ht2G.1).1
    rw [hEq] at hReq1
    exact req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode ht1G.2.2.1))
      (reqCorner_subset_req_left hReq1) (reqCorner_subset_req_left hReq2)
  have hHitMaps : hitWires ⊆ (A0 ∪ O0).image Wire.gate ∪ leaves := by
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
    have htS0 : t ∈ S0 := (Finset.mem_filter.mp ht).1
    have htG := segTopAND_goodDual (Finset.mem_sdiff.mp htS0).1
    have hSSub : ∀ r ∈ S0, r ∈ segTopAND p root := fun r hr => (Finset.mem_sdiff.mp hr).1
    have hNotAlt : ¬ AltNeed0 p root S0 (dualChild p t) := fun hA =>
      altNeed0_avoids_belowDualChain h0 h1 hSSub hA (BelowDualChain.direct htS0)
    have hwReq := (segEdge_req_dualChild h0 h1 htG.1).1
    have hwN := needCorner_child_of_reqCorner hwReq
    cases hChild : dualChild p t with
    | input i =>
      apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hiA => ?_⟩, rfl⟩
      exact hNotAlt (hChild ▸ (Finset.mem_filter.mp hiA).2)
    | gate j =>
      by_cases hjC : CutNode p root j
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjC,
          (needCorner_eq_cornerValue h0 (hChild ▸ hwN)).symm⟩, rfl⟩
      · have hjClean : CleanNode0 p root j :=
          ⟨hChild ▸ hwN, fun hjAlt => hNotAlt (hChild ▸ hjAlt), hjC⟩
        have hjNb := (cleanNode0_props h0 h1 hjClean).1.1
        apply Finset.mem_union_left
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        rcases (not_bad_structure p root hjNb).1 with hjAnd | hjOr
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjAnd⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjOr⟩)
  have hEdgesDisjHit : Disjoint (edges.image Prod.snd) hitWires := by
    rw [Finset.disjoint_left]
    intro w hwE hwH
    obtain ⟨kw, hkw, rfl⟩ := Finset.mem_image.mp hwE
    obtain ⟨k', hkAO, hM⟩ := Finset.mem_biUnion.mp hkw
    obtain ⟨w', hwC, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨t, ht, hEq⟩ := Finset.mem_image.mp hwH
    have hkClean : CleanNode0 p root k' := by
      rcases Finset.mem_union.mp hkAO with hA | hO
      · exact (Finset.mem_filter.mp hA).2.1
      · exact (Finset.mem_filter.mp hO).2.1
    have htG := segTopAND_goodDual (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).1
    have hReqK := hCleanReq k' w' hkClean hwC
    have hReqT := hEq ▸ (segEdge_req_dualChild h0 h1 htG.1).1
    have hkEq : k' = t := req_unique_parent
      (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hkClean.2.2))
      (reqCorner_subset_req_left hReqK) (reqCorner_subset_req_left hReqT)
    subst hkEq
    exact hkClean.2.1 (Finset.mem_filter.mp ht).2
  have hEdgesImgCard : (edges.image Prod.snd).card = edges.card :=
    Finset.card_image_of_injOn hEdgesInj
  have hSubAll : edges.image Prod.snd ∪ hitWires ⊆ (A0 ∪ O0).image Wire.gate ∪ leaves := by
    refine Finset.union_subset (fun w hw => ?_) hHitMaps
    obtain ⟨kw, hkw, rfl⟩ := Finset.mem_image.mp hw
    exact hEdgesMaps kw hkw
  have hJointEdges : edges.card + sHit0.card ≤ A0.card + O0.card + leaves.card := by
    have h1' := Finset.card_le_card hSubAll
    rw [Finset.card_union_of_disjoint hEdgesDisjHit, hEdgesImgCard, hHitWiresCard] at h1'
    have h2' : ((A0 ∪ O0).image (Wire.gate : Fin c.size → Wire n c.size) ∪ leaves).card ≤
        ((A0 ∪ O0).image (Wire.gate : Fin c.size → Wire n c.size)).card + leaves.card :=
      Finset.card_union_le ..
    have h3' : ((A0 ∪ O0).image (Wire.gate : Fin c.size → Wire n c.size)).card ≤ (A0 ∪ O0).card :=
      Finset.card_image_le
    have h4' : (A0 ∪ O0).card ≤ A0.card + O0.card := Finset.card_union_le ..
    omega
  have hAHitLe : A0.card + sHit0.card ≤ leaves.card := by omega
  have hSegOpAND : ∀ {u v : Fin c.size}, (p.lines u).op = .and →
      SegAnc p root u v → (p.lines v).op = .and := by
    intro u v hu hA
    induction hA with
    | refl => exact hu
    | @tail a b _ hab ih => exact (ih.symm.trans hab.2.2.2.2.1).symm
  have hExBot : ∀ t ∈ S0, ∃ k : Fin c.size,
      SegAnc p root t k ∧ k ∈ goodDual p root ∧ ¬ CutNode p root k ∧ (p.lines k).op = .and ∧
        dualChild p k ∈ A0.image Wire.gate ∪ leaves := by
    intro t htS0
    have htG := segTopAND_goodDual (Finset.mem_sdiff.mp htS0).1
    let segSet := Finset.univ.filter fun k : Fin c.size =>
      SegAnc p root t k ∧ (k = t ∨ CleanNode0 p root k)
    have htSeg : t ∈ segSet :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl, Or.inl rfl⟩
    obtain ⟨k, hkSeg, hkMin⟩ := Finset.exists_min_image segSet Fin.val ⟨t, htSeg⟩
    obtain ⟨hkAnc, hkState⟩ := (Finset.mem_filter.mp hkSeg).2
    have hkOp : (p.lines k).op = .and := hSegOpAND htG.2.1.1 hkAnc
    have hkG : k ∈ goodDual p root := by
      rcases hkState with rfl | hkClean
      · exact htG.1
      · exact ((cleanNode0_props h0 h1 hkClean).2.2 hkOp).1
    have hkNotC : ¬ CutNode p root k := by
      rcases hkState with rfl | hkClean
      · exact htG.2.2.1
      · exact hkClean.2.2
    have hwReq : (dualChild p k, false) ∈ reqCorner p root false k :=
      (segEdge_req_dualChild h0 h1 hkG).1
    have hwN := needCorner_child_of_reqCorner hwReq
    have hNotCleanIfAlt (hAlt : AltNeed0 p root S0 (dualChild p k)) : CleanNode0 p root k := by
      rcases hkState with rfl | hkClean
      · exfalso
        have hSSub : ∀ r ∈ S0, r ∈ segTopAND p root := fun r hr => (Finset.mem_sdiff.mp hr).1
        exact altNeed0_avoids_belowDualChain h0 h1 hSSub hAlt (BelowDualChain.direct htS0)
      · exact hkClean
    refine ⟨k, hkAnc, hkG, hkNotC, hkOp, ?_⟩
    cases hChild : dualChild p k with
    | input i =>
      apply Finset.mem_union_right
      by_cases hiA : i ∈ altNeed0_inputs p root S0
      · have hkClean := hNotCleanIfAlt (hChild ▸ (Finset.mem_filter.mp hiA).2)
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hiA).2, k, hkNotC, hkClean.2.1, hChild ▸ hwReq⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiA⟩, rfl⟩
    | gate j =>
      by_cases hjC : CutNode p root j
      · apply Finset.mem_union_right
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjC,
          (needCorner_eq_cornerValue h0 (hChild ▸ hwN)).symm⟩, rfl⟩
      · by_cases hjAlt : AltNeed0 p root S0 (.gate j)
        · have hkClean := hNotCleanIfAlt (hChild ▸ hjAlt)
          apply Finset.mem_union_right
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hjAlt, k, hkNotC, hkClean.2.1, hChild ▸ hwReq⟩
        · have hjClean : CleanNode0 p root j := ⟨hChild ▸ hwN, hjAlt, hjC⟩
          have hjProps := cleanNode0_props h0 h1 hjClean
          rcases (not_bad_structure p root hjProps.1.1).1 with hjAnd | hjOr
          · exfalso
            have hjG := (hjProps.2.2 hjAnd).1
            have hkSegEdge : segEdge p root k j :=
              ⟨hkG, hjG, hkNotC, hjC, hkOp.trans hjAnd.symm, hChild⟩
            have hjMem : j ∈ segSet := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, Relation.ReflTransGen.tail hkAnc hkSegEdge, Or.inr hjClean⟩
            have hLe := hkMin j hjMem
            have hkNb := (not_s0_s1_of_not_badFlip
              (not_badFlip_of_not_otherBad (goodDual_iff.mp hkG).2)).1
            have hPre := dualChild_precedes (p := p) (k := k) (not_bad_structure p root hkNb).1
            rw [hChild] at hPre
            have hLt : j.val < k.val := Nat.succ_lt_succ_iff.mp hPre
            omega
          · exact Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjClean, hjOr⟩, rfl⟩)
  choose botOf hBotProp using fun t (ht : t ∈ S0) => hExBot t ht
  have hS0Le : S0.card ≤ (A0.image Wire.gate ∪ leaves).card := by
    by_cases hEmpty : S0 = ∅
    · simp [hEmpty]
    · obtain ⟨t0, ht0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let fDef := dualChild p (botOf t0 ht0)
      let fBot (t : Fin c.size) : Wire n c.size :=
        if ht : t ∈ S0 then dualChild p (botOf t ht) else fDef
      have hfBot {t} (ht : t ∈ S0) : fBot t = dualChild p (botOf t ht) := by
        simp only [fBot]; split_ifs; rfl
      refine Finset.card_le_card_of_injOn fBot
        (fun t ht => by rw [hfBot ht]; exact (hBotProp t ht).2.2.2.2) ?_
      intro t1 ht1 t2 ht2 hEq
      have hEq' : dualChild p (botOf t1 ht1) = dualChild p (botOf t2 ht2) := by
        rwa [hfBot ht1, hfBot ht2] at hEq
      obtain ⟨hAnc1, hkG1, hkNotC1, _, _⟩ := hBotProp t1 ht1
      obtain ⟨hAnc2, hkG2, _, _, _⟩ := hBotProp t2 ht2
      have hReq1 := (segEdge_req_dualChild h0 h1 hkG1).1
      have hReq2 := (segEdge_req_dualChild h0 h1 hkG2).1
      rw [hEq'] at hReq1
      have hBotEq : botOf t1 ht1 = botOf t2 ht2 :=
        req_unique_parent (cutGate_not_hasRepeat (not_cutGate_of_not_cutNode hkNotC1))
          (reqCorner_subset_req_left hReq1) (reqCorner_subset_req_left hReq2)
      rw [hBotEq] at hAnc1
      exact segTop_anc_unique h0 h1
        (Or.inr (Finset.mem_sdiff.mp ht1).1)
        (Or.inr (Finset.mem_sdiff.mp ht2).1)
        hAnc1 hAnc2
  have hLeavesCard : leaves.card ≤ B + (cornerCutNodes p root false).card +
      sHit0.card + (badNot p root).card := by
    have hD0 : (Dropped0 p root).card ≤ B := by
      simpa [Dropped0, p, root] using
        card_altNeed0_compl_le_of_sparse c hc hSparse hf0 hf1 S0
          (fun t ht => by have hg := segTopAND_goodDual (Finset.mem_sdiff.mp ht).1; exact ⟨hg.1, hg.2.1.1⟩)
    have hAE := card_altEntry0_le_sHit c hc hf0 hf1
    let d0W : Finset (Wire n c.size) := (Dropped0 p root).image Wire.input
    let cnW : Finset (Wire n c.size) := (cornerCutNodes p root false).image Wire.gate
    have hU1 : leaves.card ≤ (d0W ∪ cnW).card + (altEntry0 p root).card :=
      Finset.card_union_le (d0W ∪ cnW) (altEntry0 p root)
    have hU2 : (d0W ∪ cnW).card ≤ d0W.card + cnW.card := Finset.card_union_le d0W cnW
    have hI1 : d0W.card ≤ (Dropped0 p root).card := Finset.card_image_le
    have hI2 : cnW.card ≤ (cornerCutNodes p root false).card := Finset.card_image_le
    dsimp only [p, root, S0, sHit0] at hAE hU1 hI2 ⊢
    omega
  have hAUL : (A0.image Wire.gate ∪ leaves).card ≤ A0.card + leaves.card :=
    (Finset.card_union_le ..).trans (add_le_add Finset.card_image_le le_rfl)
  have hHit : sHit0.card ≤ B + (dualCutNodes p root).card :=
    card_sHit0_le_dualCutNodes c hc hSparse hf0 hf1
  have hSplitSeg : (segTopAND p root).card ≤ (PureH1Bad p root).card + S0.card := by
    have hSub : segTopAND p root ⊆ PureH1Bad p root ∪ S0 := fun k hk => by
      by_cases hP : k ∈ PureH1Bad p root
      · exact Finset.mem_union_left _ hP
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hk, hP⟩)
    exact (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
  dsimp only [p, root, S0, sHit0] at hAHitLe hS0Le hLeavesCard hHit hSplitSeg ⊢
  omega

private theorem card_segTopAND_tight {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (segTopAND c.program (c.outputs 0)).card ≤ 5 * B + 623 * slack c.program (c.outputs 0) := by
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  have hEx := card_segTopAND_exact c hc hSparse hf0 hf1
  have hPure := (card_pureH1Bad_le p root h0 h1).trans (card_cutGate_le_slack p root h0 h1)
  have hCut := card_cutNode_le_slack p root h0 h1
  have hCorner := Finset.card_le_card (cornerCutNodes_subset p root false)
  have hDual := Finset.card_le_card (dualCutNodes_subset p root)
  have hBadNot : (badNot p root).card ≤ slack p root :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (card_badGates_le_slack p root)
  dsimp only [p, root] at hEx hPure hCut hCorner hDual hBadNot ⊢
  omega

theorem card_segTopAND_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (segTopAND c.program (c.outputs 0)).card ≤ 5 * B + 663 * slack c.program (c.outputs 0) :=
  (card_segTopAND_tight c hc hSparse hf0 hf1).trans (by omega)

/-! #### Monotone `.or` / `.and` forest: `ORGate`, `ANDGate`, `ORRoot`, `ANDRoot`, `ORMember`, `ANDMember` -/

/-- Clean `.or` gate outside `StopGate` needed as `false` at corner `0`. -/
def ORGate (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  k ∉ StopGate p root ∧ (p.lines k).op = .or ∧ NeedCorner p root false (.gate k, false)

/-- Clean `.and` gate outside `StopGate` needed as `true` at corner `1`. -/
def ANDGate (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  k ∉ StopGate p root ∧ (p.lines k).op = .and ∧ NeedCorner p root true (.gate k, true)

/-- Wires directly referenced by `StopGate`. -/
noncomputable def stopTargets (p : Program signature n g) (root : Wire n g) : Finset (Wire n g) :=
  (StopGate p root).biUnion fun k => Finset.univ.image (p.lines k).wires

/-- Raw inputs directly read by a stop gate. -/
noncomputable def stopInputs (p : Program signature n g) (root : Wire n g) : Finset (Fin n) :=
  Finset.univ.filter fun i => (.input i : Wire n g) ∈ stopTargets p root

theorem stopInput_mem_of_wire {p : Program signature n g} {root : Wire n g}
    {k : Fin g} (hk : k ∈ StopGate p root) (a : Fin (signature.Arity (p.lines k).op))
    {i : Fin n} (ha : (p.lines k).wires a = .input i) : i ∈ stopInputs p root :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩⟩⟩

theorem stopInputs_subset_cutInputs (p : Program signature n g) (root : Wire n g) :
    stopInputs p root ⊆ cutInputs p root := by
  intro i hi
  obtain ⟨k, hk, hw⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hi).2
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨k, hk, a, ha⟩)⟩

/-- Actual argument ports of stop gates, indexed by gate and argument. -/
noncomputable def stopPorts (p : Program signature n g) (root : Wire n g) :
    Finset (Σ k : Fin g, Fin (signature.Arity (p.lines k).op)) :=
  (StopGate p root).sigma fun _ => Finset.univ

theorem stopTargets_eq_image_ports (p : Program signature n g) (root : Wire n g) :
    stopTargets p root = (stopPorts p root).image (fun a => (p.lines a.1).wires a.2) := by
  ext w
  constructor
  · intro hw
    obtain ⟨k,hk,hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨⟨k,a⟩, Finset.mem_sigma.mpr ⟨hk,ha⟩, he⟩
  · intro hw
    obtain ⟨⟨k,a⟩,ha,he⟩ := Finset.mem_image.mp hw
    obtain ⟨hk,ha⟩ := Finset.mem_sigma.mp ha
    exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨a,ha,he⟩⟩

theorem card_stopTargets_le_twice_stopGate (p : Program signature n g) (root : Wire n g) :
    (stopTargets p root).card ≤ 2 * (StopGate p root).card := by
  rw [stopTargets_eq_image_ports]
  refine Finset.card_image_le.trans ?_
  rw [stopPorts,Finset.card_sigma]
  calc
    _ ≤ ∑ _k ∈ StopGate p root, 2 := Finset.sum_le_sum fun k _ => by
      simpa using (Program.fanInAtMost_iff.mp p.fanInAtMost_two k)
    _ = _ := by simp [Nat.mul_comm]

theorem card_stopTargets_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (stopTargets p root).card ≤ 116 * slack p root := by
  have h := card_stopTargets_le_twice_stopGate p root
  have hSG := card_stopGate_le_slack p root h0 h1
  omega

/-- Roots of the maximal clean monotone `.or` trees. -/
noncomputable def ORRoot (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  segTopOR p root ∪
    (Finset.univ.filter fun k => EnteredByOtherBad p root k ∧ ORGate p root k) ∪
    (Finset.univ.filter fun k => ORGate p root k ∧ (.gate k : Wire n g) ∈ stopTargets p root)

/-- Roots of the maximal clean monotone `.and` trees. -/
noncomputable def ANDRoot (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  segTopAND p root ∪
    (Finset.univ.filter fun k => EnteredByOtherBad p root k ∧ ANDGate p root k) ∪
    (Finset.univ.filter fun k => ANDGate p root k ∧ (.gate k : Wire n g) ∈ stopTargets p root)

private theorem orRoot_is_orGate {p : Program signature n g} {root : Wire n g} {r : Fin g}
    (hr : r ∈ ORRoot p root) : ORGate p root r := by
  rcases Finset.mem_union.mp hr with hL | hStop
  · rcases Finset.mem_union.mp hL with hSeg | hEnt
    · have hG := segTopOR_goodDual hSeg
      exact ⟨not_stopGate_of_not_cutNode hG.2.2.1, hG.2.1.1, hG.2.1.2.1⟩
    · exact (Finset.mem_filter.mp hEnt).2.2
  · exact (Finset.mem_filter.mp hStop).2.1

private theorem andRoot_is_andGate {p : Program signature n g} {root : Wire n g} {r : Fin g}
    (hr : r ∈ ANDRoot p root) : ANDGate p root r := by
  rcases Finset.mem_union.mp hr with hL | hStop
  · rcases Finset.mem_union.mp hL with hSeg | hEnt
    · have hG := segTopAND_goodDual hSeg
      exact ⟨not_stopGate_of_not_cutNode hG.2.2.1, hG.2.1.1, hG.2.1.2.2⟩
    · exact (Finset.mem_filter.mp hEnt).2.2
  · exact (Finset.mem_filter.mp hStop).2.1

private theorem root_budgets {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    ((ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      10 * B + 1442 * slack c.program (c.outputs 0)) ∧
    ((stopInputs c.program (c.outputs 0)).card +
        (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      10 * B + 1326 * slack c.program (c.outputs 0) + 2 * (StopGate c.program (c.outputs 0)).card) ∧
    ((stopInputs c.program (c.outputs 0)).card +
        (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      6 * B + 84 * slack c.program (c.outputs 0)) := by
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let eOR := Finset.univ.filter fun k : Fin c.size => EnteredByOtherBad p root k ∧ ORGate p root k
  let eAND := Finset.univ.filter fun k : Fin c.size => EnteredByOtherBad p root k ∧ ANDGate p root k
  let sOR := Finset.univ.filter fun k : Fin c.size => ORGate p root k ∧ (.gate k : Wire n c.size) ∈ stopTargets p root
  let sAND := Finset.univ.filter fun k : Fin c.size => ANDGate p root k ∧ (.gate k : Wire n c.size) ∈ stopTargets p root
  have hEO : (eOR ∪ eAND).card ≤ (Finset.univ.filter (EnteredByOtherBad p root)).card :=
    Finset.card_le_card fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rcases Finset.mem_union.mp hk with h1' | h2'
      · exact (Finset.mem_filter.mp h1').2.1
      · exact (Finset.mem_filter.mp h2').2.1⟩
  have hDisjE : Disjoint eOR eAND := by
    rw [Finset.disjoint_left]
    intro k h1' h2'
    have ho := (Finset.mem_filter.mp h1').2.2.2.1
    have ha := (Finset.mem_filter.mp h2').2.2.2.1
    rw [ho] at ha; cases ha
  have hSumE_card : eOR.card + eAND.card ≤ (Finset.univ.filter (EnteredByOtherBad p root)).card := by
    rw [← Finset.card_union_of_disjoint hDisjE]
    exact hEO
  have hSumE : eOR.card + eAND.card ≤ 55 * slack p root := by
    have h1' := card_enteredByOtherBad_le p root h0 h1
    have h2' := card_otherBad_le_slack p root h0 h1
    have hSh : shared p root ≤ slack p root := by unfold slack; omega
    omega
  have hDisjS : Disjoint sOR sAND := by
    rw [Finset.disjoint_left]
    intro k h1' h2'
    have ho := (Finset.mem_filter.mp h1').2.1.2.1
    have ha := (Finset.mem_filter.mp h2').2.1.2.1
    rw [ho] at ha; cases ha
  let rootWires := (sOR ∪ sAND).image (fun k => (.gate k : Wire n c.size))
  let inputWires := (stopInputs p root).image (fun i => (.input i : Wire n c.size))
  have hDisjWires : Disjoint inputWires rootWires := by
    apply Finset.disjoint_left.mpr
    intro w hi hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hg
    cases hk
  have hTargets : inputWires ∪ rootWires ⊆ stopTargets p root := by
    intro w hw
    rcases Finset.mem_union.mp hw with hi | hg
    · obtain ⟨i, hiInput, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hiInput).2
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hg
      rcases Finset.mem_union.mp hk with ho | ha
      · exact (Finset.mem_filter.mp ho).2.2
      · exact (Finset.mem_filter.mp ha).2.2
  have hJoint := Finset.card_le_card hTargets
  rw [Finset.card_union_of_disjoint hDisjWires] at hJoint
  have hInjI : Function.Injective (fun i => (.input i : Wire n c.size)) :=
    fun _ _ h => by cases h; rfl
  have hInjG : Function.Injective (fun k => (.gate k : Wire n c.size)) :=
    fun _ _ h => by cases h; rfl
  dsimp only [inputWires, rootWires] at hJoint
  rw [Finset.card_image_of_injective _ hInjI, Finset.card_image_of_injective _ hInjG,
    Finset.card_union_of_disjoint hDisjS] at hJoint
  have hStop := card_stopTargets_le_twice_stopGate p root
  have hStopSlack := card_stopGate_le_slack p root h0 h1
  have hORU : (ORRoot p root).card ≤ (segTopOR p root).card + eOR.card + sOR.card := by
    have h1' := Finset.card_union_le (segTopOR p root ∪ eOR) sOR
    have h2' := Finset.card_union_le (segTopOR p root) eOR
    change (segTopOR p root ∪ eOR ∪ sOR).card ≤ _
    omega
  have hANDU : (ANDRoot p root).card ≤ (segTopAND p root).card + eAND.card + sAND.card := by
    have h1' := Finset.card_union_le (segTopAND p root ∪ eAND) sAND
    have h2' := Finset.card_union_le (segTopAND p root) eAND
    change (segTopAND p root ∪ eAND ∪ sAND).card ≤ _
    omega
  have hSegOR := card_segTopOR_tight c hc hSparse hf0 hf1
  have hSegAND := card_segTopAND_tight c hc hSparse hf0 hf1
  have hExOR := card_segTopOR_exact c hc hSparse hf0 hf1
  have hExAND := card_segTopAND_exact c hc hSparse hf0 hf1
  have hPureBoth := card_pureH0Bad_add_pureH1Bad_le_tight p root h0 h1
  have hCutBoth := card_cutNode_add_badNot_le_tight p root h0 h1
  have hEBTight := card_enteredByOtherBad_le_tight p root h0 h1
  have hDualCut := card_dualCutNodes_le p root h0 h1
  have hCornerCut := card_cornerCutNodes_add p root
  have hSGTight := card_stopGate_add_badNot_le_tight p root h0 h1
  have hBadUnused := card_badGates_le p root
  have hBadAddSh : (badGates p root).card + shared p root ≤ slack p root := by
    unfold slack; omega
  dsimp only [p, root] at hORU hANDU hSumE_card hSumE hJoint hStop hStopSlack hExOR hExAND hPureBoth hCutBoth hEBTight hDualCut hCornerCut hSGTight hBadAddSh
  exact ⟨by omega, by omega, by omega⟩

theorem card_orRoot_add_andRoot_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      10 * B + 1442 * slack c.program (c.outputs 0) :=
  (root_budgets c hc hSparse hf0 hf1).1

/-- Raw inputs and forest-root wires entering stop gates share one fan-in budget. -/
theorem card_stopInputs_and_roots_le {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (stopInputs c.program (c.outputs 0)).card +
        (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      10 * B + 1326 * slack c.program (c.outputs 0) + 2 * (StopGate c.program (c.outputs 0)).card :=
  (root_budgets c hc hSparse hf0 hf1).2.1

/-- The forest boundary pays for each physical port once. Across corner
certificates only endpoints carrying both corner values need both allowances. -/
theorem card_stopInputs_and_roots_le_ports {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (stopInputs c.program (c.outputs 0)).card +
        (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      6 * B + 84 * slack c.program (c.outputs 0) :=
  (root_budgets c hc hSparse hf0 hf1).2.2

/-- The combined forest boundary budget with its original coefficient. -/
theorem card_stopInputs_and_roots_le_tight {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    (stopInputs c.program (c.outputs 0)).card +
        (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card ≤
      6 * B + 112 * slack c.program (c.outputs 0) :=
  (card_stopInputs_and_roots_le_ports c hc hSparse hf0 hf1).trans (by omega)

/-- Gate membership inside the clean monotone `.or` tree rooted at `r`. -/
inductive ORMember (p : Program signature n g) (root : Wire n g) (r : Fin g) : Fin g → Prop where
  | self (hr : r ∈ ORRoot p root) : ORMember p root r r
  | child {k j : Fin g} (hk : ORMember p root r k) (hj : ORGate p root j)
      (hjNotRoot : j ∉ ORRoot p root) (hWire : ∃ a, (p.lines k).wires a = .gate j) :
      ORMember p root r j

/-- Gate membership inside the clean monotone `.and` tree rooted at `r`. -/
inductive ANDMember (p : Program signature n g) (root : Wire n g) (r : Fin g) : Fin g → Prop where
  | self (hr : r ∈ ANDRoot p root) : ANDMember p root r r
  | child {k j : Fin g} (hk : ANDMember p root r k) (hj : ANDGate p root j)
      (hjNotRoot : j ∉ ANDRoot p root) (hWire : ∃ a, (p.lines k).wires a = .gate j) :
      ANDMember p root r j

/-- Input coordinates directly entering the clean `.or` tree rooted at `r`. -/
noncomputable def orInputs (p : Program signature n g) (root : Wire n g) (r : Fin g) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ k, ORMember p root r k ∧ ∃ a, (p.lines k).wires a = .input i

/-- Input coordinates directly entering the clean `.and` tree rooted at `r`. -/
noncomputable def andInputs (p : Program signature n g) (root : Wire n g) (r : Fin g) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ k, ANDMember p root r k ∧ ∃ a, (p.lines k).wires a = .input i

private theorem orMember_is_orGate {p : Program signature n g} {root : Wire n g} {r k : Fin g}
    (hk : ORMember p root r k) : ORGate p root k := by
  induction hk with
  | self hr => exact orRoot_is_orGate hr
  | child _ hj _ _ => exact hj

private theorem andMember_is_andGate {p : Program signature n g} {root : Wire n g} {r k : Fin g}
    (hk : ANDMember p root r k) : ANDGate p root k := by
  induction hk with
  | self hr => exact andRoot_is_andGate hr
  | child _ hj _ _ => exact hj

/-- A stop gate belongs to neither of the clean monotone forests. -/
theorem stopGate_outside_forest {p : Program signature n g} {root : Wire n g}
    {k : Fin g} (hk : k ∈ StopGate p root) :
    (∀ r, ¬ ORMember p root r k) ∧ (∀ r, ¬ ANDMember p root r k) :=
  ⟨fun _ h => (orMember_is_orGate h).1 hk, fun _ h => (andMember_is_andGate h).1 hk⟩

private theorem orMember_le {p : Program signature n g} {root : Wire n g} {r k : Fin g}
    (hk : ORMember p root r k) : k.val ≤ r.val ∧ (k ≠ r → k.val < r.val) := by
  induction hk with
  | self _ => exact ⟨le_rfl, fun h => (h rfl).elim⟩
  | @child k j _ _ _ hWire ih =>
    obtain ⟨a, ha⟩ := hWire
    have hLt := p.lt_of_lines_wires_eq_gate k a j ha
    exact ⟨le_trans hLt.le ih.1, fun _ => Nat.lt_of_lt_of_le hLt ih.1⟩

private theorem andMember_le {p : Program signature n g} {root : Wire n g} {r k : Fin g}
    (hk : ANDMember p root r k) : k.val ≤ r.val ∧ (k ≠ r → k.val < r.val) := by
  induction hk with
  | self _ => exact ⟨le_rfl, fun h => (h rfl).elim⟩
  | @child k j _ _ _ hWire ih =>
    obtain ⟨a, ha⟩ := hWire
    have hLt := p.lt_of_lines_wires_eq_gate k a j ha
    exact ⟨le_trans hLt.le ih.1, fun _ => Nat.lt_of_lt_of_le hLt ih.1⟩

private theorem orGate_req_wires {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) {k : Fin g} (hk : ORGate p root k)
    (a : Fin (signature.Arity (p.lines k).op)) :
    ((p.lines k).wires a, false) ∈ reqCorner p root false k := by
  have hVal : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hk.2.2).symm
  have hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := hVal.symm ▸ hk.2.2
  have hEval : interpretation (p.lines k).op
      (fun s => cornerValue p false ((p.lines k).wires s)) = false := by
    simpa [cornerValue_gate] using hVal
  have hMem : ∀ (op : Op) (v : Fin (signature.Arity op) → Bool)
      (_ : op = .or) (_ : interpretation op v = false)
      (s : Fin (signature.Arity op)), s ∈ selectedPins op v ∧ v s = false := by
    intro op v hop hv s; subst hop
    fin_cases s <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]
  obtain ⟨haPin, haVal⟩ := hMem _ _ hk.2.1 hEval a
  simp only [reqCorner, hg, ite_true, cornerArguments]
  exact Finset.mem_image.mpr ⟨a, haPin, Prod.ext rfl haVal⟩

private theorem andGate_req_wires {p : Program signature n g} {root : Wire n g}
    (h1 : cornerValue p true root = true) {k : Fin g} (hk : ANDGate p root k)
    (a : Fin (signature.Arity (p.lines k).op)) :
    ((p.lines k).wires a, true) ∈ reqCorner p root true k := by
  have hVal : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hk.2.2).symm
  have hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := hVal.symm ▸ hk.2.2
  have hEval : interpretation (p.lines k).op
      (fun s => cornerValue p true ((p.lines k).wires s)) = true := by
    simpa [cornerValue_gate] using hVal
  have hMem : ∀ (op : Op) (v : Fin (signature.Arity op) → Bool)
      (_ : op = .and) (_ : interpretation op v = true)
      (s : Fin (signature.Arity op)), s ∈ selectedPins op v ∧ v s = true := by
    intro op v hop hv s; subst hop
    fin_cases s <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;> simp_all [selectedPins, interpretation]
  obtain ⟨haPin, haVal⟩ := hMem _ _ hk.2.1 hEval a
  simp only [reqCorner, hg, ite_true, cornerArguments]
  exact Finset.mem_image.mpr ⟨a, haPin, Prod.ext rfl haVal⟩

theorem orMember_sound {p : Program signature n g} {root : Wire n g} {r k : Fin g}
    (hk : ORMember p root r k) (y : BitString n)
    (hy : p.trace interpretation y (.gate k) = true) :
    p.trace interpretation y (.gate r) = true := by
  induction hk with
  | self _ => exact hy
  | @child k j hkPar hj _ hWire ih =>
    obtain ⟨a, ha⟩ := hWire
    apply ih
    have hkOp := (orMember_is_orGate hkPar).2.1
    have hChild : p.trace interpretation y ((p.lines k).wires a) = true := by
      rw [ha]; exact hy
    exact (p.trace_gate interpretation y k).trans
      (op_or_eq_true (p.lines k).op hkOp (p.lines k).wires _ hChild)

theorem orInputs_sound {p : Program signature n g} {root : Wire n g} {r : Fin g} {i : Fin n}
    (hi : i ∈ orInputs p root r) (y : BitString n) (hy : y i = true) :
    p.trace interpretation y (.gate r) = true := by
  obtain ⟨k, hkMem, a, ha⟩ := (Finset.mem_filter.mp hi).2
  apply orMember_sound hkMem y
  have hkOp := (orMember_is_orGate hkMem).2.1
  have hChild : p.trace interpretation y ((p.lines k).wires a) = true := by
    rw [ha]; simpa using hy
  exact (p.trace_gate interpretation y k).trans
    (op_or_eq_true (p.lines k).op hkOp (p.lines k).wires _ hChild)

theorem andMember_sound {p : Program signature n g} {root : Wire n g} {r k : Fin g}
    (hk : ANDMember p root r k) (y : BitString n)
    (hy : p.trace interpretation y (.gate k) = false) :
    p.trace interpretation y (.gate r) = false := by
  induction hk with
  | self _ => exact hy
  | @child k j hkPar hj _ hWire ih =>
    obtain ⟨a, ha⟩ := hWire
    apply ih
    have hkOp := (andMember_is_andGate hkPar).2.1
    have hChild : p.trace interpretation y ((p.lines k).wires a) = false := by
      rw [ha]; exact hy
    exact (p.trace_gate interpretation y k).trans
      (op_and_eq_false (p.lines k).op hkOp (p.lines k).wires _ hChild)

theorem andInputs_sound {p : Program signature n g} {root : Wire n g} {r : Fin g} {i : Fin n}
    (hi : i ∈ andInputs p root r) (y : BitString n) (hy : y i = false) :
    p.trace interpretation y (.gate r) = false := by
  obtain ⟨k, hkMem, a, ha⟩ := (Finset.mem_filter.mp hi).2
  apply andMember_sound hkMem y
  have hkOp := (andMember_is_andGate hkMem).2.1
  have hChild : p.trace interpretation y ((p.lines k).wires a) = false := by
    rw [ha]; simpa using hy
  exact (p.trace_gate interpretation y k).trans
    (op_and_eq_false (p.lines k).op hkOp (p.lines k).wires _ hChild)

private theorem strictOR_only_from_same_root {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {r j : Fin g} (hjMem : ORMember p root r j) (hne : j ≠ r)
    {k_other : Fin g} {a : Fin (signature.Arity (p.lines k_other).op)}
    (hWire : (p.lines k_other).wires a = .gate j) :
    ORMember p root r k_other := by
  cases hjMem with
  | self => exact (hne rfl).elim
  | @child k_par _ hkPar hj hjNotRoot hWirePar =>
    obtain ⟨b, hb⟩ := hWirePar
    have hkOtherNotStop : k_other ∉ StopGate p root := fun hkS =>
      hjNotRoot (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hj, Finset.mem_biUnion.mpr ⟨k_other, hkS, Finset.mem_image.mpr
          ⟨a, Finset.mem_univ _, hWire⟩⟩⟩))
    have hkOtherNotBG := not_badGates_of_not_cutGate
      (fun hc => hkOtherNotStop (cutGate_subset_stopGate _ _ hc))
    obtain ⟨v, hvReq⟩ := wire_in_req_of_not_badGates hkOtherNotBG a
    rw [hWire] at hvReq
    have hkParOR := orMember_is_orGate hkPar
    have hParReq : ((.gate j : Wire n g), false) ∈ req p root k_par :=
      hb ▸ reqCorner_subset_req_left (orGate_req_wires h0 hkParOR b)
    have hkParNoRep := stopGate_not_hasRepeat hkParOR.1
    cases v with
    | false =>
      have hEq : k_par = k_other := req_unique_parent hkParNoRep hParReq hvReq
      rwa [← hEq]
    | true =>
      have hjN1 : NeedCorner p root true (.gate j, true) :=
        needCorner_child_of_reqCorner (Finset.mem_union.mp hvReq |>.elim
          (fun hL => by
            exfalso
            have hValF : cornerValue p false (.gate j) = false :=
              (needCorner_eq_cornerValue h0 hj.2.2).symm
            have hVal : cornerValue p false (.gate j) = true := by
              have hNW := needCorner_child_of_reqCorner hL
              exact (needCorner_eq_cornerValue h0 hNW).symm
            rw [hValF] at hVal; cases hVal)
          id)
      have hjGood : j ∈ goodDual p root := by
        have hbf := not_badFlip_of_not_cutGate (fun hc => hj.1 (cutGate_subset_stopGate _ _ hc))
        have hDO : IsDualOR p root j := ⟨hj.2.1, hj.2.2, hjN1⟩
        exact goodDual_iff.mpr ⟨Or.inr hDO, stopGate_not_otherBad hj.1⟩
      have hjNotCut : ¬ CutNode p root j := by
        rintro (hS | hE)
        · exact hj.1 hS
        · exact hjNotRoot (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hj⟩)))
      have hjNotSegTop : j ∉ segTopOR p root := fun hS =>
        hjNotRoot (Finset.mem_union_left _ (Finset.mem_union_left _ hS))
      have hParU : ∃ u, segEdge p root u j := by
        by_contra hNoPar
        exact hjNotSegTop (Finset.mem_filter.mpr ⟨hjGood, hj.2.1, hjNotCut, hNoPar⟩)
      obtain ⟨u, huEdge⟩ := hParU
      have huNoRep := cutGate_not_hasRepeat (not_cutGate_of_not_cutNode huEdge.2.2.1)
      have huReqF : ((.gate j : Wire n g), false) ∈ req p root u :=
        huEdge.2.2.2.2.2 ▸ reqCorner_subset_req_left (segEdge_req_dualChild h0 h1 huEdge.1).1
      have huReqT : ((.gate j : Wire n g), true) ∈ req p root u :=
        huEdge.2.2.2.2.2 ▸ reqCorner_subset_req_right (segEdge_req_dualChild h0 h1 huEdge.1).2
      have hEq1 : k_par = u := req_unique_parent hkParNoRep hParReq huReqF
      have hEq2 : u = k_other := req_unique_parent huNoRep huReqT hvReq
      rwa [← hEq2, ← hEq1]

private theorem strictAND_only_from_same_root {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {r j : Fin g} (hjMem : ANDMember p root r j) (hne : j ≠ r)
    {k_other : Fin g} {a : Fin (signature.Arity (p.lines k_other).op)}
    (hWire : (p.lines k_other).wires a = .gate j) :
    ANDMember p root r k_other := by
  cases hjMem with
  | self => exact (hne rfl).elim
  | @child k_par _ hkPar hj hjNotRoot hWirePar =>
    obtain ⟨b, hb⟩ := hWirePar
    have hkOtherNotStop : k_other ∉ StopGate p root := fun hkS =>
      hjNotRoot (Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hj, Finset.mem_biUnion.mpr ⟨k_other, hkS, Finset.mem_image.mpr
          ⟨a, Finset.mem_univ _, hWire⟩⟩⟩))
    have hkOtherNotBG := not_badGates_of_not_cutGate
      (fun hc => hkOtherNotStop (cutGate_subset_stopGate _ _ hc))
    obtain ⟨v, hvReq⟩ := wire_in_req_of_not_badGates hkOtherNotBG a
    rw [hWire] at hvReq
    have hkParAND := andMember_is_andGate hkPar
    have hParReq : ((.gate j : Wire n g), true) ∈ req p root k_par :=
      hb ▸ reqCorner_subset_req_right (andGate_req_wires h1 hkParAND b)
    have hkParNoRep := stopGate_not_hasRepeat hkParAND.1
    cases v with
    | true =>
      have hEq : k_par = k_other := req_unique_parent hkParNoRep hParReq hvReq
      rwa [← hEq]
    | false =>
      have hjN0 : NeedCorner p root false (.gate j, false) :=
        needCorner_child_of_reqCorner (Finset.mem_union.mp hvReq |>.elim
          id
          (fun hR => by
            exfalso
            have hValT : cornerValue p true (.gate j) = true :=
              (needCorner_eq_cornerValue h1 hj.2.2).symm
            have hVal : cornerValue p true (.gate j) = false := by
              have hNW := needCorner_child_of_reqCorner hR
              exact (needCorner_eq_cornerValue h1 hNW).symm
            rw [hValT] at hVal; cases hVal))
      have hjGood : j ∈ goodDual p root := by
        have hDA : IsDualAND p root j := ⟨hj.2.1, hjN0, hj.2.2⟩
        exact goodDual_iff.mpr ⟨Or.inl hDA, stopGate_not_otherBad hj.1⟩
      have hjNotCut : ¬ CutNode p root j := by
        rintro (hS | hE)
        · exact hj.1 hS
        · exact hjNotRoot (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hj⟩)))
      have hjNotSegTop : j ∉ segTopAND p root := fun hS =>
        hjNotRoot (Finset.mem_union_left _ (Finset.mem_union_left _ hS))
      have hParU : ∃ u, segEdge p root u j := by
        by_contra hNoPar
        exact hjNotSegTop (Finset.mem_filter.mpr ⟨hjGood, hj.2.1, hjNotCut, hNoPar⟩)
      obtain ⟨u, huEdge⟩ := hParU
      have huNoRep := cutGate_not_hasRepeat (not_cutGate_of_not_cutNode huEdge.2.2.1)
      have huReqF : ((.gate j : Wire n g), false) ∈ req p root u :=
        huEdge.2.2.2.2.2 ▸ reqCorner_subset_req_left (segEdge_req_dualChild h0 h1 huEdge.1).1
      have huReqT : ((.gate j : Wire n g), true) ∈ req p root u :=
        huEdge.2.2.2.2.2 ▸ reqCorner_subset_req_right (segEdge_req_dualChild h0 h1 huEdge.1).2
      have hEq1 : k_par = u := req_unique_parent hkParNoRep hParReq huReqT
      have hEq2 : u = k_other := req_unique_parent huNoRep huReqF hvReq
      rwa [← hEq2, ← hEq1]

theorem orMember_unique_root {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) {r1 r2 k : Fin g}
    (h1' : ORMember p root r1 k) (h2' : ORMember p root r2 k) : r1 = r2 := by
  induction h1' with
  | self hr1 =>
    cases h2' with
    | self => rfl
    | child _ _ hNotR _ => exact (hNotR hr1).elim
  | @child k1 j1 hk1Par _ hj1NotR hWire1 ih1 =>
    cases h2' with
    | self hr2 => exact (hj1NotR hr2).elim
    | @child k2 _ hk2Par _ _ hWire2 =>
      obtain ⟨a1, ha1⟩ := hWire1
      obtain ⟨a2, ha2⟩ := hWire2
      have hReq1 : ((.gate j1 : Wire n g), false) ∈ req p root k1 :=
        ha1 ▸ reqCorner_subset_req_left (orGate_req_wires h0 (orMember_is_orGate hk1Par) a1)
      have hReq2 : ((.gate j1 : Wire n g), false) ∈ req p root k2 :=
        ha2 ▸ reqCorner_subset_req_left (orGate_req_wires h0 (orMember_is_orGate hk2Par) a2)
      have hEq : k1 = k2 :=
        req_unique_parent (stopGate_not_hasRepeat (orMember_is_orGate hk1Par).1) hReq1 hReq2
      subst hEq
      exact ih1 hk2Par

theorem andMember_unique_root {p : Program signature n g} {root : Wire n g}
    (h1 : cornerValue p true root = true) {r1 r2 k : Fin g}
    (h1' : ANDMember p root r1 k) (h2' : ANDMember p root r2 k) : r1 = r2 := by
  induction h1' with
  | self hr1 =>
    cases h2' with
    | self => rfl
    | child _ _ hNotR _ => exact (hNotR hr1).elim
  | @child k1 j1 hk1Par _ hj1NotR hWire1 ih1 =>
    cases h2' with
    | self hr2 => exact (hj1NotR hr2).elim
    | @child k2 _ hk2Par _ _ hWire2 =>
      obtain ⟨a1, ha1⟩ := hWire1
      obtain ⟨a2, ha2⟩ := hWire2
      have hReq1 : ((.gate j1 : Wire n g), true) ∈ req p root k1 :=
        ha1 ▸ reqCorner_subset_req_right (andGate_req_wires h1 (andMember_is_andGate hk1Par) a1)
      have hReq2 : ((.gate j1 : Wire n g), true) ∈ req p root k2 :=
        ha2 ▸ reqCorner_subset_req_right (andGate_req_wires h1 (andMember_is_andGate hk2Par) a2)
      have hEq : k1 = k2 :=
        req_unique_parent (stopGate_not_hasRepeat (andMember_is_andGate hk1Par).1) hReq1 hReq2
      subst hEq
      exact ih1 hk2Par

theorem orInputs_disjoint {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) {r1 r2 : Fin g}
    (hne : r1 ≠ r2) : Disjoint (orInputs p root r1) (orInputs p root r2) := by
  rw [Finset.disjoint_left]
  intro i hi1 hi2
  obtain ⟨k1, hk1, a1, ha1⟩ := (Finset.mem_filter.mp hi1).2
  obtain ⟨k2, hk2, a2, ha2⟩ := (Finset.mem_filter.mp hi2).2
  have hReq1 : ((.input i : Wire n g), false) ∈ req p root k1 :=
    ha1 ▸ reqCorner_subset_req_left (orGate_req_wires h0 (orMember_is_orGate hk1) a1)
  have hReq2 : ((.input i : Wire n g), false) ∈ req p root k2 :=
    ha2 ▸ reqCorner_subset_req_left (orGate_req_wires h0 (orMember_is_orGate hk2) a2)
  have hEq : k1 = k2 :=
    req_unique_parent (stopGate_not_hasRepeat (orMember_is_orGate hk1).1) hReq1 hReq2
  subst hEq
  exact hne (orMember_unique_root h0 hk1 hk2)

theorem andInputs_disjoint {p : Program signature n g} {root : Wire n g}
    (h1 : cornerValue p true root = true) {r1 r2 : Fin g}
    (hne : r1 ≠ r2) : Disjoint (andInputs p root r1) (andInputs p root r2) := by
  rw [Finset.disjoint_left]
  intro i hi1 hi2
  obtain ⟨k1, hk1, a1, ha1⟩ := (Finset.mem_filter.mp hi1).2
  obtain ⟨k2, hk2, a2, ha2⟩ := (Finset.mem_filter.mp hi2).2
  have hReq1 : ((.input i : Wire n g), true) ∈ req p root k1 :=
    ha1 ▸ reqCorner_subset_req_right (andGate_req_wires h1 (andMember_is_andGate hk1) a1)
  have hReq2 : ((.input i : Wire n g), true) ∈ req p root k2 :=
    ha2 ▸ reqCorner_subset_req_right (andGate_req_wires h1 (andMember_is_andGate hk2) a2)
  have hEq : k1 = k2 :=
    req_unique_parent (stopGate_not_hasRepeat (andMember_is_andGate hk1).1) hReq1 hReq2
  subst hEq
  exact hne (andMember_unique_root h1 hk1 hk2)

/-- The operation labels and the reader constraints needed to replace a forest component. -/
theorem orMember_rebuild_data {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {r j : Fin g} (hj : ORMember p root r j) :
    (p.lines j).op = .or ∧ j.val ≤ r.val ∧
    (j ≠ r → ∃ t, ORMember p root r t ∧ ∃ a, (p.lines t).wires a = .gate j) ∧
    (∀ t (a : Fin (signature.Arity (p.lines t).op)), j ≠ r →
      (p.lines t).wires a = .gate j → ORMember p root r t) := by
  refine ⟨(orMember_is_orGate hj).2.1, (orMember_le hj).1, ?_, ?_⟩
  · intro hne
    cases hj with
    | self => exact (hne rfl).elim
    | child hp _ _ ha => exact ⟨_, hp, ha⟩
  · intro t a hne hWire
    exact strictOR_only_from_same_root h0 h1 hj hne hWire

/-- The operation labels and the reader constraints needed to replace a forest component. -/
theorem andMember_rebuild_data {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {r j : Fin g} (hj : ANDMember p root r j) :
    (p.lines j).op = .and ∧ j.val ≤ r.val ∧
    (j ≠ r → ∃ t, ANDMember p root r t ∧ ∃ a, (p.lines t).wires a = .gate j) ∧
    (∀ t (a : Fin (signature.Arity (p.lines t).op)), j ≠ r →
      (p.lines t).wires a = .gate j → ANDMember p root r t) := by
  refine ⟨(andMember_is_andGate hj).2.1, (andMember_le hj).1, ?_, ?_⟩
  · intro hne
    cases hj with
    | self => exact (hne rfl).elim
    | child hp _ _ ha => exact ⟨_, hp, ha⟩
  · intro t a hne hWire
    exact strictAND_only_from_same_root h0 h1 hj hne hWire

theorem orMember_root_precedes_output {p : Program signature n g} {root : Wire n g} {r : Fin g}
    (hr : r ∈ ORRoot p root) : wireOrder (.gate r : Wire n g) ≤ wireOrder root :=
  needCorner_precedes_root (orRoot_is_orGate hr).2.2

theorem andMember_root_precedes_output {p : Program signature n g} {root : Wire n g} {r : Fin g}
    (hr : r ∈ ANDRoot p root) : wireOrder (.gate r : Wire n g) ≤ wireOrder root :=
  needCorner_precedes_root (andRoot_is_andGate hr).2.2

private theorem needCorner_parent_of_ne_pair {p : Program signature n g} {root : Wire n g} {b : Bool}
    {key : Wire n g × Bool} (h : NeedCorner p root b key) (hNe : key ≠ (root, true)) :
    ∃ k : Fin g, NeedCorner p root b (.gate k, cornerValue p b (.gate k)) ∧
      key ∈ reqCorner p root b k := by
  cases h with
  | output => exact (hNe rfl).elim
  | argument hg ha => exact ⟨_, hg, by simp [reqCorner, hg, ha]⟩

private theorem orGate_mem_orMember {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    ∀ d : ℕ, ∀ k : Fin g, g - k.val ≤ d → ORGate p root k →
      ∃ r ∈ ORRoot p root, ORMember p root r k := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk hkOR
    by_cases hkR : k ∈ ORRoot p root
    · exact ⟨k, hkR, ORMember.self hkR⟩
    · have hNotRootWire : (.gate k : Wire n g) ≠ root := by
        intro hEq
        have hVal := hEq ▸ h0
        have hValK : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hkOR.2.2).symm
        rw [hValK] at hVal; cases hVal
      obtain ⟨p0, hp0N, hp0Req⟩ :=
        needCorner_parent_of_ne_pair hkOR.2.2 (fun h => hNotRootWire (congrArg Prod.fst h))
      have hp0NotStop : p0 ∉ StopGate p root := by
        intro hp0S
        simp only [reqCorner, hp0N, ite_true, cornerArguments] at hp0Req
        obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hp0Req
        exact hkR (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hkOR, Finset.mem_biUnion.mpr ⟨p0, hp0S, Finset.mem_image.mpr
            ⟨a, Finset.mem_univ _, congrArg Prod.fst hEqW⟩⟩⟩))
      have hbfP0 := not_badFlip_of_not_cutGate (fun hc => hp0NotStop (cutGate_subset_stopGate _ _ hc))
      have hp0ValF : cornerValue p false (.gate p0) = false := by
        by_contra hV
        have hVT : cornerValue p false (.gate p0) = true := Bool.eq_true_of_not_eq_false hV
        exact (not_s0_s1_of_not_badFlip hbfP0).2.1 (by simpa [hVT] using hp0N)
      have hp0N0 : NeedCorner p root false (.gate p0, false) := by simpa [hp0ValF] using hp0N
      rcases four_way_of_not_badFlip h0 h1 hbfP0 with hDA | hDO | hPA | hPO
      · exfalso
        have hp0G := goodDual_iff.mpr ⟨Or.inl hDA, stopGate_not_otherBad hp0NotStop⟩
        have hCardOne : (reqCorner p root false p0).card ≤ 1 := by
          simp only [reqCorner, hp0N, ite_true, cornerArguments]
          have hEval : interpretation (p.lines p0).op
              (fun s => cornerValue p false ((p.lines p0).wires s)) = false := by
            simpa [cornerValue_gate] using hp0ValF
          exact Finset.card_image_le.trans
            (selectedPins_card_le_one_of_op (p.lines p0).op _ (Or.inl ⟨hDA.1, hEval⟩))
        have hDualMem : (dualChild p p0, false) ∈ reqCorner p root false p0 :=
          (segEdge_req_dualChild h0 h1 hp0G).1
        have hEqDual : (.gate k : Wire n g) = dualChild p p0 :=
          Prod.ext_iff.mp (Finset.card_le_one.mp hCardOne _ hp0Req _ hDualMem) |>.1
        have hkN1 : NeedCorner p root true (.gate k, true) :=
          needCorner_child_of_reqCorner (hEqDual.symm ▸ (segEdge_req_dualChild h0 h1 hp0G).2)
        have hkGood := goodDual_iff.mpr ⟨Or.inr ⟨hkOR.2.1, hkOR.2.2, hkN1⟩, stopGate_not_otherBad hkOR.1⟩
        have hkNotC : ¬ CutNode p root k := by
          rintro (hS | hE)
          · exact hkOR.1 hS
          · exact hkR (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hkOR⟩)))
        have hkNoPar : ¬ ∃ u, segEdge p root u k := by
          rintro ⟨u, huEdge⟩
          have huNoRep := cutGate_not_hasRepeat (not_cutGate_of_not_cutNode huEdge.2.2.1)
          have huReq := huEdge.2.2.2.2.2 ▸ reqCorner_subset_req_left
            (segEdge_req_dualChild h0 h1 huEdge.1).1
          have hEqU := req_unique_parent huNoRep huReq (reqCorner_subset_req_left hp0Req)
          have hOpU := huEdge.2.2.2.2.1.trans hkOR.2.1
          rw [hEqU, hDA.1] at hOpU; cases hOpU
        exact hkR (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hkGood, hkOR.2.1, hkNotC, hkNoPar⟩)))
      · have hp0OR : ORGate p root p0 := ⟨hp0NotStop, hDO.1, hp0N0⟩
        have hWire : ∃ a, (p.lines p0).wires a = .gate k := by
          simp only [reqCorner, hp0N, ite_true, cornerArguments] at hp0Req
          obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hp0Req
          exact ⟨a, congrArg Prod.fst hEqW⟩
        obtain ⟨a, ha⟩ := hWire
        have hLt := p.lt_of_lines_wires_eq_gate p0 a k ha
        have hGp0 : p0.val < g := p0.isLt
        obtain ⟨r, hrR, hrMem⟩ := ih (g - p0.val) (by omega) p0 le_rfl hp0OR
        exact ⟨r, hrR, ORMember.child hrMem hkOR hkR ⟨a, ha⟩⟩
      · exact (hPA.2.1 hp0N0).elim
      · have hp0OR : ORGate p root p0 := ⟨hp0NotStop, hPO.1, hp0N0⟩
        have hWire : ∃ a, (p.lines p0).wires a = .gate k := by
          simp only [reqCorner, hp0N, ite_true, cornerArguments] at hp0Req
          obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hp0Req
          exact ⟨a, congrArg Prod.fst hEqW⟩
        obtain ⟨a, ha⟩ := hWire
        have hLt := p.lt_of_lines_wires_eq_gate p0 a k ha
        have hGp0 : p0.val < g := p0.isLt
        obtain ⟨r, hrR, hrMem⟩ := ih (g - p0.val) (by omega) p0 le_rfl hp0OR
        exact ⟨r, hrR, ORMember.child hrMem hkOR hkR ⟨a, ha⟩⟩

private theorem andGate_mem_andMember {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    ∀ d : ℕ, ∀ k : Fin g, g - k.val ≤ d → ANDGate p root k →
      ∃ r ∈ ANDRoot p root, ANDMember p root r k := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k hk hkAND
    by_cases hkR : k ∈ ANDRoot p root
    · exact ⟨k, hkR, ANDMember.self hkR⟩
    · have hNotRootWire : (.gate k : Wire n g) ≠ root := by
        intro hEq
        have hbf := not_badFlip_of_not_cutGate (fun hc => hkAND.1 (cutGate_subset_stopGate _ _ hc))
        exact (not_s0_s1_of_not_badFlip hbf).2.1
          (Eq.ndrec (motive := fun w => NeedCorner p root false (w, true)) NeedCorner.output hEq.symm)
      obtain ⟨p0, hp0N, hp0Req⟩ :=
        needCorner_parent_of_ne_pair hkAND.2.2 (fun h => hNotRootWire (congrArg Prod.fst h))
      have hp0NotStop : p0 ∉ StopGate p root := by
        intro hp0S
        simp only [reqCorner, hp0N, ite_true, cornerArguments] at hp0Req
        obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hp0Req
        exact hkR (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hkAND, Finset.mem_biUnion.mpr ⟨p0, hp0S, Finset.mem_image.mpr
            ⟨a, Finset.mem_univ _, congrArg Prod.fst hEqW⟩⟩⟩))
      have hbfP0 := not_badFlip_of_not_cutGate (fun hc => hp0NotStop (cutGate_subset_stopGate _ _ hc))
      have hp0ValT : cornerValue p true (.gate p0) = true := by
        by_contra hV
        have hVF : cornerValue p true (.gate p0) = false := Bool.eq_false_iff.mpr hV
        exact (not_s0_s1_of_not_badFlip hbfP0).2.2 (by simpa [hVF] using hp0N)
      have hp0N1 : NeedCorner p root true (.gate p0, true) := by simpa [hp0ValT] using hp0N
      rcases four_way_of_not_badFlip h0 h1 hbfP0 with hDA | hDO | hPA | hPO
      · have hp0AND : ANDGate p root p0 := ⟨hp0NotStop, hDA.1, hp0N1⟩
        have hWire : ∃ a, (p.lines p0).wires a = .gate k := by
          simp only [reqCorner, hp0N, ite_true, cornerArguments] at hp0Req
          obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hp0Req
          exact ⟨a, congrArg Prod.fst hEqW⟩
        obtain ⟨a, ha⟩ := hWire
        have hLt := p.lt_of_lines_wires_eq_gate p0 a k ha
        have hGp0 : p0.val < g := p0.isLt
        obtain ⟨r, hrR, hrMem⟩ := ih (g - p0.val) (by omega) p0 le_rfl hp0AND
        exact ⟨r, hrR, ANDMember.child hrMem hkAND hkR ⟨a, ha⟩⟩
      · exfalso
        have hp0G := goodDual_iff.mpr ⟨Or.inr hDO, stopGate_not_otherBad hp0NotStop⟩
        have hCardOne : (reqCorner p root true p0).card ≤ 1 := by
          simp only [reqCorner, hp0N, ite_true, cornerArguments]
          have hEval : interpretation (p.lines p0).op
              (fun s => cornerValue p true ((p.lines p0).wires s)) = true := by
            simpa [cornerValue_gate] using hp0ValT
          exact Finset.card_image_le.trans
            (selectedPins_card_le_one_of_op (p.lines p0).op _ (Or.inr ⟨hDO.1, hEval⟩))
        have hDualMem : (dualChild p p0, true) ∈ reqCorner p root true p0 :=
          (segEdge_req_dualChild h0 h1 hp0G).2
        have hEqDual : (.gate k : Wire n g) = dualChild p p0 :=
          Prod.ext_iff.mp (Finset.card_le_one.mp hCardOne _ hp0Req _ hDualMem) |>.1
        have hkN0 : NeedCorner p root false (.gate k, false) :=
          needCorner_child_of_reqCorner (hEqDual.symm ▸ (segEdge_req_dualChild h0 h1 hp0G).1)
        have hkGood := goodDual_iff.mpr ⟨Or.inl ⟨hkAND.2.1, hkN0, hkAND.2.2⟩, stopGate_not_otherBad hkAND.1⟩
        have hkNotC : ¬ CutNode p root k := by
          rintro (hS | hE)
          · exact hkAND.1 hS
          · exact hkR (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hkAND⟩)))
        have hkNoPar : ¬ ∃ u, segEdge p root u k := by
          rintro ⟨u, huEdge⟩
          have huNoRep := cutGate_not_hasRepeat (not_cutGate_of_not_cutNode huEdge.2.2.1)
          have huReq := huEdge.2.2.2.2.2 ▸ reqCorner_subset_req_right
            (segEdge_req_dualChild h0 h1 huEdge.1).2
          have hEqU := req_unique_parent huNoRep huReq (reqCorner_subset_req_right hp0Req)
          have hOpU := huEdge.2.2.2.2.1.trans hkAND.2.1
          rw [hEqU, hDO.1] at hOpU; cases hOpU
        exact hkR (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hkGood, hkAND.2.1, hkNotC, hkNoPar⟩)))
      · have hp0AND : ANDGate p root p0 := ⟨hp0NotStop, hPA.1, hp0N1⟩
        have hWire : ∃ a, (p.lines p0).wires a = .gate k := by
          simp only [reqCorner, hp0N, ite_true, cornerArguments] at hp0Req
          obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hp0Req
          exact ⟨a, congrArg Prod.fst hEqW⟩
        obtain ⟨a, ha⟩ := hWire
        have hLt := p.lt_of_lines_wires_eq_gate p0 a k ha
        have hGp0 : p0.val < g := p0.isLt
        obtain ⟨r, hrR, hrMem⟩ := ih (g - p0.val) (by omega) p0 le_rfl hp0AND
        exact ⟨r, hrR, ANDMember.child hrMem hkAND hkR ⟨a, ha⟩⟩
      · exact (hPO.2.2 hp0N1).elim

/-- Every non-stop gate belongs to a clean monotone component. -/
theorem non_stop_mem_forest {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∉ StopGate p root) :
    (∃ r ∈ ORRoot p root, ORMember p root r k) ∨
      (∃ r ∈ ANDRoot p root, ANDMember p root r k) := by
  have hFlip := not_badFlip_of_not_cutGate (fun h => hk (cutGate_subset_stopGate _ _ h))
  have hClass : ORGate p root k ∨ ANDGate p root k := by
    rcases four_way_of_not_badFlip h0 h1 hFlip with hDA | hDO | hPA | hPO
    · exact Or.inr ⟨hk, hDA.1, hDA.2.2⟩
    · exact Or.inl ⟨hk, hDO.1, hDO.2.1⟩
    · exact Or.inr ⟨hk, hPA.1, hPA.2.2⟩
    · exact Or.inl ⟨hk, hPO.1, hPO.2.1⟩
  exact hClass.imp (orGate_mem_orMember h0 h1 g k (by omega))
    (andGate_mem_andMember h0 h1 g k (by omega))

theorem need_input_in_stop_or_forest {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {i : Fin n} (hi : i ∈ needInputs p root false) :
    i ∈ stopInputs p root ∨ (∃ r ∈ ORRoot p root, i ∈ orInputs p root r) ∨
      (∃ r ∈ ANDRoot p root, i ∈ andInputs p root r) := by
  have hiNeed := (Finset.mem_filter.mp hi).2
  obtain ⟨k, hkNeed, hkReq⟩ := needCorner_parent_of_ne_pair hiNeed (by intro h; cases h)
  simp only [reqCorner, hkNeed, ite_true, cornerArguments] at hkReq
  obtain ⟨a, _, he⟩ := Finset.mem_image.mp hkReq
  have ha : (p.lines k).wires a = .input i := congrArg Prod.fst he
  by_cases hk : k ∈ StopGate p root
  · exact Or.inl (stopInput_mem_of_wire hk a ha)
  rcases non_stop_mem_forest h0 h1 hk with ⟨r, hr, hm⟩ | ⟨r, hr, hm⟩
  · exact Or.inr (Or.inl ⟨r, hr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hm, a, ha⟩⟩)
  · exact Or.inr (Or.inr ⟨r, hr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hm, a, ha⟩⟩)

/-! #### Structured input coverage, perturbation invariance, and `clean_case2_structure` -/

/-- Well-behaved input coordinates isolated inside both `ORRoot` and `ANDRoot`. -/
noncomputable def structuredInputs (p : Program signature n g) (root : Wire n g) : Finset (Fin n) :=
  Finset.univ.filter fun i =>
    i ∉ cutInputs p root ∧
      (∃ r ∈ ORRoot p root, i ∈ orInputs p root r) ∧
      (∃ r' ∈ ANDRoot p root, i ∈ andInputs p root r')

theorem structuredInputs_not_cut {p : Program signature n g} {root : Wire n g} {i : Fin n}
    (hi : i ∈ structuredInputs p root) : i ∉ cutInputs p root :=
  (Finset.mem_filter.mp hi).2.1

theorem structuredInputs_mem_orInputs {p : Program signature n g} {root : Wire n g} {i : Fin n}
    (hi : i ∈ structuredInputs p root) : ∃ r ∈ ORRoot p root, i ∈ orInputs p root r :=
  (Finset.mem_filter.mp hi).2.2.1

theorem structuredInputs_mem_andInputs {p : Program signature n g} {root : Wire n g} {i : Fin n}
    (hi : i ∈ structuredInputs p root) : ∃ r ∈ ANDRoot p root, i ∈ andInputs p root r :=
  (Finset.mem_filter.mp hi).2.2.2

theorem card_structuredInputs_ge {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    n ≤ (structuredInputs c.program (c.outputs 0)).card + 14 * B +
      1671 * slack c.program (c.outputs 0) := by
  classical
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  let drop0 := Finset.univ \ needInputs p root false
  let drop1 := Finset.univ \ needInputs p root true
  let miss0 := (needInputs p root false \ cutInputs p root).filter fun i =>
    ¬ ∃ r ∈ ORRoot p root, i ∈ orInputs p root r
  let miss1 := (needInputs p root true \ cutInputs p root).filter fun i =>
    ¬ ∃ r' ∈ ANDRoot p root, i ∈ andInputs p root r'
  have hCover : (Finset.univ : Finset (Fin n)) ⊆
      cutInputs p root ∪ drop0 ∪ drop1 ∪ miss0 ∪ miss1 ∪ structuredInputs p root := by
    intro i _
    by_cases hiC : i ∈ cutInputs p root
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ hiC))))
    · by_cases hi0 : i ∈ needInputs p root false
      · by_cases hi1 : i ∈ needInputs p root true
        · by_cases hiOR : ∃ r ∈ ORRoot p root, i ∈ orInputs p root r
          · by_cases hiAND : ∃ r' ∈ ANDRoot p root, i ∈ andInputs p root r'
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, hiC, hiOR, hiAND⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hi1, hiC⟩, hiAND⟩))
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hi0, hiC⟩, hiOR⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi1⟩))))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi0⟩)))))
  have hDrop0 : drop0.card ≤ B := by
    have hNI := card_needInputs_ge_of_sparse c hc hSparse false hf0
    have hSub : needInputs p root false ⊆ Finset.univ := Finset.subset_univ _
    have hEq := Finset.card_sdiff_add_card_eq_card hSub
    dsimp only [drop0, p, root] at hEq ⊢
    simp only [Finset.card_univ, Fintype.card_fin] at hEq
    omega
  have hDrop1 : drop1.card ≤ B := by
    have hNI := card_needInputs_ge_of_sparse c hc hSparse true hf1
    have hSub : needInputs p root true ⊆ Finset.univ := Finset.subset_univ _
    have hEq := Finset.card_sdiff_add_card_eq_card hSub
    dsimp only [drop1, p, root] at hEq ⊢
    simp only [Finset.card_univ, Fintype.card_fin] at hEq
    omega
  have hExMiss0 : ∀ i ∈ miss0, ∃ u ∈ segTopAND p root, ∃ k0 : Fin c.size,
      SegAnc p root u k0 ∧ dualChild p k0 = .input i := by
    intro i hi
    obtain ⟨hi0C, hiNoOR⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi0, hiNC⟩ := Finset.mem_sdiff.mp hi0C
    have hNi : NeedCorner p root false (.input i, false) := (Finset.mem_filter.mp hi0).2
    have hNotRoot : (.input i : Wire n c.size) ≠ root := by
      intro hEq
      have hV := hEq ▸ h0
      simp [cornerValue_input] at hV
    obtain ⟨k0, hk0N, hk0Req⟩ :=
      needCorner_parent_of_ne_pair hNi (fun h => hNotRoot (congrArg Prod.fst h))
    have hk0NotStop : k0 ∉ StopGate p root := by
      intro hk0S
      simp only [reqCorner, hk0N, ite_true, cornerArguments] at hk0Req
      obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hk0Req
      exact hiNC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr (Or.inr ⟨k0, hk0S, a, congrArg Prod.fst hEqW⟩)⟩)
    have hbf := not_badFlip_of_not_cutGate (fun hc => hk0NotStop (cutGate_subset_stopGate _ _ hc))
    have hk0ValF : cornerValue p false (.gate k0) = false := by
      by_contra hV
      have hVT : cornerValue p false (.gate k0) = true := Bool.eq_true_of_not_eq_false hV
      exact (not_s0_s1_of_not_badFlip hbf).2.1 (by simpa [hVT] using hk0N)
    have hk0N0 : NeedCorner p root false (.gate k0, false) := by simpa [hk0ValF] using hk0N
    have hk0Dual : IsDualAND p root k0 := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exact hDA
      · exfalso
        have hk0OR : ORGate p root k0 := ⟨hk0NotStop, hDO.1, hk0N0⟩
        obtain ⟨r, hrR, hrMem⟩ := orGate_mem_orMember h0 h1 c.size k0 (by omega) hk0OR
        simp only [reqCorner, hk0N, ite_true, cornerArguments] at hk0Req
        obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hk0Req
        exact hiNoOR ⟨r, hrR, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, k0, hrMem, a, congrArg Prod.fst hEqW⟩⟩
      · exact (hPA.2.1 hk0N0).elim
      · exfalso
        have hk0OR : ORGate p root k0 := ⟨hk0NotStop, hPO.1, hk0N0⟩
        obtain ⟨r, hrR, hrMem⟩ := orGate_mem_orMember h0 h1 c.size k0 (by omega) hk0OR
        simp only [reqCorner, hk0N, ite_true, cornerArguments] at hk0Req
        obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hk0Req
        exact hiNoOR ⟨r, hrR, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, k0, hrMem, a, congrArg Prod.fst hEqW⟩⟩
    have hk0G := goodDual_iff.mpr ⟨Or.inl hk0Dual, stopGate_not_otherBad hk0NotStop⟩
    have hDualMem : (dualChild p k0, false) ∈ reqCorner p root false k0 :=
      (segEdge_req_dualChild h0 h1 hk0G).1
    have hCardOne : (reqCorner p root false k0).card ≤ 1 := by
      simp only [reqCorner, hk0N, ite_true, cornerArguments]
      have hEval : interpretation (p.lines k0).op
          (fun s => cornerValue p false ((p.lines k0).wires s)) = false := by
        simpa [cornerValue_gate] using hk0ValF
      exact Finset.card_image_le.trans
        (selectedPins_card_le_one_of_op (p.lines k0).op _ (Or.inl ⟨hk0Dual.1, hEval⟩))
    have hDualEq : dualChild p k0 = .input i :=
      (Prod.ext_iff.mp (Finset.card_le_one.mp hCardOne _ hk0Req _ hDualMem) |>.1).symm
    have hk0NotC : ¬ CutNode p root k0 := by
      rintro (hS | hE)
      · exact hk0NotStop hS
      · obtain ⟨_, j, _, hjD⟩ := hE
        rw [hDualEq] at hjD; cases hjD
    obtain ⟨u, huMem, huAnc⟩ := exists_segTopAND_of_goodDual c.size k0 (by omega) hk0G hk0Dual.1 hk0NotC
    exact ⟨u, huMem, k0, huAnc, hDualEq⟩
  choose uOf0 huProp0 using fun i (hi : i ∈ miss0) => hExMiss0 i hi
  have hMiss0Le : miss0.card ≤ (segTopAND p root).card := by
    by_cases hEmpty : miss0 = ∅
    · simp [hEmpty]
    · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let fDef := uOf0 i0 hi0
      let fMap (i : Fin n) : Fin c.size := if hi : i ∈ miss0 then uOf0 i hi else fDef
      have hfMap {i} (hi : i ∈ miss0) : fMap i = uOf0 i hi := by
        simp only [fMap]; split_ifs; rfl
      refine Finset.card_le_card_of_injOn fMap
        (fun i hi => by rw [hfMap hi]; exact (huProp0 i hi).1) ?_
      intro i1 hi1 i2 hi2 hEq
      have hEq' : uOf0 i1 hi1 = uOf0 i2 hi2 := by rwa [hfMap hi1, hfMap hi2] at hEq
      obtain ⟨_, k1, hk1Anc, hk1D⟩ := huProp0 i1 hi1
      obtain ⟨hu2, k2, hk2Anc, hk2D⟩ := huProp0 i2 hi2
      rw [← hEq'] at hk2Anc
      have hkEq := segAnc_dualChild_input_eq h0 h1 c.size (uOf0 i1 hi1) k1 k2 i1 i2
        (Nat.le_of_lt (uOf0 i1 hi1).isLt) hk1Anc hk2Anc hk1D hk2D
      rw [hkEq] at hk1D
      have hInEq := hk1D.symm.trans hk2D
      cases hInEq
      rfl
  have hExMiss1 : ∀ i ∈ miss1, ∃ u ∈ segTopOR p root, ∃ k1 : Fin c.size,
      SegAnc p root u k1 ∧ dualChild p k1 = .input i := by
    intro i hi
    obtain ⟨hi1C, hiNoAND⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi1, hiNC⟩ := Finset.mem_sdiff.mp hi1C
    have hNi : NeedCorner p root true (.input i, true) := (Finset.mem_filter.mp hi1).2
    have hNotRoot : (.input i : Wire n c.size) ≠ root := by
      intro hEq
      have hV := hEq ▸ h0
      simp [cornerValue_input] at hV
    obtain ⟨k1, hk1N, hk1Req⟩ :=
      needCorner_parent_of_ne_pair hNi (fun h => hNotRoot (congrArg Prod.fst h))
    have hk1NotStop : k1 ∉ StopGate p root := by
      intro hk1S
      simp only [reqCorner, hk1N, ite_true, cornerArguments] at hk1Req
      obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hk1Req
      exact hiNC (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr (Or.inr ⟨k1, hk1S, a, congrArg Prod.fst hEqW⟩)⟩)
    have hbf := not_badFlip_of_not_cutGate (fun hc => hk1NotStop (cutGate_subset_stopGate _ _ hc))
    have hk1ValT : cornerValue p true (.gate k1) = true := by
      by_contra hV
      have hVF : cornerValue p true (.gate k1) = false := Bool.eq_false_iff.mpr hV
      exact (not_s0_s1_of_not_badFlip hbf).2.2 (by simpa [hVF] using hk1N)
    have hk1N1 : NeedCorner p root true (.gate k1, true) := by simpa [hk1ValT] using hk1N
    have hk1Dual : IsDualOR p root k1 := by
      rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
      · exfalso
        have hk1AND : ANDGate p root k1 := ⟨hk1NotStop, hDA.1, hk1N1⟩
        obtain ⟨r, hrR, hrMem⟩ := andGate_mem_andMember h0 h1 c.size k1 (by omega) hk1AND
        simp only [reqCorner, hk1N, ite_true, cornerArguments] at hk1Req
        obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hk1Req
        exact hiNoAND ⟨r, hrR, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, k1, hrMem, a, congrArg Prod.fst hEqW⟩⟩
      · exact hDO
      · exfalso
        have hk1AND : ANDGate p root k1 := ⟨hk1NotStop, hPA.1, hk1N1⟩
        obtain ⟨r, hrR, hrMem⟩ := andGate_mem_andMember h0 h1 c.size k1 (by omega) hk1AND
        simp only [reqCorner, hk1N, ite_true, cornerArguments] at hk1Req
        obtain ⟨a, _, hEqW⟩ := Finset.mem_image.mp hk1Req
        exact hiNoAND ⟨r, hrR, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, k1, hrMem, a, congrArg Prod.fst hEqW⟩⟩
      · exact (hPO.2.2 hk1N1).elim
    have hk1G := goodDual_iff.mpr ⟨Or.inr hk1Dual, stopGate_not_otherBad hk1NotStop⟩
    have hDualMem : (dualChild p k1, true) ∈ reqCorner p root true k1 :=
      (segEdge_req_dualChild h0 h1 hk1G).2
    have hCardOne : (reqCorner p root true k1).card ≤ 1 := by
      simp only [reqCorner, hk1N, ite_true, cornerArguments]
      have hEval : interpretation (p.lines k1).op
          (fun s => cornerValue p true ((p.lines k1).wires s)) = true := by
        simpa [cornerValue_gate] using hk1ValT
      exact Finset.card_image_le.trans
        (selectedPins_card_le_one_of_op (p.lines k1).op _ (Or.inr ⟨hk1Dual.1, hEval⟩))
    have hDualEq : dualChild p k1 = .input i :=
      (Prod.ext_iff.mp (Finset.card_le_one.mp hCardOne _ hk1Req _ hDualMem) |>.1).symm
    have hk1NotC : ¬ CutNode p root k1 := by
      rintro (hS | hE)
      · exact hk1NotStop hS
      · obtain ⟨_, j, _, hjD⟩ := hE
        rw [hDualEq] at hjD; cases hjD
    obtain ⟨u, huMem, huAnc⟩ := exists_segTopOR_of_goodDual c.size k1 (by omega) hk1G hk1Dual.1 hk1NotC
    exact ⟨u, huMem, k1, huAnc, hDualEq⟩
  choose uOf1 huProp1 using fun i (hi : i ∈ miss1) => hExMiss1 i hi
  have hMiss1Le : miss1.card ≤ (segTopOR p root).card := by
    by_cases hEmpty : miss1 = ∅
    · simp [hEmpty]
    · obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
      let fDef := uOf1 i0 hi0
      let fMap (i : Fin n) : Fin c.size := if hi : i ∈ miss1 then uOf1 i hi else fDef
      have hfMap {i} (hi : i ∈ miss1) : fMap i = uOf1 i hi := by
        simp only [fMap]; split_ifs; rfl
      refine Finset.card_le_card_of_injOn fMap
        (fun i hi => by rw [hfMap hi]; exact (huProp1 i hi).1) ?_
      intro i1 hi1 i2 hi2 hEq
      have hEq' : uOf1 i1 hi1 = uOf1 i2 hi2 := by rwa [hfMap hi1, hfMap hi2] at hEq
      obtain ⟨_, k1, hk1Anc, hk1D⟩ := huProp1 i1 hi1
      obtain ⟨hu2, k2, hk2Anc, hk2D⟩ := huProp1 i2 hi2
      rw [← hEq'] at hk2Anc
      have hkEq := segAnc_dualChild_input_eq h0 h1 c.size (uOf1 i1 hi1) k1 k2 i1 i2
        (Nat.le_of_lt (uOf1 i1 hi1).isLt) hk1Anc hk2Anc hk1D hk2D
      rw [hkEq] at hk1D
      have hInEq := hk1D.symm.trans hk2D
      cases hInEq
      rfl
  have hCardCov := Finset.card_le_card hCover
  have hU1 := Finset.card_union_le (cutInputs p root ∪ drop0 ∪ drop1 ∪ miss0 ∪ miss1) (structuredInputs p root)
  have hU2 := Finset.card_union_le (cutInputs p root ∪ drop0 ∪ drop1 ∪ miss0) miss1
  have hU3 := Finset.card_union_le (cutInputs p root ∪ drop0 ∪ drop1) miss0
  have hU4 := Finset.card_union_le (cutInputs p root ∪ drop0) drop1
  have hU5 := Finset.card_union_le (cutInputs p root) drop0
  have hCut := card_cutInputs_le_slack p root h0 h1
  have hSegAND := card_segTopAND_tight c hc hSparse hf0 hf1
  have hSegOR := card_segTopOR_tight c hc hSparse hf0 hf1
  simp only [Finset.card_univ, Fintype.card_fin] at hCardCov
  dsimp only [p, root] at hCardCov hU1 hU2 hU3 hU4 hU5 hCut hMiss0Le hMiss1Le hDrop0 hDrop1 ⊢
  omega

/-- Two-Corner Bottleneck Ledger Theorem (inspired by Schlesinger's `Frontier/Ledger/LowerBound`):
    The circuit output is completely determined by `cutInputs p root` (at most `116 * slack` bits),
    the 1-bit traces at `ORRoot p root`, and the 1-bit traces at `ANDRoot p root`. -/
theorem eval_eq_of_cutInputs_and_roots {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (x y : BitString n)
    (hCut : ∀ i ∈ cutInputs p root, y i = x i)
    (hOR : ∀ r ∈ ORRoot p root,
      p.trace interpretation y (.gate r) = p.trace interpretation x (.gate r))
    (hAND : ∀ r' ∈ ANDRoot p root,
      p.trace interpretation y (.gate r') = p.trace interpretation x (.gate r')) :
    p.trace interpretation y root = p.trace interpretation x root := by
  let StrictOR (k : Fin g) : Prop := ∃ r ∈ ORRoot p root, ORMember p root r k ∧ k ≠ r
  let StrictAND (k : Fin g) : Prop := ∃ r' ∈ ANDRoot p root, ANDMember p root r' k ∧ k ≠ r'
  have hMain : ∀ m : ℕ, ∀ k : Fin g, k.val ≤ m → ¬ StrictOR k → ¬ StrictAND k →
      p.trace interpretation y (.gate k) = p.trace interpretation x (.gate k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hk hNotSOR hNotSAND
      by_cases hkOR : k ∈ ORRoot p root
      · exact hOR k hkOR
      · by_cases hkAND : k ∈ ANDRoot p root
        · exact hAND k hkAND
        · have hkStop : k ∈ StopGate p root := by
            by_contra hkNotS
            have hbf := not_badFlip_of_not_cutGate (fun hc => hkNotS (cutGate_subset_stopGate _ _ hc))
            rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
            · have hkANDGate : ANDGate p root k := ⟨hkNotS, hDA.1, hDA.2.2⟩
              obtain ⟨r, hrR, hrMem⟩ := andGate_mem_andMember h0 h1 g k (by omega) hkANDGate
              by_cases hEq : k = r
              · subst hEq; exact hkAND hrR
              · exact hNotSAND ⟨r, hrR, hrMem, hEq⟩
            · have hkORGate : ORGate p root k := ⟨hkNotS, hDO.1, hDO.2.1⟩
              obtain ⟨r, hrR, hrMem⟩ := orGate_mem_orMember h0 h1 g k (by omega) hkORGate
              by_cases hEq : k = r
              · subst hEq; exact hkOR hrR
              · exact hNotSOR ⟨r, hrR, hrMem, hEq⟩
            · have hkANDGate : ANDGate p root k := ⟨hkNotS, hPA.1, hPA.2.2⟩
              obtain ⟨r, hrR, hrMem⟩ := andGate_mem_andMember h0 h1 g k (by omega) hkANDGate
              by_cases hEq : k = r
              · subst hEq; exact hkAND hrR
              · exact hNotSAND ⟨r, hrR, hrMem, hEq⟩
            · have hkORGate : ORGate p root k := ⟨hkNotS, hPO.1, hPO.2.1⟩
              obtain ⟨r, hrR, hrMem⟩ := orGate_mem_orMember h0 h1 g k (by omega) hkORGate
              by_cases hEq : k = r
              · subst hEq; exact hkOR hrR
              · exact hNotSOR ⟨r, hrR, hrMem, hEq⟩
          rw [p.trace_gate, p.trace_gate]
          congr 1
          funext a
          cases hWire : (p.lines k).wires a with
          | input i =>
            have hiCut : i ∈ cutInputs p root := Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨k, hkStop, a, hWire⟩)⟩
            simpa using hCut i hiCut
          | gate u =>
            have huLt := p.lt_of_lines_wires_eq_gate k a u hWire
            have huNotSOR : ¬ StrictOR u := by
              rintro ⟨r, hrR, huMem, hne⟩
              have hkMem := strictOR_only_from_same_root h0 h1 huMem hne hWire
              by_cases hEq : k = r
              · subst hEq; exact hkOR hrR
              · exact hNotSOR ⟨r, hrR, hkMem, hEq⟩
            have huNotSAND : ¬ StrictAND u := by
              rintro ⟨r', hrR', huMem', hne'⟩
              have hkMem' := strictAND_only_from_same_root h0 h1 huMem' hne' hWire
              by_cases hEq : k = r'
              · subst hEq; exact hkAND hrR'
              · exact hNotSAND ⟨r', hrR', hkMem', hEq⟩
            exact ih u.val (by omega) u le_rfl huNotSOR huNotSAND
  cases hRoot : root with
  | input i =>
    exfalso
    have hV := hRoot ▸ h0
    simp [cornerValue_input] at hV
  | gate k0 =>
    have hk0NotSOR : ¬ StrictOR k0 := by
      rintro ⟨r, hr, hMem, hne⟩
      have hLt := (orMember_le hMem).2 hne
      have hPre := needCorner_precedes_root ((orRoot_is_orGate hr).2.2)
      rw [hRoot] at hPre
      change r.val + 1 ≤ k0.val + 1 at hPre
      omega
    have hk0NotSAND : ¬ StrictAND k0 := by
      rintro ⟨r', hr', hMem', hne'⟩
      have hLt := (andMember_le hMem').2 hne'
      have hPre := needCorner_precedes_root ((andRoot_is_andGate hr').2.2)
      rw [hRoot] at hPre
      change r'.val + 1 ≤ k0.val + 1 at hPre
      omega
    exact hMain k0.val k0 le_rfl hk0NotSOR hk0NotSAND

/-- At a stop gate, agreement on raw input arguments can be replaced by
agreement on the actual gate output. -/
theorem stopReaders_perturbation_invariant {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (x y : BitString n)
    (hStop : ∀ k ∈ StopGate p root,
      (∀ a i, (p.lines k).wires a = .input i → y i = x i) ∨
      p.trace interpretation y (.gate k) = p.trace interpretation x (.gate k))
    (hOR : ∀ r ∈ ORRoot p root,
      (∃ w ∈ orInputs p root r, x w = true ∧ y w = true) ∨
      (∀ i ∈ orInputs p root r, y i = x i))
    (hAND : ∀ r' ∈ ANDRoot p root,
      (∃ u ∈ andInputs p root r', x u = false ∧ y u = false) ∨
      (∀ i ∈ andInputs p root r', y i = x i)) :
    p.trace interpretation y root = p.trace interpretation x root := by
  let StrictOR (k : Fin g) : Prop := ∃ r ∈ ORRoot p root, ORMember p root r k ∧ k ≠ r
  let StrictAND (k : Fin g) : Prop := ∃ r' ∈ ANDRoot p root, ANDMember p root r' k ∧ k ≠ r'
  have hMain : ∀ m : ℕ, ∀ k : Fin g, k.val ≤ m → ¬ StrictOR k → ¬ StrictAND k →
      p.trace interpretation y (.gate k) = p.trace interpretation x (.gate k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k hk hNotSOR hNotSAND
      by_cases hkOR : k ∈ ORRoot p root
      · rcases hOR k hkOR with ⟨w, hwIn, hwx, hwy⟩ | hAgree
        · rw [orInputs_sound hwIn x hwx, orInputs_sound hwIn y hwy]
        · have hInner : ∀ m2 : ℕ, ∀ j : Fin g, j.val ≤ m2 → j.val ≤ k.val →
              ORMember p root k j → p.trace interpretation y (.gate j) = p.trace interpretation x (.gate j) := by
            intro m2
            induction m2 using Nat.strong_induction_on with
            | h m2 ih2 =>
              intro j hj hjLeK hjMem
              rw [p.trace_gate, p.trace_gate]
              congr 1
              funext a
              cases hWire : (p.lines j).wires a with
              | input i =>
                simpa using hAgree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjMem, a, hWire⟩)
              | gate u =>
                have huLt := p.lt_of_lines_wires_eq_gate j a u hWire
                by_cases huSub : ORGate p root u ∧ u ∉ ORRoot p root
                · have huMem : ORMember p root k u := ORMember.child hjMem huSub.1 huSub.2 ⟨a, hWire⟩
                  exact ih2 u.val (by omega) u le_rfl (by omega) huMem
                · have huNotSOR : ¬ StrictOR u := by
                    rintro ⟨r1, _, huMem1, hne1⟩
                    have huOR := orMember_is_orGate huMem1
                    have huNotRoot : u ∉ ORRoot p root := by
                      intro huR
                      cases huMem1 with
                      | self => exact hne1 rfl
                      | child _ _ hNR _ => exact hNR huR
                    exact huSub ⟨huOR, huNotRoot⟩
                  have huNotSAND : ¬ StrictAND u := by
                    rintro ⟨r', _, huMem', hne'⟩
                    have hjAND := strictAND_only_from_same_root h0 h1 huMem' hne' hWire
                    have hjOp1 := (andMember_is_andGate hjAND).2.1
                    have hjOp2 := (orMember_is_orGate hjMem).2.1
                    rw [hjOp1] at hjOp2; cases hjOp2
                  exact ih u.val (by omega) u le_rfl huNotSOR huNotSAND
          exact hInner k.val k le_rfl le_rfl (ORMember.self hkOR)
      · by_cases hkAND : k ∈ ANDRoot p root
        · rcases hAND k hkAND with ⟨u, huIn, hux, huy⟩ | hAgree
          · rw [andInputs_sound huIn x hux, andInputs_sound huIn y huy]
          · have hInner : ∀ m2 : ℕ, ∀ j : Fin g, j.val ≤ m2 → j.val ≤ k.val →
                ANDMember p root k j → p.trace interpretation y (.gate j) = p.trace interpretation x (.gate j) := by
              intro m2
              induction m2 using Nat.strong_induction_on with
              | h m2 ih2 =>
                intro j hj hjLeK hjMem
                rw [p.trace_gate, p.trace_gate]
                congr 1
                funext a
                cases hWire : (p.lines j).wires a with
                | input i =>
                  simpa using hAgree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjMem, a, hWire⟩)
                | gate u =>
                  have huLt := p.lt_of_lines_wires_eq_gate j a u hWire
                  by_cases huSub : ANDGate p root u ∧ u ∉ ANDRoot p root
                  · have huMem : ANDMember p root k u := ANDMember.child hjMem huSub.1 huSub.2 ⟨a, hWire⟩
                    exact ih2 u.val (by omega) u le_rfl (by omega) huMem
                  · have huNotSAND : ¬ StrictAND u := by
                      rintro ⟨r1, _, huMem1, hne1⟩
                      have huAND := andMember_is_andGate huMem1
                      have huNotRoot : u ∉ ANDRoot p root := by
                        intro huR
                        cases huMem1 with
                        | self => exact hne1 rfl
                        | child _ _ hNR _ => exact hNR huR
                      exact huSub ⟨huAND, huNotRoot⟩
                    have huNotSOR : ¬ StrictOR u := by
                      rintro ⟨r, _, huMem, hne⟩
                      have hjOR := strictOR_only_from_same_root h0 h1 huMem hne hWire
                      have hjOp1 := (orMember_is_orGate hjOR).2.1
                      have hjOp2 := (andMember_is_andGate hjMem).2.1
                      rw [hjOp1] at hjOp2; cases hjOp2
                    exact ih u.val (by omega) u le_rfl huNotSOR huNotSAND
            exact hInner k.val k le_rfl le_rfl (ANDMember.self hkAND)
        · have hkStop : k ∈ StopGate p root := by
            by_contra hkNotS
            have hbf := not_badFlip_of_not_cutGate (fun hc => hkNotS (cutGate_subset_stopGate _ _ hc))
            rcases four_way_of_not_badFlip h0 h1 hbf with hDA | hDO | hPA | hPO
            · have hkANDGate : ANDGate p root k := ⟨hkNotS, hDA.1, hDA.2.2⟩
              obtain ⟨r, hrR, hrMem⟩ := andGate_mem_andMember h0 h1 g k (by omega) hkANDGate
              by_cases hEq : k = r
              · subst hEq; exact hkAND hrR
              · exact hNotSAND ⟨r, hrR, hrMem, hEq⟩
            · have hkORGate : ORGate p root k := ⟨hkNotS, hDO.1, hDO.2.1⟩
              obtain ⟨r, hrR, hrMem⟩ := orGate_mem_orMember h0 h1 g k (by omega) hkORGate
              by_cases hEq : k = r
              · subst hEq; exact hkOR hrR
              · exact hNotSOR ⟨r, hrR, hrMem, hEq⟩
            · have hkANDGate : ANDGate p root k := ⟨hkNotS, hPA.1, hPA.2.2⟩
              obtain ⟨r, hrR, hrMem⟩ := andGate_mem_andMember h0 h1 g k (by omega) hkANDGate
              by_cases hEq : k = r
              · subst hEq; exact hkAND hrR
              · exact hNotSAND ⟨r, hrR, hrMem, hEq⟩
            · have hkORGate : ORGate p root k := ⟨hkNotS, hPO.1, hPO.2.1⟩
              obtain ⟨r, hrR, hrMem⟩ := orGate_mem_orMember h0 h1 g k (by omega) hkORGate
              by_cases hEq : k = r
              · subst hEq; exact hkOR hrR
              · exact hNotSOR ⟨r, hrR, hrMem, hEq⟩
          rcases hStop k hkStop with hArgs | hEq
          · rw [p.trace_gate, p.trace_gate]
            congr 1
            funext a
            cases hWire : (p.lines k).wires a with
            | input i =>
              simpa using hArgs a i hWire
            | gate u =>
              have huLt := p.lt_of_lines_wires_eq_gate k a u hWire
              have huNotSOR : ¬ StrictOR u := by
                rintro ⟨r, hrR, huMem, hne⟩
                have hkMem := strictOR_only_from_same_root h0 h1 huMem hne hWire
                by_cases hEq : k = r
                · subst hEq; exact hkOR hrR
                · exact hNotSOR ⟨r, hrR, hkMem, hEq⟩
              have huNotSAND : ¬ StrictAND u := by
                rintro ⟨r', hrR', huMem', hne'⟩
                have hkMem' := strictAND_only_from_same_root h0 h1 huMem' hne' hWire
                by_cases hEq : k = r'
                · subst hEq; exact hkAND hrR'
                · exact hNotSAND ⟨r', hrR', hkMem', hEq⟩
              exact ih u.val (by omega) u le_rfl huNotSOR huNotSAND
          · exact hEq
  cases hRoot : root with
  | input i =>
    exfalso
    have hV := hRoot ▸ h0
    simp [cornerValue_input] at hV
  | gate k0 =>
    have hk0NotSOR : ¬ StrictOR k0 := by
      rintro ⟨r, hr, hMem, hne⟩
      have hLt := (orMember_le hMem).2 hne
      have hPre := needCorner_precedes_root ((orRoot_is_orGate hr).2.2)
      rw [hRoot] at hPre
      change r.val + 1 ≤ k0.val + 1 at hPre
      omega
    have hk0NotSAND : ¬ StrictAND k0 := by
      rintro ⟨r', hr', hMem', hne'⟩
      have hLt := (andMember_le hMem').2 hne'
      have hPre := needCorner_precedes_root ((andRoot_is_andGate hr').2.2)
      rw [hRoot] at hPre
      change r'.val + 1 ≤ k0.val + 1 at hPre
      omega
    exact hMain k0.val k0 le_rfl hk0NotSOR hk0NotSAND

theorem stopInputs_perturbation_invariant {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (x y : BitString n)
    (hCut : ∀ i ∈ stopInputs p root, y i = x i)
    (hOR : ∀ r ∈ ORRoot p root,
      (∃ w ∈ orInputs p root r, x w = true ∧ y w = true) ∨
      (∀ i ∈ orInputs p root r, y i = x i))
    (hAND : ∀ r' ∈ ANDRoot p root,
      (∃ u ∈ andInputs p root r', x u = false ∧ y u = false) ∨
      (∀ i ∈ andInputs p root r', y i = x i)) :
    p.trace interpretation y root = p.trace interpretation x root :=
  stopReaders_perturbation_invariant h0 h1 x y
    (fun _ hk => Or.inl fun a i ha => hCut i (stopInput_mem_of_wire hk a ha)) hOR hAND

theorem cutInputs_perturbation_invariant {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (x y : BitString n)
    (hCut : ∀ i ∈ cutInputs p root, y i = x i)
    (hOR : ∀ r ∈ ORRoot p root,
      (∃ w ∈ orInputs p root r, x w = true ∧ y w = true) ∨
      (∀ i ∈ orInputs p root r, y i = x i))
    (hAND : ∀ r' ∈ ANDRoot p root,
      (∃ u ∈ andInputs p root r', x u = false ∧ y u = false) ∨
      (∀ i ∈ andInputs p root r', y i = x i)) :
    p.trace interpretation y root = p.trace interpretation x root :=
  stopInputs_perturbation_invariant h0 h1 x y
    (fun i hi => hCut i (stopInputs_subset_cutInputs p root hi)) hOR hAND

theorem structured_perturbation_invariant {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    (x y : BitString n)
    (hOut : ∀ i ∉ structuredInputs p root, y i = x i)
    (hOR : ∀ r ∈ ORRoot p root,
      (∃ w ∈ orInputs p root r, x w = true ∧ y w = true) ∨
      (∀ i ∈ orInputs p root r, y i = x i))
    (hAND : ∀ r' ∈ ANDRoot p root,
      (∃ u ∈ andInputs p root r', x u = false ∧ y u = false) ∨
      (∀ i ∈ andInputs p root r', y i = x i)) :
    p.trace interpretation y root = p.trace interpretation x root :=
  cutInputs_perturbation_invariant h0 h1 x y
    (fun i hiCut => hOut i (fun hiS => structuredInputs_not_cut hiS hiCut)) hOR hAND

/-- Complete Case-2 monotone forest decomposition theorem for sparse two-corner circuits. -/
theorem clean_case2_structure {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hf0 : f (fun _ => false) = true) (hf1 : f (fun _ => true) = true) :
    ∃ (T_OR T_AND : Finset (Fin c.size)) (S_in : Finset (Fin n)),
      T_OR.card + T_AND.card ≤ 10 * B + 1442 * slack c.program (c.outputs 0) ∧
      n ≤ S_in.card + 14 * B + 1671 * slack c.program (c.outputs 0) ∧
      (∀ r1 ∈ T_OR, ∀ r2 ∈ T_OR, r1 ≠ r2 →
        Disjoint (orInputs c.program (c.outputs 0) r1) (orInputs c.program (c.outputs 0) r2)) ∧
      (∀ r1 ∈ T_AND, ∀ r2 ∈ T_AND, r1 ≠ r2 →
        Disjoint (andInputs c.program (c.outputs 0) r1) (andInputs c.program (c.outputs 0) r2)) ∧
      (∀ i ∈ S_in, (∃ r ∈ T_OR, i ∈ orInputs c.program (c.outputs 0) r) ∧
        (∃ r' ∈ T_AND, i ∈ andInputs c.program (c.outputs 0) r')) ∧
      (∀ x y : BitString n,
        (∀ i ∉ S_in, y i = x i) →
        (∀ r ∈ T_OR,
          (∃ w ∈ orInputs c.program (c.outputs 0) r, x w = true ∧ y w = true) ∨
          (∀ i ∈ orInputs c.program (c.outputs 0) r, y i = x i)) →
        (∀ r' ∈ T_AND,
          (∃ u ∈ andInputs c.program (c.outputs 0) r', x u = false ∧ y u = false) ∨
          (∀ i ∈ andInputs c.program (c.outputs 0) r', y i = x i)) →
        c.eval interpretation y 0 = c.eval interpretation x 0) := by
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc (fun _ => false)) 0).trans hf0
  have h1 : cornerValue p true root = true := (congrFun (hc (fun _ => true)) 0).trans hf1
  refine ⟨ORRoot p root, ANDRoot p root, structuredInputs p root,
    card_orRoot_add_andRoot_le c hc hSparse hf0 hf1,
    card_structuredInputs_ge c hc hSparse hf0 hf1,
    fun _ _ _ _ hne => orInputs_disjoint h0 hne,
    fun _ _ _ _ hne => andInputs_disjoint h1 hne,
    fun i hi => ⟨structuredInputs_mem_orInputs hi, structuredInputs_mem_andInputs hi⟩,
    fun x y hOut hOR hAND => structured_perturbation_invariant h0 h1 x y hOut hOR hAND⟩

end PvsNP.Frontier.MonotoneForest

#print axioms PvsNP.Frontier.MonotoneForest.stopTargets_eq_image_ports
#print axioms PvsNP.Frontier.MonotoneForest.card_dualCutNodes_le
#print axioms PvsNP.Frontier.MonotoneForest.card_stopInputs_and_roots_le_ports
#print axioms PvsNP.Frontier.MonotoneForest.card_segTopOR_le
#print axioms PvsNP.Frontier.MonotoneForest.card_segTopAND_le
#print axioms PvsNP.Frontier.MonotoneForest.card_orRoot_add_andRoot_le
#print axioms PvsNP.Frontier.MonotoneForest.card_structuredInputs_ge
#print axioms PvsNP.Frontier.MonotoneForest.eval_eq_of_cutInputs_and_roots
#print axioms PvsNP.Frontier.MonotoneForest.cutInputs_perturbation_invariant
#print axioms PvsNP.Frontier.MonotoneForest.structured_perturbation_invariant
#print axioms PvsNP.Frontier.MonotoneForest.clean_case2_structure
