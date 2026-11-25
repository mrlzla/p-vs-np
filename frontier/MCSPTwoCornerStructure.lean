module

public import MCSPRestrictions

/-! Separate-corner certificate accounting and gate classification for sparse circuits. -/

@[expose] public section

namespace PvsNP.Frontier.TwoCornerStructure

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates

variable {n g : ℕ}

/-- Demands traced separately from one constant-input certificate (`b = false` or `b = true`). -/
inductive NeedCorner (p : Program signature n g) (root : Wire n g) (b : Bool) :
    Wire n g × Bool → Prop where
  | output : NeedCorner p root b (root, true)
  | argument {k : Fin g} (h : NeedCorner p root b (.gate k, cornerValue p b (.gate k)))
      {key : Wire n g × Bool} (ha : key ∈ cornerArguments p k b) : NeedCorner p root b key

/-- Union of demands from both constant-input certificates. -/
def Need (p : Program signature n g) (root : Wire n g) (key : Wire n g × Bool) : Prop :=
  NeedCorner p root false key ∨ NeedCorner p root true key

/-- States requested at gate `k` by the `b`-corner certificate. -/
noncomputable def reqCorner (p : Program signature n g) (root : Wire n g) (b : Bool) (k : Fin g) :
    Finset (Wire n g × Bool) := open scoped Classical in
  if NeedCorner p root b (.gate k, cornerValue p b (.gate k)) then cornerArguments p k b else ∅

/-- Distinct states requested at gate `k` across both constant-input certificates. -/
noncomputable def req (p : Program signature n g) (root : Wire n g) (k : Fin g) :
    Finset (Wire n g × Bool) :=
  reqCorner p root false k ∪ reqCorner p root true k

noncomputable abbrev valSet (p : Program signature n g) (root : Wire n g) (k : Fin g) :
    Finset Bool :=
  stateValues (Need p root) (.gate k)

noncomputable def unused (p : Program signature n g) (root : Wire n g) (k : Fin g) : ℕ :=
  (valSet p root k).card + 1 - (req p root k).card

noncomputable def allArgs (p : Program signature n g) (root : Wire n g) : Finset (Wire n g × Bool) :=
  open scoped Classical in (Finset.univ : Finset (Fin g)).biUnion (req p root)

noncomputable def shared (p : Program signature n g) (root : Wire n g) : ℕ :=
  (∑ k : Fin g, (req p root k).card) - (allArgs p root).card

noncomputable def slack (p : Program signature n g) (root : Wire n g) : ℕ :=
  shared p root + ∑ k : Fin g, unused p root k

noncomputable def needInputs (p : Program signature n g) (root : Wire n g) (b : Bool) :
    Finset (Fin n) := open scoped Classical in
  Finset.univ.filter fun i => NeedCorner p root b (.input i, b)

@[simp] theorem cornerValue_input (p : Program signature n g) (b : Bool) (i : Fin n) :
    cornerValue p b (.input i) = b := rfl

theorem needCorner_eq_cornerValue {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {key : Wire n g × Bool}
    (h : NeedCorner p root b key) : key.2 = cornerValue p b key.1 := by
  induction h with
  | output => exact hRoot.symm
  | argument _ ha =>
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
    rfl

theorem needCorner_input_eq {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {i : Fin n} {v : Bool}
    (h : NeedCorner p root b (.input i, v)) : v = b :=
  (needCorner_eq_cornerValue hRoot h).trans (cornerValue_input p b i)

theorem need_gate_eq_false {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (h : Need p root (.gate k, false)) :
    (NeedCorner p root false (.gate k, false) ∧ cornerValue p false (.gate k) = false) ∨
      (NeedCorner p root true (.gate k, false) ∧ cornerValue p true (.gate k) = false) := by
  rcases h with hf | ht
  · exact Or.inl ⟨hf, (needCorner_eq_cornerValue h0 hf).symm⟩
  · exact Or.inr ⟨ht, (needCorner_eq_cornerValue h1 ht).symm⟩

theorem need_gate_eq_true {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (h : Need p root (.gate k, true)) :
    (NeedCorner p root false (.gate k, true) ∧ cornerValue p false (.gate k) = true) ∨
      (NeedCorner p root true (.gate k, true) ∧ cornerValue p true (.gate k) = true) := by
  rcases h with hf | ht
  · exact Or.inl ⟨hf, (needCorner_eq_cornerValue h0 hf).symm⟩
  · exact Or.inr ⟨ht, (needCorner_eq_cornerValue h1 ht).symm⟩

theorem agrees_on_needCorner (p : Program signature n g) (root : Wire n g) (b : Bool)
    (hRoot : cornerValue p b root = true) (x : BitString n)
    (agree : ∀ i ∈ needInputs p root b, x i = b) : p.trace interpretation x root = true := by
  classical
  have hTrace : ∀ w, NeedCorner p root b (w, cornerValue p b w) →
      p.trace interpretation x w = cornerValue p b w := by
    intro w
    refine p.wire_induction (P := fun w => NeedCorner p root b (w, cornerValue p b w) →
      p.trace interpretation x w = cornerValue p b w) ?_ ?_ w
    · intro i hi
      rw [cornerValue_input] at hi ⊢
      exact agree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro k ih hk
      rw [p.trace_gate, cornerValue_gate]
      apply agrees_of_selectedPins
      intro a ha
      exact ih a (NeedCorner.argument hk (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
  exact (hTrace root (hRoot.symm ▸ NeedCorner.output)).trans hRoot

theorem card_needInputs_ge_of_sparse {f : BooleanFunction n} {B : ℕ}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (b : Bool) (hb : f (fun _ => b) = true) :
    n ≤ (needInputs c.program (c.outputs 0) b).card + B := by
  classical
  let fixed := needInputs c.program (c.outputs 0) b
  let free := (Finset.univ : Finset (Fin n)) \ fixed
  let center : BitString n := fun _ => b
  have hRoot : cornerValue c.program b (c.outputs 0) = true := by
    change c.eval interpretation center 0 = true
    exact (congrFun (hc center) 0).trans hb
  let embed (u : free → Bool) (i : Fin n) : Bool :=
    if hi : i ∈ free then u ⟨i, hi⟩ else b
  have hAcc (u : free → Bool) : embed u ∈ acceptingTables f := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hTrace := agrees_on_needCorner c.program (c.outputs 0) b hRoot (embed u) fun i hi => by
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
  have hCard := (Fintype.card_le_of_injective into hInj).trans (by simpa [Fintype.card_coe] using hSparse)
  simp only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] at hCard
  have hFree : free.card ≤ B := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hCard
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ fixed)
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  change free.card + fixed.card = n at hSplit
  change n ≤ fixed.card + B
  omega

theorem card_req_le (p : Program signature n g) (root : Wire n g) (k : Fin g) :
    (req p root k).card ≤ (valSet p root k).card + 1 := by
  classical
  let v0 := cornerValue p false (.gate k)
  let v1 := cornerValue p true (.gate k)
  let S := valSet p root k
  have hv (b : Bool) : b ∈ S ↔ Need p root (.gate k, b) := by simp [S, stateValues]
  have hOne (b : Bool) : (cornerArguments p k b).card ≤ 2 := card_argumentStates_le ..
  have hUnion : (cornerArguments p k false ∪ cornerArguments p k true).card ≤
      if v0 = v1 then 2 else 3 := by
    have h := union_bound (p.lines k).op (p.lines k).wires
      (fun a => cornerValue p false ((p.lines k).wires a))
      (fun a => cornerValue p true ((p.lines k).wires a))
    simpa only [v0, v1, cornerArguments, cornerValue_gate] using h
  change ((if NeedCorner p root false (.gate k, v0) then cornerArguments p k false else ∅) ∪
    (if NeedCorner p root true (.gate k, v1) then cornerArguments p k true else ∅)).card ≤ S.card + 1
  by_cases h0 : NeedCorner p root false (.gate k, v0) <;>
    by_cases h1 : NeedCorner p root true (.gate k, v1) <;> simp [h0, h1]
  · by_cases heq : v0 = v1
    · have hcard := Finset.card_pos.mpr ⟨v0, (hv _).mpr (Or.inl h0)⟩
      simp [heq] at hUnion
      omega
    · have hset : ({v0, v1} : Finset Bool) ⊆ S := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact (hv _).mpr (Or.inl h0)
        · exact (hv _).mpr (Or.inr h1)
      have hcard := Finset.card_le_card hset
      simp [heq] at hUnion hcard
      omega
  · have hcard := Finset.card_pos.mpr ⟨v0, (hv _).mpr (Or.inl h0)⟩
    have hh := hOne false
    omega
  · have hcard := Finset.card_pos.mpr ⟨v1, (hv _).mpr (Or.inr h1)⟩
    have hh := hOne true
    omega

def wireOrder : Wire n g → ℕ
  | .input _ => 0
  | .gate k => k.val + 1

theorem cornerArg_precedes (p : Program signature n g) (k : Fin g) (b : Bool)
    {key : Wire n g × Bool} (h : key ∈ cornerArguments p k b) :
    wireOrder key.1 < wireOrder (.gate k : Wire n g) := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
  change wireOrder ((p.lines k).wires a) < k.val + 1
  cases hWire : (p.lines k).wires a with
  | input _ => simp [wireOrder]
  | gate j => exact Nat.succ_lt_succ (p.lt_of_lines_wires_eq_gate k a j hWire)

theorem needCorner_precedes_root {p : Program signature n g} {root : Wire n g} {b : Bool}
    {key : Wire n g × Bool} (h : NeedCorner p root b key) : wireOrder key.1 ≤ wireOrder root := by
  induction h with
  | output => exact le_rfl
  | argument _ ha ih => exact (cornerArg_precedes p _ b ha).le.trans ih

theorem stateSet_need_eq (p : Program signature n g) (root : Wire n g) :
    stateSet (Need p root) = insert (root, true) (allArgs p root) := by
  classical
  ext key
  constructor
  · intro hk
    rcases (Finset.mem_filter.mp hk).2 with h | h
    · cases h with
      | output => exact Finset.mem_insert_self ..
      | @argument k hGate key ha =>
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
          Finset.mem_union_left _ (by simp [reqCorner, hGate, ha])⟩)
    · cases h with
      | output => exact Finset.mem_insert_self ..
      | @argument k hGate key ha =>
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _,
          Finset.mem_union_right _ (by simp [reqCorner, hGate, ha])⟩)
  · intro hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hk with rfl | hArg
    · exact Or.inl NeedCorner.output
    · obtain ⟨k, _, hReq⟩ := Finset.mem_biUnion.mp hArg
      rcases Finset.mem_union.mp hReq with h0 | h1
      · by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
        · simp only [reqCorner, hg, ite_true] at h0
          exact Or.inl (NeedCorner.argument hg h0)
        · simp [reqCorner, hg] at h0
      · by_cases hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
        · simp only [reqCorner, hg, ite_true] at h1
          exact Or.inr (NeedCorner.argument hg h1)
        · simp [reqCorner, hg] at h1

theorem root_notMem_allArgs (p : Program signature n g) (root : Wire n g) :
    (root, true) ∉ allArgs p root := by
  classical
  intro hr
  obtain ⟨k, _, hReq⟩ := Finset.mem_biUnion.mp hr
  have hlt : wireOrder root < wireOrder root := by
    rcases Finset.mem_union.mp hReq with h0 | h1
    · by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
      · simp only [reqCorner, hg, ite_true] at h0
        exact (cornerArg_precedes p k false h0).trans_le (needCorner_precedes_root hg)
      · simp [reqCorner, hg] at h0
    · by_cases hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
      · simp only [reqCorner, hg, ite_true] at h1
        exact (cornerArg_precedes p k true h1).trans_le (needCorner_precedes_root hg)
      · simp [reqCorner, hg] at h1
  exact Nat.lt_irrefl _ hlt

theorem needInputs_add_slack_eq (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (needInputs p root false).card + (needInputs p root true).card + slack p root = g + 1 := by
  classical
  have hState := card_stateSet (Need p root)
  rw [stateSet_need_eq, Finset.card_insert_of_notMem (root_notMem_allArgs p root)] at hState
  have hInFalse : stateInputs (Need p root) false = needInputs p root false := by
    ext i
    unfold stateInputs needInputs
    rw [Finset.mem_filter, Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    exact ⟨fun h => by rcases h with hf | ht; exact hf; exact absurd (needCorner_input_eq h1 ht) (by decide),
      Or.inl⟩
  have hInTrue : stateInputs (Need p root) true = needInputs p root true := by
    ext i
    unfold stateInputs needInputs
    rw [Finset.mem_filter, Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    exact ⟨fun h => by rcases h with hf | ht; exact absurd (needCorner_input_eq h0 hf) (by decide); exact ht,
      Or.inr⟩
  rw [hInFalse, hInTrue] at hState
  have hBal (k : Fin g) : (req p root k).card + unused p root k = (valSet p root k).card + 1 := by
    have hLe := card_req_le p root k
    unfold unused
    omega
  have hSumBal : (∑ k : Fin g, (req p root k).card) + (∑ k : Fin g, unused p root k) =
      (∑ k : Fin g, (valSet p root k).card) + g := by
    simpa [Finset.sum_add_distrib] using congrArg (fun f : Fin g → ℕ => ∑ k, f k) (funext hBal)
  have hDistinct : (allArgs p root).card ≤ ∑ k : Fin g, (req p root k).card :=
    Finset.card_biUnion_le
  have hSumEq : (∑ k : Fin g, (stateValues (Need p root) (.gate k)).card) =
      ∑ k : Fin g, (valSet p root k).card := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rfl
  unfold slack shared
  omega

/-- Universal edge-counting bound across gates and requested states. -/
theorem sum_card_inter_req_le (p : Program signature n g) (root : Wire n g)
    (V : Finset (Fin g)) (S : Finset (Wire n g × Bool)) :
    ∑ k ∈ V, (req p root k ∩ S).card ≤ S.card + shared p root := by
  classical
  have hSub : ∑ k ∈ V, (req p root k ∩ S).card ≤
      ∑ k : Fin g, (req p root k ∩ S).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ V)
  have hSplit (k : Fin g) :
      (req p root k ∩ S).card + (req p root k \ S).card = (req p root k).card :=
    Finset.card_inter_add_card_sdiff (req p root k) S
  have hSumSplit : (∑ k : Fin g, (req p root k ∩ S).card) +
      (∑ k : Fin g, (req p root k \ S).card) = ∑ k : Fin g, (req p root k).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hSplit k
  have hAllSplit : (allArgs p root ∩ S).card + (allArgs p root \ S).card =
      (allArgs p root).card := Finset.card_inter_add_card_sdiff _ _
  have hInterLe : (allArgs p root ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
  have hDiffSub : allArgs p root \ S ⊆ (Finset.univ : Finset (Fin g)).biUnion (fun k => req p root k \ S) := by
    intro key hKey
    obtain ⟨hA, hNS⟩ := Finset.mem_sdiff.mp hKey
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hA
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hk, hNS⟩⟩
  have hDiffLe : (allArgs p root \ S).card ≤ ∑ k : Fin g, (req p root k \ S).card :=
    (Finset.card_le_card hDiffSub).trans Finset.card_biUnion_le
  have hDistinct : (allArgs p root).card ≤ ∑ k : Fin g, (req p root k).card :=
    Finset.card_biUnion_le
  unfold shared
  omega

/-- Convenience wrapper: if every gate in `V` requests at least `c` states inside `S`. -/
theorem mul_card_le_of_inter_req (p : Program signature n g) (root : Wire n g)
    (V : Finset (Fin g)) (S : Finset (Wire n g × Bool)) (c : ℕ)
    (hc : ∀ k ∈ V, c ≤ (req p root k ∩ S).card) :
    c * V.card ≤ S.card + shared p root := by
  calc
    c * V.card = ∑ _k ∈ V, c := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ k ∈ V, (req p root k ∩ S).card := Finset.sum_le_sum hc
    _ ≤ S.card + shared p root := sum_card_inter_req_le p root V S

/-- Subset of requested states with value `b`. -/
noncomputable def allArgsBool (p : Program signature n g) (root : Wire n g) (b : Bool) :
    Finset (Wire n g × Bool) := open scoped Classical in
  (allArgs p root).filter fun s => s.2 = b

/-- Polarity-specific edge-sharing count across requested states with value `b`. -/
noncomputable def sharedBool (p : Program signature n g) (root : Wire n g) (b : Bool) : ℕ :=
  open scoped Classical in
  (∑ k : Fin g, ((req p root k).filter fun s => s.2 = b).card) - (allArgsBool p root b).card

theorem card_allArgsBool_le_sum (p : Program signature n g) (root : Wire n g) (b : Bool) :
    (allArgsBool p root b).card ≤ ∑ k : Fin g, ((req p root k).filter fun s => s.2 = b).card := by
  classical
  have hSub : allArgsBool p root b ⊆
      (Finset.univ : Finset (Fin g)).biUnion fun k => (req p root k).filter fun s => s.2 = b := by
    intro s hs
    obtain ⟨hA, hb⟩ := Finset.mem_filter.mp hs
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hA
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hk, hb⟩⟩
  exact (Finset.card_le_card hSub).trans Finset.card_biUnion_le

theorem sharedBool_add (p : Program signature n g) (root : Wire n g) :
    sharedBool p root false + sharedBool p root true = shared p root := by
  classical
  have hAllSplit : (allArgsBool p root false).card + (allArgsBool p root true).card =
      (allArgs p root).card := by
    have hDisj : Disjoint (allArgsBool p root false) (allArgsBool p root true) := by
      rw [Finset.disjoint_left]
      intro s hF hT
      have hf := (Finset.mem_filter.mp hF).2
      have ht := (Finset.mem_filter.mp hT).2
      rw [hf] at ht; cases ht
    have hEq : allArgsBool p root false ∪ allArgsBool p root true = allArgs p root := by
      ext s
      simp only [allArgsBool, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        cases hs : s.2
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr ⟨h, rfl⟩
    rw [← Finset.card_union_of_disjoint hDisj, hEq]
  have hReqSplit (k : Fin g) :
      ((req p root k).filter fun s => s.2 = false).card +
        ((req p root k).filter fun s => s.2 = true).card = (req p root k).card := by
    have hDisj : Disjoint ((req p root k).filter fun s => s.2 = false)
        ((req p root k).filter fun s => s.2 = true) := by
      rw [Finset.disjoint_left]
      intro s hF hT
      have hf := (Finset.mem_filter.mp hF).2
      have ht := (Finset.mem_filter.mp hT).2
      rw [hf] at ht; cases ht
    have hEq : ((req p root k).filter fun s => s.2 = false) ∪
        ((req p root k).filter fun s => s.2 = true) = req p root k := by
      ext s
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        cases hs : s.2
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr ⟨h, rfl⟩
    rw [← Finset.card_union_of_disjoint hDisj, hEq]
  have hSumReq : (∑ k : Fin g, ((req p root k).filter fun s => s.2 = false).card) +
      (∑ k : Fin g, ((req p root k).filter fun s => s.2 = true).card) =
      ∑ k : Fin g, (req p root k).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hReqSplit k
  have hLeF := card_allArgsBool_le_sum p root false
  have hLeT := card_allArgsBool_le_sum p root true
  unfold shared sharedBool
  omega

/-- Sharp polarity-specific edge-counting bound against `allArgs p root ∩ S`. -/
theorem sum_card_inter_req_le_allArgs_bool (p : Program signature n g) (root : Wire n g) (b : Bool)
    (V : Finset (Fin g)) (S : Finset (Wire n g × Bool)) (hS : ∀ s ∈ S, s.2 = b) :
    ∑ k ∈ V, (req p root k ∩ S).card ≤ (allArgs p root ∩ S).card + sharedBool p root b := by
  classical
  let reqB (k : Fin g) : Finset (Wire n g × Bool) := (req p root k).filter fun s => s.2 = b
  have hReqInter (k : Fin g) : req p root k ∩ S = reqB k ∩ S := by
    ext s
    simp only [Finset.mem_inter, Finset.mem_filter, reqB]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, hS s h2⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
  have hAllInter : allArgs p root ∩ S = allArgsBool p root b ∩ S := by
    ext s
    simp only [Finset.mem_inter, Finset.mem_filter, allArgsBool]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, hS s h2⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
  have hSub : ∑ k ∈ V, (req p root k ∩ S).card ≤ ∑ k : Fin g, (reqB k ∩ S).card := by
    calc
      ∑ k ∈ V, (req p root k ∩ S).card = ∑ k ∈ V, (reqB k ∩ S).card :=
        Finset.sum_congr rfl fun k _ => congrArg Finset.card (hReqInter k)
      _ ≤ ∑ k : Fin g, (reqB k ∩ S).card := Finset.sum_le_sum_of_subset (Finset.subset_univ V)
  have hSplit (k : Fin g) : (reqB k ∩ S).card + (reqB k \ S).card = (reqB k).card :=
    Finset.card_inter_add_card_sdiff (reqB k) S
  have hSumSplit : (∑ k : Fin g, (reqB k ∩ S).card) + (∑ k : Fin g, (reqB k \ S).card) =
      ∑ k : Fin g, (reqB k).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hSplit k
  have hAllSplit : (allArgsBool p root b ∩ S).card + (allArgsBool p root b \ S).card =
      (allArgsBool p root b).card := Finset.card_inter_add_card_sdiff _ _
  have hDiffSub : allArgsBool p root b \ S ⊆ (Finset.univ : Finset (Fin g)).biUnion (fun k => reqB k \ S) := by
    intro s hs
    obtain ⟨hA, hNS⟩ := Finset.mem_sdiff.mp hs
    obtain ⟨hArg, hb⟩ := Finset.mem_filter.mp hA
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hArg
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hk, hb⟩, hNS⟩⟩
  have hDiffLe : (allArgsBool p root b \ S).card ≤ ∑ k : Fin g, (reqB k \ S).card :=
    (Finset.card_le_card hDiffSub).trans Finset.card_biUnion_le
  have hDistinct := card_allArgsBool_le_sum p root b
  rw [hAllInter]
  unfold sharedBool
  dsimp only [reqB] at hSub hSumSplit hDiffLe
  omega

/-- Polarity-specific edge-counting wrapper against `S.card`. -/
theorem sum_card_inter_req_le_bool (p : Program signature n g) (root : Wire n g) (b : Bool)
    (V : Finset (Fin g)) (S : Finset (Wire n g × Bool)) (hS : ∀ s ∈ S, s.2 = b) :
    ∑ k ∈ V, (req p root k ∩ S).card ≤ S.card + sharedBool p root b :=
  (sum_card_inter_req_le_allArgs_bool p root b V S hS).trans
    (add_le_add (Finset.card_le_card Finset.inter_subset_right) le_rfl)

/-- A wire/value state requested by at least two gates. -/
def IsRepeatState (p : Program signature n g) (root : Wire n g) (key : Wire n g × Bool) : Prop :=
  2 ≤ (Finset.univ.filter fun k : Fin g => key ∈ req p root k).card

noncomputable def repeatStates (p : Program signature n g) (root : Wire n g) :
    Finset (Wire n g × Bool) := open scoped Classical in
  (allArgs p root).filter (IsRepeatState p root)

theorem mem_repeatStates_of_ne {p : Program signature n g} {root : Wire n g}
    {k1 k2 : Fin g} (hne : k1 ≠ k2) {key : Wire n g × Bool}
    (h1 : key ∈ req p root k1) (h2 : key ∈ req p root k2) :
    key ∈ repeatStates p root := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨k1, Finset.mem_univ _, h1⟩, ?_⟩
  have hSub : ({k1, k2} : Finset (Fin g)) ⊆ Finset.univ.filter fun k => key ∈ req p root k := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ‹_›⟩
  simpa [IsRepeatState, hne] using Finset.card_le_card hSub

theorem card_repeatStates_le_shared (p : Program signature n g) (root : Wire n g) :
    (repeatStates p root).card ≤ shared p root := by
  classical
  let count (key : Wire n g × Bool) := (Finset.univ.filter fun k : Fin g => key ∈ req p root k).card
  have hSum : ∑ key ∈ allArgs p root, count key = ∑ k : Fin g, (req p root k).card := by
    have h1 : ∑ key ∈ allArgs p root, count key =
        ∑ key ∈ allArgs p root, ∑ k : Fin g, if key ∈ req p root k then 1 else 0 := by
      refine Finset.sum_congr rfl fun key _ => ?_
      dsimp only [count]
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hSub : req p root k ⊆ allArgs p root :=
      Finset.subset_biUnion_of_mem _ (Finset.mem_univ k)
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSub]
  have hOne : ∀ key ∈ allArgs p root, 1 ≤ count key := by
    intro key hKey
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hKey
    exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
  have hTwo : ∀ key ∈ repeatStates p root, 2 ≤ count key :=
    fun key hKey => (Finset.mem_filter.mp hKey).2
  have hSub : repeatStates p root ⊆ allArgs p root := Finset.filter_subset _ _
  have hSplit := Finset.sum_sdiff hSub (f := count)
  have hRest : (allArgs p root \ repeatStates p root).card ≤
      ∑ key ∈ allArgs p root \ repeatStates p root, count key := by
    calc
      _ = ∑ _key ∈ allArgs p root \ repeatStates p root, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun key hKey => hOne key (Finset.mem_sdiff.mp hKey).1
  have hRep : 2 * (repeatStates p root).card ≤ ∑ key ∈ repeatStates p root, count key := by
    calc
      2 * (repeatStates p root).card = ∑ _key ∈ repeatStates p root, 2 := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hTwo
  have hAllCard : (repeatStates p root).card + (allArgs p root \ repeatStates p root).card =
      (allArgs p root).card := by
    rw [add_comm]
    exact Finset.card_sdiff_add_card_eq_card hSub
  unfold shared
  omega

/-- Gates with nonzero unused allowance. -/
noncomputable def badGates (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k => 1 ≤ unused p root k

theorem card_badGates_le (p : Program signature n g) (root : Wire n g) :
    (badGates p root).card ≤ ∑ k : Fin g, unused p root k := by
  classical
  calc
    (badGates p root).card = ∑ _k ∈ badGates p root, 1 := by simp
    _ ≤ ∑ k ∈ badGates p root, unused p root k :=
      Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2
    _ ≤ ∑ k : Fin g, unused p root k := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem card_badGates_le_slack (p : Program signature n g) (root : Wire n g) :
    (badGates p root).card ≤ slack p root :=
  (card_badGates_le p root).trans (Nat.le_add_left _ _)

/-! ### Op-parameterized helpers (avoid dependent-type casts on `p.lines k`) -/

def dualWireOf (p : Program signature n g) (fallback : Wire n g) :
    (op : Op) → (Fin (signature.Arity op) → Wire n g) → Wire n g
  | .and, wires => if cornerValue p false (wires 0) = false then wires 0 else wires 1
  | .or, wires => if cornerValue p true (wires 0) = true then wires 0 else wires 1
  | .not, wires => wires 0
  | .const _, _ => fallback

def sideWireOf (p : Program signature n g) (fallback : Wire n g) :
    (op : Op) → (Fin (signature.Arity op) → Wire n g) → Wire n g
  | .and, wires => if cornerValue p false (wires 0) = false then wires 1 else wires 0
  | .or, wires => if cornerValue p true (wires 0) = true then wires 1 else wires 0
  | .not, wires => wires 0
  | .const _, _ => fallback

def dualChild (p : Program signature n g) (k : Fin g) : Wire n g :=
  dualWireOf p (.gate k) (p.lines k).op (p.lines k).wires

def sideChild (p : Program signature n g) (k : Fin g) : Wire n g :=
  sideWireOf p (.gate k) (p.lines k).op (p.lines k).wires

private theorem op_const_args {op : Op} {v : Bool} (hOp : op = .const v)
    (wires : Fin (signature.Arity op) → Wire n g) (x : Fin (signature.Arity op) → Bool) :
    argumentStates op wires x = ∅ := by
  subst hOp; simp [argumentStates, selectedPins]

private theorem op_not_arg {op : Op} (hOp : op = .not)
    (wires : Fin (signature.Arity op) → Wire n g) (val : Wire n g → Bool)
    {key : Wire n g × Bool} (hKey : key ∈ argumentStates op wires fun a => val (wires a)) :
    key = (wires (Fin.cast (by rw [hOp]) (0 : Fin 1)), !(interpretation op fun a => val (wires a))) := by
  subst hOp
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
  have ha : a = 0 := Subsingleton.elim ..
  subst ha
  cases val (wires 0) <;> simp [interpretation]

private theorem op_bin_const_eval {op : Op} (hOp : op = .and ∨ op = .or)
    (wires : Fin (signature.Arity op) → Wire n g) (val : Wire n g → Bool)
    (hSame : ∀ a0 a1 : Fin (signature.Arity op), wires a0 = wires a1)
    {key : Wire n g × Bool} (hKey : key ∈ argumentStates op wires fun a => val (wires a)) :
    key = (wires (Fin.cast (by rcases hOp with rfl | rfl <;> rfl) (0 : Fin 2)),
      interpretation op fun a => val (wires a)) := by
  rcases hOp with rfl | rfl
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
    have h0 : wires a = wires 0 := hSame a 0
    have h1 : wires 1 = wires 0 := hSame 1 0
    refine Prod.ext h0 ?_
    change val (wires a) = (val (wires 0) && val (wires 1))
    rw [h0, h1]
    cases val (wires 0) <;> rfl
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
    have h0 : wires a = wires 0 := hSame a 0
    have h1 : wires 1 = wires 0 := hSame 1 0
    refine Prod.ext h0 ?_
    change val (wires a) = (val (wires 0) || val (wires 1))
    rw [h0, h1]
    cases val (wires 0) <;> rfl

private theorem op_and_true_all {op : Op} (hOp : op = .and)
    (wires : Fin (signature.Arity op) → Wire n g) (val : Wire n g → Bool)
    (hEval : interpretation op (fun a => val (wires a)) = true) :
    (∀ a, val (wires a) = true) ∧
      ∀ a, (wires a, true) ∈ argumentStates op wires fun s => val (wires s) := by
  subst hOp
  have hv0 : val (wires 0) = true := by
    cases h0 : val (wires 0) <;> cases h1 : val (wires 1) <;> simp_all [interpretation]
  have hv1 : val (wires 1) = true := by
    cases h0 : val (wires 0) <;> cases h1 : val (wires 1) <;> simp_all [interpretation]
  refine ⟨fun a => by fin_cases a <;> assumption, fun a => Finset.mem_image.mpr ⟨a, ?_, ?_⟩⟩
  · simp [selectedPins, hv0, hv1]
  · fin_cases a <;> simp [hv0, hv1]

private theorem op_or_false_all {op : Op} (hOp : op = .or)
    (wires : Fin (signature.Arity op) → Wire n g) (val : Wire n g → Bool)
    (hEval : interpretation op (fun a => val (wires a)) = false) :
    (∀ a, val (wires a) = false) ∧
      ∀ a, (wires a, false) ∈ argumentStates op wires fun s => val (wires s) := by
  subst hOp
  have hv0 : val (wires 0) = false := by
    cases h0 : val (wires 0) <;> cases h1 : val (wires 1) <;> simp_all [interpretation]
  have hv1 : val (wires 1) = false := by
    cases h0 : val (wires 0) <;> cases h1 : val (wires 1) <;> simp_all [interpretation]
  refine ⟨fun a => by fin_cases a <;> assumption, fun a => Finset.mem_image.mpr ⟨a, ?_, ?_⟩⟩
  · simp [selectedPins, hv0, hv1]
  · fin_cases a <;> simp [hv0, hv1]

private theorem op_or_true_one {op : Op} (hOp : op = .or)
    (wires : Fin (signature.Arity op) → Wire n g) (val : Wire n g → Bool)
    (hEval : interpretation op (fun a => val (wires a)) = true) :
    ∃ a, argumentStates op wires (fun s => val (wires s)) = {(wires a, true)} ∧
      val (wires a) = true := by
  subst hOp
  by_cases hv0 : val (wires 0) = true
  · refine ⟨0, ?_, hv0⟩
    simp [argumentStates, selectedPins, hv0]
  · have hv0f : val (wires 0) = false := Bool.eq_false_iff.mpr hv0
    have hv1 : val (wires 1) = true := by
      cases h1' : val (wires 1) <;> simp_all [interpretation]
    refine ⟨1, ?_, hv1⟩
    simp [argumentStates, selectedPins, hv0f, hv1]

private theorem op_and_false_one {op : Op} (hOp : op = .and)
    (wires : Fin (signature.Arity op) → Wire n g) (val : Wire n g → Bool)
    (hEval : interpretation op (fun a => val (wires a)) = false) :
    ∃ a, argumentStates op wires (fun s => val (wires s)) = {(wires a, false)} ∧
      val (wires a) = false := by
  subst hOp
  by_cases hv0 : val (wires 0) = false
  · refine ⟨0, ?_, hv0⟩
    simp [argumentStates, selectedPins, hv0]
  · have hv0t : val (wires 0) = true := Bool.eq_true_of_not_eq_false hv0
    have hv1 : val (wires 1) = false := by
      cases h1' : val (wires 1) <;> simp_all [interpretation]
    refine ⟨1, ?_, hv1⟩
    simp [argumentStates, selectedPins, hv0t, hv1]

private theorem op_arity_two {op : Op} (hOp : op = .and ∨ op = .or) :
    signature.Arity op = 2 := by
  rcases hOp with rfl | rfl <;> rfl

private theorem op_dual_is_wire {op : Op} (hOp : op = .and ∨ op = .or) (fallback : Wire n g)
    (wires : Fin (signature.Arity op) → Wire n g) :
    ∃ a, wires a = dualWireOf p fallback op wires := by
  rcases hOp with rfl | rfl
  · dsimp [dualWireOf]
    split
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · dsimp [dualWireOf]
    split
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem op_side_is_wire {op : Op} (hOp : op = .and ∨ op = .or) (fallback : Wire n g)
    (wires : Fin (signature.Arity op) → Wire n g) :
    ∃ a, wires a = sideWireOf p fallback op wires := by
  rcases hOp with rfl | rfl
  · dsimp [sideWireOf]
    split
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · dsimp [sideWireOf]
    split
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

private theorem op_dual_or_side {op : Op} (hOp : op = .and ∨ op = .or) (fallback : Wire n g)
    (wires : Fin (signature.Arity op) → Wire n g) (a : Fin (signature.Arity op)) :
    wires a = dualWireOf p fallback op wires ∨ wires a = sideWireOf p fallback op wires := by
  rcases hOp with rfl | rfl
  · dsimp [dualWireOf, sideWireOf]
    split <;> fin_cases a <;> simp
  · dsimp [dualWireOf, sideWireOf]
    split <;> fin_cases a <;> simp

private theorem op_dual_ne_side {op : Op} (hOp : op = .and ∨ op = .or) (fallback : Wire n g)
    (wires : Fin (signature.Arity op) → Wire n g)
    (hNe : ∀ a0 a1, a0 ≠ a1 → wires a0 ≠ wires a1) :
    dualWireOf p fallback op wires ≠ sideWireOf p fallback op wires := by
  rcases hOp with rfl | rfl
  · dsimp [dualWireOf, sideWireOf]
    split
    · exact hNe 0 1 (by decide)
    · exact hNe 1 0 (by decide)
  · dsimp [dualWireOf, sideWireOf]
    split
    · exact hNe 0 1 (by decide)
    · exact hNe 1 0 (by decide)

private theorem op_and_false_dual {op : Op} (hOp : op = .and) (fallback : Wire n g)
    (wires : Fin (signature.Arity op) → Wire n g)
    (hEval : interpretation op (fun a => cornerValue p false (wires a)) = false) :
    argumentStates op wires (fun a => cornerValue p false (wires a)) =
      {(dualWireOf p fallback op wires, false)} := by
  subst hOp
  dsimp [dualWireOf]
  by_cases hv0 : cornerValue p false (wires 0) = false
  · simp [argumentStates, selectedPins, hv0]
  · have hv0t : cornerValue p false (wires 0) = true := Bool.eq_true_of_not_eq_false hv0
    have hv1 : cornerValue p false (wires 1) = false := by
      cases h1' : cornerValue p false (wires 1) <;> simp_all [interpretation]
    simp [argumentStates, selectedPins, hv0t, hv1]

private theorem op_or_true_dual {op : Op} (hOp : op = .or) (fallback : Wire n g)
    (wires : Fin (signature.Arity op) → Wire n g)
    (hEval : interpretation op (fun a => cornerValue p true (wires a)) = true) :
    argumentStates op wires (fun a => cornerValue p true (wires a)) =
      {(dualWireOf p fallback op wires, true)} := by
  subst hOp
  dsimp [dualWireOf]
  by_cases hv0 : cornerValue p true (wires 0) = true
  · simp [argumentStates, selectedPins, hv0]
  · have hv0f : cornerValue p true (wires 0) = false := Bool.eq_false_iff.mpr hv0
    have hv1 : cornerValue p true (wires 1) = true := by
      cases h1' : cornerValue p true (wires 1) <;> simp_all [interpretation]
    simp [argumentStates, selectedPins, hv0f, hv1]

private theorem mem_valSet_of_mem_reqCorner {p : Program signature n g} {root : Wire n g}
    {b : Bool} {k : Fin g} {key : Wire n g × Bool} (h : key ∈ reqCorner p root b k) :
    cornerValue p b (.gate k) ∈ valSet p root k := by
  classical
  by_cases hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k))
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    cases b
    · exact Or.inl hg
    · exact Or.inr hg
  · simp [reqCorner, hg] at h

private theorem req_card_gt_of_not_bad {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ badGates p root) (w : Wire n g) (fn : Bool → Bool)
    (hMap : ∀ b (key : Wire n g × Bool), key ∈ reqCorner p root b k →
      key = (w, fn (cornerValue p b (.gate k)))) : False := by
  classical
  have hUn : unused p root k = 0 := by
    by_contra hne
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩)
  have hLe := card_req_le p root k
  have hReqEq : (req p root k).card = (valSet p root k).card + 1 := by
    unfold unused at hUn
    omega
  have hSub : req p root k ⊆ (valSet p root k).image fun v => (w, fn v) := by
    intro key hKey
    rcases Finset.mem_union.mp hKey with hL | hR
    · exact Finset.mem_image.mpr ⟨cornerValue p false (.gate k),
        mem_valSet_of_mem_reqCorner hL, (hMap false key hL).symm⟩
    · exact Finset.mem_image.mpr ⟨cornerValue p true (.gate k),
        mem_valSet_of_mem_reqCorner hR, (hMap true key hR).symm⟩
  have hCard := (Finset.card_le_card hSub).trans Finset.card_image_le
  omega

/-- Every gate outside `badGates` uses its full allowance and is a binary AND/OR on distinct wires. -/
theorem not_bad_structure (p : Program signature n g) (root : Wire n g)
    {k : Fin g} (hk : k ∉ badGates p root) :
    ((p.lines k).op = .and ∨ (p.lines k).op = .or) ∧
      (req p root k).card = (valSet p root k).card + 1 ∧
      1 ≤ (valSet p root k).card ∧
      (∀ a0 a1 : Fin (signature.Arity (p.lines k).op), a0 ≠ a1 →
        (p.lines k).wires a0 ≠ (p.lines k).wires a1) := by
  classical
  have hUn : unused p root k = 0 := by
    by_contra hne
    exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩)
  have hLe := card_req_le p root k
  have hReqEq : (req p root k).card = (valSet p root k).card + 1 := by
    unfold unused at hUn
    omega
  have hValPos : 1 ≤ (valSet p root k).card := by
    by_contra hZ
    have hV0 : (valSet p root k).card = 0 := by omega
    have hReq0 : (req p root k).card = 0 := by
      have hSub : req p root k ⊆ ∅ := by
        intro key hKey
        rcases Finset.mem_union.mp hKey with hL | hR
        · have hv := mem_valSet_of_mem_reqCorner hL
          rw [Finset.card_eq_zero.mp hV0] at hv
          exact False.elim (Finset.notMem_empty _ hv)
        · have hv := mem_valSet_of_mem_reqCorner hR
          rw [Finset.card_eq_zero.mp hV0] at hv
          exact False.elim (Finset.notMem_empty _ hv)
      exact Nat.eq_zero_of_le_zero (Finset.card_le_card hSub)
    omega
  have hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or := by
    cases hOpK : (p.lines k).op with
    | and => exact Or.inl rfl
    | or => exact Or.inr rfl
    | const v =>
      have hSub : req p root k = ∅ := by
        ext key
        simp only [req, Finset.mem_union, Finset.notMem_empty, iff_false, not_or]
        constructor
        · intro hK
          by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
          · simp only [reqCorner, hg, ite_true, cornerArguments] at hK
            rw [op_const_args hOpK] at hK
            exact Finset.notMem_empty _ hK
          · simp [reqCorner, hg] at hK
        · intro hK
          by_cases hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
          · simp only [reqCorner, hg, ite_true, cornerArguments] at hK
            rw [op_const_args hOpK] at hK
            exact Finset.notMem_empty _ hK
          · simp [reqCorner, hg] at hK
      rw [hSub, Finset.card_empty] at hReqEq
      omega
    | not =>
      let i0 : Fin (signature.Arity (p.lines k).op) := Fin.cast (by rw [hOpK]) (0 : Fin 1)
      exfalso
      apply req_card_gt_of_not_bad hk ((p.lines k).wires i0) Bool.not
      intro b key hKey
      by_cases hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k))
      · simp only [reqCorner, hg, ite_true, cornerArguments] at hKey
        have hEq := op_not_arg hOpK (p.lines k).wires (cornerValue p b) hKey
        rw [← cornerValue_gate p b k] at hEq
        exact hEq
      · simp [reqCorner, hg] at hKey
  refine ⟨hOp, hReqEq, hValPos, ?_⟩
  intro a0 a1 hne heq
  have hTwo : ∀ a : Fin (signature.Arity (p.lines k).op), a = a0 ∨ a = a1 := by
    intro a
    have hCard : Fintype.card (Fin (signature.Arity (p.lines k).op)) = 2 := by
      rw [Fintype.card_fin, op_arity_two hOp]
    have hSub : ({a0, a1} : Finset _) = Finset.univ := Finset.eq_univ_of_card _ (by simp [hne, hCard])
    have hm : a ∈ ({a0, a1} : Finset _) := hSub.symm ▸ Finset.mem_univ a
    simpa using hm
  have hSame : ∀ x y : Fin (signature.Arity (p.lines k).op),
      (p.lines k).wires x = (p.lines k).wires y := by
    intro x y
    rcases hTwo x with rfl | rfl <;> rcases hTwo y with rfl | rfl <;> first | rfl | exact heq | exact heq.symm
  let i0 : Fin (signature.Arity (p.lines k).op) :=
    Fin.cast (by rcases hOp with h | h <;> rw [h]) (0 : Fin 2)
  apply req_card_gt_of_not_bad hk ((p.lines k).wires i0) id
  intro b key hKey
  by_cases hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k))
  · simp only [reqCorner, hg, ite_true, cornerArguments] at hKey
    have hEq := op_bin_const_eval hOp (p.lines k).wires (cornerValue p b) hSame hKey
    rw [← cornerValue_gate p b k] at hEq
    exact hEq
  · simp [reqCorner, hg] at hKey

/-- Gates whose polarity flips relative to the constant-input index in a certificate. -/
noncomputable def S0 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k => NeedCorner p root false (.gate k, true)

noncomputable def S1 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k => NeedCorner p root true (.gate k, false)

noncomputable def flipGates (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  (S0 p root ∪ S1 p root) \ badGates p root

noncomputable def badFlip (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  badGates p root ∪ flipGates p root

private theorem gate_of_needCorner_ne {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {w : Wire n g}
    (h : NeedCorner p root b (w, !b)) : ∃ j : Fin g, w = .gate j := by
  cases w with
  | gate j => exact ⟨j, rfl⟩
  | input i =>
    have he := needCorner_input_eq hRoot h
    cases b <;> cases he

private theorem and_true_req_both {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {k : Fin g} (hk : k ∉ badGates p root)
    (hOp : (p.lines k).op = .and) (hNeed : NeedCorner p root b (.gate k, true)) :
    (∀ a : Fin (signature.Arity (p.lines k).op),
      ((p.lines k).wires a, true) ∈ reqCorner p root b k) ∧
      2 ≤ (reqCorner p root b k).card := by
  classical
  have hVal : cornerValue p b (.gate k) = true := (needCorner_eq_cornerValue hRoot hNeed).symm
  have hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k)) := hVal.symm ▸ hNeed
  have hCorner := hVal
  rw [cornerValue_gate] at hCorner
  obtain ⟨_, hArg⟩ := op_and_true_all hOp (p.lines k).wires (cornerValue p b) hCorner
  have hMem : ∀ a, ((p.lines k).wires a, true) ∈ reqCorner p root b k := by
    intro a
    simp only [reqCorner, hg, ite_true, cornerArguments]
    exact hArg a
  refine ⟨hMem, ?_⟩
  have hInj : Function.Injective (fun a => ((p.lines k).wires a, true)) := by
    intro a0 a1 he
    by_contra hne
    exact (not_bad_structure p root hk).2.2.2 a0 a1 hne (congrArg Prod.fst he)
  have hSub : Finset.univ.image (fun a => ((p.lines k).wires a, true)) ⊆ reqCorner p root b k := by
    intro key hKey
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
    exact hMem a
  have hCard : Finset.card (Finset.univ.image fun a => ((p.lines k).wires a, true)) ≤ (reqCorner p root b k).card :=
    Finset.card_le_card hSub
  rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin, op_arity_two (Or.inl hOp)] at hCard
  exact hCard

private theorem or_false_req_both {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {k : Fin g} (hk : k ∉ badGates p root)
    (hOp : (p.lines k).op = .or) (hNeed : NeedCorner p root b (.gate k, false)) :
    (∀ a : Fin (signature.Arity (p.lines k).op),
      ((p.lines k).wires a, false) ∈ reqCorner p root b k) ∧
      2 ≤ (reqCorner p root b k).card := by
  classical
  have hVal : cornerValue p b (.gate k) = false := (needCorner_eq_cornerValue hRoot hNeed).symm
  have hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k)) := hVal.symm ▸ hNeed
  have hCorner := hVal
  rw [cornerValue_gate] at hCorner
  obtain ⟨_, hArg⟩ := op_or_false_all hOp (p.lines k).wires (cornerValue p b) hCorner
  have hMem : ∀ a, ((p.lines k).wires a, false) ∈ reqCorner p root b k := by
    intro a
    simp only [reqCorner, hg, ite_true, cornerArguments]
    exact hArg a
  refine ⟨hMem, ?_⟩
  have hInj : Function.Injective (fun a => ((p.lines k).wires a, false)) := by
    intro a0 a1 he
    by_contra hne
    exact (not_bad_structure p root hk).2.2.2 a0 a1 hne (congrArg Prod.fst he)
  have hSub : Finset.univ.image (fun a => ((p.lines k).wires a, false)) ⊆ reqCorner p root b k := by
    intro key hKey
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
    exact hMem a
  have hCard : Finset.card (Finset.univ.image fun a => ((p.lines k).wires a, false)) ≤ (reqCorner p root b k).card :=
    Finset.card_le_card hSub
  rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin, op_arity_two (Or.inr hOp)] at hCard
  exact hCard

private theorem or_true_req_one {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {k : Fin g}
    (hOp : (p.lines k).op = .or) (hNeed : NeedCorner p root b (.gate k, true)) :
    ∃ a, reqCorner p root b k = {((p.lines k).wires a, true)} ∧
      cornerValue p b ((p.lines k).wires a) = true := by
  classical
  have hVal : cornerValue p b (.gate k) = true := (needCorner_eq_cornerValue hRoot hNeed).symm
  have hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k)) := hVal.symm ▸ hNeed
  have hCorner := hVal
  rw [cornerValue_gate] at hCorner
  obtain ⟨a, hEq, hv⟩ := op_or_true_one hOp (p.lines k).wires (cornerValue p b) hCorner
  refine ⟨a, ?_, hv⟩
  simp only [reqCorner, hg, ite_true, cornerArguments]
  exact hEq

private theorem and_false_req_one {p : Program signature n g} {root : Wire n g} {b : Bool}
    (hRoot : cornerValue p b root = true) {k : Fin g}
    (hOp : (p.lines k).op = .and) (hNeed : NeedCorner p root b (.gate k, false)) :
    ∃ a, reqCorner p root b k = {((p.lines k).wires a, false)} ∧
      cornerValue p b ((p.lines k).wires a) = false := by
  classical
  have hVal : cornerValue p b (.gate k) = false := (needCorner_eq_cornerValue hRoot hNeed).symm
  have hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k)) := hVal.symm ▸ hNeed
  have hCorner := hVal
  rw [cornerValue_gate] at hCorner
  obtain ⟨a, hEq, hv⟩ := op_and_false_one hOp (p.lines k).wires (cornerValue p b) hCorner
  refine ⟨a, ?_, hv⟩
  simp only [reqCorner, hg, ite_true, cornerArguments]
  exact hEq

private theorem needCorner_child_of_mem_reqCorner {p : Program signature n g} {root : Wire n g}
    {b : Bool} {k : Fin g} {w : Wire n g} {v : Bool}
    (hMem : (w, v) ∈ reqCorner p root b k) : NeedCorner p root b (w, v) := by
  by_cases hg : NeedCorner p root b (.gate k, cornerValue p b (.gate k))
  · simp only [reqCorner, hg, ite_true] at hMem
    exact NeedCorner.argument hg hMem
  · simp [reqCorner, hg] at hMem

private theorem needCorner_parent_of_ne {p : Program signature n g} {root : Wire n g} {b : Bool}
    {key : Wire n g × Bool}
    (h : NeedCorner p root b key) (hNe : key ≠ (root, true)) :
    ∃ p' : Fin g, key ∈ reqCorner p root b p' := by
  cases h with
  | output => exact (hNe rfl).elim
  | @argument p' hp' _ ha' =>
    refine ⟨p', ?_⟩
    simp only [reqCorner, hp', ite_true]
    exact ha'

private noncomputable def flipA0 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (S0 p root \ badGates p root).filter fun k => (p.lines k).op = .and

private noncomputable def flipB0 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (S0 p root \ badGates p root).filter fun k => (p.lines k).op = .or

private noncomputable def flipA1 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (S1 p root \ badGates p root).filter fun k => (p.lines k).op = .and

private noncomputable def flipB1 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (S1 p root \ badGates p root).filter fun k => (p.lines k).op = .or

private noncomputable def flipT0 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (flipB0 p root).filter fun k => cornerValue p true (.gate k) = true

private noncomputable def flipT1 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (flipA1 p root).filter fun k => cornerValue p false (.gate k) = false

private theorem flip_s0_part (p : Program signature n g) (root : Wire n g) :
    S0 p root \ badGates p root = flipA0 p root ∪ flipB0 p root := by
  classical
  ext k
  simp only [flipA0, flipB0, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hs, hnb⟩
    rcases (not_bad_structure p root hnb).1 with hAnd | hOr
    · exact Or.inl ⟨⟨hs, hnb⟩, hAnd⟩
    · exact Or.inr ⟨⟨hs, hnb⟩, hOr⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

private theorem flip_s1_part (p : Program signature n g) (root : Wire n g) :
    S1 p root \ badGates p root = flipA1 p root ∪ flipB1 p root := by
  classical
  ext k
  simp only [flipA1, flipB1, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hs, hnb⟩
    rcases (not_bad_structure p root hnb).1 with hAnd | hOr
    · exact Or.inl ⟨⟨hs, hnb⟩, hAnd⟩
    · exact Or.inr ⟨⟨hs, hnb⟩, hOr⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

private theorem flip_disj0 (p : Program signature n g) (root : Wire n g) :
    Disjoint (flipA0 p root) (flipB0 p root) := by
  classical
  rw [Finset.disjoint_left]
  intro k ha hb
  have h1' := (Finset.mem_filter.mp ha).2
  have h2' := (Finset.mem_filter.mp hb).2
  rw [h1'] at h2'; cases h2'

private theorem flip_disj1 (p : Program signature n g) (root : Wire n g) :
    Disjoint (flipA1 p root) (flipB1 p root) := by
  classical
  rw [Finset.disjoint_left]
  intro k ha hb
  have h1' := (Finset.mem_filter.mp ha).2
  have h2' := (Finset.mem_filter.mp hb).2
  rw [h1'] at h2'; cases h2'

private theorem flip_a0_req (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) {k : Fin g} (hk : k ∈ flipA0 p root) :
    reqCorner p root false k ⊆
        req p root k ∩ ((S0 p root).image fun j : Fin g => ((.gate j : Wire n g), true)) ∧
      2 ≤ (reqCorner p root false k).card := by
  classical
  obtain ⟨hk0, hOp⟩ := Finset.mem_filter.mp hk
  obtain ⟨hs0, hnb⟩ := Finset.mem_sdiff.mp hk0
  have hNeed : NeedCorner p root false (.gate k, true) := (Finset.mem_filter.mp hs0).2
  obtain ⟨hMem, hCard⟩ := and_true_req_both h0 hnb hOp hNeed
  refine ⟨?_, hCard⟩
  intro key hKey
  refine Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hKey, ?_⟩
  by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
  · simp only [reqCorner, hg, ite_true] at hKey
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
    have hChild := needCorner_child_of_mem_reqCorner (hMem a)
    obtain ⟨j, hj⟩ := gate_of_needCorner_ne h0 hChild
    rw [hj]
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hChild⟩, ?_⟩
    have hv : cornerValue p false (.gate j) = true := (needCorner_eq_cornerValue h0 (hj ▸ hChild)).symm
    rw [← hj] at hv
    simp [hv]
  · simp [reqCorner, hg] at hKey

private theorem flip_b0_req (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) {k : Fin g} (hk : k ∈ flipB0 p root) :
    1 ≤ (reqCorner p root false k ∩
        ((S0 p root).image fun j : Fin g => ((.gate j : Wire n g), true))).card := by
  classical
  obtain ⟨hk0, hOp⟩ := Finset.mem_filter.mp hk
  obtain ⟨hs0, _⟩ := Finset.mem_sdiff.mp hk0
  have hNeed : NeedCorner p root false (.gate k, true) := (Finset.mem_filter.mp hs0).2
  obtain ⟨a, hEq, _⟩ := or_true_req_one h0 hOp hNeed
  have hMem : ((p.lines k).wires a, true) ∈ reqCorner p root false k := by rw [hEq]; exact Finset.mem_singleton_self _
  have hChild := needCorner_child_of_mem_reqCorner hMem
  obtain ⟨j, hj⟩ := gate_of_needCorner_ne h0 hChild
  refine Finset.card_pos.mpr ⟨(.gate j, true), Finset.mem_inter.mpr ⟨hj ▸ hMem, ?_⟩⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hChild⟩, rfl⟩

private theorem flip_b1_req (p : Program signature n g) (root : Wire n g)
    (h1 : cornerValue p true root = true) {k : Fin g} (hk : k ∈ flipB1 p root) :
    reqCorner p root true k ⊆
        req p root k ∩ ((S1 p root).image fun j : Fin g => ((.gate j : Wire n g), false)) ∧
      2 ≤ (reqCorner p root true k).card := by
  classical
  obtain ⟨hk1, hOp⟩ := Finset.mem_filter.mp hk
  obtain ⟨hs1, hnb⟩ := Finset.mem_sdiff.mp hk1
  have hNeed : NeedCorner p root true (.gate k, false) := (Finset.mem_filter.mp hs1).2
  obtain ⟨hMem, hCard⟩ := or_false_req_both h1 hnb hOp hNeed
  refine ⟨?_, hCard⟩
  intro key hKey
  refine Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hKey, ?_⟩
  by_cases hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k))
  · simp only [reqCorner, hg, ite_true] at hKey
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
    have hChild := needCorner_child_of_mem_reqCorner (hMem a)
    obtain ⟨j, hj⟩ := gate_of_needCorner_ne h1 hChild
    rw [hj]
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hChild⟩, ?_⟩
    have hv : cornerValue p true (.gate j) = false := (needCorner_eq_cornerValue h1 (hj ▸ hChild)).symm
    rw [← hj] at hv
    simp [hv]
  · simp [reqCorner, hg] at hKey

private theorem flip_a1_req (p : Program signature n g) (root : Wire n g)
    (h1 : cornerValue p true root = true) {k : Fin g} (hk : k ∈ flipA1 p root) :
    1 ≤ (reqCorner p root true k ∩
        ((S1 p root).image fun j : Fin g => ((.gate j : Wire n g), false))).card := by
  classical
  obtain ⟨hk1, hOp⟩ := Finset.mem_filter.mp hk
  obtain ⟨hs1, _⟩ := Finset.mem_sdiff.mp hk1
  have hNeed : NeedCorner p root true (.gate k, false) := (Finset.mem_filter.mp hs1).2
  obtain ⟨a, hEq, _⟩ := and_false_req_one h1 hOp hNeed
  have hMem : ((p.lines k).wires a, false) ∈ reqCorner p root true k := by rw [hEq]; exact Finset.mem_singleton_self _
  have hChild := needCorner_child_of_mem_reqCorner hMem
  obtain ⟨j, hj⟩ := gate_of_needCorner_ne h1 hChild
  refine Finset.card_pos.mpr ⟨(.gate j, false), Finset.mem_inter.mpr ⟨hj ▸ hMem, ?_⟩⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hChild⟩, rfl⟩

private theorem flip_b0_sub (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    flipB0 p root ⊆ flipB1 p root ∪ flipT0 p root := by
  classical
  intro k hk
  by_cases hT : cornerValue p true (.gate k) = true
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hT⟩)
  · have hF : cornerValue p true (.gate k) = false := Bool.eq_false_iff.mpr hT
    obtain ⟨hk0, hOp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hs0, hnb⟩ := Finset.mem_sdiff.mp hk0
    have hNeed0 : NeedCorner p root false (.gate k, true) := (Finset.mem_filter.mp hs0).2
    have hNeed1 : NeedCorner p root true (.gate k, false) := by
      by_contra hNo
      have hVal : valSet p root k = {true} := by
        ext v
        simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hN
          cases v with
          | true => rfl
          | false =>
            rcases need_gate_eq_false h0 h1 hN with ⟨_, hcf⟩ | ⟨ht, _⟩
            · have he := needCorner_eq_cornerValue h0 hNeed0
              rw [hcf] at he
              cases he
            · exact (hNo ht).elim
        · rintro rfl; exact Or.inl hNeed0
      have hReqEq : (req p root k).card = 2 := by
        have := (not_bad_structure p root hnb).2.1
        rw [hVal, Finset.card_singleton] at this
        exact this
      have hEmpty1 : reqCorner p root true k = ∅ := by
        have hNo' : ¬NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := by
          simpa [hF] using hNo
        simp [reqCorner, hNo']
      obtain ⟨_, hEq0, _⟩ := or_true_req_one h0 hOp hNeed0
      rw [req, hEmpty1, Finset.union_empty, hEq0, Finset.card_singleton] at hReqEq
      omega
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed1⟩, hnb⟩, hOp⟩)

private theorem flip_a1_sub (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    flipA1 p root ⊆ flipA0 p root ∪ flipT1 p root := by
  classical
  intro k hk
  by_cases hT : cornerValue p false (.gate k) = false
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hT⟩)
  · have hTr : cornerValue p false (.gate k) = true := Bool.eq_true_of_not_eq_false hT
    obtain ⟨hk1, hOp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hs1, hnb⟩ := Finset.mem_sdiff.mp hk1
    have hNeed1 : NeedCorner p root true (.gate k, false) := (Finset.mem_filter.mp hs1).2
    have hNeed0 : NeedCorner p root false (.gate k, true) := by
      by_contra hNo
      have hVal : valSet p root k = {false} := by
        ext v
        simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hN
          cases v with
          | false => rfl
          | true =>
            rcases need_gate_eq_true h0 h1 hN with ⟨hf, _⟩ | ⟨_, hct⟩
            · exact (hNo hf).elim
            · have he := needCorner_eq_cornerValue h1 hNeed1
              rw [hct] at he
              cases he
        · rintro rfl; exact Or.inr hNeed1
      have hReqEq : (req p root k).card = 2 := by
        have := (not_bad_structure p root hnb).2.1
        rw [hVal, Finset.card_singleton] at this
        exact this
      have hEmpty0 : reqCorner p root false k = ∅ := by
        have hNo' : ¬NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := by
          simpa [hTr] using hNo
        simp [reqCorner, hNo']
      obtain ⟨_, hEq1, _⟩ := and_false_req_one h1 hOp hNeed1
      rw [req, hEmpty0, Finset.empty_union, hEq1, Finset.card_singleton] at hReqEq
      omega
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed0⟩, hnb⟩, hOp⟩)

private theorem flip_t0_prop (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∈ flipT0 p root) :
    NeedCorner p root true (.gate k, true) ∧
      ∃ u v : Wire n g, u ≠ v ∧ reqCorner p root false k = {(u, true)} ∧
        reqCorner p root true k = {(v, true)} := by
  classical
  obtain ⟨hkB0, hV1⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk0, hOp⟩ := Finset.mem_filter.mp hkB0
  obtain ⟨hs0, hnb⟩ := Finset.mem_sdiff.mp hk0
  have hNeed0 : NeedCorner p root false (.gate k, true) := (Finset.mem_filter.mp hs0).2
  have hVal : valSet p root k = {true} := by
    ext v
    simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hN
      cases v with
      | true => rfl
      | false =>
        rcases need_gate_eq_false h0 h1 hN with ⟨_, hcf⟩ | ⟨_, hct⟩
        · have he := needCorner_eq_cornerValue h0 hNeed0
          rw [hcf] at he; cases he
        · rw [hV1] at hct; cases hct
    · rintro rfl; exact Or.inl hNeed0
  have hReqEq : (req p root k).card = 2 := by
    have := (not_bad_structure p root hnb).2.1
    rw [hVal, Finset.card_singleton] at this
    exact this
  obtain ⟨a0, hEq0, _⟩ := or_true_req_one h0 hOp hNeed0
  have hNeed1 : NeedCorner p root true (.gate k, true) := by
    by_contra hNo
    have hEmpty1 : reqCorner p root true k = ∅ := by
      have hNo' : ¬NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := by
        simpa [hV1] using hNo
      simp [reqCorner, hNo']
    rw [req, hEmpty1, Finset.union_empty, hEq0, Finset.card_singleton] at hReqEq
    omega
  obtain ⟨a1, hEq1, _⟩ := or_true_req_one h1 hOp hNeed1
  refine ⟨hNeed1, (p.lines k).wires a0, (p.lines k).wires a1, ?_, hEq0, hEq1⟩
  intro heq
  rw [req, hEq0, hEq1, heq, Finset.union_idempotent, Finset.card_singleton] at hReqEq
  omega

private theorem flip_t1_prop (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∈ flipT1 p root) :
    NeedCorner p root false (.gate k, false) ∧
      ∃ u v : Wire n g, u ≠ v ∧ reqCorner p root true k = {(u, false)} ∧
        reqCorner p root false k = {(v, false)} := by
  classical
  obtain ⟨hkA1, hV0⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk1, hOp⟩ := Finset.mem_filter.mp hkA1
  obtain ⟨hs1, hnb⟩ := Finset.mem_sdiff.mp hk1
  have hNeed1 : NeedCorner p root true (.gate k, false) := (Finset.mem_filter.mp hs1).2
  have hVal : valSet p root k = {false} := by
    ext v
    simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hN
      cases v with
      | false => rfl
      | true =>
        rcases need_gate_eq_true h0 h1 hN with ⟨_, hcf⟩ | ⟨_, hct⟩
        · rw [hV0] at hcf; cases hcf
        · have he := needCorner_eq_cornerValue h1 hNeed1
          rw [hct] at he; cases he
    · rintro rfl; exact Or.inr hNeed1
  have hReqEq : (req p root k).card = 2 := by
    have := (not_bad_structure p root hnb).2.1
    rw [hVal, Finset.card_singleton] at this
    exact this
  obtain ⟨a1, hEq1, _⟩ := and_false_req_one h1 hOp hNeed1
  have hNeed0 : NeedCorner p root false (.gate k, false) := by
    by_contra hNo
    have hEmpty0 : reqCorner p root false k = ∅ := by
      have hNo' : ¬NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := by
        simpa [hV0] using hNo
      simp [reqCorner, hNo']
    rw [req, hEmpty0, Finset.empty_union, hEq1, Finset.card_singleton] at hReqEq
    omega
  obtain ⟨a0, hEq0, _⟩ := and_false_req_one h0 hOp hNeed0
  refine ⟨hNeed0, (p.lines k).wires a1, (p.lines k).wires a0, ?_, hEq1, hEq0⟩
  intro heq
  rw [req, hEq0, hEq1, heq, Finset.union_idempotent, Finset.card_singleton] at hReqEq
  omega

private theorem flip_gates_sub (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    flipGates p root ⊆ flipA0 p root ∪ flipB1 p root ∪ flipT0 p root ∪ flipT1 p root := by
  classical
  intro k hk
  obtain ⟨hkU, hnb⟩ := Finset.mem_sdiff.mp hk
  rcases Finset.mem_union.mp hkU with hk0 | hk1
  · have hk0' : k ∈ S0 p root \ badGates p root := Finset.mem_sdiff.mpr ⟨hk0, hnb⟩
    rw [flip_s0_part] at hk0'
    rcases Finset.mem_union.mp hk0' with hA | hB
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hA))
    · rcases Finset.mem_union.mp (flip_b0_sub p root h0 h1 hB) with hB1' | hT0'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hB1'))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hT0')
  · have hk1' : k ∈ S1 p root \ badGates p root := Finset.mem_sdiff.mpr ⟨hk1, hnb⟩
    rw [flip_s1_part] at hk1'
    rcases Finset.mem_union.mp hk1' with hA | hB
    · rcases Finset.mem_union.mp (flip_a1_sub p root h0 h1 hA) with hA0' | hT1'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hA0'))
      · exact Finset.mem_union_right _ hT1'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hB))

theorem card_badFlip_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badFlip p root).card ≤ 9 * (badGates p root).card + 10 * shared p root := by
  classical
  let Bad := badGates p root
  let s0 := S0 p root
  let s1 := S1 p root
  let A0 := flipA0 p root
  let B0 := flipB0 p root
  let A1 := flipA1 p root
  let B1 := flipB1 p root
  let T0 := flipT0 p root
  let T1 := flipT1 p root
  let S0T := s0.image fun j : Fin g => ((.gate j : Wire n g), true)
  let S1F := s1.image fun j : Fin g => ((.gate j : Wire n g), false)
  have hS0T : S0T.card = s0.card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hS1F : S1F.card = s1.card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hS0Part := flip_s0_part p root
  have hS1Part := flip_s1_part p root
  have hDisj0 := flip_disj0 p root
  have hDisj1 := flip_disj1 p root
  have hA0_sub : ∀ k ∈ A0, 2 ≤ (req p root k ∩ S0T).card := fun k hk => by
    obtain ⟨hSub, hCard⟩ := flip_a0_req p root h0 hk
    exact hCard.trans (Finset.card_le_card hSub)
  have hB0_sub : ∀ k ∈ B0, 1 ≤ (req p root k ∩ S0T).card := fun k hk =>
    (flip_b0_req p root h0 hk).trans (Finset.card_le_card
      (Finset.inter_subset_inter Finset.subset_union_left le_rfl))
  have hSum0 := sum_card_inter_req_le p root (s0 \ Bad) S0T
  have hSum0_ge : 2 * A0.card + B0.card ≤ ∑ k ∈ s0 \ Bad, (req p root k ∩ S0T).card := by
    rw [hS0Part, Finset.sum_union hDisj0]
    calc
      2 * A0.card + B0.card = (∑ _k ∈ A0, 2) + (∑ _k ∈ B0, 1) := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Nat.add_le_add (Finset.sum_le_sum hA0_sub) (Finset.sum_le_sum hB0_sub)
  have hS0Split : s0.card ≤ (s0 \ Bad).card + Bad.card :=
    (Finset.card_le_card fun x hx => by by_cases h : x ∈ Bad <;> simp [hx, h]).trans
      (Finset.card_union_le ..)
  have hS0Diff : (s0 \ Bad).card = A0.card + B0.card := by
    rw [hS0Part, Finset.card_union_of_disjoint hDisj0]
  have hA0_le : A0.card ≤ Bad.card + shared p root := by omega
  have hB1_sub : ∀ k ∈ B1, 2 ≤ (req p root k ∩ S1F).card := fun k hk => by
    obtain ⟨hSub, hCard⟩ := flip_b1_req p root h1 hk
    exact hCard.trans (Finset.card_le_card hSub)
  have hA1_sub : ∀ k ∈ A1, 1 ≤ (req p root k ∩ S1F).card := fun k hk =>
    (flip_a1_req p root h1 hk).trans (Finset.card_le_card
      (Finset.inter_subset_inter Finset.subset_union_right le_rfl))
  have hSum1 := sum_card_inter_req_le p root (s1 \ Bad) S1F
  have hSum1_ge : 2 * B1.card + A1.card ≤ ∑ k ∈ s1 \ Bad, (req p root k ∩ S1F).card := by
    rw [hS1Part, Finset.sum_union hDisj1]
    dsimp only [A1, B1]
    calc
      2 * B1.card + A1.card = (∑ _k ∈ B1, 2) + (∑ _k ∈ A1, 1) := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ (∑ k ∈ B1, (req p root k ∩ S1F).card) + (∑ k ∈ A1, (req p root k ∩ S1F).card) :=
        Nat.add_le_add (Finset.sum_le_sum hB1_sub) (Finset.sum_le_sum hA1_sub)
      _ = (∑ k ∈ A1, (req p root k ∩ S1F).card) + (∑ k ∈ B1, (req p root k ∩ S1F).card) :=
        Nat.add_comm ..
  have hS1Split : s1.card ≤ (s1 \ Bad).card + Bad.card :=
    (Finset.card_le_card fun x hx => by by_cases h : x ∈ Bad <;> simp [hx, h]).trans
      (Finset.card_union_le ..)
  have hS1Diff : (s1 \ Bad).card = A1.card + B1.card := by
    rw [hS1Part, Finset.card_union_of_disjoint hDisj1]
  have hB1_le : B1.card ≤ Bad.card + shared p root := by omega
  have hB0Sub := flip_b0_sub p root h0 h1
  have hA1Sub := flip_a1_sub p root h0 h1
  let W0 := ((Bad ∪ A0 ∪ B1).image fun j : Fin g => ((.gate j : Wire n g), true)) ∪ repeatStates p root
  have hT0_inter : ∀ k ∈ T0, 1 ≤ (req p root k ∩ W0).card := by
    intro k hk
    obtain ⟨_, u, v, huv, hEq0, hEq1⟩ := flip_t0_prop p root h0 h1 hk
    have hMem0 : (u, true) ∈ reqCorner p root false k := by rw [hEq0]; exact Finset.mem_singleton_self _
    have hChild0 := needCorner_child_of_mem_reqCorner hMem0
    obtain ⟨ju, hju⟩ := gate_of_needCorner_ne h0 hChild0
    have hju_s0 : ju ∈ s0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hju ▸ hChild0⟩
    refine Finset.card_pos.mpr ⟨(u, true), Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hMem0, ?_⟩⟩
    by_cases hjuT : ju ∈ T0
    · apply Finset.mem_union_right
      have hNeed1ju := (flip_t0_prop p root h0 h1 hjuT).1
      have hNeRoot : (u, true) ≠ (root, true) := by
        intro hEqR
        have hr : root = .gate ju := (congrArg Prod.fst hEqR).symm.trans hju
        have hkNeed0 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp hk).1).1).1).2
        have hOrd := needCorner_precedes_root hkNeed0
        rw [hr] at hOrd
        have hLt : wireOrder (.gate ju : Wire n g) < wireOrder (.gate k : Wire n g) := by
          rw [← hju]
          by_cases hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k))
          · exact cornerArg_precedes p k false (by simpa [reqCorner, hg] using hMem0)
          · simp [reqCorner, hg] at hMem0
        exact Nat.not_lt_of_ge hOrd hLt
      obtain ⟨p', hp'Mem'⟩ := needCorner_parent_of_ne (hju.symm ▸ hNeed1ju) hNeRoot
      have hNeK : p' ≠ k := by
        intro hEqK
        subst hEqK
        rw [hEq1, Finset.mem_singleton] at hp'Mem'
        exact huv (Prod.ext_iff.mp hp'Mem').1
      exact mem_repeatStates_of_ne hNeK (Finset.mem_union_right _ hp'Mem') (Finset.mem_union_left _ hMem0)
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨ju, ?_, hju ▸ rfl⟩
      by_cases hBad : ju ∈ Bad
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hBad)
      · have hS0Diff : ju ∈ s0 \ Bad := Finset.mem_sdiff.mpr ⟨hju_s0, hBad⟩
        rw [hS0Part] at hS0Diff
        rcases Finset.mem_union.mp hS0Diff with hA | hB
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hA)
        · have hB' := hB0Sub hB
          rcases Finset.mem_union.mp hB' with hB1' | hT0'
          · exact Finset.mem_union_right _ hB1'
          · exact (hjuT hT0').elim
  have hT0_card := mul_card_le_of_inter_req p root T0 W0 1 hT0_inter
  have hW0_card : W0.card ≤ Bad.card + A0.card + B1.card + (repeatStates p root).card := by
    have h1' : W0.card ≤ ((Bad ∪ A0 ∪ B1).image fun j : Fin g => ((.gate j : Wire n g), true)).card +
        (repeatStates p root).card := Finset.card_union_le ..
    have h2' : ((Bad ∪ A0 ∪ B1).image fun j : Fin g => ((.gate j : Wire n g), true)).card ≤
        (Bad ∪ A0 ∪ B1).card := Finset.card_image_le
    have h3' : (Bad ∪ A0 ∪ B1).card ≤ (Bad ∪ A0).card + B1.card := Finset.card_union_le ..
    have h4' : (Bad ∪ A0).card ≤ Bad.card + A0.card := Finset.card_union_le ..
    omega
  have hRep := card_repeatStates_le_shared p root
  have hT0_le : T0.card ≤ 3 * Bad.card + 4 * shared p root := by omega
  let W1 := ((Bad ∪ A0 ∪ B1).image fun j : Fin g => ((.gate j : Wire n g), false)) ∪ repeatStates p root
  have hT1_inter : ∀ k ∈ T1, 1 ≤ (req p root k ∩ W1).card := by
    intro k hk
    obtain ⟨_, u, v, huv, hEq1, hEq0⟩ := flip_t1_prop p root h0 h1 hk
    have hMem1 : (u, false) ∈ reqCorner p root true k := by rw [hEq1]; exact Finset.mem_singleton_self _
    have hChild1 := needCorner_child_of_mem_reqCorner hMem1
    obtain ⟨ju, hju⟩ := gate_of_needCorner_ne h1 hChild1
    have hju_s1 : ju ∈ s1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hju ▸ hChild1⟩
    refine Finset.card_pos.mpr ⟨(u, false), Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hMem1, ?_⟩⟩
    by_cases hjuT : ju ∈ T1
    · apply Finset.mem_union_right
      have hNeed0ju := (flip_t1_prop p root h0 h1 hjuT).1
      have hNeRoot : (u, false) ≠ (root, true) := by
        intro hEqR
        have hF : false = true := congrArg Prod.snd hEqR
        cases hF
      obtain ⟨p', hp'Mem'⟩ := needCorner_parent_of_ne (hju.symm ▸ hNeed0ju) hNeRoot
      have hNeK : p' ≠ k := by
        intro hEqK
        subst hEqK
        rw [hEq0, Finset.mem_singleton] at hp'Mem'
        exact huv (Prod.ext_iff.mp hp'Mem').1
      exact mem_repeatStates_of_ne hNeK (Finset.mem_union_left _ hp'Mem') (Finset.mem_union_right _ hMem1)
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨ju, ?_, hju ▸ rfl⟩
      by_cases hBad : ju ∈ Bad
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hBad)
      · have hS1Diff : ju ∈ s1 \ Bad := Finset.mem_sdiff.mpr ⟨hju_s1, hBad⟩
        rw [hS1Part] at hS1Diff
        rcases Finset.mem_union.mp hS1Diff with hA | hB
        · have hA' := hA1Sub hA
          rcases Finset.mem_union.mp hA' with hA0' | hT1'
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hA0')
          · exact (hjuT hT1').elim
        · exact Finset.mem_union_right _ hB
  have hT1_card := mul_card_le_of_inter_req p root T1 W1 1 hT1_inter
  have hW1_card : W1.card ≤ Bad.card + A0.card + B1.card + (repeatStates p root).card := by
    have h1' : W1.card ≤ ((Bad ∪ A0 ∪ B1).image fun j : Fin g => ((.gate j : Wire n g), false)).card +
        (repeatStates p root).card := Finset.card_union_le ..
    have h2' : ((Bad ∪ A0 ∪ B1).image fun j : Fin g => ((.gate j : Wire n g), false)).card ≤
        (Bad ∪ A0 ∪ B1).card := Finset.card_image_le
    have h3' : (Bad ∪ A0 ∪ B1).card ≤ (Bad ∪ A0).card + B1.card := Finset.card_union_le ..
    have h4' : (Bad ∪ A0).card ≤ Bad.card + A0.card := Finset.card_union_le ..
    omega
  have hT1_le : T1.card ≤ 3 * Bad.card + 4 * shared p root := by omega
  have hFlipCard : (flipGates p root).card ≤ A0.card + B1.card + T0.card + T1.card := by
    have h1' := Finset.card_le_card (flip_gates_sub p root h0 h1)
    have h2' := Finset.card_union_le (A0 ∪ B1 ∪ T0) T1
    have h3' := Finset.card_union_le (A0 ∪ B1) T0
    have h4' := Finset.card_union_le A0 B1
    dsimp only [A0, B1, T0, T1] at h1' h2' h3' h4' ⊢
    omega
  have hBF : (badFlip p root).card ≤ Bad.card + (flipGates p root).card := Finset.card_union_le ..
  dsimp only [Bad] at hA0_le hB1_le hT0_le hT1_le hBF
  omega

theorem card_badFlip_le_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badFlip p root).card ≤ 10 * slack p root := by
  have hBF := card_badFlip_le p root h0 h1
  have hBad := card_badGates_le p root
  unfold slack
  omega

def IsDualAND (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  (p.lines k).op = .and ∧ NeedCorner p root false (.gate k, false) ∧
    NeedCorner p root true (.gate k, true)

def IsDualOR (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  (p.lines k).op = .or ∧ NeedCorner p root false (.gate k, false) ∧
    NeedCorner p root true (.gate k, true)

def IsPureAND1 (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  (p.lines k).op = .and ∧ ¬NeedCorner p root false (.gate k, false) ∧
    NeedCorner p root true (.gate k, true)

def IsPureOR0 (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  (p.lines k).op = .or ∧ NeedCorner p root false (.gate k, false) ∧
    ¬NeedCorner p root true (.gate k, true)

def IsDual (p : Program signature n g) (root : Wire n g) (k : Fin g) : Prop :=
  IsDualAND p root k ∨ IsDualOR p root k

theorem not_s0_s1_of_not_badFlip {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ badFlip p root) :
    k ∉ badGates p root ∧ ¬NeedCorner p root false (.gate k, true) ∧
      ¬NeedCorner p root true (.gate k, false) := by
  classical
  have hnb : k ∉ badGates p root := fun h => hk (Finset.mem_union_left _ h)
  have hnf : k ∉ flipGates p root := fun h => hk (Finset.mem_union_right _ h)
  have hnu : k ∉ S0 p root ∪ S1 p root := fun h => hnf (Finset.mem_sdiff.mpr ⟨h, hnb⟩)
  exact ⟨hnb, fun h => hnu (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)),
    fun h => hnu (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))⟩

theorem four_way_of_not_badFlip {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∉ badFlip p root) :
    IsDualAND p root k ∨ IsDualOR p root k ∨ IsPureAND1 p root k ∨ IsPureOR0 p root k := by
  classical
  obtain ⟨hnb, hns0, hns1⟩ := not_s0_s1_of_not_badFlip hk
  obtain ⟨hOp, hReqEq, hValPos, _⟩ := not_bad_structure p root hnb
  have hNeed0or1 : NeedCorner p root false (.gate k, false) ∨ NeedCorner p root true (.gate k, true) := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hValPos
    have hNv := (Finset.mem_filter.mp hv).2
    cases v with
    | false =>
      rcases hNv with hf | ht
      · exact Or.inl hf
      · exact (hns1 ht).elim
    | true =>
      rcases hNv with hf | ht
      · exact (hns0 hf).elim
      · exact Or.inr ht
  rcases hOp with hAnd | hOr
  · by_cases hn1 : NeedCorner p root true (.gate k, true)
    · by_cases hn0 : NeedCorner p root false (.gate k, false)
      · exact Or.inl ⟨hAnd, hn0, hn1⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hAnd, hn0, hn1⟩))
    · exfalso
      have hn0 : NeedCorner p root false (.gate k, false) := hNeed0or1.elim id fun h => (hn1 h).elim
      have hVal : valSet p root k = {false} := by
        ext v
        simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hN
          cases v with
          | false => rfl
          | true => exact hN.elim (fun hf => (hns0 hf).elim) (fun ht => (hn1 ht).elim)
        · rintro rfl; exact Or.inl hn0
      have hEmpty1 : reqCorner p root true k = ∅ := by
        have hNo' : ¬NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := by
          cases ht : cornerValue p true (.gate k) with
          | false => simpa [ht] using hns1
          | true => simpa [ht] using hn1
        simp [reqCorner, hNo']
      obtain ⟨a, hEq0, _⟩ := and_false_req_one h0 hAnd hn0
      rw [req, hEmpty1, Finset.union_empty, hEq0, Finset.card_singleton, hVal, Finset.card_singleton] at hReqEq
      omega
  · by_cases hn0 : NeedCorner p root false (.gate k, false)
    · by_cases hn1 : NeedCorner p root true (.gate k, true)
      · exact Or.inr (Or.inl ⟨hOr, hn0, hn1⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hOr, hn0, hn1⟩))
    · exfalso
      have hn1 : NeedCorner p root true (.gate k, true) := hNeed0or1.elim (fun h => (hn0 h).elim) id
      have hVal : valSet p root k = {true} := by
        ext v
        simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hN
          cases v with
          | true => rfl
          | false => exact hN.elim (fun hf => (hn0 hf).elim) (fun ht => (hns1 ht).elim)
        · rintro rfl; exact Or.inr hn1
      have hEmpty0 : reqCorner p root false k = ∅ := by
        have hNo' : ¬NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := by
          cases hf : cornerValue p false (.gate k) with
          | true => simpa [hf] using hns0
          | false => simpa [hf] using hn0
        simp [reqCorner, hNo']
      obtain ⟨a, hEq1, _⟩ := or_true_req_one h1 hOr hn1
      rw [req, hEmpty0, Finset.empty_union, hEq1, Finset.card_singleton, hVal, Finset.card_singleton] at hReqEq
      omega

theorem pureAND1_children {p : Program signature n g} {root : Wire n g}
    (h1 : cornerValue p true root = true) {k : Fin g} (hnb : k ∉ badGates p root)
    (hPure : IsPureAND1 p root k) :
    ∀ a : Fin (signature.Arity (p.lines k).op),
      ((p.lines k).wires a, true) ∈ reqCorner p root true k ∧
      NeedCorner p root true ((p.lines k).wires a, true) := by
  obtain ⟨hMem, _⟩ := and_true_req_both h1 hnb hPure.1 hPure.2.2
  exact fun a => ⟨hMem a, needCorner_child_of_mem_reqCorner (hMem a)⟩

theorem pureOR0_children {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) {k : Fin g} (hnb : k ∉ badGates p root)
    (hPure : IsPureOR0 p root k) :
    ∀ a : Fin (signature.Arity (p.lines k).op),
      ((p.lines k).wires a, false) ∈ reqCorner p root false k ∧
      NeedCorner p root false ((p.lines k).wires a, false) := by
  obtain ⟨hMem, _⟩ := or_false_req_both h0 hnb hPure.1 hPure.2.1
  exact fun a => ⟨hMem a, needCorner_child_of_mem_reqCorner (hMem a)⟩

theorem dualChild_is_wire {p : Program signature n g} {k : Fin g}
    (hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or) :
    ∃ a : Fin (signature.Arity (p.lines k).op), (p.lines k).wires a = dualChild p k :=
  op_dual_is_wire hOp (.gate k) (p.lines k).wires

theorem sideChild_is_wire {p : Program signature n g} {k : Fin g}
    (hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or) :
    ∃ a : Fin (signature.Arity (p.lines k).op), (p.lines k).wires a = sideChild p k :=
  op_side_is_wire hOp (.gate k) (p.lines k).wires

theorem dualChild_or_sideChild {p : Program signature n g} {k : Fin g}
    (hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or)
    (a : Fin (signature.Arity (p.lines k).op)) :
    (p.lines k).wires a = dualChild p k ∨ (p.lines k).wires a = sideChild p k :=
  op_dual_or_side hOp (.gate k) (p.lines k).wires a

theorem dualChild_ne_sideChild {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hnb : k ∉ badGates p root) : dualChild p k ≠ sideChild p k :=
  have hS := not_bad_structure p root hnb
  op_dual_ne_side hS.1 (.gate k) (p.lines k).wires hS.2.2.2

theorem wireOrder_lt_of_wire {p : Program signature n g} (k : Fin g)
    (a : Fin (signature.Arity (p.lines k).op)) :
    wireOrder ((p.lines k).wires a) < wireOrder (.gate k : Wire n g) := by
  change wireOrder ((p.lines k).wires a) < k.val + 1
  cases hW : (p.lines k).wires a with
  | input _ => simp [wireOrder]
  | gate j => exact Nat.succ_lt_succ (p.lt_of_lines_wires_eq_gate k a j hW)

theorem dualChild_precedes {p : Program signature n g} {k : Fin g}
    (hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or) :
    wireOrder (dualChild p k) < wireOrder (.gate k : Wire n g) := by
  obtain ⟨a, ha⟩ := dualChild_is_wire hOp
  exact ha ▸ wireOrder_lt_of_wire k a

theorem sideChild_precedes {p : Program signature n g} {k : Fin g}
    (hOp : (p.lines k).op = .and ∨ (p.lines k).op = .or) :
    wireOrder (sideChild p k) < wireOrder (.gate k : Wire n g) := by
  obtain ⟨a, ha⟩ := sideChild_is_wire hOp
  exact ha ▸ wireOrder_lt_of_wire k a

theorem dualAND_children {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hnb : k ∉ badGates p root) (hDual : IsDualAND p root k) :
    dualChild p k ≠ sideChild p k ∧
      reqCorner p root false k = {(dualChild p k, false)} ∧
      (dualChild p k, false) ∈ req p root k ∧
      (dualChild p k, true) ∈ req p root k ∧
      (sideChild p k, true) ∈ req p root k ∧
      NeedCorner p root false (dualChild p k, false) ∧
      NeedCorner p root true (dualChild p k, true) ∧
      NeedCorner p root true (sideChild p k, true) ∧
      cornerValue p false (dualChild p k) = false ∧
      cornerValue p true (dualChild p k) = true ∧
      cornerValue p true (sideChild p k) = true := by
  obtain ⟨hOp, hN0, hN1⟩ := hDual
  have hNe := dualChild_ne_sideChild hnb
  obtain ⟨hMem1, _⟩ := and_true_req_both h1 hnb hOp hN1
  have hMemD1 : (dualChild p k, true) ∈ reqCorner p root true k := by
    obtain ⟨a, ha⟩ := dualChild_is_wire (Or.inl hOp)
    exact ha ▸ hMem1 a
  have hMemS1 : (sideChild p k, true) ∈ reqCorner p root true k := by
    obtain ⟨a, ha⟩ := sideChild_is_wire (Or.inl hOp)
    exact ha ▸ hMem1 a
  have hEq0 : reqCorner p root false k = {(dualChild p k, false)} := by
    have hVal : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hN0).symm
    have hg : NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := hVal.symm ▸ hN0
    have hCorner := hVal
    rw [cornerValue_gate] at hCorner
    simp only [reqCorner, hg, ite_true, cornerArguments]
    exact op_and_false_dual hOp (.gate k) (p.lines k).wires hCorner
  have hMemD0 : (dualChild p k, false) ∈ reqCorner p root false k := by
    rw [hEq0]; exact Finset.mem_singleton_self _
  have hnD0 := needCorner_child_of_mem_reqCorner hMemD0
  have hnD1 := needCorner_child_of_mem_reqCorner hMemD1
  have hnS1 := needCorner_child_of_mem_reqCorner hMemS1
  exact ⟨hNe, hEq0, Finset.mem_union_left _ hMemD0, Finset.mem_union_right _ hMemD1,
    Finset.mem_union_right _ hMemS1, hnD0, hnD1, hnS1,
    (needCorner_eq_cornerValue h0 hnD0).symm, (needCorner_eq_cornerValue h1 hnD1).symm,
    (needCorner_eq_cornerValue h1 hnS1).symm⟩

theorem dualOR_children {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hnb : k ∉ badGates p root) (hDual : IsDualOR p root k) :
    dualChild p k ≠ sideChild p k ∧
      reqCorner p root true k = {(dualChild p k, true)} ∧
      (dualChild p k, true) ∈ req p root k ∧
      (dualChild p k, false) ∈ req p root k ∧
      (sideChild p k, false) ∈ req p root k ∧
      NeedCorner p root true (dualChild p k, true) ∧
      NeedCorner p root false (dualChild p k, false) ∧
      NeedCorner p root false (sideChild p k, false) ∧
      cornerValue p true (dualChild p k) = true ∧
      cornerValue p false (dualChild p k) = false ∧
      cornerValue p false (sideChild p k) = false := by
  obtain ⟨hOp, hN0, hN1⟩ := hDual
  have hNe := dualChild_ne_sideChild hnb
  obtain ⟨hMem0, _⟩ := or_false_req_both h0 hnb hOp hN0
  have hMemD0 : (dualChild p k, false) ∈ reqCorner p root false k := by
    obtain ⟨a, ha⟩ := dualChild_is_wire (Or.inr hOp)
    exact ha ▸ hMem0 a
  have hMemS0 : (sideChild p k, false) ∈ reqCorner p root false k := by
    obtain ⟨a, ha⟩ := sideChild_is_wire (Or.inr hOp)
    exact ha ▸ hMem0 a
  have hEq1 : reqCorner p root true k = {(dualChild p k, true)} := by
    have hVal : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hN1).symm
    have hg : NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := hVal.symm ▸ hN1
    have hCorner := hVal
    rw [cornerValue_gate] at hCorner
    simp only [reqCorner, hg, ite_true, cornerArguments]
    exact op_or_true_dual hOp (.gate k) (p.lines k).wires hCorner
  have hMemD1 : (dualChild p k, true) ∈ reqCorner p root true k := by
    rw [hEq1]; exact Finset.mem_singleton_self _
  have hnD1 := needCorner_child_of_mem_reqCorner hMemD1
  have hnD0 := needCorner_child_of_mem_reqCorner hMemD0
  have hnS0 := needCorner_child_of_mem_reqCorner hMemS0
  exact ⟨hNe, hEq1, Finset.mem_union_right _ hMemD1, Finset.mem_union_left _ hMemD0,
    Finset.mem_union_left _ hMemS0, hnD1, hnD0, hnS0,
    (needCorner_eq_cornerValue h1 hnD1).symm, (needCorner_eq_cornerValue h0 hnD0).symm,
    (needCorner_eq_cornerValue h0 hnS0).symm⟩

noncomputable def Z1 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k =>
    NeedCorner p root false (.gate k, false) ∧ cornerValue p true (.gate k) = false

noncomputable def Z0 (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k =>
    NeedCorner p root true (.gate k, true) ∧ cornerValue p false (.gate k) = true

noncomputable def badSideOR (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k =>
    IsDualOR p root k ∧ k ∉ badFlip p root ∧ cornerValue p true (sideChild p k) = false

noncomputable def badSideAND (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k =>
    IsDualAND p root k ∧ k ∉ badFlip p root ∧ cornerValue p false (sideChild p k) = true

noncomputable def otherBad (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  badFlip p root ∪ badSideOR p root ∪ badSideAND p root

noncomputable def goodDual (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (Finset.univ.filter (IsDual p root)) \ otherBad p root

theorem card_Z1_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (Z1 p root).card ≤ 2 * (badFlip p root).card + shared p root := by
  classical
  let z1 := Z1 p root
  let bf := badFlip p root
  let z1F := z1.image fun j : Fin g => ((.gate j : Wire n g), false)
  have hz1F : z1F.card = z1.card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hSub : ∀ k ∈ z1 \ bf, 2 ≤ (req p root k ∩ z1F).card := by
    intro k hk
    obtain ⟨hkZ, hnbF⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hN0, hV1⟩ := (Finset.mem_filter.mp hkZ).2
    have hnb := (not_s0_s1_of_not_badFlip hnbF).1
    have hPure : IsPureOR0 p root k := by
      rcases four_way_of_not_badFlip h0 h1 hnbF with hD | hD | hP | hP
      · have he := needCorner_eq_cornerValue h1 hD.2.2; rw [hV1] at he; cases he
      · have he := needCorner_eq_cornerValue h1 hD.2.2; rw [hV1] at he; cases he
      · exact (hP.2.1 hN0).elim
      · exact hP
    obtain ⟨hMem, _⟩ := or_false_req_both h0 hnb hPure.1 hPure.2.1
    have hV1Inputs : ∀ a : Fin (signature.Arity (p.lines k).op),
        cornerValue p true ((p.lines k).wires a) = false := by
      have hCorner := hV1
      rw [cornerValue_gate] at hCorner
      exact (op_or_false_all hPure.1 (p.lines k).wires (cornerValue p true) hCorner).1
    have hSubK : Finset.univ.image (fun a => ((p.lines k).wires a, false)) ⊆ req p root k ∩ z1F := by
      intro key hKey
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
      refine Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hMem a), ?_⟩
      have hV1a := hV1Inputs a
      cases hw : (p.lines k).wires a with
      | input i => rw [hw, cornerValue_input] at hV1a; cases hV1a
      | gate j =>
        have hChild := needCorner_child_of_mem_reqCorner (hMem a)
        rw [hw] at hChild hV1a
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hChild, hV1a⟩, rfl⟩
    have hInj : Function.Injective (fun a => ((p.lines k).wires a, false)) := by
      intro a0 a1 he
      by_contra hne
      exact (not_bad_structure p root hnb).2.2.2 a0 a1 hne (congrArg Prod.fst he)
    have hCard := Finset.card_le_card hSubK
    rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin,
      op_arity_two (Or.inr hPure.1)] at hCard
    exact hCard
  have hMul := mul_card_le_of_inter_req p root (z1 \ bf) z1F 2 hSub
  have hSplit : z1.card ≤ (z1 \ bf).card + bf.card :=
    (Finset.card_le_card fun x hx => by by_cases h : x ∈ bf <;> simp [hx, h]).trans
      (Finset.card_union_le ..)
  dsimp only [z1, bf] at hz1F hMul hSplit
  omega

theorem card_Z0_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (Z0 p root).card ≤ 2 * (badFlip p root).card + shared p root := by
  classical
  let z0 := Z0 p root
  let bf := badFlip p root
  let z0T := z0.image fun j : Fin g => ((.gate j : Wire n g), true)
  have hz0T : z0T.card = z0.card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hSub : ∀ k ∈ z0 \ bf, 2 ≤ (req p root k ∩ z0T).card := by
    intro k hk
    obtain ⟨hkZ, hnbF⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hN1, hV0⟩ := (Finset.mem_filter.mp hkZ).2
    have hnb := (not_s0_s1_of_not_badFlip hnbF).1
    have hPure : IsPureAND1 p root k := by
      rcases four_way_of_not_badFlip h0 h1 hnbF with hD | hD | hP | hP
      · have he := needCorner_eq_cornerValue h0 hD.2.1; rw [hV0] at he; cases he
      · have he := needCorner_eq_cornerValue h0 hD.2.1; rw [hV0] at he; cases he
      · exact hP
      · exact (hP.2.2 hN1).elim
    obtain ⟨hMem, _⟩ := and_true_req_both h1 hnb hPure.1 hPure.2.2
    have hV0Inputs : ∀ a : Fin (signature.Arity (p.lines k).op),
        cornerValue p false ((p.lines k).wires a) = true := by
      have hCorner := hV0
      rw [cornerValue_gate] at hCorner
      exact (op_and_true_all hPure.1 (p.lines k).wires (cornerValue p false) hCorner).1
    have hSubK : Finset.univ.image (fun a => ((p.lines k).wires a, true)) ⊆ req p root k ∩ z0T := by
      intro key hKey
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
      refine Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (hMem a), ?_⟩
      have hV0a := hV0Inputs a
      cases hw : (p.lines k).wires a with
      | input i => rw [hw, cornerValue_input] at hV0a; cases hV0a
      | gate j =>
        have hChild := needCorner_child_of_mem_reqCorner (hMem a)
        rw [hw] at hChild hV0a
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hChild, hV0a⟩, rfl⟩
    have hInj : Function.Injective (fun a => ((p.lines k).wires a, true)) := by
      intro a0 a1 he
      by_contra hne
      exact (not_bad_structure p root hnb).2.2.2 a0 a1 hne (congrArg Prod.fst he)
    have hCard := Finset.card_le_card hSubK
    rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin,
      op_arity_two (Or.inl hPure.1)] at hCard
    exact hCard
  have hMul := mul_card_le_of_inter_req p root (z0 \ bf) z0T 2 hSub
  have hSplit : z0.card ≤ (z0 \ bf).card + bf.card :=
    (Finset.card_le_card fun x hx => by by_cases h : x ∈ bf <;> simp [hx, h]).trans
      (Finset.card_union_le ..)
  dsimp only [z0, bf] at hz0T hMul hSplit
  omega

theorem card_badSideOR_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badSideOR p root).card ≤ 2 * (badFlip p root).card + 2 * shared p root := by
  classical
  let z1F := (Z1 p root).image fun j : Fin g => ((.gate j : Wire n g), false)
  have hz1F : z1F.card = (Z1 p root).card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hInter : ∀ k ∈ badSideOR p root, 1 ≤ (req p root k ∩ z1F).card := by
    intro k hk
    obtain ⟨hDual, hnbF, hV1⟩ := (Finset.mem_filter.mp hk).2
    have hnb := (not_s0_s1_of_not_badFlip hnbF).1
    have hChild := dualOR_children h0 h1 hnb hDual
    have hMem := hChild.2.2.2.2.1
    have hNeed := hChild.2.2.2.2.2.2.2.1
    cases hs : sideChild p k with
    | input i => rw [hs, cornerValue_input] at hV1; cases hV1
    | gate j =>
      rw [hs] at hMem hNeed hV1
      exact Finset.card_pos.mpr ⟨(.gate j, false), Finset.mem_inter.mpr
        ⟨hMem, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed, hV1⟩, rfl⟩⟩⟩
  have hMul := mul_card_le_of_inter_req p root (badSideOR p root) z1F 1 hInter
  have hZ := card_Z1_le p root h0 h1
  omega

theorem card_badSideAND_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badSideAND p root).card ≤ 2 * (badFlip p root).card + 2 * shared p root := by
  classical
  let z0T := (Z0 p root).image fun j : Fin g => ((.gate j : Wire n g), true)
  have hz0T : z0T.card = (Z0 p root).card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hInter : ∀ k ∈ badSideAND p root, 1 ≤ (req p root k ∩ z0T).card := by
    intro k hk
    obtain ⟨hDual, hnbF, hV0⟩ := (Finset.mem_filter.mp hk).2
    have hnb := (not_s0_s1_of_not_badFlip hnbF).1
    have hChild := dualAND_children h0 h1 hnb hDual
    have hMem := hChild.2.2.2.2.1
    have hNeed := hChild.2.2.2.2.2.2.2.1
    cases hs : sideChild p k with
    | input i => rw [hs, cornerValue_input] at hV0; cases hV0
    | gate j =>
      rw [hs] at hMem hNeed hV0
      exact Finset.card_pos.mpr ⟨(.gate j, true), Finset.mem_inter.mpr
        ⟨hMem, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed, hV0⟩, rfl⟩⟩⟩
  have hMul := mul_card_le_of_inter_req p root (badSideAND p root) z0T 1 hInter
  have hZ := card_Z0_le p root h0 h1
  omega

theorem card_otherBad_le (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (otherBad p root).card ≤ 45 * (badGates p root).card + 54 * shared p root := by
  have hU1 : (otherBad p root).card ≤ (badFlip p root ∪ badSideOR p root).card + (badSideAND p root).card :=
    Finset.card_union_le ..
  have hU2 : (badFlip p root ∪ badSideOR p root).card ≤ (badFlip p root).card + (badSideOR p root).card :=
    Finset.card_union_le ..
  have hBF := card_badFlip_le p root h0 h1
  have hOR := card_badSideOR_le p root h0 h1
  have hAND := card_badSideAND_le p root h0 h1
  omega

theorem card_otherBad_le_slack (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (otherBad p root).card ≤ 54 * slack p root := by
  have h := card_otherBad_le p root h0 h1
  have hBad := card_badGates_le p root
  unfold slack
  omega

/-- Anomaly gates in `otherBad` preserving standard `(false, true)` corner values. -/
noncomputable def dualOtherBad (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in (otherBad p root).filter fun j =>
    cornerValue p false (.gate j) = false ∧ cornerValue p true (.gate j) = true

private theorem twoCorner_tight_bundle (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badFlip p root).card ≤ 7 * (badGates p root).card + 3 * shared p root ∧
      (badSideOR p root).card + (badSideAND p root).card ≤
        2 * (badGates p root).card + 2 * shared p root ∧
      (otherBad p root).card ≤ 9 * (badGates p root).card + 5 * shared p root ∧
      (otherBad p root \ S0 p root).card + (otherBad p root \ S1 p root).card ≤
        10 * (badGates p root).card + 7 * shared p root ∧
      (dualOtherBad p root).card ≤ 2 * (badGates p root).card + 2 * shared p root := by
  classical
  let Bad := badGates p root
  let s0 := S0 p root
  let s1 := S1 p root
  let A0 := flipA0 p root
  let B0 := flipB0 p root
  let A1 := flipA1 p root
  let B1 := flipB1 p root
  let T0 := flipT0 p root
  let T1 := flipT1 p root
  let S0T := s0.image fun j : Fin g => ((.gate j : Wire n g), true)
  let S1F := s1.image fun j : Fin g => ((.gate j : Wire n g), false)
  have hS0T : S0T.card = s0.card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hS1F : S1F.card = s1.card := Finset.card_image_of_injective _ (fun _ _ h => by cases h; rfl)
  have hS0T_bool : ∀ s ∈ S0T, s.2 = true := fun s hs => by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hs; rfl
  have hS1F_bool : ∀ s ∈ S1F, s.2 = false := fun s hs => by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hs; rfl
  have hS0Part := flip_s0_part p root
  have hS1Part := flip_s1_part p root
  have hDisj0 := flip_disj0 p root
  have hDisj1 := flip_disj1 p root
  have hS0SplitEq : (s0 ∩ Bad).card + (s0 \ Bad).card = s0.card :=
    Finset.card_inter_add_card_sdiff s0 Bad
  have hS1SplitEq : (s1 ∩ Bad).card + (s1 \ Bad).card = s1.card :=
    Finset.card_inter_add_card_sdiff s1 Bad
  have hS0Diff : (s0 \ Bad).card = A0.card + B0.card := by
    rw [hS0Part, Finset.card_union_of_disjoint hDisj0]
  have hS1Diff : (s1 \ Bad).card = A1.card + B1.card := by
    rw [hS1Part, Finset.card_union_of_disjoint hDisj1]
  -- Step A: joint bound on `A0` and `T0` using `sharedBool true`
  let T0_root := T0.filter fun j : Fin g => (.gate j : Wire n g) = root
  let T0_A0 := T0.filter fun j : Fin g => ∃ p' ∈ A0, ((.gate j : Wire n g), true) ∈ reqCorner p root true p'
  let T0_extra := (T0 \ T0_root) \ T0_A0
  have hT0_extra_Ex : ∀ j ∈ T0_extra, ∃ p' : Fin g, ((.gate j : Wire n g), true) ∈ reqCorner p root true p' := by
    intro j hj
    have hjDiff := (Finset.mem_sdiff.mp hj).1
    have hjT0 := (Finset.mem_sdiff.mp hjDiff).1
    have hjNotR := (Finset.mem_sdiff.mp hjDiff).2
    have hNeed := (flip_t0_prop p root h0 h1 hjT0).1
    have hNeRoot : ((.gate j : Wire n g), true) ≠ (root, true) := fun hEq =>
      hjNotR (Finset.mem_filter.mpr ⟨hjT0, congrArg Prod.fst hEq⟩)
    exact needCorner_parent_of_ne hNeed hNeRoot
  choose p0Of hp0Of using fun j (hj : j ∈ T0_extra) => hT0_extra_Ex j hj
  let E0 : Finset (Fin g × (Wire n g × Bool)) :=
    (s0 \ Bad).biUnion fun k => (reqCorner p root false k ∩ S0T).image fun s => (k, s)
  let E0_all : Finset (Fin g × (Wire n g × Bool)) :=
    (Finset.univ : Finset (Fin g)).biUnion fun k => (req p root k ∩ S0T).image fun s => (k, s)
  let fExtra0 (j : Fin g) : Fin g × (Wire n g × Bool) :=
    if hj : j ∈ T0_extra then (p0Of j hj, (.gate j, true)) else (j, (.gate j, true))
  have hfExtra0 {j} (hj : j ∈ T0_extra) : fExtra0 j = (p0Of j hj, (.gate j, true)) := by
    simp only [fExtra0]
    split_ifs
    rfl
  let E0_extra := T0_extra.image fExtra0
  have hE0_extra_card : E0_extra.card = T0_extra.card := by
    refine Finset.card_image_of_injOn fun j1 hj1 j2 hj2 hEq => ?_
    rw [hfExtra0 hj1, hfExtra0 hj2] at hEq
    have hSnd := congrArg (fun x : Fin g × (Wire n g × Bool) => x.2.1) hEq
    dsimp only at hSnd
    cases hSnd; rfl
  have hE0_sub : E0 ⊆ E0_all := by
    intro ps hps
    obtain ⟨k, _, hIm⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hIm
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨s,
      Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hs).1,
        (Finset.mem_inter.mp hs).2⟩, rfl⟩⟩
  have hE0_extra_sub : E0_extra ⊆ E0_all := by
    intro ps hps
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hps
    rw [hfExtra0 hj]
    have hjT0 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).1
    have hjs0 : j ∈ s0 := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hjT0).1).1).1
    exact Finset.mem_biUnion.mpr ⟨p0Of j hj, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨(.gate j, true), Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ (hp0Of j hj), Finset.mem_image.mpr ⟨j, hjs0, rfl⟩⟩, rfl⟩⟩
  have hE0_disj : Disjoint E0 E0_extra := by
    rw [Finset.disjoint_left]
    intro ps hIn0 hInE
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hInE
    rw [hfExtra0 hj] at hIn0
    obtain ⟨k, hkS, hIm⟩ := Finset.mem_biUnion.mp hIn0
    obtain ⟨s, hs, hEq⟩ := Finset.mem_image.mp hIm
    have hkEq : k = p0Of j hj := congrArg Prod.fst hEq
    have hsEq : s = (.gate j, true) := congrArg Prod.snd hEq
    rw [hsEq] at hs
    rw [hkEq] at hkS hs
    let p' := p0Of j hj
    have hMemFalse : ((.gate j : Wire n g), true) ∈ reqCorner p root false p' :=
      (Finset.mem_inter.mp hs).1
    have hMemTrue : ((.gate j : Wire n g), true) ∈ reqCorner p root true p' := hp0Of j hj
    rw [hS0Part] at hkS
    rcases Finset.mem_union.mp hkS with hkA | hkB
    · have hjNotA := (Finset.mem_sdiff.mp hj).2
      exact hjNotA (Finset.mem_filter.mpr
        ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).1, p', hkA, hMemTrue⟩)
    · have hkOp : (p.lines p').op = .or := (Finset.mem_filter.mp hkB).2
      have hkValT : cornerValue p true (.gate p') = true := by
        by_contra hNotT
        have hkValF : cornerValue p true (.gate p') = false := Bool.eq_false_iff.mpr hNotT
        have hAllF : ∀ a : Fin (signature.Arity (p.lines p').op),
            cornerValue p true ((p.lines p').wires a) = false := by
          have hCorner := hkValF
          rw [cornerValue_gate] at hCorner
          exact (op_or_false_all hkOp (p.lines p').wires (cornerValue p true) hCorner).1
        by_cases hg : NeedCorner p root true (.gate p', cornerValue p true (.gate p'))
        · simp only [reqCorner, hg, ite_true, cornerArguments] at hMemTrue
          obtain ⟨a, _, haEq⟩ := Finset.mem_image.mp hMemTrue
          have hTF : cornerValue p true ((p.lines p').wires a) = true := congrArg Prod.snd haEq
          rw [hAllF a] at hTF; cases hTF
        · simp [reqCorner, hg] at hMemTrue
      have hkT0 : p' ∈ T0 := Finset.mem_filter.mpr ⟨hkB, hkValT⟩
      obtain ⟨_, u, v, huv, hEq0, hEq1⟩ := flip_t0_prop p root h0 h1 hkT0
      rw [hEq0, Finset.mem_singleton] at hMemFalse
      rw [hEq1, Finset.mem_singleton] at hMemTrue
      exact huv ((congrArg Prod.fst hMemFalse).symm.trans (congrArg Prod.fst hMemTrue))
  have hE0_lower : 2 * A0.card + B0.card ≤ E0.card := by
    have hDisjPairs : ∀ k1 ∈ s0 \ Bad, ∀ k2 ∈ s0 \ Bad, k1 ≠ k2 →
        Disjoint ((reqCorner p root false k1 ∩ S0T).image fun s => (k1, s))
          ((reqCorner p root false k2 ∩ S0T).image fun s => (k2, s)) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro ps h1' h2'
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1'
      obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2'
      exact hne (congrArg Prod.fst hEq).symm
    have hCardE0 : E0.card = ∑ k ∈ s0 \ Bad, (reqCorner p root false k ∩ S0T).card := by
      dsimp only [E0]
      rw [Finset.card_biUnion hDisjPairs]
      refine Finset.sum_congr rfl fun k _ =>
        Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
    rw [hCardE0, hS0Part, Finset.sum_union hDisj0]
    calc
      2 * A0.card + B0.card = (∑ _k ∈ A0, 2) + (∑ _k ∈ B0, 1) := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ (∑ k ∈ A0, (reqCorner p root false k ∩ S0T).card) +
          (∑ k ∈ B0, (reqCorner p root false k ∩ S0T).card) := by
        refine Nat.add_le_add (Finset.sum_le_sum fun k hk => ?_)
          (Finset.sum_le_sum fun k hk => flip_b0_req p root h0 hk)
        obtain ⟨hSub, hCard⟩ := flip_a0_req p root h0 hk
        have hInter : reqCorner p root false k ∩ S0T = reqCorner p root false k :=
          Finset.inter_eq_left.mpr (hSub.trans Finset.inter_subset_right)
        rw [hInter]
        exact hCard
  have hE0_all_card : E0_all.card = ∑ k : Fin g, (req p root k ∩ S0T).card := by
    have hDisjAll : ∀ k1 ∈ (Finset.univ : Finset (Fin g)),
        ∀ k2 ∈ (Finset.univ : Finset (Fin g)), k1 ≠ k2 →
        Disjoint ((req p root k1 ∩ S0T).image fun s => (k1, s))
          ((req p root k2 ∩ S0T).image fun s => (k2, s)) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro ps h1' h2'
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1'
      obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2'
      exact hne (congrArg Prod.fst hEq).symm
    dsimp only [E0_all]
    rw [Finset.card_biUnion hDisjAll]
    refine Finset.sum_congr rfl fun k _ =>
      Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
  have hE0_union := Finset.card_le_card (Finset.union_subset hE0_sub hE0_extra_sub)
  rw [Finset.card_union_of_disjoint hE0_disj, hE0_extra_card, hE0_all_card] at hE0_union
  have hSum0_tight := sum_card_inter_req_le_allArgs_bool p root true Finset.univ S0T hS0T_bool
  let R0_set : Finset (Wire n g × Bool) := T0_root.image fun j : Fin g => ((.gate j : Wire n g), true)
  have hR0_card : R0_set.card = T0_root.card :=
    Finset.card_image_of_injective _ fun _ _ h => by cases h; rfl
  have hR0_sub : R0_set ⊆ S0T \ allArgs p root := by
    intro s hs
    obtain ⟨j, hjR, rfl⟩ := Finset.mem_image.mp hs
    have hjT0 := (Finset.mem_filter.mp hjR).1
    have hjEqRoot : (.gate j : Wire n g) = root := (Finset.mem_filter.mp hjR).2
    have hjs0 : j ∈ s0 := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hjT0).1).1).1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨j, hjs0, rfl⟩, ?_⟩
    rw [hjEqRoot]
    exact root_notMem_allArgs p root
  have hS0T_split : (allArgs p root ∩ S0T).card + R0_set.card ≤ S0T.card := by
    have h1' := Finset.card_le_card hR0_sub
    have h2' := Finset.card_inter_add_card_sdiff S0T (allArgs p root)
    rw [Finset.inter_comm] at h2'
    omega
  have hA0_T0_extra : A0.card + T0_extra.card + T0_root.card ≤
      (s0 ∩ Bad).card + sharedBool p root true := by
    dsimp only [T0_root, T0_extra] at hE0_lower hE0_union hSum0_tight hS0T_split hR0_card hS0T ⊢
    omega
  have hT0_A0_le : T0_A0.card ≤ 2 * (A0 ∩ Z0 p root).card := by
    let T0_img := T0_A0.image fun j : Fin g => ((.gate j : Wire n g), true)
    have hImgCard : T0_img.card = T0_A0.card :=
      Finset.card_image_of_injective _ fun _ _ h => by cases h; rfl
    have hSub : T0_img ⊆ (A0 ∩ Z0 p root).biUnion fun p' => reqCorner p root true p' := by
      intro s hs
      obtain ⟨j, hjA, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨_, p', hp'A, hp'Mem⟩ := Finset.mem_filter.mp hjA
      have hp'Need0 : NeedCorner p root false (.gate p', true) :=
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp'A).1).1).2
      have hp'V0 : cornerValue p false (.gate p') = true :=
        (needCorner_eq_cornerValue h0 hp'Need0).symm
      have hp'Op : (p.lines p').op = .and := (Finset.mem_filter.mp hp'A).2
      have hp'Ng : NeedCorner p root true (.gate p', cornerValue p true (.gate p')) := by
        by_contra hNo
        simp [reqCorner, hNo] at hp'Mem
      have hp'V1 : cornerValue p true (.gate p') = true := by
        by_contra hNotT
        have hp'F : cornerValue p true (.gate p') = false := Bool.eq_false_iff.mpr hNotT
        have hp'N1F : NeedCorner p root true (.gate p', false) := by simpa [hp'F] using hp'Ng
        obtain ⟨_, hEq1, _⟩ := and_false_req_one h1 hp'Op hp'N1F
        rw [hEq1, Finset.mem_singleton] at hp'Mem
        have hF := congrArg Prod.snd hp'Mem
        cases hF
      have hp'Z0 : p' ∈ Z0 p root :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hp'V1] using hp'Ng, hp'V0⟩
      exact Finset.mem_biUnion.mpr ⟨p', Finset.mem_inter.mpr ⟨hp'A, hp'Z0⟩, hp'Mem⟩
    have hBiUnion : ((A0 ∩ Z0 p root).biUnion fun p' => reqCorner p root true p').card ≤
        2 * (A0 ∩ Z0 p root).card := by
      calc
        _ ≤ ∑ p' ∈ A0 ∩ Z0 p root, (reqCorner p root true p').card := Finset.card_biUnion_le
        _ ≤ ∑ _p' ∈ A0 ∩ Z0 p root, 2 := by
          refine Finset.sum_le_sum fun p' _ => ?_
          by_cases hg : NeedCorner p root true (.gate p', cornerValue p true (.gate p'))
          · simp only [reqCorner, hg, ite_true]
            exact card_argumentStates_le ..
          · simp [reqCorner, hg]
        _ = 2 * (A0 ∩ Z0 p root).card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hC := Finset.card_le_card hSub
    omega
  have hT0_decomp : T0.card ≤ T0_extra.card + T0_root.card + T0_A0.card := by
    have h1' : T0 ⊆ T0_extra ∪ T0_root ∪ T0_A0 := fun j hj => by
      by_cases hA : j ∈ T0_A0
      · exact Finset.mem_union_right _ hA
      · by_cases hR : j ∈ T0_root
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hR)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hj, hR⟩, hA⟩))
    have h2' := (Finset.card_le_card h1').trans (Finset.card_union_le ..)
    have h3' := Finset.card_union_le T0_extra T0_root
    omega
  -- Step B: joint bound on `B1` and `T1` using `sharedBool false`
  let T1_B1 := T1.filter fun j : Fin g => ∃ p' ∈ B1, ((.gate j : Wire n g), false) ∈ reqCorner p root false p'
  let T1_extra := T1 \ T1_B1
  have hT1_extra_Ex : ∀ j ∈ T1_extra, ∃ p' : Fin g, ((.gate j : Wire n g), false) ∈ reqCorner p root false p' := by
    intro j hj
    have hjT1 := (Finset.mem_sdiff.mp hj).1
    have hNeed := (flip_t1_prop p root h0 h1 hjT1).1
    exact needCorner_parent_of_ne hNeed fun hEq => by cases congrArg Prod.snd hEq
  choose p1Of hp1Of using fun j (hj : j ∈ T1_extra) => hT1_extra_Ex j hj
  let E1 : Finset (Fin g × (Wire n g × Bool)) :=
    (s1 \ Bad).biUnion fun k => (reqCorner p root true k ∩ S1F).image fun s => (k, s)
  let E1_all : Finset (Fin g × (Wire n g × Bool)) :=
    (Finset.univ : Finset (Fin g)).biUnion fun k => (req p root k ∩ S1F).image fun s => (k, s)
  let fExtra1 (j : Fin g) : Fin g × (Wire n g × Bool) :=
    if hj : j ∈ T1_extra then (p1Of j hj, (.gate j, false)) else (j, (.gate j, false))
  have hfExtra1 {j} (hj : j ∈ T1_extra) : fExtra1 j = (p1Of j hj, (.gate j, false)) := by
    simp only [fExtra1]
    split_ifs
    rfl
  let E1_extra := T1_extra.image fExtra1
  have hE1_extra_card : E1_extra.card = T1_extra.card := by
    refine Finset.card_image_of_injOn fun j1 hj1 j2 hj2 hEq => ?_
    rw [hfExtra1 hj1, hfExtra1 hj2] at hEq
    have hSnd := congrArg (fun x : Fin g × (Wire n g × Bool) => x.2.1) hEq
    dsimp only at hSnd
    cases hSnd; rfl
  have hE1_sub : E1 ⊆ E1_all := by
    intro ps hps
    obtain ⟨k, _, hIm⟩ := Finset.mem_biUnion.mp hps
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hIm
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨s,
      Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hs).1,
        (Finset.mem_inter.mp hs).2⟩, rfl⟩⟩
  have hE1_extra_sub : E1_extra ⊆ E1_all := by
    intro ps hps
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hps
    rw [hfExtra1 hj]
    have hjT1 := (Finset.mem_sdiff.mp hj).1
    have hjs1 : j ∈ s1 := (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hjT1).1).1).1
    exact Finset.mem_biUnion.mpr ⟨p1Of j hj, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨(.gate j, false), Finset.mem_inter.mpr
        ⟨Finset.mem_union_left _ (hp1Of j hj), Finset.mem_image.mpr ⟨j, hjs1, rfl⟩⟩, rfl⟩⟩
  have hE1_disj : Disjoint E1 E1_extra := by
    rw [Finset.disjoint_left]
    intro ps hIn1 hInE
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hInE
    rw [hfExtra1 hj] at hIn1
    obtain ⟨k, hkS, hIm⟩ := Finset.mem_biUnion.mp hIn1
    obtain ⟨s, hs, hEq⟩ := Finset.mem_image.mp hIm
    have hkEq : k = p1Of j hj := congrArg Prod.fst hEq
    have hsEq : s = (.gate j, false) := congrArg Prod.snd hEq
    rw [hsEq] at hs
    rw [hkEq] at hkS hs
    let p' := p1Of j hj
    have hMemTrue : ((.gate j : Wire n g), false) ∈ reqCorner p root true p' :=
      (Finset.mem_inter.mp hs).1
    have hMemFalse : ((.gate j : Wire n g), false) ∈ reqCorner p root false p' := hp1Of j hj
    rw [hS1Part] at hkS
    rcases Finset.mem_union.mp hkS with hkA | hkB
    · have hkOp : (p.lines p').op = .and := (Finset.mem_filter.mp hkA).2
      have hkValF : cornerValue p false (.gate p') = false := by
        by_contra hNotF
        have hkValT : cornerValue p false (.gate p') = true := Bool.eq_true_of_not_eq_false hNotF
        have hAllT : ∀ a : Fin (signature.Arity (p.lines p').op),
            cornerValue p false ((p.lines p').wires a) = true := by
          have hCorner := hkValT
          rw [cornerValue_gate] at hCorner
          exact (op_and_true_all hkOp (p.lines p').wires (cornerValue p false) hCorner).1
        by_cases hg : NeedCorner p root false (.gate p', cornerValue p false (.gate p'))
        · simp only [reqCorner, hg, ite_true, cornerArguments] at hMemFalse
          obtain ⟨a, _, haEq⟩ := Finset.mem_image.mp hMemFalse
          have hFT : cornerValue p false ((p.lines p').wires a) = false := congrArg Prod.snd haEq
          rw [hAllT a] at hFT; cases hFT
        · simp [reqCorner, hg] at hMemFalse
      have hkT1 : p' ∈ T1 := Finset.mem_filter.mpr ⟨hkA, hkValF⟩
      obtain ⟨_, u, v, huv, hEq1, hEq0⟩ := flip_t1_prop p root h0 h1 hkT1
      rw [hEq1, Finset.mem_singleton] at hMemTrue
      rw [hEq0, Finset.mem_singleton] at hMemFalse
      exact huv ((congrArg Prod.fst hMemTrue).symm.trans (congrArg Prod.fst hMemFalse))
    · have hjNotB := (Finset.mem_sdiff.mp hj).2
      exact hjNotB (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, p', hkB, hMemFalse⟩)
  have hE1_lower : 2 * B1.card + A1.card ≤ E1.card := by
    have hDisjPairs : ∀ k1 ∈ s1 \ Bad, ∀ k2 ∈ s1 \ Bad, k1 ≠ k2 →
        Disjoint ((reqCorner p root true k1 ∩ S1F).image fun s => (k1, s))
          ((reqCorner p root true k2 ∩ S1F).image fun s => (k2, s)) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro ps h1' h2'
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1'
      obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2'
      exact hne (congrArg Prod.fst hEq).symm
    have hCardE1 : E1.card = ∑ k ∈ s1 \ Bad, (reqCorner p root true k ∩ S1F).card := by
      dsimp only [E1]
      rw [Finset.card_biUnion hDisjPairs]
      refine Finset.sum_congr rfl fun k _ =>
        Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
    rw [hCardE1, hS1Part, Finset.sum_union hDisj1]
    calc
      2 * B1.card + A1.card = (∑ _k ∈ B1, 2) + (∑ _k ∈ A1, 1) := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ (∑ k ∈ B1, (reqCorner p root true k ∩ S1F).card) +
          (∑ k ∈ A1, (reqCorner p root true k ∩ S1F).card) := by
        refine Nat.add_le_add (Finset.sum_le_sum fun k hk => ?_)
          (Finset.sum_le_sum fun k hk => flip_a1_req p root h1 hk)
        obtain ⟨hSub, hCard⟩ := flip_b1_req p root h1 hk
        have hInter : reqCorner p root true k ∩ S1F = reqCorner p root true k :=
          Finset.inter_eq_left.mpr (hSub.trans Finset.inter_subset_right)
        rw [hInter]
        exact hCard
      _ = (∑ k ∈ A1, (reqCorner p root true k ∩ S1F).card) +
          (∑ k ∈ B1, (reqCorner p root true k ∩ S1F).card) := Nat.add_comm ..
  have hE1_all_card : E1_all.card = ∑ k : Fin g, (req p root k ∩ S1F).card := by
    have hDisjAll : ∀ k1 ∈ (Finset.univ : Finset (Fin g)),
        ∀ k2 ∈ (Finset.univ : Finset (Fin g)), k1 ≠ k2 →
        Disjoint ((req p root k1 ∩ S1F).image fun s => (k1, s))
          ((req p root k2 ∩ S1F).image fun s => (k2, s)) := by
      intro k1 _ k2 _ hne
      rw [Finset.disjoint_left]
      intro ps h1' h2'
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1'
      obtain ⟨_, _, hEq⟩ := Finset.mem_image.mp h2'
      exact hne (congrArg Prod.fst hEq).symm
    dsimp only [E1_all]
    rw [Finset.card_biUnion hDisjAll]
    refine Finset.sum_congr rfl fun k _ =>
      Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
  have hE1_union := Finset.card_le_card (Finset.union_subset hE1_sub hE1_extra_sub)
  rw [Finset.card_union_of_disjoint hE1_disj, hE1_extra_card, hE1_all_card] at hE1_union
  have hSum1_tight := sum_card_inter_req_le_bool p root false Finset.univ S1F hS1F_bool
  have hB1_T1_extra : B1.card + T1_extra.card ≤ (s1 ∩ Bad).card + sharedBool p root false := by
    dsimp only [T1_extra] at hE1_lower hE1_union hSum1_tight hS1F ⊢
    omega
  have hT1_B1_le : T1_B1.card ≤ 2 * (B1 ∩ Z1 p root).card := by
    let T1_img := T1_B1.image fun j : Fin g => ((.gate j : Wire n g), false)
    have hImgCard : T1_img.card = T1_B1.card :=
      Finset.card_image_of_injective _ fun _ _ h => by cases h; rfl
    have hSub : T1_img ⊆ (B1 ∩ Z1 p root).biUnion fun p' => reqCorner p root false p' := by
      intro s hs
      obtain ⟨j, hjB, rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨_, p', hp'B, hp'Mem⟩ := Finset.mem_filter.mp hjB
      have hp'Need1 : NeedCorner p root true (.gate p', false) :=
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp'B).1).1).2
      have hp'V1 : cornerValue p true (.gate p') = false :=
        (needCorner_eq_cornerValue h1 hp'Need1).symm
      have hp'Op : (p.lines p').op = .or := (Finset.mem_filter.mp hp'B).2
      have hp'Ng : NeedCorner p root false (.gate p', cornerValue p false (.gate p')) := by
        by_contra hNo
        simp [reqCorner, hNo] at hp'Mem
      have hp'V0 : cornerValue p false (.gate p') = false := by
        by_contra hNotF
        have hp'T : cornerValue p false (.gate p') = true := Bool.eq_true_of_not_eq_false hNotF
        have hp'N0T : NeedCorner p root false (.gate p', true) := by simpa [hp'T] using hp'Ng
        obtain ⟨_, hEq0, _⟩ := or_true_req_one h0 hp'Op hp'N0T
        rw [hEq0, Finset.mem_singleton] at hp'Mem
        have hF := congrArg Prod.snd hp'Mem
        cases hF
      have hp'Z1 : p' ∈ Z1 p root :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hp'V0] using hp'Ng, hp'V1⟩
      exact Finset.mem_biUnion.mpr ⟨p', Finset.mem_inter.mpr ⟨hp'B, hp'Z1⟩, hp'Mem⟩
    have hBiUnion : ((B1 ∩ Z1 p root).biUnion fun p' => reqCorner p root false p').card ≤
        2 * (B1 ∩ Z1 p root).card := by
      calc
        _ ≤ ∑ p' ∈ B1 ∩ Z1 p root, (reqCorner p root false p').card := Finset.card_biUnion_le
        _ ≤ ∑ _p' ∈ B1 ∩ Z1 p root, 2 := by
          refine Finset.sum_le_sum fun p' _ => ?_
          by_cases hg : NeedCorner p root false (.gate p', cornerValue p false (.gate p'))
          · simp only [reqCorner, hg, ite_true]
            exact card_argumentStates_le ..
          · simp [reqCorner, hg]
        _ = 2 * (B1 ∩ Z1 p root).card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    have hC := Finset.card_le_card hSub
    omega
  have hT1_decomp : T1.card ≤ T1_extra.card + T1_B1.card := by
    have h1' : T1 ⊆ T1_extra ∪ T1_B1 := fun j hj => by
      by_cases hB : j ∈ T1_B1
      · exact Finset.mem_union_right _ hB
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hj, hB⟩)
    exact (Finset.card_le_card h1').trans (Finset.card_union_le ..)
  -- Step C: joint `badSideAND` / `badSideOR` bounds
  let z0 := Z0 p root
  let z0Diff := z0 \ (Bad ∪ T0)
  let z0T := z0.image fun j : Fin g => ((.gate j : Wire n g), true)
  have hz0T : z0T.card = z0.card := Finset.card_image_of_injective _ fun _ _ h => by cases h; rfl
  have hz0T_bool : ∀ s ∈ z0T, s.2 = true := fun s hs => by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hs; rfl
  have hZ0_diff_req : ∀ k ∈ z0Diff, 2 ≤ (req p root k ∩ z0T).card := by
    intro k hk
    obtain ⟨hkZ, hkN⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hN1, hV0⟩ := (Finset.mem_filter.mp hkZ).2
    have hnb : k ∉ Bad := fun h => hkN (Finset.mem_union_left _ h)
    have hnT0 : k ∉ T0 := fun h => hkN (Finset.mem_union_right _ h)
    have hStr := not_bad_structure p root hnb
    have hOpAnd : (p.lines k).op = .and := by
      rcases hStr.1 with hAnd | hOr
      · exact hAnd
      · exfalso
        have hVal : valSet p root k = {true} := by
          ext v
          simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hN
            cases v with
            | true => rfl
            | false =>
              rcases need_gate_eq_false h0 h1 hN with ⟨_, hcf⟩ | ⟨ht, _⟩
              · rw [hV0] at hcf; cases hcf
              · have he := needCorner_eq_cornerValue h1 hN1
                have he' := needCorner_eq_cornerValue h1 ht
                rw [← he] at he'; cases he'
          · rintro rfl; exact Or.inr hN1
        have hReqEq : (req p root k).card = 2 := by rw [hStr.2.1, hVal, Finset.card_singleton]
        obtain ⟨_, hEq1, _⟩ := or_true_req_one h1 hOr hN1
        have hNeed0 : NeedCorner p root false (.gate k, true) := by
          by_contra hNo
          have hEmpty0 : reqCorner p root false k = ∅ := by
            have hNo' : ¬NeedCorner p root false (.gate k, cornerValue p false (.gate k)) := by
              simpa [hV0] using hNo
            simp [reqCorner, hNo']
          rw [req, hEmpty0, Finset.empty_union, hEq1, Finset.card_singleton] at hReqEq
          omega
        have hkB0 : k ∈ B0 := Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed0⟩, hnb⟩, hOr⟩
        have hkV1 : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hN1).symm
        exact hnT0 (Finset.mem_filter.mpr ⟨hkB0, hkV1⟩)
    obtain ⟨hMem, _⟩ := and_true_req_both h1 hnb hOpAnd hN1
    have hV0Inputs : ∀ a : Fin (signature.Arity (p.lines k).op),
        cornerValue p false ((p.lines k).wires a) = true := by
      have hCorner := hV0
      rw [cornerValue_gate] at hCorner
      exact (op_and_true_all hOpAnd (p.lines k).wires (cornerValue p false) hCorner).1
    have hSubK : Finset.univ.image (fun a => ((p.lines k).wires a, true)) ⊆ req p root k ∩ z0T := by
      intro key hKey
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
      refine Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (hMem a), ?_⟩
      have hV0a := hV0Inputs a
      cases hw : (p.lines k).wires a with
      | input i => rw [hw, cornerValue_input] at hV0a; cases hV0a
      | gate j =>
        have hChild := needCorner_child_of_mem_reqCorner (hMem a)
        rw [hw] at hChild hV0a
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hChild, hV0a⟩, rfl⟩
    have hInj : Function.Injective (fun a => ((p.lines k).wires a, true)) := by
      intro a0 a1 he
      by_contra hne
      exact hStr.2.2.2 a0 a1 hne (congrArg Prod.fst he)
    have hCard := Finset.card_le_card hSubK
    rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin,
      op_arity_two (Or.inl hOpAnd)] at hCard
    exact hCard
  have hBadSideAND_req : ∀ k ∈ badSideAND p root, 1 ≤ (req p root k ∩ z0T).card := by
    intro k hk
    obtain ⟨hDual, hnbF, hV0⟩ := (Finset.mem_filter.mp hk).2
    have hnb := (not_s0_s1_of_not_badFlip hnbF).1
    have hChild := dualAND_children h0 h1 hnb hDual
    have hMem := hChild.2.2.2.2.1
    have hNeed := hChild.2.2.2.2.2.2.2.1
    cases hs : sideChild p k with
    | input i => rw [hs, cornerValue_input] at hV0; cases hV0
    | gate j =>
      rw [hs] at hMem hNeed hV0
      exact Finset.card_pos.mpr ⟨(.gate j, true), Finset.mem_inter.mpr
        ⟨hMem, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed, hV0⟩, rfl⟩⟩⟩
  have hDisjZ0AND : Disjoint z0Diff (badSideAND p root) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have hV0T : cornerValue p false (.gate k) = true :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk1).1).2.2
    have hN0F : NeedCorner p root false (.gate k, false) := (Finset.mem_filter.mp hk2).2.1.2.1
    have hV0F : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hN0F).symm
    rw [hV0T] at hV0F; cases hV0F
  have hSumZ0 := sum_card_inter_req_le_bool p root true (z0Diff ∪ badSideAND p root) z0T hz0T_bool
  have hSumZ0_ge : 2 * z0Diff.card + (badSideAND p root).card ≤
      ∑ k ∈ z0Diff ∪ badSideAND p root, (req p root k ∩ z0T).card := by
    rw [Finset.sum_union hDisjZ0AND]
    calc
      2 * z0Diff.card + (badSideAND p root).card =
          (∑ _k ∈ z0Diff, 2) + (∑ _k ∈ badSideAND p root, 1) := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Nat.add_le_add (Finset.sum_le_sum hZ0_diff_req) (Finset.sum_le_sum hBadSideAND_req)
  have hZ0_cover : z0.card ≤ z0Diff.card + (z0 ∩ Bad).card + T0.card := by
    have hSub : z0 ⊆ z0Diff ∪ (z0 ∩ Bad) ∪ T0 := fun k hk => by
      by_cases hT : k ∈ T0
      · exact Finset.mem_union_right _ hT
      · by_cases hB : k ∈ Bad
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hk, hB⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨hk, fun hU => by rcases Finset.mem_union.mp hU with h1' | h2'; exact hB h1'; exact hT h2'⟩))
    have h1' := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
    have h2' := Finset.card_union_le z0Diff (z0 ∩ Bad)
    omega
  have hA0Z0_sub : A0 ∩ z0 ⊆ z0Diff := by
    intro k hk
    obtain ⟨hkA, hkZ⟩ := Finset.mem_inter.mp hk
    refine Finset.mem_sdiff.mpr ⟨hkZ, fun hU => ?_⟩
    rcases Finset.mem_union.mp hU with hB | hT
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hkA).1).2 hB
    · have hAnd : (p.lines k).op = .and := (Finset.mem_filter.mp hkA).2
      have hOr : (p.lines k).op = .or := (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).2
      rw [hAnd] at hOr; cases hOr
  have hA0Z0_card : (A0 ∩ z0).card ≤ z0Diff.card := Finset.card_le_card hA0Z0_sub
  have hA0Z0_leA0 : (A0 ∩ z0).card ≤ A0.card := Finset.card_le_card Finset.inter_subset_left
  have hBadSideAND_le : (badSideAND p root).card ≤
      (z0 ∩ Bad).card + (s0 ∩ Bad).card + 2 * sharedBool p root true := by
    dsimp only [z0] at hSumZ0 hSumZ0_ge hz0T hZ0_cover hA0Z0_card hA0Z0_leA0 hT0_A0_le ⊢
    omega
  -- Symmetric bound for `badSideOR`
  let z1 := Z1 p root
  let z1Diff := z1 \ (Bad ∪ T1)
  let z1F := z1.image fun j : Fin g => ((.gate j : Wire n g), false)
  have hz1F : z1F.card = z1.card := Finset.card_image_of_injective _ fun _ _ h => by cases h; rfl
  have hz1F_bool : ∀ s ∈ z1F, s.2 = false := fun s hs => by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hs; rfl
  have hZ1_diff_req : ∀ k ∈ z1Diff, 2 ≤ (req p root k ∩ z1F).card := by
    intro k hk
    obtain ⟨hkZ, hkN⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hN0, hV1⟩ := (Finset.mem_filter.mp hkZ).2
    have hnb : k ∉ Bad := fun h => hkN (Finset.mem_union_left _ h)
    have hnT1 : k ∉ T1 := fun h => hkN (Finset.mem_union_right _ h)
    have hStr := not_bad_structure p root hnb
    have hOpOr : (p.lines k).op = .or := by
      rcases hStr.1 with hAnd | hOr
      · exfalso
        have hVal : valSet p root k = {false} := by
          ext v
          simp only [valSet, stateValues, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hN
            cases v with
            | false => rfl
            | true =>
              rcases need_gate_eq_true h0 h1 hN with ⟨hf, _⟩ | ⟨_, hct⟩
              · have he := needCorner_eq_cornerValue h0 hN0
                have he' := needCorner_eq_cornerValue h0 hf
                rw [← he] at he'; cases he'
              · rw [hV1] at hct; cases hct
          · rintro rfl; exact Or.inl hN0
        have hReqEq : (req p root k).card = 2 := by rw [hStr.2.1, hVal, Finset.card_singleton]
        obtain ⟨_, hEq0, _⟩ := and_false_req_one h0 hAnd hN0
        have hNeed1 : NeedCorner p root true (.gate k, false) := by
          by_contra hNo
          have hEmpty1 : reqCorner p root true k = ∅ := by
            have hNo' : ¬NeedCorner p root true (.gate k, cornerValue p true (.gate k)) := by
              simpa [hV1] using hNo
            simp [reqCorner, hNo']
          rw [req, hEmpty1, Finset.union_empty, hEq0, Finset.card_singleton] at hReqEq
          omega
        have hkA1 : k ∈ A1 := Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed1⟩, hnb⟩, hAnd⟩
        have hkV0 : cornerValue p false (.gate k) = false := (needCorner_eq_cornerValue h0 hN0).symm
        exact hnT1 (Finset.mem_filter.mpr ⟨hkA1, hkV0⟩)
      · exact hOr
    obtain ⟨hMem, _⟩ := or_false_req_both h0 hnb hOpOr hN0
    have hV1Inputs : ∀ a : Fin (signature.Arity (p.lines k).op),
        cornerValue p true ((p.lines k).wires a) = false := by
      have hCorner := hV1
      rw [cornerValue_gate] at hCorner
      exact (op_or_false_all hOpOr (p.lines k).wires (cornerValue p true) hCorner).1
    have hSubK : Finset.univ.image (fun a => ((p.lines k).wires a, false)) ⊆ req p root k ∩ z1F := by
      intro key hKey
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hKey
      refine Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hMem a), ?_⟩
      have hV1a := hV1Inputs a
      cases hw : (p.lines k).wires a with
      | input i => rw [hw, cornerValue_input] at hV1a; cases hV1a
      | gate j =>
        have hChild := needCorner_child_of_mem_reqCorner (hMem a)
        rw [hw] at hChild hV1a
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hChild, hV1a⟩, rfl⟩
    have hInj : Function.Injective (fun a => ((p.lines k).wires a, false)) := by
      intro a0 a1 he
      by_contra hne
      exact hStr.2.2.2 a0 a1 hne (congrArg Prod.fst he)
    have hCard := Finset.card_le_card hSubK
    rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin,
      op_arity_two (Or.inr hOpOr)] at hCard
    exact hCard
  have hBadSideOR_req : ∀ k ∈ badSideOR p root, 1 ≤ (req p root k ∩ z1F).card := by
    intro k hk
    obtain ⟨hDual, hnbF, hV1⟩ := (Finset.mem_filter.mp hk).2
    have hnb := (not_s0_s1_of_not_badFlip hnbF).1
    have hChild := dualOR_children h0 h1 hnb hDual
    have hMem := hChild.2.2.2.2.1
    have hNeed := hChild.2.2.2.2.2.2.2.1
    cases hs : sideChild p k with
    | input i => rw [hs, cornerValue_input] at hV1; cases hV1
    | gate j =>
      rw [hs] at hMem hNeed hV1
      exact Finset.card_pos.mpr ⟨(.gate j, false), Finset.mem_inter.mpr
        ⟨hMem, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNeed, hV1⟩, rfl⟩⟩⟩
  have hDisjZ1OR : Disjoint z1Diff (badSideOR p root) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have hV1F : cornerValue p true (.gate k) = false :=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hk1).1).2.2
    have hN1T : NeedCorner p root true (.gate k, true) := (Finset.mem_filter.mp hk2).2.1.2.2
    have hV1T : cornerValue p true (.gate k) = true := (needCorner_eq_cornerValue h1 hN1T).symm
    rw [hV1F] at hV1T; cases hV1T
  have hSumZ1 := sum_card_inter_req_le_bool p root false (z1Diff ∪ badSideOR p root) z1F hz1F_bool
  have hSumZ1_ge : 2 * z1Diff.card + (badSideOR p root).card ≤
      ∑ k ∈ z1Diff ∪ badSideOR p root, (req p root k ∩ z1F).card := by
    rw [Finset.sum_union hDisjZ1OR]
    calc
      2 * z1Diff.card + (badSideOR p root).card =
          (∑ _k ∈ z1Diff, 2) + (∑ _k ∈ badSideOR p root, 1) := by
        simp [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Nat.add_le_add (Finset.sum_le_sum hZ1_diff_req) (Finset.sum_le_sum hBadSideOR_req)
  have hZ1_cover : z1.card ≤ z1Diff.card + (z1 ∩ Bad).card + T1.card := by
    have hSub : z1 ⊆ z1Diff ∪ (z1 ∩ Bad) ∪ T1 := fun k hk => by
      by_cases hT : k ∈ T1
      · exact Finset.mem_union_right _ hT
      · by_cases hB : k ∈ Bad
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hk, hB⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_sdiff.mpr ⟨hk, fun hU => by rcases Finset.mem_union.mp hU with h1' | h2'; exact hB h1'; exact hT h2'⟩))
    have h1' := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
    have h2' := Finset.card_union_le z1Diff (z1 ∩ Bad)
    omega
  have hB1Z1_sub : B1 ∩ z1 ⊆ z1Diff := by
    intro k hk
    obtain ⟨hkB, hkZ⟩ := Finset.mem_inter.mp hk
    refine Finset.mem_sdiff.mpr ⟨hkZ, fun hU => ?_⟩
    rcases Finset.mem_union.mp hU with hB | hT
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hkB).1).2 hB
    · have hOr : (p.lines k).op = .or := (Finset.mem_filter.mp hkB).2
      have hAnd : (p.lines k).op = .and := (Finset.mem_filter.mp (Finset.mem_filter.mp hT).1).2
      rw [hOr] at hAnd; cases hAnd
  have hB1Z1_card : (B1 ∩ z1).card ≤ z1Diff.card := Finset.card_le_card hB1Z1_sub
  have hB1Z1_leB1 : (B1 ∩ z1).card ≤ B1.card := Finset.card_le_card Finset.inter_subset_left
  have hBadSideOR_le : (badSideOR p root).card ≤
      (z1 ∩ Bad).card + (s1 ∩ Bad).card + 2 * sharedBool p root false := by
    dsimp only [z1] at hSumZ1 hSumZ1_ge hz1F hZ1_cover hB1Z1_card hB1Z1_leB1 hT1_B1_le ⊢
    omega
  -- Step D: Disjoint packings inside `Bad` and final assembly
  let Bad_dual := Bad.filter fun j =>
    cornerValue p false (.gate j) = false ∧ cornerValue p true (.gate j) = true
  have hBadSplit0 : (Bad \ s0).card + (s0 ∩ Bad).card = Bad.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter Bad s0
  have hBadSplit1 : (Bad \ s1).card + (s1 ∩ Bad).card = Bad.card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter Bad s1
  have hDisjBad0 : Disjoint Bad_dual (z1 ∩ Bad) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hT := (Finset.mem_filter.mp hj1).2.2
    have hF := (Finset.mem_filter.mp (Finset.mem_inter.mp hj2).1).2.2
    rw [hT] at hF; cases hF
  have hDisjBad1 : Disjoint (Bad_dual ∪ (z1 ∩ Bad)) (s0 ∩ Bad) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have hS0 : cornerValue p false (.gate j) = true :=
      (needCorner_eq_cornerValue h0 (Finset.mem_filter.mp (Finset.mem_inter.mp hj2).1).2).symm
    have hF : cornerValue p false (.gate j) = false := by
      rcases Finset.mem_union.mp hj1 with hd | hz
      · exact (Finset.mem_filter.mp hd).2.1
      · exact (needCorner_eq_cornerValue h0 (Finset.mem_filter.mp (Finset.mem_inter.mp hz).1).2.1).symm
    rw [hS0] at hF; cases hF
  have hPackBad0 : Bad_dual.card + (z1 ∩ Bad).card + (s0 ∩ Bad).card ≤ Bad.card := by
    have hSub : Bad_dual ∪ (z1 ∩ Bad) ∪ (s0 ∩ Bad) ⊆ Bad := by
      refine Finset.union_subset (Finset.union_subset ?_ Finset.inter_subset_right)
        Finset.inter_subset_right
      exact Finset.filter_subset _ _
    have hCard := Finset.card_le_card hSub
    rw [Finset.card_union_of_disjoint hDisjBad1, Finset.card_union_of_disjoint hDisjBad0] at hCard
    exact hCard
  have hPackBad1 : (z0 ∩ Bad).card + (s1 ∩ Bad).card ≤ Bad.card := by
    have hDisj : Disjoint (z0 ∩ Bad) (s1 ∩ Bad) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have hT := (needCorner_eq_cornerValue h1 (Finset.mem_filter.mp (Finset.mem_inter.mp hj1).1).2.1).symm
      have hF := (needCorner_eq_cornerValue h1 (Finset.mem_filter.mp (Finset.mem_inter.mp hj2).1).2).symm
      rw [hT] at hF; cases hF
    have hSub : (z0 ∩ Bad) ∪ (s1 ∩ Bad) ⊆ Bad :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hCard := Finset.card_le_card hSub
    rw [Finset.card_union_of_disjoint hDisj] at hCard
    exact hCard
  have hShAdd := sharedBool_add p root
  have hs0Bad : (S0 p root ∩ badGates p root).card ≤ (badGates p root).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hs1Bad : (S1 p root ∩ badGates p root).card ≤ (badGates p root).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hA0T0_le : A0.card + T0.card ≤ 3 * (s0 ∩ Bad).card + 3 * sharedBool p root true := by
    dsimp only [z0, Bad, s0] at hA0_T0_extra hT0_A0_le hA0Z0_leA0 hT0_decomp ⊢
    omega
  have hB1T1_le : B1.card + T1.card ≤ 3 * (s1 ∩ Bad).card + 3 * sharedBool p root false := by
    dsimp only [z1, Bad, s1] at hB1_T1_extra hT1_B1_le hB1Z1_leB1 hT1_decomp ⊢
    omega
  have hFlipCard : (flipGates p root).card ≤ A0.card + B1.card + T0.card + T1.card := by
    have h1' := Finset.card_le_card (flip_gates_sub p root h0 h1)
    have h2' := Finset.card_union_le (A0 ∪ B1 ∪ T0) T1
    have h3' := Finset.card_union_le (A0 ∪ B1) T0
    have h4' := Finset.card_union_le A0 B1
    dsimp only [A0, B1, T0, T1] at h1' h2' h3' h4' ⊢
    omega
  have hBF : (badFlip p root).card ≤ Bad.card + (flipGates p root).card := Finset.card_union_le ..
  have hOB_U1 : (otherBad p root).card ≤ (badFlip p root ∪ badSideOR p root).card + (badSideAND p root).card :=
    Finset.card_union_le ..
  have hOB_U2 : (badFlip p root ∪ badSideOR p root).card ≤ (badFlip p root).card + (badSideOR p root).card :=
    Finset.card_union_le ..
  have hOB_sdiff_s0 : (otherBad p root \ s0).card ≤
      (Bad \ s0).card + B1.card + T1.card + (badSideOR p root).card + (badSideAND p root).card := by
    have hSub : otherBad p root \ s0 ⊆ (Bad \ s0) ∪ B1 ∪ T1 ∪ badSideOR p root ∪ badSideAND p root := by
      intro k hk
      obtain ⟨hkOB, hns0⟩ := Finset.mem_sdiff.mp hk
      rcases Finset.mem_union.mp hkOB with hL | hAND
      · rcases Finset.mem_union.mp hL with hBF' | hOR
        · rcases Finset.mem_union.mp hBF' with hB | hF
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hB, hns0⟩))))
          · have hF' := flip_gates_sub p root h0 h1 hF
            rcases Finset.mem_union.mp hF' with hL1 | hT1
            · rcases Finset.mem_union.mp hL1 with hL2 | hT0
              · rcases Finset.mem_union.mp hL2 with hA0 | hB1
                · exact (hns0 (Finset.mem_sdiff.mp (Finset.mem_filter.mp hA0).1).1).elim
                · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ hB1)))
              · exact (hns0 (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hT0).1).1).1).elim
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hT1))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hOR)
      · exact Finset.mem_union_right _ hAND
    have h1' := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
    have h2' := Finset.card_union_le ((Bad \ s0) ∪ B1 ∪ T1) (badSideOR p root)
    have h3' := Finset.card_union_le ((Bad \ s0) ∪ B1) T1
    have h4' := Finset.card_union_le (Bad \ s0) B1
    omega
  have hOB_sdiff_s1 : (otherBad p root \ s1).card ≤
      (Bad \ s1).card + A0.card + T0.card + (badSideOR p root).card + (badSideAND p root).card := by
    have hSub : otherBad p root \ s1 ⊆ (Bad \ s1) ∪ A0 ∪ T0 ∪ badSideOR p root ∪ badSideAND p root := by
      intro k hk
      obtain ⟨hkOB, hns1⟩ := Finset.mem_sdiff.mp hk
      rcases Finset.mem_union.mp hkOB with hL | hAND
      · rcases Finset.mem_union.mp hL with hBF' | hOR
        · rcases Finset.mem_union.mp hBF' with hB | hF
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hB, hns1⟩))))
          · have hF' := flip_gates_sub p root h0 h1 hF
            rcases Finset.mem_union.mp hF' with hL1 | hT1
            · rcases Finset.mem_union.mp hL1 with hL2 | hT0
              · rcases Finset.mem_union.mp hL2 with hA0 | hB1
                · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ hA0)))
                · exact (hns1 (Finset.mem_sdiff.mp (Finset.mem_filter.mp hB1).1).1).elim
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hT0))
            · exact (hns1 (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hT1).1).1).1).elim
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hOR)
      · exact Finset.mem_union_right _ hAND
    have h1' := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
    have h2' := Finset.card_union_le ((Bad \ s1) ∪ A0 ∪ T0) (badSideOR p root)
    have h3' := Finset.card_union_le ((Bad \ s1) ∪ A0) T0
    have h4' := Finset.card_union_le (Bad \ s1) A0
    omega
  have hDualOB_card : (dualOtherBad p root).card ≤
      Bad_dual.card + (badSideOR p root).card + (badSideAND p root).card := by
    have hSub : dualOtherBad p root ⊆ Bad_dual ∪ badSideOR p root ∪ badSideAND p root := by
      intro k hk
      obtain ⟨hkOB, hkV0, hkV1⟩ := Finset.mem_filter.mp hk
      rcases Finset.mem_union.mp hkOB with hL | hAND
      · rcases Finset.mem_union.mp hL with hBF' | hOR
        · rcases Finset.mem_union.mp hBF' with hB | hF
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨hB, hkV0, hkV1⟩))
          · exfalso
            have hU := (Finset.mem_sdiff.mp hF).1
            rcases Finset.mem_union.mp hU with h0' | h1'
            · have he := (needCorner_eq_cornerValue h0 (Finset.mem_filter.mp h0').2).symm
              rw [he] at hkV0; cases hkV0
            · have he := (needCorner_eq_cornerValue h1 (Finset.mem_filter.mp h1').2).symm
              rw [he] at hkV1; cases hkV1
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hOR)
      · exact Finset.mem_union_right _ hAND
    have h1' := (Finset.card_le_card hSub).trans (Finset.card_union_le ..)
    have h2' := Finset.card_union_le Bad_dual (badSideOR p root)
    omega
  dsimp only [Bad, s0, s1, z0, z1, A0, B1, T0, T1] at hBadSplit0 hBadSplit1 hPackBad0 hPackBad1 hA0T0_le hB1T1_le hBadSideAND_le hBadSideOR_le hFlipCard hBF hOB_U1 hOB_U2 hOB_sdiff_s0 hOB_sdiff_s1 hDualOB_card
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem card_badFlip_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badFlip p root).card ≤ 7 * (badGates p root).card + 3 * shared p root :=
  (twoCorner_tight_bundle p root h0 h1).1

theorem card_badSideOR_add_badSideAND_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (badSideOR p root).card + (badSideAND p root).card ≤
      2 * (badGates p root).card + 2 * shared p root :=
  (twoCorner_tight_bundle p root h0 h1).2.1

theorem card_otherBad_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (otherBad p root).card ≤ 9 * (badGates p root).card + 5 * shared p root :=
  (twoCorner_tight_bundle p root h0 h1).2.2.1

theorem card_otherBad_sdiff_S0_add_S1_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (otherBad p root \ S0 p root).card + (otherBad p root \ S1 p root).card ≤
      10 * (badGates p root).card + 7 * shared p root :=
  (twoCorner_tight_bundle p root h0 h1).2.2.2.1

theorem card_dualOtherBad_le_tight (p : Program signature n g) (root : Wire n g)
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true) :
    (dualOtherBad p root).card ≤ 2 * (badGates p root).card + 2 * shared p root :=
  (twoCorner_tight_bundle p root h0 h1).2.2.2.2

theorem not_badFlip_of_not_otherBad {p : Program signature n g} {root : Wire n g} {k : Fin g}
    (hk : k ∉ otherBad p root) : k ∉ badFlip p root :=
  fun h => hk (Finset.mem_union_left _ (Finset.mem_union_left _ h))

theorem goodDual_iff {p : Program signature n g} {root : Wire n g} {k : Fin g} :
    k ∈ goodDual p root ↔ IsDual p root k ∧ k ∉ otherBad p root := by
  classical
  simp [goodDual]

theorem not_otherBad_decomp {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∉ otherBad p root) :
    (IsDual p root k ∧ k ∈ goodDual p root) ∨ IsPureAND1 p root k ∨ IsPureOR0 p root k := by
  rcases four_way_of_not_badFlip h0 h1 (not_badFlip_of_not_otherBad hk) with hD | hD | hP | hP
  · exact Or.inl ⟨Or.inl hD, goodDual_iff.mpr ⟨Or.inl hD, hk⟩⟩
  · exact Or.inl ⟨Or.inr hD, goodDual_iff.mpr ⟨Or.inr hD, hk⟩⟩
  · exact Or.inr (Or.inl hP)
  · exact Or.inr (Or.inr hP)

theorem goodDual_sideChild_val {p : Program signature n g} {root : Wire n g}
    (h0 : cornerValue p false root = true) (h1 : cornerValue p true root = true)
    {k : Fin g} (hk : k ∈ goodDual p root) :
    (IsDualOR p root k → cornerValue p false (sideChild p k) = false ∧
        cornerValue p true (sideChild p k) = true) ∧
      (IsDualAND p root k → cornerValue p false (sideChild p k) = false ∧
        cornerValue p true (sideChild p k) = true) := by
  classical
  obtain ⟨_, hno⟩ := goodDual_iff.mp hk
  have hnbF := not_badFlip_of_not_otherBad hno
  have hnb := (not_s0_s1_of_not_badFlip hnbF).1
  refine ⟨fun hOR => ?_, fun hAND => ?_⟩
  · have hF := (dualOR_children h0 h1 hnb hOR).2.2.2.2.2.2.2.2.2.2
    have hT : cornerValue p true (sideChild p k) = true := by
      by_contra hNot
      exact hno (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOR, hnbF, Bool.eq_false_iff.mpr hNot⟩)))
    exact ⟨hF, hT⟩
  · have hT := (dualAND_children h0 h1 hnb hAND).2.2.2.2.2.2.2.2.2.2
    have hF : cornerValue p false (sideChild p k) = false := by
      by_contra hNot
      exact hno (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAND, hnbF, Bool.eq_true_of_not_eq_false hNot⟩))
    exact ⟨hF, hT⟩

#print axioms needInputs_add_slack_eq
#print axioms sum_card_inter_req_le
#print axioms card_otherBad_le_slack

end PvsNP.Frontier.TwoCornerStructure
