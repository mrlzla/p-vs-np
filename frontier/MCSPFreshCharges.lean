module

public import MCSPNestedFaces

/-! Charge original gates that become constants or aliases for the first time. -/

@[expose] public section

namespace PvsNP.Frontier.FreshCharges

open Cslib Cslib.Circuits Cslib.Circuits.Boolean RestrictionCharges

variable {n k l g : ℕ}

def projection (i : Fin k) : BooleanFunction k := fun x => x i

def disclosed (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) (j : Fin g) : Prop :=
  let f := restrictedWire p ρ (.gate j)
  (∃ b : Bool, f = fun _ => b) ∨ (∃ i : Fin k, f = projection i) ∨
    ∃ t : Fin g, t < j ∧ f = restrictedWire p ρ (.gate t)

noncomputable def fresh (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter (fun j => ¬ disclosed p ρ j)

theorem restrictedWire_compose (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (w : Wire n g) :
    restrictedWire p (compose ρ τ) w = fun x => restrictedWire p ρ w (substitute τ x) := by
  funext x
  simp only [restrictedWire, substitute_compose]

private theorem disclosed_nested (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (j : Fin g) (h : disclosed p ρ j) :
    disclosed p (compose ρ τ) j := by
  unfold disclosed
  rw [restrictedWire_compose]
  rcases h with ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, ht, he⟩
  · exact Or.inl ⟨b, by rw [hb]⟩
  · rw [hi]
    cases hτ : τ i with
    | inl a => exact Or.inr (Or.inl ⟨a, funext fun x => substitute_inl hτ⟩)
    | inr b => exact Or.inl ⟨b, funext fun x => substitute_inr hτ⟩
  · exact Or.inr (Or.inr ⟨t, ht, by rw [restrictedWire_compose, he]⟩)

theorem fresh_nested (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) : fresh p (compose ρ τ) ⊆ fresh p ρ := by
  classical
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hd =>
    (Finset.mem_filter.mp hj).2 (disclosed_nested p ρ τ j hd)⟩

noncomputable def firstFreshLoss (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) :
    Finset (Fin g) := Finset.univ \ fresh p ρ

noncomputable def nextFreshLoss (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) : Finset (Fin g) :=
  fresh p ρ \ fresh p (compose ρ τ)

theorem fresh_losses_disjoint (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) : Disjoint (firstFreshLoss p ρ) (nextFreshLoss p ρ τ) := by
  apply Finset.disjoint_left.mpr
  intro j hj hd
  exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_sdiff.mp hd).1

private theorem essential_projection_eq {i j : Fin k} (he : EssentialAt (projection j) i) : j = i := by
  obtain ⟨x, y, hx, hn⟩ := he
  by_contra hne
  exact hn (hx j hne)

private theorem input_is_projection (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (a : Fin n) (i : Fin k) (h : EssentialAt (restrictedWire p ρ (.input a)) i) :
    restrictedWire p ρ (.input a) = projection i := by
  cases hρ : ρ a with
  | inl j =>
    have he : restrictedWire p ρ (.input a) = projection j := funext fun x => substitute_inl hρ
    rw [he] at h
    rw [he, essential_projection_eq h]
  | inr b =>
    obtain ⟨x, y, _, hne⟩ := h
    exact (hne ((substitute_inr hρ).trans (substitute_inr hρ).symm)).elim

private theorem essential_argument (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (j : Fin g) (i : Fin k) (he : EssentialAt (restrictedWire p ρ (.gate j)) i) :
    ∃ a : Fin (signature.Arity (p.lines j).op),
      EssentialAt (restrictedWire p ρ ((p.lines j).wires a)) i := by
  classical
  obtain ⟨x, y, hx, hn⟩ := he
  by_contra! h
  apply hn
  unfold restrictedWire
  rw [p.trace_gate, p.trace_gate]
  congr 1
  funext a
  by_contra hne
  exact h a ⟨x, y, hx, hne⟩

/-- Follow an essential variable past its aliases to the first gate that
changes its signal. That gate is fresh and reads a wire equal to the projection. -/
theorem first_projection_reader (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) (i : Fin k)
    (he : EssentialAt (restrictedWire p ρ root) i)
    (hRoot : restrictedWire p ρ root ≠ projection i) :
    ∃ j ∈ fresh p ρ, ∃ a : Fin (signature.Arity (p.lines j).op),
      restrictedWire p ρ ((p.lines j).wires a) = projection i := by
  classical
  let candidates := (Finset.univ : Finset (Fin g)).filter fun j =>
    EssentialAt (restrictedWire p ρ (.gate j)) i ∧ restrictedWire p ρ (.gate j) ≠ projection i
  have hn : candidates.Nonempty := by
    cases root with
    | input j => exact (hRoot (input_is_projection p ρ j i he)).elim
    | gate j => exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hRoot⟩⟩
  let j := candidates.min' hn
  obtain ⟨hjE, hjP⟩ := (Finset.mem_filter.mp (Finset.min'_mem candidates hn)).2
  have min (t : Fin g) (ht : t < j) (hEss : EssentialAt (restrictedWire p ρ (.gate t)) i) :
      restrictedWire p ρ (.gate t) = projection i := by
    by_contra hne
    have hm : t ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEss, hne⟩
    exact (not_lt_of_ge (Finset.min'_le candidates t hm)) ht
  have hfresh : j ∈ fresh p ρ := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro (⟨b, hb⟩ | ⟨a, ha⟩ | ⟨t, ht, hEq⟩)
    · rw [hb] at hjE
      obtain ⟨_, _, _, hne⟩ := hjE
      exact hne rfl
    · rw [ha] at hjE
      exact hjP (ha.trans (congrArg projection (essential_projection_eq hjE)))
    · exact hjP (hEq.trans (min t ht (hEq ▸ hjE)))
  obtain ⟨a, ha⟩ := essential_argument p ρ j i hjE
  refine ⟨j, hfresh, a, ?_⟩
  cases h : (p.lines j).wires a with
  | input t => exact input_is_projection p ρ t i (h ▸ ha)
  | gate t =>
    exact min t (p.lt_of_lines_wires_eq_gate j a t h) (h ▸ ha)

private theorem constant_arg {op : Op} (args : Fin (signature.Arity op) → BooleanFunction l)
    (i : Fin (signature.Arity op)) (b : Bool) (hb : args i = fun _ => b) :
    (∃ v : Bool, (fun x => interpretation op (fun a => args a x)) = fun _ => v) ∨
      ∃ a, (fun x => interpretation op (fun z => args z x)) = args a := by
  cases op with
  | const v => exact i.elim0
  | not =>
    have hi : i = 0 := Subsingleton.elim ..
    subst i
    exact Or.inl ⟨!b, by simp [interpretation, hb]⟩
  | and =>
    have hval : i.val = 0 ∨ i.val = 1 := by
      have hi := i.isLt
      change i.val < 2 at hi
      omega
    have hs : i = 0 ∨ i = 1 := hval.imp Fin.ext Fin.ext
    rcases hs with rfl | rfl <;> cases b
    · exact Or.inl ⟨false, by simp [interpretation, hb]⟩
    · exact Or.inr ⟨1, by simp [interpretation, hb]⟩
    · exact Or.inl ⟨false, by simp [interpretation, hb]⟩
    · exact Or.inr ⟨0, by simp [interpretation, hb]⟩
  | or =>
    have hval : i.val = 0 ∨ i.val = 1 := by
      have hi := i.isLt
      change i.val < 2 at hi
      omega
    have hs : i = 0 ∨ i = 1 := hval.imp Fin.ext Fin.ext
    rcases hs with rfl | rfl <;> cases b
    · exact Or.inr ⟨1, by simp [interpretation, hb]⟩
    · exact Or.inl ⟨true, by simp [interpretation, hb]⟩
    · exact Or.inr ⟨0, by simp [interpretation, hb]⟩
    · exact Or.inl ⟨true, by simp [interpretation, hb]⟩

/-- A constant argument makes a De Morgan gate constant or equal to a
wire already available to that gate. -/
theorem disclosed_of_constant_argument (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (j : Fin g) (a : Fin (signature.Arity (p.lines j).op))
    (b : Bool) (harg : restrictedWire p ρ ((p.lines j).wires a) = fun _ => b) :
    disclosed p ρ j := by
  have heval : restrictedWire p (ρ) (.gate j) =
      fun x => interpretation (p.lines j).op (fun t => restrictedWire p (ρ) ((p.lines j).wires t) x) :=
    funext fun _ => p.trace_gate _ _ j
  rcases constant_arg (fun t => restrictedWire p (ρ) ((p.lines j).wires t)) a b harg with
    ⟨v, hv⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨v, heval.trans hv⟩
  · have hAlias := heval.trans ht
    cases hs : (p.lines j).wires t with
    | gate u =>
      exact Or.inr (Or.inr ⟨u, p.lt_of_lines_wires_eq_gate j t u hs, hs ▸ hAlias⟩)
    | input u =>
      rw [hs] at hAlias
      cases hρ : ρ u with
      | inl v => exact Or.inr (Or.inl ⟨v, hAlias.trans (funext fun x => substitute_inl hρ)⟩)
      | inr v => exact Or.inl ⟨v, hAlias.trans (funext fun x => substitute_inr hρ)⟩

theorem disclosed_of_pinned_projection (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (j : Fin g) (a : Fin (signature.Arity (p.lines j).op))
    (i : Fin k) (b : Bool) (h : restrictedWire p ρ ((p.lines j).wires a) = projection i)
    (hpin : τ i = .inr b) : disclosed p (compose ρ τ) j := by
  have harg : restrictedWire p (compose ρ τ) ((p.lines j).wires a) = fun _ => b := by
    rw [restrictedWire_compose, h]
    exact funext fun x => substitute_inr hpin
  exact disclosed_of_constant_argument p (compose ρ τ) j a b harg

/-- Each pinned essential coordinate charges a surviving gate unique to this
stage, with at most two coordinates sharing the same gate. -/
theorem twice_nextFreshLoss_ge (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (root : Wire n g) (S : Finset (Fin k))
    (hEss : ∀ i ∈ S, EssentialAt (restrictedWire p ρ root) i)
    (hRoot : ∀ i ∈ S, restrictedWire p ρ root ≠ projection i)
    (hPin : ∀ i ∈ S, ∃ b : Bool, τ i = .inr b) :
    S.card ≤ 2 * (nextFreshLoss p ρ τ).card := by
  classical
  let lost := nextFreshLoss p ρ τ
  let pins := lost.sigma (fun j => (Finset.univ : Finset (Fin (signature.Arity (p.lines j).op))))
  have record (i : S) : ∃ a ∈ pins, restrictedWire p ρ ((p.lines a.1).wires a.2) = projection i.val := by
    obtain ⟨j, hj, a, ha⟩ := first_projection_reader p ρ root i.val (hEss _ i.property) (hRoot _ i.property)
    obtain ⟨b, hb⟩ := hPin _ i.property
    have hd := disclosed_of_pinned_projection p ρ τ j a i.val b ha hb
    have hjl : j ∈ lost := Finset.mem_sdiff.mpr ⟨hj, fun h => (Finset.mem_filter.mp h).2 hd⟩
    exact ⟨⟨j, a⟩, Finset.mem_sigma.mpr ⟨hjl, Finset.mem_univ _⟩, ha⟩
  let into (i : S) : pins := ⟨(record i).choose, (record i).choose_spec.1⟩
  have hi : Function.Injective into := by
    intro i j h
    apply Subtype.ext
    have he : projection i.val = projection j.val := by
      have hArg := congrArg (fun a : pins => restrictedWire p ρ ((p.lines a.val.1).wires a.val.2)) h
      exact ((record i).choose_spec.2).symm.trans (hArg.trans (record j).choose_spec.2)
    have hh := congrFun he (fun t => decide (t = i.val))
    simpa [projection, eq_comm] using hh
  have hcount : S.card ≤ pins.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective into hi
  refine hcount.trans ?_
  rw [Finset.card_sigma]
  calc
    _ ≤ ∑ _j ∈ lost, (2 : ℕ) := Finset.sum_le_sum fun j _ => by
      simpa using (Program.fanInAtMost_iff.mp p.fanInAtMost_two j)
    _ = _ := by simp [Nat.mul_comm, lost]

private def supplied (k : ℕ) : Set (BooleanFunction k) :=
  inputs k ∪ {(fun _ => false), (fun _ => true)}

private theorem supplied_constant (b : Bool) : (fun _ : BitString k => b) ∈ supplied k := by
  cases b <;> simp [supplied]

private def earlier (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) (d : ℕ) :
    Set (BooleanFunction k) :=
  {f | ∃ j : Fin g, j.val < d ∧ f = restrictedWire p ρ (.gate j)}

private theorem earlier_step (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) (j : Fin g) :
    earlier p ρ (j.val + 1) = earlier p ρ j.val ∪ {restrictedWire p ρ (.gate j)} := by
  ext f
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h : i.val < j.val
    · exact Or.inl ⟨i, h, rfl⟩
    · have he : i = j := Fin.ext (by omega)
      subst i
      exact Or.inr rfl
  · rintro (⟨i, hi, rfl⟩ | hf)
    · exact ⟨i, by omega, rfl⟩
    · exact ⟨j, by omega, hf⟩

private noncomputable def keptBefore (kept : Finset (Fin g))
    (d : ℕ) : Finset (Fin g) :=
  kept.filter (fun j => j.val < d)

private theorem keptBefore_step (kept : Finset (Fin g))
    (j : Fin g) :
    (keptBefore kept (j.val + 1)).card = (keptBefore kept j.val).card + (if j ∈ kept then 1 else 0) := by
  classical
  have hd : j ∉ keptBefore kept j.val := fun hj => (Nat.lt_irrefl _) (Finset.mem_filter.mp hj).2
  by_cases hj : j ∈ kept
  · have he : keptBefore kept (j.val + 1) = insert j (keptBefore kept j.val) := by
      ext i
      simp only [keptBefore, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hlt⟩
        by_cases h : i.val < j.val
        · exact Or.inr ⟨hi, h⟩
        · exact Or.inl (Fin.ext (by omega))
      · rintro (rfl | ⟨hi, hlt⟩)
        · exact ⟨hj, by omega⟩
        · exact ⟨hi, by omega⟩
    rw [he, Finset.card_insert_of_notMem hd, ite_eq_left hj]
  · have he : keptBefore kept (j.val + 1) = keptBefore kept j.val := by
      ext i
      simp only [keptBefore, Finset.mem_filter]
      constructor
      · rintro ⟨hi, hlt⟩
        refine ⟨hi, ?_⟩
        by_contra h
        have he : i = j := Fin.ext (by omega)
        exact hj (he ▸ hi)
      · rintro ⟨hi, hlt⟩
        exact ⟨hi, by omega⟩
    rw [he, ite_eq_right hj, Nat.add_zero]

private theorem supplied_input (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (i : Fin n) : restrictedWire p ρ (.input i) ∈ supplied k := by
  cases hr : ρ i with
  | inl j =>
    exact Set.mem_union_left _ ⟨j, funext fun x => (substitute_inl (x := x) hr).symm⟩
  | inr b =>
    have h : restrictedWire p ρ (.input i) = fun _ => b := funext fun x => substitute_inr (x := x) hr
    rw [h]
    exact supplied_constant b

/-- Rebuild the program in topological order, omitting lines that already
have a witness among the supplied functions or earlier lines. -/
private theorem synth_kept_prefix (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (s : Set (BooleanFunction k)) (kept : Finset (Fin g))
    (hInput : ∀ i, restrictedWire p ρ (.input i) ∈ s)
    (hSkip : ∀ j ∉ kept, restrictedWire p ρ (.gate j) ∈ s ∪ earlier p ρ j.val) :
    ∀ d ≤ g, Synthesis interpretation s (earlier p ρ d) (keptBefore kept d).card := by
  classical
  intro d
  induction d with
  | zero =>
    intro _
    apply (Synthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _)
    rintro f ⟨j, hj, _⟩
    omega
  | succ d ih =>
    intro hd
    let j : Fin g := ⟨d, by omega⟩
    let last := restrictedWire p ρ (.gate j)
    have hJ : Synthesis interpretation (s ∪ earlier p ρ d) {last}
        (if j ∈ kept then 1 else 0) := by
      by_cases hj : j ∈ kept
      · rw [ite_eq_left hj]
        have he : last = fun x => interpretation (p.lines j).op
            (fun a => restrictedWire p ρ ((p.lines j).wires a) x) := funext fun _ => p.trace_gate _ _ j
        rw [he]
        apply Synthesis.gate
        intro a
        cases h : (p.lines j).wires a with
        | input i => exact Set.mem_union_left _ (h.symm ▸ hInput i)
        | gate t => exact Set.mem_union_right _ ⟨t, p.lt_of_lines_wires_eq_gate j a t h, rfl⟩
      · rw [ite_eq_right hj]
        exact Synthesis.of_mem (hSkip j hj)
    have hPrev := ih (by omega)
    have h := hPrev.comp hJ
    have ht := earlier_step p ρ j
    have hh := keptBefore_step kept j
    change earlier p ρ (d + 1) = earlier p ρ d ∪ {last} at ht
    change (keptBefore kept (d + 1)).card = (keptBefore kept d).card + _ at hh
    rw [ht, hh]
    exact h

private theorem synth_kept_output (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) (s : Set (BooleanFunction k)) (kept : Finset (Fin g))
    (hInput : ∀ i, restrictedWire p ρ (.input i) ∈ s)
    (hSkip : ∀ j ∉ kept, restrictedWire p ρ (.gate j) ∈ s ∪ earlier p ρ j.val) :
    Synthesis interpretation s {restrictedWire p ρ root} kept.card := by
  have h := (synth_kept_prefix p ρ s kept hInput hSkip g le_rfl).comp
    (Synthesis.of_subset (t := {restrictedWire p ρ root}) (by
      apply Set.singleton_subset_iff.mpr 
      cases root with
      | input i => exact Set.mem_union_left _ (hInput i)
      | gate j => exact Set.mem_union_right _ ⟨j, j.isLt, rfl⟩))
  have hfull : keptBefore kept g = kept := by
    ext j
    simp [keptBefore]
  simpa only [hfull, Nat.add_zero] using (h.mono Set.Subset.rfl Set.subset_union_right le_rfl)

/-- An input projection or an earlier duplicate can be omitted from the
original program without supplying any extra constants. -/
theorem original_alias_complexity_le (p : Program signature n g) (root : Wire n g)
    (j : Fin g)
    (hAlias :
      (∃ i : Fin n, restrictedWire p Sum.inl (.gate j) = projection i) ∨
      ∃ t : Fin g, t < j ∧ restrictedWire p Sum.inl (.gate j) = restrictedWire p Sum.inl (.gate t)) :
    complexity interpretation (single (restrictedWire p Sum.inl root)) ≤ g - 1 := by
  classical
  let kept := (Finset.univ : Finset (Fin g)).erase j
  have hInput (i : Fin n) : restrictedWire p Sum.inl (.input i) ∈ inputs n :=
    ⟨i, rfl⟩
  have hSkip (t : Fin g) (ht : t ∉ kept) :
      restrictedWire p Sum.inl (.gate t) ∈ inputs n ∪ earlier p Sum.inl t.val := by
    have hEq : t = j := by simpa [kept] using ht
    subst t
    rcases hAlias with ⟨i, hi⟩ | ⟨u, hu, he⟩
    · exact Or.inl ⟨i, hi.symm⟩
    · exact Or.inr ⟨u, hu, he⟩
  have h := (synth_kept_output p Sum.inl root (inputs n) kept hInput hSkip).complexity_le
  simpa [kept, Finset.card_erase_of_mem] using h

theorem fresh_complexity_le (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) :
    complexity interpretation (single (restrictedWire p ρ root)) ≤ (fresh p ρ).card + 2 := by
  have constants : Synthesis interpretation (inputs k) {(fun _ => false), (fun _ => true)} 2 := by
    have hfalse : Synthesis interpretation (inputs k) {fun _ => false} 1 := Synthesis.const false
    have htrue : Synthesis interpretation (inputs k) {fun _ => true} 1 := Synthesis.const true
    simpa only [Set.singleton_union, Nat.one_add, Nat.reduceAdd] using hfalse.union htrue
  have hSkip (j : Fin g) (hj : j ∉ fresh p ρ) :
      restrictedWire p ρ (.gate j) ∈ supplied k ∪ earlier p ρ j.val := by
    classical
    have h : disclosed p ρ j := by
      by_contra hn
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    rcases h with ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, ht, he⟩
    · exact Or.inl (hb.symm ▸ supplied_constant b)
    · exact Or.inl (Or.inl ⟨i, hi.symm⟩)
    · exact Or.inr ⟨t, ht, he⟩
  have h := synth_kept_output p ρ root (supplied k) (fresh p ρ) (supplied_input p ρ) hSkip
  have h' := (constants.trans h).complexity_le
  simpa only [Nat.add_zero, Nat.zero_add, Nat.add_comm] using h'

/-- The fresh representative of a restricted signal, when it has one. -/
def Represents (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (w : Wire n g) (j : Fin g) : Prop :=
  j ∈ fresh p ρ ∧ restrictedWire p ρ (.gate j) = restrictedWire p ρ w

theorem represents_unique (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    {w : Wire n g} {i j : Fin g} (hi : Represents p ρ w i) (hj : Represents p ρ w j) :
    i = j := by
  classical
  rcases lt_trichotomy i j with h | h | h
  · exact ((Finset.mem_filter.mp hj.1).2 (Or.inr (Or.inr ⟨i, h, hj.2.trans hi.2.symm⟩))).elim
  · exact h
  · exact ((Finset.mem_filter.mp hi.1).2 (Or.inr (Or.inr ⟨j, h, hi.2.trans hj.2.symm⟩))).elim

private theorem exists_gate_representative (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (j : Fin g)
    (hNon : ¬∃ b : Bool, restrictedWire p ρ (.gate j) = fun _ => b)
    (hNoProj : ¬∃ i : Fin k, restrictedWire p ρ (.gate j) = projection i) :
    ∃ i : Fin g, i ≤ j ∧ Represents p ρ (.gate j) i := by
  classical
  let S := (Finset.univ : Finset (Fin g)).filter (fun i =>
    restrictedWire p ρ (.gate i) = restrictedWire p ρ (.gate j))
  have hj : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hn : S.Nonempty := ⟨j, hj⟩
  let i := S.min' hn
  have he := (Finset.mem_filter.mp (Finset.min'_mem S hn)).2
  refine ⟨i, Finset.min'_le S j hj, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
  rintro (⟨b, hb⟩ | ⟨a, ha⟩ | ⟨t, ht, hf⟩)
  · exact hNon ⟨b, he.symm.trans hb⟩
  · exact hNoProj ⟨a, he.symm.trans ha⟩
  · have hm : t ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.symm.trans he⟩
    exact (not_lt_of_ge (Finset.min'_le S t hm)) ht

/-- The backwards cone after replacing each alias by its fresh
representative or by an input projection. -/
inductive ResidualLive (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) : Fin g → Prop where
  | output {j : Fin g} : Represents p ρ root j → ResidualLive p ρ root j
  | argument {j t : Fin g} (h : ResidualLive p ρ root j)
      (a : Fin (signature.Arity (p.lines j).op)) :
      Represents p ρ ((p.lines j).wires a) t → ResidualLive p ρ root t

theorem residualLive_mem_fresh {p : Program signature n g} {ρ : Fin n → Fin k ⊕ Bool}
    {root : Wire n g} {j : Fin g} (h : ResidualLive p ρ root j) : j ∈ fresh p ρ := by
  cases h with
  | output h => exact h.1
  | argument _ _ h => exact h.1

noncomputable def liveFresh (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) : Finset (Fin g) := open scoped Classical in
  (fresh p ρ).filter (ResidualLive p ρ root)

theorem mem_liveFresh_iff {p : Program signature n g} {ρ : Fin n → Fin k ⊕ Bool}
    {root : Wire n g} {j : Fin g} : j ∈ liveFresh p ρ root ↔ ResidualLive p ρ root j := by
  classical
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨residualLive_mem_fresh h, h⟩⟩

noncomputable def deadFresh (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) : Finset (Fin g) :=
  fresh p ρ \ liveFresh p ρ root

theorem firstFreshLoss_disjoint_deadFresh (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g) :
    Disjoint (firstFreshLoss p ρ) (deadFresh p ρ root) := by
  apply Finset.disjoint_left.mpr
  intro j h hd
  exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mp hd).1

theorem liveFresh_empty_of_projection (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g) {i : Fin k}
    (h : restrictedWire p ρ root = projection i) :
    liveFresh p ρ root = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hj' := mem_liveFresh_iff.mp hj
  clear hj
  induction hj' with
  | output hRep =>
    exact (Finset.mem_filter.mp hRep.1).2 (Or.inr (Or.inl ⟨i, hRep.2.trans h⟩))
  | argument _ _ _ ih => exact ih

private def liveEarlier (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) (d : ℕ) : Set (BooleanFunction k) :=
  { f | ∃ j ∈ liveFresh p ρ root, j.val < d ∧ f = restrictedWire p ρ (.gate j) }

private theorem synth_live_fresh_prefix (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g) :
    ∀ d ≤ g, Synthesis interpretation (inputs k) (liveEarlier p ρ root d)
      (keptBefore (liveFresh p ρ root) d).card := by
  classical
  intro d
  induction d with
  | zero =>
    intro _
    apply (Synthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _)
    rintro f ⟨j, _, hj, _⟩
    omega
  | succ d ih =>
    intro hd
    let j : Fin g := ⟨d, by omega⟩
    have hjVal : j.val = d := rfl
    let S := liveFresh p ρ root
    let last := restrictedWire p ρ (.gate j)
    have hCount := keptBefore_step S j
    change (keptBefore S (d + 1)).card = (keptBefore S d).card + _ at hCount
    have hPrev := ih (by omega)
    by_cases hj : j ∈ S
    · have hStep : liveEarlier p ρ root (d + 1) = liveEarlier p ρ root d ∪ {last} := by
        ext f
        constructor
        · rintro ⟨t, htS, ht, hEq⟩
          by_cases hd : t.val < d
          · exact Or.inl ⟨t, htS, hd, hEq⟩
          · have he : t = j := Fin.ext (by rw [hjVal]; omega)
            exact Or.inr (hEq.trans (congrArg (fun a => restrictedWire p ρ (.gate a)) he))
        · rintro (⟨t, htS, ht, he⟩ | rfl)
          · exact ⟨t, htS, by omega, he⟩
          · exact ⟨j, hj, by rw [hjVal]; omega, rfl⟩
      have hGate : Synthesis interpretation (inputs k ∪ liveEarlier p ρ root d) {last} 1 := by
        have hEval : last = fun x => interpretation (p.lines j).op
            (fun a => restrictedWire p ρ ((p.lines j).wires a) x) :=
          funext fun _ => p.trace_gate _ _ j
        rw [hEval]
        apply Synthesis.gate
        intro a
        let w := (p.lines j).wires a
        have hLive : ResidualLive p ρ root j := mem_liveFresh_iff.mp hj
        have hNon : ¬∃ b : Bool, restrictedWire p ρ w = fun _ => b := by
          rintro ⟨b, hb⟩
          exact (Finset.mem_filter.mp (residualLive_mem_fresh hLive)).2
            (disclosed_of_constant_argument p ρ j a b hb)
        by_cases hProj : ∃ i, restrictedWire p ρ w = projection i
        · obtain ⟨i, hi⟩ := hProj
          exact Or.inl ⟨i, hi.symm⟩
        · cases hw : w with
          | input i =>
            cases hi : ρ i with
            | inl t =>
              have h : restrictedWire p ρ (.input i) = projection t :=
                funext fun _ => substitute_inl hi
              exact (hProj ⟨t, hw.symm ▸ h⟩).elim
            | inr b =>
              have h : restrictedWire p ρ (.input i) = fun _ => b :=
                funext fun _ => substitute_inr hi
              exact (hNon ⟨b, hw.symm ▸ h⟩).elim
          | gate t =>
            rw [hw] at hNon hProj
            obtain ⟨u, hu, hRep⟩ := exists_gate_representative p ρ t hNon hProj
            have hr : Represents p ρ w u := hw.symm ▸ hRep
            have hJ := p.lt_of_lines_wires_eq_gate j a t hw
            exact Or.inr ⟨u, mem_liveFresh_iff.mpr (ResidualLive.argument hLive a hr),
              lt_of_le_of_lt hu hJ, hr.2.symm⟩
      rw [hStep, hCount, ite_eq_left hj]
      exact hPrev.comp hGate
    · have hStep : liveEarlier p ρ root (d + 1) = liveEarlier p ρ root d := by
        ext f
        constructor
        · rintro ⟨t, htS, ht, he⟩
          refine ⟨t, htS, ?_, he⟩
          by_contra h
          have heq : t = j := Fin.ext (by rw [hjVal]; omega)
          exact hj (heq ▸ htS)
        · rintro ⟨t, htS, ht, he⟩
          exact ⟨t, htS, by omega, he⟩
      rw [hStep, hCount, ite_eq_right hj, Nat.add_zero]
      exact hPrev

/-- Rebuild the residual using only the live original fresh indices, with
no additional constants when its output is nonconstant. -/
theorem live_fresh_complexity_le (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) (hNon : ¬∃ b : Bool, restrictedWire p ρ root = fun _ => b) :
    complexity interpretation (single (restrictedWire p ρ root)) ≤ (liveFresh p ρ root).card := by
  have hOut : restrictedWire p ρ root ∈ inputs k ∪ liveEarlier p ρ root g := by
    by_cases hP : ∃ i, restrictedWire p ρ root = projection i
    · obtain ⟨i, hi⟩ := hP
      exact Or.inl ⟨i, hi.symm⟩
    cases root with
    | input i =>
      cases hi : ρ i with
      | inl t => exact (hP ⟨t, funext fun _ => substitute_inl hi⟩).elim
      | inr b => exact (hNon ⟨b, funext fun _ => substitute_inr hi⟩).elim
    | gate j =>
      obtain ⟨t, _, hRep⟩ := exists_gate_representative p ρ j hNon hP
      exact Or.inr ⟨t, mem_liveFresh_iff.mpr (ResidualLive.output hRep), t.isLt, hRep.2.symm⟩
  have h := (synth_live_fresh_prefix p ρ root g le_rfl).comp (Synthesis.of_mem hOut)
  have hFull : keptBefore (liveFresh p ρ root) g = liveFresh p ρ root := by
    ext j
    simp [keptBefore]
  have hc := (h.mono Set.Subset.rfl Set.subset_union_right le_rfl).complexity_le
  simpa only [hFull, Nat.add_zero] using hc

theorem liveFresh_subset_fresh (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (root : Wire n g) : liveFresh p ρ root ⊆ fresh p ρ := by
  classical
  exact Finset.filter_subset _ _

/-- The fresh-index reconstruction has no constant overhead when its
output is nonconstant. -/
theorem fresh_complexity_le_of_nonconstant (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g)
    (hNon : ¬ ∃ b : Bool, restrictedWire p ρ root = fun _ => b) :
    complexity interpretation (single (restrictedWire p ρ root)) ≤ (fresh p ρ).card :=
  (live_fresh_complexity_le p ρ root hNon).trans
    (Finset.card_le_card (liveFresh_subset_fresh p ρ root))

/-- Omitted gates, fresh but dead gates, and the residual gate budget are
disjoint parts of the original gate count. -/
theorem first_dead_and_residual_budget (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (root : Wire n g)
    (hNon : ¬∃ b : Bool, restrictedWire p ρ root = fun _ => b) :
    complexity interpretation (single (restrictedWire p ρ root)) +
      (firstFreshLoss p ρ).card + (deadFresh p ρ root).card ≤ g := by
  classical
  have h := live_fresh_complexity_le p ρ root hNon
  have hA := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (fresh p ρ))
  simp only [Finset.card_univ, Fintype.card_fin] at hA
  change (firstFreshLoss p ρ).card + (fresh p ρ).card = g at hA
  have hB := Finset.card_sdiff_add_card_eq_card (liveFresh_subset_fresh p ρ root)
  change (deadFresh p ρ root).card + (liveFresh p ρ root).card = (fresh p ρ).card at hB
  omega

#print axioms original_alias_complexity_le
#print axioms fresh_losses_disjoint
#print axioms twice_nextFreshLoss_ge
#print axioms fresh_complexity_le
#print axioms fresh_complexity_le_of_nonconstant
#print axioms live_fresh_complexity_le
#print axioms first_dead_and_residual_budget

end PvsNP.Frontier.FreshCharges
