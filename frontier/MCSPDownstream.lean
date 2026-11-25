module

public import MCSPSplitControl
public import Mathlib.Combinatorics.Hall.Finite

/-! Downstream connections and distinct crossing wires for the split-pair cuts. -/

@[expose] public section

namespace PvsNP.Frontier.Downstream

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut

variable {n g r s : ℕ}

/-- An edge stays unless its source wire is in the proposed crossing set. A single
deleted source removes all its outgoing edges, including across multiple readers. -/
def RemainingEdge (p : Program signature n g) (S : Finset (Wire n g))
    (u v : Wire n g) : Prop :=
  u ∉ S ∧ ∃ (k : Fin g) (a : Fin (signature.Arity (p.lines k).op)),
    (p.lines k).wires a = u ∧ v = .gate k

abbrev Connected (p : Program signature n g) (S : Finset (Wire n g)) :=
  Relation.EqvGen (RemainingEdge p S)

private theorem owner_eq_of_connected (p : Program signature n g) (S : Finset (Wire n g))
    (owner : Wire n g → Bool) (hcut : crossingWires p owner ⊆ S)
    {u v : Wire n g} (h : Connected p S u v) : owner u = owner v := by
  classical
  induction h with
  | rel u v h =>
    obtain ⟨hn, k, a, he, rfl⟩ := h
    by_contra hne
    exact hn (hcut (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, a, he, hne⟩))
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A crossing set is feasible exactly when the remaining wiring connects no
input on the false side to an input on the true side. -/
theorem exists_placement_iff (p : Program signature n g) (selector : BitString n)
    (S : Finset (Wire n g)) :
    (∃ owner : Wire n g → Bool, (∀ i, owner (.input i) = selector i) ∧ crossingWires p owner ⊆ S) ↔
      ¬ ∃ i j : Fin n, selector i = false ∧ selector j = true ∧
        Connected p S (.input i) (.input j) := by
  classical
  constructor
  · rintro ⟨owner, howner, hcut⟩ ⟨i, j, hi, hj, hconnected⟩
    have h := owner_eq_of_connected p S owner hcut hconnected
    rw [howner, howner, hi, hj] at h
    cases h
  · intro hsep
    let right (v : Wire n g) := ∃ j : Fin n, selector j = true ∧ Connected p S (.input j) v
    let owner (v : Wire n g) : Bool := decide (right v)
    have howner (i : Fin n) : owner (.input i) = selector i := by
      cases hi : selector i with
      | false =>
        apply decide_eq_false
        rintro ⟨j, hj, hp⟩
        exact hsep ⟨i, j, hi, hj, .symm _ _ hp⟩
      | true =>
        exact decide_eq_true ⟨i, hi, .refl _⟩
    refine ⟨owner, howner, ?_⟩
    intro u hu
    obtain ⟨k, a, he, hne⟩ := (Finset.mem_filter.mp hu).2
    by_contra hn
    have hpath : Connected p S u (.gate k) := .rel _ _ ⟨hn, k, a, he, rfl⟩
    have hiff : right u ↔ right (.gate k) := by
      constructor
      · rintro ⟨j, hj, hjp⟩
        exact ⟨j, hj, .trans _ _ _ hjp hpath⟩
      · rintro ⟨j, hj, hjp⟩
        exact ⟨j, hj, .trans _ _ _ hjp (.symm _ _ hpath)⟩
    apply hne
    exact Bool.eq_iff_iff.mpr (by simpa only [owner, decide_eq_true_eq] using hiff)

theorem connected_inputs_of_small_crossing_set (p : Program signature n g)
    (selector : BitString n) (S : Finset (Wire n g)) {L : ℕ}
    (hwidth : ∀ owner : Wire n g → Bool, (∀ i, owner (.input i) = selector i) →
      L ≤ (crossingWires p owner).card)
    (hsmall : S.card < L) :
    ∃ i j : Fin n, selector i = false ∧ selector j = true ∧ Connected p S (.input i) (.input j) := by
  classical
  by_contra h
  obtain ⟨owner, howner, hcut⟩ := (exists_placement_iff p selector S).mpr h
  exact (not_le_of_gt hsmall) ((hwidth owner howner).trans (Finset.card_le_card hcut))

/-- A wire's syntactic support is realized by directed paths in the circuit. -/
theorem path_of_mem_support (p : Program signature n g) (i : Fin n)
    (w : Wire n g) (hi : i ∈ p.wireSupport w) :
    Relation.ReflTransGen (RemainingEdge p ∅) (.input i) w := by
  revert hi
  refine p.wire_induction (P := fun w => i ∈ p.wireSupport w →
    Relation.ReflTransGen (RemainingEdge p ∅) (.input i) w) ?_ ?_ w
  · intro j hj
    have h : i = j := by simpa using hj
    subst j
    exact .refl
  · intro k ih hk
    change i ∈ p.trace (supportInterpretation signature n) (fun j => {j}) (.gate k) at hk
    rw [p.trace_gate] at hk
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hk
    exact (ih a ha).tail ⟨Finset.notMem_empty _, k, a, rfl, rfl⟩

section Matching

variable {ι : Type*}

/-- A source wire belongs to a probe coordinate's downstream cone if its
support contains an input carrying that coordinate. -/
noncomputable def sourcesFor (p : Program signature n g) (owner : Wire n g → Bool)
    (label : Fin n → ι) (a : ι) : Finset (Wire n g) := open scoped Classical in
  (crossingWires p owner).filter fun w => ∃ i ∈ p.wireSupport w, label i = a

/-- On an equality restriction, any subset of probe coordinates needs at least
that many distinct crossing source wires in its combined downstream cones. -/
theorem card_probe_coordinates_le (f : BooleanFunction n) (label : Fin n → ι)
    (selector : BitString n) (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (heq : ∀ a b : ι → Bool, f (splice selector (a ∘ label) (b ∘ label)) = true ↔ a = b)
    (owner : Wire n c.size → Bool) (howner : ∀ i, owner (.input i) = selector i)
    (J : Finset ι) : J.card ≤ (J.biUnion (sourcesFor c.program owner label)).card := by
  classical
  let W := J.biUnion (sourcesFor c.program owner label)
  let extend (a : J → Bool) (j : ι) : Bool := if hj : j ∈ J then a ⟨j, hj⟩ else false
  let send (a : J → Bool) (w : W) : Bool :=
    c.program.trace interpretation (extend a ∘ label) w.val
  have hinj : Function.Injective send := by
    intro a b hsend
    have hagree (w : Wire n c.size) (hw : w ∈ crossingWires c.program owner) :
        c.program.trace interpretation (extend a ∘ label) w =
          c.program.trace interpretation (extend b ∘ label) w := by
      by_cases h : w ∈ W
      · exact congrFun hsend ⟨w, h⟩
      · apply c.program.trace_congr interpretation
        intro i hi
        have hout : label i ∉ J := fun hj =>
          h (Finset.mem_biUnion.mpr ⟨label i, hj, Finset.mem_filter.mpr ⟨hw, i, hi, rfl⟩⟩)
        simp [extend, hout]
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

theorem exists_distinct_downstream_sources [Finite ι]
    (f : BooleanFunction n) (label : Fin n → ι) (selector : BitString n)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (heq : ∀ a b : ι → Bool, f (splice selector (a ∘ label) (b ∘ label)) = true ↔ a = b)
    (owner : Wire n c.size → Bool) (howner : ∀ i, owner (.input i) = selector i) :
    ∃ choose : ι → Wire n c.size, Function.Injective choose ∧
      ∀ a, choose a ∈ sourcesFor c.program owner label a := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp
  exact card_probe_coordinates_le f label selector c hc heq owner howner

theorem width_of_distinct_sources [Fintype ι] (p : Program signature n g)
    (owner : Wire n g → Bool) (label : Fin n → ι)
    (choose : ι → Wire n g) (hinj : Function.Injective choose)
    (hw : ∀ a, choose a ∈ sourcesFor p owner label a) :
    Fintype.card ι ≤ (crossingWires p owner).card := by
  classical
  have h := Finset.card_le_card_of_injOn (s := Finset.univ) choose (t := crossingWires p owner)
    (fun a _ => (Finset.mem_filter.mp (hw a)).1) hinj.injOn
  rwa [Finset.card_univ] at h

end Matching

def prefixLabel (r s : ℕ) (i : Fin (2 ^ (r + (s + 1)))) : BitString r :=
  ((positionEquiv r s).symm i).1

theorem probe_eq_pullback (f : BooleanFunction r) : probe s f = f ∘ prefixLabel r s := by
  funext i
  obtain ⟨⟨a, b, t⟩, rfl⟩ := (positionEquiv r s).surjective i
  change probe s f (position a b t) = _
  rw [probe_at_position]
  simp [prefixLabel]

theorem square32_distinct_downstream_sources {h : BooleanFunction 22} (hGood : h ∉ badSelectors 9 22)
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (mcspSquare 32)))
    (owner : Wire (2 ^ 32) c.size → Bool) (howner : ∀ i, owner (.input i) = mask 9 h i) :
    ∃ choose : BitString 9 → Wire (2 ^ 32) c.size, Function.Injective choose ∧
      ∀ a, choose a ∈ sourcesFor c.program owner (prefixLabel 9 22) a := by
  apply exists_distinct_downstream_sources (mcspSquare 32) _ (mask 9 h) c hc _ owner howner
  intro f g
  rw [← probe_eq_pullback, ← probe_eq_pullback]
  exact equality_restriction_of_notMem_badSelectors
    (fun f => probe_is_accepted_shannon (k := 2) (d := 7) f (by decide)) hGood f g

theorem square32_connected_after_small_proposed_cut {h : BooleanFunction 22}
    (hGood : h ∉ badSelectors 9 22) (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (S : Finset (Wire (2 ^ 32) c.size)) (hsmall : S.card < 512) :
    ∃ i j : Fin (2 ^ 32), mask 9 h i = false ∧ mask 9 h j = true ∧
      Connected c.program S (.input i) (.input j) :=
  connected_inputs_of_small_crossing_set c.program (mask 9 h) S
    (mcspSquare_32_crossing_of_good_selector hGood c hc) hsmall

def railLabel (r s : ℕ) (i : Fin (2 ^ (r + (s + 1)))) : BitString r × Bool :=
  let abt := (positionEquiv r s).symm i
  (abt.1, abt.2.1)

@[simp] theorem railLabel_position (a : BitString r) (d : Bool) (t : BitString s) :
    railLabel r s (position a d t) = (a, d) := by
  change railLabel r s (positionEquiv r s (a, d, t)) = (a, d)
  simp [railLabel]

/-- The two rails of each prefix can be assigned independently in the split control. -/
theorem splitControl_equality_by_rail (keep : Finset (BitString s)) (h : BooleanFunction s)
    (hVaries : ∃ u ∈ keep, ∃ v ∈ keep, h u ≠ h v) (f g : BitString r × Bool → Bool) :
    SplitControl.railControl r keep (splice (mask r h) (f ∘ railLabel r s) (g ∘ railLabel r s)) =
      true ↔ f = g := by
  classical
  constructor
  · intro haccept
    obtain ⟨u, hu, v, hv, hne⟩ := hVaries
    funext ad
    obtain ⟨a, d⟩ := ad
    have hBlocks := of_decide_eq_true haccept
    have hAgree := (SampleControls.agreesOn_eq_true _ _).mp (hBlocks (a, d))
      (position a d u) (SplitControl.position_mem_railBlock keep a d hu)
      (position a d v) (SplitControl.position_mem_railBlock keep a d hv)
    simp only [splice, mask_at_position, Function.comp_apply, railLabel_position] at hAgree
    cases hU : h u <;> cases hV : h v
    · exact (hne (hU.trans hV.symm)).elim
    · cases d
      · simpa [hU, hV] using hAgree.symm
      · simpa [hU, hV] using hAgree
    · cases d
      · simpa [hU, hV] using hAgree
      · simpa [hU, hV] using hAgree.symm
    · exact (hne (hU.trans hV.symm)).elim
  · rintro rfl
    rw [splice_self, SplitControl.railControl, decide_eq_true_eq]
    rintro ⟨a, d⟩
    apply (SampleControls.agreesOn_eq_true _ _).mpr
    intro i hi j hj
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hj
    simp

theorem splitControl32_distinct_downstream_sources {h : BooleanFunction 22}
    (hGood : h ∉ badSelectors 9 22) (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (owner : Wire (2 ^ 32) c.size → Bool) (howner : ∀ i, owner (.input i) = mask 9 h i) :
    ∃ choose : BitString 9 × Bool → Wire (2 ^ 32) c.size, Function.Injective choose ∧
      ∀ a, choose a ∈ sourcesFor c.program owner (railLabel 9 22) a :=
  exists_distinct_downstream_sources _ _ (mask 9 h) c hc
    (splitControl_equality_by_rail SplitControl.keep h (SplitControl.good_selector_varies hGood))
    owner howner

theorem splitControl32_crossing_width {h : BooleanFunction 22}
    (hGood : h ∉ badSelectors 9 22) (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (owner : Wire (2 ^ 32) c.size → Bool) (howner : ∀ i, owner (.input i) = mask 9 h i) :
    1024 ≤ (crossingWires c.program owner).card := by
  obtain ⟨choose, hinj, hchoose⟩ := splitControl32_distinct_downstream_sources hGood c hc owner howner
  have hcard := width_of_distinct_sources c.program owner (railLabel 9 22) choose hinj hchoose
  rw [Fintype.card_prod, BitString.card, Fintype.card_bool] at hcard
  exact hcard

theorem splitControl32_connected_after_small_proposed_cut {h : BooleanFunction 22}
    (hGood : h ∉ badSelectors 9 22) (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)))
    (S : Finset (Wire (2 ^ 32) c.size)) (hsmall : S.card < 1024) :
    ∃ i j : Fin (2 ^ 32), mask 9 h i = false ∧ mask 9 h j = true ∧
      Connected c.program S (.input i) (.input j) :=
  connected_inputs_of_small_crossing_set c.program (mask 9 h) S
    (splitControl32_crossing_width hGood c hc) hsmall

/-- The stronger downstream bound holds even for a minimum split-control circuit
inside the earlier near-twice-linear budget. -/
theorem minimum_splitControl32_width_1024 :
    ∃ c : Circuit signature (2 ^ 32) 1,
      c.Computes interpretation (single (SplitControl.railControl 9 SplitControl.keep)) ∧
      c.size = complexity interpretation (single (SplitControl.railControl 9 SplitControl.keep)) ∧
      c.size + 3071 ≤ 2 * 2 ^ 32 ∧
      ∀ (h : BooleanFunction 22) (_ : h ∉ badSelectors 9 22) (owner : Wire (2 ^ 32) c.size → Bool),
        (∀ i, owner (.input i) = mask 9 h i) → 1024 ≤ (crossingWires c.program owner).card := by
  obtain ⟨c, hc, hmin, hsize, _, _⟩ := SplitControl.minimum_wide_railControl_32
  exact ⟨c, hc, hmin, hsize, fun _ hh owner howner => splitControl32_crossing_width hh c hc owner howner⟩

/-- A nonzero wire whose truth suffices for acceptance has a large input cone. -/
theorem certifying_wire_support_lower (p : Program signature n g) (w : Wire n g)
    (f : BooleanFunction n) (x : BitString n) (hx : p.trace interpretation x w = true)
    (hcert : ∀ y, p.trace interpretation y w = true → f y = true)
    (B : ℕ) (hcount : (acceptingTables f).card ≤ 2 ^ B) :
    n ≤ (p.wireSupport w).card + B := by
  classical
  let free := Finset.univ \ p.wireSupport w
  have all (y : BitString n) : f (restrictTable x free y) = true := by
    apply hcert
    rw [p.trace_congr interpretation _ x w]
    · exact hx
    · intro i hi
      simp [restrictTable, free, hi]
  have hempty : essentialPositions (fun y => f (restrictTable x free y)) free = ∅ := by
    ext i
    simp [essentialPositions, EssentialAt, all]
  have h := (pow_card_inessential_le f x free (hcert x hx)).trans hcount
  rw [hempty, Finset.sdiff_empty] at h
  have hfree := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h
  have hSize := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (p.wireSupport w))
  simp only [Finset.card_univ, Fintype.card_fin] at hSize
  change free.card + (p.wireSupport w).card = n at hSize
  omega

theorem certifying_wire_meets_both_sides32 (p : Program signature (2 ^ 32) g)
    (w : Wire (2 ^ 32) g) (f : BooleanFunction (2 ^ 32))
    (x : BitString (2 ^ 32)) (hx : p.trace interpretation x w = true)
    (hcert : ∀ y, p.trace interpretation y w = true → f y = true)
    (hcount : (acceptingTables f).card ≤ 2 ^ descriptionBitBound 32)
    (h : BooleanFunction 22) (side : Bool) :
    ∃ i ∈ p.wireSupport w, mask 9 h i = side := by
  classical
  have hLarge := certifying_wire_support_lower p w f x hx hcert _ hcount
  by_contra! hnone
  have hsub : p.wireSupport w ⊆ Finset.univ.filter (fun i => mask 9 h i = !side) := by
    intro i hi
    have hn := hnone i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    generalize mask 9 h i = b at hn ⊢
    cases side <;> cases b <;> simp_all
  have hsmall := (Finset.card_le_card hsub).trans (card_mask_side (r := 9) (s := 22) h (!side)).le
  have hB : descriptionBitBound 32 = 27672 := by decide
  rw [hB] at hLarge
  norm_num at hLarge hsmall
  omega

#print axioms exists_placement_iff
#print axioms square32_distinct_downstream_sources
#print axioms square32_connected_after_small_proposed_cut
#print axioms splitControl32_connected_after_small_proposed_cut
#print axioms minimum_splitControl32_width_1024
#print axioms certifying_wire_meets_both_sides32

end PvsNP.Frontier.Downstream
