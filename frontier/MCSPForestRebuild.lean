module

public import MCSPMonotoneForest
public import Complexity.Computability.Circuit.Synthesis

/-! Replace disjoint monotone components in topological order, sharing supplies
and paying for each replacement on the boundary of its own component. -/

@[expose] public section

namespace PvsNP.Frontier.ForestRebuild

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest
open scoped Classical

variable {n k g : ℕ} {p : Program signature n g} {output : Wire n g}

structure Forest (p : Program signature n g) (output : Wire n g) where
  roots : Finset (Fin g)
  nodes : Fin g → Finset (Fin g)
  absorbing : Fin g → Bool
  root_mem : ∀ r ∈ roots, r ∈ nodes r
  opcode : ∀ r ∈ roots, ∀ j ∈ nodes r, (p.lines j).op = if absorbing r then .or else .and
  precedes : ∀ r ∈ roots, ∀ j ∈ nodes r, j.val ≤ r.val
  parent : ∀ r ∈ roots, ∀ j ∈ nodes r, j ≠ r →
    ∃ t ∈ nodes r, ∃ a, (p.lines t).wires a = .gate j
  readers : ∀ r ∈ roots, ∀ j ∈ nodes r, j ≠ r →
    ∀ t (a : Fin (signature.Arity (p.lines t).op)), (p.lines t).wires a = .gate j → t ∈ nodes r
  separate : ∀ r ∈ roots, ∀ s ∈ roots, r ≠ s → Disjoint (nodes r) (nodes s)
  precedes_output : ∀ r ∈ roots, wireOrder (.gate r : Wire n g) ≤ wireOrder output

/-- Any chosen subfamily of the verified two-corner forest. -/
noncomputable def ofCorners (p : Program signature n g) (output : Wire n g)
    (h0 : cornerValue p false output = true) (h1 : cornerValue p true output = true)
    (R : Finset (Fin g)) (hR : R ⊆ ORRoot p output ∪ ANDRoot p output) : Forest p output := by
  classical
  let isOR (r : Fin g) := decide (r ∈ ORRoot p output)
  let member (r j : Fin g) : Prop :=
    if isOR r then ORMember p output r j else ANDMember p output r j
  have hOr (r : Fin g) (h : isOR r = true) : r ∈ ORRoot p output :=
    of_decide_eq_true h
  have hAnd (r : Fin g) (hr : r ∈ R) (h : isOR r = false) : r ∈ ANDRoot p output :=
    (Finset.mem_union.mp (hR hr)).resolve_left (fun ho => by
      have ht : isOR r = true := decide_eq_true ho
      rw [h] at ht
      cases ht)
  have hData (r j : Fin g) (hj : member r j) :
      (p.lines j).op = (if isOR r then .or else .and) ∧ j.val ≤ r.val ∧
      (j ≠ r → ∃ t, member r t ∧ ∃ a, (p.lines t).wires a = .gate j) ∧
      (∀ t (a : Fin (signature.Arity (p.lines t).op)), j ≠ r →
        (p.lines t).wires a = .gate j → member r t) := by
    cases h : isOR r
    · have h' : ANDMember p output r j := by simpa only [member, h, Bool.false_eq_true, ↓reduceIte] using hj
      simpa only [member, h, Bool.false_eq_true, ↓reduceIte] using andMember_rebuild_data h0 h1 h'
    · have h' : ORMember p output r j := by simpa only [member, h, ↓reduceIte] using hj
      simpa only [member, h, ↓reduceIte] using orMember_rebuild_data h0 h1 h'
  let nodes (r : Fin g) := Finset.univ.filter (member r)
  have hMem {r j : Fin g} : j ∈ nodes r ↔ member r j := by simp [nodes]
  refine ⟨R, nodes, isOR, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    apply hMem.mpr
    cases h : isOR r
    · simpa only [member, h, Bool.false_eq_true, ↓reduceIte] using ANDMember.self (hAnd r hr h)
    · simpa only [member, h, ↓reduceIte] using ORMember.self (hOr r h)
  · intro r _ j hj
    exact (hData r j (hMem.mp hj)).1
  · intro r _ j hj
    exact (hData r j (hMem.mp hj)).2.1
  · intro r _ j hj hne
    obtain ⟨t, ht, htj⟩ := (hData r j (hMem.mp hj)).2.2.1 hne
    exact ⟨t, hMem.mpr ht, htj⟩
  · intro r _ j hj hne t a ha
    exact hMem.mpr ((hData r j (hMem.mp hj)).2.2.2 t a hne ha)
  · intro r _ s _ hne
    apply Finset.disjoint_left.mpr
    intro j hjr hjs
    have hmr := hMem.mp hjr
    have hms := hMem.mp hjs
    have hopr := (hData r j hmr).1
    have hops := (hData s j hms).1
    cases hor : isOR r <;> cases hos : isOR s
    · simp only [member, hor, hos, Bool.false_eq_true, ↓reduceIte] at hmr hms
      exact hne (andMember_unique_root h1 hmr hms)
    · simp [hor, hos] at hopr hops
      rw [hopr] at hops
      cases hops
    · simp [hor, hos] at hopr hops
      rw [hopr] at hops
      cases hops
    · simp only [member, hor, hos, ↓reduceIte] at hmr hms
      exact hne (orMember_unique_root h0 hmr hms)
  · intro r hr
    cases h : isOR r
    · exact andMember_root_precedes_output (hAnd r hr h)
    · exact orMember_root_precedes_output (hOr r h)

namespace Forest

variable (F : Forest p output)

abbrev Pin (p : Program signature n g) := Σ j : Fin g, Fin (signature.Arity (p.lines j).op)

def pinValue (p : Program signature n g) (a : Pin p) : Wire n g := (p.lines a.1).wires a.2

noncomputable def pins (r : Fin g) : Finset (Pin p) :=
  (F.nodes r).sigma fun _ => Finset.univ

def isInternal (r : Fin g) (w : Wire n g) : Prop := ∃ j ∈ F.nodes r, w = .gate j

/-- All wires entering the component from outside it, including other component roots. -/
noncomputable def boundary (r : Fin g) : Finset (Wire n g) :=
  ((F.pins r).filter fun a => ¬ F.isInternal r (pinValue p a)).image (pinValue p)

private theorem mem_boundary {r : Fin g} {w : Wire n g} :
    w ∈ F.boundary r ↔ ¬ F.isInternal r w ∧
      ∃ j ∈ F.nodes r, ∃ a, (p.lines j).wires a = w := by
  constructor
  · intro hw
    obtain ⟨⟨j, a⟩, ha, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨ha, hExt⟩ := Finset.mem_filter.mp ha
    exact ⟨hExt, j, (Finset.mem_sigma.mp ha).1, a, rfl⟩
  · rintro ⟨he, j, hj, a, rfl⟩
    exact Finset.mem_image.mpr
      ⟨⟨j, a⟩, Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hj, Finset.mem_univ _⟩, he⟩, rfl⟩

/-- The raw input leaves on a component's boundary. -/
noncomputable def rawLeaves (r : Fin g) : Finset (Fin n) :=
  Finset.univ.filter fun i => (.input i : Wire n g) ∈ F.boundary r

theorem mem_rawLeaves {r : Fin g} {i : Fin n} :
    i ∈ F.rawLeaves r ↔ ∃ j ∈ F.nodes r, ∃ a, (p.lines j).wires a = .input i := by
  have h : ¬ F.isInternal r (.input i) := by rintro ⟨j, _, h⟩; cases h
  simp [rawLeaves, F.mem_boundary, h]

theorem card_boundary_le {r : Fin g} (hr : r ∈ F.roots) :
    (F.boundary r).card ≤ (F.nodes r).card + 1 := by
  classical
  let internal := (F.pins r).filter fun a => F.isInternal r (pinValue p a)
  have hPins : (F.pins r).card = 2 * (F.nodes r).card := by
    rw [pins, Finset.card_sigma]
    calc
      _ = ∑ _j ∈ F.nodes r, 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hop := F.opcode r hr j hj
        rw [Finset.card_univ, Fintype.card_fin, hop]
        cases F.absorbing r <;> rfl
      _ = _ := by simp [Nat.mul_comm]
  have hInside : (((F.nodes r).erase r).image (Wire.gate : Fin g → Wire n g)) ⊆
      internal.image (pinValue p) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hne, hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨t, ht, a, ha⟩ := F.parent r hr j hj hne
    exact Finset.mem_image.mpr
      ⟨⟨t, a⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_sigma.mpr ⟨ht, Finset.mem_univ _⟩, j, hj, ha⟩, ha⟩
  have hg : ((F.nodes r).erase r).card ≤ internal.card := by
    calc
      _ = (((F.nodes r).erase r).image (Wire.gate : Fin g → Wire n g)).card :=
        (Finset.card_image_of_injective _ (by intro i j h; cases h; rfl)).symm
      _ ≤ (internal.image (pinValue p)).card := Finset.card_le_card hInside
      _ ≤ _ := Finset.card_image_le
  have hs := (Finset.card_filter_add_card_filter_not
    (s := F.pins r) (p := fun a => F.isInternal r (pinValue p a)))
  have he := Finset.card_erase_add_one (F.root_mem r hr)
  have hw : (F.boundary r).card ≤
      ((F.pins r).filter fun a => ¬ F.isInternal r (pinValue p a)).card := Finset.card_image_le
  change internal.card + _ = _ at hs
  omega

theorem card_rawLeaves_le {r : Fin g} (hr : r ∈ F.roots) :
    (F.rawLeaves r).card ≤ (F.nodes r).card + 1 := by
  apply le_trans _ (F.card_boundary_le hr)
  refine Finset.card_le_card_of_injOn (Wire.input : Fin n → Wire n g) ?_ ?_
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i _ j _ h
    cases h
    rfl

private theorem gate_absorbs_iff (b : Bool) (op : Op) (h : op = if b then .or else .and)
    (v : Fin (signature.Arity op) → Bool) :
    interpretation op v = b ↔ ∃ a, v a = b := by
  cases b
  · change op = .and at h
    subst op
    cases h0 : v 0 <;> cases h1 : v 1 <;>
      simp [interpretation, Fin.exists_fin_succ, h0, h1]
  · change op = .or at h
    subst op
    cases h0 : v 0 <;> cases h1 : v 1 <;>
      simp [interpretation, Fin.exists_fin_succ, h0, h1]

private theorem trace_absorbs_iff {r j : Fin g} (hr : r ∈ F.roots) (hj : j ∈ F.nodes r)
    (x : BitString n) : p.trace interpretation x (.gate j) = F.absorbing r ↔
      ∃ a, p.trace interpretation x ((p.lines j).wires a) = F.absorbing r := by
  rw [p.trace_gate]
  exact gate_absorbs_iff _ _ (F.opcode r hr j hj) _

theorem trace_root_iff_boundary {r : Fin g} (hr : r ∈ F.roots) (x : BitString n) :
    p.trace interpretation x (.gate r) = F.absorbing r ↔
      ∃ w ∈ F.boundary r, p.trace interpretation x w = F.absorbing r := by
  have descend (j : Fin g) (hj : j ∈ F.nodes r)
      (h : p.trace interpretation x (.gate j) = F.absorbing r) :
      ∃ w ∈ F.boundary r, p.trace interpretation x w = F.absorbing r := by
    suffices aux : ∀ d (t : Fin g), t.val = d → t ∈ F.nodes r →
        p.trace interpretation x (.gate t) = F.absorbing r →
        ∃ w ∈ F.boundary r, p.trace interpretation x w = F.absorbing r from aux _ j rfl hj h
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j hjd hj h
      obtain ⟨a, ha⟩ := (F.trace_absorbs_iff hr hj x).mp h
      by_cases hInt : F.isInternal r ((p.lines j).wires a)
      · obtain ⟨t, ht, hw⟩ := hInt
        have hlt := p.lt_of_lines_wires_eq_gate j a t hw
        exact ih t.val (by omega) t rfl ht (hw ▸ ha)
      · exact ⟨_, (F.mem_boundary).mpr ⟨hInt, j, hj, a, rfl⟩, ha⟩
  have ascend (j : Fin g) (hj : j ∈ F.nodes r)
      (h : p.trace interpretation x (.gate j) = F.absorbing r) :
      p.trace interpretation x (.gate r) = F.absorbing r := by
    suffices aux : ∀ d (t : Fin g), g - t.val = d → t ∈ F.nodes r →
        p.trace interpretation x (.gate t) = F.absorbing r →
        p.trace interpretation x (.gate r) = F.absorbing r from aux _ j rfl hj h
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro t hd ht htVal
      by_cases htr : t = r
      · exact htr ▸ htVal
      · obtain ⟨q, hq, a, ha⟩ := F.parent r hr t ht htr
        have hlt := p.lt_of_lines_wires_eq_gate q a t ha
        have hqVal := (F.trace_absorbs_iff hr hq x).mpr ⟨a, ha.symm ▸ htVal⟩
        exact ih (g - q.val) (by have := q.isLt; omega) q rfl hq hqVal
  constructor
  · exact descend r (F.root_mem r hr)
  · rintro ⟨w, hw, hVal⟩
    obtain ⟨_, j, hj, a, ha⟩ := F.mem_boundary.mp hw
    exact ascend j hj ((F.trace_absorbs_iff hr hj x).mpr ⟨a, ha.symm ▸ hVal⟩)

section Reconstruction

variable (fill : BitString k → BitString n)

def wireFunction (fill : BitString k → BitString n) (w : Wire n g) : BooleanFunction k :=
  fun U => p.trace interpretation (fill U) w

/-- Functions at a tree's boundary after the input identification. Repeated
leaves and semantic aliases contribute only one element. -/
noncomputable def boundaryFunctions (r : Fin g) : Finset (BooleanFunction k) :=
  (F.boundary r).image (wireFunction (p := p) fill)

noncomputable def replacementCost (r : Fin g) : ℕ :=
  if ∃ b : Bool, wireFunction (p := p) fill (.gate r) = fun _ => b then 0
  else (F.boundaryFunctions fill r).card - 1

noncomputable def savings : ℕ :=
  ∑ r ∈ F.roots, ((F.nodes r).card - F.replacementCost fill r)

theorem replacementCost_le {r : Fin g} (hr : r ∈ F.roots) :
    F.replacementCost fill r ≤ (F.nodes r).card := by
  classical
  have h := (Finset.card_image_le (f := wireFunction (p := p) fill)).trans (F.card_boundary_le hr)
  change (F.boundaryFunctions fill r).card ≤ _ at h
  unfold replacementCost
  split <;> omega

theorem replacementCost_eq_zero_of_constant {r : Fin g} {b : Bool}
    (h : ∀ U, wireFunction (p := p) fill (.gate r) U = b) : F.replacementCost fill r = 0 := by
  simp [replacementCost, show ∃ b : Bool, wireFunction (p := p) fill (.gate r) = fun _ => b from
    ⟨b, funext h⟩]

theorem component_le_savings_of_constant {r : Fin g} (hr : r ∈ F.roots) {b : Bool}
    (h : ∀ U, wireFunction (p := p) fill (.gate r) U = b) : (F.nodes r).card ≤ F.savings fill := by
  have he := F.replacementCost_eq_zero_of_constant fill h
  unfold savings
  simpa only [he, Nat.sub_zero] using
    (Finset.single_le_sum (f := fun t => (F.nodes t).card - F.replacementCost fill t)
      (fun _ _ => Nat.zero_le _) hr)

/-- First compress the original component to its distinct wire boundary,
then merge equal restricted functions, then charge a collapse only against
the remaining replacement cost. -/
theorem savings_eq_sum (fill : BitString k → BitString n) :
    F.savings fill = ∑ r ∈ F.roots,
      ((F.nodes r).card - ((F.boundary r).card - 1) +
       (((F.boundary r).card - 1) - ((F.boundaryFunctions fill r).card - 1)) +
       (((F.boundaryFunctions fill r).card - 1) - F.replacementCost fill r)) := by
  unfold savings
  apply Finset.sum_congr rfl
  intro r hr
  have hw := F.card_boundary_le hr
  have hv : (F.boundaryFunctions fill r).card ≤ (F.boundary r).card := Finset.card_image_le
  have hc : F.replacementCost fill r ≤ (F.boundaryFunctions fill r).card - 1 := by
    unfold replacementCost
    split <;> omega
  omega

/-- A nonempty aggregate costs one binary gate per distinct argument after the first. -/
private theorem synth_aggregate (s : Set (BooleanFunction k)) (b : Bool)
    (L : Finset (BooleanFunction k)) (hL : ∀ f ∈ L, f ∈ s)
    (hNeutral : (fun _ => !b) ∈ s) :
    ∃ f : BooleanFunction k,
      (∀ U, f U = b ↔ ∃ v ∈ L, v U = b) ∧
      Synthesis interpretation s {f} (L.card - 1) := by
  induction L using Finset.induction_on with
  | empty =>
    exact ⟨_, fun U => by cases b <;> simp, Synthesis.of_mem hNeutral⟩
  | @insert v L hv ih =>
    have hvS := hL v (Finset.mem_insert_self v L)
    by_cases hL0 : L = ∅
    · subst L
      simpa using (show ∃ f : BooleanFunction k, (∀ U, f U = b ↔ v U = b) ∧
          Synthesis interpretation s {f} 0 from ⟨v, fun _ => Iff.rfl, Synthesis.of_mem hvS⟩)
    · obtain ⟨f, hf, hSynth⟩ := ih (fun u hu => hL u (Finset.mem_insert_of_mem hu))
      let w : BooleanFunction k := fun U => if b then f U || v U else f U && v U
      have hw (U : BitString k) : w U = b ↔ v U = b ∨ f U = b := by
        change (if b then f U || v U else f U && v U) = b ↔ _
        generalize f U = x
        generalize v U = y
        cases b <;> cases x <;> cases y <;> decide
      have hOp : Synthesis interpretation s {w} ((L.card - 1) + 1) := by
        cases b
        · exact hSynth.and (Synthesis.of_mem hvS)
        · exact hSynth.or (Synthesis.of_mem hvS)
      refine ⟨w, fun U => by simp [hw, hf], hOp.mono Set.Subset.rfl Set.Subset.rfl ?_⟩
      rw [Finset.card_insert_of_notMem hv]
      have hPos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hL0)
      omega

private theorem synth_root (s : Set (BooleanFunction k)) {r : Fin g} (hr : r ∈ F.roots)
    (hBoundary : ∀ w ∈ F.boundary r, wireFunction (p := p) fill w ∈ s)
    (hConst : ∀ b : Bool, (fun _ => b) ∈ s) :
    Synthesis interpretation s {wireFunction (p := p) fill (.gate r)} (F.replacementCost fill r) := by
  classical
  unfold replacementCost
  split
  · rename_i h
    obtain ⟨b, hb⟩ := h
    rw [hb]
    exact Synthesis.of_mem (hConst b)
  · have hAvail : ∀ f ∈ F.boundaryFunctions fill r, f ∈ s := by
      intro f hf
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hf
      exact hBoundary w hw
    obtain ⟨f, hf, hSynth⟩ := synth_aggregate s (F.absorbing r) (F.boundaryFunctions fill r)
      hAvail (hConst _)
    have he (U : BitString k) :
        f U = F.absorbing r ↔ wireFunction (p := p) fill (.gate r) U = F.absorbing r := by
      rw [hf, wireFunction, F.trace_root_iff_boundary hr]
      simp only [boundaryFunctions, Finset.mem_image]
      exact ⟨fun ⟨_, ⟨w, hw, rfl⟩, h⟩ => ⟨w, hw, h⟩,
        fun ⟨w, hw, h⟩ => ⟨_, ⟨w, hw, rfl⟩, h⟩⟩
    have hEq : f = wireFunction (p := p) fill (.gate r) := by
      funext U
      have hb (x y b : Bool) (h : x = b ↔ y = b) : x = y := by
        cases x <;> cases y <;> cases b <;> simp_all
      exact hb _ _ _ (he U)
    rwa [hEq] at hSynth

private noncomputable def covered : Finset (Fin g) := F.roots.biUnion F.nodes

private def visible (j : Fin g) : Prop := j ∈ F.roots ∨ j ∉ F.covered

private theorem visible_of_wire {j t : Fin g} (hj : j ∉ F.covered)
    (a : Fin (signature.Arity (p.lines j).op)) (ha : (p.lines j).wires a = .gate t) :
    F.visible t := by
  by_contra ht
  obtain ⟨hnt, ht⟩ := not_or.mp ht
  obtain ⟨r, hr, htr⟩ := Finset.mem_biUnion.mp (not_not.mp ht)
  have hne : t ≠ r := fun he => hnt (he ▸ hr)
  exact hj (Finset.mem_biUnion.mpr ⟨r, hr, F.readers r hr t htr hne j a ha⟩)

private theorem boundary_gate_visible_before {r t : Fin g} (hr : r ∈ F.roots)
    (ht : (.gate t : Wire n g) ∈ F.boundary r) : F.visible t ∧ t.val < r.val := by
  obtain ⟨hOut, j, hj, a, ha⟩ := F.mem_boundary.mp ht
  have hLt := p.lt_of_lines_wires_eq_gate j a t ha
  refine ⟨?_, lt_of_lt_of_le hLt (F.precedes r hr j hj)⟩
  by_contra hc
  obtain ⟨hnt, ht⟩ := not_or.mp hc
  obtain ⟨u, hu, htu⟩ := Finset.mem_biUnion.mp (not_not.mp ht)
  have hne : t ≠ u := fun he => hnt (he ▸ hu)
  have hru : r ≠ u := fun he => hOut ⟨t, he ▸ htu, rfl⟩
  exact (Finset.disjoint_left.mp (F.separate r hr u hu hru)) hj (F.readers u hu t htu hne j a ha)

private noncomputable def stageCost (j : Fin g) : ℕ :=
  if j ∈ F.roots then F.replacementCost fill j else if j ∈ F.covered then 0 else 1

private def earlier (d : ℕ) : Set (BooleanFunction k) :=
  {f | ∃ j : Fin g, F.visible j ∧ j.val < d ∧ f = wireFunction (p := p) fill (.gate j)}

private noncomputable def prefixCost (d : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin g => j.val < d), F.stageCost fill j

private theorem prefixCost_step (j : Fin g) :
    F.prefixCost fill (j.val + 1) = F.prefixCost fill j.val + F.stageCost fill j := by
  classical
  have he : (Finset.univ.filter fun t : Fin g => t.val < j.val + 1) =
      insert j (Finset.univ.filter fun t : Fin g => t.val < j.val) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro ht
      by_cases h : t.val < j.val
      · exact Or.inr h
      · exact Or.inl (Fin.ext (by omega))
    · rintro (rfl | ht) <;> omega
  unfold prefixCost
  rw [he, Finset.sum_insert (by simp)]
  omega

private theorem synth_prefix (s : Set (BooleanFunction k))
    (hInput : ∀ i, wireFunction (p := p) fill (.input i) ∈ s)
    (hConst : ∀ b : Bool, (fun _ => b) ∈ s) :
    ∀ d ≤ g, Synthesis interpretation s (F.earlier fill d) (F.prefixCost fill d) := by
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
    let last := wireFunction (p := p) fill (.gate j)
    have hStep : F.prefixCost fill (d + 1) = F.prefixCost fill d + F.stageCost fill j :=
      F.prefixCost_step fill j
    have hPrev := ih (by omega)
    by_cases hv : F.visible j
    · have hEarlier : F.earlier fill (d + 1) = F.earlier fill d ∪ {last} := by
        ext f
        constructor
        · rintro ⟨t, ht, hlt, he⟩
          by_cases htd : t.val < d
          · exact Or.inl ⟨t, ht, htd, he⟩
          · exact Or.inr (he.trans (congrArg (fun i => wireFunction fill (.gate i))
              (show t = j by apply Fin.ext; change _ = d; omega)))
        · rintro (⟨t, ht, hlt, he⟩ | rfl)
          · exact ⟨t, ht, by omega, he⟩
          · exact ⟨j, hv, by change d < d + 1; omega, rfl⟩
      have hLast : Synthesis interpretation (s ∪ F.earlier fill d) {last} (F.stageCost fill j) := by
        rcases hv with hr | hj
        · rw [stageCost, ite_eq_left hr]
          apply F.synth_root fill _ hr ?_ (fun b => Or.inl (hConst b))
          intro w hw
          cases w with
          | input i => exact Or.inl (hInput i)
          | gate t =>
            have ht := F.boundary_gate_visible_before hr hw
            exact Or.inr ⟨t, ht.1, ht.2, rfl⟩
        · have hr : j ∉ F.roots := fun hr => hj (Finset.mem_biUnion.mpr ⟨j, hr, F.root_mem j hr⟩)
          rw [stageCost, ite_eq_right hr, ite_eq_right hj]
          have hEval : last = fun U => interpretation (p.lines j).op
              (fun a => wireFunction (p := p) fill ((p.lines j).wires a) U) :=
            funext fun _ => p.trace_gate _ _ j
          rw [hEval]
          apply Synthesis.gate
          intro a
          cases ha : (p.lines j).wires a with
          | input i => exact Or.inl (hInput i)
          | gate t => exact Or.inr ⟨t, F.visible_of_wire hj a ha, p.lt_of_lines_wires_eq_gate j a t ha, rfl⟩
      rw [hEarlier, hStep]
      exact hPrev.comp hLast
    · have hEarlier : F.earlier fill (d + 1) = F.earlier fill d := by
        ext f
        constructor
        · rintro ⟨t, ht, hlt, he⟩
          refine ⟨t, ht, ?_, he⟩
          by_contra hn
          exact hv ((show t = j by apply Fin.ext; change _ = d; omega) ▸ ht)
        · rintro ⟨t, ht, hlt, he⟩
          exact ⟨t, ht, by omega, he⟩
      rw [hEarlier, hStep]
      exact hPrev.mono Set.Subset.rfl Set.Subset.rfl (Nat.le_add_right _ _)

private theorem prefixCost_add_savings :
    F.prefixCost fill g + F.savings fill = g := by
  classical
  let R := F.roots
  let G := F.covered
  have hSub : R ⊆ G := fun j hj => Finset.mem_biUnion.mpr ⟨j, hj, F.root_mem j hj⟩
  have hCovered : (∑ j ∈ G, F.stageCost fill j) = ∑ j ∈ R, F.replacementCost fill j := by
    rw [← Finset.sum_subset hSub (fun j hj hR => by
      simp [stageCost, show j ∈ F.covered from hj, show j ∉ F.roots from hR])]
    apply Finset.sum_congr rfl
    intro j hj
    simp [stageCost, show j ∈ F.roots from hj]
  have hOutside : (∑ j ∈ Finset.univ \ G, F.stageCost fill j) = (Finset.univ \ G).card := by
    calc
      _ = ∑ _j ∈ Finset.univ \ G, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hg : j ∉ F.covered := (Finset.mem_sdiff.mp hj).2
        have hr : j ∉ F.roots := fun hr => hg (hSub hr)
        simp [stageCost, hg, hr]
      _ = _ := by simp
  have hTotal := Finset.sum_sdiff (Finset.subset_univ G) (f := F.stageCost fill)
  rw [hOutside, hCovered] at hTotal
  have hParts := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ G)
  rw [Finset.card_univ, Fintype.card_fin] at hParts
  have hG : G.card = ∑ r ∈ R, (F.nodes r).card := by
    apply Finset.card_biUnion
    exact fun r hr s hs hne => F.separate r hr s hs hne
  have hCharge : (∑ r ∈ R, F.replacementCost fill r) + F.savings fill = G.card := by
    rw [hG, savings, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hle := F.replacementCost_le fill hr
    omega
  have hPrefix : F.prefixCost fill g = ∑ j : Fin g, F.stageCost fill j := by
    simp [prefixCost]
  omega

/-- Keep every gate outside the selected components, and replace each selected
root exactly once. The only external costs are the shared input supplies. -/
theorem rebuild_budget (s : Set (BooleanFunction k)) {extra : ℕ}
    (hSupply : Synthesis interpretation (inputs k) s extra)
    (hInput : ∀ i, wireFunction (p := p) fill (.input i) ∈ s)
    (hConst : ∀ b : Bool, (fun _ => b) ∈ s) :
    complexity interpretation (single (wireFunction (p := p) fill output)) + F.savings fill ≤ g + extra := by
  have hOutput (w : Wire n g) (hBefore : ∀ r ∈ F.roots,
      wireOrder (.gate r : Wire n g) ≤ wireOrder w) :
      wireFunction (p := p) fill w ∈ s ∪ F.earlier fill g := by
    cases w with
    | input i => exact Or.inl (hInput i)
    | gate j =>
      refine Or.inr ⟨j, ?_, j.isLt, rfl⟩
      by_contra hj
      obtain ⟨hjr, hjg⟩ := not_or.mp hj
      obtain ⟨r, hr, hjr'⟩ := Finset.mem_biUnion.mp (not_not.mp hjg)
      have hle := F.precedes r hr j hjr'
      have hBack := hBefore r hr
      change r.val + 1 ≤ j.val + 1 at hBack
      exact hjr ((show j = r by apply Fin.ext; omega) ▸ hr)
  have hs := (F.synth_prefix fill s hInput hConst g le_rfl).comp
    (Synthesis.of_mem (hOutput output F.precedes_output))
  have hs' : Synthesis interpretation (inputs k ∪ s) {wireFunction (p := p) fill output}
      (F.prefixCost fill g + 0) := hs.mono Set.subset_union_right Set.subset_union_right le_rfl
  have hSize := (hSupply.trans hs').complexity_le
  have hBudget := F.prefixCost_add_savings fill
  omega

end Reconstruction

#print axioms trace_root_iff_boundary
#print axioms savings_eq_sum
#print axioms rebuild_budget

end Forest

end PvsNP.Frontier.ForestRebuild
