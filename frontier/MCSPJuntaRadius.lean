module

public import MCSPRadiusControl

/-! A control for patches of nine-bit prefix probes with arbitrary prefix
coordinates. The dynamic program shares distance tests between prefixes
by computing all restricted candidates at every subtree. -/

@[expose] public section

namespace PvsNP.Frontier.JuntaRadius

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CommunicationCut CornerCertificates SuperTwoN PermutedCut
open PatchedCut (patch)
open scoped Classical

/-- Each slot may read a represented coordinate or a constant. Constants
keep this type of code closed under fixing the first represented coordinate. -/
abbrev CodeFor (r m : ℕ) := (Fin r → Fin m ⊕ Bool) × BooleanFunction r

abbrev Code (m : ℕ) := CodeFor 9 m

def value {r m : ℕ} (c : CodeFor r m) (z : BitString m) : Bool :=
  c.2 (fun j => (c.1 j).elim z id)

def restrict {r m : ℕ} (b : Bool) (c : CodeFor r (m + 1)) : CodeFor r m :=
  (fun j => (c.1 j).elim (Fin.cases (.inr b) Sum.inl) Sum.inr, c.2)

theorem restrict_value {r m : ℕ} (b : Bool) (c : CodeFor r (m + 1)) (z : BitString m) :
    value (restrict b c) z = value c (Fin.cons b z) := by
  change c.2 (fun j => ((restrict b c).1 j).elim z id) = c.2 _
  apply congrArg c.2
  funext j
  rcases h : c.1 j with i | v
  · simp only [restrict, h, Sum.elim_inl]
    induction i using Fin.cases with
    | zero => rfl
    | succ t => rfl
  · simp [restrict, h]

def distance {m : ℕ} (X Y : BooleanFunction m) : ℕ :=
  (Finset.univ.filter fun z => X z ≠ Y z).card

theorem distance_eq_sum {m : ℕ} (X Y : BooleanFunction m) :
    distance X Y = ∑ z : BitString m, if X z ≠ Y z then 1 else 0 :=
  (Finset.sum_boole (R := ℕ) (fun z => X z ≠ Y z) Finset.univ).symm

def face {m : ℕ} (b : Bool) (z : BitString m) : BitString (m + 1) := Fin.cons b z

theorem distance_succ {m : ℕ} (X Y : BooleanFunction (m + 1)) :
    distance X Y = distance (X ∘ face false) (Y ∘ face false) +
      distance (X ∘ face true) (Y ∘ face true) := by
  simp only [distance_eq_sum]
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, Nat.add_comm]
  rfl

private theorem distance_zero (X Y : BooleanFunction 0) :
    distance X Y = (if X (fun _ => false) = Y (fun _ => false) then 0 else 1) := by
  have he : (Finset.univ : Finset (BitString 0)) = {fun _ => false} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact Fin.elim0 i
  rw [distance_eq_sum, he, Finset.sum_singleton]
  by_cases h : X (fun _ => false) = Y (fun _ => false) <;> simp [h]

def viewed (m : ℕ) (T : BitString (2 ^ m)) : BooleanFunction m :=
  (MCSP.truthTable m).symm T

noncomputable def controlFor (r m : ℕ) (T : BitString (2 ^ m)) : Bool :=
  decide (∃ c : CodeFor r m, distance (viewed m T) (value c) ≤ 4)

noncomputable abbrev control (m : ℕ) := controlFor 9 m

/-- Moving from represented addresses to truth-table locations preserves
the number of disagreements. -/
theorem distance_eq_raw {m : ℕ} (T : BitString (2 ^ m)) (Y : BooleanFunction m) :
    distance (viewed m T) Y =
      ((Finset.univ : Finset (Fin (2 ^ m))).filter
        fun i => T i ≠ (MCSP.truthTable m Y) i).card := by
  let e := BitString.equivFin m
  let A := (Finset.univ : Finset (BitString m)).filter (fun z => viewed m T z ≠ Y z)
  let B := (Finset.univ : Finset (Fin (2 ^ m))).filter fun i => T i ≠ (MCSP.truthTable m Y) i
  have he : A.map e.toEmbedding = B := by
    ext i
    obtain ⟨z, rfl⟩ := e.surjective i
    rw [Finset.mem_map_equiv]
    simp only [A, B, Equiv.symm_apply_apply, Finset.mem_filter, Finset.mem_univ, true_and]
    change viewed m T z ≠ Y z ↔ T (BitString.equivFin m z) ≠ (MCSP.truthTable m Y) (BitString.equivFin m z)
    rw [MCSP.truthTable_apply, Equiv.symm_apply_apply]
    rfl
  change A.card = B.card
  rw [← he, Finset.card_map]

theorem patch_distance_le {m : ℕ} (D : Finset (Fin (2 ^ m))) (Y : BooleanFunction m) :
    distance (viewed m (patch D (MCSP.truthTable m Y))) Y ≤ D.card := by
  rw [distance_eq_raw]
  apply Finset.card_le_card
  intro i hi
  have hne := (Finset.mem_filter.mp hi).2
  by_contra hn
  simp [patch, hn] at hne

/-- The control recognizes the radius-four neighborhood of the coded tables. -/
theorem controlFor_iff {r m : ℕ} (T : BitString (2 ^ m)) :
    controlFor r m T = true ↔ ∃ c : CodeFor r m, ∃ D : Finset (Fin (2 ^ m)),
      D.card ≤ 4 ∧ T = patch D (MCSP.truthTable m (value c)) := by
  rw [controlFor, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc⟩
    let Y := MCSP.truthTable m (value c)
    let D := (Finset.univ : Finset (Fin (2 ^ m))).filter fun i => T i ≠ Y i
    have hd : D.card ≤ 4 := (distance_eq_raw T (value c)).symm ▸ hc
    refine ⟨c, D, hd, ?_⟩
    change T = patch D Y
    funext i
    cases hx : T i <;> cases hy : Y i <;> simp [patch, D, hx, hy]
  · rintro ⟨c, D, hD, rfl⟩
    exact ⟨c, (patch_distance_le D (value c)).trans hD⟩

theorem control_iff {m : ℕ} (T : BitString (2 ^ m)) :
    control m T = true ↔ ∃ c : Code m, ∃ D : Finset (Fin (2 ^ m)),
      D.card ≤ 4 ∧ T = patch D (MCSP.truthTable m (value c)) := controlFor_iff T

#print axioms control_iff


section Size

variable {l r : ℕ}

/-- The state says that the table and this candidate disagree at most k times. -/
def state {m : ℕ} (read : BitString m → BooleanFunction l) (p : CodeFor r m × Fin 5) :
    BooleanFunction l := fun X => decide (distance (fun z => read z X) (value p.1) ≤ p.2.val)

private theorem split_budget (a b : ℕ) (k : Fin 5) :
    a + b ≤ k.val ↔ ∃ j : Fin 5, j.val ≤ k.val ∧ a ≤ j.val ∧ b ≤ k.val - j.val := by
  constructor
  · intro h
    exact ⟨⟨a, by have := k.isLt; omega⟩, by dsimp; omega, le_rfl, by dsimp; omega⟩
  · rintro ⟨j, hj, ha, hb⟩
    omega

private theorem state_step {m : ℕ} (read : BitString (m + 1) → BooleanFunction l)
    (s : Set (BooleanFunction l)) (c : CodeFor r (m + 1)) (k : Fin 5)
    (h0 : ∀ j : Fin 5, state (read ∘ face false) (restrict false c, j) ∈ s)
    (h1 : ∀ j : Fin 5, state (read ∘ face true) (restrict true c, j) ∈ s) :
    Synthesis interpretation s {state read (c, k)} 11 := by
  let choices := (Finset.univ : Finset (Fin 5)).filter fun j => j.val ≤ k.val
  let rem (j : Fin 5) : Fin 5 := ⟨k.val - j.val, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩
  let test (j : Fin 5) (X : BitString l) :=
    state (read ∘ face false) (restrict false c, j) X &&
      state (read ∘ face true) (restrict true c, rem j) X
  have hGate (j : Fin 5) : Synthesis interpretation s {test j} 1 :=
    (Synthesis.of_mem (h0 j)).and (Synthesis.of_mem (h1 (rem j)))
  have hAny := Synthesis.exists_mem choices test (fun _ => 1) (fun j _ => hGate j)
  apply (Synthesis.congr_iff hAny (g := state read (c,k)) ?_).mono Set.Subset.rfl Set.Subset.rfl ?_
  · intro X
    have hValue (b : Bool) : value c ∘ face b = value (restrict b c) :=
      funext fun z => (restrict_value b c z).symm
    simp only [state, decide_eq_true_eq, choices, Finset.mem_filter, Finset.mem_univ, true_and, test,
      Bool.and_eq_true, rem, Function.comp_apply]
    rw [distance_succ, hValue false, hValue true]
    exact (split_budget _ _ _).symm
  · have hc : choices.card ≤ 5 := Finset.card_le_univ _
    simp only [Finset.sum_const, smul_eq_mul]
    omega

private theorem code_card (r m : ℕ) : Fintype.card (CodeFor r m) = (m + 2) ^ r * 2 ^ 2 ^ r := by
  have hp (w : ℕ) : Fintype.card (BooleanFunction w) = 2 ^ 2 ^ w := by classical simp
  simp only [CodeFor, Fintype.card_prod, Fintype.card_fun, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_bool, hp]

def layerFor (r m : ℕ) : ℕ := 55 * ((m + 2) ^ r * 2 ^ 2 ^ r)

def budgetFor (r : ℕ) : ℕ → ℕ
  | 0 => layerFor r 0
  | m + 1 => 2 * budgetFor r m + layerFor r (m + 1)

private theorem sum_state_cost (r m : ℕ) (k : ℕ) :
    (∑ _p : CodeFor r m × Fin 5, k) = ((m + 2) ^ r * 2 ^ 2 ^ r * 5) * k := by
  rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, code_card, Fintype.card_fin]

private theorem synth_states {m : ℕ} (s : Set (BooleanFunction l))
    (read : BitString m → BooleanFunction l) (hr : ∀ z, read z ∈ s) :
    Synthesis interpretation s (Set.range (state (r := r) read)) (budgetFor r m) := by
  induction m with
  | zero =>
    have hOne (p : CodeFor r 0 × Fin 5) : Synthesis interpretation s {state read p} 1 := by
      let z : BitString 0 := fun _ => false
      by_cases h0 : p.2.val = 0
      · have he : state read p = fun X => decide (read z X = value p.1 z) := by
          funext X
          unfold state
          rw [distance_zero, h0]
          change decide ((if read z X = value p.1 z then 0 else 1) ≤ 0) = _
          by_cases h : read z X = value p.1 z <;> simp [h]
        rw [he]
        exact Synthesis.literal (hr z) (value p.1 z)
      · have he : state read p = fun _ => true := by
          funext X
          unfold state
          rw [distance_zero]
          change decide ((if read z X = value p.1 z then 0 else 1) ≤ p.2.val) = true
          apply decide_eq_true
          split <;> omega
        rw [he]
        exact Synthesis.const true
    apply (Synthesis.family (state (r := r) read) (fun _ => 1) hOne).mono Set.Subset.rfl Set.Subset.rfl
    rw [sum_state_cost, budgetFor, layerFor]
    omega
  | succ m ih =>
    let r0 := read ∘ face false
    let r1 := read ∘ face true
    have h0 := ih r0 (fun z => hr (Fin.cons false z))
    have h1 := ih r1 (fun z => hr (Fin.cons true z))
    let S := s ∪ (Set.range (state (r := r) r0) ∪ Set.range (state (r := r) r1))
    have hNew (p : CodeFor r (m + 1) × Fin 5) : Synthesis interpretation S {state read p} 11 :=
      state_step read S p.1 p.2 (fun j => Or.inr (Or.inl ⟨(restrict false p.1,j), rfl⟩))
        (fun j => Or.inr (Or.inr ⟨(restrict true p.1,j), rfl⟩))
    have h := (h0.union h1).trans (Synthesis.family (state (r := r) read) (fun _ => 11) hNew)
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    rw [sum_state_cost, budgetFor, layerFor]
    omega

theorem controlFor_size (r m : ℕ) :
    complexity interpretation (single (controlFor r m)) ≤ budgetFor r m + (m + 2) ^ r * 2 ^ 2 ^ r + 1 := by
  let read (z : BitString m) (T : BitString (2 ^ m)) := T (BitString.equivFin m z)
  have hBase := synth_states (r := r) (inputs (2 ^ m)) read (fun z => ⟨BitString.equivFin m z, rfl⟩)
  let S := inputs (2 ^ m) ∪ Set.range (state (r := r) read)
  have hOne (c : CodeFor r m) :
      Synthesis interpretation S {state read (c,4)} 0 := Synthesis.of_mem (Or.inr ⟨(c,4), rfl⟩)
  have h := Synthesis.exists_mem Finset.univ (fun c : CodeFor r m => state read (c,4)) (fun _ => 0)
    (fun c _ => hOne c)
  have hLast := Synthesis.congr_iff h (g := controlFor r m) (fun T => by
    simp only [controlFor, decide_eq_true_eq, Finset.mem_univ, true_and, state]
    rfl)
  have out := (hBase.trans hLast).complexity_le
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, code_card] at out
  omega

end Size

#print axioms synth_states
abbrev layer (m : ℕ) := layerFor 9 m
abbrev budget (m : ℕ) := budgetFor 9 m

theorem control_size (m : ℕ) :
    complexity interpretation (single (control m)) ≤ budget m + (m + 2) ^ 9 * 2 ^ 512 + 1 := by
  have h := controlFor_size 9 m
  rwa [show (2 : ℕ) ^ 9 = 512 by decide] at h

#print axioms control_size
#print axioms controlFor_size


section Tests

private theorem value_cost_from_circuit {r m : ℕ} (c : CodeFor r m)
    (core : Circuit signature r 1) (hc : core.Computes interpretation (single c.2)) :
    complexity interpretation (single (value c)) ≤ 2 + core.size := by
  let low : BooleanFunction m := fun _ => false
  let high : BooleanFunction m := fun _ => true
  let constants : Set (BooleanFunction m) := {low} ∪ {high}
  let a (j : Fin r) (x : BitString m) : Bool := (c.1 j).elim x id
  have hConst : Synthesis interpretation (inputs m) constants 2 :=
    (Synthesis.const (s := inputs m) false).union (Synthesis.const true)
  have ha (j : Fin r) : a j ∈ inputs m ∪ constants := by
    cases he : c.1 j with
    | inl i =>
      exact Or.inl ⟨i, by funext x; simp [a, he]⟩
    | inr b =>
      cases b
      · exact Or.inr (Or.inl (by funext x; simp [a, he, low]))
      · exact Or.inr (Or.inr (by funext x; simp [a, he, high]))
  have hCore := Synthesis.circuit (I := interpretation) core a ha
  have hEval (x : BitString m) : core.eval interpretation (fun j => a j x) 0 = value c x :=
    congrFun (hc (fun j => a j x)) 0
  have hOne : Synthesis interpretation (inputs m ∪ constants) {value c} core.size :=
    hCore.mono Set.Subset.rfl (fun g hg => by
      obtain rfl := hg
      exact ⟨0, funext hEval⟩) le_rfl
  exact (hConst.trans hOne).complexity_le

private theorem value_cost {m : ℕ} (c : Code m) :
    complexity interpretation (single (value c)) ≤ 850 := by
  let core := ShannonSynthesis.circuit (k := 2) (d := 7) c.2
  have hc : core.Computes interpretation (single c.2) := by
    intro x
    funext j
    exact ShannonSynthesis.eval_circuit (k := 2) (d := 7) c.2 x j
  have hSize : core.size ≤ 848 := ShannonSynthesis.size_circuit_le (k := 2) (d := 7) c.2
  exact (value_cost_from_circuit c core hc).trans (Nat.add_le_add_left hSize 2)

theorem value_costFor {r m : ℕ} (c : CodeFor r m) :
    complexity interpretation (single (value c)) ≤ 2 ^ r * (2 * r + 2) + 3 := by
  obtain ⟨core, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single c.2)
  have hSize : core.size ≤ 2 ^ r * (2 * r + 2) + 1 := by
    rw [hs]
    exact (Synthesis.selected (id : Fin r → Fin r) c.2).complexity_le
  have h := value_cost_from_circuit c core hc
  omega

theorem patched_function_of_budget {m B : ℕ} (f : BooleanFunction m) (D : Finset (Fin (2 ^ m)))
    (hD : D.card ≤ 4) (hV : complexity interpretation (single f) ≤ B)
    (budget : B + 5 * m + 13 ≤ m ^ 2) :
    mcspSquare m (patch D (MCSP.truthTable m f)) = true := by
  let fix : BooleanFunction m := fun z => decide (BitString.equivFin m z ∈ D)
  have hEq : (MCSP.truthTable m).symm (patch D (MCSP.truthTable m f)) =
      fun z => f z ^^ fix z := by
    funext z
    change ((MCSP.truthTable m f) (BitString.equivFin m z) ^^
      decide (BitString.equivFin m z ∈ D)) = (f z ^^ fix z)
    rw [MCSP.truthTable_apply, Equiv.symm_apply_apply]
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hEq]
  have hFix : complexity interpretation (single fix) ≤ m + D.card * (m + 2) + 1 :=
    MinorityResidual.point_indicator_complexity_le m D
  have hD' := Nat.mul_le_mul_right (m + 2) hD
  exact (complexity_xor_le f fix).trans (by omega)

theorem patched_code_of_budget {r m B : ℕ} (c : CodeFor r m) (D : Finset (Fin (2 ^ m)))
    (hD : D.card ≤ 4) (hV : complexity interpretation (single (value c)) ≤ B)
    (budget : B + 5 * m + 13 ≤ m ^ 2) :
    mcspSquare m (patch D (MCSP.truthTable m (value c))) = true :=
  patched_function_of_budget (value c) D hD hV budget

private theorem patched_code_accepted {m : ℕ} (hm : 32 ≤ m) (c : Code m)
    (D : Finset (Fin (2 ^ m))) (hD : D.card ≤ 4) :
    mcspSquare m (patch D (MCSP.truthTable m (value c))) = true := by
  apply patched_code_of_budget c D hD (value_cost c)
  have h := Nat.mul_le_mul_right m hm
  rw [← pow_two] at h
  omega

/-- The control accepts only exact YES instances, even outside the tested cuts. -/
theorem control_implies_exact {m : ℕ} (hm : 32 ≤ m) {T : BitString (2 ^ m)}
    (h : control m T = true) : mcspSquare m T = true := by
  obtain ⟨c, D, hD, hT⟩ := (control_iff T).mp h
  rw [hT]
  exact patched_code_accepted hm c D hD

theorem control_sparse {m : ℕ} (hm : 32 ≤ m) :
    (acceptingTables (control m)).card ≤ 2 ^ descriptionBitBound m := by
  apply le_trans _ (card_accepting_mcspSquare_le m)
  apply Finset.card_le_card
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, control_implies_exact hm (Finset.mem_filter.mp hT).2⟩

private theorem patched_transport {n : ℕ} (e : Equiv.Perm (Fin n)) (X : BitString n) (D : Finset (Fin n)) :
    patch D (X ∘ e) = (patch (D.map e.toEmbedding) X) ∘ e := by
  funext i
  simp [patch, Function.comp_apply]

theorem prefix_code_after_perm {r s : ℕ} (f : BooleanFunction r)
    (e : Equiv.Perm (Fin (r + (s + 1)))) :
    ∃ c : CodeFor r (r + (s + 1)), probe s f ∘ tablePerm e = MCSP.truthTable _ (value c) := by
  let c : CodeFor r (r + (s + 1)) := (fun j => .inl (e (Fin.castAdd (s + 1) j)), f)
  refine ⟨c, ?_⟩
  funext i
  obtain ⟨z, rfl⟩ := (BitString.equivFin (r + (s + 1))).surjective i
  change probe s f (tablePerm e (BitString.equivFin _ z)) = MCSP.truthTable _ (value c) (BitString.equivFin _ z)
  rw [tablePerm_at_assignment, probe, MCSP.truthTable_apply, MCSP.truthTable_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-- Moving all represented coordinates moves the prefix as well. For any
selector that separates the tests for exact MCSP, the control agrees on all
four-flip tests after any such permutation. -/
theorem control_passes_all_prefixes {s : ℕ} (hm : 32 ≤ 9 + (s + 1)) (h : BooleanFunction s)
    (good : ∀ (f g : BooleanFunction 9) (D : Finset (Fin (2 ^ (9 + (s + 1))))), D.card ≤ 4 →
      (mcspSquare (9 + (s + 1)) (patch D (splice (mask 9 h) (probe s f) (probe s g))) = true ↔ f = g))
    (e : Equiv.Perm (Fin (9 + (s + 1)))) (f g : BooleanFunction 9)
    (D : Finset (Fin (2 ^ (9 + (s + 1))))) (hD : D.card ≤ 4) :
    control (9 + (s + 1)) (patch D (splice (mask 9 h) (probe s f) (probe s g) ∘ tablePerm e)) = true ↔ f = g := by
  constructor
  · intro hc
    have ha := control_implies_exact hm hc
    rw [patched_transport, square_comp_tablePerm] at ha
    exact (good f g _ (by simpa using hD)).mp ha
  · intro he
    rw [he, splice_self]
    obtain ⟨c, hc⟩ := prefix_code_after_perm g e
    exact (control_iff _).mpr ⟨c, D, hD, congrArg (patch D) hc⟩

theorem control_passes_all_prefixes_32 (h : PatchedCut.Selector) (hh : PatchedCut.Tests (mcspSquare 32) h)
    (e : Equiv.Perm (Fin 32)) (f g : PatchedCut.Prefix) (D : Finset PatchedCut.Address) (hD : D.card ≤ 4) :
    control 32 (patch D (PatchedCut.mixed h f g ∘ tablePerm e)) = true ↔ f = g :=
  control_passes_all_prefixes (s := 22) (by decide) h hh e f g D hD

end Tests

#print axioms control_implies_exact
#print axioms control_sparse
#print axioms control_passes_all_prefixes_32


section LinearBudget

private theorem shifted_power (x r : ℕ) (hx : 1 ≤ x) :
    x * (x + 1) ^ r ≤ (x + (2 ^ r - 1)) * x ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    let d := (2 : ℕ) ^ r - 1
    have hd : (2 : ℕ) ^ (r + 1) - 1 = 2 * d + 1 := by
      rw [pow_succ']
      have hp := Nat.two_pow_pos r
      dsimp [d]
      omega
    have hM : (x + d) * (x + 1) ≤ (x + (2 * d + 1)) * x := by
      have he : d ≤ d * x := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hx
      nlinarith
    calc
      _ = (x * (x + 1) ^ r) * (x + 1) := by rw [pow_succ]; ring
      _ ≤ ((x + d) * x ^ r) * (x + 1) := Nat.mul_le_mul_right _ ih
      _ = ((x + d) * (x + 1)) * x ^ r := by ring
      _ ≤ ((x + (2 * d + 1)) * x) * x ^ r := Nat.mul_le_mul_right _ hM
      _ = _ := by rw [hd, pow_succ]; ring

private theorem layerFor_growth (r m : ℕ) (hm : 2 ^ (r + 1) ≤ m) :
    2 * layerFor r (m + 1) ≤ 3 * layerFor r m := by
  let x := m + 2
  have hx : 1 ≤ x := by dsimp [x]; omega
  have h := shifted_power x r hx
  have hAux : 2 * (x + (2 ^ r - 1)) ≤ 3 * x := by
    rw [pow_succ'] at hm
    dsimp [x]
    omega
  have hScaled : x * (2 * (x + 1) ^ r) ≤ x * (3 * x ^ r) := calc
    _ = 2 * (x * (x + 1) ^ r) := by ring
    _ ≤ 2 * ((x + (2 ^ r - 1)) * x ^ r) := Nat.mul_le_mul_left 2 h
    _ = (2 * (x + (2 ^ r - 1))) * x ^ r := by ring
    _ ≤ (3 * x) * x ^ r := Nat.mul_le_mul_right _ hAux
    _ = _ := by ring
  have hP := (Nat.mul_le_mul_left_iff (show 0 < x from hx)).mp hScaled
  calc
    _ = (55 * 2 ^ 2 ^ r) * (2 * (x + 1) ^ r) := by dsimp only [layerFor, x]; ring
    _ ≤ (55 * 2 ^ 2 ^ r) * (3 * x ^ r) := Nat.mul_le_mul_left _ hP
    _ = _ := by dsimp only [layerFor, x]; ring

private theorem budgetFor_linear_with_margin (r : ℕ) :
    ∃ C : ℕ, ∀ m, budgetFor r m + 3 * layerFor r m ≤ C * 2 ^ m := by
  let L := 2 ^ (r + 1)
  let C := ∑ j ∈ Finset.range (L + 1), (budgetFor r j + 3 * layerFor r j)
  have hSmall (m : ℕ) (hm : m ≤ L) : budgetFor r m + 3 * layerFor r m ≤ C * 2 ^ m := by
    have h : budgetFor r m + 3 * layerFor r m ≤ C :=
      Finset.single_le_sum (f := fun j => budgetFor r j + 3 * layerFor r j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega : m < L + 1))
    exact h.trans (by
      have hp : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hp)
  refine ⟨C, ?_⟩
  intro m
  induction m with
  | zero => exact hSmall 0 (Nat.zero_le _)
  | succ m ih =>
    by_cases hs : m + 1 ≤ L
    · exact hSmall _ hs
    have hl := layerFor_growth r m (show L ≤ m by omega)
    calc
      _ ≤ 2 * (budgetFor r m + 3 * layerFor r m) := by rw [budgetFor]; omega
      _ ≤ 2 * (C * 2 ^ m) := Nat.mul_le_mul_left 2 ih
      _ = _ := by rw [pow_succ']; ring

/-- For each fixed width the bound is uniform in the arity and prefix locations. -/
theorem controlFor_linear (r : ℕ) : ∃ C : ℕ, ∀ m,
    complexity interpretation (single (controlFor r m)) ≤ C * 2 ^ m := by
  obtain ⟨C, hC⟩ := budgetFor_linear_with_margin r
  refine ⟨C + 1, fun m => (controlFor_size r m).trans ?_⟩
  have hm := hC m
  have hcap : (m + 2) ^ r * 2 ^ 2 ^ r ≤ 3 * layerFor r m := by
    unfold layerFor
    omega
  have hp := Nat.two_pow_pos m
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem control_linear : ∃ C : ℕ, ∀ m,
    complexity interpretation (single (control m)) ≤ C * 2 ^ m := controlFor_linear 9

end LinearBudget

#print axioms control_linear
#print axioms controlFor_linear
section BeyondNine

def andTen {s : ℕ} (z : BitString (10 + s)) : Bool :=
  decide (∀ i : Fin 10, z (Fin.castAdd s i) = true)

theorem andTen_cost {s : ℕ} :
    complexity interpretation (single (andTen (s := s))) ≤ 11 := by
  have hS := Synthesis.forall_mem (s := inputs (10 + s)) (Finset.univ : Finset (Fin 10))
    (fun i (z : BitString (10 + s)) => z (Fin.castAdd s i)) (fun _ => 0)
    (fun i _ => Synthesis.of_mem ⟨Fin.castAdd s i, rfl⟩)
  have he := Synthesis.congr_iff hS (g := andTen (s := s)) fun z => by simp [andTen]
  simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] using he.complexity_le

/-- On these disjoint pairs a nine-slot code has a constant value but the
ten-way conjunction changes. Account for both the noise patch and the
four positions allowed by the control. -/
theorem andTen_patch_rejected {s : ℕ} (P : Finset (Fin (2 ^ (10 + s)))) (room : P.card + 5 ≤ 2 ^ s) :
    control (10 + s) (patch P (MCSP.truthTable _ (andTen (s := s)))) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  obtain ⟨c, D, hD, he⟩ := (control_iff _).mp h
  let S := Finset.univ.image c.1
  let mark (i : Fin 10) : Fin (10 + s) ⊕ Bool := .inl (Fin.castAdd s i)
  have hMark : Function.Injective mark := by
    intro i j hij
    have he : (Sum.inl (Fin.castAdd s i) : Fin (10 + s) ⊕ Bool) = .inl (Fin.castAdd s j) := hij
    exact Fin.ext (congrArg (fun k : Fin (10 + s) => k.val) (Sum.inl.inj he))
  have hSmall : S.card ≤ 9 := Finset.card_image_le.trans (by simp)
  obtain ⟨j, hj⟩ : ∃ j, mark j ∉ S := by
    by_contra! hg
    have h10 := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin 10))) mark
      (fun i _ => hg i) hMark.injOn
    rw [Finset.card_univ, Fintype.card_fin] at h10
    omega
  let E := P ∪ D
  have hE : E.card ≤ P.card + D.card := Finset.card_union_le _ _
  let tail (k : Fin (P.card + 5)) : BitString s := (BitString.equivFin s).symm (k.castLE room)
  let z (k : Fin (P.card + 5)) (b : Bool) : BitString (10 + s) :=
    Fin.append (fun i : Fin 10 => if i = j then b else true) (tail k)
  let idx (k : Fin (P.card + 5)) (b : Bool) := BitString.equivFin (10 + s) (z k b)
  have hAnd (k : Fin (P.card + 5)) (b : Bool) : andTen (z k b) = b := by
    cases b
    · apply decide_eq_false
      intro h
      have hR := h j
      simp [z] at hR
    · apply decide_eq_true
      intro i
      simp [z]
  have hValue (k : Fin (P.card + 5)) : value c (z k false) = value c (z k true) := by
    unfold value
    apply congrArg c.2
    funext t
    cases h : c.1 t with
    | inr b => rfl
    | inl p =>
      simp only [Sum.elim_inl]
      revert h
      refine Fin.addCases (fun i => ?_) (fun i => ?_) p
      · intro h
        have hi : i ≠ j := by
          intro hh
          subst i
          exact hj (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, h⟩)
        simp [z, hi]
      · intro _
        simp [z]
  have hTouch (k : Fin (P.card + 5)) : idx k false ∈ E ∨ idx k true ∈ E := by
    by_contra! hBoth
    have hUnpatch (b : Bool) (hb : idx k b ∉ E) : b = value c (z k b) := by
      have hp0 : idx k b ∉ P := fun h => hb (Finset.mem_union_left _ h)
      have hd0 : idx k b ∉ D := fun h => hb (Finset.mem_union_right _ h)
      have hp := congrFun he (idx k b)
      simp only [patch, hp0, hd0, decide_false, Bool.xor_false, idx, MCSP.truthTable_apply,
        Equiv.symm_apply_apply, hAnd] at hp
      exact hp
    have h0 := hUnpatch false hBoth.1
    have h1 := hUnpatch true hBoth.2
    rw [hValue k, ← h1] at h0
    cases h0
  let choose (k : Fin (P.card + 5)) := if idx k false ∈ E then idx k false else idx k true
  have hinj (k l : Fin (P.card + 5)) {b b' : Bool} (h : idx k b = idx l b') : k = l := by
    have hz : z k b = z l b' := (BitString.equivFin (10 + s)).injective h
    have hTail := congrArg (fun p : BitString (10 + s) => (p ∘ Fin.natAdd 10)) hz
    have ht : tail k = tail l := by simpa only [z, Fin.append_comp_natAdd] using hTail
    exact Fin.ext (congrArg (fun i : Fin (2 ^ s) => i.val) ((BitString.equivFin s).symm.injective ht))
  have hCard : P.card + 5 ≤ E.card := by
    have hle := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (P.card + 5)))) (t := E) choose
      (fun k _ => by
        by_cases hk : idx k false ∈ E
        · simp [choose, hk]
        · simpa [choose, hk] using (hTouch k).resolve_left hk)
      (fun k _ l _ he => by
        dsimp only [choose] at he
        split_ifs at he <;> exact hinj k l he)
    rwa [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- Ten-way conjunction is an exact YES instance and already separates the
control that handles every choice of nine prefix coordinates. -/
theorem andTen_separates {s : ℕ} (hs : 3 ≤ s) :
    mcspSquare (10 + s) (MCSP.truthTable _ (andTen (s := s))) = true ∧
      control (10 + s) (MCSP.truthTable _ (andTen (s := s))) = false := by
  constructor
  · rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
    exact andTen_cost.trans (by nlinarith)
  · have room : (∅ : Finset (Fin (2 ^ (10 + s)))).card + 5 ≤ 2 ^ s := by
      have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hs
      simp only [Finset.card_empty, Nat.zero_add]
      omega
    have h := andTen_patch_rejected ∅ room
    have hEmpty : patch ∅ (MCSP.truthTable _ (andTen (s := s))) = MCSP.truthTable _ (andTen (s := s)) := by
      funext i
      simp [patch]
    rwa [hEmpty] at h

end BeyondNine

#print axioms andTen_separates
#print axioms andTen_patch_rejected

end PvsNP.Frontier.JuntaRadius
