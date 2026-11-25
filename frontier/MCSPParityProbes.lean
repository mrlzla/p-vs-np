module

public import MCSPLogPrefixControl
public import Complexity.Computability.Circuit.Boolean.Parity

/-! Add high decision-depth parity probes to the logarithmic-width tests.
Taking a parity translate of the existing control handles the new diagonals. -/

@[expose] public section

namespace PvsNP.Frontier.ParityProbes

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open SuperTwoN CornerCertificates CommunicationCut PermutedCut PatchedCut
open scoped Classical

def parityTable (m : ℕ) : BitString (2 ^ m) := MCSP.truthTable m (parity m)

def translate {n : ℕ} (P T : BitString n) : BitString n := fun i => T i ^^ P i

def twist {m : ℕ} (T : BitString (2 ^ m)) : BitString (2 ^ m) := translate (parityTable m) T

theorem twist_involutive (m : ℕ) : Function.Involutive (twist (m := m)) := by
  intro T
  funext i
  have h (a b : Bool) : ((a ^^ b) ^^ b) = a := by cases a <;> cases b <;> decide
  exact h _ _

theorem twist_patch {m : ℕ} (D : Finset (Fin (2 ^ m))) (T : BitString (2 ^ m)) :
    twist (patch D T) = patch D (twist T) := by
  funext i
  have h (a b c : Bool) : ((a ^^ b) ^^ c) = ((a ^^ c) ^^ b) := by
    cases a <;> cases b <;> cases c <;> decide
  exact h _ _ _

theorem twist_table {m : ℕ} (f : BooleanFunction m) :
    twist (MCSP.truthTable m f) = MCSP.truthTable m (fun z => f z ^^ parity m z) := by
  funext i
  obtain ⟨z,rfl⟩ := (BitString.equivFin m).surjective i
  change ((MCSP.truthTable m f) (BitString.equivFin m z) ^^
    (MCSP.truthTable m (parity m)) (BitString.equivFin m z)) = _
  simp only [MCSP.truthTable_apply, Equiv.symm_apply_apply]

theorem parity_perm {m : ℕ} (e : Equiv.Perm (Fin m)) (z : BitString m) :
    parity m (z ∘ e) = parity m z := by
  simp only [parity, parityOn_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp e z

theorem parityTable_perm {m : ℕ} (e : Equiv.Perm (Fin m)) :
    parityTable m ∘ tablePerm e = parityTable m := by
  funext i
  obtain ⟨z,rfl⟩ := (BitString.equivFin m).surjective i
  change (MCSP.truthTable m (parity m)) (tablePerm e (BitString.equivFin m z)) =
    (MCSP.truthTable m (parity m)) (BitString.equivFin m z)
  rw [tablePerm_at_assignment, MCSP.truthTable_apply, MCSP.truthTable_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, parity_perm]

theorem twist_perm {m : ℕ} (e : Equiv.Perm (Fin m)) (T : BitString (2 ^ m)) :
    twist (T ∘ tablePerm e) = twist T ∘ tablePerm e := by
  funext i
  exact congrArg (fun b : Bool => T (tablePerm e i) ^^ b) (congrFun (parityTable_perm e).symm i)

private theorem parity_cost {m : ℕ} (hm : 0 < m) :
    complexity interpretation (single (parity m)) ≤ 4 * m := by
  cases m with
  | zero => omega
  | succ m => exact (Boolean.complexity_parity_le m).trans (by omega)

theorem patched_parity_accepted {m : ℕ} (hm : 32 ≤ m) (D : Finset (Fin (2 ^ m))) (hD : D.card ≤ 4) :
    mcspSquare m (patch D (parityTable m)) = true := by
  apply JuntaRadius.patched_function_of_budget (parity m) D hD (parity_cost (by omega))
  have h := Nat.mul_le_mul_right m hm
  rw [← pow_two] at h
  omega

theorem reinput_size {n : ℕ} (F : BooleanFunction n) (P : BitString n) :
    complexity interpretation (single (fun T => F (translate P T))) ≤
      complexity interpretation (single F) + n := by
  let wires (i : Fin n) (T : BitString n) := T i ^^ P i
  have hOne (i : Fin n) : Synthesis interpretation (inputs n) {wires i} 1 := by
    have hi : Synthesis interpretation (inputs n) {fun T : BitString n => T i} 0 :=
      Synthesis.of_mem ⟨i,rfl⟩
    cases h : P i
    · have he : wires i = fun T => T i := by funext T; simp [wires,h]
      rw [he]
      exact hi.mono Set.Subset.rfl Set.Subset.rfl (by decide)
    · have he : wires i = fun T => !(T i) := by funext T; simp [wires,h]
      rw [he]
      exact hi.not
  have hw : Synthesis interpretation (inputs n) (Set.range wires) n := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.mul_one] using
      Synthesis.family wires (fun _ => 1) hOne
  obtain ⟨c, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single F)
  have hAt := Synthesis.circuit (I := interpretation) (s := inputs n ∪ Set.range wires) c wires
    (fun i => Or.inr ⟨i,rfl⟩)
  have hOneOut : Synthesis interpretation (inputs n ∪ Set.range wires) {fun T => F (translate P T)} c.size := by
    apply hAt.mono Set.Subset.rfl ?_ le_rfl
    rintro g rfl
    exact ⟨0, funext fun T => congrFun (hc (translate P T)) 0⟩
  have h := (hw.trans hOneOut).complexity_le
  rw [hs] at h
  exact h.trans_eq (Nat.add_comm ..)

noncomputable def control (r m : ℕ) (hm : r+4 ≤ m) (T : BitString (2^m)) : Bool :=
  LogPrefixControl.control r m hm T || LogPrefixControl.control r m hm (twist T)

theorem control_size {r m : ℕ} (hm : r+4 ≤ m) :
    complexity interpretation (single (control r m hm)) ≤
      2 * complexity interpretation (single (LogPrefixControl.control r m hm)) + 2^m + 1 := by
  let F := LogPrefixControl.control r m hm
  have h := complexity_or_le F (fun T => F (twist T))
  have h0 := reinput_size F (parityTable m)
  change complexity interpretation (single (fun T => F (twist T))) ≤
    complexity interpretation (single F) + 2^m at h0
  change complexity interpretation (single (fun T => F T || F (twist T))) ≤
    2 * complexity interpretation (single F) + 2^m + 1
  exact h.trans (calc
    _ ≤ complexity interpretation (single F) + (complexity interpretation (single F) + 2^m) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left h0 _) 1
    _ = _ := by omega)

theorem control_exact {r m : ℕ} (hm : r+4 ≤ m) (hr : 10 ≤ r) (h2 : 2^r ≤ m)
    {T : BitString (2^m)} (h : control r m hm T = true) : mcspSquare m T = true := by
  rw [control, Bool.or_eq_true] at h
  rcases h with h | h
  · exact LogPrefixControl.control_exact hm hr h2 h
  · obtain ⟨t, ht, D, hD, he⟩ := LogPrefixControl.control_witness hm h
    have hUn := congrArg (twist (m := m)) he
    rw [twist_involutive, twist_patch, twist_table] at hUn
    have hTree := OrderedTree.Tree.cost t
    have hPow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ht
    have hp := parity_cost (by omega : 0 < m)
    have hCost : complexity interpretation (single (fun z => t.eval z ^^ parity m z)) ≤
        5*2^r+4*m+4 := by
      exact (complexity_xor_le t.eval (parity m)).trans (by omega)
    have hmB : 1024 ≤ m := (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hr).trans h2
    have hBig := Nat.mul_le_mul_right m (by omega : 15 ≤ m)
    rw [← pow_two] at hBig
    rw [hUn]
    exact JuntaRadius.patched_function_of_budget _ D hD hCost (by omega)

theorem control_sparse {r m : ℕ} (hm : r+4 ≤ m) (hr : 10 ≤ r) (h2 : 2^r ≤ m) :
    (acceptingTables (control r m hm)).card ≤ 2 ^ descriptionBitBound m := by
  apply le_trans _ (card_accepting_mcspSquare_le m)
  apply Finset.card_le_card
  intro T ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, control_exact hm hr h2 (Finset.mem_filter.mp ht).2⟩

#print axioms patched_parity_accepted
#print axioms control_sparse
#print axioms control_size


section Depth

private noncomputable def queries {m : ℕ} (x : BitString m) : OrderedTree.Tree m → Finset (Fin m)
  | .leaf _ => ∅
  | .node i L R => insert i (if x i then queries x R else queries x L)

private theorem queries_card {m : ℕ} (x : BitString m) (t : OrderedTree.Tree m) :
    (queries x t).card ≤ t.depth := by
  induction t with
  | leaf b => simp [queries, OrderedTree.Tree.depth]
  | node i L R hl hr =>
    unfold queries
    rw [OrderedTree.Tree.depth]
    cases hi : x i
    · simp only [Bool.false_eq_true, ite_false]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (hl.trans (le_max_left ..)))
    · simp only [ite_true]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ (hr.trans (le_max_right ..)))

private theorem eval_agree_on_queries {m : ℕ} (x y : BitString m) (t : OrderedTree.Tree m)
    (h : ∀ j ∈ queries x t, x j = y j) : t.eval x = t.eval y := by
  induction t with
  | leaf b => rfl
  | node i L R hl hr =>
    have hi := h i (by simp [queries])
    unfold OrderedTree.Tree.eval
    rw [← hi]
    cases hb : x i
    · simp only [Bool.false_eq_true, ite_false]
      exact hl (fun j hj => h j (by simp [queries,hb,hj]))
    · simp only [ite_true]
      exact hr (fun j hj => h j (by simp [queries,hb,hj]))

noncomputable def toggle {m : ℕ} (i : Fin m) (x : BitString m) : BitString m :=
  Function.update x i (!(x i))

private theorem toggle_twice {m : ℕ} (i : Fin m) (x : BitString m) : toggle i (toggle i x) = x := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [toggle]
  · simp [toggle, Function.update_of_ne hj]

private theorem wide_enough (m : ℕ) (hm : 10 ≤ m) : 8 * (m+1) < 2^m := by
  refine Nat.le_induction (m := 10) (P := fun n _ => 8 * (n + 1) < 2^n) (by decide) ?_ m hm
  intro n _ ih
  rw [pow_succ' 2 n]
  omega

/-- It suffices to have many clean candidate centers with the specified
sensitive coordinates, even if other inputs are insensitive. -/
theorem sensitive_patch_separate_tree_on {m : ℕ} (f : BooleanFunction m)
    (V : Finset (Fin m)) (C : Finset (BitString m)) (hC : 8 * (m+1) < C.card)
    (hFlip : ∀ i ∈ V, ∀ x ∈ C, f (toggle i x) = !(f x))
    (t : OrderedTree.Tree m) (ht : t.depth < V.card)
    (D E : Finset (Fin (2^m))) (hD : D.card ≤ 4) (hE : E.card ≤ 4) :
    patch D (MCSP.truthTable m f) ≠ patch E (MCSP.truthTable m t.eval) := by
  intro he
  let R := (D ∪ E).map (BitString.equivFin m).symm.toEmbedding
  let near (z : BitString m) := (Finset.univ : Finset (Fin m)).image (fun i => toggle i z)
  let bad := R ∪ R.biUnion near
  have hR : R.card ≤ 8 := by
    unfold R
    rw [Finset.card_map]
    exact (Finset.card_union_le D E).trans (by omega)
  have hNear (z : BitString m) : (near z).card ≤ m :=
    (Finset.card_image_le).trans_eq (by rw [Finset.card_univ, Fintype.card_fin])
  have hBad : bad.card ≤ 8 * (m+1) := calc
    _ ≤ R.card + (R.biUnion near).card := Finset.card_union_le _ _
    _ ≤ R.card + ∑ z ∈ R, (near z).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ R.card + ∑ _z ∈ R, m := Nat.add_le_add_left (Finset.sum_le_sum (fun z _ => hNear z)) _
    _ = R.card * (m+1) := by simp only [Finset.sum_const, smul_eq_mul]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ hR
  obtain ⟨x, hxC, hx⟩ : ∃ x ∈ C, x ∉ bad := by
    by_contra! hx
    exact (not_le_of_gt hC) ((Finset.card_le_card hx).trans hBad)
  have hxR : x ∉ R := fun h => hx (Finset.mem_union_left _ h)
  have hOutside (i : Fin m) : toggle i x ∉ R := by
    intro hi
    apply hx
    apply Finset.mem_union_right _
    exact Finset.mem_biUnion.mpr ⟨toggle i x, hi, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, toggle_twice i x⟩⟩
  have hValue (z : BitString m) (hz : z ∉ R) : f z = t.eval z := by
    let i := BitString.equivFin m z
    have hi : i ∉ D ∪ E := by
      intro h
      apply hz
      exact Finset.mem_map.mpr ⟨i,h,(BitString.equivFin m).symm_apply_apply z⟩
    have hd : i ∉ D := fun h => hi (Finset.mem_union_left _ h)
    have hE' : i ∉ E := fun h => hi (Finset.mem_union_right _ h)
    have h := congrFun he i
    simp only [patch, hd, hE', decide_false, Bool.xor_false, i,
      MCSP.truthTable_apply, Equiv.symm_apply_apply] at h
    exact h
  obtain ⟨i, hiV, hi⟩ : ∃ i ∈ V, i ∉ queries x t := by
    by_contra! ha
    have h := (Finset.card_le_card ha).trans (queries_card x t)
    omega
  have hFix : t.eval x = t.eval (toggle i x) := eval_agree_on_queries _ _ _ (by
    intro j hj
    have hn : j ≠ i := fun he => hi (he ▸ hj)
    simp [toggle, Function.update_of_ne hn])
  rw [← hValue x hxR, ← hValue (toggle i x) (hOutside i)] at hFix
  rw [hFlip i hiV x hxC] at hFix
  generalize f x = b at hFix
  cases b <;> contradiction

private theorem sensitive_patch_separate_tree {m : ℕ} (hm : 10 ≤ m) (f : BooleanFunction m)
    (V : Finset (Fin m)) (hFlip : ∀ i ∈ V, ∀ x, f (toggle i x) = !(f x))
    (t : OrderedTree.Tree m) (ht : t.depth < V.card)
    (D E : Finset (Fin (2^m))) (hD : D.card ≤ 4) (hE : E.card ≤ 4) :
    patch D (MCSP.truthTable m f) ≠ patch E (MCSP.truthTable m t.eval) := by
  have hC : 8 * (m+1) < (Finset.univ : Finset (BitString m)).card := by
    simpa only [Finset.card_univ, BitString.card] using wide_enough m hm
  exact sensitive_patch_separate_tree_on f V Finset.univ hC
    (fun i hi x _ => hFlip i hi x) t ht D E hD hE

/-- Two four-point patches cannot make parity agree with a decision tree of
depth below m. A point outside the error neighborhoods preserves its sensitivity. -/
theorem parity_patch_separate_tree {m : ℕ} (hm : 10 ≤ m) (t : OrderedTree.Tree m) (ht : t.depth < m)
    (D E : Finset (Fin (2^m))) (hD : D.card ≤ 4) (hE : E.card ≤ 4) :
    patch D (parityTable m) ≠ patch E (MCSP.truthTable m t.eval) :=
  sensitive_patch_separate_tree hm (parity m) Finset.univ
    (fun i _ x => parity_update_not x i) t (by simpa using ht) D E hD hE

theorem patched_parity_depth {m : ℕ} (hm : 10 ≤ m) (D : Finset (Fin (2^m))) (hD : D.card ≤ 4) :
    (OrderedTree.canonical m (JuntaRadius.viewed m (patch D (parityTable m)))).depth = m := by
  let X := patch D (parityTable m)
  let t := OrderedTree.canonical m (JuntaRadius.viewed m X)
  change t.depth = m
  apply le_antisymm (OrderedTree.canonical_depth_le_arity _)
  by_contra! ht
  have he : MCSP.truthTable m t.eval = X := by
    change MCSP.truthTable m (OrderedTree.canonical m (JuntaRadius.viewed m X)).eval = X
    rw [OrderedTree.canonical_eval, JuntaRadius.viewed, Equiv.apply_symm_apply]
  have hEmpty : patch ∅ (MCSP.truthTable m t.eval) = X := by
    rw [← he]
    funext i
    simp [patch]
  exact parity_patch_separate_tree hm t ht D ∅ hD (by simp) hEmpty.symm

theorem old_control_rejects_parity {r m : ℕ} (hm : r+4 ≤ m) (hm' : 10 ≤ m)
    (D : Finset (Fin (2^m))) (hD : D.card ≤ 4) :
    LogPrefixControl.control r m hm (patch D (parityTable m)) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨t, htr, E, hE, he⟩ := LogPrefixControl.control_witness hm ht
  exact parity_patch_separate_tree hm' t (by omega) D E hD hE he

end Depth

#print axioms parity_patch_separate_tree
#print axioms patched_parity_depth
#print axioms old_control_rejects_parity


section Tagged

abbrev Tagged (r : ℕ) := Bool × BooleanFunction r

/-- The phase bit specifies whether to add parity on every represented variable. -/
def taggedProbe {r s : ℕ} (u : Tagged r) : BitString (2 ^ (r + (s+1))) :=
  if u.1 then twist (probe s u.2) else probe s u.2

def repeatedSelector {s : ℕ} (h : BooleanFunction s) : BooleanFunction (s+1) :=
  h ∘ Fin.tail

/-- The selector ignores one suffix coordinate. That coordinate supplies both
parity values while the selector bit stays fixed. -/
def taggedMixed {r s : ℕ} (h : BooleanFunction s) (u v : Tagged r) :
    BitString (2 ^ (r + ((s+1)+1))) :=
  splice (mask r (repeatedSelector h)) (taggedProbe u) (taggedProbe v)

def TaggedTests {r s : ℕ} (h : BooleanFunction s) : Prop :=
  ∀ u v : Tagged r, ∀ D : Finset (Fin (2 ^ (r + ((s+1)+1)))), D.card ≤ 4 →
    (mcspSquare (r + ((s+1)+1)) (patch D (taggedMixed h u v)) = true ↔ u = v)

private theorem parity_cons {s : ℕ} (b : Bool) (t : BitString s) :
    parity (s+1) (Fin.cons b t) = (b ^^ parity s t) := by
  simp only [parity, parityOn_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.add_eq_xor]

private theorem parity_append {r s : ℕ} (a : BitString r) (t : BitString s) :
    parity (r+s) (Fin.append a t) = (parity r a ^^ parity s t) := by
  simp only [parity, parityOn_eq_sum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Bool.add_eq_xor]

private theorem parity_at {r s : ℕ} (a : BitString r) (b : Bool) (t : BitString s) :
    parityTable (r+(s+1)) (position a b t) = (parity r a ^^ (b ^^ parity s t)) := by
  unfold parityTable position
  rw [MCSP.truthTable_apply, Equiv.symm_apply_apply, parity_append, parity_cons]

private theorem tagged_at {r s : ℕ} (u : Tagged r) (a : BitString r) (b : Bool) (t : BitString s) :
    taggedProbe u (position a b t) = (u.2 a ^^ (u.1 && parityTable (r+(s+1)) (position a b t))) := by
  cases h : u.1 <;> simp [taggedProbe, h, twist, translate]

private theorem parity_pair_ne {r s : ℕ} (a : BitString r) (t : BitString s) :
    parityTable (r+((s+1)+1)) (position a false (Fin.cons false t)) ≠
      parityTable (r+((s+1)+1)) (position a false (Fin.cons true t)) := by
  rw [parity_at, parity_at, parity_cons, parity_cons]
  generalize parity r a = p
  generalize parity s t = q
  cases p <;> cases q <;> decide

private theorem xor_same_ne (a b c : Bool) (h : a ≠ b) : (a ^^ c) ≠ (b ^^ c) := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem phase_disagrees_somewhere (x y p q a b : Bool) (hp : p ≠ q) (hab : a ≠ b) :
    (x ^^ (a && p)) ≠ (y ^^ (b && p)) ∨
      (x ^^ (a && q)) ≠ (y ^^ (b && q)) := by
  cases x <;> cases y <;> cases p <;> cases q <;> cases a <;> cases b <;> simp_all

/-- Unequal tags can recover every free selector bit from one of the two
suffix rows selected to disagree. -/
theorem tagged_mixed_injective {r s : ℕ} {u v : Tagged r} (huv : u ≠ v) :
    Function.Injective (fun h : BooleanFunction s => taggedMixed h u v) := by
  intro h g he
  funext t
  have read (a : BitString r) (b : Bool)
      (hne : taggedProbe u (position a false (Fin.cons b t)) ≠
        taggedProbe v (position a false (Fin.cons b t))) : h t = g t := by
    have hc := congrFun he (position a false (Fin.cons b t))
    simp only [taggedMixed, splice, mask_at_position, Bool.false_xor, repeatedSelector, Function.comp_apply,
      Fin.tail_cons] at hc
    cases h0 : h t <;> cases h1 : g t <;> simp_all
  by_cases hp : u.1 = v.1
  · have hf : u.2 ≠ v.2 := fun he => huv (Prod.ext hp he)
    obtain ⟨a,ha⟩ : ∃ a, u.2 a ≠ v.2 a := by
      by_contra! h
      exact hf (funext h)
    apply read a false
    rw [tagged_at, tagged_at, hp]
    exact xor_same_ne _ _ _ ha
  · let a : BitString r := fun _ => false
    rcases phase_disagrees_somewhere (u.2 a) (v.2 a) _ _ u.1 v.1 (parity_pair_ne a t) hp with h0 | h1
    · apply read a false
      simpa only [tagged_at] using h0
    · apply read a true
      simpa only [tagged_at] using h1

private theorem tagged_card (r : ℕ) : Fintype.card (Tagged r) = 2 ^ (2 ^ r + 1) := by
  have hc : Fintype.card (BooleanFunction r) = 2 ^ 2 ^ r := by classical simp
  rw [Fintype.card_prod, Fintype.card_bool, hc, pow_succ']

/-- All direct and parity-shifted prefix diagonals pass the new control,
including their transported truth tables and their four-point patches. -/
theorem control_passes_tag_diag {r s : ℕ}
    (hm : r+4 ≤ r+(s+1)) (e : Equiv.Perm (Fin (r+(s+1)))) (f : BooleanFunction r) (b : Bool)
    (D : Finset (Fin (2 ^ (r+(s+1))))) (hD : D.card ≤ 4) :
    control r (r+(s+1)) hm (patch D (taggedProbe (b,f) ∘ tablePerm e)) = true := by
  obtain ⟨c,hc⟩ := JuntaRadius.prefix_code_after_perm f e
  have hYes := LogPrefixControl.control_accepts hm c D hD
  rw [control, Bool.or_eq_true]
  cases b
  · left
    simpa only [taggedProbe, Prod.fst, Prod.snd, Bool.false_eq_true, ite_false, hc] using hYes
  · right
    change LogPrefixControl.control r (r+(s+1)) hm (twist (patch D (twist (probe s f) ∘ tablePerm e))) =
      true
    rw [← twist_perm, hc, twist_patch, twist_involutive]
    exact hYes

private theorem tagExponent_room {r s : ℕ} (hr : 10 ≤ r) (hs : 2^r ≤ s+1) :
    2 * (2^r+1) + (r+((s+1)+1)+1)*4 + descriptionBitBound (r+((s+1)+1)) < 2^s := by
  have hm : 1023 ≤ s := by
    have hPow := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans hs
    omega
  have h := GrowingPrefix.wide_exponent_le hr hs
  have hCub : (s+1)^3 ≤ (2*s)^3 := Nat.pow_le_pow_left (by omega) 3
  have hPoly : 100 * (s+1)^3 ≤ 800 * s^3 := calc
    _ ≤ 100 * (2*s)^3 := Nat.mul_le_mul_left 100 hCub
    _ = _ := by ring
  have hE : 2 * (2^r+1) + (r+((s+1)+1)+1)*4 + descriptionBitBound (r+((s+1)+1)) ≤ 800*s^3+2 := by
    unfold wideExponent at h
    omega
  have hPos : 1 ≤ s^3 := Nat.pow_pos (by omega : 0 < s)
  have hLt : 800*s^3+2 < s^4 := by
    have hC : 803*s^3 ≤ s^4 := by
      rw [pow_succ' s 3]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  exact hE.trans_lt (hLt.trans_le (GrowingPrefix.four_power_le_exp s (by omega)))

/-- A single selector handles plain and parity-tagged prefixes, including
unequal pairs with different parity tags. -/
theorem exists_tagged_selector (r s : ℕ) (hr : 10 ≤ r) (hs : 2^r ≤ s+1) :
    ∃ h : BooleanFunction s, TaggedTests (r := r) h := by
  let m := r+((s+1)+1)
  have h2 : 2^r ≤ m := by dsimp [m]; omega
  have hm : r+4 ≤ m := by
    have h := (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hr).trans hs
    dsimp [m]
    omega
  have room : 2 ^ ((2^r+1)+(2^r+1)+(m+1)*4+descriptionBitBound m) <
      Fintype.card (BooleanFunction s) := by
    have hc : Fintype.card (BooleanFunction s) = 2 ^ 2 ^ s := by classical simp
    rw [hc]
    apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
    have h := tagExponent_room hr hs
    dsimp [m]
    omega
  refine exists_family_selector (mcspSquare m) (taggedMixed (r := r) (s := s))
    (tagged_card r) (q := m) le_rfl (card_accepting_mcspSquare_le m) room ?_
    (fun h => tagged_mixed_injective h)
  intro h u D hD
  apply control_exact hm hr h2
  unfold taggedMixed
  rw [splice_self]
  have hId : tablePerm (Equiv.refl (Fin m)) = Equiv.refl (Fin (2^m)) := by
    ext i
    simp [tablePerm, permuteAssignment]
  have hAcc := control_passes_tag_diag hm (Equiv.refl (Fin m)) u.2 u.1 D hD
  rw [hId] at hAcc
  exact hAcc

theorem tagged_at_cut {r s : ℕ} {h : BooleanFunction s} (hh : TaggedTests (r := r) h)
    (e : Equiv.Perm (Fin (r+((s+1)+1)))) (u v : Tagged r)
    (D : Finset (Fin (2^(r+((s+1)+1))))) (hD : D.card ≤ 4) :
    mcspSquare (r+((s+1)+1)) (patch D (taggedMixed h u v ∘ tablePerm e)) = true ↔ u = v := by
  let p := tablePerm e
  have he : patch D (taggedMixed h u v ∘ p) = (patch (D.map p.toEmbedding) (taggedMixed h u v)) ∘ p := by
    funext i
    simp [patch, Function.comp_apply]
  rw [he, square_comp_tablePerm]
  exact hh u v _ (by simpa using hD)

theorem tagged_oneWay_width {r s w : ℕ} {h : BooleanFunction s} (hh : TaggedTests (r := r) h)
    (e : Equiv.Perm (Fin (r+((s+1)+1)))) (D : Finset (Fin (2^(r+((s+1)+1))))) (hD : D.card ≤ 4)
    (send : Tagged r → BitString w) (finish : BitString w → Tagged r → Bool)
    (factor : ∀ u v, finish (send u) v = mcspSquare (r+((s+1)+1)) (patch D (taggedMixed h u v ∘ tablePerm e))) :
    2^r+1 ≤ w := by
  have hinj : Function.Injective send := by
    intro u v he
    apply (tagged_at_cut hh e u v D hD).mp
    rw [← factor, he, factor]
    exact (tagged_at_cut hh e v v D hD).mpr rfl
  have h := Fintype.card_le_of_injective send hinj
  rw [tagged_card, BitString.card] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

theorem control_passes_tagged {r s : ℕ} (hm : r+4 ≤ r+((s+1)+1))
    (hr : 10 ≤ r) (h2 : 2^r ≤ r+((s+1)+1)) (h : BooleanFunction s) (hh : TaggedTests (r := r) h)
    (e : Equiv.Perm (Fin (r+((s+1)+1)))) (u v : Tagged r)
    (D : Finset (Fin (2^(r+((s+1)+1))))) (hD : D.card ≤ 4) :
    control r (r+((s+1)+1)) hm (patch D (taggedMixed h u v ∘ tablePerm e)) = true ↔ u = v := by
  constructor
  · intro hYes
    exact (tagged_at_cut hh e u v D hD).mp (control_exact hm hr h2 hYes)
  · rintro rfl
    unfold taggedMixed
    rw [splice_self]
    exact control_passes_tag_diag hm e u.2 u.1 D hD

/-- The shorter selector still realizes the same represented arity as the
previous explicit logarithmic-width schedule. -/
theorem tagged_log_stage (r : ℕ) (hr : 10 ≤ r) :
    ∃ s, s+1=2^r ∧ ∃ h : BooleanFunction s, TaggedTests (r := r) h := by
  let s := 2^r-1
  have hs : s+1=2^r := by dsimp [s]; have := Nat.two_pow_pos r; omega
  exact ⟨s,hs,exists_tagged_selector r s hr hs.ge⟩

/-- All parity-tagged prefixes defeat the old depth-r control. Every tail
coordinate is sensitive even when the prefix contents are arbitrary. -/
theorem old_control_rejects_tagged_prefix {r s : ℕ} (hm : r+4 ≤ r+(s+1)) (hm' : 10 ≤ r+(s+1))
    (hDepth : r < s+1) (f : BooleanFunction r) (D : Finset (Fin (2^(r+(s+1))))) (hD : D.card ≤ 4) :
    LogPrefixControl.control r (r+(s+1)) hm (patch D (taggedProbe (true,f))) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨t, htr, E, hE, he⟩ := LogPrefixControl.control_witness hm ht
  let m := r+(s+1)
  let q : BooleanFunction m := fun z => f (z ∘ Fin.castAdd (s+1)) ^^ parity m z
  let V := (Finset.univ : Finset (Fin (s+1))).image (Fin.natAdd r)
  have hV : V.card = s+1 := by
    have hi : Function.Injective (Fin.natAdd r : Fin (s+1) → Fin m) := by
      intro i j h
      have he := congrArg (fun k : Fin m => k.val) h
      exact Fin.ext (by change r + i.val = r + j.val at he; omega)
    simp only [V, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  have hFlip (i : Fin m) (hi : i ∈ V) (x : BitString m) : q (toggle i x) = !(q x) := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    have hFlat : toggle (Fin.natAdd r j) x ∘ Fin.castAdd (s+1) = x ∘ Fin.castAdd (s+1) := by
      funext k
      have hn : Fin.castAdd (s+1) k ≠ Fin.natAdd r j := by
        intro he
        have hh := congrArg (fun i : Fin m => i.val) he
        change k.val = r+j.val at hh
        have := k.isLt
        omega
      exact Function.update_of_ne hn _ _
    unfold q
    rw [hFlat, show parity m (toggle (Fin.natAdd r j) x) = !(parity m x) from parity_update_not ..]
    generalize f (x ∘ Fin.castAdd (s+1)) = a
    generalize parity m x = b
    cases a <;> cases b <;> decide
  have hTag : taggedProbe (s := s) (true,f) = MCSP.truthTable m q :=
    twist_table (fun x => f (x ∘ Fin.castAdd (s+1)))
  rw [hTag] at he
  exact sensitive_patch_separate_tree hm' q V hFlip t (by rw [hV]; omega) D E hD hE he

end Tagged

#print axioms exists_tagged_selector
#print axioms control_passes_tagged
#print axioms old_control_rejects_tagged_prefix
#print axioms tagged_log_stage
#print axioms tagged_oneWay_width


section Asymptotic

/-- The parity translate adds one shared input-negation layer and a second
copy of the old control, preserving its sub-N-log-N bound. -/
theorem parity_control_sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (control r (LogPrefixControl.arity r)
        (LogPrefixControl.arity_room r hr))) ≤ LogPrefixControl.arity r * 2 ^ LogPrefixControl.arity r := by
  have hBase := LogPrefixControl.sub_nlogn (4*K)
  filter_upwards [hBase, Filter.eventually_ge_atTop (4*K)] with r he hrK hr
  let m := LogPrefixControl.arity r
  let n := 2 ^ m
  let room := LogPrefixControl.arity_room r hr
  let base := complexity interpretation (single (LogPrefixControl.control r m room))
  let full := complexity interpretation (single (control r m room))
  have hOld : (4*K)*base ≤ m*n := he hr
  have hNew : full ≤ 2*base+n+1 := control_size room
  have hn : 1 ≤ n := Nat.two_pow_pos _
  have hk : 4*K ≤ r := hrK
  have hm : 4*K ≤ m := hk.trans (Nat.le_add_right r (2^r+1))
  have hMask : (2*K)*(n+1) ≤ m*n := calc
    _ ≤ (2*K)*(2*n) := Nat.mul_le_mul_left _ (by omega)
    _ = (4*K)*n := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hm
  have hc : 2*(K*full) ≤ 2*(m*n) := calc
    _ = (2*K)*full := by ring
    _ ≤ (2*K)*(2*base+n+1) := Nat.mul_le_mul_left _ hNew
    _ = (4*K)*base+(2*K)*(n+1) := by ring
    _ ≤ _ := by omega
  exact (Nat.mul_le_mul_left_iff (by decide : 0 < 2)).mp hc

end Asymptotic

#print axioms parity_control_sub_nlogn

end PvsNP.Frontier.ParityProbes
