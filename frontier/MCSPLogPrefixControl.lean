module

public import MCSPOrderedTree
public import Complexity.Foundations.Data.Nat.Asymptotics

/-! A control for the explicit logarithmic schedule. Guess four inactive
coordinates among the first r+4, correct by a sixteen-entry majority, and verify
both the decision depth and the distance of the recovered truth table. -/

@[expose] public section

namespace PvsNP.Frontier.LogPrefixControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates CommunicationCut SuperTwoN PermutedCut PatchedCut GrowingPrefix
open JuntaRadius (distance viewed CodeFor value)
open InvariantControl (weight)
open scoped Classical

def toggled {m : ℕ} (u : Fin 4 → Fin m) (q : Fin 16) (i : Fin m) : Prop :=
  ∃ j, u j = i ∧ (BitString.equivFin 4).symm q j = true

noncomputable def shift {m : ℕ} (u : Fin 4 → Fin m) (q : Fin 16) (z : BitString m) : BitString m :=
  fun i => z i ^^ decide (toggled u q i)

private theorem shift_inj {m : ℕ} {u : Fin 4 → Fin m} (hu : Function.Injective u) (z : BitString m) :
    Function.Injective (fun q : Fin 16 => shift u q z) := by
  intro p q he
  apply (BitString.equivFin 4).symm.injective
  funext j
  have ht (a : Fin 16) : toggled u a (u j) ↔ (BitString.equivFin 4).symm a j = true := by
    constructor
    · rintro ⟨k, hk, h⟩
      rwa [hu hk] at h
    · exact fun h => ⟨j,rfl,h⟩
  have h := congrFun he (u j)
  simp only [shift, ht, Bool.decide_coe] at h
  have hc (x a b : Bool) (w : (x ^^ a) = (x ^^ b)) : a = b := by
    cases x <;> cases a <;> cases b <;> simp_all
  exact hc _ _ _ h

noncomputable def recover {m : ℕ} (u : Fin 4 → Fin m) (T : BitString (2 ^ m)) : BooleanFunction m :=
  fun z => decide (9 ≤ weight (fun q : Fin 16 => T (BitString.equivFin m (shift u q z))))

private theorem recover_patched {m : ℕ} (F : BooleanFunction m) {u : Fin 4 → Fin m}
    (hu : Function.Injective u) (hShift : ∀ q z, F (shift u q z) = F z)
    (D : Finset (Fin (2 ^ m))) (hD : D.card ≤ 4) :
    recover u (patch D (MCSP.truthTable m F)) = F := by
  funext z
  let reads (q : Fin 16) := BitString.equivFin m (shift u q z)
  let hits := Finset.univ.filter (fun q : Fin 16 => reads q ∈ D)
  let ones := Finset.univ.filter (fun q : Fin 16 => patch D (MCSP.truthTable m F) (reads q) = true)
  have hHits : hits.card ≤ 4 := by
    have hInj : Function.Injective reads := (BitString.equivFin m).injective.comp (shift_inj hu z)
    apply le_trans _ hD
    exact Finset.card_le_card_of_injOn reads (fun _ h => (Finset.mem_filter.mp h).2) hInj.injOn
  have hClean (q : Fin 16) (hq : q ∉ hits) : patch D (MCSP.truthTable m F) (reads q) = F z := by
    have hn : reads q ∉ D := fun h => hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    rw [patch]
    simp only [hn, decide_false, Bool.xor_false, reads, MCSP.truthTable_apply, Equiv.symm_apply_apply]
    exact hShift q z
  change decide (9 ≤ ones.card) = F z
  cases he : F z with
  | false =>
    have hs : ones ⊆ hits := by
      intro q hq
      by_contra hn
      have hp := (Finset.mem_filter.mp hq).2
      rw [hClean q hn, he] at hp
      cases hp
    have hb := Finset.card_le_card hs
    exact decide_eq_false (by omega)
  | true =>
    have hs : (Finset.univ : Finset (Fin 16)) \ hits ⊆ ones := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hClean q (Finset.mem_sdiff.mp hq).2).trans he⟩
    have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ hits)
    rw [Finset.card_univ, Fintype.card_fin] at he
    have hb := Finset.card_le_card hs
    exact decide_eq_true (by omega)

private theorem unused_four {r m : ℕ} (hm : r + 4 ≤ m) (c : CodeFor r m) :
    ∃ u : Fin 4 ↪ Fin (r + 4), ∀ j k, c.1 j ≠ .inl (Fin.castLE hm (u k)) := by
  let used := (Finset.univ : Finset (Fin r)).image c.1
  let mark (i : Fin (r + 4)) : Fin m ⊕ Bool := .inl (Fin.castLE hm i)
  let bad := (Finset.univ : Finset (Fin (r + 4))).filter fun j => mark j ∈ used
  have hb : bad.card ≤ r := by
    have hu : used.card ≤ r := Finset.card_image_le.trans (by simp)
    apply le_trans _ hu
    apply Finset.card_le_card_of_injOn mark (fun _ h => (Finset.mem_filter.mp h).2)
    intro i _ j _ he
    apply Fin.ext
    exact congrArg (fun k : Fin m => k.val) (Sum.inl.inj he)
  let good := (Finset.univ : Finset (Fin (r + 4))) \ bad
  have hGood : 4 ≤ good.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
    rw [Finset.card_univ, Fintype.card_fin] at h
    change good.card + bad.card = r + 4 at h
    omega
  obtain ⟨S, hSub, hCard⟩ := Finset.exists_subset_card_eq hGood
  let e : Fin 4 ≃ S := (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans hCard)).symm
  refine ⟨e.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩
  intro j k h
  have h0 := (Finset.mem_sdiff.mp (hSub (e k).property)).2
  apply h0
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h⟩⟩

noncomputable def attempt {m : ℕ} (r : ℕ) (u : Fin 4 → Fin m) (T : BitString (2 ^ m)) : Bool :=
  decide ((OrderedTree.canonical m (recover u T)).depth ≤ r ∧ distance (viewed m T) (recover u T) ≤ 4)

noncomputable def control (r m : ℕ) (hm : r + 4 ≤ m) (T : BitString (2 ^ m)) : Bool :=
  decide (∃ u : Fin 4 → Fin (r + 4), attempt r (Fin.castLE hm ∘ u) T = true)

/-- A patched function passes whenever all its relevant variables occur in an r-slot code. -/
theorem control_accepts_on_code_support {r m : ℕ} (hm : r + 4 ≤ m) (c : CodeFor r m)
    (F : BooleanFunction m)
    (hf : ∀ x y, (∀ j i, c.1 j = .inl i → x i = y i) → F x = F y)
    (D : Finset (Fin (2 ^ m))) (hD : D.card ≤ 4) :
    control r m hm (patch D (MCSP.truthTable m F)) = true := by
  obtain ⟨u, hu⟩ := unused_four hm c
  have hCast : Function.Injective (Fin.castLE hm) := fun i j h =>
    Fin.ext (congrArg (fun i : Fin m => i.val) h)
  have hShift (q : Fin 16) (z : BitString m) : F (shift (Fin.castLE hm ∘ u) q z) = F z := by
    apply hf
    intro j i hj
    have hn : ¬toggled (Fin.castLE hm ∘ u) q i := by
      rintro ⟨k, hk, _⟩
      exact hu j k (hj.trans (congrArg Sum.inl hk.symm))
    simp [shift, hn]
  apply decide_eq_true
  refine ⟨u, ?_⟩
  unfold attempt
  rw [recover_patched F (hCast.comp u.injective) hShift D hD]
  exact decide_eq_true ⟨OrderedTree.depth_le_of_code_support c F hf,
    (JuntaRadius.patch_distance_le D F).trans hD⟩

/-- All four-flip patches of all r-slot codes pass, wherever their variables lie. -/
theorem control_accepts {r m : ℕ} (hm : r + 4 ≤ m) (c : CodeFor r m)
    (D : Finset (Fin (2 ^ m))) (hD : D.card ≤ 4) :
    control r m hm (patch D (MCSP.truthTable m (value c))) = true :=
  control_accepts_on_code_support hm c _ (OrderedTree.value_depends_on_code_support c) D hD

theorem control_witness {r m : ℕ} (hm : r + 4 ≤ m)
    {T : BitString (2 ^ m)} (h : control r m hm T = true) :
    ∃ t : OrderedTree.Tree m, t.depth ≤ r ∧ ∃ D : Finset (Fin (2 ^ m)),
      D.card ≤ 4 ∧ T = patch D (MCSP.truthTable m t.eval) := by
  obtain ⟨u, hu⟩ := of_decide_eq_true h
  obtain ⟨hDepth, hDist⟩ := of_decide_eq_true hu
  let F := recover (Fin.castLE hm ∘ u) T
  let D := (Finset.univ : Finset (Fin (2 ^ m))).filter (fun i => T i ≠ (MCSP.truthTable m F) i)
  have hP : T = patch D (MCSP.truthTable m F) := by
    funext i
    simp only [patch, D, Finset.mem_filter, Finset.mem_univ, true_and]
    have hb (x y : Bool) : x = (y ^^ decide (x ≠ y)) := by cases x <;> cases y <;> decide
    exact hb _ _
  have hd : D.card ≤ 4 := (JuntaRadius.distance_eq_raw T F).symm ▸ hDist
  exact ⟨OrderedTree.canonical m F, hDepth, D, hd, by rwa [OrderedTree.canonical_eval]⟩

theorem control_exact {r m : ℕ} (hm : r + 4 ≤ m) (hr : 10 ≤ r) (h2 : 2 ^ r ≤ m)
    {T : BitString (2 ^ m)} (h : control r m hm T = true) : mcspSquare m T = true := by
  obtain ⟨t, hDepth, D, hd, hP⟩ := control_witness hm h
  have he := OrderedTree.Tree.cost t
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDepth
  have hSize : complexity interpretation (single t.eval) ≤ 5 * 2 ^ r := by omega
  have hBudget : 5 * 2 ^ r + 5 * m + 13 ≤ m^2 := by
    have hm' : 1024 ≤ m := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans h2
    have hmul := Nat.mul_le_mul_right m (by omega : 11 ≤ m)
    rw [← pow_two] at hmul
    omega
  rw [hP]
  exact JuntaRadius.patched_function_of_budget t.eval D hd hSize hBudget

#print axioms control_accepts
#print axioms control_exact


section Size

def attemptBudget (r m : ℕ) : ℕ :=
  2228241 * 2 ^ m + OrderedTree.treeBudget r m + 4

theorem attempt_size {r m : ℕ} (u : Fin 4 → Fin m) :
    Synthesis interpretation (inputs (2 ^ m)) {attempt r u} (attemptBudget r m) := by
  let n := 2 ^ m
  let read (z : BitString m) (T : BitString n) := recover u T z
  have hOne (z : BitString m) : Synthesis interpretation (inputs n) {read z} 2228225 :=
    Synthesis.selected (fun q : Fin 16 => BitString.equivFin m (shift u q z))
      (fun x : BitString 16 => decide (9 ≤ weight x))
  have hRec : Synthesis interpretation (inputs n) (Set.range read) (n * 2228225) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card] using
      Synthesis.family read (fun _ => 2228225) hOne
  let A := inputs n ∪ Set.range read
  have hTree := OrderedTree.synth_states r A read (fun z => Or.inr ⟨z,rfl⟩)
  let B := A ∪ OrderedTree.states r read
  let q (i : Fin n) (T : BitString n) := T i ^^ (MCSP.truthTable m (recover u T)) i
  have hQ (i : Fin n) : Synthesis interpretation B {q i} 4 := by
    have hIn : (fun T : BitString n => T i) ∈ B := Or.inl (Or.inl ⟨i,rfl⟩)
    have hj : (fun T => (MCSP.truthTable m (recover u T)) i) ∈ B := by
      exact Or.inl (Or.inr ⟨(BitString.equivFin m).symm i,rfl⟩)
    exact (Synthesis.of_mem hIn).xor (Synthesis.of_mem hj)
  have hErr : Synthesis interpretation B (Set.range q) (n * 4) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] using
      Synthesis.family q (fun _ => 4) hQ
  let C := B ∪ Set.range q
  have hCount := RadiusControl.synth_counter C q (fun i => Or.inr ⟨i,rfl⟩)
  let S := C ∪ Set.range (RadiusControl.counterState q)
  let hd := OrderedTree.depthWire r read (Fin.last r)
  let ht := RadiusControl.counterState q 5
  have hD : hd ∈ S := Or.inl (Or.inl (Or.inr (Or.inl ⟨Fin.last r,rfl⟩)))
  have hT : ht ∈ S := Or.inr ⟨5,rfl⟩
  have hAns := (Synthesis.of_mem hD).and (Synthesis.of_mem hT).not
  have hEq : attempt r u = fun T => hd T && !(ht T) := by
    funext T
    have hw : weight (fun i => q i T) = distance (viewed m T) (recover u T) := by
      rw [JuntaRadius.distance_eq_raw]
      unfold weight
      congr 1
    change decide ((OrderedTree.canonical m (recover u T)).depth ≤ r ∧ distance (viewed m T) (recover u T) ≤ 4) =
      (decide ((OrderedTree.canonical m (recover u T)).depth ≤ r) && !(decide (5 ≤ weight (fun i => q i T))))
    rw [hw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    by_cases he : 5 ≤ distance (viewed m T) (recover u T) <;> simp [he] <;> omega
  apply (hRec.trans (hTree.trans (hErr.trans (hCount.trans hAns)))).mono Set.Subset.rfl ?_ ?_
  · rw [hEq]
  · unfold attemptBudget
    change _ ≤ 2228241 * n + OrderedTree.treeBudget r m + 4
    omega

theorem control_size (r m : ℕ) (hm : r + 4 ≤ m) :
    complexity interpretation (single (control r m hm)) ≤
      (r + 4)^4 * (attemptBudget r m + 1) + 1 := by
  let f (u : Fin 4 → Fin (r + 4)) := attempt r (Fin.castLE hm ∘ u)
  have hs := Synthesis.exists_mem (Finset.univ : Finset (Fin 4 → Fin (r + 4))) f
    (fun _ => attemptBudget r m) (fun u _ => attempt_size (Fin.castLE hm ∘ u))
  have h' := Synthesis.congr_iff hs (g := control r m hm) (fun T => by
    simp only [control, f, Finset.mem_univ, true_and, decide_eq_true_eq])
  simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using
    h'.complexity_le

theorem control_size_poly (r m : ℕ) (hm : r + 4 ≤ m) :
    complexity interpretation (single (control r m hm)) ≤ 3000000 * (r+4)^7 * 2^m := by
  let P := (r+4)^3
  let N := 2^m
  have hp : 1 ≤ P := Nat.pow_pos (by omega)
  have hn : 1 ≤ N := Nat.two_pow_pos _
  have hPN : N ≤ P*N := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right N hp
  have ht := OrderedTree.treeBudget_poly r m
  change OrderedTree.treeBudget r m ≤ 20 * P * N at ht
  have hOne : attemptBudget r m + 1 ≤ 2230000 * (P * N) := by
    change 2228241 * N + OrderedTree.treeBudget r m + 4 + 1 ≤ _
    have h : 20 * P * N = 20 * (P * N) := by ring
    rw [h] at ht
    omega
  apply (control_size r m hm).trans
  have hMul := Nat.mul_le_mul_left ((r+4)^4) hOne
  have hSame : (r+4)^4 * (2230000 * (P * N)) = 2230000 * ((r+4)^7 * N) := by
    dsimp [P]
    ring
  rw [hSame] at hMul
  change _ ≤ 3000000 * (r + 4)^7 * N
  rw [Nat.mul_assoc]
  have hNum : 1 ≤ (r+4)^7 * N := Nat.mul_pos (Nat.pow_pos (by omega) : 0 < (r+4)^7) hn
  omega

end Size

section Schedule

def arity (r : ℕ) : ℕ := r + (2^r + 1)

theorem arity_pow_le (r : ℕ) : 2 ^ r ≤ arity r := by unfold arity; omega

theorem arity_room (r : ℕ) (hr : 10 ≤ r) : r + 4 ≤ arity r := by
  have hp : 1024 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  unfold arity
  omega

theorem sparse (r : ℕ) (hr : 10 ≤ r) :
    (acceptingTables (control r (arity r) (arity_room r hr))).card ≤ 2 ^ descriptionBitBound (arity r) := by
  apply le_trans _ (card_accepting_mcspSquare_le (arity r))
  apply Finset.card_le_card
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    control_exact _ hr (arity_pow_le r) (Finset.mem_filter.mp hT).2⟩

theorem passes_log_schedule (r : ℕ) (hr : 10 ≤ r) (h : BooleanFunction (2^r))
    (hh : WideTests (mcspSquare (arity r)) h) (e : Equiv.Perm (Fin (arity r)))
    (f g : BooleanFunction r) (D : Finset (Fin (2 ^ arity r))) (hD : D.card ≤ 4) :
    control r (arity r) (arity_room r hr) (patch D (wideMixed h f g ∘ tablePerm e)) = true ↔ f = g := by
  constructor
  · intro he
    exact (wide_transport square_comp_tablePerm hh e f g D hD).mp
      (control_exact _ hr (arity_pow_le r) he)
  · intro he
    have h : wideMixed h f g = probe (2^r) g := by rw [he, wideMixed, splice_self]
    obtain ⟨c, hc⟩ := JuntaRadius.prefix_code_after_perm g e
    have hCode : probe (2^r) g ∘ tablePerm e = MCSP.truthTable (arity r) (value c) := hc
    rw [h, hCode]
    exact control_accepts _ c D hD

/-- On the explicit logarithmic schedule the ratio to N log N tends to zero. -/
theorem sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (control r (arity r) (arity_room r hr))) ≤
        arity r * 2 ^ arity r := by
  have hf := Nat.eventually_mul_add_one_pow_le_pow_div (K * 3000000 * 4^7) 7 1
    (by decide : 1 < (2 : ℕ)) (by decide)
  filter_upwards [hf] with r he hr
  have h := control_size_poly r (arity r) (arity_room r hr)
  have hp : (r+4)^7 ≤ 4^7 * (r+1)^7 := by
    have hMul := Nat.pow_le_pow_left (by omega : r+4 ≤ 4*(r+1)) 7
    simpa only [mul_pow] using hMul
  have h2 : K * 3000000 * 4^7 * (r+1)^7 ≤ 2^r := by simpa only [Nat.div_one] using he
  have hAr : 2^r ≤ arity r := by dsimp [arity]; omega
  calc
    _ ≤ K * (3000000 * (r+4)^7 * 2^arity r) := Nat.mul_le_mul_left _ h
    _ = K * 3000000 * (r+4)^7 * 2^arity r := by ring
    _ ≤ (K * 3000000 * (4^7 * (r+1)^7)) * 2^arity r :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = (K * 3000000 * 4^7 * (r+1)^7) * 2^arity r := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (h2.trans hAr)

end Schedule

#print axioms control_size_poly
#print axioms sparse
#print axioms passes_log_schedule
#print axioms sub_nlogn

end PvsNP.Frontier.LogPrefixControl
