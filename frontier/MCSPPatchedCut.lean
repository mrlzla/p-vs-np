module

public import MCSPRefinedProbeSplices
public import MCSPMinorityResidual

/-! A single equality selector for all common patches of at most four
truth-table entries, with the option to prescribe its values at a small sample. -/

@[expose] public section

namespace PvsNP.Frontier.PatchedCut

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CommunicationCut SuperTwoN CornerCertificates PermutedCut
open scoped Classical

abbrev Address := Fin (2 ^ 32)
abbrev Prefix := BooleanFunction 9
abbrev Selector := BooleanFunction 22

def patch {n : ℕ} (D : Finset (Fin n)) (T : BitString n) : BitString n :=
  fun i => T i ^^ decide (i ∈ D)

theorem patch_injective {n : ℕ} (D : Finset (Fin n)) : Function.Injective (patch D) := by
  intro x y h
  funext i
  have he := congrFun h i
  have cancel (x y b : Bool) (h : (x ^^ b) = (y ^^ b)) : x = y := by
    cases x <;> cases y <;> cases b <;> simp_all
  exact cancel _ _ _ he

theorem patched_prefix_accepted (f : Prefix) (D : Finset Address) (hD : D.card ≤ 4) :
    mcspSquare 32 (patch D (probe 22 f)) = true := by
  let p : BooleanFunction 32 := fun z => f (z ∘ Fin.castAdd 23)
  let q : BooleanFunction 32 := fun z => decide (BitString.equivFin 32 z ∈ D)
  have hEq : (MCSP.truthTable 32).symm (patch D (probe 22 f)) = fun z => p z ^^ q z := by
    funext z
    change (probe 22 f (BitString.equivFin 32 z) ^^ decide (BitString.equivFin 32 z ∈ D)) = _
    rw [probe, MCSP.truthTable_apply, Equiv.symm_apply_apply]
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hEq]
  have hp : complexity interpretation (single p) ≤ 848 :=
    RefinedCut.shannon_lift (k := 2) (d := 7) f (Fin.castAdd 23)
  have hq : complexity interpretation (single q) ≤ 32 + D.card * 34 + 1 :=
    MinorityResidual.point_indicator_complexity_le 32 D
  exact (complexity_xor_le p q).trans (by omega)

def mixed (h : Selector) (f g : Prefix) : BitString (2 ^ 32) :=
  splice (mask 9 h) (probe 22 f) (probe 22 g)

abbrev PatchList (n : ℕ) (radius : ℕ := 4) := Fin radius → Option (Fin n)

def optionSet {n : ℕ} (o : Option (Fin n)) : Finset (Fin n) :=
  o.elim ∅ fun i => {i}

noncomputable def patchList {n radius : ℕ} (e : PatchList n radius) : Finset (Fin n) :=
  Finset.univ.biUnion fun j => optionSet (e j)

theorem patchList_surj {n radius : ℕ} (D : Finset (Fin n)) (hD : D.card ≤ radius) :
    ∃ e : PatchList n radius, patchList e = D := by
  classical
  let enum : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let e (j : Fin radius) : Option (Fin n) :=
    if h : j.val < D.card then some (enum ⟨j.val, h⟩).val else none
  refine ⟨e, ?_⟩
  ext i
  constructor
  · intro hi
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    by_cases h : j.val < D.card
    · have he : i = (enum ⟨j.val, h⟩).val := by simpa [e, h, optionSet] using hj
      exact he.symm ▸ (enum ⟨j.val, h⟩).property
    · simp [e, h, optionSet] at hj
  · intro hi
    let j := enum.symm ⟨i, hi⟩
    let j' : Fin radius := ⟨j.val, j.isLt.trans_le hD⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j', Finset.mem_univ _, ?_⟩
    have hj : j'.val < D.card := j.isLt
    simp [e, hj, optionSet, j', j]

private noncomputable def badOneFor {A H : Type} [Fintype H] {n radius : ℕ}
    (F : BooleanFunction n) (mix : H → A → A → BitString n) (test : A × A × PatchList n radius) : Finset H :=
  if test.1 = test.2.1 then ∅ else
    Finset.univ.filter fun h => F (patch (patchList test.2.2) (mix h test.1 test.2.1)) = true

private noncomputable def badFor {A H : Type} [Fintype A] [Fintype H] [DecidableEq H] {n : ℕ}
    (F : BooleanFunction n) (mix : H → A → A → BitString n) (radius : ℕ := 4) : Finset H :=
  (Finset.univ : Finset (A × A × PatchList n radius)).biUnion (badOneFor F mix)

private theorem badOne_card (test : Prefix × Prefix × PatchList (2 ^ 32)) :
    (badOneFor (mcspSquare 32) mixed test).card ≤ 2 ^ descriptionBitBound 32 := by
  by_cases he : test.1 = test.2.1
  · simp [badOneFor, he]
  · apply le_trans _ (card_accepting_mcspSquare_le 32)
    apply Finset.card_le_card_of_injOn (fun h => patch (patchList test.2.2) (mixed h test.1 test.2.1))
    · intro h hh
      simpa [badOneFor, he, acceptingTables] using hh
    · exact ((patch_injective _).comp (splice_injective_in_mask he)).injOn

private theorem tuple_test_card {A B : Type} [Fintype A] [Fintype B] {a b n : ℕ}
    (hA : Fintype.card A = 2 ^ a) (hB : Fintype.card B ≤ 2 ^ b) :
    Fintype.card (A × A × (Fin n → Option B)) ≤ 2 ^ (a + a + (b + 1) * n) := by
  have ho : Fintype.card (Option B) ≤ 2 ^ (b + 1) := by
    rw [Fintype.card_option, pow_succ']
    have hp : 0 < (2 : ℕ) ^ b := by positivity
    omega
  rw [Fintype.card_prod, Fintype.card_prod, hA, ← Nat.mul_assoc, Fintype.card_fun, Fintype.card_fin,
    pow_add 2 (a + a), pow_add 2 a a, pow_mul]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ho _)

private theorem card_functions (r : ℕ) : Fintype.card (BooleanFunction r) = 2 ^ 2 ^ r := by
  classical
  simp

set_option exponentiation.threshold 1200 in
private theorem test_card : Fintype.card (Prefix × Prefix × PatchList (2 ^ 32)) ≤ 2 ^ 1156 := by
  have h := tuple_test_card (A := Prefix) (B := Address) (a := 512) (b := 32) (n := 4)
    (card_functions 9) (le_of_eq (Fintype.card_fin (2 ^ 32)))
  rwa [show 512 + 512 + (32 + 1) * 4 = 1156 by decide] at h

private theorem card_biUnion_univ_le {T H : Type} [Fintype T] [DecidableEq H]
    (B : T → Finset H) (M : ℕ) (h : ∀ t, (B t).card ≤ M) :
    ((Finset.univ : Finset T).biUnion B).card ≤ Fintype.card T * M := by
  calc
    _ ≤ ∑ t : T, (B t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t : T, M := Finset.sum_le_sum fun t _ => h t
    _ = _ := by rw [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ]

private theorem bad_card : (badFor (mcspSquare 32) mixed).card ≤ 2 ^ 28828 := by
  have hB : descriptionBitBound 32 = 27672 := by decide
  calc
    _ ≤ Fintype.card (Prefix × Prefix × PatchList (2 ^ 32)) * 2 ^ descriptionBitBound 32 :=
      card_biUnion_univ_le (badOneFor (mcspSquare 32) mixed) (2 ^ descriptionBitBound 32) badOne_card
    _ ≤ 2 ^ 1156 * 2 ^ descriptionBitBound 32 :=
      Nat.mul_le_mul_right (2 ^ descriptionBitBound 32) test_card
    _ = 2 ^ 28828 := by rw [← pow_add, hB]

def Tests (F : BooleanFunction (2 ^ 32)) (h : Selector) : Prop :=
  ∀ f g : Prefix, ∀ D : Finset Address, D.card ≤ 4 →
    (F (patch D (mixed h f g)) = true ↔ f = g)

private theorem exists_outside {H : Type} {s t : Finset H} (hc : s.card < t.card) :
    ∃ x ∈ t, x ∉ s := by
  by_contra! h
  exact (not_le_of_gt hc) (Finset.card_le_card h)

private theorem choose_good {A H : Type} [Fintype A] [Fintype H] [DecidableEq H] {n radius : ℕ}
    (F : BooleanFunction n) (mix : H → A → A → BitString n) (C : Finset H) (P : H → Prop)
    (hC : (badFor F mix radius).card < C.card) (hP : ∀ h ∈ C, P h)
    (diag : ∀ h f D, D.card ≤ radius → F (patch D (mix h f f)) = true) :
    ∃ h, P h ∧ ∀ f g D, D.card ≤ radius → (F (patch D (mix h f g)) = true ↔ f = g) := by
  obtain ⟨h, hMem, hGood⟩ := exists_outside hC
  refine ⟨h, hP h hMem, fun f g D hD => ?_⟩
  constructor
  · intro hAccept
    by_contra hne
    obtain ⟨e, hE⟩ := patchList_surj D hD
    apply hGood
    apply Finset.mem_biUnion.mpr
    refine ⟨(f, g, e), Finset.mem_univ _, ?_⟩
    simpa [badOneFor, hne, hE] using hAccept
  · rintro rfl
    exact diag h f D hD

/-- A single selector avoids all patched off-diagonals when the mixed
table identifies the selector with bounded auxiliary information. -/
theorem exists_family_selector_with_aux_radius {A H J : Type}
    [Fintype A] [Fintype H] [DecidableEq H] [Fintype J] {n p q B d radius : ℕ}
    (F : BooleanFunction n) (mix : H → A → A → BitString n)
    (hA : Fintype.card A = 2 ^ p) (hN : n ≤ 2 ^ q)
    (hSparse : (acceptingTables F).card ≤ 2 ^ B) (hJ : Fintype.card J ≤ 2 ^ d)
    (room : 2 ^ (p + p + (q + 1) * radius + B + d) < Fintype.card H)
    (diagonal : ∀ h f D, D.card ≤ radius → F (patch D (mix h f f)) = true)
    (separate : ∀ {f g}, f ≠ g →
      ∃ aux : H → J, Function.Injective (fun h => (mix h f g, aux h))) :
    ∃ h, ∀ f g D, D.card ≤ radius → (F (patch D (mix h f g)) = true ↔ f = g) := by
  have hOne (test : A × A × PatchList n radius) : (badOneFor F mix test).card ≤ 2 ^ (B + d) := by
    by_cases he : test.1 = test.2.1
    · simp [badOneFor, he]
    · obtain ⟨aux, hinj⟩ := separate he
      let out := acceptingTables F ×ˢ (Finset.univ : Finset J)
      have hout : out.card ≤ 2 ^ (B + d) := by
        simpa only [out, Finset.card_product, Finset.card_univ, pow_add] using Nat.mul_le_mul hSparse hJ
      apply le_trans _ hout
      refine Finset.card_le_card_of_injOn
        (fun h => (patch (patchList test.2.2) (mix h test.1 test.2.1), aux h)) ?_ ?_
      · intro h hh
        have hYes : F (patch (patchList test.2.2) (mix h test.1 test.2.1)) = true := by
          simpa [badOneFor, he] using hh
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hYes⟩, Finset.mem_univ _⟩
      · intro x _ y _ hxy
        have hAux : aux x = aux y := congrArg Prod.snd hxy
        exact hinj (Prod.ext ((patch_injective _) (congrArg Prod.fst hxy)) hAux)
  have hcard : (badFor F mix radius).card ≤ 2 ^ (p + p + (q + 1) * radius + B + d) := by
    have hTests : Fintype.card (A × A × PatchList n radius) ≤ 2 ^ (p + p + (q+1) * radius) :=
      tuple_test_card (a := p) (b := q) (n := radius) hA (by simpa only [Fintype.card_fin] using hN)
    calc
      _ ≤ Fintype.card (A × A × PatchList n radius) * 2 ^ (B + d) := card_biUnion_univ_le _ _ hOne
      _ ≤ 2 ^ (p + p + (q+1) * radius) * 2 ^ (B + d) := Nat.mul_le_mul_right _ hTests
      _ = _ := by rw [← pow_add, ← Nat.add_assoc]
  have hlt : (badFor F mix radius).card < (Finset.univ : Finset H).card := by
    rw [Finset.card_univ]
    exact hcard.trans_lt room
  obtain ⟨h, _, ht⟩ := choose_good F mix Finset.univ (fun _ => True) hlt (fun _ _ => trivial) diagonal
  exact ⟨h, ht⟩

theorem exists_family_selector_with_aux {A H J : Type}
    [Fintype A] [Fintype H] [DecidableEq H] [Fintype J] {n p q B d : ℕ}
    (F : BooleanFunction n) (mix : H → A → A → BitString n)
    (hA : Fintype.card A = 2 ^ p) (hN : n ≤ 2 ^ q)
    (hSparse : (acceptingTables F).card ≤ 2 ^ B) (hJ : Fintype.card J ≤ 2 ^ d)
    (room : 2 ^ (p + p + (q + 1) * 4 + B + d) < Fintype.card H)
    (diagonal : ∀ h f D, D.card ≤ 4 → F (patch D (mix h f f)) = true)
    (separate : ∀ {f g}, f ≠ g →
      ∃ aux : H → J, Function.Injective (fun h => (mix h f g, aux h))) :
    ∃ h, ∀ f g D, D.card ≤ 4 → (F (patch D (mix h f g)) = true ↔ f = g) :=
  exists_family_selector_with_aux_radius F mix hA hN hSparse hJ room diagonal separate

/-- The injective case needs no auxiliary information. -/
theorem exists_family_selector {A H : Type} [Fintype A] [Fintype H] [DecidableEq H] {n p q B : ℕ}
    (F : BooleanFunction n) (mix : H → A → A → BitString n)
    (hA : Fintype.card A = 2 ^ p) (hN : n ≤ 2 ^ q)
    (hSparse : (acceptingTables F).card ≤ 2 ^ B)
    (room : 2 ^ (p + p + (q + 1) * 4 + B) < Fintype.card H)
    (diagonal : ∀ h f D, D.card ≤ 4 → F (patch D (mix h f f)) = true)
    (separate : ∀ {f g}, f ≠ g → Function.Injective (fun h => mix h f g)) :
    ∃ h, ∀ f g D, D.card ≤ 4 → (F (patch D (mix h f g)) = true ↔ f = g) := by
  exact exists_family_selector_with_aux (J := Unit) (d := 0) F mix hA hN hSparse
    (by simp) (by simpa using room) diagonal (fun he => ⟨fun _ => (), fun _ _ eq =>
      separate he (congrArg Prod.fst eq)⟩)

private theorem prefix_diag (h : Selector) (f : Prefix) (D : Finset Address) (hD : D.card ≤ 4) :
    mcspSquare 32 (patch D (mixed h f f)) = true := by
  unfold mixed
  rw [splice_self]
  exact patched_prefix_accepted f D hD

/-- One selector rejects every patched off-diagonal while retaining all the
patched diagonals. The selector may also satisfy a prescribed anchor pattern. -/
theorem exists_patched_selector_with (A : Finset (BitString 22)) (v : Selector)
    (hA : 28828 < 2 ^ 22 - A.card) :
    ∃ h : Selector, (∀ t ∈ A, h t = v t) ∧ Tests (mcspSquare 32) h :=
  choose_good (mcspSquare 32) mixed (RefinedCut.prescribed A v) (fun h => ∀ t ∈ A, h t = v t)
    (bad_card.trans_lt (RefinedCut.prescribed_large A v hA))
    (fun h => (@RefinedCut.mem_prescribed 22 A v h).mp) prefix_diag

theorem exists_patched_selector : ∃ h : Selector, Tests (mcspSquare 32) h := by
  have hn : 28828 < 2 ^ 22 - (∅ : Finset (BitString 22)).card := by decide
  obtain ⟨h, _, hh⟩ := exists_patched_selector_with ∅ (fun _ => false) hn
  exact ⟨h, hh⟩

/-- Transport the entire patched family along each chosen split-bit swap. -/
theorem patched_transport {F : BooleanFunction (2 ^ 32)}
    (hPerm : ∀ (e : Equiv.Perm (Fin 23)) T, F (T ∘ tablePerm (liftTail 9 e)) = F T)
    {h : Selector} (hh : Tests F h) (e : Equiv.Perm (Fin 23))
    (f g : Prefix) (D : Finset Address) (hD : D.card ≤ 4) :
    F (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) = true ↔ f = g := by
  let p := tablePerm (liftTail 9 e)
  have he : patch D (mixed h f g ∘ p) = (patch (D.map p.toEmbedding) (mixed h f g)) ∘ p := by
    funext i
    simp [patch, Function.comp_apply]
  rw [he, hPerm e]
  exact hh f g _ (by simpa using hD)

set_option exponentiation.threshold 600 in
/-- Every fixed patch still requires 512 bits in a one-way factorization. -/
theorem patched_oneWay_width {h : Selector} (hh : Tests (mcspSquare 32) h)
    (e : Equiv.Perm (Fin 23)) (D : Finset Address) (hD : D.card ≤ 4)
    {w : ℕ} (send : Prefix → BitString w) (finish : BitString w → Prefix → Bool)
    (factor : ∀ f g, finish (send f) g =
      mcspSquare 32 (patch D (mixed h f g ∘ tablePerm (liftTail 9 e)))) : 512 ≤ w := by
  have heq := patched_transport (fun e => square_comp_tablePerm (liftTail 9 e)) hh e
  have hi : Function.Injective send := by
    intro f g hfg
    apply (heq f g D hD).mp
    rw [← factor, hfg, factor]
    exact (heq g g D hD).mpr rfl
  have hc := Fintype.card_le_of_injective send hi
  rw [card_functions, BitString.card] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc

#print axioms exists_patched_selector_with
#print axioms patched_transport
#print axioms patched_oneWay_width


section Wider

variable {r s : ℕ}

def wideMixed (h : BooleanFunction s) (f g : BooleanFunction r) : BitString (2 ^ (r + (s + 1))) :=
  splice (mask r h) (probe s f) (probe s g)

def WideTests (F : BooleanFunction (2 ^ (r + (s + 1)))) (h : BooleanFunction s) : Prop :=
  ∀ f g : BooleanFunction r, ∀ D : Finset (Fin (2 ^ (r + (s + 1)))), D.card ≤ 4 →
    (F (patch D (wideMixed h f g)) = true ↔ f = g)

def wideExponent (r s : ℕ) : ℕ :=
  2 ^ r + 2 ^ r + ((r + (s + 1)) + 1) * 4 + descriptionBitBound (r + (s + 1))

private theorem wide_bad_one_card
    (test : BooleanFunction r × BooleanFunction r × PatchList (2 ^ (r + (s + 1)))) :
    (badOneFor (mcspSquare (r + (s + 1))) wideMixed test).card ≤
      2 ^ descriptionBitBound (r + (s + 1)) := by
  by_cases he : test.1 = test.2.1
  · simp [badOneFor, he]
  · apply le_trans _ (card_accepting_mcspSquare_le (r + (s + 1)))
    apply Finset.card_le_card_of_injOn (fun h => patch (patchList test.2.2) (wideMixed h test.1 test.2.1))
    · intro h hh
      simpa [badOneFor, he, acceptingTables] using hh
    · exact ((patch_injective _).comp (splice_injective_in_mask he)).injOn

private theorem wide_bad_card :
    (badFor (mcspSquare (r + (s + 1))) wideMixed).card ≤ 2 ^ wideExponent r s := by
  let m := r + (s + 1)
  have hc : Fintype.card (BooleanFunction r × BooleanFunction r × PatchList (2 ^ m)) ≤
      2 ^ (2 ^ r + 2 ^ r + (m + 1) * 4) :=
    tuple_test_card (a := 2 ^ r) (b := m) (n := 4) (card_functions r) (le_of_eq (Fintype.card_fin _))
  calc
    _ ≤ Fintype.card (BooleanFunction r × BooleanFunction r × PatchList (2 ^ m)) *
        2 ^ descriptionBitBound m :=
      card_biUnion_univ_le (badOneFor (mcspSquare m) wideMixed) _ wide_bad_one_card
    _ ≤ 2 ^ (2 ^ r + 2 ^ r + (m + 1) * 4) * 2 ^ descriptionBitBound m :=
      Nat.mul_le_mul_right _ hc
    _ = _ := (pow_add ..).symm

/-- The same counting argument works at any prefix width where the diagonal
and selector budgets hold. -/
theorem exists_wide_selector_with (A : Finset (BitString s)) (v : BooleanFunction s)
    (room : wideExponent r s < 2 ^ s - A.card)
    (accept : ∀ (f : BooleanFunction r) (D : Finset (Fin (2 ^ (r + (s + 1))))), D.card ≤ 4 →
      mcspSquare (r + (s + 1)) (patch D (probe s f)) = true) :
    ∃ h : BooleanFunction s, (∀ t ∈ A, h t = v t) ∧ WideTests (mcspSquare (r + (s + 1))) h := by
  refine choose_good (mcspSquare (r + (s + 1))) wideMixed (RefinedCut.prescribed A v)
    (fun h => ∀ t ∈ A, h t = v t) (wide_bad_card.trans_lt (RefinedCut.prescribed_large A v room))
    (fun h => (@RefinedCut.mem_prescribed s A v h).mp) ?_
  intro h f D hD
  unfold wideMixed
  rw [splice_self]
  exact accept f D hD

theorem wide_transport {F : BooleanFunction (2 ^ (r + (s + 1)))}
    (hPerm : ∀ (e : Equiv.Perm (Fin (r + (s + 1)))) T, F (T ∘ tablePerm e) = F T)
    {h : BooleanFunction s} (hh : WideTests F h) (e : Equiv.Perm (Fin (r + (s + 1))))
    (f g : BooleanFunction r) (D : Finset (Fin (2 ^ (r + (s + 1))))) (hD : D.card ≤ 4) :
    F (patch D (wideMixed h f g ∘ tablePerm e)) = true ↔ f = g := by
  let p := tablePerm e
  have he : patch D (wideMixed h f g ∘ p) = (patch (D.map p.toEmbedding) (wideMixed h f g)) ∘ p := by
    funext i
    simp [patch, Function.comp_apply]
  rw [he, hPerm e]
  exact hh f g _ (by simpa using hD)

/-- The communication bound is per cut. -/
theorem wide_oneWay_width {h : BooleanFunction s} (hh : WideTests (mcspSquare (r + (s + 1))) h)
    (e : Equiv.Perm (Fin (r + (s + 1)))) (D : Finset (Fin (2 ^ (r + (s + 1))))) (hD : D.card ≤ 4)
    {w : ℕ} (send : BooleanFunction r → BitString w) (finish : BitString w → BooleanFunction r → Bool)
    (factor : ∀ f g, finish (send f) g =
      mcspSquare (r + (s + 1)) (patch D (wideMixed h f g ∘ tablePerm e))) : 2 ^ r ≤ w := by
  have heq := wide_transport square_comp_tablePerm hh e
  have hi : Function.Injective send := by
    intro f g hfg
    apply (heq f g D hD).mp
    rw [← factor, hfg, factor]
    exact (heq g g D hD).mpr rfl
  have hc := Fintype.card_le_of_injective send hi
  rw [card_functions, BitString.card] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hc

/-- Sending the prefix itself meets the one-way lower bound. -/
theorem wide_prefix_message {h : BooleanFunction s} (hh : WideTests (mcspSquare (r + (s + 1))) h)
    (e : Equiv.Perm (Fin (r + (s + 1)))) (D : Finset (Fin (2 ^ (r + (s + 1))))) (hD : D.card ≤ 4) :
    ∃ send : BooleanFunction r → BitString (2 ^ r),
      ∃ finish : BitString (2 ^ r) → BooleanFunction r → Bool,
        ∀ f g, finish (send f) g =
          mcspSquare (r + (s + 1)) (patch D (wideMixed h f g ∘ tablePerm e)) := by
  refine ⟨MCSP.truthTable r, fun msg g => decide (msg = MCSP.truthTable r g), ?_⟩
  intro f g
  apply Bool.eq_iff_iff.mpr
  exact decide_eq_true_iff.trans ((MCSP.truthTable r).apply_eq_iff_eq.trans
    (wide_transport square_comp_tablePerm hh e f g D hD).symm)

/-- Even before a cut is chosen, exact MCSP's accepting-table count caps the
number of independent bits in a fully accepted prefix family. -/
theorem prefix_payload_le_description {h : BooleanFunction s}
    (hh : WideTests (mcspSquare (r + (s + 1))) h) : 2 ^ r ≤ descriptionBitBound (r + (s + 1)) := by
  have hYes (f : BooleanFunction r) : probe s f ∈ acceptingTables (mcspSquare (r + (s + 1))) := by
    have hc := (hh f f ∅ (by simp)).mpr rfl
    unfold wideMixed at hc
    rw [splice_self] at hc
    have hEmpty : patch ∅ (probe s f) = probe s f := by funext i; simp [patch]
    rw [hEmpty] at hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  let encode (f : BooleanFunction r) : acceptingTables (mcspSquare (r + (s + 1))) := ⟨probe s f, hYes f⟩
  have hInj : Function.Injective encode := by
    intro f g he
    have hu := congrArg Subtype.val he
    funext a
    have hc := congrFun hu (position a false (fun _ : Fin s => false))
    simpa only [encode, probe_at_position] using hc
  have hCount := Fintype.card_le_of_injective encode hInj
  rw [Fintype.card_coe, card_functions] at hCount
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (hCount.trans (card_accepting_mcspSquare_le (r + (s + 1))))

end Wider

#print axioms exists_wide_selector_with
#print axioms wide_oneWay_width
#print axioms wide_prefix_message
#print axioms prefix_payload_le_description

end PvsNP.Frontier.PatchedCut
