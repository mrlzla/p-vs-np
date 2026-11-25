module

public import MCSPPatchedControl

/-! A sparse linear-size control for every selector in the patched
prefix experiment. It recognizes the radius-four neighborhood of the
repeated-prefix tables. -/
@[expose] public section

namespace PvsNP.Frontier.RadiusControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open PatchedCut (patch weight_cons PatchList patchList patchList_surj)
open CommunicationCut CornerCertificates SuperTwoN PermutedCut
open InvariantControl (weight point point_cons perm_point)
open scoped Classical

abbrev Location (s : ℕ) := Fin (2 ^ (9 + (s + 1)))

def row {s : ℕ} (i : Location s) : BitString 9 := ((positionEquiv 9 s).symm i).1

private theorem probe_eq_row {s : ℕ} (f : BooleanFunction 9) (i : Location s) :
    probe s f i = f (row i) := by
  obtain ⟨⟨a,b,t⟩, rfl⟩ := (positionEquiv 9 s).surjective i
  change probe s f (position a b t) = f (((positionEquiv 9 s).symm ((positionEquiv 9 s) (a,b,t))).1)
  rw [probe_at_position, Equiv.symm_apply_apply]

section Samples

variable {s : ℕ} (sample : Fin 9 ↪ BitString s)

def decode (X : Location s → Bool) (a : BitString 9) : Bool :=
  decide (5 ≤ weight (fun j => X (position a false (sample j))))

def errors (X : Location s → Bool) : Finset (Location s) :=
  Finset.univ.filter fun i => (X i ^^ probe s (decode sample X) i) = true

def radius (X : Location s → Bool) : Bool := decide ((errors sample X).card ≤ 4)

private noncomputable def touched (E : Finset (Location s)) (a : BitString 9) : Finset (Fin 9) :=
  Finset.univ.filter fun j => position a false (sample j) ∈ E ∨ position a true (sample j) ∈ E

private theorem touched_card (E : Finset (Location s)) (a : BitString 9) :
    (touched sample E a).card ≤ E.card := by
  let b (j : Fin 9) := !(decide (position a false (sample j) ∈ E))
  apply Finset.card_le_card_of_injOn (fun j => position a (b j) (sample j))
  · intro j hj
    rcases (Finset.mem_filter.mp hj).2 with h | h
    · simp [b, h]
    · by_cases h' : position a false (sample j) ∈ E <;> simp [b, h', h]
  · intro j _ k _ he
    change (positionEquiv 9 s) (a, b j, sample j) = (positionEquiv 9 s) (a, b k, sample k) at he
    have h := (positionEquiv 9 s).injective he
    exact sample.injective (congrArg (fun p : BitString 9 × Bool × BitString s => p.2.2) h)

private theorem untouched {E : Finset (Location s)} {a : BitString 9} {j : Fin 9}
    (h : j ∉ touched sample E a) (b : Bool) : position a b (sample j) ∉ E := by
  intro hE
  apply h
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by cases b; exacts [Or.inl hE, Or.inr hE]⟩

private theorem decode_patched (f : BooleanFunction 9) (D : Finset (Location s)) (hD : D.card ≤ 4) :
    decode sample (patch D (probe s f)) = f := by
  funext a
  let Y := (Finset.univ : Finset (Fin 9)).filter fun j => patch D (probe s f) (position a false (sample j)) = true
  have ht := (touched_card sample D a).trans hD
  have hp (j : Fin 9) (hj : j ∉ touched sample D a) :
      patch D (probe s f) (position a false (sample j)) = f a := by
    simp [patch, untouched sample hj false]
  cases he : f a
  · have hSub : Y ⊆ touched sample D a := by
      intro j hj
      by_contra h
      have hv := (Finset.mem_filter.mp hj).2
      rw [hp j h, he] at hv
      cases hv
    have hn : ¬ 5 ≤ Y.card := by have := (Finset.card_le_card hSub).trans ht; omega
    exact decide_eq_false hn
  · have hSub : (Finset.univ : Finset (Fin 9)) \ touched sample D a ⊆ Y := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hp j (Finset.mem_sdiff.mp hj).2).trans he⟩
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (touched sample D a))
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have hY := Finset.card_le_card hSub
    exact decide_eq_true (by omega : 5 ≤ Y.card)

private theorem recover_table (X : Location s → Bool) :
    X = patch (errors sample X) (probe s (decode sample X)) := by
  funext i
  cases hx : X i <;> cases hp : probe s (decode sample X) i <;> simp [errors, patch, hx, hp]

/-- The recovered prefix is a witness exactly when the input is within
four flips of some repeated prefix table. -/
theorem radius_iff (X : Location s → Bool) :
    radius sample X = true ↔ ∃ f : BooleanFunction 9, ∃ D : Finset (Location s),
      D.card ≤ 4 ∧ X = patch D (probe s f) := by
  change decide ((errors sample X).card ≤ 4) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨decode sample X, errors sample X, h, recover_table sample X⟩
  · rintro ⟨f, D, hD, rfl⟩
    have he : errors sample (patch D (probe s f)) = D := by
      ext i
      simp only [errors, decode_patched sample f D hD, Finset.mem_filter, Finset.mem_univ, true_and]
      cases hb : probe s f i <;> by_cases hi : i ∈ D <;> simp [patch, hb, hi]
    rwa [he]

/-- This control passes the patched equality test for every selector. -/
theorem radius_tests (h : BooleanFunction s) (f g : BooleanFunction 9) (D : Finset (Location s))
    (hD : D.card ≤ 4) :
    radius sample (patch D (splice (mask 9 h) (probe s f) (probe s g))) = true ↔ f = g := by
  rw [radius_iff]
  constructor
  · rintro ⟨q, E, hE, hEq⟩
    by_contra hne
    obtain ⟨a, ha⟩ : ∃ a, f a ≠ g a := by by_contra! h; exact hne (funext h)
    have hu : (D ∪ E).card ≤ 8 := (Finset.card_union_le _ _).trans (by omega)
    have hFew := (touched_card sample (D ∪ E) a).trans hu
    obtain ⟨j, hj⟩ : ∃ j : Fin 9, j ∉ touched sample (D ∪ E) a := by
      by_contra! h
      have he := Finset.eq_univ_of_forall h
      rw [he, Finset.card_univ, Fintype.card_fin] at hFew
      omega
    have hb (b : Bool) : (splice (mask 9 h) (probe s f) (probe s g)) (position a b (sample j)) = q a := by
      have hU := untouched sample hj b
      have hD' : position a b (sample j) ∉ D := fun hm => hU (Finset.mem_union_left _ hm)
      have hE' : position a b (sample j) ∉ E := fun hm => hU (Finset.mem_union_right _ hm)
      have he := congrFun hEq (position a b (sample j))
      simpa [patch, hD', hE'] using he
    have h0 := hb false
    have h1 := hb true
    simp only [splice, mask_at_position, probe_at_position] at h0 h1
    cases hh : h (sample j)
    · simp [hh] at h0 h1
      exact ha (h1.trans h0.symm)
    · simp [hh] at h0 h1
      exact ha (h0.trans h1.symm)
  · rintro rfl
    rw [splice_self]
    exact ⟨f, D, hD, rfl⟩

private theorem probe_perm {s : ℕ} (e : Equiv.Perm (Fin (s + 1))) (f : BooleanFunction 9) :
    probe s f ∘ tablePerm (liftTail 9 e) = probe s f := by
  have hP (a : BitString 9) (t : BitString (s + 1)) : probe s f (point a t) = f a := by
    rw [← Fin.cons_self_tail t, point_cons, probe_at_position]
  funext i
  obtain ⟨⟨a,b,t⟩, rfl⟩ := (positionEquiv 9 s).surjective i
  change probe s f (tablePerm (liftTail 9 e) (point a (Fin.cons b t))) =
    probe s f (point a (Fin.cons b t))
  rw [perm_point, hP, hP]

private theorem patch_map {n : ℕ} (e : Equiv.Perm (Fin n)) (D : Finset (Fin n)) (T : BitString n) :
    patch D T ∘ e = patch (D.map e.symm.toEmbedding) (T ∘ e) := by
  funext i
  simp [patch, Function.comp_apply]

theorem radius_perm (e : Equiv.Perm (Fin (s + 1))) (X : Location s → Bool) :
    radius sample (X ∘ tablePerm (liftTail 9 e)) = radius sample X := by
  let p := tablePerm (liftTail 9 e)
  have hComp (x : Location s → Bool) (f : BooleanFunction 9) (D : Finset (Location s))
      (h : x = patch D (probe s f)) :
      x ∘ p = patch (D.map p.symm.toEmbedding) (probe s f) := by
    rw [h, patch_map, show probe s f ∘ p = probe s f from probe_perm e f]
  apply Bool.eq_iff_iff.mpr
  rw [radius_iff, radius_iff]
  constructor
  · rintro ⟨f, D, hd, he⟩
    refine ⟨f, D.map p.toEmbedding, by simpa using hd, ?_⟩
    have he' := congrArg (fun X : Location s → Bool => X ∘ p.symm) he
    have hRev : probe s f ∘ p.symm = probe s f := by
      funext i
      have h := congrFun (probe_perm e f) (p.symm i)
      change probe s f (p (p.symm i)) = probe s f (p.symm i) at h
      rwa [Equiv.apply_symm_apply, eq_comm] at h
    rw [patch_map, hRev] at he'
    have hRestore : (X ∘ p) ∘ p.symm = X := by
      funext i
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rwa [hRestore] at he'
  · rintro ⟨f, D, hd, he⟩
    exact ⟨f, D.map p.symm.toEmbedding, by simpa using hd, hComp X f D he⟩

theorem radius_transport_tests (e : Equiv.Perm (Fin (s + 1))) (h : BooleanFunction s)
    (f g : BooleanFunction 9) (D : Finset (Location s)) (hD : D.card ≤ 4) :
    radius sample (patch D ((splice (mask 9 h) (probe s f) (probe s g)) ∘ tablePerm (liftTail 9 e))) =
      true ↔ f = g := by
  let p := tablePerm (liftTail 9 e)
  let T := splice (mask 9 h) (probe s f) (probe s g)
  have he : patch D (T ∘ p) = (patch (D.map p.toEmbedding) T) ∘ p := by
    funext i
    simp [patch, Function.comp_apply]
  rw [he, radius_perm]
  exact radius_tests sample h f g _ (by simpa using hD)

end Samples

#print axioms radius_iff
#print axioms radius_tests
#print axioms radius_perm

section Size

variable {l : ℕ}

def counterStateAt {n k : ℕ} (f : Fin n → BooleanFunction l) (j : Fin k) : BooleanFunction l :=
  fun X => decide (j.val ≤ weight (fun i => f i X))

abbrev counterState {n : ℕ} (f : Fin n → BooleanFunction l) (j : Fin 6) : BooleanFunction l :=
  counterStateAt f j

private theorem threshold_step {n : ℕ} (b : Bool) (q : BitString n) (j : ℕ) :
    decide (j + 1 ≤ weight (Fin.cons b q)) =
      (decide (j + 1 ≤ weight q) || (b && decide (j ≤ weight q))) := by
  rw [weight_cons]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  cases b <;> simp; omega

/-- Each update reuses the earlier threshold bits and costs at most two gates per threshold. -/
theorem synth_counterAt {n k : ℕ} (hk : 0 < k) (base : Set (BooleanFunction l))
    (f : Fin n → BooleanFunction l) (hf : ∀ j, f j ∈ base) :
    Synthesis interpretation base (Set.range (counterStateAt (k := k) f)) (2 * k * n + 2) := by
  induction n with
  | zero =>
    have hlo : Synthesis interpretation base {fun _ => false} 1 := Synthesis.const false
    have hhi : Synthesis interpretation base {fun _ => true} 1 := Synthesis.const true
    apply (hlo.union hhi).mono Set.Subset.rfl ?_ (by omega)
    rintro _ ⟨j, rfl⟩
    have he : counterStateAt f j = fun _ => decide (j.val = 0) := by
      funext X
      simp [counterStateAt, weight]
    rw [he]
    by_cases hj : j.val = 0 <;> simp [hj]
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    let g : Fin n → BooleanFunction l := fun i => f i.succ
    let available := base ∪ Set.range (counterStateAt (k := k+1) g)
    have hBase : Synthesis interpretation base (Set.range (counterStateAt (k := k+1) g)) (2 * (k+1) * n + 2) :=
      ih g (fun i => hf i.succ)
    have hNew (j : Fin (k+1)) : Synthesis interpretation available {counterStateAt f j} 2 := by
      refine Fin.cases ?_ (fun k => ?_) j
      · have he : counterStateAt f (0 : Fin (k+1)) = counterStateAt g (0 : Fin (k+1)) := by funext X; simp [counterStateAt]
        rw [he]
        exact (Synthesis.of_mem (show counterStateAt g (0 : Fin (k+1)) ∈ available from Or.inr ⟨0, rfl⟩)).mono
          Set.Subset.rfl Set.Subset.rfl (by decide)
      · have hA : Synthesis interpretation available {counterStateAt g k.succ} 0 :=
          Synthesis.of_mem (Or.inr ⟨k.succ, rfl⟩)
        have hB : Synthesis interpretation available {counterStateAt g k.castSucc} 0 :=
          Synthesis.of_mem (Or.inr ⟨k.castSucc, rfl⟩)
        have hRead : Synthesis interpretation available {f 0} 0 := Synthesis.of_mem (Or.inl (hf 0))
        have he : counterStateAt f k.succ = fun X =>
            counterStateAt g k.succ X || (f 0 X && counterStateAt g k.castSucc X) := by
          funext X
          have hw : (fun i => f i X) = Fin.cons (f 0 X) (fun i => g i X) :=
            (Fin.cons_self_tail (fun i => f i X)).symm
          unfold counterStateAt
          rw [hw]
          exact threshold_step _ _ k.val
        rw [he]
        exact hA.or (hRead.and hB)
    apply (hBase.trans (Synthesis.family (counterStateAt (k := k+1) f) (fun _ => 2) hNew)).mono
      Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [Nat.mul_succ (2*(k+1)) n]
    omega

theorem synth_counter {n : ℕ} (base : Set (BooleanFunction l))
    (f : Fin n → BooleanFunction l) (hf : ∀ j, f j ∈ base) :
    Synthesis interpretation base (Set.range (counterState f)) (12 * n + 2) :=
  synth_counterAt (by decide : 0 < 6) base f hf

variable {s : ℕ} (sample : Fin 9 ↪ BitString s)

/-- Decoding each prefix once, then counting discrepancies with the running
threshold bits, uses a uniform constant number of gates per table entry. -/

theorem radius_size :
    complexity interpretation (single (radius sample)) ≤
      16 * 2 ^ (9 + (s + 1)) + 5243395 := by
  let N := 2 ^ (9 + (s + 1))
  let f (a : BitString 9) : BooleanFunction N := fun X => decode sample X a
  have hOne (a : BitString 9) : Synthesis interpretation (inputs N) {f a} 10241 :=
    Synthesis.selected (fun j => position a false (sample j)) (fun v : BitString 9 => decide (5 ≤ weight v))
  have hDecode : Synthesis interpretation (inputs N) (Set.range f) 5243392 := by
    have h := Synthesis.family f (fun _ => 10241) hOne
    apply h.mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card]
    decide
  let base := inputs N ∪ Set.range f
  let q (i : Fin N) : BooleanFunction N := fun X => X i ^^ f (row i) X
  have hOne' (i : Fin N) : Synthesis interpretation base {q i} 4 :=
    (Synthesis.of_mem (show (fun X : BitString N => X i) ∈ base from Or.inl ⟨i, rfl⟩)).xor
      (Synthesis.of_mem (show f (row i) ∈ base from Or.inr ⟨row i, rfl⟩))
  have hErr : Synthesis interpretation base (Set.range q) (N * 4) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] using
      Synthesis.family q (fun _ => 4) hOne'
  let ready := base ∪ Set.range q
  have hCount := synth_counter ready q (fun i => Or.inr ⟨i, rfl⟩)
  have hTest : Synthesis interpretation (ready ∪ Set.range (counterState q))
      {fun X => !counterState q 5 X} 1 :=
    (Synthesis.of_mem (Or.inr ⟨5, rfl⟩)).not
  have hRebuild := hDecode.trans (hErr.trans (hCount.trans hTest))
  have hEq : (fun X => !counterState q 5 X) = radius sample := by
    funext X
    have hErrEq : weight (fun i => q i X) = (errors sample X).card := by
      unfold weight errors
      congr 1
    change (!decide (5 ≤ weight (fun i => q i X))) = decide ((errors sample X).card ≤ 4)
    rw [hErrEq]
    by_cases h : (errors sample X).card ≤ 4
    · have h' : ¬ 5 ≤ (errors sample X).card := by omega
      simp [h, h']
    · have h' : 5 ≤ (errors sample X).card := by omega
      simp [h, h']
  rw [hEq] at hRebuild
  exact hRebuild.complexity_le.trans (by change _ ≤ 16 * N + 5243395; omega)

end Size

section Sparsity

private theorem card_patches_bound (m : ℕ) : Fintype.card (PatchList (2 ^ m)) ≤ 2 ^ ((m + 1) * 4) := by
  have h0 : Fintype.card (Option (Fin (2 ^ m))) ≤ 2 ^ (m + 1) := by
    rw [Fintype.card_option, Fintype.card_fin, pow_succ']
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos _
    omega
  calc
    _ = Fintype.card (Option (Fin (2 ^ m))) ^ 4 := by
      simp only [PatchList, Fintype.card_fun, Fintype.card_fin]
    _ ≤ (2 ^ (m + 1)) ^ 4 := Nat.pow_le_pow_left h0 4
    _ = _ := (pow_mul ..).symm

private theorem accepted_value {n : ℕ} {F : BooleanFunction n} {X : BitString n}
    (h : X ∈ acceptingTables F) : F X = true := (Finset.mem_filter.mp h).2

private theorem card_of_encoding {A I : Type} [Fintype I] (S : Finset A) (encode : I → A)
    (h : ∀ X ∈ S, ∃ i, encode i = X) : S.card ≤ Fintype.card I := by
  classical
  have hSub : S ⊆ Finset.univ.image encode := by
    intro X hX
    obtain ⟨i, he⟩ := h X hX
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩
  exact (Finset.card_le_card hSub).trans (Finset.card_image_le.trans_eq Finset.card_univ)

theorem accepting_radius_card {s : ℕ} (sample : Fin 9 ↪ BitString s) :
    (acceptingTables (radius sample)).card ≤ 2 ^ (512 + (9 + (s + 1) + 1) * 4) := by
  let m := 9 + (s + 1)
  let make (v : BooleanFunction 9 × PatchList (2 ^ m)) : Location s → Bool := patch (patchList v.2) (probe s v.1)
  have hs : (acceptingTables (radius sample)).card ≤ Fintype.card (BooleanFunction 9 × PatchList (2 ^ m)) := by
    apply card_of_encoding (acceptingTables (radius sample)) make
    intro X hX
    have hv : radius sample X = true := accepted_value hX
    have hd : (errors sample X).card ≤ 4 := of_decide_eq_true hv
    have hCode := patchList_surj (errors sample X) hd
    let p := hCode.choose
    have hp : patchList p = errors sample X := hCode.choose_spec
    refine ⟨(decode sample X, p), ?_⟩
    change patch (patchList p) (probe s (decode sample X)) = X
    rw [hp]
    exact (recover_table sample X).symm
  have h0 : Fintype.card (BooleanFunction 9) = 2 ^ 512 := by
    change Fintype.card (BitString 9 → Bool) = _
    rw [Fintype.card_fun, Fintype.card_bool, BitString.card]
    rw [show 2 ^ 9 = 512 by decide]
  calc
    _ ≤ Fintype.card (BooleanFunction 9 × PatchList (2 ^ m)) := hs
    _ = 2 ^ 512 * Fintype.card (PatchList (2 ^ m)) := by
      rw [Fintype.card_prod, h0]
    _ ≤ 2 ^ 512 * 2 ^ ((m + 1) * 4) := Nat.mul_le_mul_left _ (card_patches_bound m)
    _ = _ := (pow_add ..).symm

theorem radius_sparse {s : ℕ} (sample : Fin 9 ↪ BitString s) :
    (acceptingTables (radius sample)).card ≤ 2 ^ descriptionBitBound (9 + (s + 1)) := by
  apply (accepting_radius_card sample).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  let m := 9 + (s + 1)
  change 512 + (m + 1) * 4 ≤ descriptionBitBound m
  have hm : 10 ≤ m := by dsimp [m]; omega
  have hmul : 10 * m ≤ m ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right m hm
  have hDesc : 7 * m ^ 2 ≤ descriptionBitBound m := by
    dsimp only [descriptionBitBound]
    have h : 7 ≤ 3 + 4 * (Nat.log2 (m + 1) + 1) := by omega
    have hh := Nat.mul_le_mul_right (m ^ 2) h
    omega
  omega

end Sparsity

/-- For every suffix width with room for nine samples, one sparse linear-size
circuit passes the four-flip tests for every selector and every tail cut. -/
theorem sparse_linear_control (s : ℕ) (hs : 4 ≤ s) :
    ∃ F : BooleanFunction (2 ^ (9 + (s + 1))),
      complexity interpretation (single F) ≤ 16 * 2 ^ (9 + (s + 1)) + 5243395 ∧
      (acceptingTables F).card ≤ 2 ^ descriptionBitBound (9 + (s + 1)) ∧
      ∀ (e : Equiv.Perm (Fin (s + 1))) (h : BooleanFunction s) (f g : BooleanFunction 9)
        (D : Finset (Location s)), D.card ≤ 4 →
        (F (patch D ((splice (mask 9 h) (probe s f) (probe s g)) ∘ tablePerm (liftTail 9 e))) = true ↔ f = g) := by
  have h9 : 9 ≤ 2 ^ s := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hs
    omega
  let bank : Fin 9 ↪ Fin (2 ^ s) :=
    ⟨Fin.castLE h9, fun _ _ h => Fin.ext (congrArg (fun i : Fin (2 ^ s) => i.val) h)⟩
  let sample := bank.trans (BitString.equivFin s).symm.toEmbedding
  exact ⟨radius sample, radius_size sample, radius_sparse sample, radius_transport_tests sample⟩

/-- Changing the prefix coordinates can separate this control from exact MCSP.
The split-bit projection is a prefix probe after exchanging a prefix bit with
the split bit, and it lies outside the original prefix neighborhood. -/
theorem radius_misses_split_projection {s : ℕ} (sample : Fin 9 ↪ BitString s) :
    let T := MCSP.truthTable (9 + (s + 1)) (fun x => x (Fin.natAdd 9 (0 : Fin (s + 1))))
    mcspSquare (9 + (s + 1)) T = true ∧ radius sample T = false := by
  intro T
  have hSize : complexity interpretation
      (single (fun x : BitString (9 + (s + 1)) => x (Fin.natAdd 9 (0 : Fin (s + 1))))) = 0 :=
    complexity_single_proj _
  constructor
  · unfold T
    rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply, hSize]
    exact Nat.zero_le _
  · let f : BooleanFunction 9 := fun _ => true
    let g : BooleanFunction 9 := fun _ => false
    have he : splice (mask 9 (fun _ : BitString s => false)) (probe s f) (probe s g) = T := by
      funext i
      obtain ⟨⟨a,b,t⟩, rfl⟩ := (positionEquiv 9 s).surjective i
      change splice (mask 9 (fun _ : BitString s => false)) (probe s f) (probe s g) (position a b t) =
        T (BitString.equivFin _ (Fin.append a (Fin.cons b t)))
      unfold T splice
      rw [mask_at_position, probe_at_position, probe_at_position, MCSP.truthTable_apply,
        Equiv.symm_apply_apply, Fin.append_right, Fin.cons_zero]
      cases b <;> rfl
    have hTest := radius_tests sample (fun _ => false) f g ∅ (by simp)
    rw [he] at hTest
    have hPatch : patch ∅ T = T := by funext i; simp [patch]
    rw [hPatch] at hTest
    apply Bool.eq_false_of_not_eq_true
    intro h
    have hf := congrFun (hTest.mp h) (fun _ => false)
    cases hf

#print axioms radius_size
#print axioms accepting_radius_card
#print axioms radius_sparse
#print axioms radius_transport_tests
#print axioms sparse_linear_control
#print axioms radius_misses_split_projection

end PvsNP.Frontier.RadiusControl
