module

public import MCSPJointOrbit

/-! Decode a signed subcube from support counts capped at five. A binary
decomposition shares the counts for all coordinates in linear circuit size. -/

@[expose] public section

namespace PvsNP.Frontier.FaceDecoder

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open QuadraticForest
open scoped Classical BigOperators

abbrev Slot (m : ℕ) := Option (Fin m × Bool)

def selects {m : ℕ} (q : Slot m) (z : BitString m) : Bool :=
  q.elim true (fun a => z a.1 == a.2)

def tally {m : ℕ} (f : BooleanFunction m) (q : Slot m) : ℕ :=
  ∑ z : BitString m, if f z = true ∧ selects q z = true then 1 else 0

theorem tally_eq_card {m : ℕ} (f : BooleanFunction m) (q : Slot m) :
    tally f q = (Finset.univ.filter (fun z => f z = true ∧ selects q z = true)).card := by
  rw [tally, ← Finset.sum_filter]
  simp

private theorem sum_split {m : ℕ} (f : BitString (m+1) → ℕ) :
    (∑ z, f z) = (∑ z, f (Fin.cons false z)) + (∑ z, f (Fin.cons true z)) := by
  let e : Bool × BitString m ≃ BitString (m+1) := Fin.consEquiv (fun _ => Bool)
  rw [← Equiv.sum_comp e f, Fintype.sum_prod_type, Fintype.sum_bool]
  exact Nat.add_comm _ _

private theorem tally_total {m : ℕ} (f : BooleanFunction (m+1)) :
    tally f none = tally (fun y => f (Fin.cons false y)) none +
      tally (fun y => f (Fin.cons true y)) none := by
  unfold tally
  rw [sum_split]
  rfl

private theorem tally_head {m : ℕ} (f : BooleanFunction (m+1)) (b : Bool) :
    tally f (some (0,b)) = tally (fun y => f (Fin.cons b y)) none := by
  unfold tally
  rw [sum_split]
  cases b <;> simp [selects]

private theorem tally_tail {m : ℕ} (f : BooleanFunction (m+1)) (i : Fin m) (b : Bool) :
    tally f (some (i.succ,b)) = tally (fun y => f (Fin.cons false y)) (some (i,b)) +
      tally (fun y => f (Fin.cons true y)) (some (i,b)) := by
  unfold tally
  rw [sum_split]
  rfl

def moment {m n : ℕ} (w : BitString m → BooleanFunction n)
    (q : Slot m × Fin 6) (T : BitString n) : Bool :=
  decide (q.2.val ≤ tally (fun z => w z T) q.1)

private theorem synth_sum {n : ℕ} {S : Set (BooleanFunction n)}
    (a b : BitString n → ℕ) (t : Fin 6)
    (ha : ∀ j : Fin 6, (fun T => decide (j.val ≤ a T)) ∈ S)
    (hb : ∀ j : Fin 6, (fun T => decide (j.val ≤ b T)) ∈ S) :
    Synthesis interpretation S {fun T => decide (t.val ≤ a T+b T)} 13 := by
  let sub (j : Fin 6) : Fin 6 := ⟨t.val-j.val, by omega⟩
  let term (j : Fin 6) (T : BitString n) := decide (j.val ≤ a T) && decide ((sub j).val ≤ b T)
  have hOne (j : Fin 6) : Synthesis interpretation S {term j} 1 :=
    (Synthesis.of_mem (ha j)).and (Synthesis.of_mem (hb (sub j)))
  have h := Synthesis.exists_mem Finset.univ term (fun _ => 1) (fun j _ => hOne j)
  have hEq := Synthesis.congr_iff h (g := fun T => decide (t.val ≤ a T+b T)) (fun T => by
    simp only [Finset.mem_univ, true_and, term, sub, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨j, hj₀, hj₁⟩
      omega
    · intro ht
      let j : Fin 6 := ⟨min (a T) t.val, by omega⟩
      exact ⟨j, by dsimp [j]; omega, by dsimp [j]; omega⟩)
  simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] using hEq

def momentBudget (m : ℕ) : ℕ := 400*(2*2^m-(m+2))+2

theorem synth_moments {n : ℕ} (m : ℕ) {S : Set (BooleanFunction n)}
    (w : BitString m → BooleanFunction n) (hw : ∀ z, w z ∈ S) :
    Synthesis interpretation S (Set.range (moment w)) (momentBudget m) := by
  induction m with
  | zero =>
    have hlo : Synthesis interpretation S {fun _ => false} 1 := Synthesis.const false
    have hhi : Synthesis interpretation S {fun _ => true} 1 := Synthesis.const true
    have h := (hlo.union hhi).union (Synthesis.of_mem (hw (zeroVec 0)))
    apply h.mono Set.Subset.rfl ?_ (by decide)
    rintro _ ⟨⟨q,t⟩,rfl⟩
    have hq : q = none := by
      cases q with
      | none => rfl
      | some a => exact Fin.elim0 a.1
    subst q
    have hT (T : BitString n) : tally (fun z => w z T) none = if w (zeroVec 0) T then 1 else 0 := by
      rw [tally, Fintype.sum_unique]
      have he (z : BitString 0) : w z T = w (zeroVec 0) T := by
        rw [Subsingleton.elim z (zeroVec 0)]
      simp [he, selects]
    by_cases ht : t.val = 0
    · left; right
      exact funext fun T => by simp [moment, ht]
    by_cases ht' : t.val = 1
    · right
      exact funext fun T => by
        simp only [moment, hT, ht']
        cases w (zeroVec 0) T <;> decide
    · left; left
      exact funext fun T => by
        simp only [moment, hT]
        split <;> exact decide_eq_false (by omega)
  | succ m ih =>
    let w0 (y : BitString m) := w (Fin.cons false y)
    let w1 (y : BitString m) := w (Fin.cons true y)
    let A := S ∪ (Set.range (moment w0) ∪ Set.range (moment w1))
    have hKids := (ih w0 (fun z => hw _)).union (ih w1 (fun z => hw _))
    have h0 (q : Slot m) (t : Fin 6) : moment w0 (q,t) ∈ A := Or.inr (Or.inl ⟨_,rfl⟩)
    have h1 (q : Slot m) (t : Fin 6) : moment w1 (q,t) ∈ A := Or.inr (Or.inr ⟨_,rfl⟩)
    have hBoth (q : Slot m) (t : Fin 6) :
        Synthesis interpretation A
          {fun T => decide (t.val ≤ tally (fun z => w0 z T) q + tally (fun z => w1 z T) q)} 13 :=
      synth_sum _ _ t (h0 q) (h1 q)
    have hEach (p : Slot (m+1) × Fin 6) : Synthesis interpretation A {moment w p} 13 := by
      rcases p with ⟨q,t⟩
      cases q with
      | none =>
        refine Synthesis.congr_iff (hBoth none t) (fun T => ?_)
        simp only [moment, tally_total, w0, w1]
      | some a =>
        rcases a with ⟨i,b⟩
        cases i using Fin.cases with
        | zero =>
          cases b
          · refine Synthesis.congr_iff ((Synthesis.of_mem (h0 none t)).mono
              Set.Subset.rfl Set.Subset.rfl (by decide)) (fun T => ?_)
            simp [moment, tally_head, w0]
          · refine Synthesis.congr_iff ((Synthesis.of_mem (h1 none t)).mono
              Set.Subset.rfl Set.Subset.rfl (by decide)) (fun T => ?_)
            simp [moment, tally_head, w1]
        | succ i =>
          refine Synthesis.congr_iff (hBoth (some (i,b)) t) (fun T => ?_)
          simp only [moment, tally_tail, w0, w1]
    apply (hKids.trans (Synthesis.family (moment w) (fun _ => 13) hEach)).mono
      Set.Subset.rfl Set.Subset.rfl
    have hRoom : m+2 ≤ 2*2^m := by
      have hm : m < 2^m := Nat.lt_two_pow_self
      omega
    have hCard : Fintype.card (Slot (m+1) × Fin 6) = (1+(m+1)*2)*6 := by
      simp [Fintype.card_option, Nat.add_comm]
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, hCard, momentBudget, pow_succ]
    omega

def face {m : ℕ} (allow : Fin m → Bool → Bool) : BooleanFunction m :=
  fun z => decide (∀ i, allow i (z i) = true)

def recovered {m : ℕ} (R : BooleanFunction m) : BooleanFunction m :=
  face (fun i b => decide (5 ≤ tally R (some (i,b))))

theorem face_cost {m : ℕ} (allow : Fin m → Bool → Bool) :
    complexity interpretation (single (face allow)) ≤ 2*m+1 := by
  have hTerm (i : Fin m) : Synthesis interpretation (inputs m) {fun z => allow i (z i)} 1 := by
    have hProj : Synthesis interpretation (inputs m) {fun z : BitString m => z i} 0 :=
      Synthesis.of_mem ⟨i,rfl⟩
    cases hl : allow i false <;> cases hh : allow i true
    · exact Synthesis.of_forall_eq_const false (fun z => by cases z i <;> assumption)
    · refine Synthesis.congr_iff (hProj.mono Set.Subset.rfl Set.Subset.rfl (by decide)) (fun z => ?_)
      cases z i <;> simp [hl,hh]
    · refine Synthesis.congr_iff hProj.not (fun z => ?_)
      cases z i <;> simp [hl,hh]
    · exact Synthesis.of_forall_eq_const true (fun z => by cases z i <;> assumption)
  have hs := Synthesis.forall_mem Finset.univ (fun i (z : BitString m) => allow i (z i))
    (fun _ => 1) (fun i _ => hTerm i)
  have h := Synthesis.congr_iff hs (g := face allow) (fun z => by simp [face])
  simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.mul_comm] using
    h.complexity_le

theorem synth_face {m n : ℕ} {S : Set (BooleanFunction n)}
    (a : Fin m → Bool → BooleanFunction n) (ha : ∀ i b, a i b ∈ S) :
    Synthesis interpretation S (Set.range (fun z T => face (fun i b => a i b T) z)) (2*2^m) := by
  induction m with
  | zero =>
    refine (Synthesis.const (s := S) true).mono Set.Subset.rfl ?_ (by decide)
    rintro _ ⟨z,rfl⟩
    exact Set.mem_singleton_iff.mpr (funext fun T => by simp [face])
  | succ m ih =>
    let tail (z : BitString m) (T : BitString n) := face (fun i b => a i.succ b T) z
    let A := S ∪ Set.range tail
    have hTail : Synthesis interpretation S (Set.range tail) (2*2^m) :=
      ih (fun i => a i.succ) (fun i b => ha i.succ b)
    have hOne (z : BitString (m+1)) :
        Synthesis interpretation A {fun T => face (fun i b => a i b T) z} 1 := by
      have h0 : Synthesis interpretation A {a 0 (z 0)} 0 := Synthesis.of_mem (Or.inl (ha _ _))
      have h1 : Synthesis interpretation A {tail (Fin.tail z)} 0 := Synthesis.of_mem (Or.inr ⟨_,rfl⟩)
      refine Synthesis.congr_iff (h0.and h1) (fun T => ?_)
      simp only [Bool.and_eq_true, tail, face, Fin.tail, Fin.forall_fin_succ]
      constructor
      · rintro ⟨h0,h1⟩
        exact decide_eq_true ⟨h0,of_decide_eq_true h1⟩
      · intro h
        obtain ⟨h0,h1⟩ := of_decide_eq_true h
        exact ⟨h0,decide_eq_true h1⟩
    apply (hTail.trans (Synthesis.family _ (fun _ => 1) hOne)).mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, pow_succ]
    omega

theorem synth_recovered {m n : ℕ} {S : Set (BooleanFunction n)}
    (w : BitString m → BooleanFunction n) (hw : ∀ z, w z ∈ S) :
    Synthesis interpretation S (Set.range (fun z T => recovered (fun y => w y T) z)) (805*2^m) := by
  have hM := synth_moments m w hw
  let A := S ∪ Set.range (moment w)
  let a (i : Fin m) (b : Bool) := moment w (some (i,b),5)
  have hF := synth_face a (S := A) (fun i b => Or.inr ⟨_,rfl⟩)
  apply (hM.trans hF).mono Set.Subset.rfl Set.Subset.rfl
  have h : 2*(2^m) - (m+2) ≤ 2*2^m := Nat.sub_le _ _
  have h' := Nat.mul_le_mul_left 400 h
  have hN : 0 < 2^m := Nat.two_pow_pos _
  unfold momentBudget
  omega

#print axioms synth_moments
#print axioms synth_recovered

end PvsNP.Frontier.FaceDecoder
