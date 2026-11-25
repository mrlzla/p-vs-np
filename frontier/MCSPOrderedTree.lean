module

public import MCSPGrowingPrefix

/-! Compressed ordered decision trees for the widening experiment. -/

@[expose] public section

namespace PvsNP.Frontier.OrderedTree

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open JuntaRadius (face)
open scoped Classical

inductive Tree (m : ℕ) where
  | leaf (b : Bool)
  | node (i : Fin m) (left right : Tree m)
  deriving DecidableEq

namespace Tree

variable {m : ℕ}

def depth : Tree m → ℕ
  | .leaf _ => 0
  | .node _ L R => max L.depth R.depth + 1

def eval : Tree m → BooleanFunction m
  | .leaf b, _ => b
  | .node i L R, x => if x i then R.eval x else L.eval x

def lift : Tree m → Tree (m + 1)
  | .leaf b => .leaf b
  | .node i L R => .node i.succ L.lift R.lift

@[simp] theorem lift_depth (t : Tree m) : t.lift.depth = t.depth := by
  induction t <;> simp [lift, depth, *]

@[simp] theorem lift_eval (t : Tree m) (b : Bool) (z : BitString m) :
    t.lift.eval (face b z) = t.eval z := by
  induction t <;> simp_all [lift, eval, face]

theorem cost (t : Tree m) : complexity interpretation (single t.eval) + 4 ≤ 5 * 2 ^ t.depth := by
  induction t with
  | leaf b =>
    have h : complexity interpretation (single (Tree.leaf (m := m) b).eval) ≤ 1 :=
      (Synthesis.const (s := inputs m) b).complexity_le
    change _ ≤ 5 * 2 ^ (0 : ℕ)
    omega
  | node i L R ihL ihR =>
    let a : BooleanFunction m := fun x => x i
    let lo : BooleanFunction m := fun x => !a x && L.eval x
    let hi : BooleanFunction m := fun x => a x && R.eval x
    have hA : complexity interpretation (single a) = 0 := complexity_single_proj i
    have hn : complexity interpretation (single (fun x => !a x)) ≤ 1 := by
      have h := complexity_not_le a
      rw [hA] at h
      exact h
    have hLo := complexity_and_le (fun x => !a x) L.eval
    have hHi := complexity_and_le a R.eval
    have hw : (Tree.node i L R).eval = fun x => lo x || hi x := by
      funext x
      cases hb : x i <;> simp [eval, lo, hi, a, hb]
    change complexity interpretation (single (Tree.node i L R).eval) + 4 ≤
      5 * 2 ^ ((max L.depth R.depth) + 1)
    rw [hw, pow_succ']
    have hOr := complexity_or_le lo hi
    change complexity interpretation (single lo) ≤ _ at hLo
    change complexity interpretation (single hi) ≤ _ at hHi
    have hLo' : complexity interpretation (single lo) ≤ complexity interpretation (single L.eval) + 2 :=
      hLo.trans (calc
        _ ≤ 1 + complexity interpretation (single L.eval) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right hn _) _
        _ = _ := by omega)
    have hHi' : complexity interpretation (single hi) ≤ complexity interpretation (single R.eval) + 1 := by
      rw [hA, Nat.zero_add] at hHi
      exact hHi
    have hOut : complexity interpretation (single (fun x => lo x || hi x)) + 4 ≤
        complexity interpretation (single L.eval) + complexity interpretation (single R.eval) + 8 := by
      apply (Nat.add_le_add_right hOr 4).trans
      omega
    have hL := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (le_max_left L.depth R.depth)
    have hR := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (le_max_right L.depth R.depth)
    apply hOut.trans
    omega

end Tree

/-- Compare the reduced children in the common variable order. Identical
children do not require a branch on the first variable. -/
def canonical : (m : ℕ) → BooleanFunction m → Tree m
  | 0, f => .leaf (f (fun _ => false))
  | m + 1, f =>
    let L := canonical m (f ∘ face false)
    let R := canonical m (f ∘ face true)
    if L = R then L.lift else .node 0 L.lift R.lift

@[simp] private theorem face_zero {m : ℕ} (b : Bool) (z : BitString m) : face b z 0 = b := rfl

theorem canonical_eval : ∀ {m : ℕ} (f : BooleanFunction m), (canonical m f).eval = f
  | 0, f => by
    funext x
    have he : (fun _ : Fin 0 => false) = x := funext fun j => Fin.elim0 j
    simp [canonical, Tree.eval, he]
  | m + 1, f => by
    funext x
    obtain ⟨⟨b,z⟩, rfl⟩ := (Fin.consEquiv fun _ : Fin (m + 1) => Bool).surjective x
    change (canonical (m+1) f).eval (face b z) = f (face b z)
    let L := canonical m (f ∘ face false)
    let R := canonical m (f ∘ face true)
    have hL : L.eval = f ∘ face false := canonical_eval _
    have hR : R.eval = f ∘ face true := canonical_eval _
    change (if L = R then L.lift else Tree.node 0 L.lift R.lift).eval (face b z) = _
    by_cases h : L = R
    · rw [ite_eq_left h, Tree.lift_eval]
      cases b
      · exact congrFun hL z
      · exact (congrArg (fun t : Tree m => t.eval z) h).trans (congrFun hR z)
    · rw [ite_eq_right h]
      cases b <;> simp [Tree.eval, hL, hR, Function.comp_apply]

/-- The number of active variables bounds the number of branches on a path. -/
theorem canonical_depth_le_of_support : ∀ {m : ℕ} (f : BooleanFunction m) (S : Finset (Fin m)),
    (∀ x y, (∀ i ∈ S, x i = y i) → f x = f y) → (canonical m f).depth ≤ S.card
  | 0, f, S, _ => by simp [canonical, Tree.depth]
  | m + 1, f, S, h => by
    let L := canonical m (f ∘ face false)
    let R := canonical m (f ∘ face true)
    let rest : Finset (Fin m) := Finset.univ.filter fun i => i.succ ∈ S
    have hRest (b : Bool) : ∀ x y, (∀ i ∈ rest, x i = y i) → (f ∘ face b) x = (f ∘ face b) y := by
      intro x y he
      apply h
      intro i hi
      induction i using Fin.cases with
      | zero => rfl
      | succ j =>
        exact he j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    have hL : L.depth ≤ rest.card := canonical_depth_le_of_support _ rest (hRest false)
    have hR : R.depth ≤ rest.card := canonical_depth_le_of_support _ rest (hRest true)
    have hRestCard : rest.card ≤ (S.erase 0).card := by
      apply Finset.card_le_card_of_injOn Fin.succ
      · intro i hi
        exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero _, (Finset.mem_filter.mp hi).2⟩
      · intro i _ j _ he
        have h := congrArg (fun a : Fin (m + 1) => a.val) he
        apply Fin.ext
        simp only [Fin.val_succ] at h
        omega
    change (if L = R then L.lift else Tree.node 0 L.lift R.lift).depth ≤ _
    by_cases hEq : L = R
    · rw [ite_eq_left hEq, Tree.lift_depth]
      exact hL.trans (hRestCard.trans Finset.card_erase_le)
    · have hMem : (0 : Fin (m+1)) ∈ S := by
        by_contra hn
        apply hEq
        have hF : f ∘ face false = f ∘ face true := by
          funext x
          apply h
          intro i hi
          induction i using Fin.cases with
          | zero => exact (hn hi).elim
          | succ j => rfl
        exact congrArg (canonical m) hF
      rw [ite_eq_right hEq]
      simp only [Tree.depth, Tree.lift_depth]
      have he := Finset.card_erase_add_one hMem
      omega

theorem canonical_depth_le_arity {m : ℕ} (f : BooleanFunction m) :
    (canonical m f).depth ≤ m := by
  have h := canonical_depth_le_of_support f Finset.univ
    (fun x y he => congrArg f (funext fun i => he i (Finset.mem_univ _)))
  simpa only [Finset.card_univ, Fintype.card_fin] using h

theorem depth_le_of_code_support {r m : ℕ} (c : JuntaRadius.CodeFor r m)
    (f : BooleanFunction m)
    (hf : ∀ x y, (∀ j i, c.1 j = .inl i → x i = y i) → f x = f y) :
    (canonical m f).depth ≤ r := by
  let S := (Finset.univ : Finset (Fin r)).biUnion fun j =>
    (c.1 j).elim (fun i => {i}) (fun _ => ∅)
  have hs : S.card ≤ r := calc
    _ ≤ ∑ j : Fin r, ((c.1 j).elim (fun i => ({i} : Finset (Fin m))) (fun _ => ∅)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin r, 1 := by
      apply Finset.sum_le_sum
      intro j _
      cases c.1 j <;> simp
    _ = _ := by simp
  apply le_trans (canonical_depth_le_of_support _ S ?_) hs
  intro x y h
  apply hf x y
  intro j i he
  exact h i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by simp [he]⟩)

theorem value_depends_on_code_support {r m : ℕ} (c : JuntaRadius.CodeFor r m)
    (x y : BitString m) (h : ∀ j i, c.1 j = .inl i → x i = y i) :
    JuntaRadius.value c x = JuntaRadius.value c y := by
  unfold JuntaRadius.value
  apply congrArg c.2
  funext j
  cases he : c.1 j with
  | inl i => exact h j i he
  | inr b => rfl

theorem codeFor_depth {r m : ℕ} (c : JuntaRadius.CodeFor r m) :
    (canonical m (JuntaRadius.value c)).depth ≤ r :=
  depth_le_of_code_support c _ (value_depends_on_code_support c)

#print axioms canonical_eval
#print axioms codeFor_depth
#print axioms Tree.cost

abbrev Label (m : ℕ) := Fin m ⊕ Bool

def liftLabel {m : ℕ} (a : Label m) : Label (m + 1) :=
  a.elim (fun j => .inl j.succ) Sum.inr

private theorem liftLabel_injective {m : ℕ} : Function.Injective (liftLabel (m := m)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [liftLabel]

private theorem liftLabel_ne_root {m : ℕ} (a : Label m) : liftLabel a ≠ .inl 0 := by
  cases a <;> simp [liftLabel]

namespace Tree

variable {m : ℕ}

def labelAt : Tree m → List Bool → Option (Label m)
  | .leaf b, [] => some (.inr b)
  | .leaf _, _ :: _ => none
  | .node i _ _, [] => some (.inl i)
  | .node _ L R, b :: p => (if b then R else L).labelAt p

theorem label_lift (t : Tree m) (p : List Bool) :
    t.lift.labelAt p = (t.labelAt p).map liftLabel := by
  induction t generalizing p with
  | leaf b => cases p <;> rfl
  | node i L R hl hr =>
    cases p with
    | nil => rfl
    | cons b p => cases b <;> simp [lift, labelAt, hl, hr]

theorem label_none (t : Tree m) (p : List Bool) (h : t.depth < p.length) :
    t.labelAt p = none := by
  induction t generalizing p with
  | leaf b =>
    cases p with
    | nil => simp [depth] at h
    | cons => rfl
  | node i L R hl hr =>
    cases p with
    | nil => simp [depth] at h
    | cons b p =>
      have hl' : L.depth < p.length := by
        have hmax := le_max_left L.depth R.depth
        simp [depth] at h
        omega
      have hr' : R.depth < p.length := by
        have hmax := le_max_right L.depth R.depth
        simp [depth] at h
        omega
      cases b
      · exact hl p hl'
      · exact hr p hr'

theorem label_injective (L R : Tree m) (h : ∀ p, L.labelAt p = R.labelAt p) : L = R := by
  induction L generalizing R with
  | leaf b =>
    have he := h []
    cases R <;> simp_all [labelAt]
  | node i L0 L1 ih0 ih1 =>
    have he := h []
    cases R with
    | leaf b => simp [labelAt] at he
    | node j R0 R1 =>
      have hi : i = j := by simpa [labelAt] using he
      have h0 := ih0 R0 (fun p => h (false :: p))
      have h1 := ih1 R1 (fun p => h (true :: p))
      simp [hi, h0, h1]

end Tree

/-- A padded key describes a path up to the given depth. Multiple encodings
of short paths are harmless, and allow a simple fixed wiring at each node. -/
abbrev PathKey (k : ℕ) := Fin (k + 1) × BitString k

def path {k : ℕ} (p : PathKey k) : List Bool := (List.ofFn p.2).take p.1.val

theorem path_length {k : ℕ} (p : PathKey k) : (path p).length ≤ k := by
  simp [path, List.length_take]

private theorem path_surj {k : ℕ} (xs : List Bool) (hs : xs.length ≤ k) :
    ∃ p : PathKey k, path p = xs := by
  let p : PathKey k := (⟨xs.length, by omega⟩, fun j => xs[j.val]?.getD false)
  refine ⟨p, ?_⟩
  apply List.ext_getElem
  · simp [path, p, Nat.min_eq_left hs]
  · intro j h1 h2
    simp only [path] at h1 ⊢
    rw [List.getElem_take, List.getElem_ofFn]
    change xs[j]?.getD false = xs[j]
    rw [List.getElem?_eq_getElem h2]
    rfl

abbrev Key (r m : ℕ) := PathKey (min r m) × Label m

def bit {r m : ℕ} (t : Tree m) (p : Key r m) : Bool :=
  decide (t.depth ≤ r ∧ t.labelAt (path p.1) = some p.2)

def codeSame (r : ℕ) {m : ℕ} (L R : Tree m) : Bool :=
  decide (∀ p : Key r m, bit L p = bit R p)

private theorem option_of_bits {A : Type} (x y : Option A)
    (h : ∀ a : A, (x = some a ↔ y = some a)) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some a => have he := (h a).mpr rfl; cases he
  | some a => exact ((h a).mp rfl).symm

theorem codeSame_iff {r m : ℕ} {L R : Tree m}
    (hl : L.depth ≤ min r m) (hr : R.depth ≤ min r m) :
    codeSame r L R = true ↔ L = R := by
  unfold codeSame
  rw [decide_eq_true_eq]
  constructor
  · intro h
    apply Tree.label_injective
    intro p
    by_cases hp : p.length ≤ min r m
    · obtain ⟨q, hq⟩ := path_surj p hp
      apply option_of_bits
      intro a
      have he := Bool.eq_iff_iff.mp (h (q,a))
      simpa only [bit, decide_eq_true_eq, hl.trans (min_le_left _ _), hr.trans (min_le_left _ _),
        true_and, hq] using he
    · rw [Tree.label_none L p (by omega), Tree.label_none R p (by omega)]
  · rintro rfl p
    rfl

def join {m : ℕ} (L R : Tree m) : Tree (m + 1) :=
  if L = R then L.lift else .node 0 L.lift R.lift

private theorem both_of_join {m : ℕ} {L R : Tree m} {k : ℕ}
    (h : (join L R).depth ≤ k) : L.depth ≤ k ∧ R.depth ≤ k := by
  by_cases he : L = R
  · subst R
    simpa [join] using h
  · simp only [join, he, ite_false, Tree.depth, Tree.lift_depth] at h
    exact ⟨(le_max_left ..).trans (Nat.le_of_succ_le h), (le_max_right ..).trans (Nat.le_of_succ_le h)⟩

private theorem depth_join_eq {r m : ℕ} {L R : Tree m} (hL : L.depth ≤ m) (hR : R.depth ≤ m)
    (k : Fin (r + 1)) :
    decide ((join L R).depth ≤ k.val) =
      ((decide (L.depth ≤ k.val) && decide (R.depth ≤ k.val)) &&
       (codeSame r L R || (decide (0 < k.val) && decide (L.depth ≤ k.val - 1) && decide (R.depth ≤ k.val - 1)))) := by
  by_cases h : L.depth ≤ k.val ∧ R.depth ≤ k.val
  · have hKr : k.val ≤ r := by omega
    have hS := codeSame_iff (r := r) (L := L) (R := R)
      (le_min (h.1.trans hKr) hL) (le_min (h.2.trans hKr) hR)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hS]
    by_cases he : L = R
    · subst R
      simp [join, h.1]
    · simp only [join, he, ite_false, Tree.depth, Tree.lift_depth, false_or]
      have hM : max L.depth R.depth ≤ k.val := max_le h.1 h.2
      constructor
      · intro hJ
        refine ⟨h,⟨by omega,?_⟩,?_⟩ <;> omega
      · rintro ⟨_,⟨hk,h0⟩,h1⟩
        have hm := max_le h0 h1
        omega
  · have hn : ¬(join L R).depth ≤ k.val := fun h' => h (both_of_join h')
    by_cases h0 : L.depth ≤ k.val
    · have h1 : ¬R.depth ≤ k.val := fun h1 => h ⟨h0,h1⟩
      simp [hn, h1]
    · simp [hn, h0]


section Synthesis

variable {l m r : ℕ}

def codeWire (r : ℕ) {m : ℕ} (f : BitString m → BooleanFunction l) (p : Key r m) :
    BooleanFunction l := fun X => bit (canonical m (fun z => f z X)) p

def depthWire (r : ℕ) {m : ℕ} (f : BitString m → BooleanFunction l) (k : Fin (r+1)) :
    BooleanFunction l := fun X => decide ((canonical m (fun z => f z X)).depth ≤ k.val)

def states (r : ℕ) {m : ℕ} (f : BitString m → BooleanFunction l) :
    Set (BooleanFunction l) := Set.range (depthWire r f) ∪ Set.range (codeWire r f)

private def comparison (r : ℕ) (L R : BitString m → BooleanFunction l) : BooleanFunction l :=
  fun X => codeSame r (canonical m (fun z => L z X)) (canonical m (fun z => R z X))

private def padded (r : ℕ) (f : BitString m → BooleanFunction l) (p : List Bool) (a : Label (m+1)) :
    BooleanFunction l := fun X =>
      let t := canonical m (fun z => f z X)
      decide (t.depth ≤ r ∧ t.lift.labelAt p = some a)

private theorem padded_cost {s : Set (BooleanFunction l)} (f : BitString m → BooleanFunction l)
    (hc : ∀ k, codeWire r f k ∈ s) (p : List Bool) (a : Label (m+1)) :
    Synthesis interpretation s {padded r f p a} 1 := by
  have hFalse (h : ∀ X, padded r f p a X = false) :
      Synthesis interpretation s {padded r f p a} 1 := Synthesis.of_forall_eq_const false h
  by_cases hp : p.length ≤ min r m
  · obtain ⟨key, hkey⟩ := path_surj p hp
    have hLift (b : Label m) (hb : a = liftLabel b) :
        Synthesis interpretation s {padded r f p a} 1 := by
      have he : padded r f p a = codeWire r f (key,b) := by
        funext X
        apply Bool.eq_iff_iff.mpr
        simp only [padded, codeWire, bit, decide_eq_true_eq, Tree.label_lift, hkey, hb]
        generalize (canonical m (fun z => f z X)).labelAt p = v
        cases v with
        | none => simp
        | some v => simp only [Option.map_some, Option.some.injEq, liftLabel_injective.eq_iff]
      rw [he]
      exact (Synthesis.of_mem (hc (key,b))).mono Set.Subset.rfl Set.Subset.rfl (by decide)
    cases a with
    | inr b => exact hLift (.inr b) rfl
    | inl i =>
      induction i using Fin.cases with
      | zero =>
        apply hFalse
        intro X
        simp only [padded, Tree.label_lift, decide_eq_false_iff_not]
        generalize (canonical m (fun z => f z X)).labelAt p = v
        cases v <;> simp [liftLabel_ne_root]
      | succ j => exact hLift (.inl j) rfl
  · apply hFalse
    intro X
    apply decide_eq_false
    rintro ⟨hr, h⟩
    have he := canonical_depth_le_arity (fun z => f z X)
    have ht := lt_of_le_of_lt (le_min hr he) (lt_of_not_ge hp)
    rw [Tree.label_none _ _ (by simpa only [Tree.lift_depth] using ht)] at h
    cases h

private theorem comparison_cost {s : Set (BooleanFunction l)} (L R : BitString m → BooleanFunction l)
    (hL : ∀ k, codeWire r L k ∈ s) (hR : ∀ k, codeWire r R k ∈ s) :
    Synthesis interpretation s {comparison r L R} (Fintype.card (Key r m) * 6 + 1) := by
  let test (k : Key r m) (X : BitString l) := !(codeWire r L k X ^^ codeWire r R k X)
  have he (k : Key r m) : Synthesis interpretation s {test k} 5 :=
    ((Synthesis.of_mem (hL k)).xor (Synthesis.of_mem (hR k))).not
  have h := Synthesis.forall_mem Finset.univ test (fun _ => 5) (fun k _ => he k)
  have hEq (X : BitString l) : (∀ i ∈ (Finset.univ : Finset (Key r m)), test i X = true) ↔
      comparison r L R X = true := by
    simp only [comparison, codeSame, decide_eq_true_eq, Finset.mem_univ, true_implies]
    apply forall_congr'
    intro k
    change (!(codeWire r L k X ^^ codeWire r R k X)) = true ↔
      codeWire r L k X = codeWire r R k X
    generalize codeWire r L k X = x
    generalize codeWire r R k X = y
    cases x <;> cases y <;> decide
  have hs' := Synthesis.congr_iff h (g := comparison r L R) (fun X => by
    simp only [decide_eq_true_eq]
    exact hEq X)
  exact hs'.mono Set.Subset.rfl Set.Subset.rfl (by simp [Finset.sum_const, smul_eq_mul])

private theorem depthWire_cost {s : Set (BooleanFunction l)}
    (f : BitString (m+1) → BooleanFunction l)
    (hL : ∀ k, depthWire r (f ∘ face false) k ∈ s) (hR : ∀ k, depthWire r (f ∘ face true) k ∈ s)
    (hCompare : comparison r (f ∘ face false) (f ∘ face true) ∈ s) (k : Fin (r+1)) :
    Synthesis interpretation s {depthWire r f k} 4 := by
  let low := depthWire r (f ∘ face false)
  let high := depthWire r (f ∘ face true)
  let comp := comparison r (f ∘ face false) (f ∘ face true)
  let j : Fin (r+1) := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le ..) k.isLt⟩
  let smaller : BooleanFunction l := fun X => decide (0 < k.val) && low j X && high j X
  have hBoth : Synthesis interpretation s {fun X => low k X && high k X} 1 :=
    (Synthesis.of_mem (hL k)).and (Synthesis.of_mem (hR k))
  have hSmaller : Synthesis interpretation s {smaller} 1 := by
    by_cases h : 0 < k.val
    · have he : smaller = fun X => low j X && high j X := by
        funext X
        simp [smaller, h]
      rw [he]
      exact (Synthesis.of_mem (hL j)).and (Synthesis.of_mem (hR j))
    · exact Synthesis.of_forall_eq_const false (fun X => by simp [smaller, h])
  have hGate := hBoth.and ((Synthesis.of_mem hCompare).or hSmaller)
  have he : depthWire r f k = fun X => (low k X && high k X) && (comp X || smaller X) := by
    funext X
    exact depth_join_eq (canonical_depth_le_arity _) (canonical_depth_le_arity _) k
  rwa [he]

private theorem synth_mux {s : Set (BooleanFunction l)} {c a b : BooleanFunction l}
    (hc : c ∈ s) (ha : Synthesis interpretation s {a} 1)
    (hb : Synthesis interpretation s {b} 1) :
    Synthesis interpretation s {fun X => if c X then a X else b X} 6 := by
  have h := ((Synthesis.of_mem hc).and ha).or (((Synthesis.of_mem hc).not).and hb)
  apply Synthesis.congr_iff h
  intro X
  cases c X <;> simp

private theorem codeWire_cost {s : Set (BooleanFunction l)}
    (f : BitString (m+1) → BooleanFunction l)
    (hL : ∀ p, codeWire r (f ∘ face false) p ∈ s) (hR : ∀ p, codeWire r (f ∘ face true) p ∈ s)
    (hCompare : comparison r (f ∘ face false) (f ∘ face true) ∈ s)
    (hDepth : depthWire r f (Fin.last r) ∈ s) (k : Key r (m+1)) :
    Synthesis interpretation s {codeWire r f k} 7 := by
  let read0 := f ∘ face false
  let read1 := f ∘ face true
  let p := path k.1
  let a := k.2
  let yes := padded r read0 p a
  let no : BooleanFunction l :=
    match p with
    | [] => fun _ => decide (a = .inl 0)
    | b :: tail => if b then padded r read1 tail a else padded r read0 tail a
  have hNo : Synthesis interpretation s {no} 1 := by
    cases hp : p with
    | nil => simpa only [no, hp] using (Synthesis.const (s := s) (decide (a = .inl 0)))
    | cons b tail =>
      cases b
      · simpa [no, hp] using padded_cost read0 hL tail a
      · simpa [no, hp] using padded_cost read1 hR tail a
  have hYes : Synthesis interpretation s {yes} 1 := padded_cost read0 hL p a
  have hMerge := (Synthesis.of_mem hDepth).and (synth_mux hCompare hYes hNo)
  have he : codeWire r f k = fun X => depthWire r f (Fin.last r) X &&
      (if comparison r read0 read1 X then yes X else no X) := by
    funext X
    let L := canonical m (fun z => read0 z X)
    let R := canonical m (fun z => read1 z X)
    let T := join L R
    change decide (T.depth ≤ r ∧ T.labelAt p = some a) =
      (decide (T.depth ≤ r) && if codeSame r L R then yes X else no X)
    by_cases ht : T.depth ≤ r
    · have hParts : L.depth ≤ r ∧ R.depth ≤ r := both_of_join ht
      have hSmall := codeSame_iff (r := r) (L := L) (R := R)
        (le_min hParts.1 (canonical_depth_le_arity _)) (le_min hParts.2 (canonical_depth_le_arity _))
      by_cases he : L = R
      · have he' : codeSame r L R = true := hSmall.mpr he
        have ht' : T = L.lift := by simp [T, join, he]
        simp only [ht, true_and, decide_true, Bool.true_and, he', ite_true]
        rw [ht']
        simp [yes, padded, L, hParts.1]
      · have he' : codeSame r L R = false := Bool.eq_false_of_not_eq_true fun h => he (hSmall.mp h)
        simp only [ht, true_and, decide_true, Bool.true_and, he', Bool.false_eq_true, ite_false]
        cases hp : p with
        | nil => simp [T, join, he, Tree.labelAt, no, hp, eq_comm]
        | cons b tl =>
          cases b <;> simp [T, join, he, Tree.labelAt, no, hp, padded, L, R, hParts]
    · simp [ht]
  rwa [he]

end Synthesis


def levelCost (r m : ℕ) : ℕ := 20 * ((r + 3) * (m + 3)) * 2 ^ min r m

def treeBudget (r : ℕ) : ℕ → ℕ
  | 0 => levelCost r 0
  | m + 1 => 2 * treeBudget r m + levelCost r (m + 1)

private theorem cardKey (r m : ℕ) : Fintype.card (Key r m) =
    (min r m + 1) * 2 ^ min r m * (m + 2) := by
  simp only [Key, PathKey, Label, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool,
    BitString.card]

private theorem key_mono (r m : ℕ) : Fintype.card (Key r m) ≤ Fintype.card (Key r (m+1)) := by
  rw [cardKey, cardKey]
  have h : min r m ≤ min r (m+1) := min_le_min le_rfl (Nat.le_succ _)
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.pow_le_pow_right (by decide) h))
    (by omega)

private theorem gate_sum_le (r m : ℕ) :
    (Fintype.card (Key r m) * 6 + 1) + (r+1)*4 + Fintype.card (Key r (m+1))*7 ≤ levelCost r (m+1) := by
  let q := ((r+3)*(m+1+3)) * 2 ^ min r (m+1)
  have hKey : Fintype.card (Key r (m+1)) ≤ q := by
    rw [cardKey]
    have h : min r (m+1) + 1 ≤ r+3 := by have := min_le_left r (m+1); omega
    calc
      _ = ((min r (m+1)+1)*(m+1+2)) * 2 ^ min r (m+1) := by ring
      _ ≤ q := Nat.mul_le_mul_right _ (Nat.mul_le_mul h (by omega))
  have hp : 1 ≤ 2 ^ min r (m+1) := Nat.two_pow_pos _
  have hr : r+1 ≤ q := calc
    _ ≤ (r+3) * 1 * 1 := by omega
    _ ≤ q := Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) hp
  have hh := key_mono r m
  have he : levelCost r (m+1) = 20*q := by simp [levelCost, q, Nat.mul_assoc]
  rw [he]
  omega

theorem synth_states (r : ℕ) {l m : ℕ} (s : Set (BooleanFunction l))
    (f : BitString m → BooleanFunction l) (hf : ∀ x, f x ∈ s) :
    Synthesis interpretation s (states r f) (treeBudget r m) := by
  induction m with
  | zero =>
    let z : BitString 0 := fun _ => false
    have hD (k : Fin (r+1)) : Synthesis interpretation s {depthWire r f k} 1 :=
      Synthesis.of_forall_eq_const true (by intro X; simp [depthWire, canonical, Tree.depth])
    have hC (p : Key r 0) : Synthesis interpretation s {codeWire r f p} 1 := by
      have hp : path p.1 = [] := by
        have hl := path_length p.1
        simp only [min_zero] at hl
        exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
      obtain ⟨k,b⟩ := p
      change path k = [] at hp
      cases b with
      | inl i => exact i.elim0
      | inr b =>
        have h := Synthesis.literal (hf z) b
        apply Synthesis.congr_iff h
        intro X
        simp [codeWire, bit, canonical, Tree.depth, Tree.labelAt, hp, z]
    have hd := Synthesis.family (depthWire r f) (fun _ => 1) hD
    have hc := Synthesis.family (codeWire r f) (fun _ => 1) hC
    apply (hd.union hc).mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.mul_one,
      treeBudget, levelCost, cardKey, min_zero]
    omega
  | succ m ih =>
    let L := f ∘ face false
    let R := f ∘ face true
    have hL := ih L (fun x => hf (face false x))
    have hR := ih R (fun x => hf (face true x))
    let base := s ∪ (states r L ∪ states r R)
    let together := base ∪ {comparison r L R}
    have hCL (k) : codeWire r L k ∈ base := Or.inr (Or.inl (Or.inr ⟨k,rfl⟩))
    have hCR (k) : codeWire r R k ∈ base := Or.inr (Or.inr (Or.inr ⟨k,rfl⟩))
    have hEq := comparison_cost L R hCL hCR
    have hd (k) : Synthesis interpretation together {depthWire r f k} 4 :=
      depthWire_cost f (fun j => Or.inl (Or.inr (Or.inl (Or.inl ⟨j,rfl⟩))))
        (fun j => Or.inl (Or.inr (Or.inr (Or.inl ⟨j,rfl⟩)))) (Or.inr rfl) k
    let avail := together ∪ Set.range (depthWire r f)
    have hc (p) : Synthesis interpretation avail {codeWire r f p} 7 :=
      codeWire_cost f (fun j => Or.inl (Or.inl (hCL j))) (fun j => Or.inl (Or.inl (hCR j)))
        (Or.inl (Or.inr rfl)) (Or.inr ⟨Fin.last r,rfl⟩) p
    have hDepth := Synthesis.family (depthWire r f) (fun _ => 4) hd
    have hCode := Synthesis.family (codeWire r f) (fun _ => 7) hc
    have hBuild := (hL.union hR).trans (hEq.trans (hDepth.comp hCode))
    apply hBuild.mono Set.Subset.rfl Set.Subset.rfl
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, treeBudget, two_mul]
    have hh := gate_sum_le r m
    omega

private def baseFactor (r : ℕ) : ℕ := 20 * (r + 3) ^ 2

private theorem level_le_low {r m : ℕ} (h : m ≤ r) : levelCost r m ≤ baseFactor r * 2 ^ m := by
  rw [levelCost, min_eq_right h, baseFactor, pow_two]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul_left _ (by omega)

private theorem level_le_high {r m : ℕ} (h : r ≤ m) :
    levelCost r m ≤ baseFactor r * (m - r + 1) * 2 ^ r := by
  rw [levelCost, min_eq_left h, baseFactor, pow_two]
  apply Nat.mul_le_mul_right
  have hm : m + 3 ≤ (r + 3) * (m - r + 1) := by
    let d := m - r
    have he : m = r + d := by dsimp [d]; omega
    have hd : d ≤ (r+3) * d := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right d (by omega : 1 ≤ r+3)
    have hh : m + 3 ≤ (r + 3) * (d + 1) := by rw [Nat.mul_add]; omega
    exact hh
  calc
    _ ≤ 20 * ((r + 3) * ((r + 3) * (m - r + 1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ = _ := by ring

private theorem treeBudget_le (r m : ℕ) :
    treeBudget r m ≤ baseFactor r * (r + 4) * 2 ^ m := by
  let C := baseFactor r
  have hLow : ∀ m ≤ r, treeBudget r m ≤ C * (m+1) * 2^m := by
    intro m
    induction m with
    | zero =>
      intro _
      simpa [treeBudget, C] using level_le_low (r := r) (m := 0) (Nat.zero_le r)
    | succ m ih =>
      intro hm
      have h0 := ih (by omega)
      have h1 := level_le_low hm
      change levelCost r (m+1) ≤ C * 2^(m+1) at h1
      rw [treeBudget, pow_succ' 2 m]
      calc
        _ ≤ 2 * (C * (m+1) * 2^m) + C * 2^(m+1) :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 h0) h1
        _ = _ := by rw [pow_succ' 2 m]; ring
  by_cases hmr : m ≤ r
  · exact (hLow m hmr).trans (Nat.mul_le_mul_right (2^m) (Nat.mul_le_mul_left C (by omega)))
  · have hHigh : ∀ m, r ≤ m →
        treeBudget r m + C * (m-r+3) * 2^r ≤ C * (r+4) * 2^m := by
      intro n hn
      refine Nat.le_induction
        (P := fun m _ => treeBudget r m + C * (m-r+3) * 2^r ≤ C * (r+4) * 2^m) ?_ ?_ n hn
      · have h := Nat.add_le_add_right (hLow r le_rfl) (C * 3 * 2^r)
        simp only [Nat.sub_self, Nat.zero_add]
        exact h.trans (by ring_nf; omega)
      · intro j hj ih
        have h1 := level_le_high (show r ≤ j+1 by omega)
        change levelCost r (j+1) ≤ C * (j+1-r+1) * 2^r at h1
        rw [treeBudget]
        calc
          _ ≤ 2 * treeBudget r j + C * (j+1-r+1) * 2^r + C * (j+1-r+3) * 2^r := by omega
          _ = 2 * (treeBudget r j + C * (j-r+3) * 2^r) := by
            rw [show j+1-r+1 = j-r+2 by omega, show j+1-r+3 = j-r+4 by omega]
            ring
          _ ≤ 2 * (C * (r+4) * 2^j) := Nat.mul_le_mul_left 2 ih
          _ = _ := by rw [pow_succ' 2 j]; ring
    exact (Nat.le_add_right _ _).trans (hHigh m (by omega))

theorem treeBudget_poly (r m : ℕ) : treeBudget r m ≤ 20 * (r + 4)^3 * 2^m := by
  apply (treeBudget_le r m).trans
  have h : (r+3)^2 ≤ (r+4)^2 := Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 20 * (r+4)^2 * (r+4) * 2^m := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 20 h))
    _ = _ := by ring

#print axioms synth_states
#print axioms treeBudget_poly

end PvsNP.Frontier.OrderedTree

