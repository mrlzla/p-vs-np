import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_060_aux

open PEqualNP.MetaComplexity

def bit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bit_xor (x y : Bool) : bit (x ^^ y) = bit x + bit y := by
  cases x <;> cases y <;> decide

def parity {n : ℕ} (x : Fin n → Bool) : ZMod 2 := ∑ i, bit (x i)

def odd {n : ℕ} (x : Fin n → Bool) : Bool := decide (parity x = 1)

theorem zmod_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem bit_odd {n : ℕ} (x : Fin n → Bool) : bit (odd x) = parity x := by
  unfold odd
  rcases zmod_cases (parity x) with h | h <;> simp [h, bit]

theorem odd_xor {n : ℕ} (x y : Fin n → Bool) :
    odd (fun i => x i ^^ y i) = (odd x ^^ odd y) := by
  have inj : Function.Injective bit := by
    intro a b
    cases a <;> cases b <;> decide
  apply inj
  simp only [bit_odd, bit_xor, parity, Finset.sum_add_distrib]

theorem parity_eq_card {n : ℕ} (x : Fin n → Bool) :
    parity x = ((Finset.univ.filter fun i => x i = true).card : ZMod 2) := by
  have h : (∑ i : Fin n, if x i = true then (1 : ℕ) else 0) =
      (Finset.univ.filter fun i => x i = true).card := by
    rw [← Finset.sum_filter]
    simp
  rw [← h, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> rfl

theorem odd_false_iff {n : ℕ} (x : Fin n → Bool) :
    odd x = false ↔ (Finset.univ.filter fun i => x i = true).card % 2 = 0 := by
  have hz : ∀ z : ZMod 2, z ≠ 1 ↔ z = 0 := by
    intro z
    rcases zmod_cases z with rfl | rfl <;> decide
  unfold odd
  exact decide_eq_false_iff_not.trans ((hz (parity x)).trans (by
    rw [parity_eq_card, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_iff_mod_eq_zero))

def pulse {n : ℕ} (i : Fin n) (j : Fin n) : Bool := decide (j = i)

theorem odd_pulse {n : ℕ} (i : Fin n) : odd (pulse i) = true := by
  apply decide_eq_true
  unfold parity
  rw [Finset.sum_eq_single i]
  · simp [pulse, bit]
  · intro j _ hj
    simp [pulse, bit, hj]
  · simp

def flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) (j : Fin n) : Bool := x j ^^ pulse i j

theorem flip_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) : flip i (flip i x) = x := by
  funext j
  unfold flip
  cases x j <;> cases pulse i j <;> rfl

theorem odd_flip {n : ℕ} (i : Fin n) (x : Fin n → Bool) : odd (flip i x) = !odd x := by
  change odd (fun j => x j ^^ pulse i j) = _
  rw [odd_xor, odd_pulse]
  cases odd x <;> rfl

noncomputable def parityClass (n : ℕ) (b : Bool) : Finset (Fin n → Bool) := open scoped Classical in
  Finset.univ.filter fun x => odd x = b

theorem card_parityClass {n : ℕ} (i : Fin n) (b : Bool) :
    (parityClass n b).card = 2 ^ (n - 1) := by
  classical
  have bound (d : Bool) : (parityClass n d).card ≤ (parityClass n (!d)).card := by
    apply Finset.card_le_card_of_injOn (flip i)
    · intro x hx
      have h := (Finset.mem_filter.mp hx).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (odd_flip i x).trans (congrArg Bool.not h)⟩
    · intro x _ y _ h
      simpa only [flip_flip] using congrArg (flip i) h
  have heq : (parityClass n false).card = (parityClass n true).card :=
    le_antisymm (bound false) (bound true)
  have hSet : (Finset.univ : Finset (Fin n → Bool)).filter (fun x => ¬ odd x = false) =
      parityClass n true := by
    ext x
    cases h : odd x <;> simp [parityClass, h]
  have hSum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → Bool))) (p := fun x => odd x = false)
  rw [hSet, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hSum
  change (parityClass n false).card + (parityClass n true).card = 2 ^ n at hSum
  have hn : n - 1 + 1 = n := by have := i.isLt; omega
  have hp : 2 ^ n = (2 : ℕ) ^ (n - 1) + 2 ^ (n - 1) := by rw [← hn, pow_succ', two_mul]; simp [hn]
  rw [hp] at hSum
  cases b <;> omega

abbrev Grid (r c : ℕ) := Fin r → Fin c → Bool

def transform {r c : ℕ} (first : Fin c) (x : Fin c → Bool) (T : Grid r c) : Grid r c :=
  fun i j => T i j ^^ (odd (T i) && flip first x j)

theorem transformed_parity {r c : ℕ} (first : Fin c) (x : Fin c → Bool) (T : Grid r c) (i : Fin r) :
    odd (transform first x T i) = (odd (T i) && odd x) := by
  unfold transform
  rw [odd_xor]
  cases ht : odd (T i)
  · simp only [Bool.false_and, Bool.false_xor]
    simp [odd, parity, bit]
  · simp only [Bool.true_and, Bool.true_xor, odd_flip, Bool.not_not]

theorem recover {r c : ℕ} (first : Fin c) (x : Fin c → Bool)
    (T U : Grid r c) (h : transform first x T = transform first x U)
    (hp : ∀ i, odd (T i) = odd (U i)) : T = U := by
  funext i j
  have hh := congrFun (congrFun h i) j
  change (T i j ^^ (odd (T i) && flip first x j)) =
    (U i j ^^ (odd (U i) && flip first x j)) at hh
  rw [hp i] at hh
  have h' := congrArg (fun b => b ^^ (odd (U i) && flip first x j)) hh
  simpa using h'

theorem transform_injective_odd {r c : ℕ} (first : Fin c) (x : Fin c → Bool) (hx : odd x = true) :
    Function.Injective (transform (r := r) first x) := by
  intro T U h
  apply recover first x T U h
  intro i
  have hh := congrArg (fun W : Grid r c => odd (W i)) h
  simpa only [transformed_parity, hx, Bool.and_true] using hh

theorem transform_even_plus_parities {r c : ℕ} (first : Fin c) (x : Fin c → Bool) :
    Function.Injective (fun T : Grid r c => (transform first x T, fun i => odd (T i))) := by
  intro T U h
  apply recover first x T U (congrArg Prod.fst h)
  exact congrFun (congrArg Prod.snd h)

def flatten {r c : ℕ} (T : Grid r c) : List Bool :=
  List.ofFn fun k : Fin (r * c) =>
    let ij := finProdFinEquiv.symm k
    T ij.1 ij.2

theorem flatten_length {r c : ℕ} (T : Grid r c) : (flatten T).length = r * c := by
  simp [flatten]

theorem flatten_read {r c : ℕ} (T : Grid r c) (i : Fin r) (j : Fin c) :
    (flatten T).getD (i.val * c + j.val) false = T i j := by
  let k : Fin (r * c) := finProdFinEquiv (i, j)
  have hval : k.val = i.val * c + j.val := by
    change j.val + c * i.val = _
    ac_rfl
  rw [← hval]
  have hk : k.val < (flatten T).length := by rw [flatten_length]; exact k.isLt
  rw [List.getD_eq_getElem _ _ hk]
  simp only [flatten, List.getElem_ofFn]
  change T (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = _
  rw [show finProdFinEquiv.symm k = (i, j) from finProdFinEquiv.symm_apply_apply _]

theorem flatten_injective {r c : ℕ} : Function.Injective (@flatten r c) := by
  intro T U h
  funext i j
  have he := congrArg (fun L : List Bool => L.getD (i.val * c + j.val) false) h
  change (flatten T).getD _ false = (flatten U).getD _ false at he
  rwa [flatten_read T i j, flatten_read U i j] at he

theorem row_count_eq {r c : ℕ} (T : Grid r c) (i : Fin r) :
    ((List.range c).filter (fun j => (flatten T).getD (i.val * c + j) false = true)).length =
      (Finset.univ.filter fun j => T i j = true).card := by
  classical
  let value := fun j => (flatten T).getD (i.val * c + j) false
  have hrow : (List.range c).map value = List.ofFn (T i) := by
    apply List.ext_getElem (by simp)
    intro j hj hrowj
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact flatten_read T i ⟨j, by simpa using hrowj⟩
  have hcount : (((List.range c).filter fun j => value j = true)).length =
      (List.ofFn (T i)).count true := by
    rw [← hrow, List.count_eq_countP, List.countP_eq_length_filter, List.filter_map]
    simp [Function.comp_def]
  have hcount' : (List.ofFn (T i)).count true = (Finset.univ.filter fun j => T i j = true).card := by
    rw [List.ofFn_eq_map]
    simp only [List.count_eq_countP, List.countP_eq_length_filter, List.filter_map, List.length_map,
      beq_true]
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange c).filter _), List.toFinset_filter]
    congr 1
    simp
  exact hcount.trans hcount'

def RowEven (r c : ℕ) (T : List Bool) : Prop :=
  ∀ i : ℕ, i < r →
    ((List.range c).filter fun j => T.getD (i * c + j) false = true).length % 2 = 0

theorem flatten_rowEven {r c : ℕ} (T : Grid r c) (h : ∀ i, odd (T i) = false) :
    RowEven r c (flatten T) := by
  intro i hi
  rw [row_count_eq T ⟨i, hi⟩]
  exact (odd_false_iff _).mp (h ⟨i, hi⟩)

theorem split_unique (s t : ℕ) (A B : List Bool)
    (h : List.replicate s true ++ false :: A = List.replicate t true ++ false :: B) :
    s = t ∧ A = B := by
  induction s generalizing t with
  | zero =>
    cases t with
    | zero =>
      simp only [List.replicate_zero, List.nil_append] at h
      exact ⟨rfl, (List.cons.inj h).2⟩
    | succ t => simp [List.replicate_succ] at h
  | succ s ih =>
    cases t with
    | zero => simp [List.replicate_succ] at h
    | succ t =>
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h
      obtain ⟨he, hAB⟩ := ih t (List.cons.inj h).2
      exact ⟨congrArg Nat.succ he, hAB⟩

theorem word_mem (m s : ℕ) (T : List Bool) (hT : T.length = 2 ^ m) :
    List.replicate s true ++ false :: T ∈ MCSP ↔ HasCircuitSize m (tableFun m T) s := by
  constructor
  · rintro ⟨n, t, U, he, hu, hc⟩
    obtain ⟨rfl, rfl⟩ := split_unique s t T U he
    have hn : m = n := Nat.pow_right_injective (le_refl 2) (hT.symm.trans hu)
    subst n
    exact hc
  · intro hc
    exact ⟨m, s, T, rfl, hT, hc⟩

def Easy (m s : ℕ) : Set (List Bool) :=
  {T | T.length = 2 ^ m ∧ HasCircuitSize m (tableFun m T) s}

def HardEven (r c m s : ℕ) : Set (List Bool) :=
  {T | T.length = 2 ^ m ∧ RowEven r c T ∧ ¬ HasCircuitSize m (tableFun m T) s}

noncomputable def bad {r c : ℕ} (m s : ℕ) (first : Fin c) (x : Fin c → Bool) :
    Finset (Grid r c) := open scoped Classical in
  Finset.univ.filter fun T =>
    let U := flatten (transform first x T)
    if odd x then HasCircuitSize m (tableFun m U) s else ¬ HasCircuitSize m (tableFun m U) s

theorem card_bad_even {r c : ℕ} (m s : ℕ) (hlen : r * c = 2 ^ m)
    (first : Fin c) (x : Fin c → Bool) (hx : odd x = false) :
    (bad (r := r) m s first x).card ≤ (HardEven r c m s).ncard * 2 ^ r := by
  classical
  have hf : (HardEven r c m s).Finite :=
    (List.finite_length_eq Bool (2 ^ m)).subset fun _ h => h.1
  have hcard := Finset.card_le_card_of_injOn (s := bad (r := r) m s first x)
    (t := hf.toFinset ×ˢ (Finset.univ : Finset (Fin r → Bool)))
    (fun T : Grid r c => (flatten (transform first x T), fun i => odd (T i)))
    (fun T hT => by
      apply Finset.mem_product.mpr
      refine ⟨hf.mem_toFinset.mpr ⟨(flatten_length _).trans hlen, ?_, ?_⟩, Finset.mem_univ _⟩
      · apply flatten_rowEven
        intro i
        rw [transformed_parity, hx, Bool.and_false]
      · have hh := (Finset.mem_filter.mp hT).2
        simpa [hx] using hh)
    (fun T _ U _ he => by
      have hparity := congrArg (fun p : List Bool × (Fin r → Bool) => p.2) he
      exact (transform_even_plus_parities first x) (Prod.ext
        (flatten_injective (congrArg Prod.fst he)) hparity))
  rwa [Finset.card_product, ← Set.ncard_eq_toFinset_card _ hf, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin] at hcard

theorem card_bad_odd {r c : ℕ} (m s : ℕ) (hlen : r * c = 2 ^ m)
    (first : Fin c) (x : Fin c → Bool) (hx : odd x = true) :
    (bad (r := r) m s first x).card ≤ (Easy m s).ncard := by
  classical
  have hf : (Easy m s).Finite := (List.finite_length_eq Bool (2 ^ m)).subset fun _ h => h.1
  have hcard := Finset.card_le_card_of_injOn (s := bad (r := r) m s first x) (t := hf.toFinset)
    (fun T : Grid r c => flatten (transform first x T))
    (fun T hT => hf.mem_toFinset.mpr ⟨(flatten_length _).trans hlen, by
      have he := (Finset.mem_filter.mp hT).2
      simpa [hx] using he⟩)
    (flatten_injective.comp (transform_injective_odd (r := r) first x hx)).injOn
  rwa [← Set.ncard_eq_toFinset_card _ hf] at hcard

theorem exists_good_seed {r c : ℕ} (m s : ℕ) (hlen : r * c = 2 ^ m) (first : Fin c)
    (hsmall : 2 ^ (c - 1) * ((HardEven r c m s).ncard * 2 ^ r + (Easy m s).ncard) < 2 ^ (r * c)) :
    ∃ T : Grid r c, ∀ x : Fin c → Bool,
      odd x = false ↔ HasCircuitSize m (tableFun m (flatten (transform first x T))) s := by
  classical
  let ev := (parityClass c false).biUnion (bad (r := r) m s first)
  let od := (parityClass c true).biUnion (bad (r := r) m s first)
  have hev : ev.card ≤ 2 ^ (c - 1) * ((HardEven r c m s).ncard * 2 ^ r) := by
    calc
      _ ≤ ∑ x ∈ parityClass c false, (bad (r := r) m s first x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ parityClass c false, (HardEven r c m s).ncard * 2 ^ r :=
        Finset.sum_le_sum fun x hx => card_bad_even m s hlen first x (Finset.mem_filter.mp hx).2
      _ = _ := by rw [Finset.sum_const, Nat.nsmul_eq_mul, card_parityClass first]
  have hod : od.card ≤ 2 ^ (c - 1) * (Easy m s).ncard := by
    calc
      _ ≤ ∑ x ∈ parityClass c true, (bad (r := r) m s first x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ parityClass c true, (Easy m s).ncard :=
        Finset.sum_le_sum fun x hx => card_bad_odd m s hlen first x (Finset.mem_filter.mp hx).2
      _ = _ := by rw [Finset.sum_const, Nat.nsmul_eq_mul, card_parityClass first]
  have hCard : (ev ∪ od).card < (Finset.univ : Finset (Grid r c)).card := by
    have hb := (Finset.card_union_le ev od).trans (Nat.add_le_add hev hod)
    rw [← Nat.mul_add] at hb
    rw [Finset.card_univ]
    have hF : Fintype.card (Grid r c) = 2 ^ (r * c) := by
      simp only [Grid, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul, Nat.mul_comm c r]
    rw [hF]
    exact hb.trans_lt hsmall
  obtain ⟨T, hT⟩ : ∃ T, T ∉ ev ∪ od := by
    by_contra! hnone
    exact (lt_irrefl _) (by simpa only [Finset.eq_univ_of_forall hnone] using hCard)
  refine ⟨T, fun x => ?_⟩
  have ht : T ∉ bad (r := r) m s first x := by
    intro h
    apply hT
    cases hx : odd x
    · exact Finset.mem_union.mpr (.inl (Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, h⟩))
    · exact Finset.mem_union.mpr (.inr (Finset.mem_biUnion.mpr
        ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, h⟩))
  cases hx : odd x <;> simp_all [bad]

def word {r c : ℕ} (s : ℕ) (first : Fin c) (T : Grid r c) (x : Fin c → Bool) : List Bool :=
  List.replicate s true ++ false :: flatten (transform first x T)

theorem word_local {r c : ℕ} (s : ℕ) (first : Fin c) (T : Grid r c) :
    QueryLocal c 1 (word s first T) := by
  classical
  intro j x
  let header := List.replicate s true ++ [false]
  have hword (y : Fin c → Bool) : word s first T y = header ++ flatten (transform first y T) := by
    simp [word, header, List.append_assoc]
  by_cases hh : j < header.length
  · refine ⟨∅, by simp, fun y _ => ?_⟩
    rw [hword, hword, List.getElem?_append_left hh, List.getElem?_append_left hh]
  · have hge := Nat.le_of_not_gt hh
    let k := j - header.length
    by_cases hk : k < r * c
    · let ij := finProdFinEquiv.symm (⟨k, hk⟩ : Fin (r * c))
      refine ⟨{ij.2}, by simp, fun y hy => ?_⟩
      have hy' : y ij.2 = x ij.2 := hy ij.2 (Finset.mem_singleton_self _)
      rw [hword, hword, List.getElem?_append_right hge, List.getElem?_append_right hge]
      change (flatten (transform first y T))[k]? = (flatten (transform first x T))[k]?
      simp only [flatten, List.getElem?_ofFn, hk, dite_true]
      change some (transform first y T ij.1 ij.2) = some (transform first x T ij.1 ij.2)
      simp [transform, flip, hy']
    · refine ⟨∅, by simp, fun y _ => ?_⟩
      rw [hword, hword, List.getElem?_append_right hge, List.getElem?_append_right hge]
      change (flatten (transform first y T))[k]? = (flatten (transform first x T))[k]?
      simp [flatten, hk]

end PEqualNP.Outside.L_meta_060_aux

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_060_aux in
theorem PEqualNP.Outside.L_meta_060 :
    ∀ (a b s : ℕ), 2 ^ (2 ^ b - 1) *
      ({T : List Bool | T.length = 2 ^ (a + b) ∧
        (∀ i : ℕ, i < 2 ^ a →
          ((List.range (2 ^ b)).filter (fun j => T.getD (i * 2 ^ b + j) false = true)).length % 2 = 0) ∧
        ¬ PEqualNP.MetaComplexity.HasCircuitSize (a + b) (PEqualNP.MetaComplexity.tableFun (a + b) T) s}.ncard *
        2 ^ (2 ^ a) +
        {T : List Bool | T.length = 2 ^ (a + b) ∧
          PEqualNP.MetaComplexity.HasCircuitSize (a + b) (PEqualNP.MetaComplexity.tableFun (a + b) T) s}.ncard)
      < 2 ^ (2 ^ (a + b)) →
    ∃ w : (Fin (2 ^ b) → Bool) → List Bool,
      PEqualNP.MetaComplexity.QueryLocal (2 ^ b) 1 w ∧
      (∀ x : Fin (2 ^ b) → Bool, ∃ T : List Bool, w x = List.replicate s true ++ false :: T ∧
        T.length = 2 ^ (a + b)) ∧
      ∀ x : Fin (2 ^ b) → Bool,
        (Finset.univ.filter fun i : Fin (2 ^ b) => x i = true).card % 2 = 0 ↔
          w x ∈ PEqualNP.MetaComplexity.MCSP := by
  intro a b s hsmall
  have hlen : 2 ^ a * 2 ^ b = 2 ^ (a + b) := (pow_add 2 a b).symm
  let first : Fin (2 ^ b) := ⟨0, Nat.two_pow_pos b⟩
  have hsmall' : 2 ^ (2 ^ b - 1) *
      ((HardEven (2 ^ a) (2 ^ b) (a + b) s).ncard * 2 ^ (2 ^ a) +
        (Easy (a + b) s).ncard) < 2 ^ (2 ^ a * 2 ^ b) := by
    rw [hlen]
    exact hsmall
  obtain ⟨T, hT⟩ := exists_good_seed (a + b) s hlen first hsmall'
  refine ⟨word s first T, word_local s first T, fun x => ⟨_, rfl, (flatten_length _).trans hlen⟩, ?_⟩
  intro x
  rw [word, word_mem (a + b) s _ ((flatten_length _).trans hlen)]
  exact (odd_false_iff x).symm.trans (hT x)
