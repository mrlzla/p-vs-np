module

public import MCSPParityProbes
public import MCSPQuadraticForest

/-! A small control for four-flip patches of arbitrary parity translates of
logarithmic-width juntas. Five disjoint radius-one neighborhoods suffice to
recover the parity coefficients off the support of the junta. -/

@[expose] public section

namespace PvsNP.Frontier.AffineProbes

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open SuperTwoN CornerCertificates CommunicationCut PermutedCut PatchedCut
open JuntaRadius (CodeFor value)
open QuadraticForest (bitXor bitXor_cancel_self_right dot_bitXor_left)
open ParityProbes (translate)
open scoped Classical

def center (m : ℕ) (a : Fin 5) : BitString m :=
  fun i => decide (i.val / 3 = a.val)

def neighbor {m : ℕ} (x : BitString m) (v : Option (Fin m)) : BitString m :=
  v.elim x (fun i => Function.update x i (!(x i)))

private theorem neighbor_apply_of_ne {m : ℕ} (x : BitString m) (v : Option (Fin m))
    (i : Fin m) (h : some i ≠ v) : neighbor x v i = x i := by
  cases v with
  | none => rfl
  | some j =>
    exact Function.update_of_ne (fun e => h (congrArg some e)) _ _

noncomputable def star (m : ℕ) (a : Fin 5) : Finset (Fin (2 ^ m)) :=
  Finset.univ.image (fun v => BitString.equivFin m (neighbor (center m a) v))

theorem stars_disjoint {m : ℕ} (hm : 15 ≤ m) {a b : Fin 5} (hab : a ≠ b) :
    Disjoint (star m a) (star m b) := by
  apply Finset.disjoint_left.mpr
  intro j ha hb
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ha
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hb
  have he := (BitString.equivFin m).injective (hv.trans hw.symm)
  let slot (k : Fin 3) : Fin m := ⟨3*a.val+k.val, by omega⟩
  have hinj : Function.Injective (fun k => some (slot k)) := by
    intro i k hik
    have h := congrArg Fin.val (Option.some.inj hik)
    exact Fin.ext (by dsimp [slot] at h; omega)
  have hout : ∃ k, some (slot k) ≠ v ∧ some (slot k) ≠ w := by
    by_contra! h
    have hh : (Finset.univ : Finset (Fin 3)).card ≤ ({v, w} : Finset (Option (Fin m))).card := by
      refine Finset.card_le_card_of_injOn (fun k => some (slot k)) ?_ hinj.injOn
      intro k _
      by_cases hv : some (slot k) = v
      · simp [hv]
      · simp [h k hv]
    have hpair := Finset.card_insert_le v ({w} : Finset (Option (Fin m)))
    simp only [Finset.card_singleton] at hpair
    rw [Finset.card_univ, Fintype.card_fin] at hh
    omega
  obtain ⟨k, hk, hk'⟩ := hout
  have hD : (slot k).val / 3 = a.val := by dsimp [slot]; omega
  have hn : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have h := congrFun he (slot k)
  rw [neighbor_apply_of_ne _ _ _ hk, neighbor_apply_of_ne _ _ _ hk'] at h
  simp [center, hD, hn] at h

theorem exists_clean_star {m : ℕ} (hm : 15 ≤ m) (D : Finset (Fin (2 ^ m)))
    (hD : D.card ≤ 4) : ∃ a : Fin 5, Disjoint D (star m a) := by
  by_contra! h
  have hn (a : Fin 5) : ∃ j, j ∈ D ∧ j ∈ star m a := by
    have he := h a
    rw [Finset.disjoint_left] at he
    push Not at he
    exact he
  choose f hf using hn
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact Finset.disjoint_left.mp (stars_disjoint hm hne) (hf a).2 (hab ▸ (hf b).2)
  have hc := Finset.card_le_card_of_injOn f
    (s := Finset.univ) (t := D) (fun a _ => (hf a).1) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin] at hc
  omega

def sample {m : ℕ} (a : Fin 5) (T : BitString (2 ^ m)) : BitString m :=
  fun i => T (BitString.equivFin m (center m a)) ^^
    T (BitString.equivFin m (neighbor (center m a) (some i)))

def mask {m : ℕ} (b : BitString m) (T : BitString (2 ^ m)) : BitString (2 ^ m) :=
  translate (MCSP.truthTable m (dot b)) T

private theorem mask_self {m : ℕ} (b : BitString m) (T : BitString (2 ^ m)) :
    mask b (mask b T) = T :=
  bitXor_cancel_self_right T _

private theorem mask_patch {m : ℕ} (b : BitString m) (D : Finset (Fin (2 ^ m)))
    (T : BitString (2 ^ m)) : mask b (patch D T) = patch D (mask b T) := by
  funext i
  change ((T i ^^ decide (i ∈ D)) ^^ _) = ((T i ^^ _) ^^ decide (i ∈ D))
  rw [Bool.xor_assoc, Bool.xor_assoc, Bool.xor_comm (decide (i ∈ D))]

private theorem mask_table {m : ℕ} (b : BitString m) (f : BooleanFunction m) :
    mask b (MCSP.truthTable m f) = MCSP.truthTable m (fun z => f z ^^ dot b z) := by
  funext i
  simp [mask, translate, MCSP.truthTable_apply]

private theorem dot_congr {m : ℕ} (b x y : BitString m)
    (h : ∀ i, b i = true → x i = y i) : dot b x = dot b y := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have ht := ih (Fin.tail b) (Fin.tail x) (Fin.tail y) (fun i => h i.succ)
    have h0 : (b 0 && x 0) = (b 0 && y 0) := by cases hb : b 0 <;> simp [hb, h 0]
    simp only [dot, ht, h0]

private theorem tail_neighbor_succ {m : ℕ} (x : BitString (m+1)) (i : Fin m) :
    Fin.tail (neighbor x (some i.succ)) = neighbor (Fin.tail x) (some i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [neighbor, Fin.tail]
  · rw [show Fin.tail (neighbor x (some i.succ)) j = x j.succ from
      neighbor_apply_of_ne _ _ _ (by simpa using hj),
    neighbor_apply_of_ne _ _ _ (by simpa using hj)]
    rfl

private theorem dot_toggle {m : ℕ} (b x : BitString m) (i : Fin m) :
    dot b (neighbor x (some i)) = (dot b x ^^ b i) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases i using Fin.cases with
    | zero =>
      have ht : Fin.tail (neighbor x (some 0)) = Fin.tail x := by
        funext j
        exact neighbor_apply_of_ne _ _ _ (by simp)
      simp only [dot, ht]
      change ((b 0 && Function.update x 0 (!(x 0)) 0) ^^ _) = ((_ ^^ _) ^^ _)
      rw [Function.update_self]
      cases b 0 <;> cases x 0 <;> cases dot (Fin.tail b) (Fin.tail x) <;> rfl
    | succ i =>
      have h0 := neighbor_apply_of_ne x (some i.succ) 0 (fun h => Fin.succ_ne_zero i (Option.some.inj h).symm)
      simp only [dot, h0, tail_neighbor_succ, ih, Bool.xor_assoc]
      rfl

private theorem sample_off_support {r m : ℕ} (c : CodeFor r m) (b : BitString m)
    (D : Finset (Fin (2 ^ m))) (a : Fin 5) (ha : Disjoint D (star m a))
    (i : Fin m) (hi : ∀ j, c.1 j ≠ .inl i) :
    sample a (patch D (MCSP.truthTable m (fun z => value c z ^^ dot b z))) i = b i := by
  have hclean (v : Option (Fin m)) : BitString.equivFin m (neighbor (center m a) v) ∉ D :=
    fun h => Finset.disjoint_left.mp ha h (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  have h0 : BitString.equivFin m (center m a) ∉ D := hclean none
  have hv : value c (neighbor (center m a) (some i)) = value c (center m a) := by
    apply OrderedTree.value_depends_on_code_support
    intro j k hj
    exact neighbor_apply_of_ne _ _ _ (fun e => hi j (by rwa [Option.some.inj e] at hj))
  simp only [sample, patch, h0, hclean, decide_false, Bool.xor_false, MCSP.truthTable_apply,
    Equiv.symm_apply_apply, hv, dot_toggle]
  have cancel (x y z : Bool) : ((x ^^ y) ^^ (x ^^ (y ^^ z))) = z := by
    cases x <;> cases y <;> cases z <;> rfl
  exact cancel _ _ _

noncomputable def control (r m : ℕ) (hm : r + 4 ≤ m) (T : BitString (2 ^ m)) : Bool :=
  decide (∃ a : Fin 5, LogPrefixControl.control r m hm (mask (sample a T) T) = true)

/-- Every four-flip patch passes for every parity mask and placement of the r slots. -/
theorem control_accepts {r m : ℕ} (hm : r + 4 ≤ m) (hm' : 15 ≤ m)
    (c : CodeFor r m) (b : BitString m) (D : Finset (Fin (2 ^ m))) (hD : D.card ≤ 4) :
    control r m hm (patch D (MCSP.truthTable m (fun z => value c z ^^ dot b z))) = true := by
  let T := patch D (MCSP.truthTable m (fun z => value c z ^^ dot b z))
  obtain ⟨a, ha⟩ := exists_clean_star hm' D hD
  let d := sample a T
  change control r m hm T = true
  apply decide_eq_true
  refine ⟨a, ?_⟩
  change LogPrefixControl.control r m hm (mask d T) = true
  have hMask : mask d T =
      patch D (MCSP.truthTable m (fun z => value c z ^^ dot (bitXor b d) z)) := by
    rw [show T = patch D (MCSP.truthTable m (fun z => value c z ^^ dot b z)) from rfl,
      mask_patch, mask_table]
    simp only [dot_bitXor_left, Bool.xor_assoc]
  rw [hMask]
  apply LogPrefixControl.control_accepts_on_code_support hm c _ _ D hD
  intro x y hxy
  rw [OrderedTree.value_depends_on_code_support c x y hxy]
  congr 1
  apply dot_congr
  intro i hi
  by_contra hn
  have hu (j : Fin r) : c.1 j ≠ .inl i := fun hj => hn (hxy j i hj)
  have hd : d i = b i := sample_off_support c b D a ha i hu
  simp [bitXor, hd] at hi

theorem control_exact {r m : ℕ} (hm : r + 4 ≤ m) (hr : 10 ≤ r) (h2 : 2 ^ r ≤ m)
    {T : BitString (2 ^ m)} (h : control r m hm T = true) : mcspSquare m T = true := by
  obtain ⟨a, ha⟩ := of_decide_eq_true h
  obtain ⟨t, ht, D, hD, he⟩ := LogPrefixControl.control_witness hm ha
  have hUn := congrArg (mask (sample a T)) he
  rw [mask_self, mask_patch, mask_table] at hUn
  have hTree := OrderedTree.Tree.cost t
  have hPow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) ht
  have hPhase : complexity interpretation (single (dot (sample a T))) ≤ 4 * m + 1 := by
    have he : affine (sample a T) false = dot (sample a T) :=
      funext fun z => Bool.false_xor (dot (sample a T) z)
    simpa only [he] using complexity_affine_le (sample a T) false
  have hCost : complexity interpretation (single (fun z => t.eval z ^^ dot (sample a T) z)) ≤
      5 * 2 ^ r + 4 * m + 5 :=
    (complexity_xor_le t.eval (dot (sample a T))).trans (by omega)
  have hmB : 1024 ≤ m := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans h2
  have hBig := Nat.mul_le_mul_right m (by omega : 15 ≤ m)
  rw [← pow_two] at hBig
  rw [hUn]
  exact JuntaRadius.patched_function_of_budget _ D hD hCost (by omega)

theorem control_sparse {r m : ℕ} (hm : r + 4 ≤ m) (hr : 10 ≤ r) (h2 : 2 ^ r ≤ m) :
    (acceptingTables (control r m hm)).card ≤ 2 ^ descriptionBitBound m := by
  apply le_trans _ (card_accepting_mcspSquare_le m)
  apply Finset.card_le_card
  intro T ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, control_exact hm hr h2 (Finset.mem_filter.mp ht).2⟩

section Size

/-- All parity sums of a vector of wires share their partial sums. -/
private theorem synth_dot_family {n : ℕ} {S : Set (BooleanFunction n)} :
    ∀ {m : ℕ} (b : Fin m → BooleanFunction n), (∀ i, b i ∈ S) →
      Synthesis interpretation S
        (Set.range fun z : BitString m => fun T => dot (fun i => b i T) z) (4 * 2 ^ m)
  | 0, _, _ => by
    apply (Synthesis.const (s := S) false).mono Set.Subset.rfl ?_ (by decide)
    rintro _ ⟨_, rfl⟩
    rfl
  | m + 1, b, hb => by
    let tail (z : BitString m) (T : BitString n) := dot (fun i => b i.succ T) z
    let head (z : BitString m) (T : BitString n) := b 0 T ^^ tail z T
    have hTail : Synthesis interpretation S (Set.range tail) (4 * 2^m) :=
      synth_dot_family (fun i => b i.succ) (fun i => hb i.succ)
    have hHead (z : BitString m) :
        Synthesis interpretation (S ∪ Set.range tail) {head z} 4 := by
      have h0 : Synthesis interpretation (S ∪ Set.range tail) {b 0} 0 :=
        Synthesis.of_mem (Or.inl (hb 0))
      have h1 : Synthesis interpretation (S ∪ Set.range tail) {tail z} 0 :=
        Synthesis.of_mem (Or.inr ⟨z, rfl⟩)
      exact h0.xor h1
    have hs : Synthesis interpretation (S ∪ Set.range tail) (Set.range head) (4 * 2^m) := by
      simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card,
        Nat.mul_comm (2^m) 4] using Synthesis.family head (fun _ => 4) hHead
    apply (hTail.comp hs).mono Set.Subset.rfl ?_ (by rw [pow_succ]; omega)
    rintro _ ⟨z, rfl⟩
    have hz (T : BitString n) :
        dot (fun i => b i T) z = ((b 0 T && z 0) ^^ tail (Fin.tail z) T) := rfl
    cases h : z 0
    · exact Or.inl ⟨Fin.tail z, funext fun T => by simp [hz, h]⟩
    · exact Or.inr ⟨Fin.tail z, funext fun T => by simp [head, hz, h]⟩

private theorem synth_reinput {m : ℕ} (a : Fin 5) :
    Synthesis interpretation (inputs (2^m))
      (Set.range fun i : Fin (2^m) => fun T => mask (sample a T) T i) (4*m + 8*2^m) := by
  let n := 2^m
  let b (i : Fin m) (T : BitString n) := sample a T i
  let phase (z : BitString m) (T : BitString n) := dot (fun i => b i T) z
  let wires (i : Fin n) (T : BitString n) := mask (sample a T) T i
  have hb (i : Fin m) : Synthesis interpretation (inputs n) {b i} 4 := by
    have h0 : Synthesis interpretation (inputs n) {fun T => T (BitString.equivFin m (center m a))} 0 :=
      Synthesis.of_mem ⟨_, rfl⟩
    have h1 : Synthesis interpretation (inputs n)
        {fun T => T (BitString.equivFin m (neighbor (center m a) (some i)))} 0 :=
      Synthesis.of_mem ⟨_, rfl⟩
    exact h0.xor h1
  have hbAll : Synthesis interpretation (inputs n) (Set.range b) (4*m) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin,
      Nat.mul_comm m 4] using Synthesis.family b (fun _ => 4) hb
  have hp : Synthesis interpretation (inputs n ∪ Set.range b) (Set.range phase) (4*n) :=
    synth_dot_family b (fun i => Or.inr ⟨i, rfl⟩)
  let S := inputs n ∪ (Set.range b ∪ Set.range phase)
  have hw (i : Fin n) : Synthesis interpretation S {wires i} 4 := by
    have hi : Synthesis interpretation S {fun T => T i} 0 :=
      Synthesis.of_mem (Or.inl ⟨i, rfl⟩)
    have hj : Synthesis interpretation S {phase ((BitString.equivFin m).symm i)} 0 :=
      Synthesis.of_mem (Or.inr (Or.inr ⟨_, rfl⟩))
    exact hi.xor hj
  have hwAll : Synthesis interpretation S (Set.range wires) (4*n) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin,
      Nat.mul_comm n 4] using Synthesis.family wires (fun _ => 4) hw
  exact ((hbAll.comp hp).trans hwAll).mono Set.Subset.rfl Set.Subset.rfl (by omega)

private theorem reinput_size {m : ℕ} (a : Fin 5) (F : BooleanFunction (2^m)) :
    complexity interpretation (single (fun T => F (mask (sample a T) T))) ≤
      complexity interpretation (single F) + 12*2^m := by
  let wires (i : Fin (2^m)) (T : BitString (2^m)) := mask (sample a T) T i
  obtain ⟨c, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single F)
  have hAt := Synthesis.circuit (I := interpretation) (s := inputs (2^m) ∪ Set.range wires)
    c wires (fun i => Or.inr ⟨i, rfl⟩)
  have hOut : Synthesis interpretation (inputs (2^m) ∪ Set.range wires)
      {fun T => F (mask (sample a T) T)} c.size := by
    apply hAt.mono Set.Subset.rfl ?_ le_rfl
    rintro _ rfl
    exact ⟨0, funext fun T => congrFun (hc (mask (sample a T) T)) 0⟩
  have h := ((synth_reinput a).trans hOut).complexity_le
  rw [hs] at h
  have hm : m ≤ 2^m := m.lt_two_pow_self.le
  change complexity interpretation (single (fun T => F (mask (sample a T) T))) ≤ _ at h
  omega

theorem control_size {r m : ℕ} (hm : r + 4 ≤ m) :
    complexity interpretation (single (control r m hm)) ≤
      5 * complexity interpretation (single (LogPrefixControl.control r m hm)) + 60*2^m + 6 := by
  let F := LogPrefixControl.control r m hm
  let g (a : Fin 5) (T : BitString (2^m)) := F (mask (sample a T) T)
  let budget := complexity interpretation (single F) + 12*2^m
  have hOne (a : Fin 5) : Synthesis interpretation (inputs (2^m)) {g a} budget := by
    obtain ⟨c, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single (g a))
    let wires (i : Fin (2^m)) (T : BitString (2^m)) := T i
    have hAt := Synthesis.circuit (I := interpretation) (s := inputs (2^m)) c wires
      (fun i => ⟨i, rfl⟩)
    apply hAt.mono Set.Subset.rfl ?_ (hs.trans_le (reinput_size a F))
    rintro _ rfl
    exact ⟨0, funext fun T => congrFun (hc T) 0⟩
  have hs := Synthesis.exists_mem (Finset.univ : Finset (Fin 5)) g (fun _ => budget) (fun a _ => hOne a)
  have h := (Synthesis.congr_iff hs (g := control r m hm) (fun T => by
    simp only [control, g, F, Finset.mem_univ, true_and, decide_eq_true_eq])).complexity_le
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] at h
  exact h.trans_eq (by dsimp [budget, F]; omega)

theorem affine_control_sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (control r (LogPrefixControl.arity r)
        (LogPrefixControl.arity_room r hr))) ≤ LogPrefixControl.arity r * 2 ^ LogPrefixControl.arity r := by
  have hBase := LogPrefixControl.sub_nlogn (10*K)
  filter_upwards [hBase, Filter.eventually_ge_atTop (132*K)] with r he hrK hr
  let m := LogPrefixControl.arity r
  let n := 2 ^ m
  let room := LogPrefixControl.arity_room r hr
  let base := complexity interpretation (single (LogPrefixControl.control r m room))
  let full := complexity interpretation (single (control r m room))
  have hOld : (10*K)*base ≤ m*n := he hr
  have hNew : full ≤ 5*base+60*n+6 := control_size room
  have hn : 1 ≤ n := Nat.two_pow_pos _
  have hm : 132*K ≤ m := hrK.trans (Nat.le_add_right r (2^r+1))
  have hMask : (2*K)*(60*n+6) ≤ m*n := calc
    _ ≤ (2*K)*(66*n) := Nat.mul_le_mul_left _ (by omega)
    _ = (132*K)*n := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hm
  have hc : 2*(K*full) ≤ 2*(m*n) := calc
    _ = (2*K)*full := by ring
    _ ≤ (2*K)*(5*base+60*n+6) := Nat.mul_le_mul_left _ hNew
    _ = (10*K)*base+(2*K)*(60*n+6) := by ring
    _ ≤ _ := by omega
  exact (Nat.mul_le_mul_left_iff (by decide : 0 < 2)).mp hc

end Size

section Cut

open scoped BigOperators

theorem dot_eq_sum {m : ℕ} (a z : BitString m) : dot a z = ∑ i, (a i && z i) := by
  induction m with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty]; rfl
  | succ m ih =>
    rw [dot, ih (Fin.tail a) (Fin.tail z), Fin.sum_univ_succ, Bool.add_eq_xor]
    rfl

private theorem dot_perm {m : ℕ} (e : Equiv.Perm (Fin m)) (a z : BitString m) :
    dot a (z ∘ e) = dot (a ∘ e.symm) z := by
  simp only [dot_eq_sum, Function.comp_apply]
  calc
    _ = ∑ i, ((a ∘ e.symm) (e i) && z (e i)) := by simp
    _ = _ := Equiv.sum_comp e (fun i => (a ∘ e.symm) i && z i)

private theorem dot_suffix {r s : ℕ} (a : Bool) (b : BitString s)
    (x : BitString r) (v : Bool) (y : BitString s) :
    dot (Fin.append (fun _ : Fin r => false) (Fin.cons a b)) (Fin.append x (Fin.cons v y)) =
      ((a && v) ^^ dot b y) := by
  rw [dot_eq_sum, dot_eq_sum, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hz : (∑ i : Fin r, (false && x i)) = 0 := Finset.sum_eq_zero (fun _ _ => rfl)
  rw [hz, zero_add, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Bool.add_eq_xor]

abbrev Tagged (r s : ℕ) := BooleanFunction r × Bool × BitString s

def phaseVector {r s : ℕ} (a : Bool) (b : BitString s) : BitString (r + (s + 1)) :=
  Fin.append (fun _ : Fin r => false) (Fin.cons a b)

def taggedProbe {r s : ℕ} (u : Tagged r s) : BitString (2 ^ (r + (s + 1))) :=
  mask (phaseVector u.2.1 u.2.2) (probe s u.1)

def taggedMixed {r s : ℕ} (h : BooleanFunction s) (u v : Tagged r s) :
    BitString (2 ^ (r + (s + 1))) :=
  splice (CommunicationCut.mask r h) (taggedProbe u) (taggedProbe v)

def TaggedTests {r s : ℕ} (h : BooleanFunction s) : Prop :=
  ∀ u v : Tagged r s, ∀ D : Finset (Fin (2 ^ (r + (s + 1)))), D.card ≤ 4 →
    (mcspSquare (r + (s + 1)) (patch D (taggedMixed h u v)) = true ↔ u = v)

private theorem tagged_at {r s : ℕ} (u : Tagged r s) (x : BitString r) (v : Bool) (y : BitString s) :
    taggedProbe u (position x v y) = (u.1 x ^^ ((u.2.1 && v) ^^ dot u.2.2 y)) := by
  unfold taggedProbe mask translate
  simp only [probe_at_position]
  unfold position
  rw [MCSP.truthTable_apply, Equiv.symm_apply_apply]
  exact congrArg (Bool.xor (u.1 x)) (dot_suffix u.2.1 u.2.2 x v y)

private theorem mask_perm {m : ℕ} (e : Equiv.Perm (Fin m)) (a : BitString m) (T : BitString (2^m)) :
    mask a T ∘ tablePerm e = mask (a ∘ e.symm) (T ∘ tablePerm e) := by
  funext i
  obtain ⟨z,rfl⟩ := (BitString.equivFin m).surjective i
  simp only [mask, translate, Function.comp_apply]
  conv_lhs => arg 2; rw [tablePerm_at_assignment, MCSP.truthTable_apply, Equiv.symm_apply_apply, dot_perm]
  rw [MCSP.truthTable_apply, Equiv.symm_apply_apply]

theorem control_passes_tag_diag {r s : ℕ} (hm : r+4 ≤ r+(s+1)) (hm' : 15 ≤ r+(s+1))
    (e : Equiv.Perm (Fin (r+(s+1)))) (u : Tagged r s)
    (D : Finset (Fin (2 ^ (r+(s+1))))) (hD : D.card ≤ 4) :
    control r (r+(s+1)) hm (patch D (taggedProbe u ∘ tablePerm e)) = true := by
  obtain ⟨c, hc⟩ := JuntaRadius.prefix_code_after_perm u.1 e
  rw [taggedProbe, mask_perm, hc, mask_table]
  exact control_accepts hm hm' c (phaseVector u.2.1 u.2.2 ∘ e.symm) D hD

private def row {s : ℕ} (i : Fin (s+1)) (t : BitString s) (b : Bool) : BitString (s+1) :=
  Fin.cons b t ∘ Equiv.swap 0 i

private theorem row_toggle {s : ℕ} (i : Fin (s+1)) (t : BitString s) :
    row i t true = neighbor (row i t false) (some i) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [row, neighbor]
  · have hj : Equiv.swap 0 i j ≠ 0 := by
      intro he
      apply h
      exact (Equiv.swap 0 i).injective (he.trans (Equiv.swap_apply_right 0 i).symm)
    rw [neighbor_apply_of_ne _ _ _ (fun e => h (Option.some.inj e))]
    obtain ⟨k, hk⟩ := Fin.exists_succ_eq.mpr hj
    simp [row, ← hk]

private theorem row_surjective {s : ℕ} (i : Fin (s+1)) (z : BitString (s+1)) :
    ∃ (t : BitString s) (b : Bool), row i t b = z := by
  let x := z ∘ Equiv.swap 0 i
  refine ⟨Fin.tail x, x 0, ?_⟩
  rw [row, Fin.cons_self_tail]
  funext j
  simp [x, Function.comp_apply, Equiv.swap_apply_self]

/-- On a suffix direction where the masks differ, the two members of each
row pair have opposite agreement status. The hidden row needs one bit. -/
theorem tagged_mixed_with_aux {r s : ℕ} {u v : Tagged r (s+1)} (huv : u ≠ v) :
    ∃ aux : BooleanFunction (s+1) → BooleanFunction s,
      Function.Injective (fun h => (taggedMixed h u v, aux h)) := by
  have read (h g : BooleanFunction (s+1)) (he : taggedMixed h u v = taggedMixed g u v)
      (x : BitString r) (b : Bool) (y : BitString (s+1))
      (hne : taggedProbe u (position x b y) ≠ taggedProbe v (position x b y)) :
      h y = g y := by
    have hc := congrFun he (position x b y)
    simp only [taggedMixed, splice, mask_at_position] at hc
    cases b <;> cases h0 : h y <;> cases h1 : g y <;> simp_all
  by_cases hPhase : u.2.2 = v.2.2
  · refine ⟨fun _ _ => false, ?_⟩
    intro h g he
    apply funext
    intro y
    by_cases hSplit : u.2.1 = v.2.1
    · obtain ⟨x, hx⟩ : ∃ x, u.1 x ≠ v.1 x := by
        by_contra! hEq
        exact huv (Prod.ext (funext hEq) (Prod.ext hSplit hPhase))
      apply read h g (congrArg Prod.fst he) x false y
      rw [tagged_at, tagged_at, hPhase]
      simp only [Bool.and_false, Bool.false_xor]
      generalize dot v.2.2 y = b
      cases b <;> simpa using hx
    · let x : BitString r := fun _ => false
      have hDiff : ∃ b, taggedProbe u (position x b y) ≠ taggedProbe v (position x b y) := by
        simp only [tagged_at, hPhase]
        have hDiff' (p q a b d : Bool) (h : a ≠ b) :
            ∃ c : Bool, (p ^^ ((a && c) ^^ d)) ≠ (q ^^ ((b && c) ^^ d)) := by
          cases p <;> cases q <;> cases a <;> cases b <;> cases d <;> simp_all
        exact hDiff' _ _ _ _ _ hSplit
      obtain ⟨b, hb⟩ := hDiff
      exact read h g (congrArg Prod.fst he) x b y hb
  · obtain ⟨i, hi⟩ : ∃ i, u.2.2 i ≠ v.2.2 i := by
      by_contra! hEq
      exact hPhase (funext hEq)
    let x : BitString r := fun _ => false
    let visible (y : BitString (s+1)) : Prop := (u.1 x ^^ dot u.2.2 y) ≠ (v.1 x ^^ dot v.2.2 y)
    let hidden (t : BitString s) : Bool := decide (visible (row i t false))
    refine ⟨fun h t => h (row i t (hidden t)), ?_⟩
    intro h g he
    apply funext
    intro z
    obtain ⟨t, b, rfl⟩ := row_surjective i z
    have hAux := congrFun (congrArg Prod.snd he) t
    have hVis (b : Bool) (hb : b ≠ hidden t) : visible (row i t b) := by
      cases b
      · by_contra hn
        exact hb (decide_eq_false (show ¬visible (row i t false) from fun hv => hv hn)).symm
      · have hEq : ¬ visible (row i t false) := by simpa [hidden] using hb
        dsimp only [visible] at hEq ⊢
        rw [row_toggle, dot_toggle, dot_toggle]
        by_cases hu : u.2.2 i = true <;> by_cases hv : v.2.2 i = true <;> simp_all
    by_cases hb : b = hidden t
    · simpa only [hb] using hAux
    · apply read h g (congrArg Prod.fst he) x false _
      simpa only [tagged_at, Bool.and_false, Bool.false_xor] using hVis b hb

private theorem tagged_card (r s : ℕ) : Fintype.card (Tagged r s) = 2 ^ (2 ^ r + (s+1)) := by
  have hc : Fintype.card (BooleanFunction r) = 2 ^ 2 ^ r := by classical simp
  rw [Fintype.card_prod, Fintype.card_prod, hc, BitString.card, Fintype.card_bool, pow_add, pow_succ']

private theorem tag_exponent_room {r s : ℕ} (hr : 10 ≤ r) (hs : 2 ^ r ≤ s+1) :
    (2^r+(s+2))+(2^r+(s+2))+(r+((s+1)+1)+1)*4 + descriptionBitBound (r+((s+1)+1)) < 2^s := by
  have hBig : 1023 ≤ s := by
    have h := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans hs
    omega
  have h := GrowingPrefix.wide_exponent_le hr hs
  have hCub : (s+1)^3 ≤ (2*s)^3 := Nat.pow_le_pow_left (by omega) 3
  have hPoly : 100*(s+1)^3 ≤ 800*s^3 := calc
    _ ≤ 100*(2*s)^3 := Nat.mul_le_mul_left 100 hCub
    _ = _ := by ring
  have hSmall : s ≤ s^3 := calc
    _ = s*1 := by simp
    _ ≤ s*s^2 := Nat.mul_le_mul_left _ (Nat.pow_pos (by omega : 0 < s))
    _ = _ := by ring
  have hE : (2^r+(s+2))+(2^r+(s+2))+(r+((s+1)+1)+1)*4 +
      descriptionBitBound (r+((s+1)+1)) ≤ 805*s^3 := by
    unfold wideExponent at h
    omega
  have hLt : 805*s^3 < s^4 := by
    rw [pow_succ' s 3]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega : 0 < s))
  exact hE.trans_lt (hLt.trans_le (GrowingPrefix.four_power_le_exp s (by omega)))

/-- A common selector works for every split and suffix parity mask and four-flip placement.
The arbitrary prefix function absorbs parity coefficients on the prefix itself. -/
theorem exists_tagged_selector (r s : ℕ) (hr : 10 ≤ r) (hs : 2 ^ r ≤ s+1) :
    ∃ h : BooleanFunction (s+1), TaggedTests (r := r) h := by
  let m := r+((s+1)+1)
  have h2 : 2^r ≤ m := by dsimp [m]; omega
  have hBig : 1024 ≤ s+1 := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans hs
  have hm : r+4 ≤ m := by dsimp [m]; omega
  have h15 : 15 ≤ m := by dsimp [m]; omega
  have hCard (k : ℕ) : Fintype.card (BooleanFunction k) = 2 ^ 2 ^ k := by classical simp
  have room : 2 ^ ((2^r+(s+2))+(2^r+(s+2))+(m+1)*4+descriptionBitBound m+2^s) <
      Fintype.card (BooleanFunction (s+1)) := by
    rw [hCard]
    apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
    have h := tag_exponent_room hr hs
    rw [pow_succ]
    dsimp only [m]
    omega
  refine exists_family_selector_with_aux (mcspSquare m) (taggedMixed (r := r) (s := s+1))
    (tagged_card r (s+1)) (q := m) le_rfl (card_accepting_mcspSquare_le m)
    (hCard s).le room ?_ (fun h => tagged_mixed_with_aux h)
  intro h u D hD
  apply control_exact hm hr h2
  unfold taggedMixed
  rw [splice_self]
  have hId : tablePerm (Equiv.refl (Fin m)) = Equiv.refl (Fin (2^m)) := by
    ext i
    simp [tablePerm, permuteAssignment]
  have hAcc := control_passes_tag_diag hm h15 (Equiv.refl (Fin m)) u D hD
  rw [hId] at hAcc
  exact hAcc

theorem tagged_at_cut {r s : ℕ} {h : BooleanFunction s} (hh : TaggedTests (r := r) h)
    (e : Equiv.Perm (Fin (r+(s+1)))) (u v : Tagged r s)
    (D : Finset (Fin (2^(r+(s+1))))) (hD : D.card ≤ 4) :
    mcspSquare (r+(s+1)) (patch D (taggedMixed h u v ∘ tablePerm e)) = true ↔ u = v := by
  let p := tablePerm e
  have he : patch D (taggedMixed h u v ∘ p) =
      (patch (D.map p.toEmbedding) (taggedMixed h u v)) ∘ p := by
    funext i
    simp [patch, Function.comp_apply]
  rw [he, square_comp_tablePerm]
  exact hh u v _ (by simpa using hD)

theorem control_passes_tagged {r s : ℕ} (hm : r+4 ≤ r+(s+1)) (hr : 10 ≤ r)
    (h2 : 2^r ≤ r+(s+1)) {h : BooleanFunction s} (hh : TaggedTests (r := r) h)
    (e : Equiv.Perm (Fin (r+(s+1)))) (u v : Tagged r s)
    (D : Finset (Fin (2^(r+(s+1))))) (hD : D.card ≤ 4) :
    control r (r+(s+1)) hm (patch D (taggedMixed h u v ∘ tablePerm e)) = true ↔ u = v := by
  constructor
  · intro hYes
    exact (tagged_at_cut hh e u v D hD).mp (control_exact hm hr h2 hYes)
  · rintro rfl
    unfold taggedMixed
    rw [splice_self]
    have hBig := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans h2
    exact control_passes_tag_diag hm (by omega) e u D hD

theorem tagged_oneWay_width {r s w : ℕ} {h : BooleanFunction s} (hh : TaggedTests (r := r) h)
    (e : Equiv.Perm (Fin (r+(s+1)))) (D : Finset (Fin (2^(r+(s+1))))) (hD : D.card ≤ 4)
    (send : Tagged r s → BitString w) (finish : BitString w → Tagged r s → Bool)
    (factor : ∀ u v, finish (send u) v = mcspSquare (r+(s+1)) (patch D (taggedMixed h u v ∘ tablePerm e))) :
    2^r+(s+1) ≤ w := by
  have hinj : Function.Injective send := by
    intro u v he
    apply (tagged_at_cut hh e u v D hD).mp
    rw [← factor, he, factor]
    exact (tagged_at_cut hh e v v D hD).mpr rfl
  have h := Fintype.card_le_of_injective send hinj
  rw [tagged_card, BitString.card] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

theorem tagged_log_stage (r : ℕ) (hr : 10 ≤ r) :
    ∃ h : BooleanFunction (2^r), TaggedTests (r := r) h := by
  let s := 2^r-1
  have hs : s+1=2^r := by dsimp [s]; have := Nat.two_pow_pos r; omega
  rw [← hs]
  exact exists_tagged_selector r s hr hs.ge

/-- One small circuit passes every valid selector test on the explicit
logarithmic schedule, for every placement of the prefix, split and suffix. -/
theorem passes_log_schedule (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TaggedTests (r := r) h) (e : Equiv.Perm (Fin (LogPrefixControl.arity r)))
    (u v : Tagged r (2^r)) (D : Finset (Fin (2 ^ LogPrefixControl.arity r))) (hD : D.card ≤ 4) :
    control r (LogPrefixControl.arity r) (LogPrefixControl.arity_room r hr)
        (patch D (taggedMixed h u v ∘ tablePerm e)) = true ↔ u = v :=
  control_passes_tagged _ hr (LogPrefixControl.arity_pow_le r) hh e u v D hD

end Cut

section QuadraticExample

/-- One represented bit multiplied by the parity of all the others. -/
def gatedParity {k : ℕ} (x : BitString (k+1)) : Bool :=
  x 0 && dot (fun _ => true) (Fin.tail x)

private theorem gatedParity_cost (k : ℕ) :
    complexity interpretation (single (gatedParity (k := k))) ≤ 12 * (k+1) + 8 := by
  let a := QuadraticForest.zeroVec (k+1)
  let c : BitString (k+1) := Fin.cons true (QuadraticForest.zeroVec k)
  let d : BitString (k+1) := Fin.cons false (fun _ : Fin k => true)
  have he : QuadraticForest.quad a false c d = gatedParity := by
    funext x
    have h0 : affine a false x = false := by
      simp only [affine, a, Bool.false_xor, QuadraticForest.dot_zero_left]
    rw [QuadraticForest.quad, h0, Bool.false_xor]
    simp [c, d, dot, QuadraticForest.dot_zero_left, gatedParity]
  rw [← he]
  exact QuadraticForest.complexity_quad_le a false c d

theorem gatedParity_patched_exact {k : ℕ} (hk : 32 ≤ k+1)
    (D : Finset (Fin (2^(k+1)))) (hD : D.card ≤ 4) :
    mcspSquare (k+1) (patch D (MCSP.truthTable (k+1) gatedParity)) = true := by
  apply JuntaRadius.patched_function_of_budget gatedParity D hD (gatedParity_cost k)
  have hc := Nat.mul_le_mul_right (k+1) hk
  rw [← pow_two] at hc
  omega

private theorem gatedParity_mask_separates {r k : ℕ} (hk : 2*r < k)
    (hRoom : 8*(k+2) < 2^k) (a : BitString (k+1))
    (t : OrderedTree.Tree (k+1)) (ht : t.depth ≤ r)
    (D E : Finset (Fin (2^(k+1)))) (hD : D.card ≤ 4) (hE : E.card ≤ 4) :
    patch D (MCSP.truthTable (k+1) (fun x => gatedParity x ^^ dot a x)) ≠
      patch E (MCSP.truthTable (k+1) t.eval) := by
  let S (b : Bool) := (Finset.univ : Finset (Fin k)).filter (fun i => (a i.succ ^^ b) = true)
  have hCover : S false ∪ S true = Finset.univ := by
    ext i
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases a i.succ <;> decide
  have hSum := Finset.card_union_le (S false) (S true)
  rw [hCover, Finset.card_univ, Fintype.card_fin] at hSum
  obtain ⟨b, hb⟩ : ∃ b, r < (S b).card := by
    by_contra! h
    have h0 := h false
    have h1 := h true
    omega
  let V := (S b).image (Fin.succ : Fin k → Fin (k+1))
  let lift (y : BitString k) : BitString (k+1) := Fin.cons b y
  let C := (Finset.univ : Finset (BitString k)).image lift
  have hV : V.card = (S b).card :=
    Finset.card_image_of_injective _ (Fin.succ_injective k)
  have hLift : Function.Injective lift := by
    intro u v huv
    have hTail : Fin.tail (lift u) = Fin.tail (lift v) := congrArg Fin.tail huv
    simpa only [lift, Fin.tail_cons] using hTail
  have hC : C.card = 2^k := by
    simp only [C, Finset.card_image_of_injective _ hLift, Finset.card_univ, BitString.card]
  apply ParityProbes.sensitive_patch_separate_tree_on _ V C (hC.symm ▸ hRoom) _
    t (by omega) D E hD hE
  intro j hj x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  have hCoeff : (a i.succ ^^ b) = true := (Finset.mem_filter.mp hi).2
  let x := (Fin.cons b y : BitString (k+1))
  change (gatedParity (neighbor x (some i.succ)) ^^ dot a (neighbor x (some i.succ))) =
    !(gatedParity x ^^ dot a x)
  have h0 : neighbor x (some i.succ) 0 = x 0 :=
    neighbor_apply_of_ne _ _ _ (fun h => Fin.succ_ne_zero i (Option.some.inj h).symm)
  simp only [gatedParity, h0, tail_neighbor_succ, dot_toggle]
  change ((b && (dot (fun _ => true) (Fin.tail x) ^^ true)) ^^ (dot a x ^^ a i.succ)) =
    !((b && dot (fun _ => true) (Fin.tail x)) ^^ dot a x)
  have hFlip (b p q c : Bool) (hc : (c ^^ b) = true) :
      ((b && (p ^^ true)) ^^ (q ^^ c)) = !((b && p) ^^ q) := by
    cases b <;> cases p <;> cases q <;> cases c <;> simp_all
  exact hFlip _ _ _ _ hCoeff

/-- This rank-one quadratic YES probe defeats the affine control even after
four arbitrary truth-table flips. Every guessed mask leaves a deep branch. -/
theorem gatedParity_rejects_control {r k : ℕ} (hm : r+4 ≤ k+1) (hk : 2*r < k)
    (hRoom : 8*(k+2) < 2^k) (D : Finset (Fin (2^(k+1)))) (hD : D.card ≤ 4) :
    control r (k+1) hm (patch D (MCSP.truthTable (k+1) gatedParity)) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  obtain ⟨i, hi⟩ := of_decide_eq_true h
  obtain ⟨t, ht, E, hE, hEq⟩ := LogPrefixControl.control_witness hm hi
  rw [mask_patch, mask_table] at hEq
  exact gatedParity_mask_separates hk hRoom _ t ht D E hD hE hEq

theorem gatedParity_separates_log_schedule (r : ℕ) (hr : 10 ≤ r)
    (D : Finset (Fin (2 ^ LogPrefixControl.arity r))) (hD : D.card ≤ 4) :
    let T := patch D (MCSP.truthTable (LogPrefixControl.arity r) gatedParity)
    mcspSquare (LogPrefixControl.arity r) T = true ∧
      control r (LogPrefixControl.arity r) (LogPrefixControl.arity_room r hr) T = false := by
  have hp : 1024 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  have hLarge : r < 2^r := r.lt_two_pow_self
  have h32 : 32 ≤ (r+2^r)+1 := by omega
  have hRoom (k : ℕ) (hk : 10 ≤ k) : 8*(k+2) < 2^k := by
    refine Nat.le_induction (m := 10) (P := fun n _ => 8*(n+2) < 2^n) (by decide) ?_ k hk
    intro n _ ih
    rw [pow_succ]
    omega
  exact ⟨gatedParity_patched_exact h32 D hD,
    gatedParity_rejects_control _ (by omega) (hRoom (r+2^r) (by omega)) D hD⟩

end QuadraticExample

#print axioms exists_clean_star
#print axioms control_accepts
#print axioms control_sparse
#print axioms control_size
#print axioms tagged_log_stage
#print axioms passes_log_schedule
#print axioms tagged_oneWay_width
#print axioms affine_control_sub_nlogn
#print axioms gatedParity_separates_log_schedule

end PvsNP.Frontier.AffineProbes
