module

public import MCSPPolynomialBarrier

/-! Interpolate a Boolean polynomial from its low-weight samples. The full
prediction shares XORs and costs at most eight gates per degree per entry. -/

@[expose] public section

namespace PvsNP.Frontier.DegreeSampler

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open PolynomialBarrier QuadraticForest

def consEmb (m : ℕ) (b : Bool) : BitString m ↪ BitString (m+1) :=
  ⟨fun z => Fin.cons b z, fun _ _ h => by
    simpa using congrArg (Fin.tail : BitString (m+1) → BitString m) h⟩

def sample : (d m : ℕ) → Finset (BitString m)
  | 0, m => {zeroVec m}
  | _+1, 0 => {zeroVec 0}
  | d+1, m+1 => (sample (d+1) m).map (consEmb m false) ∪ (sample d m).map (consEmb m true)

private theorem cons_mem_sample {d m : ℕ} (b : Bool) (z : BitString m)
    (hz : z ∈ sample (if b then d else d+1) m) : Fin.cons b z ∈ sample (d+1) (m+1) := by
  cases b
  · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨z, hz, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨z, hz, rfl⟩)

theorem card_sample_le (d m : ℕ) : (sample d m).card ≤ (m+1)^d := by
  induction m generalizing d with
  | zero => cases d <;> simp [sample]
  | succ m ih =>
    cases d with
    | zero => simp [sample]
    | succ d =>
      have h := Finset.card_union_le ((sample (d+1) m).map (consEmb m false))
        ((sample d m).map (consEmb m true))
      simp only [Finset.card_map] at h
      refine h.trans ((Nat.add_le_add (ih (d+1)) (ih d)).trans ?_)
      calc
        (m+1)^(d+1)+(m+1)^d = (m+1)^d*(m+2) := by rw [pow_succ]; ring
        _ ≤ (m+2)^d*(m+2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
        _ = (m+2)^(d+1) := (pow_succ ..).symm

private theorem sample_succ (d m : ℕ) : sample d m ⊆ sample (d+1) m := by
  induction m generalizing d with
  | zero => cases d <;> exact Finset.Subset.rfl
  | succ m ih =>
    intro z hz
    cases d with
    | zero =>
      change z ∈ ({zeroVec (m+1)} : Finset _) at hz
      have hz' := Finset.mem_singleton.mp hz
      rw [hz', show zeroVec (m+1) = Fin.cons false (zeroVec m) by
        funext i
        cases i using Fin.cases <;> rfl]
      exact cons_mem_sample false _ (ih 0 (by simp [sample]))
    | succ d =>
      rcases Finset.mem_union.mp hz with hL | hR
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hL
        exact cons_mem_sample false _ (ih (d+1) hx)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hR
        exact cons_mem_sample true _ (ih d hx)

def extend : (d m : ℕ) → BooleanFunction m → BooleanFunction m
  | 0, m, f => fun _ => f (zeroVec m)
  | _+1, 0, f => f
  | d+1, m+1, f => fun z =>
      extend (d+1) m (fun y => f (Fin.cons false y)) (Fin.tail z) ^^
        (z 0 && extend d m (fun y => f (Fin.cons false y) ^^ f (Fin.cons true y)) (Fin.tail z))

theorem extend_congr (d m : ℕ) {f g : BooleanFunction m}
    (h : ∀ z ∈ sample d m, f z = g z) : extend d m f = extend d m g := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => exact funext fun _ => h (zeroVec 0) (Finset.mem_singleton_self _)
    | succ d =>
      funext z
      exact h z (by rw [Subsingleton.elim z (zeroVec 0)]; exact Finset.mem_singleton_self _)
  | succ m ih =>
    cases d with
    | zero => exact funext fun _ => h _ (Finset.mem_singleton_self _)
    | succ d =>
      have hlo := ih (d+1) (f := fun y => f (Fin.cons false y))
        (g := fun y => g (Fin.cons false y)) (fun z hz => h _ (cons_mem_sample false z hz))
      have hd := ih d (f := fun y => f (Fin.cons false y) ^^ f (Fin.cons true y))
        (g := fun y => g (Fin.cons false y) ^^ g (Fin.cons true y)) fun z hz => by
          rw [h _ (cons_mem_sample false z (sample_succ d m hz)),
            h _ (cons_mem_sample true z hz)]
      funext z
      simp only [extend, hlo, hd]

theorem extend_eq_of_degree (d m : ℕ) {f : BooleanFunction m}
    (h : isDegFn d m f = true) : extend d m f = f := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => exact funext fun z => ((isDegFn_zero_iff.mp h) z).symm
    | succ d => rfl
  | succ m ih =>
    cases d with
    | zero => exact funext fun z => ((isDegFn_zero_iff.mp h) z).symm
    | succ d =>
      obtain ⟨h0,h1⟩ := Bool.and_eq_true_iff.mp h
      funext z
      rw [← Fin.cons_self_tail z]
      cases hb : z 0 <;>
        simp [extend, ih (d+1) h0, ih d h1]

theorem degree_extend (d m : ℕ) (f : BooleanFunction m) :
    isDegFn d m (extend d m f) = true := by
  induction m generalizing d with
  | zero => cases d <;> simp [extend, isDegFn]
  | succ m ih =>
    cases d with
    | zero => exact isDegFn_const 0 _ _
    | succ d =>
      have h0 : (fun y => extend (d+1) (m+1) f (Fin.cons false y)) =
          extend (d+1) m (fun y => f (Fin.cons false y)) := by
        funext y
        simp [extend]
      have h1 : (fun y => extend (d+1) (m+1) f (Fin.cons false y) ^^
          extend (d+1) (m+1) f (Fin.cons true y)) =
          extend d m (fun y => f (Fin.cons false y) ^^ f (Fin.cons true y)) := by
        funext y
        simp [extend]
      simp only [isDegFn, h0, h1, ih, Bool.and_self]

theorem eq_of_sample (d m : ℕ) {f g : BooleanFunction m}
    (hf : isDegFn d m f = true) (hg : isDegFn d m g = true)
    (h : ∀ z ∈ sample d m, f z = g z) : f = g := by
  rw [← extend_eq_of_degree d m hf, ← extend_eq_of_degree d m hg]
  exact extend_congr d m h

theorem extend_synthesis {n : ℕ} (d m : ℕ) {S : Set (BooleanFunction n)}
    (w : BitString m → BooleanFunction n) (hw : ∀ z, w z ∈ S) :
    Synthesis interpretation S (Set.range (fun z x => extend d m (fun y => w y x) z))
      (8 * d * 2^m) := by
  induction m generalizing d S with
  | zero =>
    apply (Synthesis.of_mem (hw (zeroVec 0))).mono Set.Subset.rfl ?_ (Nat.zero_le _)
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (zeroVec 0)]
    cases d <;> rfl
  | succ m ih =>
    cases d with
    | zero =>
      apply (Synthesis.of_mem (hw (zeroVec (m+1)))).mono Set.Subset.rfl ?_ (Nat.zero_le _)
      intro f hf
      obtain ⟨z, rfl⟩ := hf
      rfl
    | succ d =>
      let delta (y : BitString m) (x : BitString n) := w (Fin.cons false y) x ^^ w (Fin.cons true y) x
      let base (y : BitString m) (x : BitString n) :=
        extend (d+1) m (fun z => w (Fin.cons false z) x) y
      let diff (y : BitString m) (x : BitString n) :=
        extend d m (fun z => delta z x) y
      let top (y : BitString m) (x : BitString n) := base y x ^^ diff y x
      let A := S ∪ Set.range delta
      let B := S ∪ (Set.range delta ∪ Set.range base)
      let C := S ∪ ((Set.range delta ∪ Set.range base) ∪ Set.range diff)
      have hDelta : Synthesis interpretation S (Set.range delta) (4*2^m) := by
        simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, Nat.mul_comm] using
          Synthesis.family delta (fun _ => 4) (fun y =>
            (Synthesis.of_mem (hw (Fin.cons false y))).xor (Synthesis.of_mem (hw (Fin.cons true y))))
      have hBase : Synthesis interpretation A (Set.range base) (8*(d+1)*2^m) :=
        ih (d+1) (fun y => w (Fin.cons false y)) (fun y => Or.inl (hw _))
      have hDiff : Synthesis interpretation B (Set.range diff) (8*d*2^m) :=
        ih d delta (fun y => Or.inr (Or.inl ⟨y, rfl⟩))
      have hTop : Synthesis interpretation C (Set.range top) (4*2^m) := by
        have hOne (y : BitString m) : Synthesis interpretation C {top y} 4 :=
          (Synthesis.of_mem (Or.inr (Or.inl (Or.inr ⟨y, rfl⟩)))).xor
            (Synthesis.of_mem (Or.inr (Or.inr ⟨y,rfl⟩)))
        simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, Nat.mul_comm] using
          Synthesis.family top (fun _ => 4) hOne
      apply (((hDelta.comp hBase).comp hDiff).comp hTop).mono Set.Subset.rfl ?_ ?_
      · rintro _ ⟨z, rfl⟩
        cases hz : z 0
        · exact Or.inl (Or.inl (Or.inr ⟨Fin.tail z, funext fun x => by simp [extend, base, hz]⟩))
        · exact Or.inr ⟨Fin.tail z, funext fun x => by simp [extend, top, base, diff, delta, hz]⟩
      · rw [pow_succ 2 m]
        ring_nf
        omega

def shifted {m : ℕ} (S : Finset (BitString m)) (a : BitString m) : Finset (BitString m) :=
  S.image (fun z => bitXor z a)

/-- The sets of sampled addresses for distinct centers are disjoint. -/
def Separated {m : ℕ} (S C : Finset (BitString m)) : Prop :=
  (C : Set (BitString m)).Pairwise (fun a b => Disjoint (shifted S a) (shifted S b))

theorem sample_nonempty (d m : ℕ) : (sample d m).Nonempty := by
  induction m generalizing d with
  | zero => cases d <;> exact ⟨_, Finset.mem_singleton_self _⟩
  | succ m ih =>
    cases d with
    | zero => exact ⟨_, Finset.mem_singleton_self _⟩
    | succ d =>
      obtain ⟨z,hz⟩ := ih (d+1)
      exact ⟨_, cons_mem_sample false z hz⟩

theorem exists_separated {m : ℕ} (S : Finset (BitString m)) (hNonempty : S.Nonempty) {k : ℕ}
    (hRoom : k * (S.card * S.card) < 2^m) :
    ∃ C : Finset (BitString m), C.card = k+1 ∧ Separated S C := by
  induction k with
  | zero =>
    exact ⟨{zeroVec m}, Finset.card_singleton _, by
      intro a ha b hb hne
      rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
      exact (hne (ha.trans hb.symm)).elim⟩
  | succ k ih =>
    have hk : k * (S.card * S.card) < 2 ^ m :=
      (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans_lt hRoom
    obtain ⟨C, hC, hSep⟩ := ih hk
    let used := C.biUnion (shifted S)
    have hu : used.card ≤ C.card * S.card := by
      have h := Finset.card_biUnion_le (s := C) (t := shifted S)
      exact h.trans (by
        simpa only [Finset.sum_const, smul_eq_mul] using
          Finset.sum_le_sum (s := C) (fun a _ =>
            (show (shifted S a).card ≤ S.card from Finset.card_image_le)))
    let bad := Finset.image₂ bitXor used S
    have hBad : bad.card < (Finset.univ : Finset (BitString m)).card := by
      rw [Finset.card_univ, BitString.card]
      calc
        _ ≤ used.card * S.card := Finset.card_image₂_le _ _ _
        _ ≤ (k+1) * (S.card * S.card) := by
          simpa [hC, Nat.mul_assoc] using Nat.mul_le_mul_right S.card hu
        _ < _ := hRoom
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hBad
    obtain ⟨z,hz⟩ := hNonempty
    have hDis (b : BitString m) (hb : b ∈ C) : Disjoint (shifted S a) (shifted S b) := by
      refine Finset.disjoint_left.mpr fun x hx hy => ha ?_
      obtain ⟨y,hy',rfl⟩ := Finset.mem_image.mp hx
      have hv : bitXor y a ∈ used := Finset.mem_biUnion.mpr ⟨b,hb,hy⟩
      have he : bitXor (bitXor y a) y = a := by rw [bitXor_comm y a, bitXor_cancel_self_right]
      exact Finset.mem_image₂.mpr ⟨_,hv,y,hy',he⟩
    have haC : a ∉ C := fun hb =>
      Finset.disjoint_left.mp (hDis a hb)
        (Finset.mem_image_of_mem _ hz) (Finset.mem_image_of_mem _ hz)
    refine ⟨insert a C, by rw [Finset.card_insert_of_notMem haC, hC], ?_⟩
    intro x hx y hy hne
    simp only [Finset.mem_coe, Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact (hne rfl).elim
      · exact hDis y hy
    · rcases hy with rfl | hy
      · exact (hDis x hx).symm
      · exact hSep hx hy hne

theorem exists_clean {m : ℕ} {S C D : Finset (BitString m)}
    (hSep : Separated S C) (hSize : D.card < C.card) :
    ∃ a ∈ C, Disjoint D (shifted S a) := by
  by_contra! h
  have hit (a : C) : ∃ i, i ∈ D ∧ i ∈ shifted S a := by
    have hh := h a a.property
    rw [Finset.disjoint_left] at hh
    push Not at hh
    exact hh
  choose f hf using hit
  have hinj : Function.Injective f := by
    intro a b he
    by_contra hn
    have hne : a.val ≠ b.val := fun h => hn (Subtype.ext h)
    exact Finset.disjoint_left.mp (hSep a.property b.property hne) (hf a).2 (he ▸ (hf b).2)
  let encode (a : C) : D := ⟨f a, (hf a).1⟩
  have hc := Fintype.card_le_of_injective encode (fun a b he => hinj (congrArg Subtype.val he))
  rw [Fintype.card_coe, Fintype.card_coe] at hc
  omega

#print axioms eq_of_sample
#print axioms extend_synthesis
#print axioms exists_separated

end PvsNP.Frontier.DegreeSampler
