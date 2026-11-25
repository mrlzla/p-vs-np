module

public import MCSPPatchedCut

/-! The patched equality tests can share a sampler across the entire orbit
of tail permutations. The sampled sides are fixed by parity anchors. -/

@[expose] public section

namespace PvsNP.Frontier.PatchedCut

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CommunicationCut SuperTwoN PermutedCut
open InvariantControl (point point_cons unit unit_injective weight weight_perm)
open RefinedProbeControl (sample sample_card sample_perm pairPoint pulse)
open scoped Classical

noncomputable def parityAnchors : Finset (BitString 22) := (sample 23).image Fin.tail

def suffixParity : Selector := fun t => decide (weight t % 2 = 1)

def ParityAnchored (h : Selector) : Prop := ∀ t ∈ parityAnchors, h t = suffixParity t

private theorem parityAnchors_card : parityAnchors.card ≤ 576 :=
  Finset.card_image_le.trans (sample_card 23)

theorem exists_parity_anchored_selector : ∃ h : Selector, ParityAnchored h ∧ Tests (mcspSquare 32) h := by
  have hGap (k : ℕ) (hk : k ≤ 576) : 28828 < 2 ^ 22 - k := by omega
  exact exists_patched_selector_with parityAnchors suffixParity (hGap _ parityAnchors_card)

theorem weight_cons {m : ℕ} (b : Bool) (x : BitString m) :
    weight (Fin.cons b x) = weight x + (if b then 1 else 0) := by
  have hs {l : ℕ} (z : BitString l) : weight z = ∑ i, if z i then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp [weight]
  rw [hs, hs, Fin.sum_univ_succ]
  simp [Nat.add_comm]

private theorem weight_unit {m : ℕ} (j : Fin m) : weight (unit j) = 1 := by
  have h : (Finset.univ.filter fun i => unit j i = true) = {j} := by ext i; simp [unit]
  unfold weight
  rw [h, Finset.card_singleton]

theorem cons_unit_sample (b : Bool) (j : Fin 22) : Fin.cons b (unit j) ∈ sample 23 := by
  refine Finset.mem_image.mpr ⟨(if b then some (0 : Fin 23) else none, some j.succ),
    Finset.mem_univ _, ?_⟩
  funext i
  refine Fin.cases ?_ (fun l => ?_) i
  · cases b <;> simp [pairPoint, pulse, unit, Ne.symm (Fin.succ_ne_zero j)]
  · cases b <;> simp [pairPoint, pulse, unit]

theorem point_tail (a : BitString 9) (z : BitString 23) :
    point a z = position (s := 22) a (z 0) (Fin.tail z) := by
  rw [← point_cons, Fin.cons_self_tail]

private theorem probe_point (f : Prefix) (a : BitString 9) (z : BitString 23) :
    probe 22 f (point a z) = f a := by rw [point_tail, probe_at_position]

private theorem mask_point_parity {h : Selector} (hh : ParityAnchored h)
    (a : BitString 9) {z : BitString 23} (hz : z ∈ sample 23) :
    mask 9 h (point a z) = decide (weight z % 2 = 1) := by
  have ht : Fin.tail z ∈ parityAnchors := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have he : weight z = weight (Fin.tail z) + (if z 0 then 1 else 0) := by
    simpa only [Fin.cons_self_tail] using weight_cons (z 0) (Fin.tail z)
  rw [point_tail, mask_at_position, hh _ ht, he]
  unfold suffixParity
  have hParity (b : Bool) (n : ℕ) :
      (b ^^ decide (n % 2 = 1)) = decide ((n + (if b then 1 else 0)) % 2 = 1) := by
    cases b
    · simp
    · by_cases hp : n % 2 = 1
      · have he : (n + 1) % 2 ≠ 1 := by omega
        simp [hp, he]
      · have he : (n + 1) % 2 = 1 := by omega
        simp [hp, he]
  exact hParity _ _

def readAddress (a : BitString 9) (j : Fin 9) (b : Bool) : Address :=
  position a b (unit (j.castLE (by decide : 9 ≤ 22)))

private theorem readAddress_pair_injective (a : BitString 9) :
    Function.Injective (fun p : Fin 9 × Bool => readAddress a p.1 p.2) := by
  intro x y h
  change (positionEquiv 9 22) (a, x.2, unit (x.1.castLE _)) =
    (positionEquiv 9 22) (a, y.2, unit (y.1.castLE _)) at h
  have he := (positionEquiv 9 22).injective h
  have hb := congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.1) he
  have hj := unit_injective 22 (congrArg (fun p : BitString 9 × Bool × BitString 22 => p.2.2) he)
  exact Prod.ext (Fin.ext (congrArg (fun i : Fin 22 => i.val) hj)) hb

/-- Every transported splice has the same values on the fixed pair sample. -/
theorem sample_value {h : Selector} (hh : ParityAnchored h) (e : Equiv.Perm (Fin 23))
    (f g : Prefix) (a : BitString 9) (j : Fin 9) (b : Bool) :
    (mixed h f g ∘ tablePerm (liftTail 9 e)) (readAddress a j b) =
      if b then g a else f a := by
  let i : Fin 22 := j.castLE (by decide)
  let z : BitString 23 := Fin.cons b (unit i)
  change mixed h f g (tablePerm (liftTail 9 e) (point a z)) = _
  rw [InvariantControl.perm_point]
  have hz : z ∘ e ∈ sample 23 := sample_perm e (cons_unit_sample b i)
  have hw : weight (z ∘ e) = 1 + (if b then 1 else 0) := by
    rw [weight_perm]
    change weight (Fin.cons b (unit i)) = _
    rw [weight_cons, weight_unit]
  unfold mixed splice
  rw [mask_point_parity hh a hz, hw, probe_point, probe_point]
  cases b <;> rfl

/-- Transport leaves each wire in the sample bank on its original side. -/
theorem sample_side {h : Selector} (hh : ParityAnchored h) (e : Equiv.Perm (Fin 23))
    (a : BitString 9) (j : Fin 9) (b : Bool) :
    (mask 9 h ∘ tablePerm (liftTail 9 e)) (readAddress a j b) = !b := by
  have hm : mixed h (fun _ => true) (fun _ => false) = mask 9 h := by
    funext i
    obtain ⟨⟨p, b', t⟩, he⟩ := (positionEquiv 9 22).surjective i
    change position p b' t = i at he
    rw [← he]
    unfold mixed splice
    rw [probe_at_position, probe_at_position]
    cases mask 9 h (position p b' t) <;> rfl
  have he := sample_value hh e (fun _ => true) (fun _ => false) a j b
  rw [hm] at he
  cases b <;> exact he

/-- The same physical sampler observes the same signals at every transported cut,
even when the submitted table contains a common patch. -/
theorem same_patched_sample {h : Selector} (hh : ParityAnchored h)
    (e e' : Equiv.Perm (Fin 23)) (f g : Prefix) (D : Finset Address)
    (a : BitString 9) (j : Fin 9) (b : Bool) :
    patch D (mixed h f g ∘ tablePerm (liftTail 9 e)) (readAddress a j b) =
      patch D (mixed h f g ∘ tablePerm (liftTail 9 e')) (readAddress a j b) := by
  unfold patch
  rw [sample_value hh, sample_value hh]

section Control

variable {n : ℕ} (read : BitString 9 → Fin 9 → Bool → Fin n)

def mismatch (T : BitString n) (a : BitString 9) (j : Fin 9) : Bool :=
  T (read a j false) ^^ T (read a j true)

noncomputable def fiveSets : Finset (Finset (Fin 9)) := (Finset.univ : Finset (Fin 9)).powersetCard 5

theorem fiveSets_card : fiveSets.card = 126 := by
  rw [fiveSets, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

noncomputable def rowPass (T : BitString n) (a : BitString 9) : Bool :=
  !decide (∃ S ∈ fiveSets, ∀ j ∈ S, mismatch read T a j = true)

noncomputable def sampleControl (T : BitString n) : Bool := decide (∀ a, rowPass read T a = true)

theorem rowPass_iff (T : BitString n) (a : BitString 9) :
    rowPass read T a = true ↔ ¬∃ S ∈ fiveSets, ∀ j ∈ S, mismatch read T a j = true := by
  simp [rowPass]

theorem sampleControl_iff (T : BitString n) : sampleControl read T = true ↔
    ∀ a, ¬∃ S ∈ fiveSets, ∀ j ∈ S, mismatch read T a j = true := by
  simp only [sampleControl, decide_eq_true_eq, rowPass_iff]

private theorem rowPass_cost (a : BitString 9) :
    Synthesis interpretation (inputs n) {fun T => rowPass read T a} 3404 := by
  have hX (j : Fin 9) : Synthesis interpretation (inputs n) {fun T => mismatch read T a j} 4 := by
    exact (Synthesis.of_mem (show (fun T : BitString n => T (read a j false)) ∈ inputs n from
      ⟨_, rfl⟩)).xor (Synthesis.of_mem ⟨read a j true, rfl⟩)
  let all (S : Finset (Fin 9)) (T : BitString n) := decide (∀ j ∈ S, mismatch read T a j = true)
  have hAll (S : Finset (Fin 9)) (hS : S ∈ fiveSets) :
      Synthesis interpretation (inputs n) {all S} 26 := by
    have hc := (Finset.mem_powersetCard.mp hS).2
    have hs := Synthesis.forall_mem S (fun j T => mismatch read T a j) (fun _ => 4) (fun j _ => hX j)
    have he := Synthesis.congr_iff hs (g := all S) (fun T => by simp [all])
    simpa only [Finset.sum_const, smul_eq_mul, hc] using he
  let any (T : BitString n) := decide (∃ S ∈ fiveSets, all S T = true)
  have hAny : Synthesis interpretation (inputs n) {any} 3403 := by
    have hs := Synthesis.exists_mem fiveSets all (fun _ => 26) hAll
    simpa only [any, Finset.sum_const, smul_eq_mul, fiveSets_card] using hs
  exact Synthesis.congr_iff hAny.not (fun T => by simp [any, all, rowPass])

theorem sampleControl_size :
    complexity interpretation (single (sampleControl read)) ≤ 1743361 := by
  have h := Synthesis.forall_mem (Finset.univ : Finset (BitString 9))
    (fun a T => rowPass read T a) (fun _ => 3404) (fun a _ => rowPass_cost read a)
  have he := Synthesis.congr_iff h (g := sampleControl read) (fun T => by
    simp only [sampleControl, decide_eq_true_eq, Finset.mem_univ, true_implies])
  exact he.complexity_le.trans (by
    simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card]
    decide)

end Control

private noncomputable def touched (D : Finset Address) (a : BitString 9) : Finset (Fin 9) :=
  Finset.univ.filter fun j => readAddress a j false ∈ D ∨ readAddress a j true ∈ D

private theorem touched_card (D : Finset Address) (a : BitString 9) : (touched D a).card ≤ D.card := by
  let b (j : Fin 9) := !(decide (readAddress a j false ∈ D))
  apply Finset.card_le_card_of_injOn (fun j => readAddress a j (b j))
  · intro j hj
    rcases (Finset.mem_filter.mp hj).2 with hf | ht
    · simp [b, hf]
    · by_cases hf : readAddress a j false ∈ D
      · simp [b, hf]
      · simpa [b, hf] using ht
  · intro j _ k _ he
    have hh : (j, b j) = (k, b k) := readAddress_pair_injective a he
    exact congrArg Prod.fst hh

private theorem mismatch_untouched {h : Selector} (hh : ParityAnchored h)
    (e : Equiv.Perm (Fin 23)) (f g : Prefix) (D : Finset Address)
    (a : BitString 9) (j : Fin 9) (hj : j ∉ touched D a) :
    mismatch readAddress (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) a j = (f a ^^ g a) := by
  have hn (b : Bool) : readAddress a j b ∉ D := by
    intro hi
    apply hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    cases b
    · exact Or.inl hi
    · exact Or.inr hi
  unfold mismatch patch
  rw [sample_value hh, sample_value hh]
  simp [hn false, hn true]

theorem sampleControl_passes_transports {h : Selector} (hh : ParityAnchored h)
    (e : Equiv.Perm (Fin 23)) (f g : Prefix) (D : Finset Address) (hD : D.card ≤ 4) :
    sampleControl readAddress (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) = true ↔ f = g := by
  rw [sampleControl_iff]
  have ht (a : BitString 9) : (touched D a).card ≤ 4 := (touched_card D a).trans hD
  constructor
  · intro hAll
    by_contra hne
    obtain ⟨a, ha⟩ : ∃ a, f a ≠ g a := by by_contra! h; exact hne (funext h)
    let clean := Finset.univ \ touched D a
    have hClean : 5 ≤ clean.card := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (touched D a))
      rw [Finset.card_univ, Fintype.card_fin] at h
      change clean.card + (touched D a).card = 9 at h
      have ht' := ht a
      omega
    obtain ⟨S, hSub, hCard⟩ := Finset.exists_subset_card_eq hClean
    apply hAll a
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hCard⟩, fun j hj => ?_⟩
    have hJ := (Finset.mem_sdiff.mp (hSub hj)).2
    rw [mismatch_untouched hh e f g D a j hJ]
    cases hf : f a <;> cases hg : g a <;> simp_all
  · rintro rfl a ⟨S, hS, hAll⟩
    have hs : S ⊆ touched D a := by
      intro j hj
      by_contra hJ
      have h := hAll j hj
      rw [mismatch_untouched hh e f f D a j hJ, Bool.xor_self] at h
      cases h
    have h := (Finset.card_le_card hs).trans (ht a)
    have hCard := (Finset.mem_powersetCard.mp hS).2
    omega

noncomputable def sampleIndex : (BitString 9 × Fin 9 × Bool) ≃ Fin 9216 :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_prod, BitString.card, Fintype.card_fin, Fintype.card_bool]
    decide)

noncomputable def sampleRead (i : Fin 9216) : Address :=
  let a := sampleIndex.symm i
  readAddress a.1 a.2.1 a.2.2

/-- A circuit on the fixed sample bank handles the tests on all cuts. Even its
entire trace is identical when the cut is transported at fixed patch positions. -/
theorem common_sample_circuit {h : Selector} (hh : ParityAnchored h) :
    ∃ c : Circuit signature 9216 1, c.size ≤ 1743361 ∧
      (∀ T : BitString (2 ^ 32), c.eval interpretation (T ∘ sampleRead) 0 = sampleControl readAddress T) ∧
      ∀ (e e' : Equiv.Perm (Fin 23)) (f g : Prefix) (D : Finset Address) (w : Wire 9216 c.size),
        c.program.trace interpretation ((patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) ∘ sampleRead) w =
          c.program.trace interpretation ((patch D (mixed h f g ∘ tablePerm (liftTail 9 e'))) ∘ sampleRead) w := by
  let read (a : BitString 9) (j : Fin 9) (b : Bool) := sampleIndex (a, j, b)
  obtain ⟨c, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single (sampleControl read))
  have hRead (a : BitString 9) (j : Fin 9) (b : Bool) : sampleRead (read a j b) = readAddress a j b := by
    simp [sampleRead, read]
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hs]
    exact sampleControl_size read
  · intro T
    rw [congrFun (hc (T ∘ sampleRead)) 0]
    change sampleControl read (T ∘ sampleRead) = sampleControl readAddress T
    apply Bool.eq_iff_iff.mpr
    simp only [sampleControl_iff, mismatch, Function.comp_apply, hRead]
  · intro e e' f g D w
    have he : (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) ∘ sampleRead =
        (patch D (mixed h f g ∘ tablePerm (liftTail 9 e'))) ∘ sampleRead := by
      funext i
      let a := sampleIndex.symm i
      exact same_patched_sample hh e e' f g D a.1 a.2.1 a.2.2
    rw [he]

/-- One selector works for exact MCSP and also for a single small sampled
circuit on every transported cut, including all common patches. -/
theorem shared_sample_control :
    ∃ h : Selector, ParityAnchored h ∧ complexity interpretation (single (sampleControl readAddress)) ≤ 1743361 ∧
      ∀ (e : Equiv.Perm (Fin 23)) (f g : Prefix) (D : Finset Address), D.card ≤ 4 →
        (mcspSquare 32 (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) = true ↔ f = g) ∧
        (sampleControl readAddress (patch D (mixed h f g ∘ tablePerm (liftTail 9 e))) = true ↔ f = g) := by
  obtain ⟨h, hh, hMCSP⟩ := exists_parity_anchored_selector
  exact ⟨h, hh, sampleControl_size readAddress, fun e f g D hD =>
    ⟨patched_transport (fun e => square_comp_tablePerm (liftTail 9 e)) hMCSP e f g D hD,
      sampleControl_passes_transports hh e f g D hD⟩⟩

#print axioms sampleControl_size
#print axioms sample_side
#print axioms same_patched_sample
#print axioms shared_sample_control
#print axioms common_sample_circuit

end PvsNP.Frontier.PatchedCut
