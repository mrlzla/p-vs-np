module

public import MCSPOrbitCharge

/-! A symmetric control that admits all transported refined probes. -/

@[expose] public section

namespace PvsNP.Frontier.RefinedProbeControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut PermutedCut
open InvariantControl (unit unit_perm point pointEquiv perm_point)
open SampleControls (agreesOn agreesOn_eq_true agreesOn_cost)

def pulse {w : ℕ} (c : Option (Fin w)) : BitString w :=
  c.elim (fun _ => false) unit

def pairPoint {w : ℕ} (p : Option (Fin w) × Option (Fin w)) : BitString w :=
  fun z => pulse p.1 z || pulse p.2 z

/-- All tail assignments formed by the union of at most two singleton supports. -/
noncomputable def sample (w : ℕ) : Finset (BitString w) :=
  Finset.univ.image (pairPoint (w := w))

theorem sample_card (w : ℕ) : (sample w).card ≤ (w + 1) * (w + 1) := by
  unfold sample
  apply Finset.card_image_le.trans
  simp [Fintype.card_prod, Fintype.card_option]

private theorem pulse_perm {w : ℕ} (e : Equiv.Perm (Fin w)) (c : Option (Fin w)) :
    pulse c ∘ e = pulse (c.map e.symm) := by
  cases c with
  | none => rfl
  | some i => exact unit_perm i e

theorem sample_perm {w : ℕ} (e : Equiv.Perm (Fin w)) {z : BitString w} (hz : z ∈ sample w) :
    z ∘ e ∈ sample w := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
  refine Finset.mem_image.mpr ⟨(p.1.map e.symm, p.2.map e.symm), Finset.mem_univ _, ?_⟩
  funext i
  exact congrArg₂ (· || ·) (congrFun (pulse_perm e p.1).symm i)
    (congrFun (pulse_perm e p.2).symm i)

abbrev Pattern (w : ℕ) := Bool × Option (Fin w)

def pattern {w : ℕ} (p : Pattern w) (z : BitString w) : Bool :=
  p.1 ^^ p.2.elim false z

theorem pattern_perm {w : ℕ} (e : Equiv.Perm (Fin w)) (p : Pattern w) (z : BitString w) :
    pattern p (z ∘ e) = pattern (p.1, p.2.map e) z := by
  obtain ⟨b, i⟩ := p
  cases i <;> rfl

def chosen : Finset (BitString 9) :=
  Finset.univ.filter (fun a => RefinedCut.high a = RefinedCut.zeroHigh)

private theorem chosen_card : chosen.card = 32 := by
  have h : chosen = (Finset.univ : Finset (BitString 5)).image
      (fun p => Fin.append p RefinedCut.zeroHigh) := by
    ext a
    simp only [chosen, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨RefinedCut.low a, ?_⟩
      rw [← h]
      exact Fin.append_castAdd_natAdd
    · rintro ⟨p, rfl⟩
      exact Fin.append_comp_natAdd ..
  have hinj : Function.Injective (fun p : BitString 5 => Fin.append p RefinedCut.zeroHigh) := by
    intro p q h
    funext i
    simpa using congrFun h (Fin.castAdd 4 i)
  rw [h, Finset.card_image_of_injective _ hinj, Finset.card_univ, BitString.card]
  decide

private theorem complement_card : chosenᶜ.card = 480 := by
  rw [Finset.card_compl, BitString.card, chosen_card]
  decide

section Family

variable {r s : ℕ}

abbrev GridSize (r s : ℕ) := 2 ^ (r + (s + 1))

noncomputable def rowPositions (s : ℕ) (a : BitString r) : Finset (Fin (GridSize r s)) :=
  (Finset.univ : Finset (BitString (s + 1))).image (point (s := s) a)

private theorem rowPositions_card (s : ℕ) (a : BitString r) : (rowPositions s a).card = 2 ^ (s + 1) := by
  have hinj : Function.Injective (point (s := s) a) := by
    intro z t h
    exact congrArg Prod.snd ((pointEquiv r s).injective h)
  rw [rowPositions, Finset.card_image_of_injective _ hinj, Finset.card_univ, BitString.card]

noncomputable def checksPattern (a : BitString r) (p : Pattern (s + 1)) (T : BitString (GridSize r s)) :
    Bool := open scoped Classical in
  decide (∀ z ∈ sample (s + 1), T (point (s := s) a z) = pattern p z)

noncomputable def chosenRow (s : ℕ) (a : BitString r) (T : BitString (GridSize r s)) : Bool :=
  open scoped Classical in decide (∃ p : Pattern (s + 1), checksPattern a p T = true)

noncomputable def family (s : ℕ) (A : Finset (BitString r)) (T : BitString (GridSize r s)) : Bool :=
  open scoped Classical in
  decide (∀ a ∈ A, chosenRow s a T = true) &&
    decide (∀ a ∈ Aᶜ, agreesOn (rowPositions s a) T = true)

theorem family_iff (A : Finset (BitString r)) (T : BitString (GridSize r s)) :
    family s A T = true ↔
      (∀ a ∈ A, ∃ p : Pattern (s + 1), ∀ z ∈ sample (s + 1), T (point (s := s) a z) = pattern p z) ∧
      (∀ a ∉ A, ∀ z z' : BitString (s + 1), T (point (s := s) a z) = T (point (s := s) a z')) := by
  classical
  simp only [family, chosenRow, checksPattern, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_compl]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h a ha z z'
    apply (agreesOn_eq_true _ _).mp (h a ha)
    · exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨z', Finset.mem_univ _, rfl⟩
  · intro h a ha
    apply (agreesOn_eq_true _ _).mpr
    intro i hi j hj
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z', _, rfl⟩ := Finset.mem_image.mp hj
    exact h a ha z z'

theorem family_perm (A : Finset (BitString r)) (e : Equiv.Perm (Fin (s + 1)))
    (T : BitString (GridSize r s)) :
    family s A (T ∘ tablePerm (liftTail r e)) = family s A T := by
  apply Bool.eq_iff_iff.mpr
  simp only [family_iff]
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨p, hp⟩ := hA a ha
      refine ⟨(p.1, p.2.map e.symm), fun z hz => ?_⟩
      have he := hp (z ∘ e.symm) (sample_perm e.symm hz)
      rw [pattern_perm] at he
      simpa [Function.comp_def] using he
    · intro a ha z z'
      have he := hB a ha (z ∘ e.symm) (z' ∘ e.symm)
      simpa [Function.comp_def] using he
  · rintro ⟨hA, hB⟩
    constructor
    · intro a ha
      obtain ⟨p, hp⟩ := hA a ha
      refine ⟨(p.1, p.2.map e), fun z hz => ?_⟩
      rw [Function.comp_apply, perm_point, ← pattern_perm]
      exact hp _ (sample_perm e hz)
    · intro a ha z z'
      simp only [Function.comp_apply, perm_point]
      exact hB a ha (z ∘ e) (z' ∘ e)

private theorem codeCost (a : BitString r) (p : Pattern (s + 1)) :
    Synthesis interpretation (inputs (GridSize r s)) {checksPattern a p} ((s + 2) * (s + 2) * 2 + 1) := by
  classical
  let F (z : BitString (s + 1)) (T : BitString (GridSize r s)) := decide (T (point (s := s) a z) = pattern p z)
  obtain ⟨g, he, hg⟩ := Synthesis.exists_forall_mem (sample (s + 1)) F
    (c := 1) (sample_card (s + 1)) (fun z _ =>
      Synthesis.literal (s := inputs (GridSize r s))
        (f := fun T => T (point (s := s) a z)) ⟨point (s := s) a z, rfl⟩ (pattern p z))
  exact Synthesis.congr_iff hg (fun T => (he T).trans (by simp [checksPattern, F]))

private theorem chosenCost (s : ℕ) (a : BitString r) :
    Synthesis interpretation (inputs (GridSize r s)) {chosenRow s a}
      (2 * (s + 2) * ((s + 2) * (s + 2) * 2 + 2) + 1) := by
  classical
  have hCard : (Finset.univ : Finset (Pattern (s + 1))).card ≤ 2 * (s + 2) := by
    simp [Fintype.card_prod, Fintype.card_option]
  obtain ⟨g, he, hg⟩ := Synthesis.exists_exists_mem Finset.univ (checksPattern a)
    (c := (s + 2) * (s + 2) * 2 + 1) hCard (fun p _ => codeCost a p)
  exact Synthesis.congr_iff hg (fun T => (he T).trans (by simp [chosenRow]))

private theorem family_size (s : ℕ) (A : Finset (BitString r)) :
    complexity interpretation (single (family s A)) ≤
      A.card * (2 * (s + 2) * ((s + 2) * (s + 2) * 2 + 2) + 2) +
        Aᶜ.card * (2 * 2 ^ (s + 1) + 5) + 3 := by
  classical
  have hA := Synthesis.forall_mem A (chosenRow s) _ (fun a _ => chosenCost s a)
  have hB := Synthesis.forall_mem Aᶜ (fun a => agreesOn (rowPositions s a))
    (fun _ => 2 * 2 ^ (s + 1) + 4) (fun a _ => by rw [← rowPositions_card s a]; exact agreesOn_cost _)
  have h := Synthesis.congr_iff (hA.and hB) (g := family s A) (fun T => by simp [family])
  have hw := h.complexity_le
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hw
  exact hw.trans (by ring_nf; exact le_rfl)

end Family

abbrev N := GridSize 9 22

noncomputable def control : BooleanFunction N := family 22 chosen

theorem control_iff (T : BitString N) :
    control T = true ↔
      (∀ a, RefinedCut.high a = RefinedCut.zeroHigh →
        ∃ p : Pattern 23, ∀ z ∈ sample 23, T (point (s := 22) a z) = pattern p z) ∧
      (∀ a, RefinedCut.high a ≠ RefinedCut.zeroHigh → ∀ z z' : BitString 23,
        T (point (s := 22) a z) = T (point (s := 22) a z')) := by
  have hMem (a : BitString 9) : a ∈ chosen ↔ RefinedCut.high a = RefinedCut.zeroHigh := by
    simp only [chosen, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨hchosen, hregular⟩ := (family_iff (r := 9) (s := 22) chosen T).mp h
    exact ⟨fun a ha => hchosen a ((hMem a).mpr ha),
      fun a ha => hregular a (fun hm => ha ((hMem a).mp hm))⟩
  · rintro ⟨hchosen, hregular⟩
    exact (family_iff (r := 9) (s := 22) chosen T).mpr
      ⟨fun a ha => hchosen a ((hMem a).mp ha),
        fun a ha => hregular a (fun he => ha ((hMem a).mpr he))⟩

theorem control_perm (e : Equiv.Perm (Fin 23)) (T : BitString N) :
    control (T ∘ tablePerm (liftTail 9 e)) = control T :=
  family_perm (s := 22) chosen e T

theorem control_size : complexity interpretation (single control) + 535095901 ≤ 2 * N := by
  have hw := family_size 22 chosen
  rw [chosen_card, complement_card] at hw
  exact (Nat.add_le_add_right hw 535095901).trans (by decide)

private theorem label_at (a : BitString 9) (b : Bool) (t : BitString 22) :
    RefinedCut.label (position a b t) = RefinedCut.pick a b := by
  change RefinedCut.label (positionEquiv 9 22 (a, b, t)) = _
  simp [RefinedCut.label]

theorem label_point (a : BitString 9) (z : BitString 23) :
    RefinedCut.label (point (s := 22) a z) = RefinedCut.pick a (z 0) := by
  have he : Fin.cons (z 0) (fun j : Fin 22 => z j.succ) = z := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hl : RefinedCut.label (point (s := 22) a (Fin.cons (z 0) (fun j : Fin 22 => z j.succ))) =
      RefinedCut.pick a (z 0) := label_at a (z 0) (fun j : Fin 22 => z j.succ)
  rw [he] at hl
  exact hl

private theorem pattern_for_head (v : Bool → Bool) :
    ∃ p : Pattern 23, ∀ z : BitString 23, v (z 0) = pattern p z := by
  refine ⟨(v false, if v false = v true then none else some 0), fun z => ?_⟩
  cases hz : z 0 <;> cases h₀ : v false <;> cases h₁ : v true <;> simp_all [pattern]

theorem accepts_refined (f : RefinedCut.Coordinate → Bool) : control (f ∘ RefinedCut.label) = true := by
  apply (control_iff _).mpr
  constructor
  · intro a _
    obtain ⟨p, hp⟩ := pattern_for_head (fun b => f (RefinedCut.pick a b))
    refine ⟨p, fun z _ => ?_⟩
    simp only [Function.comp_apply, label_point, hp]
  · intro a ha z z'
    simp only [Function.comp_apply, label_point]
    cases z 0 <;> cases z' 0 <;> simp [RefinedCut.pick, ha]

private theorem accepts_reindexed {n : ℕ} {α : Type*} (f : BooleanFunction n)
    (p : Equiv.Perm (Fin n)) (hinv : ∀ T, f (T ∘ p) = f T)
    (code : α → Bool) (label : Fin n → α) (h : f (code ∘ label) = true) :
    f (code ∘ (label ∘ p)) = true :=
  (hinv (code ∘ label)).trans h

theorem accepts_transported (e : Equiv.Perm (Fin 23)) (f : RefinedCut.Coordinate → Bool) :
    control (f ∘ (RefinedCut.label ∘ tablePerm (liftTail 9 e))) = true :=
  accepts_reindexed (n := N) control (tablePerm (liftTail 9 e)) (control_perm e)
    f RefinedCut.label (accepts_refined f)

/-- An entire chosen row outside the sample remains unconstrained. -/
theorem family_accepted_count_lower {r s : ℕ} (A : Finset (BitString r))
    (center : BitString r) (hc : center ∈ A) :
    2 ^ (2 ^ (s + 1) - (sample (s + 1)).card) ≤ (acceptingTables (family s A)).card := by
  classical
  let outside := (Finset.univ : Finset (BitString (s + 1))) \ sample (s + 1)
  let fill (u : outside → Bool) (i : Fin (GridSize r s)) :=
    let z := (pointEquiv r s).symm i
    if hz : z.1 = center ∧ z.2 ∈ outside then u ⟨z.2, hz.2⟩ else false
  have readFill (u : outside → Bool) (a : BitString r) (z : BitString (s + 1)) :
      fill u (point (s := s) a z) =
        if hz : a = center ∧ z ∈ outside then u ⟨z, hz.2⟩ else false := by
    unfold fill point
    rw [Equiv.symm_apply_apply]
  have hAccept (u : outside → Bool) : family s A (fill u) = true := by
    apply (family_iff A _).mpr
    constructor
    · intro a _
      refine ⟨(false, none), fun z hz => ?_⟩
      have hnot : z ∉ outside := fun h => (Finset.mem_sdiff.mp h).2 hz
      rw [readFill]
      simp [hnot, pattern]
    · intro a ha z z'
      have hne : a ≠ center := fun he => ha (he.symm ▸ hc)
      rw [readFill, readFill]
      simp [hne]
  let embed (u : outside → Bool) : acceptingTables (family s A) :=
    ⟨fill u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAccept u⟩⟩
  have hi : Function.Injective embed := by
    intro u v he
    funext z
    have h := congrFun (congrArg Subtype.val he) (point (s := s) center z.val)
    change fill u _ = fill v _ at h
    rw [readFill, readFill] at h
    simpa [z.property] using h
  have hout : outside.card = 2 ^ (s + 1) - (sample (s + 1)).card := by
    simp [outside, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hout] using
    Fintype.card_le_of_injective embed hi

set_option linter.constructorNameAsVariable false in
theorem accepted_count_lower :
    2 ^ (2 ^ (22 + 1) - (sample (22 + 1)).card) ≤ (acceptingTables control).card := by
  let center : BitString 9 := fun _ => false
  have hChosen : center ∈ chosen := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  unfold control
  exact family_accepted_count_lower (r := 9) (s := 22) chosen center hChosen

#print axioms control_size
#print axioms control_perm
#print axioms accepts_transported
#print axioms accepted_count_lower

end PvsNP.Frontier.RefinedProbeControl
