module

public import MCSPRefinedProbeControl

/-! The relaxed control also separates the transported mixed probes. -/

@[expose] public section

namespace PvsNP.Frontier.RefinedProbeControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut PermutedCut Downstream
open InvariantControl (unit point pointEquiv point_cons)

def blank (w : ℕ) : BitString w := fun _ => false

private theorem cons_blank_mem (b : Bool) : Fin.cons b (blank 22) ∈ sample 23 := by
  refine Finset.mem_image.mpr ⟨(if b then some (0 : Fin 23) else none, none),
    Finset.mem_univ _, ?_⟩
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · cases b <;> simp [pairPoint, pulse, unit]
  · cases b <;> simp [pairPoint, pulse, unit, blank]

private theorem cons_unit_mem (b : Bool) (k : Fin 22) : Fin.cons b (unit k) ∈ sample 23 := by
  refine Finset.mem_image.mpr ⟨(if b then some (0 : Fin 23) else none, some k.succ),
    Finset.mem_univ _, ?_⟩
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · cases b <;> simp [pairPoint, pulse, unit, Ne.symm (Fin.succ_ne_zero k)]
  · cases b <;> simp [pairPoint, pulse, unit]

private theorem pattern_same (p : Pattern 23) (b : Bool) (j : Fin 22)
    (hne : p.2 ≠ some j.succ) :
    pattern p (Fin.cons b (blank 22)) = pattern p (Fin.cons b (unit j)) := by
  obtain ⟨v, i⟩ := p
  cases i with
  | none => rfl
  | some i =>
    revert hne
    refine Fin.cases ?_ (fun k => ?_) i
    · intro _
      rfl
    · intro hne
      by_cases hk : k = j
      · subst k
        exact (hne rfl).elim
      · simp [pattern, blank, unit, hk]

private theorem mixed_read (h : BooleanFunction 22) (f g : RefinedCut.Coordinate → Bool)
    (a : BitString 9) (b : Bool) (t : BitString 22) :
    splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)
        (point (s := 22) a (Fin.cons b t)) =
      if b ^^ h t then f (RefinedCut.pick a b) else g (RefinedCut.pick a b) := by
  have hl := label_point a (Fin.cons b t)
  rw [point_cons] at hl
  rw [point_cons, splice, mask_at_position]
  simp only [Function.comp_apply, hl, Fin.cons_zero]

def Anchored (h : BooleanFunction 22) : Prop :=
  h (blank 22) = false ∧ h (unit (0 : Fin 22)) = true ∧ h (unit (1 : Fin 22)) = true

theorem equality_of_anchored (h : BooleanFunction 22) (ha : Anchored h)
    (f g : RefinedCut.Coordinate → Bool) :
    control (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g := by
  constructor
  · intro hc
    obtain ⟨hcSpecial, hcRegular⟩ := (control_iff _).mp hc
    have same (a : BitString 9) (b : Bool) : f (RefinedCut.pick a b) = g (RefinedCut.pick a b) := by
      by_cases hs : RefinedCut.high a = RefinedCut.zeroHigh
      · obtain ⟨p, hp⟩ := hcSpecial a hs
        by_contra hne
        have forces (j : Fin 22) (hj : h (unit j) = true) : p.2 = some j.succ := by
          by_contra hnot
          have h0 := hp (Fin.cons b (blank 22)) (cons_blank_mem b)
          have h1 := hp (Fin.cons b (unit j)) (cons_unit_mem b j)
          have he := h0.trans ((pattern_same p b j hnot).trans h1.symm)
          rw [mixed_read, mixed_read, ha.1, hj] at he
          cases b
          · exact hne he.symm
          · exact hne he
        have he := (forces 0 ha.2.1).symm.trans (forces 1 ha.2.2)
        have hc : (some (0 : Fin 22).succ : Option (Fin 23)) ≠ some (1 : Fin 22).succ := by decide
        exact hc he
      · have he := hcRegular a hs (Fin.cons false (blank 22)) (Fin.cons true (blank 22))
        rw [mixed_read, mixed_read, ha.1] at he
        simpa [RefinedCut.pick, hs] using he.symm
    funext q
    obtain ⟨⟨a,b⟩, hq⟩ := RefinedCut.pick_surjective q
    change RefinedCut.pick a b = q at hq
    exact hq ▸ same a b
  · rintro rfl
    rw [splice_self]
    exact accepts_refined f

def anchors : Finset (BitString 22) := {blank 22, unit (0 : Fin 22), unit (1 : Fin 22)}

private theorem anchors_card : anchors.card ≤ 3 := by
  classical
  have h₀ := Finset.card_insert_le (blank 22) ({unit (0 : Fin 22), unit (1 : Fin 22)} : Finset _)
  have h₁ := Finset.card_insert_le (unit (0 : Fin 22)) ({unit (1 : Fin 22)} : Finset _)
  change anchors.card ≤ _ at h₀
  rw [Finset.card_singleton] at h₁
  omega

theorem exists_common_selector :
    ∃ h : BooleanFunction 22, Anchored h ∧
      ∀ f g : RefinedCut.Coordinate → Bool,
        mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g := by
  let p : BooleanFunction 22 := fun t => decide (t ≠ blank 22)
  have hExp : 28760 + 1 < 2 ^ 22 - anchors.card := by
    have h := anchors_card
    have hpow : (2 : ℕ) ^ 22 = 4194304 := by decide
    rw [hpow]
    omega
  obtain ⟨h, hp, _, heq⟩ := RefinedCut.exists_refined_equality_cut_with anchors p hExp
  have ne (j : Fin 22) : unit j ≠ blank 22 := by
    intro he
    have h' := congrFun he j
    simp [unit, blank] at h'
  have m0 : blank 22 ∈ anchors := Finset.mem_insert_self ..
  have m1 : unit (0 : Fin 22) ∈ anchors := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
  have m2 : unit (1 : Fin 22) ∈ anchors :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  exact ⟨h, ⟨(hp _ m0).trans (by simp [p]), (hp _ m1).trans (decide_eq_true (ne _)),
    (hp _ m2).trans (decide_eq_true (ne _))⟩, heq⟩

/-- The control and exact MCSP agree on every transported diagonal or mixed probe
of one shared refined selector. -/
theorem common_transport_test :
    ∃ h : BooleanFunction 22, ∀ (e : Equiv.Perm (Fin 23)) (f g : RefinedCut.Coordinate → Bool),
      let p := tablePerm (liftTail 9 e)
      let t := splice (mask 9 h ∘ p) (f ∘ (RefinedCut.label ∘ p)) (g ∘ (RefinedCut.label ∘ p))
      (control t = true ↔ f = g) ∧ (mcspSquare 32 t = true ↔ f = g) := by
  obtain ⟨h, hh, hEq⟩ := exists_common_selector
  refine ⟨h, fun e f g => ⟨?_, ?_⟩⟩
  · exact transport_equality control (tablePerm (liftTail 9 e)) (control_perm e)
      (mask 9 h) RefinedCut.label (equality_of_anchored h hh) f g
  · exact transport_equality (mcspSquare 32) (tablePerm (liftTail 9 e)) (square_comp_tablePerm _)
      (mask 9 h) RefinedCut.label hEq f g

#print axioms common_transport_test

end PvsNP.Frontier.RefinedProbeControl
