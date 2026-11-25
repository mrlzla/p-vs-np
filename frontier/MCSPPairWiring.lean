module

public import MCSPNarrowCut

/-! Structural consequences of the split-pair swap bound. -/

@[expose] public section

namespace PvsNP.Frontier.PairWiring

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut NarrowCut

variable {n q r s : ℕ}

def exchangeWire (left right : Fin n) : Wire n q → Wire n q :=
  Wire.elim (fun i => .input (Equiv.swap left right i)) Wire.gate

def pairAnd (left right : Fin n) : Line signature n q :=
  ⟨.and, fun a => .input (if a = 0 then left else right)⟩

def pairOr (left right : Fin n) : Line signature n q :=
  ⟨.or, fun a => .input (if a = 0 then left else right)⟩

/-- A line either ignores both endpoints or reads exactly the pair with a commutative gate. -/
def SymmetricUse (line : Line signature n q) (left right : Fin n) : Prop :=
  (∀ a, line.wires a ≠ .input left ∧ line.wires a ≠ .input right) ∨
    line = pairAnd left right ∨ line = pairAnd right left ∨
    line = pairOr left right ∨ line = pairOr right left

theorem SymmetricUse.eval_exchange {line : Line signature n q} {left right : Fin n}
    (h : SymmetricUse line left right) (v : Wire n q → Bool) :
    interpretation line.op (fun a => v (exchangeWire left right (line.wires a))) =
      interpretation line.op (fun a => v (line.wires a)) := by
  rcases h with hIgnore | rfl | rfl | rfl | rfl
  · congr 1
    funext a
    apply congrArg v
    have hNot := hIgnore a
    cases he : line.wires a with
    | gate k => rfl
    | input i =>
      have hne₀ : i ≠ left := fun h => hNot.1 (he.trans (congrArg Wire.input h))
      have hne₁ : i ≠ right := fun h => hNot.2 (he.trans (congrArg Wire.input h))
      simp [exchangeWire, Equiv.swap_apply_of_ne_of_ne hne₀ hne₁]
  · simp [pairAnd, exchangeWire, interpretation, Bool.and_comm]
  · simp [pairAnd, exchangeWire, interpretation, Bool.and_comm]
  · simp [pairOr, exchangeWire, interpretation, Bool.or_comm]
  · simp [pairOr, exchangeWire, interpretation, Bool.or_comm]

theorem trace_exchange_of_symmetricUses (p : Program signature n q) (left right : Fin n)
    (h : ∀ k, SymmetricUse (p.lines k) left right) (x : BitString n) (w : Wire n q) :
    p.trace interpretation (x ∘ Equiv.swap left right) w =
      p.trace interpretation x (exchangeWire left right w) := by
  refine p.wire_induction (P := fun w => p.trace interpretation (x ∘ Equiv.swap left right) w =
    p.trace interpretation x (exchangeWire left right w)) (fun _ => rfl) ?_ w
  intro k ih
  change _ = p.trace interpretation x (.gate k)
  rw [p.trace_gate, p.trace_gate]
  simp only [ih]
  exact (h k).eval_exchange (p.trace interpretation x)

theorem swapPair_eq_input_exchange (key : BitString r × BitString s)
    (x : BitString (2 ^ (r + (s + 1)))) :
    swapPair key x = x ∘ Equiv.swap (position key.1 false key.2) (position key.1 true key.2) := by
  classical
  funext i
  obtain ⟨⟨a, b, u⟩, rfl⟩ := (positionEquiv r s).surjective i
  change swapPair key x (position a b u) = x
    ((Equiv.swap (position key.1 false key.2) (position key.1 true key.2)) (position a b u))
  have hp : (positionEquiv r s).symm (position a b u) = (a, b, u) :=
    (positionEquiv r s).symm_apply_apply (a, b, u)
  simp only [swapPair, hp]
  by_cases he : (a, u) = key
  · subst key
    cases b <;> simp
  · have hne (j : Bool) : position a b u ≠ position key.1 j key.2 := by
      intro h
      change positionEquiv r s (a, b, u) = positionEquiv r s (key.1, j, key.2) at h
      have h' := (positionEquiv r s).injective h
      exact he (congrArg (fun z : BitString r × Bool × BitString s => (z.1, z.2.2)) h')
    rw [ite_eq_right he, Equiv.swap_apply_of_ne_of_ne (hne false) (hne true)]

def PairWiredSymmetrically (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (key : BitString r × BitString s) : Prop :=
  ∀ k, SymmetricUse (c.program.lines k) (position key.1 false key.2) (position key.1 true key.2)

/-- A pair outside the symmetric class has a gate that reads at least one endpoint
and is not a paired AND or OR. -/
theorem exists_nonsymmetric_consumer (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (key : BitString r × BitString s) (h : ¬ PairWiredSymmetrically c key) :
    ∃ k : Fin c.size,
      (∃ a : Fin (signature.Arity (c.program.lines k).op),
        (c.program.lines k).wires a = .input (position key.1 false key.2) ∨
        (c.program.lines k).wires a = .input (position key.1 true key.2)) ∧
      ¬ SymmetricUse (c.program.lines k) (position key.1 false key.2) (position key.1 true key.2) := by
  classical
  obtain ⟨k, hk⟩ := not_forall.mp h
  refine ⟨k, ?_, hk⟩
  by_contra hNo
  apply hk
  left
  intro a
  exact ⟨fun ha => hNo ⟨a, Or.inl ha⟩, fun ha => hNo ⟨a, Or.inr ha⟩⟩

theorem eval_swap_of_symmetric_pair (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hOutput : ∃ k, c.outputs 0 = .gate k) {key : BitString r × BitString s}
    (h : PairWiredSymmetrically c key) (x : BitString (2 ^ (r + (s + 1)))) :
    c.eval interpretation (swapPair key x) 0 = c.eval interpretation x 0 := by
  obtain ⟨k, hk⟩ := hOutput
  rw [swapPair_eq_input_exchange]
  change c.program.trace interpretation _ (c.outputs 0) = c.program.trace interpretation x (c.outputs 0)
  rw [hk]
  exact trace_exchange_of_symmetricUses _ _ _ h x (.gate k)

theorem output_is_gate_of_accepts_zero (c : Circuit signature n 1)
    (hTrue : c.eval interpretation (fun _ => false) 0 = true) : ∃ k, c.outputs 0 = .gate k := by
  cases he : c.outputs 0 with
  | gate k => exact ⟨k, rfl⟩
  | input i =>
    change c.program.trace interpretation (fun _ => false) (c.outputs 0) = true at hTrue
    rw [he] at hTrue
    cases hTrue

open scoped Classical in
/-- At most the counting allowance many split pairs have only symmetric direct uses.
This is true for all correct circuits, including minimum circuits. -/
theorem card_symmetrically_wired_pairs_le (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (r + (s + 1))))) :
    ((Finset.univ : Finset (BitString r × BitString s)).filter (PairWiredSymmetrically c)).card ≤
      descriptionBitBound (r + (s + 1)) := by
  classical
  have hOutput := output_is_gate_of_accepts_zero c
    ((congrFun (hc _) 0).trans (mcspSquare_constant_table _ (by omega) false))
  apply mcspSquare_swap_invariance_bound
  intro key hk x
  exact (congrFun (hc (swapPair key x)) 0).symm.trans
    ((eval_swap_of_symmetric_pair c hOutput (Finset.mem_filter.mp hk).2 x).trans (congrFun (hc x) 0))

open scoped Classical in
theorem many_pairs_have_nonsymmetric_use (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (r + (s + 1))))) :
    2 ^ (r + s) - descriptionBitBound (r + (s + 1)) ≤
      ((Finset.univ : Finset (BitString r × BitString s)).filter
        (fun key => ¬ PairWiredSymmetrically c key)).card := by
  classical
  have hBound := card_symmetrically_wired_pairs_le c hc
  have hParts := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (BitString r × BitString s))) (p := PairWiredSymmetrically c)
  simp only [Finset.card_univ, Fintype.card_prod, BitString.card, ← pow_add] at hParts
  omega

end PvsNP.Frontier.PairWiring
