module

public import MCSPSuperTwoN
public import Complexity.Computability.Circuit.Boolean.Substitution

/-! Original gate identities under nested substitutions. -/

@[expose] public section

namespace PvsNP.Frontier.RestrictionCharges

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

variable {n k l g : ℕ}

def compose (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) : Fin n → Fin l ⊕ Bool :=
  fun i => (ρ i).elim τ Sum.inr

theorem substitute_compose (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) (x : BitString l) :
    substitute (compose ρ τ) x = substitute ρ (substitute τ x) := by
  funext i
  cases h : ρ i <;> simp [substitute, compose, h]

def restrictedWire (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) (w : Wire n g) :
    BooleanFunction k := fun x => p.trace interpretation (substitute ρ x) w

def varies (f : BooleanFunction k) : Prop := ∃ x y, f x ≠ f y

noncomputable def gateCost (f : BooleanFunction k) : ℕ := open scoped Classical in
  if varies f then 1 else 0

/-- Original gate indices whose wire functions are nonconstant on the restriction. -/
noncomputable def surviving (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun j => varies (restrictedWire p ρ (.gate j))

theorem surviving_nested_subset (p : Program signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (τ : Fin k → Fin l ⊕ Bool) :
    surviving p (compose ρ τ) ⊆ surviving p ρ := by
  classical
  intro j hj
  obtain ⟨x, y, hxy⟩ := (Finset.mem_filter.mp hj).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, substitute τ x, substitute τ y, ?_⟩
  simpa only [restrictedWire, substitute_compose] using hxy

noncomputable def firstLost (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool) : Finset (Fin g) :=
  Finset.univ \ surviving p ρ

noncomputable def secondLost (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) : Finset (Fin g) :=
  surviving p ρ \ surviving p (compose ρ τ)

theorem losses_disjoint (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) :
    Disjoint (firstLost p ρ) (secondLost p ρ τ) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

theorem card_partition (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) :
    (firstLost p ρ).card + (secondLost p ρ τ).card + (surviving p (compose ρ τ)).card = g := by
  have h₁ := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (surviving p ρ))
  have h₂ := Finset.card_sdiff_add_card_eq_card (surviving_nested_subset p ρ τ)
  simp only [Finset.card_univ, Fintype.card_fin] at h₁
  change (firstLost p ρ).card + (surviving p ρ).card = g at h₁
  change (secondLost p ρ τ).card + (surviving p (compose ρ τ)).card = (surviving p ρ).card at h₂
  omega

private def supplied (k : ℕ) : Set (BooleanFunction k) :=
  inputs k ∪ {(fun _ => false), (fun _ => true)}

private theorem supplied_const (k : ℕ) (b : Bool) : (fun _ => b) ∈ supplied k := by
  cases b <;> simp [supplied]

private theorem restrictedWire_castSucc (p : Program signature n g) (line : Line signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) (w : Wire n g) :
    restrictedWire (p.gate line) ρ w.castSucc = restrictedWire p ρ w :=
  funext fun _ => Program.trace_gate_castSucc _ _ _ _ _

private theorem restrictedWire_last (p : Program signature n g) (line : Line signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) :
    restrictedWire (p.gate line) ρ (.gate (Fin.last g)) =
      fun x => interpretation line.op (fun a => restrictedWire p ρ (line.wires a) x) :=
  funext fun _ => Program.eval_gate_last _ _ _ _

private theorem surviving_gate_card (p : Program signature n g) (line : Line signature n g)
    (ρ : Fin n → Fin k ⊕ Bool) :
    (surviving (p.gate line) ρ).card = (surviving p ρ).card +
      gateCost (restrictedWire (p.gate line) ρ (.gate (Fin.last g))) := by
  classical
  have h {g' : ℕ} (q : Program signature n g') :
      (surviving q ρ).card = ∑ j : Fin g', gateCost (restrictedWire q ρ (.gate j)) := by
    unfold gateCost
    rw [← Finset.sum_filter]
    simp [surviving]
  rw [h, h, Fin.sum_univ_castSucc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change gateCost (restrictedWire (p.gate line) ρ (Wire.gate j).castSucc) = _
  rw [restrictedWire_castSucc]

private theorem synth_restricted (ρ : Fin n → Fin k ⊕ Bool) (p : Program signature n g) :
    Synthesis interpretation (supplied k) (Set.range (restrictedWire p ρ)) (surviving p ρ).card := by
  classical
  induction p with
  | empty =>
    apply (Synthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (Nat.zero_le _)
    rintro _ ⟨w, rfl⟩
    cases w with
    | input i =>
      cases h : ρ i with
      | inl j =>
        apply Set.mem_union_left
        exact ⟨j, funext fun x => (substitute_inl (x := x) h).symm⟩
      | inr b =>
        have he : restrictedWire (.empty : Program signature n 0) ρ (.input i) = fun _ => b :=
          funext fun x => substitute_inr h
        exact he.symm ▸ supplied_const k b
    | gate j => exact j.elim0
  | @gate g p line ih =>
    let last := restrictedWire (p.gate line) ρ (.gate (Fin.last g))
    have hNew : Synthesis interpretation (supplied k ∪ Set.range (restrictedWire p ρ)) {last}
        (gateCost last) := by
      by_cases hv : varies last
      · simp only [gateCost, hv, ite_true]
        change Synthesis interpretation _ {restrictedWire (p.gate line) ρ (.gate (Fin.last g))} 1
        rw [restrictedWire_last]
        exact Synthesis.gate line.op (fun a => restrictedWire p ρ (line.wires a))
          (fun a => Set.mem_union_right _ ⟨line.wires a, rfl⟩)
      · simp only [gateCost, hv, ite_false]
        apply Synthesis.of_mem
        let b := last (fun _ => false)
        have he : last = fun _ => b := by
          funext x
          by_contra hn
          exact hv ⟨x, fun _ => false, hn⟩
        rw [he]
        exact Set.mem_union_left _ (supplied_const k b)
    refine (ih.comp hNew).mono Set.Subset.rfl ?_ ?_
    · rintro _ ⟨w, rfl⟩
      cases w with
      | input i => exact Set.mem_union_left _ ⟨.input i, rfl⟩
      | gate j =>
        refine Fin.lastCases ?_ (fun i => ?_) j
        · exact Set.mem_union_right _ (Set.mem_singleton last)
        · exact Set.mem_union_left _ ⟨.gate i, (restrictedWire_castSucc p line ρ (.gate i)).symm⟩
    · rw [surviving_gate_card]

/-- Rebuild only the nonconstant original gates, with at most two shared constants.
The surviving set is indexed by gates of the original program. -/
theorem restricted_complexity_le (p : Program signature n g) (root : Wire n g)
    (ρ : Fin n → Fin k ⊕ Bool) :
    complexity interpretation (single (restrictedWire p ρ root)) ≤ (surviving p ρ).card + 2 := by
  have constants :
      Synthesis interpretation (inputs k) {(fun _ => false), (fun _ => true)} 2 := by
    have hfalse : Synthesis interpretation (inputs k) {fun _ => false} 1 := Synthesis.const false
    have htrue : Synthesis interpretation (inputs k) {fun _ => true} 1 := Synthesis.const true
    simpa only [Set.singleton_union, Nat.one_add, Nat.reduceAdd] using hfalse.union htrue
  have h := constants.trans (synth_restricted ρ p)
  have hOne := h.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ⟨root, rfl⟩) le_rfl
  simpa only [Nat.add_comm] using hOne.complexity_le

#print axioms card_partition
#print axioms restricted_complexity_le

end PvsNP.Frontier.RestrictionCharges
