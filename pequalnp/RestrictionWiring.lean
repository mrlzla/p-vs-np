import PEqualNP.Outside.L_meta_169
import PEqualNP.Outside.L_meta_170
import PEqualNP.Outside.L_meta_171
import PEqualNP.Outside.L_meta_193

/-! Restriction and fan-out consequences of Brilliant's circuit rewrites in its pinned model. -/

namespace PvsNP.PEqualNPAudit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- An essential input with two nonconstant restrictions saves at least two gates
on one of its two settings in a minimum circuit. -/
theorem exists_two_gate_saving {n : ℕ} {C : Circuit} (hmin : IsMinimalCircuit (n + 1) C)
    (hdep : ∃ y, circuitFun (n + 1) C (Fin.snoc y false) ≠
      circuitFun (n + 1) C (Fin.snoc y true))
    (hnonconstant : ∀ b : Bool, ∃ y y', circuitFun (n + 1) C (Fin.snoc y b) ≠
      circuitFun (n + 1) C (Fin.snoc y' b)) :
    ∃ (b : Bool) (s : ℕ), HasCircuitSize n (fun y => circuitFun (n + 1) C (Fin.snoc y b)) s ∧
      s + 2 ≤ C.size := by
  classical
  by_contra h
  have tight (b : Bool) (s : ℕ)
      (hs : HasCircuitSize n (fun y => circuitFun (n + 1) C (Fin.snoc y b)) s) :
      C.size ≤ s + 1 := by
    by_contra hb
    exact h ⟨b, s, hs, by omega⟩
  obtain ⟨j, hj, _⟩ := PEqualNP.Outside.L_meta_170 n C hmin hdep
    (hnonconstant true) (tight true)
  have hand := (PEqualNP.Outside.L_meta_171 n C hmin hdep
    (hnonconstant true) (tight true) j hj).1
  have hor := (PEqualNP.Outside.L_meta_169 n C hmin hdep
    (hnonconstant false) (tight false) j hj).1
  cases hand.symm.trans hor

/-- Count distinct effective gate readers. Repeated pins count once. -/
def readerCount (C : Circuit) (n h : ℕ) : ℕ :=
  C.gates.zipIdx.countP (fun p =>
      decide (h < n + p.2) &&
        (match p.1.op with
          | .not => p.1.inputs.take 1
          | _ => p.1.inputs).contains h)

/-- Brilliant's absorption rewrite with the effective reader count exposed. -/
theorem absorption_replacement {n : ℕ} {C : Circuit}
    (hfan : FanInTwo C) (h : ℕ)
    (haccept : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      circuitFun n C x = true) :
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + readerCount C n h ≤ C.size + 1 := by
  obtain ⟨D, hD, hfun, hsize⟩ := PEqualNP.Outside.L_meta_193 n C h hfan haccept
  have effectiveInputs (g : Gate) :
      GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1)
        (fun _ => g.inputs) g.inputs =
        (match g.op with
          | .not => g.inputs.take 1
          | _ => g.inputs) := by
    cases g.op <;> rfl
  simp only [effectiveInputs] at hsize
  exact ⟨D, hD, hfun, hsize⟩

/-- Wires whose truth forces acceptance can have at most one distinct gate reader
in a minimum circuit. -/
theorem at_most_one_reader_of_forces_acceptance {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C) (h : ℕ)
    (haccept : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      circuitFun n C x = true) : readerCount C n h ≤ 1 := by
  obtain ⟨D, hD, hfun, hsize⟩ := absorption_replacement hmin.1 h haccept
  have hle := hmin.2 D hD hfun
  omega

/-- Absorption can be local even when the wire's truth fails to certify the full output.
The replacement premise requires one exposed output and accounts for every gate in the block. -/
theorem at_most_one_reader_in_replaceable_block {n m : ℕ} {C block : Circuit}
    (hmin : IsMinimalCircuit n C) (hfan : FanInTwo block)
    (replace : ∀ D : Circuit, FanInTwo D → circuitFun m D = circuitFun m block →
      ∃ C' : Circuit, FanInTwo C' ∧ circuitFun n C' = circuitFun n C ∧
        C'.size + block.size ≤ C.size + D.size)
    (h : ℕ)
    (hLocal : ∀ x : Fin m → Bool, (block.wires (List.ofFn x)).getD h false = true →
      circuitFun m block x = true) :
    readerCount block m h ≤ 1 := by
  obtain ⟨D, hD, hfun, hsize⟩ := absorption_replacement hfan h hLocal
  obtain ⟨C', hC', hFull, hBudget⟩ := replace D hD hfun
  have hle := hmin.2 C' hC' hFull
  omega

theorem shared_wire_has_rejecting_true_witness {n : ℕ} {C : Circuit}
    (hmin : IsMinimalCircuit n C) (h : ℕ) (hReaders : 2 ≤ readerCount C n h) :
    ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true ∧
      circuitFun n C x = false := by
  by_contra! h
  have hle := at_most_one_reader_of_forces_acceptance hmin _ fun x hx => by
    exact Bool.eq_true_of_not_eq_false (h x hx)
  omega

/-- A live acceptance condition in a sparse minimum circuit has large input support
and cannot branch to multiple readers. -/
theorem certifying_wire_support_and_fanout {n : ℕ} {C : Circuit} (hmin : IsMinimalCircuit n C)
    (h : ℕ) (S : Finset (Fin n)) (B : ℕ)
    (hcount : ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun x => circuitFun n C x = true)).card ≤ 2 ^ B)
    (x : Fin n → Bool) (hx : (C.wires (List.ofFn x)).getD h false = true)
    (hdepends : ∀ y, (∀ i ∈ S, y i = x i) →
      (C.wires (List.ofFn y)).getD h false = (C.wires (List.ofFn x)).getD h false)
    (haccept : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD h false = true →
      circuitFun n C y = true) :
    n ≤ S.card + B ∧ readerCount C n h ≤ 1 := by
  classical
  let free := (Finset.univ : Finset (Fin n)) \ S
  let accepted := (Finset.univ : Finset (Fin n → Bool)).filter (fun y => circuitFun n C y = true)
  let fill (z : free → Bool) (i : Fin n) := if hi : i ∈ free then z ⟨i, hi⟩ else x i
  let embed (z : free → Bool) : accepted :=
    ⟨fill z, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      haccept _ ((hdepends _ fun i hi => by simp [fill, free, hi]).trans hx)⟩⟩
  have hinj : Function.Injective embed := by
    intro a b heq
    funext i
    simpa [embed, fill, i.property] using congrFun (congrArg Subtype.val heq) i.val
  have hsubcube : 2 ^ free.card ≤ accepted.card := by
    simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using
      Fintype.card_le_of_injective embed hinj
  have hfree := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (hsubcube.trans hcount)
  have hsize := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hsize
  change free.card + S.card = n at hsize
  exact ⟨by omega, at_most_one_reader_of_forces_acceptance hmin h haccept⟩

#print axioms exists_two_gate_saving
#print axioms at_most_one_reader_of_forces_acceptance
#print axioms at_most_one_reader_in_replaceable_block
#print axioms shared_wire_has_rejecting_true_witness
#print axioms certifying_wire_support_and_fanout

end PvsNP.PEqualNPAudit
