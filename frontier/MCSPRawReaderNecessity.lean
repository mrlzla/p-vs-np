module

public import MCSPProbePairBarrier

/-! Exact duality and minimum size impose a cost on replacing raw readers
by unary gates. This counts binary access to individual raw addresses. -/

@[expose] public section

namespace PvsNP.Frontier.RawReaderNecessity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates SuperTwoN
open scoped Classical BigOperators

variable {n g : ℕ}

def RawNot (l : Line signature n g) : Prop :=
  l.op = .not ∧ ∃ (a : Fin (signature.Arity l.op)) (i : Fin n), l.wires a = .input i

noncomputable def rawNotCount : {g : ℕ} → Program signature n g → ℕ
  | _, .empty => 0
  | _, .gate p l => rawNotCount p + if RawNot l then 1 else 0

noncomputable def binaryReadInputs (p : Program signature n g) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ j : Fin g, 2 ≤ signature.Arity (p.lines j).op ∧
    ∃ a, (p.lines j).wires a = .input i

noncomputable def negInputs (p : Program signature n g) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ j : Fin g, (p.lines j).op = .not ∧ ∃ a, (p.lines j).wires a = .input i

private theorem castSucc_raw_iff {w : Wire n g} {i : Fin n} :
    w.castSucc = .input i ↔ w = .input i := by
  cases w <;> simp [Wire.castSucc]

private theorem rawNot_widen (l : Line signature n g) :
    RawNot (l.mapWires Wire.Renaming.castSucc) ↔ RawNot l := by
  unfold RawNot
  simp only [Line.mapWires_op, Line.mapWires_wires,
    Wire.Renaming.castSucc_apply, castSucc_raw_iff]

private theorem rawNotCount_le (p : Program signature n g) : rawNotCount p ≤ g := by
  induction p with
  | empty => rfl
  | gate p l ih =>
    by_cases h : RawNot l <;> simp [rawNotCount, h] <;> omega

private theorem rawNotCount_eq_card (p : Program signature n g) :
    rawNotCount p = (Finset.univ.filter fun j : Fin g => RawNot (p.lines j)).card := by
  have he : (Finset.univ.filter fun j : Fin g => RawNot (p.lines j)).card =
      ∑ j : Fin g, if RawNot (p.lines j) then 1 else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_one]
  rw [he]
  clear he
  induction p with
  | empty => simp [rawNotCount]
  | gate p l ih =>
    simp only [rawNotCount, Fin.sum_univ_castSucc, Program.lines_gate_castSucc,
      Program.lines_gate_last, rawNot_widen, ih]

private theorem negInputs_card_le (p : Program signature n g) : (negInputs p).card ≤ rawNotCount p := by
  let R := Finset.univ.filter fun j : Fin g => RawNot (p.lines j)
  have hw (i : negInputs p) :
      ∃ j : R, ∃ a, (p.lines j.val).wires a = .input i.val := by
    obtain ⟨j, hop, a, h⟩ := (Finset.mem_filter.mp i.property).2
    exact ⟨⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hop, a, i, h⟩⟩, a, h⟩
  choose select arg hEq using hw
  have hInj : Function.Injective select := by
    intro i k he
    apply Subtype.ext
    have hOther : ∃ a, (p.lines (select k).val).wires a = .input k.val := ⟨arg k,hEq k⟩
    rw [← he] at hOther
    obtain ⟨other,hew⟩ := hOther
    have hop := (Finset.mem_filter.mp (select i).property).2.1
    have hPort (a b : Fin (signature.Arity (p.lines (select i).val).op)) : a = b := by
      have hArity : signature.Arity (p.lines (select i).val).op = 1 := by rw [hop]
      have ha := a.isLt.trans_le hArity.le
      have hb := b.isLt.trans_le hArity.le
      exact Fin.ext (by omega)
    have h := hEq i
    rw [hPort (arg i) other] at h
    exact Wire.input.inj (h.symm.trans hew)
  have h := Fintype.card_le_of_injective select hInj
  rw [Fintype.card_coe, Fintype.card_coe, ← rawNotCount_eq_card] at h
  exact h

private def negated (x : BitString n) : BitString n := fun i => !(x i)

private theorem trace_last_eq (p : Program signature n g) (l : Line signature n g) (x : BitString n) :
    (p.gate l).trace interpretation x (.gate (Fin.last g)) =
      interpretation l.op (fun a => p.trace interpretation x (l.wires a)) := by
  change (p.gate l).eval interpretation x (Fin.last g) = _
  rw [Program.eval_gate_last]
  rfl

private theorem eval_rawNot (op : Op) (h : op = .not)
    (f : Fin (signature.Arity op) → Bool) (a : Fin (signature.Arity op)) :
    interpretation op f = !(f a) := by
  subst op
  rw [Fin.eq_zero a]
  rfl

/-- Compute on complemented raw inputs. A direct NOT becomes a free
projection. Only raw inputs to binary gates need supplied negations. -/
private theorem synth_negated_traces (p : Program signature n g) (S : Set (BooleanFunction n))
    (hProj : inputs n ⊆ S)
    (hBinary : ∀ i ∈ binaryReadInputs p, (fun x : BitString n => !(x i)) ∈ S) :
    Synthesis interpretation S
      (Set.range fun j : Fin g => fun x => p.trace interpretation (negated x) (.gate j))
      (g-rawNotCount p) := by
  induction p with
  | empty =>
    apply Synthesis.of_subset
    rintro _ ⟨j,_⟩
    exact Fin.elim0 j
  | @gate g p l ih =>
    let bank := Set.range fun j : Fin g => fun x : BitString n => p.trace interpretation (negated x) (.gate j)
    have hOld := ih (fun i hi => by
      obtain ⟨j, hop, a, ha⟩ := (Finset.mem_filter.mp hi).2
      apply hBinary
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, j.castSucc, ?_⟩
      rw [Program.lines_gate_castSucc]
      exact ⟨hop,a,by simp only [Line.mapWires_wires, Wire.Renaming.castSucc_apply, ha]; rfl⟩)
    let last (x : BitString n) := (p.gate l).trace interpretation (negated x) (.gate (Fin.last g))
    have hLast : Synthesis interpretation (S ∪ bank) {last} (if RawNot l then 0 else 1) := by
      by_cases h : RawNot l
      · obtain ⟨hop, a, i, ha⟩ := h
        have he : last = fun x => x i := by
          funext x
          dsimp only [last]
          rw [trace_last_eq, eval_rawNot l.op hop _ a, ha, Program.trace_input]
          simp [negated]
        rw [he, ite_eq_left ⟨hop,a,i,ha⟩]
        exact Synthesis.of_mem (Or.inl (hProj ⟨i,rfl⟩))
      · rw [ite_eq_right h]
        let args (a : Fin (signature.Arity l.op)) (x : BitString n) :=
          p.trace interpretation (negated x) (l.wires a)
        have hAvail (a : Fin (signature.Arity l.op)) : args a ∈ S ∪ bank := by
          cases he : l.wires a with
          | gate j => exact Or.inr ⟨j, funext fun x => by simp only [args, he]⟩
          | input i =>
            have hop : 2 ≤ signature.Arity l.op := by
              cases e : l.op with
              | const b =>
                have hz : signature.Arity l.op = 0 := by rw [e]
                exact (Nat.not_lt_zero _ (a.isLt.trans_le hz.le)).elim
              | not => exact (h ⟨e,a,i,he⟩).elim
              | and => exact Nat.le_refl 2
              | or => exact Nat.le_refl 2
            have hi : i ∈ binaryReadInputs (p.gate l) := by
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, Fin.last g, ?_⟩
              rw [Program.lines_gate_last]
              exact ⟨hop,a,by simp only [Line.mapWires_wires, Wire.Renaming.castSucc_apply, he]; rfl⟩
            have hd : args a = fun x => !(x i) := by funext x; simp [args, he, negated]
            exact Or.inl (hd.symm ▸ hBinary i hi)
        have he : (fun x => interpretation l.op (fun a => args a x)) = last :=
          funext fun x => (trace_last_eq p l (negated x)).symm
        rw [← he]
        exact Synthesis.gate _ args hAvail
    apply (hOld.comp hLast).mono Set.Subset.rfl ?_ ?_
    · rintro _ ⟨j,rfl⟩
      refine Fin.lastCases ?_ (fun k => ?_) j
      · exact Or.inr rfl
      · exact Or.inl ⟨k, funext fun x => (Program.trace_gate_castSucc p l _ _ (.gate k)).symm⟩
    · have hLe := rawNotCount_le p
      by_cases h : RawNot l
      · simp only [rawNotCount, h, ite_true, Nat.add_zero]
        omega
      · simp only [rawNotCount, h, ite_false, Nat.add_zero]
        omega

private theorem negated_mcsp_complexity (m : ℕ) :
    complexity interpretation (single (fun x => mcspSquare m (negated x))) =
      complexity interpretation (single (mcspSquare m)) := by
  let e : Equiv.Perm (Fin (2^m)) :=
    ⟨PairFunnelGap.compIdx m, PairFunnelGap.compIdx m,
      PairFunnelGap.compIdx_involutive m, PairFunnelGap.compIdx_involutive m⟩
  have h := PermutedCut.complexity_comp_perm e (fun x => mcspSquare m (negated x))
  have he : (fun x => mcspSquare m (negated (x ∘ e))) = mcspSquare m :=
    funext (PairFunnelGap.mcspSquare_dualTable m)
  rw [he] at h
  exact h.symm

private theorem exact_mcsp_output_gate (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2^m) 1) (hc : c.Computes interpretation (single (mcspSquare m))) :
    ∃ j, c.outputs 0 = .gate j := by
  cases he : c.outputs 0 with
  | input i =>
    have h := congrFun (hc (fun _ => false)) 0
    change c.program.trace interpretation (fun _ => false) (c.outputs 0) = mcspSquare m (fun _ => false) at h
    rw [he, Program.trace_input, mcspSquare_constant_table m hm false] at h
    cases h
  | gate j => exact ⟨j, rfl⟩

/-- A minimum exact MCSP circuit cannot use more raw NOT gates than
distinct raw addresses read by binary gates. -/
theorem exact_mcsp_rawNot_le_binary (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2^m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (hMin : c.size = complexity interpretation (single (mcspSquare m))) :
    rawNotCount c.program ≤ (binaryReadInputs c.program).card := by
  let n := 2^m
  let p := c.program
  let R := binaryReadInputs p
  let ns (i : R) : BooleanFunction n := fun x => !(x i.val)
  let bank := Set.range ns
  let S := inputs n ∪ bank
  have hOne (i : R) : Synthesis interpretation (inputs n) {ns i} 1 :=
    (Synthesis.of_mem (show (fun x : BitString n => x i.val) ∈ inputs n from ⟨i.val,rfl⟩)).not
  have hBank : Synthesis interpretation (inputs n) bank R.card := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe, Nat.mul_one]
      using Synthesis.family ns (fun _ => 1) hOne
  have hBinary (i : Fin n) (hi : i ∈ R) : (fun x : BitString n => !(x i)) ∈ S :=
    Or.inr ⟨⟨i,hi⟩,rfl⟩
  have hSyn := synth_negated_traces p S Set.subset_union_left hBinary
  obtain ⟨j,hj⟩ := exact_mcsp_output_gate m hm c hc
  have hOut : Synthesis interpretation S {fun x => mcspSquare m (negated x)} (c.size-rawNotCount p) := by
    apply hSyn.mono Set.Subset.rfl ?_ le_rfl
    rintro _ rfl
    refine ⟨j,funext fun x => ?_⟩
    have h := congrFun (hc (negated x)) 0
    change p.trace interpretation (negated x) (c.outputs 0) = _ at h
    rwa [hj] at h
  have h := (hBank.trans hOut).complexity_le
  rw [negated_mcsp_complexity, ← hMin] at h
  change c.size ≤ (binaryReadInputs c.program).card+(c.size-rawNotCount c.program) at h
  have hR := rawNotCount_le c.program
  omega

private theorem live_raw_has_source {p : Program signature n g} {root w : Wire n g}
    (h : WireAccounting.Live p root w) (i : Fin n) (hi : w = .input i) :
    root = .input i ∨ ∃ j a, (p.lines j).wires a = .input i := by
  cases h with
  | output => exact Or.inl hi
  | @argument j _ a => exact Or.inr ⟨j,a,hi⟩

private theorem live_raw_subset_binary_or_not (m : ℕ) (hm : 1 ≤ m) (c : Circuit signature (2^m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m))) :
    WireAccounting.inputs c.program (c.outputs 0) ⊆ binaryReadInputs c.program ∪ negInputs c.program := by
  obtain ⟨j,hj⟩ := exact_mcsp_output_gate m hm c hc
  intro i hi
  rcases live_raw_has_source (Finset.mem_filter.mp hi).2 i rfl with hroot | ⟨k,a,ha⟩
  · rw [hj] at hroot
    cases hroot
  · cases hop : (c.program.lines k).op with
    | const b =>
      have hz : signature.Arity (c.program.lines k).op = 0 := by rw [hop]
      exact (Nat.not_lt_zero _ (a.isLt.trans_le hz.le)).elim
    | not =>
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k,hop,a,ha⟩)
    | and =>
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, k, by rw [hop], a,ha⟩)
    | or =>
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, k, by rw [hop], a,ha⟩)

/-- In minimum exact MCSP circuits, at least (N-B)/2 distinct raw inputs
are read by binary gates. This bounds individual raw access. -/
theorem exact_mcsp_many_binary_read_inputs {m B : ℕ} (hm : 1 ≤ m)
    (c : Circuit signature (2^m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (hMin : c.size = complexity interpretation (single (mcspSquare m)))
    (hSparse : (acceptingTables (mcspSquare m)).card ≤ 2^B) :
    2^m ≤ 2*(binaryReadInputs c.program).card+B := by
  let f := mcspSquare m
  let z : BitString (2^m) := fun _ => false
  let E := essentialPositions f Finset.univ
  have h0 : f z = true := mcspSquare_constant_table m hm false
  have hPow := (pow_card_inessential_le f z Finset.univ h0).trans hSparse
  have hId (T : BitString (2^m)) : restrictTable z Finset.univ T = T := by
    funext i
    simp [restrictTable]
  simp only [hId] at hPow
  change 2^((Finset.univ : Finset _) \ E).card ≤ 2^B at hPow
  have hMiss := (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hPow
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
  rw [Finset.card_univ, Fintype.card_fin] at hPart
  have hEss : E ⊆ WireAccounting.inputs c.program (c.outputs 0) := by
    intro i hi
    exact WireAccounting.essential_mem_inputs hc (Finset.mem_filter.mp hi).2
  have hRead := (Finset.card_le_card (hEss.trans (live_raw_subset_binary_or_not m hm c hc))).trans
    (Finset.card_union_le _ _)
  have hNeg := negInputs_card_le c.program
  have hMinNeg := exact_mcsp_rawNot_le_binary m hm c hc hMin
  omega

theorem exact_mcsp_32_binary_read_inputs
    (c : Circuit signature (2^32) 1) (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32))) :
    2147473914 ≤ (binaryReadInputs c.program).card := by
  have hSparse : (acceptingTables (mcspSquare 32)).card ≤ 2^19468 := by
    have h := DownstreamBlockPinning.padded_sparsity_of_factorial (m := 32) (b := 8204) (fun _ => false) ∅
      (by decide) (by rw [Finset.card_empty, Nat.zero_add]; exact ConstantBlockExits.factorial_room_32_dyadic)
    have he : (fun y => mcspSquare 32 (substitute (ForestPinning.pinAt (fun _ => false) ∅) y)) = mcspSquare 32 := by
      funext y
      congr 1
    rwa [he, show descriptionBitBound 32 - 8204 = 19468 by decide] at h
  have h := exact_mcsp_many_binary_read_inputs (by decide : 1 ≤ 32) c hc hMin hSparse
  norm_num at h
  omega

#print axioms exact_mcsp_rawNot_le_binary
#print axioms exact_mcsp_many_binary_read_inputs
#print axioms exact_mcsp_32_binary_read_inputs

end PvsNP.Frontier.RawReaderNecessity
