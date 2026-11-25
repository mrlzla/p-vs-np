module

public import MCSPConstantBlockExits
public import MCSPMinimumAliases

/-! Count eligible prefixes via the actual raw-pair gates in a minimum
circuit. The count separates within-block wiring from corner coverage. -/

@[expose] public section

namespace PvsNP.Frontier.RawPairPool

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest ForestBlockPinning ForestPinning
open RestrictionCharges FreshCharges NestedFaces QuadraticForest DownstreamBlockPinning
open IndependentBlockPinning MultiBlockPinning SecondBlockExits ConstantBlockExits
open MinimumAliases
open scoped Classical BigOperators

section GateCounts

variable {a d g : ℕ}

/-- The original gates whose two raw arguments are in a specified block. -/
noncomputable def pairGates (p : Program signature (2^(a+d)) g) (s : BitString a) : Finset (Fin g) :=
  Finset.univ.filter fun j => ∃ (i r : Fin (signature.Arity (p.lines j).op)), i ≠ r ∧
    ∃ u ∈ block (d := d) s, ∃ v ∈ block (d := d) s,
      (p.lines j).wires i = .input u ∧ (p.lines j).wires r = .input v

theorem pairGates_nonempty_iff (p : Program signature (2^(a+d)) g) (s : BitString a) :
    (pairGates p s).Nonempty ↔ HasRawPair p s := by
  simp only [Finset.nonempty_def, pairGates, Finset.mem_filter, Finset.mem_univ, true_and, HasRawPair]

private theorem op_on_two_values (op : Op) (i j : Fin (signature.Arity op)) (hne : i ≠ j) :
    ∃ b : Bool, ∀ f : Fin (signature.Arity op) → Bool,
      interpretation op f = if b then (f i && f j) else (f i || f j) := by
  cases op with
  | const b => exact Fin.elim0 i
  | not => exact (hne ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  | and =>
    refine ⟨true, fun f => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [interpretation, Bool.and_comm]
  | or =>
    refine ⟨false, fun f => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [interpretation, Bool.or_comm]

/-- Minimality makes the original gate traces injective. On a block of
size L, the operation and the two raw addresses therefore encode at most
2*L^2 raw-pair gates. -/
theorem card_pairGates_le_of_minimum {f : BooleanFunction (2^(a+d))}
    (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f)) (s : BitString a) :
    (pairGates c.program s).card ≤ 2*(2^d)^2 := by
  let p := c.program
  let G := pairGates p s
  let P := block (d := d) s
  have encode (j : G) : ∃ b : Bool, ∃ u v : P,
      restrictedWire p Sum.inl (.gate j.val) =
        fun x => if b then (x u.val && x v.val) else (x u.val || x v.val) := by
    obtain ⟨i, r, hn, u, hu, v, hv, hi, hr⟩ := (Finset.mem_filter.mp j.property).2
    obtain ⟨b, hb⟩ := op_on_two_values (p.lines j.val).op i r hn
    refine ⟨b, ⟨u, hu⟩, ⟨v, hv⟩, funext fun x => ?_⟩
    unfold restrictedWire
    rw [p.trace_gate, hb, hi, hr]
    rfl
  choose bit left right he using encode
  let code (j : G) : Bool × P × P := (bit j, left j, right j)
  have hInj : Function.Injective code := by
    intro u v hh
    have h₀ : bit u = bit v := congrArg Prod.fst hh
    have h₁ : left u = left v := congrArg (fun q => q.2.1) hh
    have h₂ : right u = right v := congrArg (fun q => q.2.2) hh
    apply Subtype.ext
    apply minimum_original_gate_injective c hc hMin
    change restrictedWire p Sum.inl (.gate u.val) = restrictedWire p Sum.inl (.gate v.val)
    rw [he u, he v, h₀, h₁, h₂]
  have hCard := Fintype.card_le_of_injective code hInj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool, P, G, p, card_block, pow_two]
    using hCard

/-- Prefixes with a raw pair and all their addresses covered by S. -/
noncomputable def coveredPairPool (p : Program signature (2^(a+d)) g)
    (S : Finset (Fin (2^(a+d)))) : Finset (BitString a) :=
  Finset.univ.filter fun s => HasRawPair p s ∧ block (d := d) s ⊆ S

/-- Count all within-block raw-pair gates, including those in uncovered blocks. -/
noncomputable def sameBlockPairGates (p : Program signature (2^(a+d)) g) : Finset (Fin g) :=
  (Finset.univ : Finset (BitString a)).biUnion (pairGates p)

/-- At most one prefix is spoiled by each missing address. The remaining
prefixes each account for at most 2*L^2 distinct raw-pair gates. -/
theorem sameBlockPairGates_le_of_coverage {f : BooleanFunction (2^(a+d))}
    (c : Circuit signature (2^(a+d)) 1)
    (hc : c.Computes interpretation (single f)) (hMin : c.size = complexity interpretation (single f))
    (S : Finset (Fin (2^(a+d)))) :
    (sameBlockPairGates c.program).card ≤
      ((coveredPairPool c.program S).card + ((Finset.univ : Finset _) \ S).card)*(2*(2^d)^2) := by
  let p := c.program
  let P := coveredPairPool p S
  let bad := ((Finset.univ : Finset _) \ S).image tag
  have hSub : sameBlockPairGates p ⊆ (P ∪ bad).biUnion (pairGates p) := by
    intro j hj
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hj
    refine Finset.mem_biUnion.mpr ⟨s, ?_, hs⟩
    by_cases hCover : block (d := d) s ⊆ S
    · have hPair := (pairGates_nonempty_iff p s).mp ⟨j, hs⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPair, hCover⟩)
    · obtain ⟨i, hi, hm⟩ : ∃ i ∈ block (d := d) s, i ∉ S := by
        by_contra! h
        exact hCover h
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, hm⟩, (Finset.mem_filter.mp hi).2⟩)
  have hcBad : bad.card ≤ ((Finset.univ : Finset _) \ S).card := Finset.card_image_le
  calc
    _ ≤ ((P ∪ bad).biUnion (pairGates p)).card := Finset.card_le_card hSub
    _ ≤ ∑ s ∈ P ∪ bad, (pairGates p s).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ P ∪ bad, 2*(2^d)^2 := Finset.sum_le_sum fun s _ =>
      card_pairGates_le_of_minimum c hc hMin s
    _ = (P ∪ bad).card*(2*(2^d)^2) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _
      ((Finset.card_union_le P bad).trans (Nat.add_le_add_left hcBad P.card))

/-- A numerical threshold on the co-block raw-pair gates suffices for
the existing separated-block and second-exit argument on exact MCSP. -/
theorem exact_mcsp_second_exit_of_gate_count {k l r K H reserve : ℕ}
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l)))))
    (hd : 1 ≤ k+l) (hFew : descriptionBitBound (a+(k+l)) < 2^(a+(k+l)))
    (hHeavy : 18*c.size < K*(H+1))
    (hPairs : (r*(18*K+1)+H+descriptionBitBound (a+(k+l)))*(2*(2^(k+l))^2) ≤
      (sameBlockPairGates (a := a) (d := k+l) c.program).card)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (hReserve : reserve ≤ descriptionBitBound (a+(k+l)))
    (hFactorial : 2^(r*2^(k+l)+reserve) ≤ ((a+(k+l))^2).factorial) :
    280*(2*2^(a+(k+l)) + r*2^(k+l-1) + 2*r) + 2*2^(a+(k+l)) ≤
      280*(c.size+2*(descriptionBitBound (a+(k+l))-reserve)+1) +
        17*(descriptionBitBound (a+(k+l))-reserve) := by
  let m := a+(k+l)
  let S := needInputs c.program (c.outputs 0) false
  let pool := coveredPairPool (a := a) (d := k+l) c.program S
  have hs := card_needInputs_ge_of_sparse c hc (card_accepting_mcspSquare_le m) false
    (mcspSquare_constant_table m (by omega) false)
  have hMiss : ((Finset.univ : Finset _) \ S).card ≤ descriptionBitBound m := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    change ((Finset.univ : Finset _) \ S).card + S.card = 2^m at h
    change 2^m ≤ S.card + descriptionBitBound m at hs
    omega
  have hCount := sameBlockPairGates_le_of_coverage c hc hMin S
  have hCap : 0 < 2*(2^(k+l))^2 := by positivity
  have hRoom : r*(18*K+1)+H ≤ pool.card := by
    have h := (Nat.mul_le_mul_right_iff hCap).mp (hPairs.trans hCount)
    change r*(18*K+1)+H+descriptionBitBound m ≤ pool.card + ((Finset.univ : Finset _) \ S).card at h
    omega
  have hPool : ∀ s ∈ pool, HasRawPair c.program s := fun s hs =>
    (Finset.mem_filter.mp hs).2.1
  have hCovered : blocks (d := k+l) pool ⊆ S := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2.2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
  exact exact_mcsp_many_rawPair_blocks c hc hMin hd hFew pool hPool hCovered hHeavy
    hRoom hRepair hReserve hFactorial

end GateCounts

section SerialControl

variable {n g : ℕ}

def chainLine (b : Bool) (w u : Wire n g) : Line signature n g :=
  ⟨if b then .or else .and, fun i => if i.val = 0 then w else u⟩

private theorem trace_last (p : Program signature n g) (l : Line signature n g) (x : BitString n) :
    (p.gate l).trace interpretation x (.gate (Fin.last g)) =
      interpretation l.op (fun i => p.trace interpretation x (l.wires i)) := by
  change (p.gate l).eval interpretation x (Fin.last g) = _
  rw [Program.eval_gate_last]
  rfl

private theorem trace_chainLine (p : Program signature n g) (b : Bool) (w u : Wire n g)
    (x : BitString n) :
    (p.gate (chainLine b w u)).trace interpretation x (.gate (Fin.last g)) = b ↔
      p.trace interpretation x w = b ∨ p.trace interpretation x u = b := by
  rw [trace_last]
  cases b <;> cases hw : p.trace interpretation x w <;> cases hu : p.trace interpretation x u <;>
    simp [chainLine, interpretation, hw, hu]

def aggregateWire (k : ℕ) (hk : k < n) (b : Bool) : Wire n (2*k) :=
  match k with
  | 0 => .input ⟨0, hk⟩
  | j+1 => if b then .gate (Fin.last (2*j)).castSucc else .gate (Fin.last (2*j+1))

/-- Two interleaved combs share only their first raw pair. Each stage
appends an OR and an AND with the next raw input. -/
def dualComb (n : ℕ) : (k : ℕ) → k < n → Program signature n (2*k)
  | 0, _ => .empty
  | k+1, hk =>
    let h : k < n := by omega
    let i : Fin n := ⟨k+1, hk⟩
    let p := (dualComb n k h).gate (chainLine true (aggregateWire k h true) (.input i))
    p.gate (chainLine false (aggregateWire k h false).castSucc (.input i))

private theorem trace_dualComb (k : ℕ) (hk : k < n) (b : Bool) (x : BitString n) :
    (dualComb n k hk).trace interpretation x (aggregateWire k hk b) = b ↔
      ∃ i : Fin n, i.val ≤ k ∧ x i = b := by
  induction k with
  | zero =>
    change x ⟨0, hk⟩ = b ↔ _
    constructor
    · exact fun h => ⟨⟨0, hk⟩, le_rfl, h⟩
    · rintro ⟨i, hi, he⟩
      have hEq : i = ⟨0, hk⟩ := Fin.ext (Nat.le_zero.mp hi)
      rwa [← hEq]
  | succ k ih =>
    have h : k < n := by omega
    let i : Fin n := ⟨k+1, hk⟩
    have hStep : (dualComb n (k+1) hk).trace interpretation x (aggregateWire (k+1) hk b) = b ↔
        (dualComb n k h).trace interpretation x (aggregateWire k h b) = b ∨ x i = b := by
      cases b
      · simp only [dualComb, aggregateWire, Bool.false_eq_true, ite_false] at ⊢
        have he := trace_chainLine ((dualComb n k h).gate
          (chainLine true (aggregateWire k h true) (.input i))) false
          (aggregateWire k h false).castSucc (.input i) x
        simpa only [Program.trace_gate_castSucc, Program.trace_input, aggregateWire,
          Bool.false_eq_true, ite_false] using he
      · simp only [dualComb, aggregateWire, ite_true]
        rw [show (.gate (Fin.last (2*k)).castSucc : Wire n (2*k+2)) =
            (Wire.gate (Fin.last (2*k)) : Wire n (2*k+1)).castSucc from rfl,
          Program.trace_gate_castSucc]
        exact trace_chainLine (dualComb n k h) true (aggregateWire k h true) (.input i) x
    rw [hStep, ih h]
    constructor
    · rintro (⟨j, hj, he⟩ | hI)
      · exact ⟨j, hj.trans (Nat.le_succ _), he⟩
      · exact ⟨i, le_rfl, hI⟩
    · rintro ⟨j, hj, he⟩
      by_cases hj' : j.val ≤ k
      · exact Or.inl ⟨j, hj', he⟩
      · have hji : j = i := Fin.ext (by dsimp [i]; omega)
        exact Or.inr (hji ▸ he)

def equalCombProgram (k : ℕ) : Program signature (k+2) (2*(k+2)) :=
  let p := dualComb (k+2) (k+1) (by omega)
  let w := aggregateWire (n := k+2) (k+1) (by omega) true
  let v := aggregateWire (n := k+2) (k+1) (by omega) false
  let q := p.gate ⟨.not, fun _ => w⟩
  q.gate (chainLine true (.gate (Fin.last (2*(k+1)))) v.castSucc)

def equalCombCircuit (k : ℕ) : Circuit signature (k+2) 1 :=
  ⟨equalCombProgram k, fun _ => .gate (Fin.last (2*(k+1)+1))⟩

noncomputable def allEqual (x : BitString n) : Bool :=
  decide (∃ b : Bool, ∀ i, x i = b)

theorem equalComb_computes (k : ℕ) :
    (equalCombCircuit k).Computes interpretation (single (allEqual (n := k+2))) := by
  intro x
  funext i
  let p := dualComb (k+2) (k+1) (by omega)
  let w := aggregateWire (n := k+2) (k+1) (by omega) true
  let v := aggregateWire (n := k+2) (k+1) (by omega) false
  let q := p.gate ⟨.not, fun _ => w⟩
  apply Bool.eq_iff_iff.mpr
  change (q.gate (chainLine true (.gate (Fin.last (2*(k+1)))) v.castSucc)).trace interpretation x
    (.gate (Fin.last (2*(k+1)+1))) = true ↔ _
  rw [trace_chainLine, Program.trace_gate_castSucc]
  have hNot : q.trace interpretation x (.gate (Fin.last (2*(k+1)))) =
      !(p.trace interpretation x w) := by
    change (p.gate ⟨.not, fun _ => w⟩).trace interpretation x (.gate (Fin.last (2*(k+1)))) = _
    rw [trace_last]
    rfl
  rw [hNot]
  have h0 := trace_dualComb (k+1) (n := k+2) (by omega) true x
  have h1 := trace_dualComb (k+1) (n := k+2) (by omega) false x
  have hAll (b : Bool) : (∀ i : Fin (k+2), x i = b) ↔ ¬∃ i : Fin (k+2), i.val ≤ k+1 ∧ x i = !b := by
    constructor
    · rintro h ⟨i, _, he⟩
      have := (h i).symm.trans he
      cases b <;> contradiction
    · intro h i
      by_contra he
      have hs : i.val ≤ k+1 := by have := i.isLt; omega
      apply h
      refine ⟨i, hs, ?_⟩
      cases b <;> cases x i <;> simp_all
  have e0 : (!(p.trace interpretation x w)) = true ↔ ∀ i : Fin (k+2), x i = false := by
    have h := hAll false
    simp only [Bool.not_false] at h
    rw [h, ← show p.trace interpretation x w = true ↔ _ from h0]
    cases p.trace interpretation x w <;> decide
  have e1 : p.trace interpretation x v = true ↔ ∀ i : Fin (k+2), x i = true := by
    have h := hAll true
    simp only [Bool.not_true] at h
    rw [h, ← show p.trace interpretation x v = false ↔ _ from h1]
    cases p.trace interpretation x v <;> decide
  rw [e0, e1]
  change (∀ j, x j = false) ∨ (∀ j, x j = true) ↔ allEqual x = true
  rw [allEqual, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, h⟩
    cases b
    · exact Or.inl h
    · exact Or.inr h

def LineUsesOnlyInitialPair (l : Line signature n g) : Prop :=
  ∀ (i r : Fin (signature.Arity l.op)) (u v : Fin n), i ≠ r →
    l.wires i = .input u → l.wires r = .input v →
    (u.val = 0 ∧ v.val = 1) ∨ (v.val = 0 ∧ u.val = 1)

def UsesOnlyInitialPair (p : Program signature n g) : Prop :=
  ∀ j, LineUsesOnlyInitialPair (p.lines j)

private theorem castSucc_input_injective {w : Wire n g} {i : Fin n}
    (h : w.castSucc = .input i) : w = .input i := by
  cases w
  · cases h
    rfl
  · cases h

private theorem widen_line_use {l : Line signature n g} (h : LineUsesOnlyInitialPair l) :
    LineUsesOnlyInitialPair (l.mapWires Wire.Renaming.castSucc) := by
  intro i r u v hn hu hv
  exact h i r u v hn (castSucc_input_injective hu) (castSucc_input_injective hv)

private theorem append_line_use {p : Program signature n g} {l : Line signature n g}
    (hp : UsesOnlyInitialPair p) (hl : LineUsesOnlyInitialPair l) :
    UsesOnlyInitialPair (p.gate l) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Program.lines_gate_last]
    exact widen_line_use hl
  · rw [Program.lines_gate_castSucc]
    exact widen_line_use (hp i)

private theorem chainLine_use (b : Bool) (w z : Wire n g)
    (h : ∀ u v : Fin n, w = .input u → z = .input v → u.val = 0 ∧ v.val = 1) :
    LineUsesOnlyInitialPair (chainLine b w z) := by
  intro i r u v hn hu hv
  have hArity : signature.Arity (chainLine b w z).op = 2 := by cases b <;> rfl
  have hi : i.val < 2 := i.isLt.trans_le hArity.le
  have hr : r.val < 2 := r.isLt.trans_le hArity.le
  have hne : i.val ≠ r.val := fun he => hn (Fin.ext he)
  have hCases : (i.val = 0 ∧ r.val ≠ 0) ∨ (r.val = 0 ∧ i.val ≠ 0) := by omega
  rcases hCases with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl (h u v (by simpa only [chainLine, h0, ite_true] using hu)
      (by simpa only [chainLine, h1, ite_false] using hv))
  · exact Or.inr (h v u (by simpa only [chainLine, h0, ite_true] using hv)
      (by simpa only [chainLine, h1, ite_false] using hu))

private theorem agg_input_spec (k : ℕ) (hk : k < n) (b : Bool) (u : Fin n)
    (h : aggregateWire k hk b = .input u) : k = 0 ∧ u.val = 0 := by
  cases k with
  | zero =>
    change (.input ⟨0, hk⟩ : Wire n 0) = .input u at h
    cases h
    exact ⟨rfl, rfl⟩
  | succ k => cases b <;> simp [aggregateWire] at h

theorem dualComb_only_initial_pair (k : ℕ) (hk : k < n) :
    UsesOnlyInitialPair (dualComb n k hk) := by
  induction k with
  | zero => intro j; exact Fin.elim0 j
  | succ k ih =>
    unfold dualComb
    apply append_line_use (append_line_use (ih (by omega)) ?_) ?_
    · apply chainLine_use
      intro u v hu hv
      obtain ⟨hk0, huv⟩ := agg_input_spec k (by omega) true u hu
      have hv' : v.val = k+1 := congrArg Fin.val (Wire.input.inj hv).symm
      exact ⟨huv, by omega⟩
    · apply chainLine_use
      intro u v hu hv
      obtain ⟨hk0, huv⟩ := agg_input_spec k (by omega) false u (castSucc_input_injective hu)
      have hv' : v.val = k+1 := congrArg Fin.val (Wire.input.inj hv).symm
      exact ⟨huv, by omega⟩

theorem equalComb_only_initial_pair (k : ℕ) : UsesOnlyInitialPair (equalCombProgram k) := by
  unfold equalCombProgram
  apply append_line_use (append_line_use (dualComb_only_initial_pair _ _) ?_) ?_
  · intro i r u v hn
    exact (hn ((Fin.eq_zero i).trans (Fin.eq_zero r).symm)).elim
  · apply chainLine_use
    intro u v h
    cases h

private theorem allEqual_corner (b : Bool) : allEqual (fun _ : Fin n => b) = true :=
  decide_eq_true ⟨b, fun _ => rfl⟩

private theorem allEqual_pivot (hn : 2 ≤ n) (b : Bool) (i : Fin n) :
    allEqual (Function.update (fun _ => b) i (!b)) = false := by
  apply decide_eq_false
  rintro ⟨v, hv⟩
  let j : Fin n := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hj : j ≠ i := by
    intro he
    have hval := congrArg (fun z : Fin n => z.val) he
    by_cases hi : i.val = 0
    · simp [j, hi] at hval
    · simp only [j, hi, ite_false] at hval
      exact hi hval.symm
  have h1 := hv i
  have h2 := hv j
  rw [Function.update_self] at h1
  rw [Function.update_of_ne hj] at h2
  cases b <;> simp_all

theorem equalComb_minimum (k : ℕ) :
    (equalCombCircuit k).size = complexity interpretation (single (allEqual (n := k+2))) := by
  apply le_antisymm _ (complexity_le_of_computes _ (equalComb_computes k))
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (allEqual (n := k+2)))
  rw [← hSize]
  exact QuarterDeadFrontier.opposite_corners_all_pivotal_lower c hc allEqual_corner
    (allEqual_pivot (by omega))

theorem equalComb_accepting_card (k : ℕ) :
    (acceptingTables (allEqual (n := k+2))).card = 2 := by
  have he : acceptingTables (allEqual (n := k+2)) =
      (Finset.univ : Finset Bool).image (fun b (_ : Fin (k+2)) => b) := by
    ext x
    simp only [acceptingTables, allEqual, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
      true_and, decide_eq_true_eq]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, (funext hb).symm⟩, fun ⟨b, he⟩ => ⟨b, fun i => (congrFun he i).symm⟩⟩
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => congrFun h 0),
    Finset.card_univ, Fintype.card_bool]

/-- Both corner certificates of every implementation of the all-equal
function include all raw input addresses. -/
theorem allEqual_needInputs {n : ℕ} (hn : 2 ≤ n) (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single allEqual)) (b : Bool) :
    needInputs c.program (c.outputs 0) b = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  have hRoot : cornerValue c.program b (c.outputs 0) = true := (congrFun (hc _) 0).trans (allEqual_corner b)
  have hAgree : ∀ j ∈ needInputs c.program (c.outputs 0) b, Function.update (fun _ => b) i (!b) j = b := by
    intro j hj
    have hne : j ≠ i := fun he => hi (he ▸ hj)
    exact Function.update_of_ne hne _ _
  have h := agrees_on_needCorner c.program (c.outputs 0) b hRoot
    (Function.update (fun _ => b) i (!b)) hAgree
  have hEq := congrFun (hc (Function.update (fun _ => b) i (!b))) 0
  exact Bool.noConfusion ((allEqual_pivot hn b i).symm.trans (hEq.symm.trans h))

theorem exists_initialPair_minimum_control (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : Circuit signature n 1,
      c.Computes interpretation (single allEqual) ∧
      c.size = complexity interpretation (single (allEqual (n := n))) ∧
      (acceptingTables (allEqual (n := n))).card = 2 ∧ UsesOnlyInitialPair c.program := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, (Nat.sub_add_cancel hn).symm⟩
  exact ⟨equalCombCircuit k, equalComb_computes k, equalComb_minimum k, equalComb_accepting_card k,
    equalComb_only_initial_pair k⟩

/-- Growing minimum controls with both corners covered, and at most one
raw-pair prefix even if the partition is chosen after seeing the circuit. -/
theorem sparse_minimum_control_pool_le_one (a d : ℕ) (hm : 1 ≤ a+d) :
    ∃ c : Circuit signature (2^(a+d)) 1,
      c.Computes interpretation (single allEqual) ∧
      c.size = complexity interpretation (single (allEqual (n := 2^(a+d)))) ∧
      (acceptingTables (allEqual (n := 2^(a+d)))).card = 2 ∧
      (∀ b, needInputs c.program (c.outputs 0) b = Finset.univ) ∧
      (coveredPairPool (a := a) (d := d) c.program (needInputs c.program (c.outputs 0) false)).card ≤ 1 := by
  have hn : 2 ≤ 2^(a+d) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm
  obtain ⟨c, hc, hMin, hSparse, hPair⟩ := exists_initialPair_minimum_control (2^(a+d)) hn
  refine ⟨c, hc, hMin, hSparse, allEqual_needInputs hn c hc, ?_⟩
  let i₀ : Fin (2^(a+d)) := ⟨0, Nat.two_pow_pos _⟩
  have hSub : coveredPairPool c.program (needInputs c.program (c.outputs 0) false) ⊆ {tag i₀} := by
    intro s hs
    obtain ⟨j, i, r, hn, u, hu, v, hv, hi, hr⟩ := (Finset.mem_filter.mp hs).2.1
    apply Finset.mem_singleton.mpr
    rcases hPair j i r u v hn hi hr with ⟨he, _⟩ | ⟨he, _⟩
    · have hEq : u = i₀ := Fin.ext he
      exact ((Finset.mem_filter.mp hu).2).symm.trans (congrArg tag hEq)
    · have hEq : v = i₀ := Fin.ext he
      exact ((Finset.mem_filter.mp hv).2).symm.trans (congrArg tag hEq)
  exact (Finset.card_le_card hSub).trans (by simp)

private theorem first_bit_mod_two {m : ℕ} (hm : 0 < m) (x : BitString m) :
    (BitString.equivFin m x).val % 2 = (x ⟨0,hm⟩).toNat := by
  cases m with
  | zero => omega
  | succ m =>
    have h := BitString.val_equivFin_cons (x 0) (Fin.tail x)
    rw [Fin.cons_self_tail] at h
    rw [h, show (⟨0,hm⟩ : Fin (m+1)) = 0 from rfl]
    cases x 0 <;> simp

private theorem zero_one_tags_different {a d : ℕ} (ha : 1 ≤ a)
    (u v : Fin (2^(a+d))) (hu : u.val = 0) (hv : v.val = 1) :
    tag (a := a) (d := d) u ≠ tag (a := a) (d := d) v := by
  intro h
  have hm : 0 < a+d := by omega
  let x := (BitString.equivFin (a+d)).symm u
  let y := (BitString.equivFin (a+d)).symm v
  have hFirst : x ⟨0,hm⟩ = y ⟨0,hm⟩ := congrFun h ⟨0,ha⟩
  have hx := first_bit_mod_two hm x
  have hy := first_bit_mod_two hm y
  rw [hFirst] at hx
  dsimp only [x, y] at hx hy
  rw [Equiv.apply_symm_apply, hu] at hx
  rw [Equiv.apply_symm_apply, hv] at hy
  omega

/-- With a nonempty address prefix, the two raw addresses used by the
minimum control have different tags. Its covered raw-pair pool is empty. -/
theorem sparse_minimum_control_pool_empty (a d : ℕ) (ha : 1 ≤ a) :
    ∃ c : Circuit signature (2^(a+d)) 1,
      c.Computes interpretation (single allEqual) ∧
      c.size = complexity interpretation (single (allEqual (n := 2^(a+d)))) ∧
      (acceptingTables (allEqual (n := 2^(a+d)))).card = 2 ∧
      (∀ b, needInputs c.program (c.outputs 0) b = Finset.univ) ∧
      coveredPairPool (a := a) (d := d) c.program (needInputs c.program (c.outputs 0) false) = ∅ := by
  have hn : 2 ≤ 2^(a+d) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 1 ≤ a+d)
  obtain ⟨c, hc, hMin, hSparse, hPair⟩ := exists_initialPair_minimum_control _ hn
  refine ⟨c, hc, hMin, hSparse, allEqual_needInputs hn c hc, ?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨j, i, r, hn, u, hu, v, hv, hi, hr⟩ := (Finset.mem_filter.mp hs).2.1
  have hTag : tag (a := a) (d := d) u = tag (a := a) (d := d) v :=
    ((Finset.mem_filter.mp hu).2).trans ((Finset.mem_filter.mp hv).2).symm
  rcases hPair j i r u v hn hi hr with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact zero_one_tags_different ha u v h0 h1 hTag
  · exact zero_one_tags_different ha v u h0 h1 hTag.symm

/-- A projection accepted by exact MCSP separates it from the control. -/
theorem projection_separates_allEqual (m : ℕ) (i : Fin m) :
    let T := MCSP.truthTable m (fun x => x i)
    mcspSquare m T = true ∧ allEqual T = false := by
  constructor
  · rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply, complexity_single_proj]
    exact Nat.zero_le _
  · apply decide_eq_false
    rintro ⟨b, hb⟩
    have h0 := hb (BitString.equivFin m (fun _ => false))
    have h1 := hb (BitString.equivFin m (fun _ => true))
    simp only [MCSP.truthTable_apply, Equiv.symm_apply_apply] at h0 h1
    cases h0.trans h1.symm

end SerialControl

#print axioms card_pairGates_le_of_minimum
#print axioms sameBlockPairGates_le_of_coverage
#print axioms exact_mcsp_second_exit_of_gate_count
#print axioms sparse_minimum_control_pool_le_one
#print axioms sparse_minimum_control_pool_empty
#print axioms projection_separates_allEqual

end PvsNP.Frontier.RawPairPool
