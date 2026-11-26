module

public import MCSPResidualTraceRank

/-! Remove both raw traces and the span of already counted gate traces.
A rank contribution after both quotients can be added to the paid indices. -/

@[expose] public section

namespace PvsNP.Frontier.ForestTraceQuotient

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open BatchRank ResidualTraceRank RestrictionCharges ForestPinning DownstreamBlockPinning
open scoped Classical BigOperators

section Quotient

variable {n k g : ℕ}

/-- The ambient trace space after removing the raw inputs. -/
abbrev RawQuotient (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) :=
  ((Fin k → F₂) → F₂) ⧸ rawSpan (substitute pin a) (fun z => substitute pin (perturb a z))

noncomputable def paidSpan (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) : Submodule F₂ (RawQuotient pin a) :=
  Submodule.span F₂ (Set.range (fun j : paid => pinQuotientTrace p pin a j.val))

noncomputable def paidRank (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) : ℕ :=
  Module.finrank F₂ (paidSpan p pin a paid)

noncomputable def remainingRank (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) : ℕ :=
  Module.finrank F₂ ((traceSpan p (substitute pin a) (fun z => substitute pin (perturb a z))).map
    (paidSpan p pin a paid).mkQ)

theorem paidSpan_le (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) :
    paidSpan p pin a paid ≤ traceSpan p (substitute pin a) (fun z => substitute pin (perturb a z)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.subset_span ⟨Wire.gate j.val,rfl⟩

theorem pinRank_split (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) :
    pinRank p pin a = paidRank p pin a paid+remainingRank p pin a paid := by
  let S := traceSpan p (substitute pin a) (fun z => substitute pin (perturb a z))
  let D := paidSpan p pin a paid
  let f := D.mkQ.comp S.subtype
  have h := f.finrank_range_add_finrank_ker
  have hRange : LinearMap.range f = S.map D.mkQ := by
    ext z
    constructor
    · rintro ⟨⟨v,hv⟩,rfl⟩
      exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
    · intro hz
      obtain ⟨v,hv,hz⟩ := Submodule.mem_map.mp hz
      exact ⟨⟨v,hv⟩,hz⟩
  have hKer : LinearMap.ker f = D.comap S.subtype := by
    change LinearMap.ker (D.mkQ.comp S.subtype) = _
    rw [LinearMap.ker_comp,Submodule.ker_mkQ]
  rw [hRange,hKer,(Submodule.comapSubtypeEquivOfLe (paidSpan_le p pin a paid)).finrank_eq] at h
  exact h.symm.trans (Nat.add_comm _ _)

private theorem outside_generates (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) :
    let D := paidSpan p pin a paid
    let outside := (binaryGates p \ constantReaders p pin) \ paid
    (traceSpan p (substitute pin a) (fun z => substitute pin (perturb a z))).map D.mkQ =
      Submodule.span F₂ (Set.range (fun j : outside => D.mkQ (pinQuotientTrace p pin a j.val))) := by
  let D := paidSpan p pin a paid
  let S := binaryGates p \ constantReaders p pin
  let outside := S \ paid
  let V := Submodule.span F₂ (Set.range (fun j : outside => D.mkQ (pinQuotientTrace p pin a j.val)))
  change (traceSpan p (substitute pin a) (fun z => substitute pin (perturb a z))).map D.mkQ = V
  rw [pin_traceSpan_eq_active,Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨j,rfl⟩,rfl⟩
    by_cases hj : j.val ∈ paid
    · have hk : pinQuotientTrace p pin a j.val ∈ LinearMap.ker D.mkQ := by
        rw [Submodule.ker_mkQ]
        exact Submodule.subset_span ⟨⟨j.val,hj⟩,rfl⟩
      rw [LinearMap.mem_ker.mp hk]
      exact V.zero_mem
    · exact Submodule.subset_span ⟨⟨j.val,Finset.mem_sdiff.mpr ⟨j.property,hj⟩⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span ⟨_,⟨⟨j.val,(Finset.mem_sdiff.mp j.property).1⟩,rfl⟩,rfl⟩

/-- The remaining rank can be added to the count of named paid gates and the
constant-reader losses, taking their union so that overlaps cost only once. -/
theorem remainingRank_with_paid_and_losses (p : Program signature n g)
    (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) (paid : Finset (Fin g)) :
    remainingRank p pin a paid + (paid ∪ constantReaders p pin).card ≤ g := by
  let D := paidSpan p pin a paid
  let outside := (binaryGates p \ constantReaders p pin) \ paid
  have hRank : remainingRank p pin a paid ≤ outside.card := by
    unfold remainingRank
    rw [outside_generates]
    exact (finrank_range_le_card (fun j : outside => D.mkQ (pinQuotientTrace p pin a j.val))).trans_eq
      (Fintype.card_coe _)
  let used := paid ∪ constantReaders p pin
  have hSub : outside ⊆ Finset.univ \ used := by
    intro j hj
    obtain ⟨hjS,hP⟩ := Finset.mem_sdiff.mp hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h =>
      (Finset.mem_union.mp h).elim hP (Finset.mem_sdiff.mp hjS).2⟩
  have hCount := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ used)
  rw [Finset.card_univ,Fintype.card_fin] at hCount
  exact (Nat.add_le_add_right (hRank.trans (Finset.card_le_card hSub)) used.card).trans_eq hCount

open CornerCertificates in
/-- Sparsity constrains the sum of the two ranks. A bound on paid rank is
needed to turn it into a positive charge outside those gates. -/
theorem remainingRank_lower_of_sparse (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (out : Wire n g) (paid : Finset (Fin g)) (B : ℕ)
    (hYes : restrictedWire p pin out a = true)
    (hSparse : (acceptingTables (restrictedWire p pin out)).card ≤ 2^B) :
    k ≤ B + paidRank p pin a paid + remainingRank p pin a paid + 1 := by
  have h := pinRank_lower p pin a out B hYes hSparse
  rw [pinRank_split p pin a paid] at h
  omega

noncomputable def afterPaidTrace (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) (j : Fin g) :
    RawQuotient pin a ⧸ paidSpan p pin a paid :=
  (paidSpan p pin a paid).mkQ (pinQuotientTrace p pin a j)

theorem independent_outside_paid (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (paid : Finset (Fin g)) :
    ∃ pick : Fin (remainingRank p pin a paid) ↪ Fin g,
      (∀ i, pick i ∈ (binaryGates p \ constantReaders p pin) \ paid) ∧
      LinearIndependent F₂ (fun i => afterPaidTrace p pin a paid (pick i)) := by
  let outside := (binaryGates p \ constantReaders p pin) \ paid
  let gen (j : outside) := afterPaidTrace p pin a paid j.val
  have he : remainingRank p pin a paid = Module.finrank F₂ (Submodule.span F₂ (Set.range gen)) := by
    unfold remainingRank
    rw [outside_generates]
    rfl
  rw [he]
  obtain ⟨f,hf,_,hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F₂ (Set.range gen)
  choose j hj using hf
  have hVec : (fun i => afterPaidTrace p pin a paid (j i).val) = f := funext hj
  have hi : Function.Injective (fun i => (j i).val) := by
    intro u v h
    apply hli.injective
    rw [← hj u,← hj v]
    exact congrArg (afterPaidTrace p pin a paid) h
  exact ⟨⟨_,hi⟩,fun i => (j i).property,hVec.symm ▸ hli⟩

open CornerCertificates in
/-- A numerical gate bound from sparsity once the actual paid rank and
the number of already counted original indices are available. -/
theorem count_paid_and_additional_of_sparse (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (out : Wire n g) (paid : Finset (Fin g)) (B : ℕ)
    (hYes : restrictedWire p pin out a = true)
    (hSparse : (acceptingTables (restrictedWire p pin out)).card ≤ 2^B) :
    (paid ∪ constantReaders p pin).card +
      (k-(B+paidRank p pin a paid+1)) ≤ g := by
  have hLower := remainingRank_lower_of_sparse p pin a out paid B hYes hSparse
  have hUpper := remainingRank_with_paid_and_losses p pin a paid
  omega

end Quotient

section CountedChain

open RawReaderNecessity CornerCertificates
variable {n : ℕ}

def andRoot (k : ℕ) (hk : k < n) : Wire n k :=
  match k with
  | 0 => .input ⟨0,hk⟩
  | t+1 => .gate (Fin.last t)

/-- A monotone comb with one new leaf at each gate. Every AND feeds the
next AND, and the last one is the comb output. -/
def andComb (n : ℕ) : (k : ℕ) → k < n → Program signature n k
  | 0, _ => .empty
  | k+1, hk => (andComb n k (by omega)).gate
      (RawPairPool.chainLine false (andRoot k (by omega)) (.input ⟨k+1,hk⟩))

private theorem comb_trace (k : ℕ) (hk : k < n) (x : BitString n) :
    (andComb n k hk).trace interpretation x (andRoot k hk) = false ↔
      ∃ i : Fin n, i.val ≤ k ∧ x i = false := by
  induction k with
  | zero =>
    change x ⟨0,hk⟩ = false ↔ _
    exact ⟨fun h => ⟨⟨0,hk⟩,le_rfl,h⟩,fun ⟨i,hi,he⟩ =>
      (Fin.ext (Nat.le_zero.mp hi) : i = ⟨0,hk⟩) ▸ he⟩
  | succ k ih =>
    have hprev : k < n := by omega
    let p := andComb n k hprev
    let i : Fin n := ⟨k+1,hk⟩
    let line := RawPairPool.chainLine false (andRoot k hprev) (.input i)
    have he : (andComb n (k+1) hk).trace interpretation x (andRoot (k+1) hk) =
        (p.trace interpretation x (andRoot k hprev) && x i) := by
      change (p.gate line).eval interpretation x (Fin.last k) = _
      rw [Program.eval_gate_last]
      rfl
    rw [he, Bool.and_eq_false_iff, ih hprev]
    constructor
    · rintro (⟨j,hj,hb⟩ | hb)
      · exact ⟨j,by omega,hb⟩
      · exact ⟨i,le_rfl,hb⟩
    · rintro ⟨j,hj,hb⟩
      by_cases h : j.val ≤ k
      · exact Or.inl ⟨j,h,hb⟩
      · exact Or.inr ((Fin.ext (by dsimp [i]; omega) : j=i) ▸ hb)

def stageGate (k : ℕ) (i : Fin n) (hi : 0 < i.val) (h : i.val ≤ k) : Fin k :=
  ⟨i.val-1,by omega⟩

private theorem comb_stage_trace (k : ℕ) (hk : k < n) (i : Fin n) (hi : 0 < i.val)
    (h : i.val ≤ k) (x : BitString n) :
    (andComb n k hk).trace interpretation x (.gate (stageGate k i hi h)) = false ↔
      ∃ j : Fin n, j.val ≤ i.val ∧ x j = false := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i.val=k+1
    · rw [show stageGate (k+1) i hi h = Fin.last k from Fin.ext (by dsimp [stageGate]; omega)]
      change (andComb n (k+1) hk).trace interpretation x (andRoot (k+1) hk) = false ↔ _
      rw [comb_trace,he]
    · have h' : i.val ≤ k := by omega
      have hg : stageGate (k+1) i hi h = (stageGate k i hi h').castSucc := Fin.ext rfl
      rw [hg]
      change ((andComb n k (by omega)).gate _).trace interpretation x
        (Wire.gate (stageGate k i hi h')).castSucc = false ↔ _
      rw [Program.trace_gate_castSucc]
      exact ih (by omega) h'

/-- Append the existing recognizer to the comb and OR its answer with the
all-one guard. The comb's original indices and wire functions stay visible. -/
theorem same_recognizer_with_comb {f : BooleanFunction n} (hn : 2 ≤ n)
    (hYes : f (fun _ => true) = true) :
    ∃ (c : Circuit signature n 1) (gate : Fin n → Fin c.size),
      c.Computes interpretation (single f) ∧
      c.size ≤ complexity interpretation (single f)+n ∧
      ∀ (i : Fin n), 0 < i.val → ∀ T,
        c.program.trace interpretation T (.gate (gate i)) = false ↔
          ∃ j : Fin n, j.val ≤ i.val ∧ T j = false := by
  obtain ⟨base,hBase,hMin⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  let k := n-1
  have hk : k < n := by dsimp [k]; omega
  let p0 := andComb n k hk
  let p := p0.append Wire.input base.program
  let w := (andRoot k hk).castAdd base.size
  let v : Wire n (k+base.size) := Program.appendedWire Wire.input (base.outputs 0)
  let line := RawPairPool.chainLine true w v
  let q := p.gate line
  let c : Circuit signature n 1 := ⟨q,fun _ => .gate (Fin.last (k+base.size))⟩
  let gate (i : Fin n) : Fin c.size :=
    if hi : 0 < i.val then ((stageGate k i hi (by dsimp [k]; omega)).castAdd base.size).castSucc
      else Fin.last (k+base.size)
  refine ⟨c,gate,?_,?_,?_⟩
  · intro T
    funext j
    change q.eval interpretation T (Fin.last (k+base.size)) = f T
    change (p.gate line).eval interpretation T (Fin.last (k+base.size)) = _
    rw [Program.eval_gate_last]
    change (p.trace interpretation T w || p.trace interpretation T v) = f T
    rw [show p.trace interpretation T w = p0.trace interpretation T (andRoot k hk) from
      Program.trace_append_castAdd _ _ _ _ _ _]
    have hv := Program.trace_append_appendedWire p0 Wire.input interpretation T base.program (base.outputs 0)
    have hb := congrFun (hBase T) 0
    change base.program.trace interpretation T (base.outputs 0) = f T at hb
    change p.trace interpretation T v = base.program.trace interpretation T (base.outputs 0) at hv
    rw [hv, hb]
    cases hGuard : p0.trace interpretation T (andRoot k hk)
    · rfl
    · have hAll : T = fun _ => true := by
        funext i
        cases hi : T i
        · have hC := (comb_trace k hk T).mpr ⟨i,by dsimp [k]; omega,hi⟩
          rw [hGuard] at hC
          cases hC
        · rfl
      rw [hAll]
      simp [hYes]
  · change k+base.size+1 ≤ _
    dsimp [k]
    omega
  intro i hi T
  have hw : (.gate (gate i) : Wire n c.size) =
      ((Wire.gate (stageGate k i hi (by dsimp [k]; omega)) : Wire n k).castAdd base.size).castSucc := by
    simp only [gate,hi,dite_true]
    rfl
  change q.trace interpretation T (.gate (gate i)) = false ↔ _
  rw [hw]
  have ht := Program.trace_append_castAdd p0 Wire.input interpretation T base.program
    (Wire.gate (stageGate k i hi (by dsimp [k]; omega)))
  change (p.gate line).trace interpretation T
    ((Wire.gate (stageGate k i hi (by dsimp [k]; omega))).castAdd base.size).castSucc = false ↔ _
  rw [Program.trace_gate_castSucc, ht]
  exact comb_stage_trace k hk i hi (by dsimp [k]; omega) T

private def delta (i : Fin n) : Fin n → F₂ := Pi.single i 1

private def mixedEval (i j : Fin n) : ((Fin n → F₂) → F₂) →ₗ[F₂] F₂ where
  toFun f := f (delta i+delta j)+f (delta i)+f (delta j)
  map_add' f g := by
    simp only [Pi.add_apply]
    ring
  map_smul' a f := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

private theorem field_self_add (a : F₂) : a+a=0 := by
  calc
    _ = (1+1)*a := by ring
    _ = _ := by rw [show (1+1:F₂)=0 from rfl,zero_mul]

private theorem mixedEval_vanishes (pin : Fin n → Fin n ⊕ Bool) (a : BitString n)
    (i j : Fin n) :
    rawSpan (substitute pin a) (fun z => substitute pin (perturb a z)) ≤ LinearMap.ker (mixedEval i j) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v,rfl⟩
  obtain ⟨L,hL⟩ := pin_raw_linear pin a v
  apply LinearMap.mem_ker.mpr
  let f := raw (substitute pin a) (fun z => substitute pin (perturb a z)) v
  change f (delta i+delta j)+f (delta i)+f (delta j) = 0
  change ∀ x ∈ (⊤ : Submodule F₂ (Fin n → F₂)), f x = L x at hL
  rw [hL _ Submodule.mem_top,hL _ Submodule.mem_top,hL _ Submodule.mem_top,map_add]
  calc
    _ = (L (delta i)+L (delta i))+(L (delta j)+L (delta j)) := by ring
    _ = _ := by rw [field_self_add,field_self_add,zero_add]

private noncomputable def pairEval (pin : Fin n → Fin n ⊕ Bool) (a : BitString n) (i j : Fin n) :
    RawQuotient pin a →ₗ[F₂] F₂ :=
  (rawSpan (substitute pin a) (fun z => substitute pin (perturb a z))).liftQ
    (mixedEval i j) (mixedEval_vanishes pin a i j)

private theorem single_flip (P : Finset (Fin n)) {i : Fin n} (hi : i ∉ P) (t : Fin n) :
    substitute (pinAt (fun _ => true) P) (perturb (fun _ => true) (delta i)) t = false ↔ t=i := by
  by_cases hP : t ∈ P
  · have hn : t ≠ i := fun h => hi (h ▸ hP)
    simp [substitute,pinAt,hP,hn]
  · by_cases he : t=i
    · subst t
      simp [substitute,pinAt,hP,perturb,delta]
    · simp [substitute,pinAt,hP,perturb,delta,he]

private theorem double_flip (P : Finset (Fin n)) {i j : Fin n} (hi : i ∉ P) (hj : j ∉ P)
    (hne : i ≠ j) (t : Fin n) :
    substitute (pinAt (fun _ => true) P) (perturb (fun _ => true) (delta i+delta j)) t =
      false ↔ t=i ∨ t=j := by
  by_cases hP : t ∈ P
  · have hni : t ≠ i := fun h => hi (h ▸ hP)
    have hnj : t ≠ j := fun h => hj (h ▸ hP)
    simp [substitute,pinAt,hP,hni,hnj]
  · by_cases hI : t=i
    · subst t
      simp [substitute,pinAt,hP,perturb,delta,hne]
    · by_cases hJ : t=j
      · subst t
        simp [substitute,pinAt,hP,perturb,delta,hI]
      · simp [substitute,pinAt,hP,perturb,delta,hI,hJ]

private theorem chain_pair_eval {g : ℕ} (p : Program signature n g) (P : Finset (Fin n))
    {i j t : Fin n} (hi : i ∉ P) (hj : j ∉ P) (hne : i ≠ j) (hij : i.val ≤ j.val) (w : Fin g)
    (hWire : ∀ T, p.trace interpretation T (.gate w) = false ↔
      ∃ v : Fin n, v.val ≤ t.val ∧ T v = false) :
    pairEval (pinAt (fun _ => true) P) (fun _ => true) i j
      (pinQuotientTrace p (pinAt (fun _ => true) P) (fun _ => true) w) =
      if j.val ≤ t.val then 1 else 0 := by
  let a : BitString n := fun _ => true
  let pin := pinAt a P
  let base := substitute pin a
  let T (z : Fin n → F₂) := substitute pin (perturb a z)
  let f := centered p base T (.gate w)
  have hb : base = a := by
    funext v
    by_cases hv : v ∈ P <;> simp [base,pin,pinAt,hv]
  have hBase : p.trace interpretation base (.gate w) = true := by
    apply Bool.eq_true_of_not_eq_false
    rw [hWire,hb]
    simp [a]
  have htrace (z : Fin n → F₂) :
      f z = if (∃ v : Fin n, v.val ≤ t.val ∧ T z v=false) then 1 else 0 := by
    have hCond := hWire (T z)
    cases h : p.trace interpretation (T z) (.gate w)
    · have hv := hCond.mp h
      simp only [hv,ite_true,f,centered,hBase,h]
      rfl
    · have hn : ¬∃ v : Fin n, v.val ≤ t.val ∧ T z v=false := by
        intro hz
        have hh := hCond.mpr hz
        rw [h] at hh
        cases hh
      simp only [hn,ite_false,f,centered,hBase,h]
      rfl
  have hI : f (delta i) = if i.val ≤ t.val then 1 else 0 := by
    rw [htrace]
    have he : (∃ v : Fin n, v.val ≤ t.val ∧ T (delta i) v=false) ↔ i.val ≤ t.val := by
      simp only [T,pin,a,single_flip P hi]
      exact ⟨fun ⟨v,hv,he⟩ => he ▸ hv,fun h => ⟨i,h,rfl⟩⟩
    simp only [he]
  have hJ : f (delta j) = if j.val ≤ t.val then 1 else 0 := by
    rw [htrace]
    have he : (∃ v : Fin n, v.val ≤ t.val ∧ T (delta j) v=false) ↔ j.val ≤ t.val := by
      simp only [T,pin,a,single_flip P hj]
      exact ⟨fun ⟨v,hv,he⟩ => he ▸ hv,fun h => ⟨j,h,rfl⟩⟩
    simp only [he]
  have hIJ : f (delta i+delta j) = if i.val ≤ t.val then 1 else 0 := by
    rw [htrace]
    have he : (∃ v : Fin n, v.val ≤ t.val ∧ T (delta i+delta j) v=false) ↔ i.val ≤ t.val := by
      simp only [T,pin,a,double_flip P hi hj hne]
      constructor
      · rintro ⟨v,hv,rfl | rfl⟩
        · exact hv
        · exact hij.trans hv
      · exact fun h => ⟨i,h,Or.inl rfl⟩
    simp only [he]
  change (rawSpan base T).liftQ (mixedEval i j) _ (Submodule.Quotient.mk f) = _
  rw [Submodule.liftQ_apply]
  change f (delta i+delta j)+f (delta i)+f (delta j) = _
  rw [hIJ,hI,hJ,field_self_add,zero_add]

private theorem independent_of_triangular_evaluations {J W : Type*} [LinearOrder J] [Fintype J]
    [AddCommGroup W] [Module F₂ W] (v : J → W) (eval : J → W →ₗ[F₂] F₂)
    (hEval : ∀ i j, eval i (v j) = if i ≤ j then 1 else 0) : LinearIndependent F₂ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro coeff h i
  by_contra hn
  let S := Finset.univ.filter (fun j => coeff j ≠ 0)
  have hS : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  let top := S.max' hS
  have ht := Finset.max'_mem S hS
  have hz := congrArg (eval top) h
  rw [map_sum,map_zero] at hz
  simp only [map_smul,hEval,smul_eq_mul] at hz
  have he : (∑ j, coeff j*(if top ≤ j then 1 else 0)) = coeff top := by
    rw [Finset.sum_eq_single top]
    · simp
    · intro j _ hj
      by_cases hLe : top ≤ j
      · have h0 : coeff j = 0 := by
          by_contra hNon
          have hIn : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hNon⟩
          exact hj (le_antisymm (Finset.le_max' S _ hIn) hLe)
        simp [h0]
      · simp [hLe]
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  exact (Finset.mem_filter.mp ht).2 (he.symm.trans hz)

/-- A live AND comb can already carry one independent direction per free
leaf after the first, even after arbitrary all-one pins. -/
theorem comb_paidRank_lower {g : ℕ} (p : Program signature n g) (gate : Fin n → Fin g)
    (hTrace : ∀ t : Fin n, 0 < t.val → ∀ T,
      p.trace interpretation T (.gate (gate t)) = false ↔
        ∃ v : Fin n, v.val ≤ t.val ∧ T v = false)
    (P : Finset (Fin n)) (hP : P.card < n) :
    let paid := ((Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val)).image gate
    n-P.card-1 ≤ paidRank p (pinAt (fun _ => true) P) (fun _ => true) paid := by
  let paid := ((Finset.univ : Finset (Fin n)).filter (fun i => 0 < i.val)).image gate
  let A : Finset (Fin n) := Finset.univ \ P
  have ha : A.card+P.card = n := by
    simpa [A] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  let start := A.min' hA
  have hStart := Finset.min'_mem A hA
  let J := A.erase start
  have hJ : J.card = n-P.card-1 := by
    rw [Finset.card_erase_of_mem hStart]
    omega
  let a : BitString n := fun _ => true
  let pin := pinAt a P
  let v (t : J) := pinQuotientTrace p pin a (gate t.val)
  have before (t : J) : start.val < t.val.val := by
    have ht := Finset.mem_erase.mp t.property
    have hLe : start.val ≤ t.val.val := Finset.min'_le A _ ht.2
    have hNe : start.val ≠ t.val.val := fun h => ht.1 (Fin.ext h.symm)
    exact lt_of_le_of_ne hLe hNe
  have hPos (t : J) : 0 < t.val.val := by have h := before t; omega
  have hEval (i j : J) : pairEval pin a start i.val (v j) = if i ≤ j then 1 else 0 := by
    have hn := Finset.mem_erase.mp i.property
    exact chain_pair_eval p P (Finset.mem_sdiff.mp hStart).2 (Finset.mem_sdiff.mp hn.2).2
      hn.1.symm (before i).le _ (hTrace j.val (hPos j))
  have hLI : LinearIndependent F₂ v := independent_of_triangular_evaluations v _ hEval
  have hSub : Submodule.span F₂ (Set.range v) ≤ paidSpan p pin a paid := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span ⟨⟨gate j.val,
      Finset.mem_image.mpr ⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hPos j⟩,rfl⟩⟩,rfl⟩
  have hDim : Module.finrank F₂ (Submodule.span F₂ (Set.range v)) = J.card := by
    rw [finrank_span_eq_card hLI,Fintype.card_coe]
  rw [← hJ,← hDim]
  exact Submodule.finrank_mono hSub

end CountedChain

section Applications

open CornerCertificates ForestBlockPinning MultiBlockPinning QuadraticForest JointSparseCompletion

set_option exponentiation.threshold 30000 in
/-- Apply the two quotients to the actual tested joint forest restriction. -/
theorem mcsp32_clean_quotient_budget (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32)))
    (hSize : c.size ≤ 3*(2^32)) :
    ∃ (E : Finset (BitString 28)) (x : BitString (2^32)) (exit : E ↪ Fin c.size),
      E.card = 11 ∧
      (∀ s : E, exit s ∈ downstreamReaders c.program (blocks (d := 4) E) x) ∧
      (let pin := pinAt x (blocks (d := 4) E)
       let forest := cleanGates c.program (c.outputs 0)
       let a : BitString (2^32) := fun _ => false
       4294948381 ≤ paidRank c.program pin a forest + remainingRank c.program pin a forest ∧
       remainingRank c.program pin a forest + (forest ∪ constantReaders c.program pin).card ≤ c.size) := by
  obtain ⟨E,x,exit,hE,hExit,hS,hQ,_⟩ := mcsp32_eleven_joint_exits c hc hMin hSize
  let P := blocks (d := 4) E
  let pin := pinAt x P
  let forest := cleanGates c.program (c.outputs 0)
  let a : BitString (2^32) := fun _ => false
  have hEq := NestedFaces.restricted_circuit_eq c hc pin
  have hYes : restrictedWire c.program pin (c.outputs 0) a = true := by
    have h := hQ (zeroVec 32) false (zeroVec 32) (zeroVec 32)
    have he : MCSP.truthTable 32 (quad (zeroVec 32) false (zeroVec 32) (zeroVec 32)) = a := by
      funext i
      simp only [MCSP.truthTable_apply,quad,SuperTwoN.affine,dot_zero_left,Bool.and_false,Bool.xor_false]
      rfl
    rw [he] at h
    rw [hEq]
    exact h
  have hSparse : (acceptingTables (restrictedWire c.program pin (c.outputs 0))).card ≤ 2^18914 := by
    rw [hEq]
    exact hS
  have hR := remainingRank_lower_of_sparse c.program pin a (c.outputs 0) forest 18914 hYes hSparse
  refine ⟨E,x,exit,hE,fun s => (hExit s).2,?_,remainingRank_with_paid_and_losses c.program pin a forest⟩
  change 4294948381 ≤ paidRank c.program pin a forest+remainingRank c.program pin a forest
  norm_num at hR
  omega

/-- The sparse signed-AND control can carry essentially all the guaranteed
rank in a named monotone comb, on every non-full all-one pin set. -/
theorem signedAnd_comb_paid_rank (r : ℕ) (hr : 10 ≤ r) :
    let N := 2^JointOrbit.logArity r
    ∃ (c : Circuit signature N 1) (paid : Finset (Fin c.size)),
      c.Computes interpretation (single (GrowingAndOrbit.control r hr)) ∧
      c.size ≤ (5100*(r+1)+1)*N ∧
      ∀ P : Finset (Fin N), P.card < N →
        N-P.card-1 ≤ paidRank c.program (pinAt (fun _ => true) P) (fun _ => true) paid := by
  let N := 2^JointOrbit.logArity r
  let f := GrowingAndOrbit.control r hr
  have hN : 2 ≤ N := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    (show 1 ≤ JointOrbit.logArity r from Nat.succ_pos _)
  obtain ⟨c,gate,hc,hSize,hTrace⟩ :=
    same_recognizer_with_comb hN (ChargeMultiplicity.signedAnd_constant r hr true)
  let paid := ((Finset.univ : Finset (Fin N)).filter (fun i => 0 < i.val)).image gate
  refine ⟨c,paid,hc,?_,fun P hP => comb_paidRank_lower c.program gate hTrace P hP⟩
  calc
    _ ≤ complexity interpretation (single f)+N := hSize
    _ ≤ 5100*(r+1)*N+N := Nat.add_le_add_right (GrowingAndOrbit.control_size r hr) _
    _ = _ := by ring

end Applications

#print axioms pinRank_split
#print axioms remainingRank_with_paid_and_losses
#print axioms independent_outside_paid
#print axioms count_paid_and_additional_of_sparse
#print axioms mcsp32_clean_quotient_budget
#print axioms comb_paidRank_lower
#print axioms signedAnd_comb_paid_rank

end PvsNP.Frontier.ForestTraceQuotient
