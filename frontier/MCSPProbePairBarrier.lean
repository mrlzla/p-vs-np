module

public import MCSPRawPairPool
public import MCSPPolynomialBarrier
public import MCSPMultiCertificates

/-! Two tests of the raw-pair approach. Exact MCSP rules out compressing
many whole blocks to just their AND and OR. Probe acceptance and sparsity
alone allow small circuits with no binary gates reading two raw inputs. -/

@[expose] public section

namespace PvsNP.Frontier.ProbePairBarrier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates ForestBlockPinning SuperTwoN QuadraticForest
open MultiBlockPinning IndependentBlockPinning RawPairPool PolynomialBarrier
open scoped Classical BigOperators

section BlockFlags

variable {a d B : ℕ}

/-- A table has a zero and a one in each selected block. -/
def MixedOnBlocks (E : Finset (BitString a)) (T : BitString (2^(a+d))) : Prop :=
  ∀ s ∈ E, ∀ b : Bool, ∃ i ∈ block (d := d) s, T i = b

/-- A circuit factors through the outside bits and the two flags per block
telling whether a zero or a one occurs. These are equivalent to AND/OR. -/
def DependsOnBlockFlags (F : BooleanFunction (2^(a+d))) (E : Finset (BitString a)) : Prop :=
  ∀ U V : BitString (2^(a+d)), (∀ i ∉ blocks (d := d) E, U i = V i) →
    (∀ s ∈ E, ∀ b : Bool,
      (∃ i ∈ block (d := d) s, U i = b) ↔ ∃ i ∈ block (d := d) s, V i = b) →
    F U = F V

/-- One accepted mixed table preserves all flags after fixing two
entries per block. Sparsity bounds how many entries can remain free. -/
theorem mixed_flag_capacity (F : BooleanFunction (2^(a+d))) (E : Finset (BitString a))
    (T : BitString (2^(a+d))) (hYes : F T = true) (hMixed : MixedOnBlocks (d := d) E T)
    (hSparse : (acceptingTables F).card ≤ 2^B) (hFlags : DependsOnBlockFlags F E) :
    E.card*2^d ≤ 2*E.card+B := by
  let P := blocks (d := d) E
  have pick (s : E) (b : Bool) : ∃ i ∈ block (d := d) s.val, T i = b :=
    hMixed s.val s.property b
  choose addr hAddr hBit using pick
  let anchors := (Finset.univ : Finset (E × Bool)).image (fun sb => addr sb.1 sb.2)
  let outside := (Finset.univ : Finset (Fin (2^(a+d)))) \ P
  let mask := outside ∪ anchors
  have hAccept (U : BitString (2^(a+d))) (hU : ∀ i ∈ mask, U i = T i) : F U = true := by
    apply (hFlags U T ?_ ?_).trans hYes
    · intro i hi
      exact hU i (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩))
    · intro s hs b
      constructor
      · exact fun _ => hMixed s hs b
      · intro _
        let q : E := ⟨s,hs⟩
        refine ⟨addr q b, hAddr q b, ?_⟩
        exact (hU _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(q,b), Finset.mem_univ _, rfl⟩))).trans (hBit q b)
  have hFree := card_masked_le hSparse T mask hAccept
  have hAnchor : anchors.card ≤ 2*E.card := Finset.card_image_le.trans (by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_coe, Nat.mul_comm, le_refl])
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  simp only [Finset.card_univ, Fintype.card_fin] at hPart
  change outside.card+P.card = 2^(a+d) at hPart
  rw [show P.card = E.card*2^d from card_blocks E] at hPart
  have hMask : mask.card ≤ outside.card+anchors.card := Finset.card_union_le _ _
  omega

private theorem address_of_uniform_tail (s : BitString a) (b : Bool) :
    BitString.equivFin (a+d) (Fin.append s (fun _ : Fin d => b)) ∈ block (d := d) s := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simp [tag, addressHead, Function.comp_def]

/-- A suffix projection is simultaneously mixed on every full block. -/
theorem suffix_projection_mixed (E : Finset (BitString a)) (j : Fin d) :
    MixedOnBlocks (d := d) E (MCSP.truthTable (a+d) (fun x => x (Fin.natAdd a j))) := by
  intro s _ b
  refine ⟨_, address_of_uniform_tail (d := d) s b, ?_⟩
  simp only [MCSP.truthTable_apply, Equiv.symm_apply_apply, Fin.append_right]

/-- Exact MCSP can summarize at most this many blocks by their AND/OR
flags. The witness is one projection, mixed on all blocks at once. -/
theorem mcspSquare_flag_capacity (E : Finset (BitString a)) (j : Fin d)
    (hFlags : DependsOnBlockFlags (mcspSquare (a+d)) E) :
    E.card*2^d ≤ 2*E.card+descriptionBitBound (a+d) :=
  mixed_flag_capacity _ E _ (MultiCertificates.mcspSquare_accepts_projection _ (Fin.natAdd a j))
    (suffix_projection_mixed E j) (card_accepting_mcspSquare_le _) hFlags

/-- A rank-one quadratic made from two suffix coordinates gives the
same obstruction via a non-affine mixed probe. -/
theorem mcspSquare_quadratic_flag_capacity (E : Finset (BitString a)) (i j : Fin d)
    (hm : 13 ≤ a+d) (hFlags : DependsOnBlockFlags (mcspSquare (a+d)) E) :
    E.card*2^d ≤ 2*E.card+descriptionBitBound (a+d) := by
  let u : BitString (a+d) := fun k => decide (k = Fin.natAdd a i)
  let v : BitString (a+d) := fun k => decide (k = Fin.natAdd a j)
  let F := quad (zeroVec (a+d)) false u v
  let T := MCSP.truthTable (a+d) F
  have hMix : MixedOnBlocks (d := d) E T := by
    intro s _ b
    refine ⟨_, address_of_uniform_tail (d := d) s b, ?_⟩
    simp [T, F, quad, affine, dot_zero_left, u, v, MCSP.truthTable_apply, dot_basisVec]
  exact mixed_flag_capacity _ E T (mcspSquare_accepts_quad _ hm _ _ _ _) hMix
    (card_accepting_mcspSquare_le _) hFlags

/-- Independent replacement in each block composes over disjoint
prefix blocks. -/
theorem individual_flags_combine (F : BooleanFunction (2^(a+d))) (E : Finset (BitString a))
    (hEach : ∀ s ∈ E, DependsOnBlockFlags (d := d) F {s}) :
    DependsOnBlockFlags F E := by
  induction E using Finset.induction_on with
  | empty =>
    intro U V hOutside _
    exact congrArg F (funext fun i => hOutside i (by simp [blocks]))
  | @insert s E hs ih =>
    intro U V hOutside hFlags
    let W (i : Fin (2^(a+d))) := if tag i = s then U i else V i
    have hIn (i) (hi : i ∈ block (d := d) s) : W i = U i := by
      simp [W, (Finset.mem_filter.mp hi).2]
    have hOut (i) (hi : i ∉ block (d := d) s) : W i = V i := by
      have hn : tag i ≠ s := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      simp [W, hn]
    have hRepl : F W = F V := by
      apply hEach s (Finset.mem_insert_self ..) W V
      · intro i hi
        apply hOut i
        intro h
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2⟩)
      · intro q hq b
        have hqs : q = s := Finset.mem_singleton.mp hq
        subst q
        rw [← hFlags s (Finset.mem_insert_self ..) b]
        exact exists_congr fun i => and_congr_right fun hi => by rw [hIn i hi]
    have hRemaining := ih (fun q hq => hEach q (Finset.mem_insert_of_mem hq))
    apply (hRemaining U W ?_ ?_).trans hRepl
    · intro i hi
      by_cases hin : i ∈ block (d := d) s
      · exact (hIn i hin).symm
      · rw [hOut i hin]
        apply hOutside i
        intro him
        rcases Finset.mem_insert.mp (Finset.mem_filter.mp him).2 with he | he
        · exact hin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
        · exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    · intro q hq b
      rw [hFlags q (Finset.mem_insert_of_mem hq) b]
      exact exists_congr fun i => and_congr_right fun hi => by
        have hn : i ∉ block (d := d) s := fun he =>
          hs (((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp he).2) ▸ hq)
        rw [hOut i hn]

/-- Even if a different circuit implements the two flags in each block,
only few blocks can be summarized that way in exact MCSP. -/
noncomputable def flagOnlyBlocks (a d : ℕ) : Finset (BitString a) :=
  Finset.univ.filter fun s => DependsOnBlockFlags (d := d) (mcspSquare (a+d)) {s}

theorem mcspSquare_individual_flag_capacity (j : Fin d) :
    (flagOnlyBlocks a d).card*2^d ≤ 2*(flagOnlyBlocks a d).card+descriptionBitBound (a+d) :=
  mcspSquare_flag_capacity _ j
    (individual_flags_combine _ _ (fun _ hs => (Finset.mem_filter.mp hs).2))

/-- Except for at most B/(2^d-2) blocks, there are two tables differing
in that block alone that have the same flags and different MCSP decisions. -/
theorem mcspSquare_many_blocks_need_more_than_flags (hd : 2 ≤ d) :
    2^a ≤ ((Finset.univ : Finset (BitString a)) \ flagOnlyBlocks a d).card +
      descriptionBitBound (a+d)/(2^d-2) := by
  let E := flagOnlyBlocks a d
  have h := mcspSquare_individual_flag_capacity (a := a) (d := d) ⟨0,by omega⟩
  have hL : 4 ≤ (2:ℕ)^d := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd
  have hSplit : E.card*(2^d-2)+2*E.card = E.card*2^d := by
    rw [Nat.mul_comm 2 E.card, ← Nat.mul_add, Nat.sub_add_cancel (by omega : 2 ≤ (2:ℕ)^d)]
  change E.card*2^d ≤ 2*E.card+descriptionBitBound (a+d) at h
  have hSub : E.card*(2^d-2) ≤ descriptionBitBound (a+d) := by omega
  have hE := (Nat.le_div_iff_mul_le (by omega : 0 < (2:ℕ)^d-2)).mpr hSub
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
  rw [Finset.card_univ, BitString.card] at hPart
  exact hPart.ge.trans (Nat.add_le_add_left hE _)

/-- At arity 32 almost all of the 256-address blocks require distinctions
beyond their two flags. -/
theorem mcspSquare_32_nonflag_blocks :
    16777108 ≤ ((Finset.univ : Finset (BitString 24)) \ flagOnlyBlocks 24 8).card := by
  have h := mcspSquare_many_blocks_need_more_than_flags (a := 24) (d := 8) (by decide)
  rw [show descriptionBitBound (24+8) = 27672 by decide] at h
  norm_num at h
  omega

end BlockFlags

section ProbeControl

variable {n g : ℕ}

/-- Every gate with a raw argument is unary or nullary. -/
def UnaryRawReaders (p : Program signature n g) : Prop :=
  ∀ j : Fin g, ∀ b : Fin (signature.Arity (p.lines j).op), ∀ i : Fin n,
    (p.lines j).wires b = .input i → signature.Arity (p.lines j).op ≤ 1

private theorem raw_of_castSucc {w : Wire n g} {i : Fin n}
    (h : w.castSucc = .input i) : w = .input i := by
  cases w
  · cases h
    rfl
  · cases h

private theorem unaryRaw_gate {p : Program signature n g} {l : Line signature n g}
    (hp : UnaryRawReaders p)
    (hl : ∀ b i, l.wires b = .input i → signature.Arity l.op ≤ 1) :
    UnaryRawReaders (p.gate l) := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Program.lines_gate_last]
    intro b i h
    exact hl b i (raw_of_castSucc h)
  · rw [Program.lines_gate_castSucc]
    intro b i h
    exact hp j b i (raw_of_castSucc h)

/-- Feed a suffix program entirely from gate wires. It introduces no new
raw readers, even when its own input gates read two arguments. -/
theorem unaryRaw_append {k h : ℕ} (p : Program signature n g) (q : Program signature k h)
    (feed : Fin k → Wire n g) (hp : UnaryRawReaders p)
    (hFeed : ∀ i : Fin k, ∃ j : Fin g, feed i = .gate j) :
    UnaryRawReaders (p.append feed q) := by
  induction q with
  | empty => exact hp
  | @gate h q l ih =>
    apply unaryRaw_gate ih
    intro b i he
    change Program.appendedWire feed (l.wires b) = .input i at he
    cases e : l.wires b with
    | input j =>
      obtain ⟨t, ht⟩ := hFeed j
      rw [e, Program.appendedWire_input, ht] at he
      cases he
    | gate j =>
      rw [e, Program.appendedWire_gate] at he
      cases he

/-- One original unary NOT per input. -/
def rawNegationProgram (n : ℕ) : (k : ℕ) → k ≤ n → Program signature n k
  | 0, _ => .empty
  | k+1, hk =>
    (rawNegationProgram n k (by omega)).gate ⟨.not, fun _ => .input ⟨k, by omega⟩⟩

private theorem rawNegation_unary (k : ℕ) (hk : k ≤ n) :
    UnaryRawReaders (rawNegationProgram n k hk) := by
  induction k with
  | zero => intro j; exact Fin.elim0 j
  | succ k ih =>
    unfold rawNegationProgram
    exact unaryRaw_gate (ih (by omega)) (fun _ _ _ => Nat.le_refl 1)

private theorem rawNegation_trace (k : ℕ) (hk : k ≤ n) (i : Fin k) (T : BitString n) :
    (rawNegationProgram n k hk).trace interpretation T (.gate i) = !(T (Fin.castLE hk i)) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    change ((rawNegationProgram n k (by omega)).gate ⟨.not, fun _ => .input ⟨k,by omega⟩⟩).trace
      interpretation T (.gate i) = !(T (Fin.castLE hk i))
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Program.trace_gateWire, Program.gateFunction_apply, Program.eval_gate_last]
      rfl
    · rw [show (.gate j.castSucc : Wire n (k+1)) = (Wire.gate j : Wire n k).castSucc from rfl,
        Program.trace_gate_castSucc]
      exact ih (by omega) j

def rawNegationCircuit (n : ℕ) : Circuit signature n n :=
  ⟨rawNegationProgram n n le_rfl, Wire.gate⟩

private theorem rawNegation_eval (n : ℕ) (T : BitString n) :
    (rawNegationCircuit n).eval interpretation T = fun i => !(T i) := by
  funext i
  exact rawNegation_trace n le_rfl i T

theorem unaryRaw_pairGates_empty {a d g : ℕ} {p : Program signature (2^(a+d)) g}
    (hRaw : UnaryRawReaders p) :
    sameBlockPairGates (a := a) (d := d) p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨i, r, hn, u, _, _, _, hu, _⟩ := (Finset.mem_filter.mp hs).2
  have hArity := hRaw j i u hu
  have hi := i.isLt
  have hr := r.isLt
  exact hn (Fin.ext (by omega))

private theorem isDeg_complement (d m : ℕ) (T : BitString (2^m)) :
    isDeg d m (fun i => !(T i)) = isDeg d m T := by
  unfold isDeg
  have h : (MCSP.truthTable m).symm (fun i => !(T i)) =
      fun z => !((MCSP.truthTable m).symm T z) := rfl
  rw [h, isDegFn_not]

/-- A sparse linear-size control accepts all quadratic probes and
projections, yet it has no raw-pair gates. The circuit bound here is an
explicit upper bound, so this does not assert minimality. -/
theorem exists_unaryRaw_quadratic_control (m : ℕ) (hm : 1 ≤ m) :
    ∃ c : Circuit signature (2^m) 1,
      c.Computes interpretation (single (isDeg 2 m)) ∧ c.size ≤ 11*2^m+m^2 ∧
      UnaryRawReaders c.program ∧ (acceptingTables (isDeg 2 m)).card ≤ 2^descriptionBitBound m ∧
      (∀ j : Fin m, isDeg 2 m (MCSP.truthTable m (fun x => x j)) = true) ∧
      (∀ (u : BitString m) (b : Bool) (v w : BitString m),
        isDeg 2 m (MCSP.truthTable m (quad u b v w)) = true) := by
  let n := 2^m
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (isDeg 2 m))
  let bank := rawNegationCircuit n
  let D := c.comp bank
  have hComputes : D.Computes interpretation (single (isDeg 2 m)) := by
    intro T
    change (c.comp bank).eval interpretation T = _
    rw [Circuit.eval_comp, show bank.eval interpretation T = _ from rawNegation_eval n T, hc]
    funext i
    exact isDeg_complement 2 m T
  have hBound : D.size ≤ 11*2^m+m^2 := by
    rw [show D.size = n+c.size from Circuit.size_comp _ _, hSize]
    have h := complexity_isDeg2_le m
    dsimp only [n]
    omega
  have hRaw : UnaryRawReaders D.program := unaryRaw_append bank.program c.program bank.outputs
    (rawNegation_unary n le_rfl) (fun i => ⟨i,rfl⟩)
  refine ⟨D, hComputes, hBound, hRaw, card_accepting_isDeg2_le_mcspBound m hm, ?_, isDeg_two_accepts_quad m⟩
  intro j
  have h := isDeg_two_accepts_quad m (fun i => decide (i = j)) false (zeroVec m) (zeroVec m)
  have he : quad (fun i => decide (i=j)) false (zeroVec m) (zeroVec m) = fun x => x j := by
    funext x
    simp only [quad, affine, Bool.false_xor, dot_zero_left, Bool.and_false, Bool.xor_false, dot_basisVec]
  rwa [he] at h

/-- Even for the full exact decision function, address duality and
one unary NOT per input remove all raw-pair gates. -/
theorem exact_mcsp_unaryRaw_with_linear_overhead (m : ℕ)
    (c : Circuit signature (2^m) 1) (hc : c.Computes interpretation (single (mcspSquare m))) :
    ∃ D : Circuit signature (2^m) 1,
      D.Computes interpretation (single (mcspSquare m)) ∧
      D.size = 2^m+c.size ∧ UnaryRawReaders D.program := by
  let n := 2^m
  let bank : Circuit signature n n :=
    ⟨rawNegationProgram n n le_rfl, fun i => .gate (PairFunnelGap.compIdx m i)⟩
  let D := c.comp bank
  have hBank (T : BitString n) : bank.eval interpretation T = PairFunnelGap.dualTable m T := by
    funext i
    exact rawNegation_trace n le_rfl (PairFunnelGap.compIdx m i) T
  have hD : D.Computes interpretation (single (mcspSquare m)) := by
    intro T
    change (c.comp bank).eval interpretation T = _
    rw [Circuit.eval_comp, hBank, hc]
    funext i
    exact PairFunnelGap.mcspSquare_dualTable m T
  exact ⟨D, hD, Circuit.size_comp _ _, unaryRaw_append bank.program c.program bank.outputs
    (rawNegation_unary n le_rfl) (fun i => ⟨PairFunnelGap.compIdx m i, rfl⟩)⟩

end ProbeControl

#print axioms mcspSquare_individual_flag_capacity
#print axioms mcspSquare_32_nonflag_blocks
#print axioms mcspSquare_quadratic_flag_capacity
#print axioms unaryRaw_pairGates_empty
#print axioms exists_unaryRaw_quadratic_control
#print axioms exact_mcsp_unaryRaw_with_linear_overhead

end PvsNP.Frontier.ProbePairBarrier
