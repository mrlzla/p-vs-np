module

public import MCSPBlockChargeDichotomy
public import MCSPGrowingAndOrbit

/-! Count incidences between prefix blocks and the original gates charged
by the first- and second-exit arguments. -/

@[expose] public section

namespace PvsNP.Frontier.ChargeMultiplicity

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates ForestBlockPinning ForestPinning RestrictionCharges
open DownstreamBlockPinning IndependentBlockPinning SecondBlockExits
open MultiBlockPinning FreshCharges TwoCornerStructure
open scoped Classical BigOperators

section Counting

variable {A J : Type*} [DecidableEq J]

/-- The number of distinct labels charging an original index. -/
noncomputable def multiplicity (E : Finset A) (charge : A → Finset J) (j : J) : ℕ :=
  (E.filter fun s => j ∈ charge s).card

theorem sum_cards_eq_sum_multiplicity (E : Finset A) (charge : A → Finset J) :
    (∑ s ∈ E, (charge s).card) =
      ∑ j ∈ E.biUnion charge, multiplicity E charge j := by
  let U := E.biUnion charge
  calc
    _ = ∑ s ∈ E, ∑ j ∈ U, if j ∈ charge s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem charge hs)]
      simp
    _ = ∑ j ∈ U, ∑ s ∈ E, if j ∈ charge s then 1 else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp [multiplicity]

theorem sum_cards_le_of_multiplicity (E : Finset A) (charge : A → Finset J) (b : ℕ)
    (h : ∀ j ∈ E.biUnion charge, multiplicity E charge j ≤ b) :
    (∑ s ∈ E, (charge s).card) ≤ b*(E.biUnion charge).card := by
  rw [sum_cards_eq_sum_multiplicity]
  exact (Finset.sum_le_sum h).trans_eq (by simp [Nat.mul_comm])

end Counting

section Footprint

variable {a d g : ℕ}

/-- Each port contributes its own raw tag or the tags behind a gate operand. -/
private noncomputable def portTags (p : Program signature (2^(a+d)) g)
    (back : Fin g → Finset (BitString a)) (j : Fin g) : Finset (BitString a) :=
  Finset.univ.biUnion fun b => match (p.lines j).wires b with
    | .input i => {tag i}
    | .gate u => back u

private theorem card_portTags (p : Program signature (2^(a+d)) g)
    (back : Fin g → Finset (BitString a)) (j : Fin g) {cap : ℕ}
    (hPos : 1 ≤ cap) (hBack : ∀ u, (back u).card ≤ cap) :
    (portTags p back j).card ≤ 2*cap := by
  let f (b : Fin (signature.Arity (p.lines j).op)) :=
    match (p.lines j).wires b with | .input i => {tag i} | .gate u => back u
  have hEach (b) : (f b).card ≤ cap := by
    cases he : (p.lines j).wires b with
    | input i => simpa [f, he] using hPos
    | gate u => simpa [f, he] using hBack u
  calc
    _ ≤ ∑ b, (f b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : Fin (signature.Arity (p.lines j).op), cap :=
      Finset.sum_le_sum (fun b _ => hEach b)
    _ ≤ _ := by
      simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right cap (Program.fanInAtMost_iff.mp p.fanInAtMost_two j)

private theorem readerTags_sub_port (p : Program signature (2^(a+d)) g)
    (back : Fin g → Finset (BitString a)) (j : Fin g) :
    readerTags p j ⊆ portTags p back j := by
  intro s hs
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp hs
  refine Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,?_⟩
  cases he : (p.lines j).wires b <;> simp_all

private theorem nearbyTags_sub_port (p : Program signature (2^(a+d)) g)
    (back : Fin g → Finset (BitString a)) (j : Fin g)
    (hBack : ∀ u, readerTags p u ⊆ back u) :
    nearbyTags p j ⊆ portTags p back j := by
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact readerTags_sub_port p back j h
  · obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp h
    refine Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,?_⟩
    cases he : (p.lines j).wires b with
    | input i => simp [he] at hb
    | gate u => simpa only [he] using hBack u (by simpa only [he] using hb)

/-- The first-exit footprint has at most four tags. A raw input and a
predecessor gate compete for the same port. -/
theorem card_first_footprint (p : Program signature (2^(a+d)) g) (j : Fin g) :
    (nearbyTags p j).card ≤ 4 :=
  (Finset.card_le_card (nearbyTags_sub_port p (readerTags p) j (fun _ => Finset.Subset.rfl))).trans
    (card_portTags p (readerTags p) j (by decide) (card_readerTags_le p))

/-- The second-exit footprint has at most eight tags. -/
theorem card_second_footprint (p : Program signature (2^(a+d)) g) (j : Fin g) :
    (extendedTags p j).card ≤ 8 := by
  apply le_trans _ (card_portTags p (nearbyTags p) j (by decide) (card_first_footprint p))
  apply Finset.card_le_card
  intro s hs
  rcases Finset.mem_union.mp hs with h | h
  · exact nearbyTags_sub_port p (nearbyTags p) j (readerTags_subset_nearby p) h
  · obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp h
    refine Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,?_⟩
    cases he : (p.lines j).wires b <;> simp_all

/-- A charge is counted at most once per block, and its original index
determines all possible block labels. Pin values may differ between blocks. -/
theorem multiplicity_le_of_footprint (E : Finset (BitString a))
    (charge : BitString a → Finset (Fin g)) (footprint : Fin g → Finset (BitString a))
    (hCharge : ∀ s ∈ E, ∀ j ∈ charge s, s ∈ footprint j) (j : Fin g) :
    multiplicity E charge j ≤ (footprint j).card := by
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hs,hj⟩ := Finset.mem_filter.mp hs
  exact hCharge s hs j hj

theorem first_exit_incidence_bound (p : Program signature (2^(a+d)) g)
    (E : Finset (BitString a)) (charge : BitString a → Finset (Fin g))
    (hCharge : ∀ s ∈ E, ∀ j ∈ charge s, s ∈ nearbyTags p j) :
    (∑ s ∈ E, (charge s).card) ≤ 4*(E.biUnion charge).card :=
  sum_cards_le_of_multiplicity E charge 4 (fun j _ =>
    (multiplicity_le_of_footprint E charge (nearbyTags p) hCharge j).trans (card_first_footprint p j))

theorem second_exit_incidence_bound (p : Program signature (2^(a+d)) g)
    (E : Finset (BitString a)) (charge : BitString a → Finset (Fin g))
    (hCharge : ∀ s ∈ E, ∀ j ∈ charge s, s ∈ extendedTags p j) :
    (∑ s ∈ E, (charge s).card) ≤ 8*(E.biUnion charge).card :=
  sum_cards_le_of_multiplicity E charge 8 (fun j _ =>
    (multiplicity_le_of_footprint E charge (extendedTags p) hCharge j).trans (card_second_footprint p j))

/-- The tighter incidence bound plugs into the existing greedy selection
for a single joint restriction. -/
theorem tighter_separated_pool (p : Program signature (2^(a+d)) g)
    (pool : Finset (BitString a)) (r K H : ℕ)
    (hHeavy : 8*g < K*(H+1)) (hRoom : r*(8*K+1)+H ≤ pool.card) :
    ∃ E ⊆ pool, E.card = r ∧ SeparatedBy (extendedTags p) E :=
  exists_separated_subset_by (extendedTags p) (card_second_footprint p) pool r K H hHeavy hRoom

private theorem blocks_singleton_eq (s : BitString a) :
    blocks (d := d) ({s} : Finset (BitString a)) = block (d := d) s := by
  ext i
  simp [blocks, block]

/-- Run each block restriction separately. Even if the same gate disappears
under several pins, the localized first exits cover at least a quarter as
many distinct original gates as there are blocks. -/
theorem distinct_first_exits_of_single_blocks (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a))
    (hFresh : fresh p Sum.inl = Finset.univ) (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ s ∈ E, ∀ i ∈ block (d := d) s,
      ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i)
    (hNon : ∀ s ∈ E, ∀ x : BitString (2^(a+d)), ¬ ∃ b : Bool,
      restrictedWire p (pinAt x (block (d := d) s)) root = fun _ => b) :
    ∃ exit : E → Fin g,
      (∀ s : E, ∃ x, exit s ∈ downstreamReaders p (block (d := d) s.val) x ∧
        s.val ∈ nearbyTags p (exit s)) ∧
      E.card ≤ 4*((Finset.univ : Finset E).image exit).card := by
  have hExit (s : E) : ∃ (j : Fin g) (x : BitString (2^(a+d))),
      j ∈ downstreamReaders p (block (d := d) s.val) x ∧ s.val ∈ nearbyTags p j := by
    let Q : Finset (BitString a) := {s.val}
    have hSep : Separated p Q := by simp [Q,Separated,SeparatedBy]
    have hp : blocks (d := d) Q = block (d := d) s.val := blocks_singleton_eq s.val
    obtain ⟨x,q,hq⟩ := exists_matched_exits p root Q hSep hFresh hLive
      (fun i hi => hRead s.val s.property i (hp ▸ hi))
      (fun y => by rw [hp]; exact hNon s.val s.property y)
    let s' : Q := ⟨s.val,Finset.mem_singleton_self _⟩
    refine ⟨(q s').val,x,?_,hq s'⟩
    exact (congrArg (fun P => (q s').val ∈ downstreamReaders p P x) hp).mp (q s').property
  choose j x hj using hExit
  let charge (s : BitString a) : Finset (Fin g) := if hs : s ∈ E then {j ⟨s,hs⟩} else ∅
  have hCap : (∑ s ∈ E, (charge s).card) ≤ 4*(E.biUnion charge).card :=
    first_exit_incidence_bound p E charge (fun s hs v hv => by
      simp only [charge, hs, dite_true, Finset.mem_singleton] at hv
      exact hv.symm ▸ (hj ⟨s,hs⟩).2)
  have hs : (∑ s ∈ E, (charge s).card) = E.card := by
    calc
      _ = ∑ _s ∈ E, 1 := Finset.sum_congr rfl (fun s hs => by simp [charge,hs])
      _ = _ := by simp
  have he : E.biUnion charge = (Finset.univ : Finset E).image j := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s,hs,hv⟩
      simp only [charge,hs,dite_true,Finset.mem_singleton] at hv
      exact ⟨⟨s,hs⟩,hv.symm⟩
    · rintro ⟨s,rfl⟩
      exact ⟨s.val,s.property,by simp [charge,s.property]⟩
  rw [hs,he] at hCap
  exact ⟨j,fun s => ⟨x s,hj s⟩,hCap⟩

theorem exact_distinct_first_exits {a k l : ℕ}
    (hAr : 1 ≤ a+(k+l))
    (hFew : descriptionBitBound (a+(k+l))+2^(k+l) < 2^(a+(k+l)))
    (hRepair : 1+lookupBankCost k l+(2*2^l+2*a+3)+5 ≤ (a+(k+l))^2)
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l))))) :
    let E := BlockChargeDichotomy.eligiblePrefixes (a := a) (d := k+l) c
    ∃ exit : E → Fin c.size,
      (∀ s : E, ∃ x, exit s ∈ downstreamReaders c.program (block (d := k+l) s.val) x ∧
        s.val ∈ nearbyTags (d := k+l) c.program (exit s)) ∧
      E.card ≤ 4*((Finset.univ : Finset E).image exit).card := by
  let m := a+(k+l)
  let p := c.program
  let w := c.outputs 0
  let E := BlockChargeDichotomy.eligiblePrefixes (a := a) (d := k+l) c
  have h0 := mcspSquare_constant_table m hAr false
  have h1 := mcspSquare_constant_table m hAr true
  have hc0 : cornerValue p false w = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true w = true := (congrFun (hc _) 0).trans h1
  have hSparse := card_accepting_mcspSquare_le m
  have hOrig := not_constant_of_sparse ((Nat.le_add_right _ _).trans_lt hFew) hSparse h0
  have hRead (s : BitString a) (hs : s ∈ E) (i : Fin (2^m))
      (hi : i ∈ block (d := k+l) s) : ∃ j : Fin c.size, ∃ b, (p.lines j).wires b = .input i := by
    have hSub : ({s} : Finset (BitString a)) ⊆ E := by
      intro u hu
      rwa [Finset.mem_singleton.mp hu]
    have hCover := BlockChargeDichotomy.eligible_covered (a := a) (d := k+l) c {s} hSub
    have hNeed : i ∈ needInputs p w false :=
      hCover ((blocks_singleton_eq (d := k+l) s).symm ▸ hi)
    obtain ⟨j,_,b,hb⟩ := need_input_has_reader hc0 hc1 hNeed
    exact ⟨j,b,hb⟩
  have hNon (s : BitString a) (_ : s ∈ E) (x : BitString (2^m)) :
      ¬∃ b : Bool, restrictedWire p (pinAt x (block (d := k+l) s)) w = fun _ => b := by
    let P := block (d := k+l) s
    let f : BooleanFunction (2^m) := fun T => mcspSquare m (substitute (pinAt x P) T)
    rw [NestedFaces.restricted_circuit_eq c hc (pinAt x P)]
    change ¬∃ b : Bool, f = fun _ => b
    have hS : (acceptingTables f).card ≤ 2^(descriptionBitBound m+2^(k+l)) := by
      have h := card_accepting_pin_le (mcspSquare m) x P
      rw [show P.card = 2^(k+l) from card_block s] at h
      calc
        _ ≤ 2^(2^(k+l))*(acceptingTables (mcspSquare m)).card := h
        _ ≤ 2^(2^(k+l))*2^descriptionBitBound m := Nat.mul_le_mul_left _ hSparse
        _ = _ := by rw [Nat.mul_comm, ← pow_add]
    have hYes : f (fun _ => false) = true := by
      have hConst : complexity interpretation (single (fun _ : BitString m => false)) ≤ 1 :=
        (Synthesis.const (s := inputs m) false).complexity_le
      have hBudget : complexity interpretation (single (fun _ : BitString m => false)) +
          lookupBankCost k l + ({s} : Finset (BitString a)).card*(2*2^l+2*a+3)+5 ≤ m^2 := by
        rw [Finset.card_singleton, Nat.one_mul]
        exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hConst _) _) _).trans hRepair
      have h := accepted_after_blocks_pin (k := k) (l := l)
        ({s} : Finset (BitString a)) x (fun _ => false) hBudget
      have he : MCSP.truthTable m (fun _ : BitString m => false) = fun _ => false := by
        funext i
        change (fun _ : BitString m => false) ((BitString.equivFin m).symm i) = false
        rfl
      rw [blocks_singleton_eq, he] at h
      exact h
    exact not_constant_of_sparse hFew hS hYes
  exact distinct_first_exits_of_single_blocks (d := k+l) p w E
    (minimum_fresh_univ c hc hMin hOrig) (minimum_live_univ c hc hMin hOrig) hRead hNon

/-- At arity 32, pooling the first-exit witnesses from separate covered
256-entry blocks certifies over two million distinct original indices. -/
theorem mcsp32_distinct_first_exits (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32))) :
    let E := BlockChargeDichotomy.eligiblePrefixes (a := 24) (d := 8) c
    ∃ exit : E → Fin c.size,
      (∀ s : E, ∃ x, exit s ∈ downstreamReaders c.program (block (d := 8) s.val) x ∧
        s.val ∈ nearbyTags (d := 8) c.program (exit s)) ∧
      2079857 ≤ ((Finset.univ : Finset E).image exit).card := by
  obtain ⟨exit,hExit,hBound⟩ := exact_distinct_first_exits (a := 24) (k := 2) (l := 6)
    (by decide) (by decide) (by decide) c hc hMin
  let E := BlockChargeDichotomy.eligiblePrefixes (a := 24) (d := 8) c
  have hEligible := BlockChargeDichotomy.eligible_prefixes_dense (a := 24) (d := 8) (by decide) c hc hMin
  have hBits : descriptionBitBound 32 = 27672 := by decide
  change 2^24 ≤ 2*E.card+5*descriptionBitBound 32 at hEligible
  change E.card ≤ 4*((Finset.univ : Finset E).image exit).card at hBound
  rw [hBits] at hEligible
  refine ⟨exit,hExit,?_⟩
  norm_num at hEligible
  omega

end Footprint

section GuardControl

variable {n : ℕ}

noncomputable def anyInput (T : BitString n) : Bool := decide (∃ i, T i = true)

private theorem any_size (n : ℕ) : complexity interpretation (single (anyInput (n := n))) ≤ n+1 := by
  have h := Synthesis.exists_mem (s := inputs n) (Finset.univ : Finset (Fin n)) (fun i (T : BitString n) => T i)
    (fun _ => 0) (fun i _ => Synthesis.of_mem ⟨i,rfl⟩)
  have h' := Synthesis.congr_iff h (g := anyInput) (fun T => by simp [anyInput])
  simpa only [Nat.zero_add, Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin,
    Nat.mul_one] using h'.complexity_le

private theorem any_not_projection (hn : 2 ≤ n) (i : Fin n) : anyInput ≠ fun T => T i := by
  intro he
  let j : Fin n := if i.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hj : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    by_cases hi : i.val = 0 <;> simp [j,hi] at hv
  let T : BitString n := fun k => decide (k = j)
  have h1 : anyInput T = true := decide_eq_true ⟨j,by simp [T]⟩
  have h0 : T i = false := by simp [T,hj]
  have he' := congrFun he T
  rw [h1,h0] at he'
  cases he'

/-- Evaluate the all-zero branch explicitly, then OR it with an equivalent
recognizer. The negation of the aggregate is originally nonconstant. It is
a downstream reader under every nonempty all-one pin set. -/
theorem equivalent_recognizer_with_shared_reader (hn : 2 ≤ n) {F : BooleanFunction n}
    (hZero : F (fun _ => false) = true) :
    ∃ c : Circuit signature n 1, c.Computes interpretation (single F) ∧
      c.size ≤ complexity interpretation (single F)+n+3 ∧
      ∃ j : Fin c.size, ∀ P : Finset (Fin n), P.Nonempty →
        j ∈ downstreamReaders c.program P (fun _ => true) := by
  obtain ⟨base,hBase,hSize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single F)
  obtain ⟨any,hAny,hAnySize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (anyInput (n := n)))
  obtain ⟨v,hv⟩ : ∃ v, any.outputs 0 = .gate v := by
    cases he : any.outputs 0 with
    | input i =>
      apply (any_not_projection hn i ?_).elim
      funext T
      have h := congrFun (hAny T) 0
      change any.program.trace interpretation T (any.outputs 0) = anyInput T at h
      rw [he, Program.trace_input] at h
      exact h.symm
    | gate v => exact ⟨v,rfl⟩
  let g := any.size+base.size
  let p : Program signature n g := any.program.append Wire.input base.program
  let first : Wire n g := .gate (v.castAdd base.size)
  let value : Wire n g := Program.appendedWire Wire.input (base.outputs 0)
  let neg : Line signature n g := ⟨.not, fun _ => first⟩
  let last : Line signature n (g+1) := ⟨.or, Fin.cases (.gate (Fin.last g)) (fun _ => value.castSucc)⟩
  let q := (p.gate neg).gate last
  let c : Circuit signature n 1 := ⟨q,fun _ => .gate (Fin.last (g+1))⟩
  have hFirst (T : BitString n) : p.trace interpretation T first = anyInput T := by
    have hh := Program.trace_append_castAdd any.program Wire.input interpretation T base.program (any.outputs 0)
    rw [hv] at hh
    have ht := congrFun (hAny T) 0
    change any.program.trace interpretation T (any.outputs 0) = anyInput T at ht
    rw [hv] at ht
    exact hh.trans ht
  have hValue (T : BitString n) : p.trace interpretation T value = F T := by
    have hh := Program.trace_append_appendedWire any.program Wire.input interpretation T base.program (base.outputs 0)
    exact hh.trans (congrFun (hBase T) 0)
  have hNeg (T : BitString n) : (p.gate neg).trace interpretation T (.gate (Fin.last g)) =
      !(anyInput T) := by
    change (p.gate neg).eval interpretation T (Fin.last g) = _
    rw [Program.eval_gate_last]
    change (!(p.trace interpretation T first)) = (!(anyInput T))
    rw [hFirst]
  have hComp : c.Computes interpretation (single F) := by
    intro T
    funext i
    change ((p.gate neg).gate last).eval interpretation T (Fin.last (g+1)) = F T
    rw [Program.eval_gate_last]
    change ((p.gate neg).trace interpretation T (.gate (Fin.last g)) ||
      (p.gate neg).trace interpretation T value.castSucc) = F T
    rw [hNeg, Program.trace_gate_castSucc, hValue]
    cases hT : anyInput T
    · have he : T = fun _ => false := by
        funext i
        cases hi : T i
        · rfl
        · have hYes : anyInput T = true := decide_eq_true ⟨i,hi⟩
          rw [hT] at hYes
          cases hYes
      simp [he,hZero]
    · simp
  have hAnyBound : any.size ≤ n+1 := hAnySize.le.trans (any_size n)
  refine ⟨c,hComp,?_,(Fin.last g).castSucc,?_⟩
  · change any.size+base.size+1+1 ≤ _
    omega
  intro P hP
  let j := (Fin.last g).castSucc
  have hLine : ∀ (b : Fin (signature.Arity (q.lines j).op)),
      (q.lines j).wires b = first.castSucc.castSucc := by
    dsimp only [j, q]
    rw [Program.lines_gate_castSucc, Program.lines_gate_last]
    intro b
    rfl
  have hNoRaw : j ∉ directReaders q P := by
    intro h
    obtain ⟨i,_,b,hb⟩ := (Finset.mem_filter.mp h).2
    rw [hLine] at hb
    cases hb
  have hC : restrictedWire q (pinAt (fun _ => true) P) first.castSucc.castSucc = fun _ => true := by
    funext T
    unfold restrictedWire
    rw [show q.trace interpretation (substitute (pinAt (fun _ => true) P) T) first.castSucc.castSucc =
      p.trace interpretation (substitute (pinAt (fun _ => true) P) T) first from
        (Program.trace_gate_castSucc _ _ _ _ _).trans (Program.trace_gate_castSucc _ _ _ _ _), hFirst]
    obtain ⟨i,hi⟩ := hP
    exact decide_eq_true ⟨i,by simp [substitute,pinAt,hi]⟩
  have hAr : signature.Arity (q.lines j).op = 1 := by
    dsimp only [q,j]
    rw [Program.lines_gate_castSucc, Program.lines_gate_last]
    rfl
  let b : Fin (signature.Arity (q.lines j).op) := ⟨0,by omega⟩
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,b,true,by rw [hLine,hC]⟩,hNoRaw⟩

end GuardControl

section SignedAndControl

set_option maxHeartbeats 800000 in
theorem signedAnd_patched_constant (r : ℕ) (hr : 10 ≤ r) (b : Bool)
    (D : Finset (Fin (2^JointOrbit.logArity r))) (hD : D.card ≤ 4) :
    GrowingAndOrbit.control r hr (PatchedCut.patch D (fun _ => b)) = true := by
  let U : JointEquality.Labels r (2^r) := fun _ => (fun _ => b, false, QuadraticForest.zeroVec _)
  have hTag (v : Bool) : AffineProbes.taggedProbe (U v) = fun _ => b := by
    funext i
    obtain ⟨⟨x,a,y⟩,rfl⟩ := (CommunicationCut.positionEquiv r (2^r)).surjective i
    change AffineProbes.taggedProbe (U v) (CommunicationCut.position x a y) = b
    rw [AffineProbes.tagged_at]
    simp [U, QuadraticForest.dot_zero_left]
  have hDiag : JointEquality.diagonal U = fun _ => b := by
    funext i
    simp [JointEquality.diagonal, JointEquality.joinBlocks, MCSP.truthTable_apply, hTag]
  obtain ⟨h,hh⟩ := JointEquality.log_stage r hr
  have hTable : JointOrbit.rotated 0 (JointEquality.mixed h U U) =
      (fun _ => b) := by
    rw [JointEquality.mixed_eq_splice, CommunicationCut.splice_self, hDiag]
    funext i
    rfl
  rw [← hTable]
  exact (GrowingAndOrbit.control_original_tests r hr hh 0 U U D hD).mpr rfl

theorem signedAnd_constant (r : ℕ) (hr : 10 ≤ r) (b : Bool) :
    GrowingAndOrbit.control r hr (fun _ => b) = true := by
  have h := signedAnd_patched_constant r hr b ∅ (by simp)
  have he : PatchedCut.patch ∅ (fun _ : Fin (2^JointOrbit.logArity r) => b) = fun _ => b := by
    funext i
    simp [PatchedCut.patch]
  rwa [he] at h

private theorem description_lt_half {m : ℕ} (hm : 1024 ≤ m) :
    descriptionBitBound m < 2^(m-1) := by
  let n := m-1
  have hn : m ≤ 2*n := by dsimp [n]; omega
  have hP : descriptionBitBound m ≤ 5*m^3 := calc
    _ ≤ (4*m+12)*m^2 := QuadraticPinning.description_le_polynomial m (by omega)
    _ ≤ (5*m)*m^2 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have hS : 5*m^3 ≤ 40*n^3 := calc
    _ ≤ 5*(2*n)^3 := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hn 3)
    _ = _ := by ring
  have hL : 40*n^3 < n^4 := by
    rw [pow_succ' n 3]
    exact Nat.mul_lt_mul_of_pos_right (by dsimp [n]; omega) (Nat.pow_pos (by dsimp [n]; omega))
  exact (hP.trans hS).trans_lt (hL.trans_le (GrowingPrefix.four_power_le_exp n (by dsimp [n]; omega)))

/-- The same signed-AND recognizer has an implementation in which one
original downstream gate is lost under every nonempty all-one pin set
of at most half the entries. Every such restriction leaves the output
nonconstant. -/
theorem signedAnd_control_shared_reader (r : ℕ) (hr : 10 ≤ r) :
    let m := JointOrbit.logArity r
    ∃ c : Circuit signature (2^m) 1,
      c.Computes interpretation (single (GrowingAndOrbit.control r hr)) ∧
      c.size ≤ 5104*(r+1)*2^m ∧
      ∃ j : Fin c.size, ∀ P : Finset (Fin (2^m)), P.Nonempty → P.card ≤ 2^(m-1) →
        j ∈ downstreamReaders c.program P (fun _ => true) ∧
        ¬∃ b : Bool, restrictedWire c.program (pinAt (fun _ => true) P) (c.outputs 0) = fun _ => b := by
  let m := JointOrbit.logArity r
  let F := GrowingAndOrbit.control r hr
  have hm : 1024 ≤ m := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans
    (by dsimp [m,JointOrbit.logArity,JointOrbit.Arity]; omega)
  have hN : 2 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 1 ≤ m by omega)
  obtain ⟨c,hc,hSize,j,hRead⟩ := equivalent_recognizer_with_shared_reader hN (signedAnd_constant r hr false)
  refine ⟨c,hc,?_,j,fun P hP hHalf => ⟨hRead P hP,?_⟩⟩
  · have hBase := GrowingAndOrbit.control_size r hr
    change complexity interpretation (single F) ≤ 5100*(r+1)*2^m at hBase
    change c.size ≤ complexity interpretation (single F)+2^m+3 at hSize
    refine hSize.trans ?_
    have hN' : (2^m)+3 ≤ 4*(2^m) := by omega
    calc
      _ ≤ 5100*(r+1)*2^m+(2^m+3) := by omega
      _ ≤ 5100*(r+1)*2^m+4*(2^m) := Nat.add_le_add_left hN' _
      _ ≤ 5100*(r+1)*2^m+(4*(r+1))*2^m := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
      _ = _ := by ring
  rw [NestedFaces.restricted_circuit_eq c hc (pinAt (fun _ => true) P)]
  let f : BooleanFunction (2^m) := fun T => F (substitute (pinAt (fun _ => true) P) T)
  have hYes : f (fun _ => true) = true := by
    have he : substitute (pinAt (fun _ => true) P) (fun _ => true) = fun _ => true := by
      funext i
      by_cases hi : i ∈ P <;> simp [substitute,pinAt,hi]
    change F (substitute (pinAt (fun _ => true) P) (fun _ => true)) = _
    rw [he]
    exact signedAnd_constant r hr true
  have hSparse : (acceptingTables f).card ≤ 2^(P.card+descriptionBitBound m) := calc
    _ ≤ 2^P.card*(acceptingTables F).card := card_accepting_pin_le F _ P
    _ ≤ 2^P.card*2^descriptionBitBound m :=
      Nat.mul_le_mul_left _ (GrowingAndOrbit.control_sparse r hr)
    _ = _ := (pow_add ..).symm
  have hFew : P.card+descriptionBitBound m < 2^m := by
    change P.card ≤ 2^(m-1) at hHalf
    have h := description_lt_half hm
    have hPow : 2*2^(m-1) = 2^m := calc
      _ = 2^(m-1+1) := (pow_succ' 2 (m-1)).symm
      _ = _ := by rw [Nat.sub_add_cancel (show 1 ≤ m by omega)]
    omega
  change ¬∃ b : Bool, f = fun _ => b
  rintro ⟨b,he⟩
  have hb : b = true := (congrFun he (fun _ => true)).symm.trans hYes
  rw [he,hb] at hSparse
  simp only [acceptingTables, Finset.filter_true, Finset.card_univ, BitString.card] at hSparse
  exact (not_le_of_gt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hFew)) hSparse

end SignedAndControl

#print axioms sum_cards_eq_sum_multiplicity
#print axioms card_first_footprint
#print axioms card_second_footprint
#print axioms first_exit_incidence_bound
#print axioms second_exit_incidence_bound
#print axioms tighter_separated_pool
#print axioms mcsp32_distinct_first_exits
#print axioms signedAnd_control_shared_reader

end PvsNP.Frontier.ChargeMultiplicity
