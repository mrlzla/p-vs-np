module

public import MCSPDownstreamBlockPinning

/-! Select blocks using the input labels of the original gates and their
predecessors. The same labels certify that different blocks have different
downstream exits. -/

@[expose] public section

namespace PvsNP.Frontier.IndependentBlockPinning

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure ForestPinning ForestBlockPinning
open RestrictionCharges FreshCharges NestedFaces QuadraticForest QuadraticPinning SuperTwoN
open MultiBlockPinning DownstreamBlockPinning
open scoped Classical BigOperators

section Conflicts

variable {a d g : ℕ}

/-- The prefix labels of the raw inputs of this gate. -/
noncomputable def readerTags (p : Program signature (2^(a+d)) g) (j : Fin g) :
    Finset (BitString a) :=
  Finset.univ.biUnion (fun b =>
    match (p.lines j).wires b with
    | .input i => {tag i}
    | .gate _ => ∅)

/-- The tags read by this gate or by a gate immediately supplying it. -/
noncomputable def nearbyTags (p : Program signature (2^(a+d)) g) (j : Fin g) :
    Finset (BitString a) :=
  readerTags p j ∪ Finset.univ.biUnion (fun b =>
    match (p.lines j).wires b with
    | .input _ => ∅
    | .gate u => readerTags p u)

theorem mem_readerTags {p : Program signature (2^(a+d)) g} {j : Fin g} {s : BitString a} :
    s ∈ readerTags p j ↔ j ∈ directReaders p (block (d := d) s) := by
  constructor
  · intro h
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp h
    cases he : (p.lines j).wires b with
    | input i =>
      rw [he] at hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_singleton.mp hb).symm⟩, b, he⟩
    | gate i => simp [he] at hb
  · intro h
    obtain ⟨i, hi, b, hb⟩ := (Finset.mem_filter.mp h).2
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, by
      rw [hb]
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hi).2.symm⟩

theorem readerTags_subset_nearby (p : Program signature (2^(a+d)) g) (j : Fin g) :
    readerTags p j ⊆ nearbyTags p j := Finset.subset_union_left

theorem readerTags_subset_nearby_of_wire (p : Program signature (2^(a+d)) g) {j u : Fin g}
    {b : Fin (signature.Arity (p.lines j).op)} (h : (p.lines j).wires b = .gate u) :
    readerTags p u ⊆ nearbyTags p j := by
  intro s hs
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, by simpa only [h] using hs⟩

theorem card_readerTags_le (p : Program signature (2^(a+d)) g) (j : Fin g) :
    (readerTags p j).card ≤ 2 := by
  let f (b : Fin (signature.Arity (p.lines j).op)) : Finset (BitString a) :=
    match (p.lines j).wires b with | .input i => {tag i} | .gate _ => ∅
  calc
    _ ≤ ∑ b, (f b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : Fin (signature.Arity (p.lines j).op), 1 := Finset.sum_le_sum (fun b _ => by
      cases he : (p.lines j).wires b <;> simp [f, he])
    _ ≤ _ := by
      simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.mul_one]
        using (Program.fanInAtMost_iff.mp p.fanInAtMost_two j)

theorem card_nearbyTags_le (p : Program signature (2^(a+d)) g) (j : Fin g) :
    (nearbyTags p j).card ≤ 6 := by
  let f (b : Fin (signature.Arity (p.lines j).op)) :=
    match (p.lines j).wires b with | .input _ => ∅ | .gate u => readerTags p u
  have hEach (b) : (f b).card ≤ 2 := by
    cases he : (p.lines j).wires b with
    | input i => simp [f, he]
    | gate u => simpa only [f, he] using card_readerTags_le p u
  have hSum : (Finset.univ.biUnion f).card ≤ 4 := calc
    _ ≤ ∑ b, (f b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b : Fin (signature.Arity (p.lines j).op), 2 :=
      Finset.sum_le_sum (fun b _ => hEach b)
    _ ≤ _ := by
      simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin]
      exact Nat.mul_le_mul_right 2 (Program.fanInAtMost_iff.mp p.fanInAtMost_two j)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (card_readerTags_le p j) hSum)

/-- Distinct selected blocks may never occur together in one gate footprint. -/
def SeparatedBy (tags : Fin g → Finset (BitString a)) (E : Finset (BitString a)) : Prop :=
  ∀ u ∈ E, ∀ v ∈ E, u ≠ v → ∀ j : Fin g, u ∈ tags j → v ∉ tags j

def Separated (p : Program signature (2^(a+d)) g) (E : Finset (BitString a)) : Prop :=
  SeparatedBy (nearbyTags p) E

private noncomputable def occurrences (tags : Fin g → Finset (BitString a))
    (s : BitString a) : Finset (Fin g) :=
  Finset.univ.filter fun j => s ∈ tags j

private theorem sum_occurrences_le (tags : Fin g → Finset (BitString a)) {w : ℕ}
    (hTags : ∀ j, (tags j).card ≤ w) :
    (∑ s : BitString a, (occurrences tags s).card) ≤ w*g := calc
  _ = ∑ s : BitString a, ∑ j : Fin g, (if s ∈ tags j then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_filter]
    simp [occurrences]
  _ = ∑ j : Fin g, ∑ s : BitString a, (if s ∈ tags j then 1 else 0) := Finset.sum_comm
  _ = ∑ j : Fin g, (tags j).card := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_filter]
    simp
  _ ≤ ∑ _j : Fin g, w := Finset.sum_le_sum fun j _ => hTags j
  _ = _ := by simp [Nat.mul_comm]

private noncomputable def closedNeighbors (tags : Fin g → Finset (BitString a))
    (s : BitString a) : Finset (BitString a) :=
  insert s ((occurrences tags s).biUnion tags)

private theorem card_closedNeighbors_le (tags : Fin g → Finset (BitString a)) {w : ℕ}
    (hTags : ∀ j, (tags j).card ≤ w) (s : BitString a) {K : ℕ} (hK : (occurrences tags s).card ≤ K) :
    (closedNeighbors tags s).card ≤ w*K+1 := by
  have h : ((occurrences tags s).biUnion tags).card ≤ w*K := calc
    _ ≤ ∑ j ∈ occurrences tags s, (tags j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ occurrences tags s, w := Finset.sum_le_sum fun j _ => hTags j
    _ ≤ _ := by simpa [Nat.mul_comm] using Nat.mul_le_mul_left w hK
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right h 1)

private theorem choose_separated (tags : Fin g → Finset (BitString a)) {w : ℕ}
    (hTags : ∀ j, (tags j).card ≤ w)
    (S : Finset (BitString a)) (r K : ℕ) (hS : r*(w*K+1) ≤ S.card)
    (hLight : ∀ s ∈ S, (occurrences tags s).card ≤ K) :
    ∃ E ⊆ S, E.card = r ∧ SeparatedBy tags E := by
  induction r generalizing S with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp [SeparatedBy]⟩
  | succ r ih =>
    have hRoom := hS
    rw [Nat.succ_mul] at hRoom
    obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    let T := S \ closedNeighbors tags s
    have hN := card_closedNeighbors_le tags hTags s (hLight s hs)
    have hCard : r*(w*K+1) ≤ T.card := by
      have h := Finset.card_sdiff_add_card_eq_card
        (Finset.inter_subset_left (s₁ := S) (s₂ := closedNeighbors tags s))
      have hSub := Finset.card_le_card
        (Finset.inter_subset_right (s₁ := S) (s₂ := closedNeighbors tags s))
      have he : S \ (S ∩ closedNeighbors tags s) = T := by
        ext u
        simp [T]
      rw [he] at h
      omega
    obtain ⟨E, hE, hEc, hSep⟩ := ih T hCard (fun u hu => hLight u (Finset.mem_sdiff.mp hu).1)
    have hNot : s ∉ E := fun h => (Finset.mem_sdiff.mp (hE h)).2 (Finset.mem_insert_self ..)
    have hSide (u : BitString a) (hu : u ∈ E) (j : Fin g) (hsj : s ∈ tags j) :
        u ∉ tags j := fun huj =>
      (Finset.mem_sdiff.mp (hE hu)).2 (Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsj⟩, huj⟩))
    refine ⟨insert s E, ?_, by rw [Finset.card_insert_of_notMem hNot, hEc], ?_⟩
    · intro u hu
      rcases Finset.mem_insert.mp hu with he | hu
      · exact he.symm ▸ hs
      · exact (Finset.mem_sdiff.mp (hE hu)).1
    intro u hu v hv hne j hj hV
    rcases Finset.mem_insert.mp hu with heu | huE
    · subst u
      rcases Finset.mem_insert.mp hv with hev | hvE
      · exact hne hev.symm
      · exact hSide v hvE j hj hV
    · rcases Finset.mem_insert.mp hv with hev | hvE
      · subst v
        exact hSide u huE j hV hj
      · exact hSep u huE v hvE hne j hj hV

/-- Choose separated tags from an explicitly eligible pool. -/
theorem exists_separated_subset_by (tags : Fin g → Finset (BitString a)) {w : ℕ}
    (hTags : ∀ j, (tags j).card ≤ w)
    (S : Finset (BitString a)) (r K H : ℕ)
    (hHeavy : w*g < K*(H+1))
    (hRoom : r*(w*K+1) + H ≤ S.card) :
    ∃ E ⊆ S, E.card = r ∧ SeparatedBy tags E := by
  let heavy := Finset.univ.filter fun s => K < (occurrences tags s).card
  have hHeavySum : K*heavy.card ≤ w*g := calc
    _ = ∑ _s ∈ heavy, K := by simp [Nat.mul_comm]
    _ ≤ ∑ s ∈ heavy, (occurrences tags s).card := Finset.sum_le_sum fun s hs =>
      (Finset.mem_filter.mp hs).2.le
    _ ≤ ∑ s : BitString a, (occurrences tags s).card :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ ≤ _ := sum_occurrences_le tags hTags
  have hH : heavy.card ≤ H := by
    by_contra! h
    exact (not_le_of_gt hHeavy) ((Nat.mul_le_mul_left K h).trans hHeavySum)
  let good := S \ heavy
  have hPart := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_left (s₁ := S) (s₂ := heavy))
  have hPart' : good.card + (S ∩ heavy).card = S.card := by
    have hEq : S \ (S ∩ heavy) = good := by ext s; simp [good]
    rwa [hEq] at hPart
  have hInt := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := heavy))
  have hEnough : r*(w*K+1) ≤ good.card := by omega
  obtain ⟨E, hE, hc, hd⟩ := choose_separated tags hTags good r K hEnough (fun s hs => by
    by_contra! h
    exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  exact ⟨E, hE.trans Finset.sdiff_subset, hc, hd⟩

/-- Discard prefixes with missing addresses before applying the selector. -/
theorem exists_separated_covered_blocks_by (tags : Fin g → Finset (BitString a)) {w : ℕ}
    (hTags : ∀ j, (tags j).card ≤ w)
    (S : Finset (Fin (2^(a+d)))) (r K H : ℕ)
    (hHeavy : w*g < K*(H+1))
    (hRoom : r*(w*K+1) + H + ((Finset.univ : Finset _) \ S).card ≤ 2^a) :
    ∃ E : Finset (BitString a), E.card = r ∧ SeparatedBy tags E ∧ blocks (d := d) E ⊆ S := by
  let missing := ((Finset.univ : Finset _) \ S).image tag
  let good := Finset.univ \ missing
  have hM : missing.card ≤ ((Finset.univ : Finset _) \ S).card := Finset.card_image_le
  have hGood := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ missing)
  rw [Finset.card_univ, BitString.card] at hGood
  change good.card + missing.card = 2^a at hGood
  have hEnough : r*(w*K+1) + H ≤ good.card := by omega
  obtain ⟨E, hE, hc, hd⟩ := exists_separated_subset_by tags hTags good r K H hHeavy hEnough
  refine ⟨E, hc, hd, ?_⟩
  intro i hi
  by_contra h
  exact (Finset.mem_sdiff.mp (hE (Finset.mem_filter.mp hi).2)).2
    (Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩)

theorem exists_separated_covered_blocks (p : Program signature (2^(a+d)) g)
    (S : Finset (Fin (2^(a+d)))) (r K H : ℕ)
    (hHeavy : 6*g < K*(H+1))
    (hRoom : r*(6*K+1) + H + ((Finset.univ : Finset _) \ S).card ≤ 2^a) :
    ∃ E : Finset (BitString a), E.card = r ∧ Separated p E ∧ blocks (d := d) E ⊆ S :=
  exists_separated_covered_blocks_by (nearbyTags p) (card_nearbyTags_le p) S r K H hHeavy hRoom

end Conflicts

section Exits

variable {a d g : ℕ}

theorem has_exit_of_constant_reader (p : Program signature (2^(a+d)) g)
    (root : Wire (2^(a+d)) g) (E : Finset (BitString a)) (x : BitString (2^(a+d)))
    (hSep : Separated p E) (hFresh : fresh p Sum.inl = Finset.univ)
    (hNon : ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b)
    (s : BitString a) (hs : s ∈ E)
    {j : Fin g} (hj : ResidualLive p Sum.inl root j) (hTag : s ∈ readerTags p j)
    (hConst : ∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) (.gate j) = fun _ => b) :
    ∃ u ∈ downstreamReaders p (blocks (d := d) E) x, s ∈ nearbyTags p u := by
  let P := blocks (d := d) E
  let ρ := pinAt x P
  by_contra hNo
  have hAbsent {u : Fin g} (h : ResidualLive p Sum.inl root u) :
      s ∈ readerTags p u → ¬∃ b : Bool, restrictedWire p ρ (.gate u) = fun _ => b := by
    induction h with
    | @output u hRep =>
      intro _
      have he := original_represents_gate hFresh hRep
      simpa only [he] using hNon
    | @argument u v hLive i hRep ih =>
      intro hv
      rintro ⟨b, hb⟩
      have he := original_represents_gate hFresh hRep
      have hsU : s ∈ nearbyTags p u := readerTags_subset_nearby_of_wire p he hv
      have hArg : restrictedWire p ρ ((p.lines u).wires i) = fun _ => b := he ▸ hb
      have hConstU : u ∈ constantReaders p ρ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, b, hArg⟩
      have hDirect : u ∈ directReaders p P := by
        by_contra h
        exact hNo ⟨u, Finset.mem_sdiff.mpr ⟨hConstU, h⟩, hsU⟩
      obtain ⟨z, hz, k, hk⟩ := (Finset.mem_filter.mp hDirect).2
      have hzE : tag z ∈ E := (Finset.mem_filter.mp hz).2
      have hzTag : tag z ∈ readerTags p u := mem_readerTags.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, z,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, k, hk⟩)
      have hzEq : s = tag z := by
        by_contra hn
        exact hSep s hs _ hzE hn u hsU (readerTags_subset_nearby p u hzTag)
      have hn : i ≠ k := by
        intro e
        rw [e, hk] at he
        cases he
      exact ih (hzEq ▸ hzTag) (constant_of_two_arguments p ρ u i k hn b (x z)
        hArg (hk ▸ pin_input_constant p x hz))
  exact hAbsent hj hTag hConst

/-- Use a separate controlling bit in each block, then assign its first
downstream exit. The footprint separation makes this assignment injective. -/
theorem exists_matched_exits (p : Program signature (2^(a+d)) g) (root : Wire (2^(a+d)) g)
    (E : Finset (BitString a)) (hSep : Separated p E)
    (hFresh : fresh p Sum.inl = Finset.univ)
    (hLive : liveFresh p Sum.inl root = Finset.univ)
    (hRead : ∀ i ∈ blocks (d := d) E, ∃ j : Fin g, ∃ k, (p.lines j).wires k = .input i)
    (hNon : ∀ x : BitString (2^(a+d)),
      ¬∃ b : Bool, restrictedWire p (pinAt x (blocks (d := d) E)) root = fun _ => b) :
    ∃ (x : BitString (2^(a+d))) (exit : E ↪ downstreamReaders p (blocks (d := d) E) x),
      ∀ s : E, s.val ∈ nearbyTags p (exit s).val := by
  let P := blocks (d := d) E
  have seed (s : E) : ∃ (v : Bool) (j : Fin g),
      s.val ∈ readerTags p j ∧
      ∀ x : BitString (2^(a+d)), (∀ i ∈ block (d := d) s.val, x i = v) →
        ∃ b : Bool, restrictedWire p (pinAt x P) (.gate j) = fun _ => b := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [card_block]; exact Nat.two_pow_pos _ :
      0 < (block (d := d) s.val).card)
    have he : tag i = s.val := (Finset.mem_filter.mp hi).2
    have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ s.property⟩
    obtain ⟨j, q, hq⟩ := hRead i hiP
    obtain ⟨v, b, hb⟩ := op_can_force_constant (p.lines j).op q
    refine ⟨v, j, mem_readerTags.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, q, hq⟩), ?_⟩
    intro x hx
    refine ⟨b, funext fun z => ?_⟩
    have hA : restrictedWire p (pinAt x P) ((p.lines j).wires q) = fun _ => v := by
      rw [hq, pin_input_constant p x hiP, hx i hi]
    unfold restrictedWire
    rw [p.trace_gate]
    exact hb _ (congrFun hA z)
  choose bit start hTag hStart using seed
  let x (i : Fin (2^(a+d))) : Bool :=
    if h : tag i ∈ E then bit ⟨tag i, h⟩ else false
  have exitExists (s : E) : ∃ u ∈ downstreamReaders p P x, s.val ∈ nearbyTags p u := by
    apply has_exit_of_constant_reader p root E x hSep hFresh (hNon x) s.val s.property
      (mem_liveFresh_iff.mp (hLive.symm ▸ Finset.mem_univ (start s))) (hTag s)
    apply hStart s
    intro i hi
    have he : tag i = s.val := (Finset.mem_filter.mp hi).2
    simp only [x, he, s.property, dite_true]
  choose target hTarget hNear using exitExists
  let into (s : E) : downstreamReaders p P x := ⟨target s, hTarget s⟩
  have hInj : Function.Injective into := by
    intro s q h
    apply Subtype.ext
    by_contra hn
    have he : target s = target q := congrArg Subtype.val h
    exact hSep s.val s.property q.val q.property hn (target s) (hNear s) (he.symm ▸ hNear q)
  exact ⟨x, ⟨into, hInj⟩, hNear⟩

end Exits

section ExactMCSP

variable {a k l r K H reserve : ℕ}

/-- Pick separated blocks in a minimum exact-MCSP circuit and count their
distinct original exits in addition to the direct readers. -/
theorem original_separated_block_exits
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l)))))
    (hr : 0 < r) (hm : 1 ≤ a+(k+l))
    (hHeavy : 6*c.size < K*(H+1))
    (hRoom : r*(6*K+1) + H + descriptionBitBound (a+(k+l)) ≤ 2^a)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (hReserve : reserve ≤ descriptionBitBound (a+(k+l)))
    (hFactorial : 2^(r*2^(k+l)+reserve) ≤ ((a+(k+l))^2).factorial) :
    ∃ (E : Finset (BitString a)) (x : BitString (2^(a+(k+l)))),
      E.card = r ∧ Separated c.program E ∧
      let P := blocks (d := k+l) E
      let f : BooleanFunction (2^(a+(k+l))) := fun y => mcspSquare (a+(k+l)) (substitute (pinAt x P) y)
      Nonempty (E ↪ downstreamReaders c.program P x) ∧
      r*2^(k+l) ≤ 2*(directReaders c.program P).card ∧
      (280*(2*2^(a+(k+l))) + 2*2^(a+(k+l)) ≤
        280*(complexity interpretation (single f) + 2*(descriptionBitBound (a+(k+l))-reserve) + 1) +
          17*(descriptionBitBound (a+(k+l))-reserve)) ∧
      complexity interpretation (single f) + (directReaders c.program P).card +
        (downstreamReaders c.program P x).card +
        (deadFresh c.program (pinAt x P) (c.outputs 0)).card ≤ c.size := by
  let p := c.program
  let root := c.outputs 0
  let m := a+(k+l)
  let S := needInputs p root false
  let B := descriptionBitBound m
  have hStrict : B < 2^a := by
    have hp := Nat.mul_pos hr (by omega : 0 < 6*K+1)
    change r*(6*K+1) + H + B ≤ 2^a at hRoom
    omega
  have hFew : B < 2^m := hStrict.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right a (k+l)))
  have hSparse : (acceptingTables (mcspSquare m)).card ≤ 2^B := card_accepting_mcspSquare_le m
  have h0 := mcspSquare_constant_table m hm false
  have h1 := mcspSquare_constant_table m hm true
  have hc0 : cornerValue p false root = true := (congrFun (hc _) 0).trans h0
  have hc1 : cornerValue p true root = true := (congrFun (hc _) 0).trans h1
  have hNeed : 2^m ≤ S.card+B := card_needInputs_ge_of_sparse c hc hSparse false h0
  have hMiss := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hMiss
  obtain ⟨E, hE, hSep, hCover⟩ := exists_separated_covered_blocks p S r K H hHeavy (by
    dsimp only [m, B] at hNeed hMiss
    omega)
  let P := blocks (d := k+l) E
  have hP : P.card = r*2^(k+l) := (card_blocks E).trans (by rw [hE])
  let f (x : BitString (2^m)) : BooleanFunction (2^m) :=
    fun y => mcspSquare m (substitute (pinAt x P) y)
  have hResid (x : BitString (2^m)) : (acceptingTables (f x)).card ≤ 2^(B-reserve) :=
    padded_sparsity_of_factorial x P hReserve (by rwa [hP])
  have hQ (x : BitString (2^m)) (u : BitString m) (v : Bool) (c₁ c₂ : BitString m) :
      f x (MCSP.truthTable m (quad u v c₁ c₂)) = true := by
    apply accepted_after_blocks_pin (k := k) (l := l)
    have hCost := complexity_quad_shared_le u v c₁ c₂
    dsimp only [m] at hCost
    rw [hE]
    omega
  have hZero (x : BitString (2^m)) : f x (fun _ => false) = true := by
    have h := hQ x (zeroVec m) false (zeroVec m) (zeroVec m)
    have he : MCSP.truthTable m (quad (zeroVec m) false (zeroVec m) (zeroVec m)) = fun _ => false := by
      funext i
      simp only [MCSP.truthTable_apply, quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    rwa [he] at h
  have hInitNon := not_constant_of_sparse hFew hSparse h0
  have hFresh := minimum_fresh_univ c hc hMin hInitNon
  have hLive := minimum_live_univ c hc hMin hInitNon
  have hEq (x : BitString (2^m)) : restrictedWire p (pinAt x P) root = f x :=
    restricted_circuit_eq c hc (pinAt x P)
  have hNon (x : BitString (2^m)) : ¬∃ b : Bool, restrictedWire p (pinAt x P) root = fun _ => b := by
    rw [hEq]
    exact not_constant_of_sparse ((Nat.sub_le B reserve).trans_lt hFew) (hResid x) (hZero x)
  have hRead (i) (hi : i ∈ P) : ∃ j : Fin c.size, ∃ b, (p.lines j).wires b = .input i := by
    obtain ⟨j, _, b, hb⟩ := need_input_has_reader hc0 hc1 (hCover hi)
    exact ⟨j, b, hb⟩
  obtain ⟨x, e, he⟩ := exists_matched_exits p root E hSep hFresh hLive hRead hNon
  have hD := directReader_charge_of_coverage p P P x (by rfl) hFresh hRead
  rw [hP] at hD
  have hForest := quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding (hResid x) (hQ x)
  have hCost := original_reader_and_dead_budget p root P x (hNon x)
  rw [hEq x] at hCost
  exact ⟨E, x, hE, hSep, ⟨e⟩, hD, hForest, hCost⟩

theorem circuit_size_separated_blocks
    (c : Circuit signature (2^(a+(k+l))) 1)
    (hc : c.Computes interpretation (single (mcspSquare (a+(k+l)))))
    (hMin : c.size = complexity interpretation (single (mcspSquare (a+(k+l)))))
    (hr : 0 < r) (hd : 1 ≤ k+l) (hm : 1 ≤ a+(k+l))
    (hHeavy : 6*c.size < K*(H+1))
    (hRoom : r*(6*K+1) + H + descriptionBitBound (a+(k+l)) ≤ 2^a)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (hReserve : reserve ≤ descriptionBitBound (a+(k+l)))
    (hFactorial : 2^(r*2^(k+l)+reserve) ≤ ((a+(k+l))^2).factorial) :
    280*(2*2^(a+(k+l)) + r*2^(k+l-1) + r) + 2*2^(a+(k+l)) ≤
      280*(c.size + 2*(descriptionBitBound (a+(k+l))-reserve) + 1) +
        17*(descriptionBitBound (a+(k+l))-reserve) := by
  obtain ⟨E, x, hE, _, ⟨exits⟩, hD, hForest, hCost⟩ :=
    original_separated_block_exits c hc hMin hr hm hHeavy hRoom hRepair hReserve hFactorial
  have hExit := Fintype.card_le_of_injective exits exits.injective
  simp only [Fintype.card_coe, hE] at hExit
  have hp : r*2^(k+l) = 2*(r*2^(k+l-1)) := calc
    _ = r*2^(k+l-1+1) := by rw [Nat.sub_add_cancel hd]
    _ = _ := by rw [pow_succ']; ring
  rw [hp] at hD
  omega

theorem mcspSquare_separated_blocks_of_small_size
    (hr : 0 < r) (hd : 1 ≤ k+l) (hm : 1 ≤ a+(k+l))
    (hHeavy : 6*complexity interpretation (single (mcspSquare (a+(k+l)))) < K*(H+1))
    (hRoom : r*(6*K+1) + H + descriptionBitBound (a+(k+l)) ≤ 2^a)
    (hRepair : 4*(a+(k+l)) + 48 + lookupBankCost k l +
      r*(2*2^l+2*a+3) ≤ (a+(k+l))^2)
    (hReserve : reserve ≤ descriptionBitBound (a+(k+l)))
    (hFactorial : 2^(r*2^(k+l)+reserve) ≤ ((a+(k+l))^2).factorial) :
    280*(2*2^(a+(k+l)) + r*2^(k+l-1) + r) + 2*2^(a+(k+l)) ≤
      280*(complexity interpretation (single (mcspSquare (a+(k+l)))) +
        2*(descriptionBitBound (a+(k+l))-reserve) + 1) + 17*(descriptionBitBound (a+(k+l))-reserve) := by
  obtain ⟨c, hc, hMin⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare (a+(k+l))))
  have h := circuit_size_separated_blocks c hc hMin hr hd hm (hMin ▸ hHeavy)
    hRoom hRepair hReserve hFactorial
  rwa [hMin] at h

/-- The three-block proof at arity 32 now charges three distinct exits. -/
theorem mcspSquare_32_separated_blocks :
    8620564205 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hMin⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  suffices h : 8620564205 ≤ c.size by rwa [← hMin]
  by_contra! hSmall
  have h := circuit_size_separated_blocks (a := 24) (k := 2) (l := 6) (r := 3)
    (K := 16384) (H := 8388608) (reserve := 3840) c hc hMin
    (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by decide)
    (by
      rw [show (3:ℕ)*2^(2+6)+3840 = 4608 by decide]
      exact factorial_room_32)
  rw [show descriptionBitBound (24+(2+6)) = 27672 by decide] at h
  norm_num at h
  omega

end ExactMCSP

section Scaling

/-- Use one quarter as many blocks as there are represented variables. -/
def separatedBlockCount (t : ℕ) : ℕ := 2^(2*t-2)

theorem four_mul_separatedBlockCount (t : ℕ) (ht : 8 ≤ t) :
    4*separatedBlockCount t = multiBlockArity t := by
  unfold separatedBlockCount multiBlockArity
  rw [show (4:ℕ) = 2^2 by decide, ← pow_add, show 2+(2*t-2) = 2*t by omega]

theorem separated_rows (t : ℕ) (ht : 8 ≤ t) :
    4*(separatedBlockCount t*2^(2*t)) = (multiBlockArity t)^2 := calc
  _ = 2^(2+(2*t-2+(2*t))) := by
    unfold separatedBlockCount
    rw [show (4:ℕ)=2^2 by decide, ← pow_add, ← pow_add]
  _ = 2^((2*t)*2) := congrArg (fun n : ℕ => 2^n) (by omega)
  _ = _ := pow_mul _ _ _

theorem same_direct_charge (t : ℕ) (ht : 8 ≤ t) :
    separatedBlockCount t * 2^(t.log2+(2*t)-1) = multiBlockLoss t := by
  unfold separatedBlockCount multiBlockLoss
  rw [← pow_add, ← pow_add]
  congr 1
  omega

theorem two_mul_multiBlockLoss (t : ℕ) (ht : 8 ≤ t) :
    2*multiBlockLoss t = separatedBlockCount t*2^(t.log2+(2*t)) := by
  have h : 1 ≤ t.log2+(2*t) := by omega
  rw [← same_direct_charge t ht,
    show 2*(separatedBlockCount t*2^(t.log2+(2*t)-1)) =
      separatedBlockCount t*(2*2^(t.log2+(2*t)-1)) by ring,
    ← pow_succ', Nat.sub_add_cancel h]

theorem growing_conflict_budget (t : ℕ) (ht : 8 ≤ t) :
    let m := multiBlockArity t
    let k := t.log2
    let l := 2*t
    let d := k+l
    let a := m-d
    let r := separatedBlockCount t
    let K := 64*2^d
    let H := 2^(a-1)
    d ≤ m ∧ 1 ≤ a ∧ r*(6*K+1)+H+descriptionBitBound m ≤ 2^a ∧
      4*m+48+lookupBankCost k l+r*(2*2^l+2*a+3) ≤ m^2 ∧
      2*(multiBlockLoss t + r) ≤ 2^m := by
  let m := multiBlockArity t
  let k := t.log2
  let l := 2*t
  let d := k+l
  let a := m-d
  let r := separatedBlockCount t
  let L := (2:ℕ)^d
  let K := 64*L
  let H := (2:ℕ)^(a-1)
  change d ≤ m ∧ 1 ≤ a ∧ r*(6*K+1)+H+descriptionBitBound m ≤ 2^a ∧
    4*m+48+lookupBankCost k l+r*(2*2^l+2*a+3) ≤ m^2 ∧
    2*(multiBlockLoss t + r) ≤ 2^m
  have hR : 256 ≤ (2:ℕ)^t := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ht
  have hM : m = 2^t*2^t := by
    dsimp only [m, multiBlockArity]
    rw [show 2*t = t+t by omega, pow_add]
  have hm : 65536 ≤ m := hM ▸ Nat.mul_le_mul hR hR
  have htr : t ≤ (2:ℕ)^t := t.lt_two_pow_self.le
  have hBaseM : (2:ℕ)^t ≤ m := by
    simpa only [Nat.mul_one, ← hM] using Nat.mul_le_mul_left (2^t) (by omega : 1 ≤ (2:ℕ)^t)
  have hr : 4*r = m := four_mul_separatedBlockCount t ht
  have hrm : r ≤ m := by omega
  have hd : 2*d+2 ≤ m := calc
    _ ≤ 10*2^t := by
      have hk := Nat.log2_le_self t
      dsimp only [d, k, l]
      omega
    _ ≤ 2^t*2^t := Nat.mul_le_mul_right (2^t) (by omega)
    _ = _ := hM.symm
  have ha : 1 ≤ a := by dsimp only [a]; omega
  have hHalf : m ≤ 2*(a-1) := by dsimp only [a]; omega
  have hA : 32768 ≤ a-1 := by omega
  have hM3 : m ≤ m^3 := calc
    _ = m*1 := by simp
    _ ≤ m*m^2 := Nat.mul_le_mul_left _ (Nat.pow_pos (by omega))
    _ = _ := by ring
  have hRows : 4*(r*2^l) = m^2 := separated_rows t ht
  have hK : 2^k ≤ t := Nat.log2_self_le (by omega : t ≠ 0)
  have hRL : r*L ≤ m^3 := calc
    _ = (r*2^l)*2^k := by dsimp only [L, d]; rw [pow_add]; ring
    _ ≤ m^2*m := Nat.mul_le_mul (by omega) (hK.trans (htr.trans hBaseM))
    _ = _ := by ring
  have hB : descriptionBitBound m ≤ 5*m^3 := calc
    _ ≤ (4*m+12)*m^2 := description_le_polynomial m (by omega)
    _ ≤ (5*m)*m^2 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring
  have hSmall : r*(6*K+1)+descriptionBitBound m ≤ 390*m^3 := by
    rw [show r*(6*K+1) = 384*(r*L)+r by dsimp only [K]; ring]
    omega
  have hCap : 390*m^3 ≤ H := calc
    _ ≤ 390*(2*(a-1))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hHalf 3)
    _ = 3120*(a-1)^3 := by ring
    _ ≤ (a-1)*(a-1)^3 := Nat.mul_le_mul_right _ (by omega)
    _ = (a-1)^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp _ (by omega)
  have hPow : 2^a = 2*H := by
    dsimp only [H]
    rw [← pow_succ', Nat.sub_add_cancel ha]
  have hLoss : 2*multiBlockLoss t = r*L := two_mul_multiBlockLoss t ht
  have hFloor : 4*m^3 ≤ 2^m := calc
    _ ≤ m*m^3 := Nat.mul_le_mul_right _ (by omega)
    _ = m^4 := by ring
    _ ≤ _ := GrowingPrefix.four_power_le_exp m (by omega)
  have hLM : 2^l = m := rfl
  have hDouble : 2*t ≤ (2:ℕ)^t := calc
    _ ≤ 2*2^(t-1) := Nat.mul_le_mul_left _ (by
      have h := (t-1).lt_two_pow_self
      omega)
    _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  have hLib : 2*(2^(2^k)*2^k) ≤ m := calc
    _ = (2*2^k)*2^(2^k) := by ring
    _ ≤ 2^t*2^t := Nat.mul_le_mul
      ((Nat.mul_le_mul_left 2 hK).trans hDouble)
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hK)
    _ = _ := hM.symm
  have hPay : 256*2^t ≤ m := (Nat.mul_le_mul_right (2^t) hR).trans_eq hM.symm
  have hSmallBase : 2*(3*2^k+48) ≤ m := by omega
  have hBase : 4*m+48+lookupBankCost k l ≤ 8*m := by
    unfold lookupBankCost
    rw [hLM]
    omega
  have h19 : 19 ≤ d := by
    have hLog : 3 ≤ k := (Nat.le_log2 (by omega : t ≠ 0)).mpr ht
    dsimp only [d, l]
    omega
  have hPrefix : r*(2*2^l+2*a+3)+8*m ≤ m^2 := calc
    _ = r*(2*2^l+2*a+3+32) := by rw [← hr]; ring
    _ ≤ r*(4*m) := by
      apply Nat.mul_le_mul_left
      rw [hLM]
      dsimp only [a]
      omega
    _ = _ := by rw [show r*(4*m) = (4*r)*m by ring, hr, pow_two]
  exact ⟨by omega, ha, by omega, by omega, by omega⟩

/-- The direct-reader term is preserved, and the downstream term grows
linearly in the represented arity on this schedule. -/
theorem mcspSquare_growing_separated_blocks (t : ℕ) (ht : 8 ≤ t) :
    280*(2*2^(multiBlockArity t) + multiBlockLoss t + separatedBlockCount t) + 2*2^(multiBlockArity t) ≤
      280*(complexity interpretation (single (mcspSquare (multiBlockArity t))) +
        2*descriptionBitBound (multiBlockArity t) + 1) + 17*descriptionBitBound (multiBlockArity t) := by
  let m := multiBlockArity t
  let k := t.log2
  let l := 2*t
  let a := m-(k+l)
  let L := (2:ℕ)^(k+l)
  let K := 64*L
  let H := (2:ℕ)^(a-1)
  let r := separatedBlockCount t
  let G := complexity interpretation (single (mcspSquare m))
  obtain ⟨hd, ha, hRoom, hRepair, hCeiling⟩ := growing_conflict_budget t ht
  have he : a+(k+l) = m := Nat.sub_add_cancel hd
  change 280*(2*2^m + multiBlockLoss t + r) + 2*2^m ≤
    280*(G + 2*descriptionBitBound m + 1) + 17*descriptionBitBound m
  change 2*(multiBlockLoss t + r) ≤ 2^m at hCeiling
  by_cases hG : G ≤ 3*2^m
  · have hN : 2^m = 2*H*L := by
      dsimp only [H, L]
      rw [← pow_succ', Nat.sub_add_cancel ha, ← pow_add, he]
    have hHeavy : 6*G < K*(H+1) := calc
      _ ≤ 6*(3*2^m) := Nat.mul_le_mul_left 6 hG
      _ = (36*H)*L := by rw [hN]; ring
      _ < (64*(H+1))*L := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = _ := by unfold K; ring
    have h := mcspSquare_separated_blocks_of_small_size
      (a := a) (k := k) (l := l) (r := r) (K := K) (H := H) (reserve := 0)
      (Nat.two_pow_pos _) (by dsimp only [l]; omega) (by rw [he]; exact Nat.two_pow_pos _)
      (by rwa [he]) (by rwa [he]) (by rwa [he]) (Nat.zero_le _) (by
        rw [Nat.add_zero, he, ← two_mul_multiBlockLoss t ht]
        exact growing_blocks_fit_factorial t ht)
    have hSize : complexity interpretation (single (mcspSquare (a+(k+l)))) = G := by
      unfold G
      rw [he]
    have hDirect : r*2^(k+l-1) = multiBlockLoss t := same_direct_charge t ht
    rw [hSize, hDirect] at h
    simpa only [he, Nat.sub_zero] using h
  · omega

end Scaling

#print axioms exists_separated_covered_blocks
#print axioms exists_matched_exits
#print axioms original_separated_block_exits
#print axioms mcspSquare_32_separated_blocks
#print axioms four_mul_separatedBlockCount
#print axioms mcspSquare_growing_separated_blocks

end PvsNP.Frontier.IndependentBlockPinning
