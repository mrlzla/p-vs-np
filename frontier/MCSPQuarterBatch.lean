module

public import MCSPQuarterForest

/-! Simultaneous signed identifications with one edited address per copy.
Keep exactly the parameters that still have an unsigned representative. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterBatch

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN ForestRebuild QuarterForest
open scoped Classical

structure Copies where
  sources : Finset Address
  partner : Address → Address
  partner_unsigned : ∀ i ∈ sources, partner i ∉ sources

namespace Copies

variable (C : Copies) {q : ℕ} (parent : Address → Fin q)

noncomputable def keys : Finset (Fin q) := (Finset.univ \ C.sources).image parent

noncomputable def keyEquiv : Fin (C.keys parent).card ≃ C.keys parent :=
  (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm

noncomputable def slot (i : Address) (hi : i ∉ C.sources) : Fin (C.keys parent).card :=
  (C.keyEquiv parent).symm ⟨parent i, Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩⟩

noncomputable def fill (U : BitString (C.keys parent).card) (i : Address) : Bool :=
  if hi : i ∈ C.sources then !(U (C.slot parent (C.partner i) (C.partner_unsigned i hi)))
  else U (C.slot parent i hi)

theorem fill_unsigned (U : BitString (C.keys parent).card) {i : Address} (hi : i ∉ C.sources) :
    C.fill parent U i = U (C.slot parent i hi) := by simp [fill, hi]

theorem fill_complement (U : BitString (C.keys parent).card) {i : Address} (hi : i ∈ C.sources) :
    C.fill parent U i = !(C.fill parent U (C.partner i)) := by
  rw [C.fill_unsigned parent U (C.partner_unsigned i hi)]
  simp [fill, hi]

theorem slot_surjective : ∀ j : Fin (C.keys parent).card, ∃ (i : Address) (hi : i ∉ C.sources),
    C.slot parent i hi = j := by
  intro j
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (C.keyEquiv parent j).property
  have hi' := (Finset.mem_sdiff.mp hi).2
  refine ⟨i, hi', ?_⟩
  apply (C.keyEquiv parent).injective
  rw [slot, Equiv.apply_symm_apply]
  exact Subtype.ext he

theorem fill_injective : Function.Injective (C.fill parent) := by
  intro U V h
  funext j
  obtain ⟨i, hi, rfl⟩ := C.slot_surjective parent j
  have he := congrFun h i
  rwa [C.fill_unsigned parent U hi, C.fill_unsigned parent V hi] at he

theorem lost_keys_le (hSurj : Function.Surjective parent) :
    q ≤ (C.keys parent).card + C.sources.card := by
  have hCover : (Finset.univ : Finset (Fin q)) ⊆ C.keys parent ∪ C.sources.image parent := by
    intro j _
    obtain ⟨i, rfl⟩ := hSurj j
    by_cases hi : i ∈ C.sources
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩)
  have hCover' := (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, Fintype.card_fin] at hCover'
  have hSmall : (C.sources.image parent).card ≤ C.sources.card := Finset.card_image_le
  omega

noncomputable def labels (e : Fin q ↪ BitString 32) : Fin (C.keys parent).card ↪ BitString 32 :=
  (C.keyEquiv parent).toEmbedding.trans (Function.Embedding.subtype _ |>.trans e)

theorem affine_accepted (e : Fin q ↪ BitString 32) (hCard : C.sources.card ≤ 25)
    (a : BitString 32) (b : Bool)
    (hCost : complexity interpretation (single ((MCSP.truthTable 32).symm
      (fun i => affine a b (e (parent i))))) ≤ 131) :
    mcspSquare 32 (C.fill parent (fun j => affine a b (C.labels parent e j))) = true := by
  apply edited_table_accepted _ _ C.sources hCard hCost
  intro i hi
  rw [C.fill_unsigned parent _ hi]
  change affine a b (e (C.keyEquiv parent (C.slot parent i hi)).val) = _
  simp only [slot, Equiv.apply_symm_apply]

set_option maxRecDepth 4000 in
theorem residual_bound (e : Fin q ↪ BitString 32) (hCard : C.sources.card ≤ 25)
    (hCost : ∀ (a : BitString 32) (b : Bool),
      complexity interpretation (single ((MCSP.truthTable 32).symm
        (fun i => affine a b (e (parent i))))) ≤ 131) :
    25884 * (2 * (C.keys parent).card) + 14 * (C.keys parent).card ≤
      25884 * (complexity interpretation (single (mcspSquare 32 ∘ C.fill parent)) + 55345) +
        196 * 27672 := by
  have hs := QuarterFold.pullback_sparse (C.fill parent) (C.fill_injective parent)
    (card_accepting_mcspSquare_le 32)
  have h := tight_reindexed_forest_size (C.labels parent e) hs
    (fun a b => C.affine_accepted parent e hCard a b (hCost a b))
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  exact h

theorem quarter_bound (hCard : C.sources.card ≤ 25) :
    6444137619 ≤ complexity interpretation (single (mcspSquare 32 ∘ C.fill (QuarterFold.foldKey 30))) := by
  let parent := QuarterFold.foldKey 30
  have h := C.residual_bound parent (QuarterBlock.labels 30) hCard QuarterFold.complexity_fold_affine_le_32
  have hk := C.lost_keys_le parent (fun j => ⟨_, QuarterFold.foldKey_at_retained 30 j⟩)
  change 3221225472 ≤ _ at hk
  change 6444137619 ≤ complexity interpretation (single (mcspSquare 32 ∘ C.fill parent))
  omega

theorem full_bound (hCard : C.sources.card ≤ 25) :
    8592202027 ≤ complexity interpretation
      (single (mcspSquare 32 ∘ C.fill (id : Address → Address))) := by
  have hCost (a : BitString 32) (b : Bool) :
      complexity interpretation (single ((MCSP.truthTable 32).symm
        (fun i => affine a b ((BitString.equivFin 32).symm i)))) ≤ 131 := by
    change complexity interpretation (single ((MCSP.truthTable 32).symm
      (MCSP.truthTable 32 (affine a b)))) ≤ _
    rw [Equiv.symm_apply_apply]
    exact (complexity_affine_le a b).trans (by decide)
  have h := C.residual_bound (id : Address → Address) (BitString.equivFin 32).symm.toEmbedding hCard hCost
  have hk := C.lost_keys_le (id : Address → Address) Function.surjective_id
  change 4294967296 ≤ _ at hk
  omega

noncomputable def negKeys : Finset (Fin (C.keys parent).card) :=
  C.sources.attach.image fun i => C.slot parent (C.partner i.val) (C.partner_unsigned i.val i.property)

private def negations {l : ℕ} (T : Finset (Fin l)) : Set (BooleanFunction l) :=
  {f | ∃ j ∈ T, f = fun U => !(U j)}

private theorem synth_negations {l : ℕ} (T : Finset (Fin l)) :
    Synthesis interpretation (inputs l) (negations T) T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have h : negations (∅ : Finset (Fin l)) = ∅ := by ext f; simp [negations]
    rw [h]
    exact Synthesis.of_subset (Set.empty_subset _)
  | @insert j T hj ih =>
    have h : negations (insert j T) = {fun U : BitString l => !(U j)} ∪ negations T := by
      ext f
      simp only [negations, Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union, Set.mem_singleton_iff]
      exact ⟨by rintro ⟨i, rfl | hi, he⟩; exacts [Or.inl he, Or.inr ⟨i, hi, he⟩],
        by rintro (rfl | ⟨i, hi, he⟩); exacts [⟨j, Or.inl rfl, rfl⟩, ⟨i, Or.inr hi, he⟩]⟩
    rw [h, Finset.card_insert_of_notMem hj, Nat.add_comm]
    have hOne : Synthesis interpretation (inputs l) {fun U : BitString l => !(U j)} 1 :=
      (Synthesis.of_mem (show (fun U : BitString l => U j) ∈ inputs l from ⟨j, rfl⟩)).not
    exact hOne.union ih

theorem rebuild (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    complexity interpretation (single (mcspSquare 32 ∘ C.fill parent)) +
      (actualForest c hc).savings (C.fill parent) ≤ c.size + ((C.negKeys parent).card + 2) := by
  let l := (C.keys parent).card
  let low : BooleanFunction l := fun _ => false
  let high : BooleanFunction l := fun _ => true
  let supplies : Set (BooleanFunction l) := inputs l ∪ (negations (C.negKeys parent) ∪ {low} ∪ {high})
  have hLow : Synthesis interpretation (inputs l) {low} 1 := Synthesis.const false
  have hHigh : Synthesis interpretation (inputs l) {high} 1 := Synthesis.const true
  have hSup : Synthesis interpretation (inputs l) supplies ((C.negKeys parent).card + 2) := by
    have h := (synth_negations (C.negKeys parent)).union hLow |>.union hHigh
    have h' := (Synthesis.of_subset (I := interpretation) (Set.Subset.rfl : inputs l ⊆ inputs l)).union h
    simpa only [Nat.zero_add, Nat.add_assoc] using h'
  have hIn (i : Address) : Forest.wireFunction (p := c.program) (C.fill parent) (.input i) ∈ supplies := by
    change (fun U => C.fill parent U i) ∈ supplies
    by_cases hi : i ∈ C.sources
    · apply Set.mem_union_right
      apply Set.mem_union_left
      apply Set.mem_union_left
      let j := C.slot parent (C.partner i) (C.partner_unsigned i hi)
      have hj : j ∈ C.negKeys parent := Finset.mem_image.mpr ⟨⟨i, hi⟩, by simp, rfl⟩
      refine ⟨j, hj, ?_⟩
      funext U
      simp [j, fill, hi]
    · exact Or.inl ⟨C.slot parent i hi, funext fun U => (C.fill_unsigned parent U hi).symm⟩
  have hConst (b : Bool) : (fun _ => b) ∈ supplies := by
    cases b
    · exact Or.inr (Or.inl (Or.inr rfl))
    · exact Or.inr (Or.inr rfl)
  have hh := (actualForest c hc).rebuild_budget (C.fill parent) supplies hSup hIn hConst
  have he : Forest.wireFunction (p := c.program) (C.fill parent) (c.outputs 0) =
      mcspSquare 32 ∘ C.fill parent := by
    funext U
    exact congrFun (hc (C.fill parent U)) 0
  rwa [he] at hh

theorem negKeys_le : (C.negKeys parent).card ≤ C.sources.card := by
  exact Finset.card_image_le.trans (by simp)

theorem quarter_beat_threshold (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hCard : C.sources.card ≤ 25)
    (hSaving : 2148064511 ≤ (actualForest c hc).savings (C.fill (QuarterFold.foldKey 30))) :
    8592202103 ≤ c.size := by
  have h := C.rebuild (QuarterFold.foldKey 30) c hc
  have hL := C.quarter_bound hCard
  have hN := C.negKeys_le (QuarterFold.foldKey 30)
  omega

end Copies

section Packing

variable {α : Type*} (R : Finset α) (leaves : α → Finset Address)

/-- The two leaves of a selected tree are reserved against every other selection. -/
structure Packing where
  chosen : Finset α
  source : α → Address
  partner : α → Address
  subset : chosen ⊆ R
  leaves_mem : ∀ r ∈ chosen, source r ∈ leaves r ∧ partner r ∈ leaves r ∧ source r ≠ partner r
  separate : ∀ r ∈ chosen, ∀ s ∈ chosen, r ≠ s →
    Disjoint ({source r, partner r} : Finset Address) {source s, partner s}

namespace Packing

variable {R leaves} (P : Packing R leaves)

noncomputable def used : Finset Address := P.chosen.biUnion fun r => {P.source r, P.partner r}

theorem used_card_le : P.used.card ≤ 2 * P.chosen.card := by
  calc
    _ ≤ ∑ r ∈ P.chosen, ({P.source r, P.partner r} : Finset Address).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ P.chosen, 2 := Finset.sum_le_sum fun _ _ => (Finset.card_insert_le _ _).trans (by simp)
    _ = _ := by simp [Nat.mul_comm]

private theorem source_inj : Set.InjOn P.source (↑P.chosen : Set α) := by
  intro r hr s hs he
  by_contra hn
  exact Finset.disjoint_left.mp (P.separate r hr s hs hn)
    (by simp : P.source r ∈ ({P.source r, P.partner r} : Finset Address))
    (by simp [he])

theorem partner_unsigned {r : α} (hr : r ∈ P.chosen) :
    P.partner r ∉ P.chosen.image P.source := by
  intro h
  obtain ⟨s, hs, he⟩ := Finset.mem_image.mp h
  by_cases hn : r = s
  · subst s
    exact (P.leaves_mem r hr).2.2 he
  · exact Finset.disjoint_left.mp (P.separate r hr s hs hn)
      (by simp : P.partner r ∈ ({P.source r, P.partner r} : Finset Address))
      (by simp [← he])

noncomputable def copies : Copies := by
  let sources := P.chosen.image P.source
  let partner (i : Address) : Address :=
    if hi : i ∈ sources then P.partner (Finset.mem_image.mp hi).choose else i
  refine ⟨sources, partner, ?_⟩
  intro i hi
  simp only [partner, dite_eq_left hi]
  exact P.partner_unsigned (Finset.mem_image.mp hi).choose_spec.1

theorem copies_card : P.copies.sources.card = P.chosen.card :=
  Finset.card_image_of_injOn P.source_inj

theorem complementary {q : ℕ} (parent : Address → Fin q) {r : α} (hr : r ∈ P.chosen)
    (U : BitString (P.copies.keys parent).card) :
    P.copies.fill parent U (P.source r) = !(P.copies.fill parent U (P.partner r)) := by
  have hi : P.source r ∈ P.copies.sources := Finset.mem_image_of_mem P.source hr
  have he : P.copies.partner (P.source r) = P.partner r := by
    change (if h : P.source r ∈ P.chosen.image P.source then
      P.partner (Finset.mem_image.mp h).choose else P.source r) = _
    split
    · rename_i h'
      congr 1
      have h := (Finset.mem_image.mp h').choose_spec
      exact P.source_inj h.1 hr h.2
    · rename_i h'
      exact (h' hi).elim
  simpa only [he] using P.copies.fill_complement parent U hi

private theorem extend {r : α} (hr : r ∈ R) (hn : r ∉ P.chosen) {s t : Address}
    (hs : s ∈ leaves r \ P.used) (ht : t ∈ leaves r \ P.used) (hne : s ≠ t) :
    ∃ Q : Packing R leaves, Q.chosen.card = P.chosen.card + 1 := by
  let source := Function.update P.source r s
  let partner := Function.update P.partner r t
  have hSame (j : α) (hj : j ≠ r) :
      ({source j, partner j} : Finset Address) = {P.source j, P.partner j} := by
    simp [source, partner, hj]
  have hDis (j : α) (hj : j ∈ P.chosen) :
      Disjoint ({s, t} : Finset Address) {P.source j, P.partner j} := by
    apply Finset.disjoint_left.mpr
    intro i hi hj'
    have hiU : i ∈ P.used := Finset.mem_biUnion.mpr ⟨j, hj, hj'⟩
    have he : i = s ∨ i = t := by simpa using hi
    rcases he with rfl | rfl
    · exact (Finset.mem_sdiff.mp hs).2 hiU
    · exact (Finset.mem_sdiff.mp ht).2 hiU
  refine ⟨⟨insert r P.chosen, source, partner, ?_, ?_, ?_⟩, Finset.card_insert_of_notMem hn⟩
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hr
    · exact P.subset hj
  · intro j hj
    by_cases he : j = r
    · subst j
      simpa [source, partner] using And.intro (Finset.mem_sdiff.mp hs).1
        (And.intro (Finset.mem_sdiff.mp ht).1 hne)
    · have hj' := (Finset.mem_insert.mp hj).resolve_left he
      simpa [source, partner, he] using P.leaves_mem j hj'
  · intro j hj k hk hjk
    by_cases he : j = r
    · subst j
      have hk' := (Finset.mem_insert.mp hk).resolve_left hjk.symm
      rw [hSame k hjk.symm]
      simpa [source, partner] using hDis k hk'
    · have hj' := (Finset.mem_insert.mp hj).resolve_left he
      rw [hSame j he]
      by_cases he' : k = r
      · subst k
        simpa [source, partner] using (hDis j hj').symm
      · have hk' := (Finset.mem_insert.mp hk).resolve_left he'
        rw [hSame k he']
        exact P.separate j hj' k hk' hjk

/-- Greedily extend until the budget is full or no unselected root has two
unused leaves. Existing signed pairs never interfere with newly chosen ones. -/
theorem exists_full_or_maximal [DecidableEq α] (cap : ℕ) :
    ∃ P : Packing R leaves, P.chosen.card ≤ cap ∧
      (P.chosen.card = cap ∨ ∀ r ∈ R \ P.chosen, (leaves r \ P.used).card ≤ 1) := by
  have h (t : ℕ) (P : Packing R leaves) (hP : P.chosen.card + t = cap) :
      ∃ Q : Packing R leaves, Q.chosen.card ≤ cap ∧
        (Q.chosen.card = cap ∨ ∀ r ∈ R \ Q.chosen, (leaves r \ Q.used).card ≤ 1) := by
    induction t generalizing P with
    | zero => exact ⟨P, by omega, Or.inl (by omega)⟩
    | succ t ih =>
      by_cases he : ∃ r ∈ R \ P.chosen, 1 < (leaves r \ P.used).card
      · obtain ⟨r, hr, hPair⟩ := he
        obtain ⟨s, hs, u, hu, hsu⟩ := Finset.one_lt_card.mp hPair
        obtain ⟨Q, hQ⟩ := P.extend (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp hr).2 hs hu hsu
        exact ih Q (by omega)
      · exact ⟨P, by omega, Or.inr fun r hr => Nat.le_of_not_gt fun h' => he ⟨r, hr, h'⟩⟩
  let E : Packing R leaves :=
    ⟨∅, fun _ => 0, fun _ => 0, Finset.empty_subset _, by simp, by simp⟩
  exact h cap E (by simp [E])

end Packing
end Packing

section Actual

variable (c : Circuit signature (2 ^ 32) 1)
variable (hc : c.Computes interpretation (single (mcspSquare 32)))

abbrev ForestPacking := Packing (actualForest c hc).roots (actualForest c hc).rawLeaves

include hc in
private theorem forest_corners :
    cornerValue c.program false (c.outputs 0) = true ∧ cornerValue c.program true (c.outputs 0) = true :=
  ⟨(congrFun (hc _) 0).trans (mcspSquare_constant_table 32 (by decide) false),
    (congrFun (hc _) 0).trans (mcspSquare_constant_table 32 (by decide) true)⟩

private theorem input_in_forest {i : Address} (hi : i ∈ needInputs c.program (c.outputs 0) false) :
    i ∈ stopInputs c.program (c.outputs 0) ∨
      ∃ r ∈ (actualForest c hc).roots, i ∈ (actualForest c hc).rawLeaves r := by
  classical
  have hCorner := forest_corners c hc
  rcases need_input_in_stop_or_forest hCorner.1 hCorner.2 hi with hs | ⟨r, hr, hLeaf⟩ | ⟨r, hr, hLeaf⟩
  · exact Or.inl hs
  · refine Or.inr ⟨r, Finset.mem_union_left _ hr, ((actualForest c hc).mem_rawLeaves).mpr ?_⟩
    obtain ⟨j, hj, a, ha⟩ := (Finset.mem_filter.mp hLeaf).2
    refine ⟨j, ?_, a, ha⟩
    simp [actualForest, ofCorners, hr, hj]
  · have hNo : r ∉ ORRoot c.program (c.outputs 0) := by
      intro h
      have ho := (orMember_rebuild_data hCorner.1 hCorner.2 (ORMember.self h)).1
      have ha := (andMember_rebuild_data hCorner.1 hCorner.2 (ANDMember.self hr)).1
      rw [ho] at ha
      cases ha
    refine Or.inr ⟨r, Finset.mem_union_right _ hr, ((actualForest c hc).mem_rawLeaves).mpr ?_⟩
    obtain ⟨j, hj, a, ha⟩ := (Finset.mem_filter.mp hLeaf).2
    refine ⟨j, ?_, a, ha⟩
    simp [actualForest, ofCorners, hNo, hj]

variable (P : ForestPacking c hc)

noncomputable def collapsedNodes : ℕ :=
  ∑ r ∈ P.chosen, ((actualForest c hc).nodes r).card

theorem weight_of_collapse {q : ℕ} (parent : Address → Fin q)
    {r : Fin c.size} (hr : r ∈ P.chosen) :
    (actualForest c hc).replacementCost (P.copies.fill parent) r = 0 := by
  let F := actualForest c hc
  apply F.replacementCost_eq_zero_of_constant (P.copies.fill parent) (b := F.absorbing r)
  intro U
  change c.program.trace interpretation (P.copies.fill parent U) (.gate r) = F.absorbing r
  have hs : (.input (P.source r) : Wire (2 ^ 32) c.size) ∈ F.boundary r :=
    (Finset.mem_filter.mp (P.leaves_mem r hr).1).2
  have ht : (.input (P.partner r) : Wire (2 ^ 32) c.size) ∈ F.boundary r :=
    (Finset.mem_filter.mp (P.leaves_mem r hr).2.1).2
  have hComplement := P.complementary parent hr U
  apply (F.trace_root_iff_boundary (P.subset hr) _).mpr
  by_cases hValue : P.copies.fill parent U (P.partner r) = F.absorbing r
  · exact ⟨.input (P.partner r), ht, hValue⟩
  · refine ⟨.input (P.source r), hs, ?_⟩
    change P.copies.fill parent U (P.source r) = F.absorbing r
    rw [hComplement]
    have hBool (x b : Bool) (h : x ≠ b) : (!x) = b := by cases x <;> cases b <;> simp_all
    exact hBool _ _ hValue

/-- Duplication is charged only in trees whose entire size was not charged. -/
noncomputable def otherDuplicateSavings {q : ℕ} (parent : Address → Fin q) : ℕ :=
  let F := actualForest c hc
  ∑ r ∈ F.roots \ P.chosen,
    (((F.boundary r).card - 1) - ((F.boundaryFunctions (P.copies.fill parent) r).card - 1))

theorem combined_savings {q : ℕ} (parent : Address → Fin q) :
    collapsedNodes c hc P + otherDuplicateSavings c hc P parent ≤
      (actualForest c hc).savings (P.copies.fill parent) := by
  classical
  let F := actualForest c hc
  let fill := P.copies.fill parent
  let f (r : Fin c.size) := (F.nodes r).card - F.replacementCost fill r
  have hSum : (∑ r ∈ F.roots \ P.chosen, f r) + (∑ r ∈ P.chosen, f r) = ∑ r ∈ F.roots, f r :=
    Finset.sum_sdiff P.subset
  have hC : ∑ r ∈ P.chosen, f r = collapsedNodes c hc P := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [f, fill, F, weight_of_collapse c hc P parent hr, Nat.sub_zero]
  have hD : otherDuplicateSavings c hc P parent ≤ ∑ r ∈ F.roots \ P.chosen, f r := by
    unfold otherDuplicateSavings
    apply Finset.sum_le_sum
    intro r hr
    have hw := F.card_boundary_le (Finset.mem_sdiff.mp hr).1
    have he : F.replacementCost fill r ≤ (F.boundaryFunctions fill r).card - 1 := by
      unfold Forest.replacementCost
      split <;> omega
    change (F.boundary r).card - 1 - ((F.boundaryFunctions fill r).card - 1) ≤ _
    dsimp only [f]
    omega
  change _ ≤ ∑ r ∈ F.roots, f r
  rw [hC] at hSum
  omega

/-- A near-full version of the same edits bounds the number of original
nodes in the selected trees, independently of the quarter fold. -/
theorem collapsed_nodes_cap (hSize : c.size ≤ 8592202102) (hCard : P.chosen.card ≤ 25) :
    collapsedNodes c hc P ≤ 102 := by
  let parent : Address → Address := id
  have hCard' : P.copies.sources.card ≤ 25 := by rwa [P.copies_card]
  have h := P.copies.rebuild parent c hc
  have hL := P.copies.full_bound hCard'
  change 8592202027 ≤ complexity interpretation (single (mcspSquare 32 ∘ P.copies.fill parent)) at hL
  have hN := (P.copies.negKeys_le parent).trans hCard'
  have hS := combined_savings c hc P parent
  omega

private theorem forest_cover_large (hSize : c.size ≤ 8592202102) :
    954397414 + ((actualForest c hc).roots).card + (stopInputs c.program (c.outputs 0)).card ≤
      (needInputs c.program (c.outputs 0) false).card := by
  have hF0 := mcspSquare_constant_table 32 (by decide) false
  have hF1 := mcspSquare_constant_table 32 (by decide) true
  have hC := forest_corners c hc
  have hSparse := card_accepting_mcspSquare_le 32
  rw [show descriptionBitBound 32 = 27672 by decide] at hSparse
  have hN0 := card_needInputs_ge_of_sparse c hc hSparse false hF0
  have hN1 := card_needInputs_ge_of_sparse c hc hSparse true hF1
  have hAcct := needInputs_add_slack_eq c.program (c.outputs 0) hC.1 hC.2
  change 4294967296 ≤ (needInputs c.program (c.outputs 0) false).card + 27672 at hN0
  change 4294967296 ≤ (needInputs c.program (c.outputs 0) true).card + 27672 at hN1
  change _ = c.size + 1 at hAcct
  have hSlack : slack c.program (c.outputs 0) ≤ 2322855 := by omega
  have hRoots : ((actualForest c hc).roots).card ≤
      (ORRoot c.program (c.outputs 0)).card + (ANDRoot c.program (c.outputs 0)).card :=
    Finset.card_union_le _ _
  have hJoint := card_stopInputs_and_roots_le c hc hSparse hF0 hF1
  have hStop := card_stopGate_le_56_slack c.program (c.outputs 0) hC.1 hC.2
  omega

private theorem maximal_pack_large (hSize : c.size ≤ 8592202102)
    (hCard : P.chosen.card < 25)
    (hMax : ∀ r ∈ (actualForest c hc).roots \ P.chosen,
      ((actualForest c hc).rawLeaves r \ P.used).card ≤ 1) :
    954397366 ≤ collapsedNodes c hc P := by
  let F := actualForest c hc
  let S := stopInputs c.program (c.outputs 0)
  let L := (F.roots \ P.chosen).biUnion (fun r => F.rawLeaves r \ P.used)
  let J := P.chosen.biUnion F.rawLeaves
  have hCover : needInputs c.program (c.outputs 0) false ⊆ S ∪ P.used ∪ L ∪ J := by
    intro i hi
    rcases input_in_forest c hc hi with hs | ⟨r, hr, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hs))
    · by_cases hr' : r ∈ P.chosen
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr', hi⟩)
      · by_cases hu : i ∈ P.used
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨r, Finset.mem_sdiff.mpr ⟨hr, hr'⟩, Finset.mem_sdiff.mpr ⟨hi, hu⟩⟩))
  have hL : L.card ≤ (F.roots \ P.chosen).card := by
    calc
      _ ≤ ∑ r ∈ F.roots \ P.chosen, (F.rawLeaves r \ P.used).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ F.roots \ P.chosen, 1 := Finset.sum_le_sum hMax
      _ = _ := by simp
  have hJ : J.card ≤ collapsedNodes c hc P + P.chosen.card := by
    calc
      _ ≤ ∑ r ∈ P.chosen, (F.rawLeaves r).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ P.chosen, ((F.nodes r).card + 1) :=
        Finset.sum_le_sum (fun r hr => F.card_rawLeaves_le (P.subset hr))
      _ = _ := by simp [collapsedNodes, F, Finset.sum_add_distrib]
  have hSplit := Finset.card_sdiff_add_card_eq_card P.subset
  change (F.roots \ P.chosen).card + P.chosen.card = F.roots.card at hSplit
  have hu := P.used_card_le
  have hCover' := Finset.card_le_card hCover
  have hU0 := Finset.card_union_le S P.used
  have hU1 := Finset.card_union_le (S ∪ P.used) L
  have hU2 := Finset.card_union_le (S ∪ P.used ∪ L) J
  have h := forest_cover_large c hc hSize
  change 954397414 + F.roots.card + S.card ≤ _ at h
  omega

/-- A circuit within the full-size benchmark admits 25 disjoint leaf
pairs in 25 distinct components. An early halt would collapse too many
gates even when the underlying fold is replaced by the identity. -/
theorem exists_twentyfive (hSize : c.size ≤ 8592202102) :
    ∃ P' : ForestPacking c hc, P'.chosen.card = 25 := by
  obtain ⟨Q, hQ, hExact | hMax⟩ :=
    Packing.exists_full_or_maximal (R := (actualForest c hc).roots) (leaves := (actualForest c hc).rawLeaves) 25
  · exact ⟨Q, hExact⟩
  · by_cases hEq : Q.chosen.card = 25
    · exact ⟨Q, hEq⟩
    · have hLo := maximal_pack_large c hc Q hSize (by omega) hMax
      have hHi := collapsed_nodes_cap c hc Q hSize hQ
      omega

theorem quarter_beat_of_counted_savings (hCard : P.chosen.card ≤ 25)
    (hSaving : 2148064511 ≤ collapsedNodes c hc P +
      otherDuplicateSavings c hc P (QuarterFold.foldKey 30)) : 8592202103 ≤ c.size := by
  apply P.copies.quarter_beat_threshold c hc (by rwa [P.copies_card])
  exact hSaving.trans (combined_savings c hc P (QuarterFold.foldKey 30))

section RawDuplicates

private theorem raw_of_OR {r : Fin c.size} (hr : r ∈ ORRoot c.program (c.outputs 0)) :
    (actualForest c hc).rawLeaves r = orInputs c.program (c.outputs 0) r := by
  ext i
  rw [(actualForest c hc).mem_rawLeaves]
  simp [actualForest, ofCorners, hr, orInputs]

include hc in
private theorem roots_disjoint :
    Disjoint (ORRoot c.program (c.outputs 0)) (ANDRoot c.program (c.outputs 0)) := by
  apply Finset.disjoint_left.mpr
  intro r ho ha
  have h := forest_corners c hc
  have hO := (orMember_rebuild_data h.1 h.2 (ORMember.self ho)).1
  have hA := (andMember_rebuild_data h.1 h.2 (ANDMember.self ha)).1
  rw [hO] at hA
  cases hA

private theorem raw_of_AND {r : Fin c.size} (hr : r ∈ ANDRoot c.program (c.outputs 0)) :
    (actualForest c hc).rawLeaves r = andInputs c.program (c.outputs 0) r := by
  have hNo : r ∉ ORRoot c.program (c.outputs 0) := fun ho => Finset.disjoint_left.mp (roots_disjoint c hc) ho hr
  ext i
  rw [(actualForest c hc).mem_rawLeaves]
  simp [actualForest, ofCorners, hNo, andInputs]

variable (B : Copies)

/-- Count equal raw leaf signals within each tree outside the selected trees. -/
noncomputable def rawDuplicateSavings : ℕ :=
  ∑ r ∈ (actualForest c hc).roots \ P.chosen,
    (let leaves := (actualForest c hc).rawLeaves r
     leaves.card - (leaves.image (fun i U => P.copies.fill (QuarterFold.foldKey 30) U i)).card)

private theorem raw_cost_le_boundary (r : Fin c.size) :
    (let L := (actualForest c hc).rawLeaves r
     L.card - (L.image (fun i U => P.copies.fill (QuarterFold.foldKey 30) U i)).card) ≤
      (((actualForest c hc).boundary r).card - 1) -
        (((actualForest c hc).boundaryFunctions (P.copies.fill (QuarterFold.foldKey 30)) r).card - 1) := by
  let F := actualForest c hc
  let fill := P.copies.fill (QuarterFold.foldKey 30)
  let f := Forest.wireFunction (p := c.program) fill
  let L := F.rawLeaves r
  let I := L.image (Wire.input : Address → Wire (2 ^ 32) c.size)
  let W := F.boundary r
  have hIW : I ⊆ W := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hi).2
  have hI : I.card = L.card := Finset.card_image_of_injective _ (by intro i j h; cases h; rfl)
  have hfI : I.image f = L.image (fun i U => fill U i) := by
    rw [show I = L.image (Wire.input : Address → Wire (2 ^ 32) c.size) from rfl, Finset.image_image]
    rfl
  have hU : (W.image f).card ≤ (I.image f).card + (W \ I).card := by
    calc
      _ = ((I.image f) ∪ ((W \ I).image f)).card := by
        rw [← Finset.image_union, Finset.union_sdiff_of_subset hIW]
      _ ≤ _ := (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have hP := Finset.card_sdiff_add_card_eq_card hIW
  have hMono : (I.image f).card ≤ (W.image f).card := Finset.card_le_card (Finset.image_subset_image hIW)
  change L.card - (L.image (fun i U => fill U i)).card ≤ (W.card - 1) - ((W.image f).card - 1)
  rw [← hI, ← hfI]
  by_cases hN : W.Nonempty
  · have h1 := Finset.card_pos.mpr hN
    have h2 := Finset.card_pos.mpr (hN.image f)
    omega
  · have hW := Finset.not_nonempty_iff_eq_empty.mp hN
    have hIempty : I = ∅ := Finset.subset_empty.mp (hW ▸ hIW)
    simp [hIempty]

theorem raw_duplicates_in_boundary_budget :
    rawDuplicateSavings c hc P ≤ otherDuplicateSavings c hc P (QuarterFold.foldKey 30) := by
  unfold rawDuplicateSavings otherDuplicateSavings
  exact Finset.sum_le_sum fun r _ => raw_cost_le_boundary c hc P r

private theorem quarter_key_inj_kept {i j : Address}
    (hi : QuarterBlock.keptKey 30 i = true) (hj : QuarterBlock.keptKey 30 j = true)
    (h : QuarterFold.foldKey 30 i = QuarterFold.foldKey 30 j) : i = j := by
  let e := QuarterBlock.freeEquiv 30
  have hKey (x : Address) (hx : QuarterBlock.keptKey 30 x = true) :
      QuarterFold.foldKey 30 x = e.symm ⟨x, hx⟩ := by
    have he : (e (e.symm ⟨x, hx⟩)).val = x := congrArg Subtype.val (e.apply_symm_apply _)
    exact (congrArg (QuarterFold.foldKey 30) he).symm.trans (QuarterFold.foldKey_at_retained 30 _)
  rw [hKey i hi, hKey j hj] at h
  exact congrArg Subtype.val (e.symm.injective h)

private theorem kept_leaf_signals_injective :
    Set.InjOn (fun i U => B.fill (QuarterFold.foldKey 30) U i)
      (↑((Finset.univ : Finset Address) \ (QuarterBlock.zeroBlock 30 ∪ B.sources)) : Set Address) := by
  let parent := QuarterFold.foldKey 30
  intro i hi j hj h
  have hInfo (x : Address) (hx : x ∈ (Finset.univ : Finset Address) \ (QuarterBlock.zeroBlock 30 ∪ B.sources)) :
      QuarterBlock.keptKey 30 x = true ∧ x ∉ B.sources := by
    have h := (Finset.mem_sdiff.mp hx).2
    refine ⟨Bool.eq_true_of_not_eq_false (fun ha => h (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))), fun ha => h (Finset.mem_union_right _ ha)⟩
  obtain ⟨hiK, hiB⟩ := hInfo i hi
  obtain ⟨hjK, hjB⟩ := hInfo j hj
  have he : B.slot parent i hiB = B.slot parent j hjB := by
    by_contra hn
    let U : BitString (B.keys parent).card := fun t => decide (t = B.slot parent i hiB)
    have ht := congrFun h U
    change B.fill parent U i = B.fill parent U j at ht
    rw [B.fill_unsigned parent U hiB, B.fill_unsigned parent U hjB] at ht
    simp [U, Ne.symm hn] at ht
  have hKey (x : Address) (hx : x ∉ B.sources) :
      (B.keyEquiv parent (B.slot parent x hx)).val = parent x := by
    simp only [Copies.slot, Equiv.apply_symm_apply]
  have hs := congrArg (fun j => (B.keyEquiv parent j).val) he
  rw [hKey i hiB, hKey j hjB] at hs
  exact quarter_key_inj_kept hiK hjK hs

private theorem raw_duplicates_le_bad (L : Finset Address) :
    L.card - (L.image (fun i U => B.fill (QuarterFold.foldKey 30) U i)).card ≤
      (L ∩ (QuarterBlock.zeroBlock 30 ∪ B.sources)).card := by
  let bad := QuarterBlock.zeroBlock 30 ∪ B.sources
  let f := fun i U => B.fill (QuarterFold.foldKey 30) U i
  have hInj : Set.InjOn f (↑(L \ (L ∩ bad)) : Set Address) := by
    apply (kept_leaf_signals_injective B).mono
    intro i hi
    have hi' : i ∈ L \ (L ∩ bad) := hi
    obtain ⟨hL, hB⟩ := Finset.mem_sdiff.mp hi'
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hB (Finset.mem_inter.mpr ⟨hL, h⟩)⟩
  have hImg : (L \ (L ∩ bad)).card ≤ (L.image f).card := by
    rw [← Finset.card_image_of_injOn hInj]
    exact Finset.card_le_card (Finset.image_subset_image Finset.sdiff_subset)
  have hPart := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : L ∩ bad ⊆ L)
  change L.card - (L.image f).card ≤ (L ∩ bad).card
  omega

/-- In either polarity a raw address can spend the duplicate charge only once. -/
theorem raw_duplicate_cap (hCard : P.chosen.card ≤ 25) :
    rawDuplicateSavings c hc P ≤ 2147483698 := by
  let F := actualForest c hc
  let bad := QuarterBlock.zeroBlock 30 ∪ P.copies.sources
  let f := fun i U => P.copies.fill (QuarterFold.foldKey 30) U i
  let cost (r : Fin c.size) := (F.rawLeaves r).card - ((F.rawLeaves r).image f).card
  have hBad := Finset.card_union_le (QuarterBlock.zeroBlock 30) P.copies.sources
  rw [QuarterBlock.zeroBlock_card, P.copies_card] at hBad
  change bad.card ≤ 1073741824 + P.chosen.card at hBad
  have hSide (T : Finset (Fin c.size))
      (h : ∀ r ∈ T, ∀ s ∈ T, r ≠ s → Disjoint (F.rawLeaves r) (F.rawLeaves s)) :
      (∑ r ∈ T, cost r) ≤ bad.card := by
    calc
      _ ≤ ∑ r ∈ T, (F.rawLeaves r ∩ bad).card :=
        Finset.sum_le_sum (fun r _ => raw_duplicates_le_bad P.copies (F.rawLeaves r))
      _ = (T.biUnion fun r => F.rawLeaves r ∩ bad).card := by
        symm
        apply Finset.card_biUnion
        intro r hr s hs hne
        exact (h r hr s hs hne).mono Finset.inter_subset_left Finset.inter_subset_left
      _ ≤ _ := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨r, _, hi'⟩ := Finset.mem_biUnion.mp hi
        exact (Finset.mem_inter.mp hi').2
  have hC := forest_corners c hc
  have hOr := hSide (ORRoot c.program (c.outputs 0)) (fun r hr s hs hne => by
    simp only [F, raw_of_OR c hc hr, raw_of_OR c hc hs]
    exact orInputs_disjoint hC.1 hne)
  have hAnd := hSide (ANDRoot c.program (c.outputs 0)) (fun r hr s hs hne => by
    simp only [F, raw_of_AND c hc hr, raw_of_AND c hc hs]
    exact andInputs_disjoint hC.2 hne)
  have hSub : rawDuplicateSavings c hc P ≤ ∑ r ∈ F.roots, cost r :=
    Finset.sum_le_sum_of_subset Finset.sdiff_subset
  have hSum : (∑ r ∈ F.roots, cost r) ≤ bad.card + bad.card := by
    change (∑ r ∈ ORRoot c.program (c.outputs 0) ∪ ANDRoot c.program (c.outputs 0), cost r) ≤ _
    rw [Finset.sum_union (roots_disjoint c hc)]
    exact Nat.add_le_add hOr hAnd
  omega

/-- Even granting all the raw-duplicate credit, the selected collapses
and raw duplicates cannot meet the quarter benchmark by themselves. -/
theorem raw_and_selected_below (hSize : c.size ≤ 8592202102) (hCard : P.chosen.card ≤ 25) :
    collapsedNodes c hc P + rawDuplicateSavings c hc P ≤ 2147483800 := by
  exact Nat.add_le_add (collapsed_nodes_cap c hc P hSize hCard) (raw_duplicate_cap c hc P hCard)

theorem raw_count_shortfall (hSize : c.size ≤ 8592202102) (hCard : P.chosen.card ≤ 25) :
    6444137669 + (collapsedNodes c hc P + rawDuplicateSavings c hc P) + 580634 ≤ 8592202103 := by
  have h := raw_and_selected_below c hc P hSize hCard
  omega

end RawDuplicates

end Actual

#print axioms Copies.quarter_bound
#print axioms Copies.full_bound
#print axioms Copies.rebuild
#print axioms Copies.quarter_beat_threshold

#print axioms combined_savings
#print axioms collapsed_nodes_cap
#print axioms exists_twentyfive
#print axioms quarter_beat_of_counted_savings
#print axioms raw_and_selected_below
#print axioms raw_duplicates_in_boundary_budget
#print axioms raw_count_shortfall

end PvsNP.Frontier.QuarterBatch
