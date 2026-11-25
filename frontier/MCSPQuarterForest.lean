module

public import MCSPForestRebuild
public import MCSPQuarterFold
public import MCSPMinorityResidual

/-! Choose a complemented copy from the actual two-corner forest. Rebuild the
three-quarter residual and charge original forest gates component by component. -/

@[expose] public section

namespace PvsNP.Frontier.QuarterForest

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN ForestRebuild
open QuarterBlock (keptKey freeEquiv labels zeroBlock)
open QuarterFold (foldKey pullback_sparse complexity_fold_affine_le_32)
open MinorityResidual (point_indicator_complexity_le)
open scoped Classical

abbrev Address := Fin (2 ^ 32)
abbrev Free := Fin (3 * 2 ^ 30)
abbrev Fill := (Free → Bool) → (Address → Bool)

/-- Point corrections share a single bank of negated represented inputs. -/
theorem edited_table_accepted (T W : Address → Bool) (P : Finset Address) (hCard : P.card ≤ 25)
    (hCost : complexity interpretation (single ((MCSP.truthTable 32).symm T)) ≤ 131)
    (hAgree : ∀ i ∉ P, W i = T i) :
    mcspSquare 32 W = true := by
  classical
  let A := (MCSP.truthTable 32).symm T
  let D := P.filter fun i => W i ≠ T i
  let mask : BooleanFunction 32 := fun z => decide (BitString.equivFin 32 z ∈ D)
  have hMask : (MCSP.truthTable 32).symm (W) = fun z => A z ^^ mask z := by
    funext z
    let i := BitString.equivFin 32 z
    change W i = (T i ^^ decide (i ∈ D))
    by_cases hi : i ∈ P
    · simp only [D, Finset.mem_filter, hi, true_and]
      have he (x y : Bool) : y = (x ^^ decide (y ≠ x)) := by cases x <;> cases y <;> decide
      exact he (T i) (W i)
    · rw [hAgree i hi]
      simp [D, hi]
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hMask]
  have hA : complexity interpretation (single A) ≤ 131 := hCost
  have hm : complexity interpretation (single mask) ≤ 32 + D.card * 34 + 1 :=
    point_indicator_complexity_le 32 D
  have hD : D.card ≤ P.card := Finset.card_filter_le _ _
  exact (complexity_xor_le A mask).trans (by omega)

/-- Up to 25 edits preserve the same residual lower bound if all free
inputs remain recoverable. -/
theorem residual_of_injective_edit (fill : Fill) (P : Finset Address) (hCard : P.card ≤ 25)
    (hInj : Function.Injective fill)
    (hAgree : ∀ U i, i ∉ P → fill U i = U (foldKey 30 i)) :
    6444137669 ≤ complexity interpretation (single (mcspSquare 32 ∘ fill)) := by
  have hSparse := pullback_sparse fill hInj (card_accepting_mcspSquare_le 32)
  have hAffine (a : BitString 32) (b : Bool) :
      mcspSquare 32 (fill (fun j => affine a b (labels 30 j))) = true :=
    edited_table_accepted _ _ P hCard (complexity_fold_affine_le_32 a b) (hAgree _)
  have h := tight_reindexed_forest_size (labels 30) hSparse hAffine
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 25884 * (2 * 3221225472) + 14 * 3221225472 ≤
    25884 * (complexity interpretation (single (mcspSquare 32 ∘ fill)) + 2 * 27672 + 1) +
      196 * 27672 at h
  omega

theorem residual_of_modified_fold (fill : Fill) (P : Finset Address) (hCard : P.card ≤ 25)
    (hQuarter : P ⊆ zeroBlock 30)
    (hAgree : ∀ U i, i ∉ P → fill U i = U (foldKey 30 i)) :
    6444137669 ≤ complexity interpretation (single (mcspSquare 32 ∘ fill)) := by
  classical
  have hInj : Function.Injective fill := by
    intro U V h
    funext j
    let i := (freeEquiv 30 j).val
    have hi : i ∉ P := by
      intro hP
      have hFalse : keptKey 30 i = false := (Finset.mem_filter.mp (hQuarter hP)).2
      rw [(freeEquiv 30 j).property] at hFalse
      cases hFalse
    have he := congrFun h i
    rw [hAgree U i hi, hAgree V i hi] at he
    exact (by simpa only [i, QuarterFold.foldKey_at_retained] using he)
  exact residual_of_injective_edit fill P hCard hInj hAgree

/-- At one deleted entry, use the complement of the value read by the chosen
other leaf. The other leaf may itself be an unsigned copy. -/
noncomputable def signedCopy (source partner : Address) : Fill :=
  fun U i => if i = source then !(U (foldKey 30 partner)) else U (foldKey 30 i)

theorem signedCopy_complementary {source partner : Address} (hne : partner ≠ source) (U : Free → Bool) :
    signedCopy source partner U source = !(signedCopy source partner U partner) := by
  simp [signedCopy, hne]

theorem mcsp_signedCopy_residual {source partner : Address} (hSource : source ∈ zeroBlock 30) :
    6444137669 ≤ complexity interpretation (single (mcspSquare 32 ∘ signedCopy source partner)) := by
  apply residual_of_modified_fold _ {source} (by simp)
  · simpa using hSource
  · intro U i hi
    have he : i ≠ source := by simpa using hi
    simp [signedCopy, he]

private theorem rebuild_signedCopy {n k : ℕ} {g : ℕ}
    {p : Program signature n g} {output : Wire n g} (F : Forest p output)
    (parent : Fin n → Fin k) (source : Fin n) (target : Fin k) :
    let fill : BitString k → BitString n := fun U i => if i = source then !(U target) else U (parent i)
    complexity interpretation (single (Forest.wireFunction (p := p) fill output)) + F.savings fill ≤ g + 3 := by
  intro fill
  let neg : BooleanFunction k := fun U => !(U target)
  let low : BooleanFunction k := fun _ => false
  let high : BooleanFunction k := fun _ => true
  let supplies : Set (BooleanFunction k) := inputs k ∪ ({neg} ∪ {low} ∪ {high})
  have hNeg : Synthesis interpretation (inputs k) {neg} 1 :=
    (Synthesis.of_mem (show (fun U : BitString k => U target) ∈ inputs k from ⟨target, rfl⟩)).not
  have hLow : Synthesis interpretation (inputs k) {low} 1 := Synthesis.const false
  have hHigh : Synthesis interpretation (inputs k) {high} 1 := Synthesis.const true
  have hSup : Synthesis interpretation (inputs k) supplies 3 := by
    have h := (hNeg.union hLow).union hHigh
    exact (Synthesis.of_subset (I := interpretation) (Set.Subset.rfl : inputs k ⊆ inputs k)).union h
  refine F.rebuild_budget fill supplies hSup ?_ ?_
  · intro i
    change (fun U => if i = source then !(U target) else U (parent i)) ∈ supplies
    by_cases hi : i = source
    · simp [hi, supplies, neg]
    · exact (by
        rw [show (fun U : BitString k => if i = source then !(U target) else U (parent i)) =
            (fun U => U (parent i)) by funext U; simp [hi]]
        exact Or.inl ⟨parent i, rfl⟩)
  · intro b
    cases b <;> simp [supplies, low, high]

noncomputable def actualForest (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) : Forest c.program (c.outputs 0) :=
  ofCorners c.program (c.outputs 0)
    ((congrFun (hc _) 0).trans (mcspSquare_constant_table 32 (by decide) false))
    ((congrFun (hc _) 0).trans (mcspSquare_constant_table 32 (by decide) true))
    (ORRoot c.program (c.outputs 0) ∪ ANDRoot c.program (c.outputs 0)) (fun _ h => h)

/-- One reconstruction pays for the NOT and both shared constants. Each tree's
contribution is its size minus its replacement size. -/
theorem mcsp_signedCopy_forest_budget (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) {source partner : Address}
    (hSource : source ∈ zeroBlock 30) :
    6444137669 + (actualForest c hc).savings (signedCopy source partner) ≤ c.size + 3 := by
  have h := rebuild_signedCopy (actualForest c hc) (foldKey 30) source (foldKey 30 partner)
  change complexity interpretation (single (Forest.wireFunction (p := c.program)
      (signedCopy source partner) (c.outputs 0))) + _ ≤ c.size + 3 at h
  have he : Forest.wireFunction (p := c.program) (signedCopy source partner) (c.outputs 0) =
      mcspSquare 32 ∘ signedCopy source partner := by
    funext U
    exact congrFun (hc (signedCopy source partner U)) 0
  rw [he] at h
  exact (Nat.add_le_add_right (mcsp_signedCopy_residual hSource) _).trans h

theorem signedCopy_beat_threshold (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) {source partner : Address}
    (hSource : source ∈ zeroBlock 30)
    (hSaving : 2148064437 ≤ (actualForest c hc).savings (signedCopy source partner)) :
    8592202103 ≤ c.size := by
  have h := mcsp_signedCopy_forest_budget c hc (partner := partner) hSource
  omega

theorem or_tree_collapses_of_signedCopy {g : ℕ} {p : Program signature (2 ^ 32) g}
    {output : Wire (2 ^ 32) g} {r : Fin g} {source partner : Address}
    (hs : source ∈ orInputs p output r) (hp : partner ∈ orInputs p output r)
    (hn : partner ≠ source) (U : Free → Bool) :
    p.trace interpretation (signedCopy source partner U) (.gate r) = true :=
  QuarterFold.or_root_constant_of_complementary_inputs hs hp (signedCopy_complementary hn) U

theorem and_tree_collapses_of_signedCopy {g : ℕ} {p : Program signature (2 ^ 32) g}
    {output : Wire (2 ^ 32) g} {r : Fin g} {source partner : Address}
    (hs : source ∈ andInputs p output r) (hp : partner ∈ andInputs p output r)
    (hn : partner ≠ source) (U : Free → Bool) :
    p.trace interpretation (signedCopy source partner U) (.gate r) = false :=
  QuarterFold.and_root_constant_of_complementary_inputs hs hp (signedCopy_complementary hn) U

/-- If the chosen source was kept, preserve its independent value at a deleted
reserve address. The partner still receives its ordinary unsigned value. -/
noncomputable def signedCopyWithReserve (source partner reserve : Address) : Fill :=
  fun U i => if i = source then !(U (foldKey 30 partner))
    else U (if i = reserve then foldKey 30 source else foldKey 30 i)

theorem reserveCopy_complementary {source partner reserve : Address}
    (hps : partner ≠ source) (hpr : partner ≠ reserve) (U : Free → Bool) :
    signedCopyWithReserve source partner reserve U source =
      !(signedCopyWithReserve source partner reserve U partner) := by
  simp [signedCopyWithReserve, hps, hpr]

theorem reserveCopy_residual {source partner reserve : Address}
    (hReserve : reserve ∈ zeroBlock 30) (hrs : reserve ≠ source) :
    6444137669 ≤ complexity interpretation
      (single (mcspSquare 32 ∘ signedCopyWithReserve source partner reserve)) := by
  classical
  apply residual_of_injective_edit _ {source, reserve}
  · exact (Finset.card_insert_le _ _).trans (by simp)
  · intro U V h
    funext j
    let i := (freeEquiv 30 j).val
    have hef : foldKey 30 i = j := QuarterFold.foldKey_at_retained 30 j
    have hir : i ≠ reserve := by
      intro he
      have hFalse : keptKey 30 reserve = false := (Finset.mem_filter.mp hReserve).2
      rw [← he, (freeEquiv 30 j).property] at hFalse
      cases hFalse
    by_cases his : i = source
    · have he := congrFun h reserve
      change signedCopyWithReserve source partner reserve U reserve =
        signedCopyWithReserve source partner reserve V reserve at he
      rw [his] at hef
      simpa [signedCopyWithReserve, hrs, hef] using he
    · have he := congrFun h i
      change signedCopyWithReserve source partner reserve U i =
        signedCopyWithReserve source partner reserve V i at he
      simpa only [signedCopyWithReserve, his, hir, ite_false, hef] using he
  · intro U i hi
    have his : i ≠ source := fun he => hi (he.symm ▸ Finset.mem_insert_self _ _)
    have hir : i ≠ reserve := fun he => hi (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    simp [signedCopyWithReserve, his, hir]

theorem reserveCopy_forest_budget (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) {source partner reserve : Address}
    (hReserve : reserve ∈ zeroBlock 30) (hrs : reserve ≠ source) :
    6444137669 + (actualForest c hc).savings (signedCopyWithReserve source partner reserve) ≤ c.size + 3 := by
  let parent : Address → Free := fun i => if i = reserve then foldKey 30 source else foldKey 30 i
  have h := rebuild_signedCopy (actualForest c hc) parent source (foldKey 30 partner)
  change complexity interpretation (single (Forest.wireFunction (p := c.program)
    (signedCopyWithReserve source partner reserve) (c.outputs 0))) + _ ≤ c.size + 3 at h
  have he : Forest.wireFunction (p := c.program) (signedCopyWithReserve source partner reserve) (c.outputs 0) =
      mcspSquare 32 ∘ signedCopyWithReserve source partner reserve := by
    funext U
    exact congrFun (hc (signedCopyWithReserve source partner reserve U)) 0
  rw [he] at h
  exact (Nat.add_le_add_right (reserveCopy_residual hReserve hrs) _).trans h

theorem reserveCopy_beat_threshold (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) {source partner reserve : Address}
    (hReserve : reserve ∈ zeroBlock 30) (hrs : reserve ≠ source)
    (hSaving : 2148064437 ≤ (actualForest c hc).savings (signedCopyWithReserve source partner reserve)) :
    8592202103 ≤ c.size := by
  have h := reserveCopy_forest_budget c hc (partner := partner) hReserve hrs
  omega

private theorem exists_reserve (source partner : Address) :
    ∃ reserve ∈ zeroBlock 30, reserve ≠ source ∧ reserve ≠ partner := by
  by_contra h
  have hSub : zeroBlock 30 ⊆ ({source, partner} : Finset Address) := by
    intro i hi
    by_cases hs : i = source
    · simp [hs]
    · have hp : i = partner := by
        by_contra hp
        exact h ⟨i, hi, hs, hp⟩
      simp [hp]
  have ha := Finset.card_le_card hSub
  have hb : ({source, partner} : Finset Address).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  rw [QuarterBlock.zeroBlock_card] at ha
  change 1073741824 ≤ _ at ha
  omega

/-- If the full-size target does not already hold, the verified forest must
have a component with two distinct raw leaves. -/
theorem exists_component_leaf_pair (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hSize : c.size ≤ 8592202102) :
    (∃ r ∈ ORRoot c.program (c.outputs 0), 1 < (orInputs c.program (c.outputs 0) r).card) ∨
    (∃ r ∈ ANDRoot c.program (c.outputs 0), 1 < (andInputs c.program (c.outputs 0) r).card) := by
  classical
  let p := c.program
  let root := c.outputs 0
  let O := ORRoot p root
  let A := ANDRoot p root
  let o := O.biUnion (orInputs p root)
  let a := A.biUnion (andInputs p root)
  let S := stopInputs p root
  have hF0 := mcspSquare_constant_table 32 (by decide) false
  have hF1 := mcspSquare_constant_table 32 (by decide) true
  have h0 : cornerValue p false root = true := (congrFun (hc _) 0).trans hF0
  have h1 : cornerValue p true root = true := (congrFun (hc _) 0).trans hF1
  have hSparse := card_accepting_mcspSquare_le 32
  rw [show descriptionBitBound 32 = 27672 by decide] at hSparse
  have hN0 := card_needInputs_ge_of_sparse c hc hSparse false hF0
  have hN1 := card_needInputs_ge_of_sparse c hc hSparse true hF1
  have hAcct := needInputs_add_slack_eq p root h0 h1
  have hSlack : slack p root ≤ 2322855 := by
    change 4294967296 ≤ (needInputs p root false).card + 27672 at hN0
    change 4294967296 ≤ (needInputs p root true).card + 27672 at hN1
    change (needInputs p root false).card + (needInputs p root true).card + slack p root = c.size + 1 at hAcct
    omega
  have hSC : S.card ≤ 117 * slack p root :=
    (Finset.card_le_card (stopInputs_subset_cutInputs p root)).trans (card_cutInputs_le_slack p root h0 h1)
  have hRoot : O.card + A.card ≤ 10 * 27672 + 1442 * slack p root :=
    card_orRoot_add_andRoot_le c hc hSparse hF0 hF1
  have hCover : needInputs p root false ⊆ S ∪ o ∪ a := by
    intro i hi
    rcases need_input_in_stop_or_forest h0 h1 hi with hs | ⟨r, hr, ho⟩ | ⟨r, hr, ha⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hs)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, ho⟩))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, ha⟩)
  by_contra h
  have hNoO (r : Fin c.size) (hr : r ∈ O) : (orInputs p root r).card ≤ 1 :=
    Nat.le_of_not_gt (fun he => h (Or.inl ⟨r, hr, he⟩))
  have hNoA (r : Fin c.size) (hr : r ∈ A) : (andInputs p root r).card ≤ 1 :=
    Nat.le_of_not_gt (fun he => h (Or.inr ⟨r, hr, he⟩))
  have ho : o.card ≤ O.card := by
    calc
      _ ≤ ∑ r ∈ O, (orInputs p root r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ O, 1 := Finset.sum_le_sum hNoO
      _ = _ := by simp
  have ha : a.card ≤ A.card := by
    calc
      _ ≤ ∑ r ∈ A, (andInputs p root r).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ A, 1 := Finset.sum_le_sum hNoA
      _ = _ := by simp
  have hUnion0 := Finset.card_union_le S o
  have hUnion1 := Finset.card_union_le (S ∪ o) a
  have hCov := Finset.card_le_card hCover
  change 4294967296 ≤ (needInputs p root false).card + 27672 at hN0
  omega

/-- Pick a pair from a component of the actual circuit, then choose a deleted
reserve address. This removes the chosen component as a whole. -/
theorem exists_wiring_chosen_fold (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) (hSize : c.size ≤ 8592202102) :
    ∃ (source partner reserve : Address) (r : Fin c.size),
      reserve ∈ zeroBlock 30 ∧ reserve ≠ source ∧ reserve ≠ partner ∧ source ≠ partner ∧
      r ∈ (actualForest c hc).roots ∧
      (actualForest c hc).replacementCost (signedCopyWithReserve source partner reserve) r = 0 ∧
      ((actualForest c hc).nodes r).card ≤ (actualForest c hc).savings
        (signedCopyWithReserve source partner reserve) := by
  rcases exists_component_leaf_pair c hc hSize with ⟨r, hr, hPair⟩ | ⟨r, hr, hPair⟩
  · obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hPair
    obtain ⟨v, hv, hvs, hvt⟩ := exists_reserve s t
    have hr' : r ∈ (actualForest c hc).roots := Finset.mem_union_left _ hr
    have he (U : Free → Bool) :
        Forest.wireFunction (p := c.program) (signedCopyWithReserve s t v) (.gate r) U = true :=
      QuarterFold.or_root_constant_of_complementary_inputs hs ht (reserveCopy_complementary hst.symm hvt.symm) U
    exact ⟨s, t, v, r, hv, hvs, hvt, hst, hr', (actualForest c hc).replacementCost_eq_zero_of_constant _ he,
      (actualForest c hc).component_le_savings_of_constant _ hr' he⟩
  · obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hPair
    obtain ⟨v, hv, hvs, hvt⟩ := exists_reserve s t
    have hr' : r ∈ (actualForest c hc).roots := Finset.mem_union_right _ hr
    have he (U : Free → Bool) :
        Forest.wireFunction (p := c.program) (signedCopyWithReserve s t v) (.gate r) U = false :=
      QuarterFold.and_root_constant_of_complementary_inputs hs ht (reserveCopy_complementary hst.symm hvt.symm) U
    exact ⟨s, t, v, r, hv, hvs, hvt, hst, hr', (actualForest c hc).replacementCost_eq_zero_of_constant _ he,
      (actualForest c hc).component_le_savings_of_constant _ hr' he⟩

#print axioms residual_of_modified_fold
#print axioms mcsp_signedCopy_forest_budget
#print axioms signedCopy_beat_threshold
#print axioms or_tree_collapses_of_signedCopy
#print axioms and_tree_collapses_of_signedCopy

#print axioms reserveCopy_forest_budget
#print axioms reserveCopy_beat_threshold
#print axioms exists_wiring_chosen_fold

end PvsNP.Frontier.QuarterForest
