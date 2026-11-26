module

public import PvsNP.ReachableSemanticBarrier

@[expose] public section

open Filter

namespace PvsNP

/-!
# Algebraic Degree Barrier (`ℤ/2ℤ` ANF) and Hamming-Weight Conservation

Closes the $\mathbb{F}_2$-linear loophole of `ClosedComparatorXor` along both algebraic and
combinatorial axes:

1. **Exact $\mathbb{F}_2$ Algebraic Normal Form (`anfCoeff`, `anf_eval`, `anfDegree`)**:
   Formalizes Möbius inversion over `Finset (Fin n)` in `ZMod 2`, proving exact ANF expansion
   (`anf_eval`), `anfDegree (ClosedComparatorXor.source d).eval = 1`
   (`ClosedComparatorXor.output_anfDegree_eq`), and `anfDegree (allAnd n) = n`
   (`anfDegree_allAnd_eq`).
2. **Exact Integer Hamming-Weight Conservation (`ClosedComparatorXor.layer_hammingWeight_invariant`)**:
   Every layer `ℓ ≤ d` of the comparator butterfly conserves exact `ℕ` Hamming weight
   (`(a && b).toNat + (a || b).toNat = a.toNat + b.toNat`), implying all-true equivalence at every
   layer (`ClosedComparatorXor.layer_allTrue_iff`).
3. **Closed Purely Nonlinear Comparator-AND Butterfly (`ClosedComparatorAnd.source d`)**:
   Replaces the `(2 ^ d - 1)` `XOR` reduction gates with `AND` gates (`HybridGate.and`) and proves:
   - 100% single-output reachability (`all_wires_reachable`);
   - 100% nonlinear gates (`(d + 1) * 2 ^ d - 1`, `nonlinearCount_eq`, `escapes_sublinear_nonlinear`);
   - $\Omega(2 ^ d)$ treewidth and binary gate contraction width (`treewidth_linear`,
     `gateContractionWidth_linear`);
   - 100% pairwise semantic distinctness across all `(d + 1) * 2 ^ d` butterfly wires
     (`bfly_wires_pairwise_distinct`);
   - Maximal algebraic degree `anfDegree (source d).eval = 2 ^ d` (`output_anfDegree_eq`);
   - Exact `#Circuit-SAT` collapse `Fintype.card { x // (source d).eval x = true } = 1`
     (`acceptCount_eq`).
-/

section AlgebraicNormalForm

private lemma zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl <;> decide

/-- Exact `ℤ/2ℤ` Möbius / ANF coefficient of Boolean function `f` on monomial `S : Finset (Fin n)`. -/
def anfCoeff {n : Nat} (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)) : ZMod 2 :=
  ∑ T ∈ S.powerset, boolToZMod2 (f fun i => decide (i ∈ T))

/-- Algebraic degree (maximum monomial weight with nonzero `ℤ/2ℤ` ANF coefficient). -/
def anfDegree {n : Nat} (f : (Fin n → Bool) → Bool) : Nat :=
  open Classical in
  ((Finset.univ : Finset (Finset (Fin n))).filter fun S => anfCoeff f S ≠ 0).sup Finset.card

/-- Characteristic `2` powerset parity identity: `∑ T ∈ A.powerset, (1 : ZMod 2) = 1` iff `A = ∅`. -/
lemma powerset_card_zmod2 {α : Type*} [DecidableEq α] (A : Finset α) :
    (∑ _T ∈ A.powerset, (1 : ZMod 2)) = if A = ∅ then 1 else 0 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hNe : insert a s ≠ ∅ := Finset.insert_ne_empty a s
      simp only [hNe, ↓reduceIte]
      rw [Finset.powerset_insert s a]
      have hDisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro t htS htImg
        rw [Finset.mem_image] at htImg
        rcases htImg with ⟨u, _, rfl⟩
        rw [Finset.mem_powerset] at htS
        exact ha (htS (Finset.mem_insert_self a u))
      rw [Finset.sum_union hDisj]
      have hInj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
        intro u hu v hv hEq
        rw [Finset.mem_coe, Finset.mem_powerset] at hu hv
        have hua : a ∉ u := fun h => ha (hu h)
        have hva : a ∉ v := fun h => ha (hv h)
        ext x
        by_cases hxa : x = a
        · subst hxa; exact iff_of_false hua hva
        · have := congrArg (fun S => x ∈ S) hEq
          simpa [Finset.mem_insert, hxa] using this
      rw [Finset.sum_image hInj]
      exact zmod2_add_self _

private lemma powerset_interval_sum_zmod2 {α : Type*} [DecidableEq α] (T A : Finset α)
    (hTA : T ⊆ A) :
    (∑ S ∈ A.powerset, if T ⊆ S then (1 : ZMod 2) else 0) = if T = A then 1 else 0 := by
  have hFilt : (∑ S ∈ A.powerset, if T ⊆ S then (1 : ZMod 2) else 0) =
      ∑ _S ∈ (A.powerset.filter (fun S => T ⊆ S)), (1 : ZMod 2) := by
    rw [Finset.sum_filter]
  rw [hFilt]
  have hBij : (∑ _S ∈ (A.powerset.filter (fun S => T ⊆ S)), (1 : ZMod 2)) =
      ∑ _U ∈ (A \ T).powerset, (1 : ZMod 2) := by
    refine Finset.sum_bij (fun S _ => S \ T) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro S hS
      rw [Finset.mem_filter] at hS
      rw [Finset.mem_powerset]
      exact Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp hS.1) le_rfl
    · intro S₁ hS₁ S₂ hS₂ hEq
      rw [Finset.mem_filter] at hS₁ hS₂
      calc
        S₁ = (S₁ \ T) ∪ T := (Finset.sdiff_union_of_subset hS₁.2).symm
        _ = (S₂ \ T) ∪ T := by rw [hEq]
        _ = S₂ := Finset.sdiff_union_of_subset hS₂.2
    · intro U hU
      rw [Finset.mem_powerset] at hU
      refine ⟨T ∪ U, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_left⟩, ?_⟩
      · exact Finset.union_subset hTA (hU.trans Finset.sdiff_subset)
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxT | hxU, hxNotT⟩
          · exact False.elim (hxNotT hxT)
          · exact hxU
        · intro hxU
          have hxDiff := hU hxU
          rw [Finset.mem_sdiff] at hxDiff
          exact ⟨Or.inr hxU, hxDiff.2⟩
  rw [hBij, powerset_card_zmod2]
  have hDiffIff : A \ T = ∅ ↔ T = A := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => Finset.Subset.antisymm hTA h, fun h => h ▸ le_rfl⟩
  by_cases hEq : T = A
  · have hEmpty : A \ T = ∅ := hDiffIff.mpr hEq
    simp [hEq]
  · have hNotEmpty : A \ T ≠ ∅ := fun h => hEq (hDiffIff.mp h)
    simp [hEq, hNotEmpty]

/-- **Exact ANF Evaluation Theorem**: every Boolean function `f : (Fin n → Bool) → Bool` equals its
`ℤ/2ℤ` multilinear ANF polynomial `∑ S, anfCoeff f S * ∏_{i ∈ S} x_i` on every input `x`. -/
theorem anf_eval {n : Nat} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    boolToZMod2 (f x) =
      ∑ S : Finset (Fin n), anfCoeff f S * (if ∀ i ∈ S, x i = true then 1 else 0) := by
  let A : Finset (Fin n) := Finset.univ.filter fun i => x i = true
  have hxA : ∀ S : Finset (Fin n), (∀ i ∈ S, x i = true) ↔ S ⊆ A := by
    intro S
    simp only [Finset.subset_iff, A, Finset.mem_filter, Finset.mem_univ, true_and]
  have hRHS1 :
      (∑ S : Finset (Fin n), anfCoeff f S * (if ∀ i ∈ S, x i = true then 1 else 0)) =
        ∑ S ∈ A.powerset, anfCoeff f S := by
    symm
    calc
      ∑ S ∈ A.powerset, anfCoeff f S
        = ∑ S ∈ A.powerset, anfCoeff f S * (if ∀ i ∈ S, x i = true then 1 else 0) := by
            refine Finset.sum_congr rfl fun S hS => ?_
            rw [Finset.mem_powerset] at hS
            have hSub : ∀ i ∈ S, x i = true := (hxA S).mpr hS
            split_ifs
            exact (mul_one _).symm
      _ = ∑ S : Finset (Fin n), anfCoeff f S * (if ∀ i ∈ S, x i = true then 1 else 0) := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro S _ hNot
            rw [Finset.mem_powerset] at hNot
            have hNotAll : ¬ ∀ i ∈ S, x i = true := fun h => hNot ((hxA S).mp h)
            split_ifs
            exact mul_zero _
  rw [hRHS1]
  have hExpand :
      (∑ S ∈ A.powerset, anfCoeff f S) =
        ∑ S ∈ A.powerset, ∑ T ∈ A.powerset,
          if T ⊆ S then boolToZMod2 (f fun i => decide (i ∈ T)) else 0 := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    dsimp [anfCoeff]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext T
    rw [Finset.mem_powerset, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => ⟨h.trans hS, h⟩, fun h => h.2⟩
  rw [hExpand, Finset.sum_comm]
  have hInner :
      (∑ T ∈ A.powerset, ∑ S ∈ A.powerset,
          if T ⊆ S then boolToZMod2 (f fun i => decide (i ∈ T)) else 0) =
        ∑ T ∈ A.powerset,
          boolToZMod2 (f fun i => decide (i ∈ T)) *
            (if T = A then 1 else 0) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    have hFactor :
        (∑ S ∈ A.powerset,
            if T ⊆ S then boolToZMod2 (f fun i => decide (i ∈ T)) else 0) =
          boolToZMod2 (f fun i => decide (i ∈ T)) *
            (∑ S ∈ A.powerset, if T ⊆ S then (1 : ZMod 2) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp
    rw [hFactor, powerset_interval_sum_zmod2 T A hT]
  rw [hInner]
  have hCollapse :
      (∑ T ∈ A.powerset,
          boolToZMod2 (f fun i => decide (i ∈ T)) *
            (if T = A then 1 else 0)) =
        boolToZMod2 (f fun i => decide (i ∈ A)) := by
    rw [Finset.sum_eq_single A]
    · simp
    · intro T _ hNe
      simp [hNe]
    · intro hNot
      exact False.elim (hNot (Finset.mem_powerset.mpr le_rfl))
  rw [hCollapse]
  have hxEq : (fun i : Fin n => decide (i ∈ A)) = x := by
    funext i
    dsimp [A]
    cases hxi : x i <;> simp [hxi]
  rw [hxEq]

/-- Degree of any `n`-variable Boolean function is bounded by `n`. -/
theorem anfDegree_le {n : Nat} (f : (Fin n → Bool) → Bool) : anfDegree f ≤ n := by
  classical
  unfold anfDegree
  rw [Finset.sup_le_iff]
  intro S _
  exact (Finset.card_le_univ S).trans (by simp)

private lemma powerset_mem_sum_zmod2 {n : Nat} (S : Finset (Fin n)) (i : Fin n) :
    (∑ T ∈ S.powerset, boolToZMod2 (decide (i ∈ T))) =
      if i ∈ S ∧ S.card = 1 then 1 else 0 := by
  by_cases hi : i ∈ S
  · have hEq : (∑ T ∈ S.powerset, boolToZMod2 (decide (i ∈ T))) =
        ∑ _T ∈ (S.powerset.filter (fun T => i ∈ T)), (1 : ZMod 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hT : i ∈ T <;> simp [hT, boolToZMod2]
    rw [hEq]
    have hBij : (∑ _T ∈ (S.powerset.filter (fun T => i ∈ T)), (1 : ZMod 2)) =
        ∑ _U ∈ (S.erase i).powerset, (1 : ZMod 2) := by
      refine Finset.sum_bij (fun T _ => T.erase i) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro T hT
        rw [Finset.mem_filter] at hT
        rw [Finset.mem_powerset]
        exact Finset.erase_subset_erase i (Finset.mem_powerset.mp hT.1)
      · intro T₁ hT₁ T₂ hT₂ hEq'
        rw [Finset.mem_filter] at hT₁ hT₂
        calc
          T₁ = insert i (T₁.erase i) := (Finset.insert_erase hT₁.2).symm
          _ = insert i (T₂.erase i) := by rw [hEq']
          _ = T₂ := Finset.insert_erase hT₂.2
      · intro U hU
        rw [Finset.mem_powerset] at hU
        refine ⟨insert i U, Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨hi, hU.trans (Finset.erase_subset i S)⟩),
             Finset.mem_insert_self i U⟩, ?_⟩
        exact Finset.erase_insert (fun h => Finset.notMem_erase i S (hU h))
    rw [hBij, powerset_card_zmod2]
    have hEraseIff : S.erase i = ∅ ↔ S.card = 1 := by
      constructor
      · intro hEmpty
        have hSub : S.card - 1 = 0 := by
          have := Finset.card_erase_of_mem hi
          rw [hEmpty, Finset.card_empty] at this
          exact this.symm
        have hPos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      · intro hCard
        rw [Finset.card_eq_one] at hCard
        rcases hCard with ⟨j, rfl⟩
        rw [Finset.mem_singleton] at hi
        subst hi
        exact Finset.erase_singleton i
    by_cases hCard : S.card = 1
    · have hE : S.erase i = ∅ := hEraseIff.mpr hCard
      simp [hi, hCard, hE]
    · have hNE : S.erase i ≠ ∅ := fun h => hCard (hEraseIff.mp h)
      simp [hi, hCard, hNE]
  · have hZero : ∀ T ∈ S.powerset, boolToZMod2 (decide (i ∈ T)) = 0 := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      have hNot : i ∉ T := fun h => hi (hT h)
      simp [hNot, boolToZMod2]
    rw [Finset.sum_eq_zero hZero]
    simp [hi]

/-- ANF coefficients of any exact `ℤ/2ℤ`-linear parity function are supported exclusively on
singletons (`S.card = 1`). -/
theorem anfCoeff_parity_eq {n : Nat} (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, boolToZMod2 (f x) = ∑ i : Fin n, boolToZMod2 (x i))
    (S : Finset (Fin n)) :
    anfCoeff f S = if S.card = 1 then 1 else 0 := by
  dsimp [anfCoeff]
  simp_rw [hf]
  rw [Finset.sum_comm]
  simp_rw [powerset_mem_sum_zmod2]
  by_cases hCard : S.card = 1
  · simp only [hCard, ↓reduceIte, and_true]
    rcases Finset.card_eq_one.mp hCard with ⟨i₀, rfl⟩
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro i _ hNe
      simp [hNe]
    · intro hNot
      exact False.elim (hNot (Finset.mem_univ i₀))
  · simp only [hCard, ↓reduceIte, and_false]
    simp

/-- Every `n`-variable parity function (`1 ≤ n`) has exact ANF degree `1`. -/
theorem anfDegree_parity_eq {n : Nat} (hn : 1 ≤ n) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, boolToZMod2 (f x) = ∑ i : Fin n, boolToZMod2 (x i)) :
    anfDegree f = 1 := by
  classical
  unfold anfDegree
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro S hS
    rw [Finset.mem_filter, anfCoeff_parity_eq f hf S] at hS
    by_cases h1 : S.card = 1
    · omega
    · simp [h1] at hS
  · have hMem : ({⟨0, hn⟩} : Finset (Fin n)) ∈
        ((Finset.univ : Finset (Finset (Fin n))).filter fun S => anfCoeff f S ≠ 0) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [anfCoeff_parity_eq f hf]
      simp
    exact Finset.le_sup (f := Finset.card) hMem

/-- `ClosedComparatorXor.source d` has exact `ℤ/2ℤ` algebraic degree `1`. -/
theorem ClosedComparatorXor.output_anfDegree_eq (d : Nat) :
    anfDegree (ClosedComparatorXor.source d).eval = 1 :=
  anfDegree_parity_eq (Nat.two_pow_pos d) (ClosedComparatorXor.source d).eval
    (ClosedComparatorXor.source_eval_zmod2 d)

/-- Full `n`-input conjunction `x ↦ ⋀_i x_i`. -/
def allAnd (n : Nat) (x : Fin n → Bool) : Bool :=
  decide (∀ i : Fin n, x i = true)

/-- Exact ANF coefficients of `allAnd n`: nonzero only at the top monomial `S = Finset.univ`. -/
theorem anfCoeff_allAnd (n : Nat) (S : Finset (Fin n)) :
    anfCoeff (allAnd n) S = if S = Finset.univ then 1 else 0 := by
  dsimp [anfCoeff, allAnd]
  by_cases hUniv : S = Finset.univ
  · subst hUniv
    rw [Finset.sum_eq_single (Finset.univ : Finset (Fin n))]
    · simp [boolToZMod2]
    · intro T _ hNe
      have hNotAll : ¬ ∀ i : Fin n, decide (i ∈ T) = true := by
        intro hAll
        apply hNe
        ext i
        exact ⟨fun _ => Finset.mem_univ i, fun _ => decide_eq_true_iff.mp (hAll i)⟩
      rw [decide_eq_false hNotAll]
      decide
    · intro hNot
      exact False.elim (hNot (Finset.mem_powerset.mpr le_rfl))
  · simp only [hUniv, ↓reduceIte]
    refine Finset.sum_eq_zero fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    have hNotAll : ¬ ∀ i : Fin n, decide (i ∈ T) = true := by
      intro hAll
      apply hUniv
      ext i
      exact ⟨fun _ => Finset.mem_univ i, fun _ => hT (decide_eq_true_iff.mp (hAll i))⟩
    rw [decide_eq_false hNotAll]
    decide

/-- `allAnd n` achieves the maximal `ℤ/2ℤ` ANF degree `n`. -/
theorem anfDegree_allAnd_eq (n : Nat) : anfDegree (allAnd n) = n := by
  classical
  unfold anfDegree
  apply le_antisymm
  · rw [Finset.sup_le_iff]
    intro S _
    exact (Finset.card_le_univ S).trans (by simp)
  · have hMem : (Finset.univ : Finset (Fin n)) ∈
        ((Finset.univ : Finset (Finset (Fin n))).filter fun S => anfCoeff (allAnd n) S ≠ 0) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [anfCoeff_allAnd]
      simp
    calc
      n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ _ := Finset.le_sup (f := Finset.card) hMem

end AlgebraicNormalForm

section HammingConservation

private lemma toNat_and_add_or (a b : Bool) : (a && b).toNat + (a || b).toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> decide

private lemma sum_pair_flipBit_nat {d ℓ : Nat} (hℓ : ℓ < d) (f : Fin (2 ^ d) → Nat) :
    ∑ j : Fin (2 ^ d), f j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ d) => j.val.testBit ℓ = false),
        (f j + f ⟨ButterflyNet.flipBit j.val ℓ, ButterflyNet.flipBit_lt j.isLt hℓ⟩) := by
  classical
  let S₀ := Finset.univ.filter (fun j : Fin (2 ^ d) => j.val.testBit ℓ = false)
  let S₁ := Finset.univ.filter (fun j : Fin (2 ^ d) => ¬ (j.val.testBit ℓ = false))
  have hSplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin (2 ^ d)))
    (fun j : Fin (2 ^ d) => j.val.testBit ℓ = false) f
  have hPair : ∑ j ∈ S₁, f j =
      ∑ j ∈ S₀, f ⟨ButterflyNet.flipBit j.val ℓ, ButterflyNet.flipBit_lt j.isLt hℓ⟩ := by
    refine (Finset.sum_bij
      (fun j _ => ⟨ButterflyNet.flipBit j.val ℓ, ButterflyNet.flipBit_lt j.isLt hℓ⟩)
      ?_ ?_ ?_ (fun _ _ => rfl)).symm
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [ButterflyNet.flipBit_testBit_self, hj.2]
      decide
    · intro a _ b _ hEq
      have hVal := congrArg Fin.val hEq
      dsimp at hVal
      have hInv := congrArg (fun z => ButterflyNet.flipBit z ℓ) hVal
      rw [ButterflyNet.flipBit_involutive, ButterflyNet.flipBit_involutive] at hInv
      exact Fin.ext hInv
    · intro y hy
      rw [Finset.mem_filter] at hy
      have hyT : y.val.testBit ℓ = true := Bool.eq_true_of_not_eq_false hy.2
      refine ⟨⟨ButterflyNet.flipBit y.val ℓ, ButterflyNet.flipBit_lt y.isLt hℓ⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [ButterflyNet.flipBit_testBit_self, hyT]; rfl⟩
      · exact Fin.ext (ButterflyNet.flipBit_involutive y.val ℓ)
  rw [← hSplit, hPair, ← Finset.sum_add_distrib]

/-- **Exact Integer Hamming-Weight Conservation**: at every layer `ℓ ≤ d` of `buildCompBfly`,
the number of `true` wires equals the Hamming weight `∑ x_j.toNat` of the input. -/
theorem ClosedComparatorXor.layer_hammingWeight_invariant (d ℓ : Nat) (hℓ : ℓ ≤ d)
    (x : Fin (2 ^ d) → Bool) :
    ∑ j : Fin (2 ^ d),
        ((ClosedComparatorXor.buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j.val, by
          rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩).toNat =
      ∑ j : Fin (2 ^ d), (x j).toNat := by
  induction ℓ with
  | zero =>
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ClosedComparatorXor.buildCompBfly, HybridCircuit.evalWires]
      exact congrArg Bool.toNat (congrArg x (Fin.ext (by simp)))
  | succ ℓ ih =>
      rw [sum_pair_flipBit_nat hℓ, ← ih (Nat.le_of_lt hℓ), sum_pair_flipBit_nat hℓ]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_filter] at hj
      have hjFalse : j.val.testBit ℓ = false := hj.2
      have hFlipLt := ButterflyNet.flipBit_lt j.isLt hℓ
      have hj'True : (ButterflyNet.flipBit j.val ℓ).testBit ℓ = true := by
        rw [ButterflyNet.flipBit_testBit_self, hjFalse]
        rfl
      rw [ClosedComparatorXor.buildCompBfly_eval_succ d ℓ j.val hℓ j.isLt x,
        ClosedComparatorXor.buildCompBfly_eval_succ d ℓ _ hℓ hFlipLt x]
      simp only [hjFalse, ↓reduceIte, hj'True, Bool.true_eq_false]
      have hInv : ButterflyNet.flipBit (ButterflyNet.flipBit j.val ℓ) ℓ = j.val :=
        ButterflyNet.flipBit_involutive j.val ℓ
      have hB : (ClosedComparatorXor.buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x
          ⟨ℓ * 2 ^ d + ButterflyNet.flipBit (ButterflyNet.flipBit j.val ℓ) ℓ, by
            rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ =
          (ClosedComparatorXor.buildCompBfly d ℓ (Nat.le_of_lt hℓ)).evalWires x
            ⟨ℓ * 2 ^ d + j.val, by rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ := by
        congr 1; exact Fin.ext (by simp [hInv])
      rw [hB, Bool.or_comm, toNat_and_add_or]

/-- At any layer `ℓ ≤ d` of `buildCompBfly`, all `2 ^ d` wires evaluate to `true` if and only
if every input bit is `true`. -/
theorem ClosedComparatorXor.layer_allTrue_iff (d ℓ : Nat) (hℓ : ℓ ≤ d)
    (x : Fin (2 ^ d) → Bool) :
    (∀ j : Fin (2 ^ d),
        (ClosedComparatorXor.buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j.val, by
          rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ = true) ↔
      (∀ i : Fin (2 ^ d), x i = true) := by
  have hSumBool : ∀ (f : Fin (2 ^ d) → Bool),
      (∑ j : Fin (2 ^ d), (f j).toNat = 2 ^ d) ↔ (∀ j : Fin (2 ^ d), f j = true) := by
    intro f
    constructor
    · intro hEq j
      by_contra hjFalse
      have hjF : f j = false := Bool.eq_false_iff.mpr hjFalse
      have hj0 : (f j).toNat = 0 := by simp [hjF]
      have hErase := Finset.add_sum_erase Finset.univ (fun q => (f q).toNat) (Finset.mem_univ j)
      have hRest : ∑ q ∈ Finset.univ.erase j, (f q).toNat ≤ 2 ^ d - 1 := by
        calc
          ∑ q ∈ Finset.univ.erase j, (f q).toNat
            ≤ ∑ _q ∈ Finset.univ.erase j, 1 := Finset.sum_le_sum fun q _ => by
                cases f q <;> decide
          _ = (Finset.univ.erase j).card := by simp
          _ = 2 ^ d - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
      have hPos := Nat.two_pow_pos d
      omega
    · intro hAll
      calc
        ∑ j : Fin (2 ^ d), (f j).toNat = ∑ _j : Fin (2 ^ d), 1 :=
          Finset.sum_congr rfl fun j _ => by simp [hAll j]
        _ = 2 ^ d := by simp
  have hInv := ClosedComparatorXor.layer_hammingWeight_invariant d ℓ hℓ x
  rw [← hSumBool, hInv, hSumBool]

end HammingConservation

namespace ClosedComparatorAnd

open ClosedComparatorXor

/-- Appends `m` `AND` reduction gates (`0 ≤ m ≤ 2 ^ d - 1`) on top of the comparator butterfly,
wiring internal heap node `p = 2 ^ d - 1 - m` to `2 * p` and `2 * p + 1`. -/
def appendAndGates (d : Nat) :
    ∀ m, m ≤ 2 ^ d - 1 → HybridCircuit (2 ^ d) (LayeredRing.ringWires (2 ^ d) d + m)
  | 0, _ => buildCompBfly d d le_rfl
  | m + 1, hm =>
      let prev := appendAndGates d m (Nat.le_of_lt hm)
      let p := 2 ^ d - 1 - m
      let g : HybridGate (LayeredRing.ringWires (2 ^ d) d + m) :=
        HybridGate.and
          ⟨heapWireVal d (2 * p), heapWireVal_lt_xorStep d m (2 * p) hm (Or.inl rfl)⟩
          ⟨heapWireVal d (2 * p + 1), heapWireVal_lt_xorStep d m (2 * p + 1) hm (Or.inr rfl)⟩
      prev.snoc g

/-- Closed single-output comparator-AND butterfly circuit instance on `2 ^ d` inputs: purely
nonlinear (`AND`/`OR` only, zero `XOR` gates). -/
def source (d : Nat) : HybridCircuitInstance (2 ^ d) where
  wires := LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1)
  circuit := appendAndGates d (2 ^ d - 1) le_rfl
  output := ⟨LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) - 1, by
    have hBase := LayeredRing.ringWires_eq (2 ^ d) d
    have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
    have hWPos : 1 ≤ (d + 1) * 2 ^ d :=
      le_trans hPos (Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d))
    omega⟩

lemma source_wires_eq (d : Nat) : (source d).wires = totalWires d := by
  change LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) = (d + 2) * 2 ^ d - 1
  rw [LayeredRing.ringWires_eq]
  have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hMul : (d + 1) * 2 ^ d + 2 ^ d = (d + 2) * 2 ^ d := by ring
  omega

lemma source_output_val (d : Nat) : (source d).output.val = heapWireVal d 1 := by
  change LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) - 1 = heapWireVal d 1
  rw [LayeredRing.ringWires_eq]
  dsimp [heapWireVal]
  by_cases hd : d = 0
  · subst hd; decide
  · have hGt : 1 < 2 ^ d := Nat.one_lt_two_pow hd
    simp only [hGt, ↓reduceIte]
    have hMul : (d + 1) * 2 ^ d + 2 ^ d = (d + 2) * 2 ^ d := by ring
    omega

/-- Butterfly wire `(ℓ, j)` inside `ClosedComparatorAnd.source d`. -/
def compWireInSource (d ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d) : Fin (source d).wires :=
  ⟨ℓ * 2 ^ d + j, by
    change _ < LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1)
    rw [LayeredRing.ringWires_eq]
    have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
    have h2 : (ℓ + 1) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (Nat.succ_le_succ hℓ)
    omega⟩

private lemma appendAndGates_directedEdge_of_prev (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    {u v : Fin (LayeredRing.ringWires (2 ^ d) d)}
    (h : (buildCompBfly d d le_rfl).DirectedEdge u v) :
    (appendAndGates d m hm).DirectedEdge
      ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ m)⟩
      ⟨v.val, Nat.lt_of_lt_of_le v.isLt (Nat.le_add_right _ m)⟩ := by
  induction m with
  | zero => exact h
  | succ m ih =>
      dsimp [appendAndGates]
      exact HybridCircuit.directedEdge_snoc_castSucc (ih (Nat.le_of_lt hm))

private lemma appendAndGates_directedEdge_step (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    (h : Nat) (hh1 : 2 ≤ h) (hh2 : 2 ^ d - m ≤ h / 2) (hh3 : h < 2 ^ (d + 1)) :
    have hBase : LayeredRing.ringWires (2 ^ d) d = (d + 1) * 2 ^ d :=
      LayeredRing.ringWires_eq (2 ^ d) d
    have hU : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
      rw [hBase]
      dsimp [heapWireVal]
      have hMul1 : d * 2 ^ d + 2 ^ d = (d + 1) * 2 ^ d := by ring
      have hMul2 : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      split_ifs <;> omega
    have hV : heapWireVal d (h / 2) < LayeredRing.ringWires (2 ^ d) d + m := by
      rw [hBase]
      have hSub : h / 2 < 2 ^ d := by
        rw [Nat.pow_succ, Nat.mul_two] at hh3
        omega
      dsimp [heapWireVal]
      simp only [hSub, ↓reduceIte]
      have hMul2 : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      omega
    (appendAndGates d m hm).DirectedEdge ⟨heapWireVal d h, hU⟩ ⟨heapWireVal d (h / 2), hV⟩ := by
  induction m with
  | zero => omega
  | succ m ih =>
      intro hBase hU hV
      dsimp [appendAndGates]
      set p := 2 ^ d - 1 - m
      by_cases hEq : h / 2 = p
      · have hStep : heapWireVal d (h / 2) = LayeredRing.ringWires (2 ^ d) d + m := by
          rw [hBase, hEq]
          have hpLt : p < 2 ^ d := by
            have := Nat.two_pow_pos d
            omega
          dsimp [heapWireVal]
          simp only [hpLt, ↓reduceIte]
          have hMul2 : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
          omega
        have hvLast : (⟨heapWireVal d (h / 2), hV⟩ :
            Fin (LayeredRing.ringWires (2 ^ d) d + (m + 1))) = Fin.last _ :=
          Fin.ext (by simp [hStep])
        have hULT : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
          have : h = 2 * p ∨ h = 2 * p + 1 := by omega
          exact heapWireVal_lt_xorStep d m h hm this
        have hUses : HybridGateUsesWire
            (HybridGate.and
              ⟨heapWireVal d (2 * p), heapWireVal_lt_xorStep d m (2 * p) hm (Or.inl rfl)⟩
              ⟨heapWireVal d (2 * p + 1), heapWireVal_lt_xorStep d m (2 * p + 1) hm (Or.inr rfl)⟩)
            ⟨heapWireVal d h, hULT⟩ := by
          rcases (show h = 2 * p ∨ h = 2 * p + 1 by omega) with hL | hR
          · exact (congrArg (HybridGateUsesWire _) (Fin.ext (by simp [hL]))).mpr
              (HybridGateUsesWire.and_left _ _)
          · exact (congrArg (HybridGateUsesWire _) (Fin.ext (by simp [hR]))).mpr
              (HybridGateUsesWire.and_right _ _)
        rw [hvLast]
        exact HybridCircuit.directedEdge_snoc_last hUses
      · have hh2' : 2 ^ d - m ≤ h / 2 := by omega
        exact HybridCircuit.directedEdge_snoc_castSucc (ih (Nat.le_of_lt hm) hh2')

/-- **100% Reachability**: every wire in `ClosedComparatorAnd.source d` reaches `output`. -/
theorem all_wires_reachable (d : Nat) (u : Fin (source d).wires) :
    (source d).circuit.DirectedReach u (source d).output := by
  have hBase : LayeredRing.ringWires (2 ^ d) d = (d + 1) * 2 ^ d :=
    LayeredRing.ringWires_eq (2 ^ d) d
  have hHeapReach : ∀ h (hh1 : 1 ≤ h) (hh2 : h < 2 ^ (d + 1)),
      ∃ hu : heapWireVal d h < (source d).wires,
        (source d).circuit.DirectedReach ⟨heapWireVal d h, hu⟩ (source d).output := by
    intro h
    induction h using Nat.strong_induction_on with
    | h h ih =>
        intro hh1 hh2
        by_cases h1 : h = 1
        · subst h1
          refine ⟨by rw [← source_output_val]; exact (source d).output.isLt, ?_⟩
          have hOut : (⟨heapWireVal d 1, by rw [← source_output_val]; exact (source d).output.isLt⟩ :
              Fin (source d).wires) = (source d).output := Fin.ext (source_output_val d).symm
          rw [hOut]
          exact Relation.ReflTransGen.refl
        · have hhGe2 : 2 ≤ h := by omega
          have hp1 : 1 ≤ h / 2 := by omega
          have hp2 : h / 2 < 2 ^ (d + 1) := by omega
          have hpLt : h / 2 < h := Nat.div_lt_self (by omega) (by decide)
          obtain ⟨hpW, hpReach⟩ := ih (h / 2) hpLt hp1 hp2
          have hh2m : 2 ^ d - (2 ^ d - 1) ≤ h / 2 := by
            have := Nat.two_pow_pos d
            omega
          have hEdge := appendAndGates_directedEdge_step d (2 ^ d - 1) le_rfl h hhGe2 hh2m hh2
          exact ⟨_, Relation.ReflTransGen.head hEdge hpReach⟩
  have hBflyReach : ∀ m (ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d) (hm : m = d - ℓ),
      ∃ hu : ℓ * 2 ^ d + j < (source d).wires,
        (source d).circuit.DirectedReach ⟨ℓ * 2 ^ d + j, hu⟩ (source d).output := by
    intro m
    induction m with
    | zero =>
        intro ℓ j hℓ hj hm
        have hEq : ℓ = d := by omega
        subst hEq
        have hh1 : 1 ≤ 2 ^ ℓ + j := by
          have := Nat.two_pow_pos ℓ
          omega
        have hh2 : 2 ^ ℓ + j < 2 ^ (ℓ + 1) := by
          rw [Nat.pow_succ, Nat.mul_two]
          omega
        obtain ⟨hW, hReach⟩ := hHeapReach (2 ^ ℓ + j) hh1 hh2
        have hVal : heapWireVal ℓ (2 ^ ℓ + j) = ℓ * 2 ^ ℓ + j := by
          dsimp [heapWireVal]
          have hNot : ¬ (2 ^ ℓ + j < 2 ^ ℓ) := by omega
          simp only [hNot, ↓reduceIte, Nat.add_sub_cancel_left]
        refine ⟨by rw [← hVal]; exact hW, ?_⟩
        convert hReach using 1
        exact Fin.ext hVal.symm
    | succ m ih =>
        intro ℓ j hℓ hj hm
        have hℓLt : ℓ < d := by omega
        obtain ⟨hNextW, hNextReach⟩ := ih (ℓ + 1) j hℓLt hj (by omega)
        have hCurLt : ℓ * 2 ^ d + j < LayeredRing.ringWires (2 ^ d) d := by
          rw [hBase]
          have : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
          have : (ℓ + 1) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
          omega
        have hNextLt : (ℓ + 1) * 2 ^ d + j < LayeredRing.ringWires (2 ^ d) d := by
          rw [hBase]
          have : (ℓ + 1) * 2 ^ d + 2 ^ d = (ℓ + 2) * 2 ^ d := by ring
          have : (ℓ + 2) * 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.mul_le_mul_right _ (by omega)
          omega
        have hEdgeB := buildCompBfly_directedEdge_of_bflyStep d d le_rfl
          ⟨ℓ * 2 ^ d + j, hCurLt⟩ ⟨(ℓ + 1) * 2 ^ d + j, hNextLt⟩
          ⟨ℓ, j, hℓLt, hj, rfl, Or.inl rfl⟩
        have hEdgeS := appendAndGates_directedEdge_of_prev d (2 ^ d - 1) le_rfl hEdgeB
        exact ⟨_, Relation.ReflTransGen.head hEdgeS hNextReach⟩
  have hUlt : u.val < (d + 2) * 2 ^ d - 1 := by
    simpa [source_wires_eq, totalWires] using u.isLt
  by_cases hInBfly : u.val < (d + 1) * 2 ^ d
  · have hPos : 0 < 2 ^ d := Nat.two_pow_pos d
    have hℓ : u.val / 2 ^ d ≤ d := by
      have : u.val / 2 ^ d < d + 1 := Nat.div_lt_of_lt_mul (by linarith)
      omega
    have hj : u.val % 2 ^ d < 2 ^ d := Nat.mod_lt u.val hPos
    obtain ⟨hW, hReach⟩ := hBflyReach (d - u.val / 2 ^ d) (u.val / 2 ^ d) (u.val % 2 ^ d) hℓ hj rfl
    have hDM : (u.val / 2 ^ d) * 2 ^ d + u.val % 2 ^ d = u.val := by
      have := Nat.div_add_mod u.val (2 ^ d)
      linarith [Nat.mul_comm (u.val / 2 ^ d) (2 ^ d)]
    have hFinEq : (⟨(u.val / 2 ^ d) * 2 ^ d + u.val % 2 ^ d, hW⟩ : Fin (source d).wires) = u :=
      Fin.ext hDM
    rwa [hFinEq] at hReach
  · set h := (d + 2) * 2 ^ d - 1 - u.val
    have hh1 : 1 ≤ h := by omega
    have hh2 : h < 2 ^ (d + 1) := by
      have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      rw [Nat.pow_succ, Nat.mul_two]
      omega
    have hhSmall : h < 2 ^ d := by
      have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
      omega
    obtain ⟨hW, hReach⟩ := hHeapReach h hh1 hh2
    have hVal : heapWireVal d h = u.val := by
      dsimp [heapWireVal]
      simp only [hhSmall, ↓reduceIte]
      omega
    have hFinEq : (⟨heapWireVal d h, hW⟩ : Fin (source d).wires) = u := Fin.ext hVal
    rwa [hFinEq] at hReach

private lemma appendAndGates_nonlinearCount (d m : Nat) (hm : m ≤ 2 ^ d - 1) :
    (appendAndGates d m hm).nonlinearCount = d * 2 ^ d + m := by
  induction m with
  | zero => exact buildCompBfly_nonlinearCount d d le_rfl
  | succ m ih =>
      dsimp [appendAndGates, HybridCircuit.nonlinearCount, HybridGate.nonlinearWeight]
      rw [ih (Nat.le_of_lt hm)]
      omega

/-- Exact nonlinear gate count of `ClosedComparatorAnd.source d`: every single gate
(`d * 2 ^ d` comparator gates + `2 ^ d - 1` `AND` reduction gates = `(d + 1) * 2 ^ d - 1`) is
nonlinear. -/
theorem nonlinearCount_eq (d : Nat) :
    (source d).circuit.nonlinearCount = (d + 1) * 2 ^ d - 1 := by
  change (appendAndGates d (2 ^ d - 1) le_rfl).nonlinearCount = (d + 1) * 2 ^ d - 1
  rw [appendAndGates_nonlinearCount]
  have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hMul : (d + 1) * 2 ^ d = d * 2 ^ d + 2 ^ d := by ring
  omega

/-- `ClosedComparatorAnd.source` defeats every sublinear nonlinear-gate budget `o(2 ^ d)`. -/
theorem escapes_sublinear_nonlinear (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (B : Nat → ℝ) (hB : B =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) :
    ¬ (∀ᶠ i in atTop, (((source (d i)).circuit.nonlinearCount : Nat) : ℝ) ≤ B i) := by
  intro hLe
  rw [Asymptotics.isLittleO_iff] at hB
  have hBound := hB (show (0 : ℝ) < 1 by norm_num)
  have hD2 : ∀ᶠ i in atTop, 2 ≤ d i := hd.eventually_ge_atTop 2
  obtain ⟨i, hiLe, hiB, hiD⟩ := (hLe.and (hBound.and hD2)).exists
  rw [nonlinearCount_eq (d i)] at hiLe
  have hPowPos : 1 ≤ 2 ^ d i := Nat.two_pow_pos (d i)
  have hLower : d i * 2 ^ d i ≤ (d i + 1) * 2 ^ d i - 1 := by
    have hMul : (d i + 1) * 2 ^ d i = d i * 2 ^ d i + 2 ^ d i := by ring
    omega
  have hLowerR : ((d i : ℝ) * ((2 ^ d i : Nat) : ℝ)) ≤
      (((d i + 1) * 2 ^ d i - 1 : Nat) : ℝ) := by exact_mod_cast hLower
  have hPowPosR : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by exact_mod_cast hPowPos
  have hNormB : B i ≤ ‖B i‖ := le_abs_self _
  have hNormPow : ‖((2 ^ d i : Nat) : ℝ)‖ = ((2 ^ d i : Nat) : ℝ) :=
    Real.norm_of_nonneg hPowPosR.le
  rw [hNormPow, one_mul] at hiB
  have hDReal : (2 : ℝ) ≤ (d i : ℝ) := by exact_mod_cast hiD
  nlinarith

private lemma source_embeds_butterfly (d : Nat) :
    let f : Fin (ButterflyNet.source d).wires → Fin (source d).wires :=
      fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩
    Function.Injective f ∧
      (∀ u v, CircuitEdge (ButterflyNet.source d).circuit u v →
        HybridCircuitEdge (source d).circuit (f u) (f v)) := by
  intro f
  refine ⟨fun a b h => Fin.ext (by simpa [f] using congrArg Fin.val h), fun u v huv => ?_⟩
  have hDirOr : (ButterflyNet.source d).circuit.DirectedEdge u v ∨
      (ButterflyNet.source d).circuit.DirectedEdge v u :=
    CircuitEdge.to_directedEdge_or huv
  rcases hDirOr with hDir | hDir
  · rw [ButterflyNet.source_directedEdge_iff] at hDir
    have hComp := buildCompBfly_directedEdge_of_bflyStep d d le_rfl u v hDir
    have hAnd := appendAndGates_directedEdge_of_prev d (2 ^ d - 1) le_rfl hComp
    exact HybridCircuit.directedEdge_to_hybridCircuitEdge hAnd
  · rw [ButterflyNet.source_directedEdge_iff] at hDir
    have hComp := buildCompBfly_directedEdge_of_bflyStep d d le_rfl v u hDir
    have hAnd := appendAndGates_directedEdge_of_prev d (2 ^ d - 1) le_rfl hComp
    exact (HybridCircuit.directedEdge_to_hybridCircuitEdge hAnd).symm

/-- **Linear Treewidth Wall**: any tree decomposition of `ClosedComparatorAnd.source d` has width
`Ω(2 ^ d)`. -/
theorem treewidth_linear (d : Nat) (td : TreeDecomp (HybridCircuitEdge (source d).circuit)) :
    2 ^ d ≤ 18 * (td.width + 1) := by
  let f : Fin (ButterflyNet.source d).wires → Fin (source d).wires :=
    fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩
  have hf : Function.Injective f := (source_embeds_butterfly d).1
  have hEdge := (source_embeds_butterfly d).2
  have hLin := ButterflyNet.butterfly_treewidth_linear d (td.restrict f hf hEdge)
  have hLe := td.restrict_le f hf hEdge
  omega

/-- **Linear Gate-Contraction-Width Wall**: any leaf-bounded binary contraction tree of
`ClosedComparatorAnd.source d` has width `Ω(2 ^ d)`. -/
theorem gateContractionWidth_linear (d : Nat) (hd : 2 ≤ d)
    (ct : ValidContractionTree (HybridCircuitEdge (source d).circuit))
    (hLeaves : ContractionTree.AllLeaves (fun s => s.card ≤ 2) ct.tree) :
    2 ^ d ≤ 18 * ct.contractionWidth := by
  let f : Fin (ButterflyNet.source d).wires → Fin (source d).wires :=
    fun u => ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩
  have hf : Function.Injective f := (source_embeds_butterfly d).1
  have hEdge := (source_embeds_butterfly d).2
  have hLin : 2 ^ d ≤ 18 * (ct.restrict f hf hEdge).contractionWidth := by
    refine ButterflyNet.butterfly_gateContractionWidth_linear d hd (ct.restrict f hf hEdge) ?_
    refine ContractionTree.allLeaves_restrict f hf ?_ ct.tree hLeaves
    intro s hs
    have hPreLe : (s.preimage f hf.injOn).card ≤ s.card :=
      Finset.card_le_card_of_injOn f (fun u hu => Finset.mem_preimage.mp hu)
        (fun x _ y _ h => hf h)
    have hFiltLe : ({x : Fin (2 ^ d) | ⟨x.val, by
        change x.val < LayeredRing.ringWires (2 ^ d) d
        have hx := x.isLt
        have hWPos : 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d)
        rw [LayeredRing.ringWires_eq]
        exact lt_of_lt_of_le hx hWPos⟩ ∈ s.preimage f hf.injOn} : Finset _).card ≤
        (s.preimage f hf.injOn).card := by
      refine Finset.card_le_card_of_injOn
        (fun x : Fin (2 ^ d) => ⟨x.val, by
          change x.val < LayeredRing.ringWires (2 ^ d) d
          have hx := x.isLt
          have hWPos : 2 ^ d ≤ (d + 1) * 2 ^ d := Nat.le_mul_of_pos_left (2 ^ d) (Nat.succ_pos d)
          rw [LayeredRing.ringWires_eq]
          exact lt_of_lt_of_le hx hWPos⟩)
        (fun x hx => by simpa using hx)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    exact hFiltLe.trans (hPreLe.trans hs)
  have hLe := ct.restrict_le f hf hEdge
  omega

/-- `ClosedComparatorAnd.source` defeats all sublinear-treewidth algorithms. -/
theorem escapes_sublinear_treewidth (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (td : (i : Nat) → TreeDecomp (HybridCircuitEdge (source (d i)).circuit)) :
    ¬ ((fun i => ((td i).width : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) := by
  let td' : (i : Nat) → TreeDecomp (CircuitEdge (ButterflyNet.source (d i)).circuit) :=
    fun i => (td i).restrict _ (source_embeds_butterfly (d i)).1 (source_embeds_butterfly (d i)).2
  intro hSub
  have hSub' : (fun i => ((td' i).width : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ) := by
    refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
    filter_upwards [(Asymptotics.isLittleO_iff.mp hSub) hε] with i hi
    have hLe : ((td' i).width : ℝ) ≤ ((td i).width : ℝ) := by
      exact_mod_cast (td i).restrict_le _ (source_embeds_butterfly (d i)).1
        (source_embeds_butterfly (d i)).2
    have hNonneg : 0 ≤ ((td' i).width : ℝ) := Nat.cast_nonneg _
    have hNonneg2 : 0 ≤ ((td i).width : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg hNonneg]
    rw [Real.norm_of_nonneg hNonneg2] at hi
    exact hLe.trans hi
  exact ButterflyNet.butterfly_escapes_sublinear_treewidth d hd td' hSub'

/-- `ClosedComparatorAnd.source` defeats all sublinear contraction-width algorithms. -/
theorem escapes_sublinear_contractionWidth (d : Nat → Nat) (hd : Tendsto d atTop atTop)
    (ct : (i : Nat) → ValidContractionTree (HybridCircuitEdge (source (d i)).circuit))
    (hLeaves : ∀ i, ContractionTree.AllLeaves (fun s => s.card ≤ 2) (ct i).tree) :
    ¬ ((fun i => ((ct i).contractionWidth : ℝ)) =o[atTop] fun i => ((2 ^ d i : Nat) : ℝ)) := by
  intro hSub
  rw [Asymptotics.isLittleO_iff] at hSub
  have hBound := hSub (show (0 : ℝ) < 1 / 36 by norm_num)
  have hD2 : ∀ᶠ i in atTop, 2 ≤ d i := hd.eventually_ge_atTop 2
  obtain ⟨i, hiB, hiD⟩ := (hBound.and hD2).exists
  have hLin : 2 ^ d i ≤ 18 * (ct i).contractionWidth :=
    gateContractionWidth_linear (d i) hiD (ct i) (hLeaves i)
  have hLinR : ((2 ^ d i : Nat) : ℝ) ≤ 18 * ((ct i).contractionWidth : ℝ) := by
    exact_mod_cast hLin
  have hNonneg : 0 ≤ ((ct i).contractionWidth : ℝ) := Nat.cast_nonneg _
  have hPowPos : (0 : ℝ) < ((2 ^ d i : Nat) : ℝ) := by exact_mod_cast Nat.two_pow_pos (d i)
  rw [Real.norm_of_nonneg hNonneg, Real.norm_of_nonneg hPowPos.le] at hiB
  nlinarith

private lemma appendAndGates_evalWires_stable (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    (x : Fin (2 ^ d) → Bool) (u : Fin (LayeredRing.ringWires (2 ^ d) d)) :
    (appendAndGates d m hm).evalWires x
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ m)⟩ =
      (buildCompBfly d d le_rfl).evalWires x u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      dsimp [appendAndGates]
      exact (HybridCircuit.evalWires_snoc_castSucc _ _ x _).trans (ih (Nat.le_of_lt hm))

private lemma source_evalWire_comp (d ℓ j : Nat) (hℓ : ℓ ≤ d) (hj : j < 2 ^ d)
    (x : Fin (2 ^ d) → Bool) :
    (source d).circuit.evalWires x (compWireInSource d ℓ j hℓ hj) =
      (buildCompBfly d ℓ hℓ).evalWires x ⟨ℓ * 2 ^ d + j, by
        rw [LayeredRing.ringWires_eq]
        have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
        omega⟩ := by
  have hX := appendAndGates_evalWires_stable d (2 ^ d - 1) le_rfl x
    (ClosedComparatorXor.compWire d ℓ j hℓ hj)
  have hB := buildCompBfly_evalWires_stable d x ℓ d hℓ le_rfl
    ⟨ℓ * 2 ^ d + j, by
      rw [LayeredRing.ringWires_eq]
      have h1 : ℓ * 2 ^ d + 2 ^ d = (ℓ + 1) * 2 ^ d := by ring
      omega⟩
  exact hX.trans hB

/-- **100% Pairwise Semantic Distinctness**: all `(d + 1) * 2 ^ d` butterfly wires of
`ClosedComparatorAnd.source d` compute pairwise distinct Boolean functions. -/
theorem bfly_wires_pairwise_distinct (d : Nat)
    (ℓ₁ ℓ₂ j₁ j₂ : Nat) (hℓ₁ : ℓ₁ ≤ d) (hℓ₂ : ℓ₂ ≤ d) (hj₁ : j₁ < 2 ^ d) (hj₂ : j₂ < 2 ^ d)
    (hNe : (ℓ₁, j₁) ≠ (ℓ₂, j₂)) :
    ∃ x : Fin (2 ^ d) → Bool,
      (source d).circuit.evalWires x (compWireInSource d ℓ₁ j₁ hℓ₁ hj₁) ≠
        (source d).circuit.evalWires x (compWireInSource d ℓ₂ j₂ hℓ₂ hj₂) := by
  obtain ⟨x, hxNe⟩ := ClosedComparatorXor.bfly_wires_pairwise_distinct d ℓ₁ ℓ₂ j₁ j₂
    hℓ₁ hℓ₂ hj₁ hj₂ hNe
  refine ⟨x, ?_⟩
  rw [source_evalWire_comp, source_evalWire_comp]
  rwa [ClosedComparatorXor.source_evalWire_comp, ClosedComparatorXor.source_evalWire_comp] at hxNe

private lemma heapWireVal_lt_frontier (d m h : Nat) (_hm : m ≤ 2 ^ d - 1)
    (hh1 : 2 ^ d - m ≤ h) (hh2 : h < 2 * (2 ^ d - m)) :
    heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m := by
  rw [LayeredRing.ringWires_eq]
  dsimp [heapWireVal]
  have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
  have hMul2 : d * 2 ^ d + 2 ^ d = (d + 1) * 2 ^ d := by ring
  split_ifs <;> omega

private def evalAndAt (d m : Nat) (hm : m ≤ 2 ^ d - 1) (x : Fin (2 ^ d) → Bool)
    (h : Nat) : Bool :=
  if hLt : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m then
    (appendAndGates d m hm).evalWires x ⟨heapWireVal d h, hLt⟩
  else false

private lemma evalAndAt_eq_of_lt {d m : Nat} {hm : m ≤ 2 ^ d - 1}
    {x : Fin (2 ^ d) → Bool} {h : Nat}
    (hLt : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m) :
    evalAndAt d m hm x h = (appendAndGates d m hm).evalWires x ⟨heapWireVal d h, hLt⟩ := by
  simp only [evalAndAt, hLt, ↓reduceDIte]

private lemma evalAndAt_step_old (d m : Nat) (hm : m < 2 ^ d - 1) (x : Fin (2 ^ d) → Bool)
    (h : Nat) (hh1 : 2 ^ d - m ≤ h) (hh2 : h < 2 * (2 ^ d - (m + 1))) :
    evalAndAt d (m + 1) hm x h = evalAndAt d m (Nat.le_of_lt hm) x h := by
  have hLt0 : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + m :=
    heapWireVal_lt_frontier d m h (Nat.le_of_lt hm) hh1 (by omega)
  have hLt1 : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + (m + 1) :=
    Nat.lt_succ_of_lt hLt0
  rw [evalAndAt_eq_of_lt hLt1, evalAndAt_eq_of_lt hLt0]
  dsimp [appendAndGates]
  exact HybridCircuit.evalWires_snoc_castSucc (appendAndGates d m (Nat.le_of_lt hm)) _ x
    ⟨heapWireVal d h, hLt0⟩

private lemma evalAndAt_step_new (d m : Nat) (hm : m < 2 ^ d - 1) (x : Fin (2 ^ d) → Bool) :
    let p := 2 ^ d - 1 - m
    evalAndAt d (m + 1) hm x p =
      (evalAndAt d m (Nat.le_of_lt hm) x (2 * p) &&
        evalAndAt d m (Nat.le_of_lt hm) x (2 * p + 1)) := by
  intro p
  have hBase := LayeredRing.ringWires_eq (2 ^ d) d
  have hpLt : p < 2 ^ d := by
    have := Nat.two_pow_pos d
    dsimp [p]; omega
  have hValP : heapWireVal d p = LayeredRing.ringWires (2 ^ d) d + m := by
    rw [hBase]
    dsimp [heapWireVal]
    simp only [hpLt, ↓reduceIte]
    have hMul : (d + 2) * 2 ^ d = (d + 1) * 2 ^ d + 2 ^ d := by ring
    dsimp [p]; omega
  have hLtP : heapWireVal d p < LayeredRing.ringWires (2 ^ d) d + (m + 1) := by omega
  have hLt2P : heapWireVal d (2 * p) < LayeredRing.ringWires (2 ^ d) d + m :=
    heapWireVal_lt_xorStep d m (2 * p) hm (Or.inl rfl)
  have hLt2P1 : heapWireVal d (2 * p + 1) < LayeredRing.ringWires (2 ^ d) d + m :=
    heapWireVal_lt_xorStep d m (2 * p + 1) hm (Or.inr rfl)
  rw [evalAndAt_eq_of_lt hLtP, evalAndAt_eq_of_lt hLt2P, evalAndAt_eq_of_lt hLt2P1]
  have hFinLast : (⟨heapWireVal d p, hLtP⟩ :
      Fin (LayeredRing.ringWires (2 ^ d) d + (m + 1))) = Fin.last _ :=
    Fin.ext hValP
  rw [hFinLast]
  change ((appendAndGates d m (Nat.le_of_lt hm)).snoc _).evalWires x (Fin.last _) = _
  rw [HybridCircuit.evalWires_snoc_last]
  rfl

private lemma appendAndGates_allTrue_frontier (d m : Nat) (hm : m ≤ 2 ^ d - 1)
    (x : Fin (2 ^ d) → Bool) :
    (∀ h ∈ Finset.Ico (2 ^ d - m) (2 * (2 ^ d - m)), evalAndAt d m hm x h = true) ↔
      (∀ i : Fin (2 ^ d), x i = true) := by
  induction m with
  | zero =>
      simp only [Nat.sub_zero]
      rw [← ClosedComparatorXor.layer_allTrue_iff d d le_rfl x]
      constructor
      · intro hAll j
        have hMem : 2 ^ d + j.val ∈ Finset.Ico (2 ^ d) (2 * 2 ^ d) := by
          rw [Finset.mem_Ico]
          exact ⟨Nat.le_add_right _ _, by rw [Nat.two_mul]; exact Nat.add_lt_add_left j.isLt _⟩
        have hjTrue := hAll (2 ^ d + j.val) hMem
        have hNot : ¬ (2 ^ d + j.val < 2 ^ d) := by omega
        have hVal : heapWireVal d (2 ^ d + j.val) = d * 2 ^ d + j.val := by
          dsimp [heapWireVal]
          simp only [hNot, ↓reduceIte, Nat.add_sub_cancel_left]
        have hLt : heapWireVal d (2 ^ d + j.val) < LayeredRing.ringWires (2 ^ d) d + 0 := by
          rw [hVal, LayeredRing.ringWires_eq]
          nlinarith [j.isLt]
        rw [evalAndAt_eq_of_lt hLt] at hjTrue
        have hFin : (⟨heapWireVal d (2 ^ d + j.val), hLt⟩ :
            Fin (LayeredRing.ringWires (2 ^ d) d + 0)) =
            ⟨d * 2 ^ d + j.val, by rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ :=
          Fin.ext hVal
        change (buildCompBfly d d le_rfl).evalWires x ⟨heapWireVal d (2 ^ d + j.val), hLt⟩ = true
          at hjTrue
        rwa [hFin] at hjTrue
      · intro hAll h hh
        rw [Finset.mem_Ico, Nat.two_mul] at hh
        let j : Fin (2 ^ d) := ⟨h - 2 ^ d, by omega⟩
        have hNot : ¬ (h < 2 ^ d) := by omega
        have hVal : heapWireVal d h = d * 2 ^ d + j.val := by
          dsimp [heapWireVal, j]
          simp only [hNot, ↓reduceIte]
        have hLt : heapWireVal d h < LayeredRing.ringWires (2 ^ d) d + 0 := by
          rw [hVal, LayeredRing.ringWires_eq]
          nlinarith [j.isLt]
        rw [evalAndAt_eq_of_lt hLt]
        have hFin : (⟨heapWireVal d h, hLt⟩ :
            Fin (LayeredRing.ringWires (2 ^ d) d + 0)) =
            ⟨d * 2 ^ d + j.val, by rw [LayeredRing.ringWires_eq]; nlinarith [j.isLt]⟩ :=
          Fin.ext hVal
        change (buildCompBfly d d le_rfl).evalWires x ⟨heapWireVal d h, hLt⟩ = true
        rw [hFin]
        exact hAll j
  | succ m ih =>
      set p := 2 ^ d - 1 - m
      have hpPos : 1 ≤ p := by dsimp [p]; omega
      have hSub1 : 2 ^ d - (m + 1) = p := by dsimp [p]; omega
      have hSub0 : 2 ^ d - m = p + 1 := by dsimp [p]; omega
      rw [← ih (Nat.le_of_lt hm), hSub1, hSub0]
      constructor
      · intro hAll h hh
        rw [Finset.mem_Ico] at hh
        by_cases hBig : h = 2 * p ∨ h = 2 * p + 1
        · have hpMem : p ∈ Finset.Ico p (2 * p) := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
          have hpTrue := hAll p hpMem
          rw [evalAndAt_step_new d m hm x, Bool.and_eq_true] at hpTrue
          rcases hBig with rfl | rfl
          · exact hpTrue.1
          · exact hpTrue.2
        · have hMem' : h ∈ Finset.Ico p (2 * p) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          have hTrue := hAll h hMem'
          rwa [evalAndAt_step_old d m hm x h (by omega) (by omega)] at hTrue
      · intro hAll h hh
        rw [Finset.mem_Ico] at hh
        by_cases hpEq : h = p
        · rw [hpEq, evalAndAt_step_new d m hm x, Bool.and_eq_true]
          exact ⟨hAll (2 * p) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩),
            hAll (2 * p + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)⟩
        · have hMem' : h ∈ Finset.Ico (p + 1) (2 * (p + 1)) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
          have hTrue := hAll h hMem'
          rwa [evalAndAt_step_old d m hm x h (by omega) (by omega)]

/-- **Exact Semantic Identity**: `ClosedComparatorAnd.source d` computes `allAnd (2 ^ d)` on
every input `x`. -/
theorem source_eval_eq_allAnd (d : Nat) (x : Fin (2 ^ d) → Bool) :
    (source d).eval x = allAnd (2 ^ d) x := by
  apply Bool.eq_iff_iff.mpr
  have hF := appendAndGates_allTrue_frontier d (2 ^ d - 1) le_rfl x
  have hPos : 1 ≤ 2 ^ d := Nat.two_pow_pos d
  have hSub : 2 ^ d - (2 ^ d - 1) = 1 := by omega
  rw [hSub, show 2 * 1 = 2 by decide] at hF
  have hLt : heapWireVal d 1 < LayeredRing.ringWires (2 ^ d) d + (2 ^ d - 1) := by
    rw [← source_output_val]
    exact (source d).output.isLt
  have hOut : (⟨heapWireVal d 1, hLt⟩ : Fin (source d).wires) = (source d).output :=
    Fin.ext (source_output_val d).symm
  have hFront : (∀ h ∈ Finset.Ico 1 2, evalAndAt d (2 ^ d - 1) le_rfl x h = true) ↔
      (source d).eval x = true := by
    rw [show Finset.Ico 1 2 = {1} from by decide]
    simp only [Finset.mem_singleton, forall_eq, evalAndAt_eq_of_lt hLt]
    change (source d).circuit.evalWires x ⟨heapWireVal d 1, hLt⟩ = true ↔
      (source d).circuit.evalWires x (source d).output = true
    rw [hOut]
  have hAllAnd : (allAnd (2 ^ d) x = true) ↔ (∀ i : Fin (2 ^ d), x i = true) := by
    simp [allAnd]
  exact hFront.symm.trans (hF.trans hAllAnd.symm)

/-- **Maximal `ℤ/2ℤ` Algebraic Degree**: `ClosedComparatorAnd.source d` has exact ANF degree
`2 ^ d` (defeating low-degree polynomial / affine-branching reductions simultaneously). -/
theorem output_anfDegree_eq (d : Nat) : anfDegree (source d).eval = 2 ^ d := by
  have hFun : (source d).eval = allAnd (2 ^ d) := funext (source_eval_eq_allAnd d)
  rw [hFun, anfDegree_allAnd_eq]

/-- **Exact `#Circuit-SAT` Collapse**: `ClosedComparatorAnd.source d` has a unique accepting
input (`Fintype.card = 1`). -/
theorem acceptCount_eq (d : Nat) :
    Fintype.card { x : Fin (2 ^ d) → Bool // (source d).eval x = true } = 1 := by
  classical
  have e : { x : Fin (2 ^ d) → Bool // (source d).eval x = true } ≃
      { x : Fin (2 ^ d) → Bool // x = fun _ => true } :=
    Equiv.subtypeEquivRight fun x => by
      rw [source_eval_eq_allAnd d x]
      simp [allAnd, funext_iff]
  rw [Fintype.card_congr e, Fintype.card_unique]

end ClosedComparatorAnd

end PvsNP
