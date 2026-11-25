module

public import MCSPPairSeparation
public import Complexity.Computability.Circuit.Synthesis

/-! Keep the affine forest lower bound in a nearly full residual, by pinning
towards the branch with fewer accepting tables and repairing affine probes. -/

@[expose] public section

namespace PvsNP.Frontier.MinorityResidual

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open SuperTwoN ForestPinning RestrictionCharges FreshCharges PairSeparation
open CornerCertificates TwoCornerStructure MonotoneForest NestedFaces

variable {n : ℕ}

/-- Pinning one coordinate doubles the number of accepted tables on the
chosen side when we keep the old coordinate as an ignored slot. -/
theorem card_pinned_branch (f : BooleanFunction n) (i : Fin n) (v : Bool) :
    (acceptingTables (fun y => f (Function.update y i v))).card =
      2 * ((acceptingTables f).filter fun y => y i = v).card := by
  classical
  let S := (acceptingTables f).filter fun y => y i = v
  let U := acceptingTables (fun y => f (Function.update y i v))
  have hUpdate (y : S) : Function.update y.val i v = y.val := by
    rw [← (Finset.mem_filter.mp y.property).2, Function.update_eq_self]
  let e : U ≃ Bool × S :=
    { toFun := fun y => (y.val i, ⟨Function.update y.val i v,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp y.property).2⟩, by simp⟩⟩)
      invFun := fun z => ⟨Function.update z.2.val i z.1, by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change f (Function.update (Function.update z.2.val i z.1) i v) = true
        rw [Function.update_idem, hUpdate z.2]
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp z.2.property).1).2⟩
      left_inv := fun y => by
        apply Subtype.ext
        change Function.update (Function.update y.val i v) i (y.val i) = y.val
        rw [Function.update_idem, Function.update_eq_self]
      right_inv := fun z => by
        apply Prod.ext
        · simp
        · apply Subtype.ext
          change Function.update (Function.update z.2.val i z.1) i v = z.2.val
          rw [Function.update_idem, hUpdate z.2] }
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool] using Fintype.card_congr e

theorem exists_sparse_pin (f : BooleanFunction n) (i : Fin n) :
    ∃ v : Bool, (acceptingTables (fun y => f (Function.update y i v))).card ≤
      (acceptingTables f).card := by
  classical
  let A := (acceptingTables f).filter fun y => y i = false
  let D := (acceptingTables f).filter fun y => y i = true
  have hRest : acceptingTables f \ A = D := by
    ext y
    simp only [A, D, Finset.mem_sdiff, Finset.mem_filter]
    cases y i <;> simp
  have hSum := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset (fun y => y i = false) (acceptingTables f))
  change (acceptingTables f \ A).card + A.card = (acceptingTables f).card at hSum
  rw [hRest] at hSum
  by_cases h : A.card ≤ D.card
  · refine ⟨false, ?_⟩
    rw [card_pinned_branch]
    change 2 * A.card ≤ _
    omega
  · refine ⟨true, ?_⟩
    rw [card_pinned_branch]
    change 2 * D.card ≤ _
    omega

def negatives (m : ℕ) : Set (BooleanFunction m) :=
  Set.range fun i : Fin m => fun y : BitString m => !(y i)

theorem synthesis_negatives (m : ℕ) :
    Synthesis interpretation (inputs m) (negatives m) m := by
  let c := Circuit.pi fun i : Fin m =>
    Circuit.oneGate (σ := signature) .not (fun _ => i)
  have h := Synthesis.circuit (I := interpretation) (s := inputs m) c
    (fun i y => y i) (fun i => ⟨i, rfl⟩)
  simpa [c, negatives, interpretation] using h

private def minterm (m : ℕ) (i : Fin (2 ^ m)) : BooleanFunction m :=
  fun y => decide (BitString.equivFin m y = i)

private theorem synthesis_shared_minterm (m : ℕ) (i : Fin (2 ^ m)) :
    Synthesis interpretation (inputs m ∪ negatives m) {minterm m i} (m + 1) := by
  classical
  let w := (BitString.equivFin m).symm i
  let lit (j : Fin m) (y : BitString m) := if w j then y j else !(y j)
  have hLit (j : Fin m) : lit j ∈ inputs m ∪ negatives m := by
    cases hj : w j
    · exact Or.inr ⟨j, by funext y; simp [lit, hj]⟩
    · exact Or.inl ⟨j, by funext y; simp [lit, hj]⟩
  obtain ⟨d, hd, hS⟩ := Synthesis.exists_forall_mem
    (s := inputs m ∪ negatives m) (Finset.univ : Finset (Fin m)) lit (c := 0) (m := m)
    (by simp) (fun j _ => Synthesis.of_mem (hLit j))
  have hEq (y : BitString m) : d y = true ↔ minterm m i y = true := by
    rw [hd]
    simp only [Finset.mem_univ, true_implies, minterm, decide_eq_true_eq]
    rw [← Equiv.eq_symm_apply]
    change (∀ j, lit j y = true) ↔ y = w
    have hl (j : Fin m) : lit j y = true ↔ y j = w j := by
      cases hw : w j <;> cases hy : y j <;> simp [lit, hw, hy]
    simp only [hl]
    exact ⟨funext, congrFun⟩
  exact (Synthesis.congr_iff hS hEq).mono Set.Subset.rfl Set.Subset.rfl (by omega)

/-- A finite collection of points shares the negations of all represented inputs. -/
theorem point_indicator_complexity_le (m : ℕ) (D : Finset (Fin (2 ^ m))) :
    complexity interpretation (single (fun z : BitString m => decide (BitString.equivFin m z ∈ D))) ≤
      m + D.card * (m + 2) + 1 := by
  classical
  obtain ⟨d, hd, hS⟩ := Synthesis.exists_exists_mem
    (s := inputs m ∪ negatives m) D (minterm m) (m := D.card) le_rfl
    (fun i _ => synthesis_shared_minterm m i)
  have he (z : BitString m) : d z = true ↔
      decide (BitString.equivFin m z ∈ D) = true := by
    rw [hd]
    simp [minterm, eq_comm]
  have hc := ((synthesis_negatives m).trans (Synthesis.congr_iff hS he)).complexity_le
  change complexity interpretation (single (fun z => decide (BitString.equivFin m z ∈ D))) ≤
    m + (D.card * (m + 2) + 1) at hc
  exact hc.trans (by omega)

/-- Repair an affine probe at arbitrary pinned truth-table entries. All point
tests reuse the same bank of negated represented inputs. -/
theorem patched_affine_accepted (m : ℕ) (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m)))
    (a : BitString m) (b : Bool) (hBudget : 5 * m + 6 + (m + 2) * P.card ≤ m ^ 2) :
    mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (affine a b))) = true := by
  classical
  let T := MCSP.truthTable m (affine a b)
  let D := P.filter fun i => T i ≠ x i
  have hDc : D.card ≤ P.card := Finset.card_filter_le _ _
  let d : BooleanFunction m := fun z => decide (BitString.equivFin m z ∈ D)
  have hD (z : BitString m) : d z = true ↔ BitString.equivFin m z ∈ D := by simp [d]
  have hEq : MCSP.truthTable m (fun z => affine a b z ^^ d z) =
      substitute (pinAt x P) T := by
    funext i
    have hDi := hD ((BitString.equivFin m).symm i)
    rw [Equiv.apply_symm_apply] at hDi
    change (T i ^^ d ((BitString.equivFin m).symm i)) = substitute (pinAt x P) T i
    by_cases hi : i ∈ P
    · rw [substitute_inr (show pinAt x P i = .inr (x i) by simp [pinAt, hi])]
      by_cases he : T i = x i
      · have hDfalse : d ((BitString.equivFin m).symm i) = false :=
          Bool.eq_false_of_not_eq_true (fun h => by simpa [D, hi, he] using hDi.mp h)
        rw [hDfalse]
        exact (by cases (T i) <;> rfl : (T i ^^ false) = T i).trans he
      · have hDtrue : d ((BitString.equivFin m).symm i) = true :=
          hDi.mpr (Finset.mem_filter.mpr ⟨hi, he⟩)
        have hx : (!(T i)) = x i := by cases hT : T i <;> cases hz : x i <;> simp_all
        rw [hDtrue]
        exact (by cases (T i) <;> rfl : (T i ^^ true) = !(T i)).trans hx
    · have hDfalse : d ((BitString.equivFin m).symm i) = false :=
        Bool.eq_false_of_not_eq_true (fun h => hi (Finset.mem_filter.mp (hDi.mp h)).1)
      rw [hDfalse, substitute_inl (show pinAt x P i = .inl i by simp [pinAt, hi])]
      cases (T i) <;> rfl
  change mcspSquare m (substitute (pinAt x P) T) = true
  rw [← hEq, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  have hcD := point_indicator_complexity_le m D
  change complexity interpretation (single d) ≤ m + D.card * (m + 2) + 1 at hcD
  have hTermBudget := Nat.mul_le_mul_right (m + 2) hDc
  rw [Nat.mul_comm P.card (m + 2)] at hTermBudget
  have hcAff := complexity_affine_le a b
  exact (complexity_xor_le (affine a b) d).trans (by omega)

private theorem residual_affine_size {m B : ℕ} {f : BooleanFunction (2 ^ m)}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hAff : ∀ a b, f (MCSP.truthTable m (affine a b)) = true) :
    18694 * (2 * 2 ^ m) + 10 * 2 ^ m ≤
      18694 * (complexity interpretation (single f) + 2 * B + 1) + 142 * B := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single f)
  have hCorner (b : Bool) : f (fun _ => b) = true := by
    have h := hAff (fun _ => false) b
    rwa [affine_constant] at h
  have h0 : cornerValue c.program false (c.outputs 0) = true := (congrFun (hc _) 0).trans (hCorner false)
  have h1 : cornerValue c.program true (c.outputs 0) = true := (congrFun (hc _) 0).trans (hCorner true)
  have hN0 := card_needInputs_ge_of_sparse c hc hSparse false (hCorner false)
  have hN1 := card_needInputs_ge_of_sparse c hc hSparse true (hCorner true)
  have hLedger := needInputs_add_slack_eq c.program (c.outputs 0) h0 h1
  have hForest := sparse_affine_stop_budget c hc hSparse (hCorner false) (hCorner true) hAff
  have hStop := card_stopGate_le_56_slack c.program (c.outputs 0) h0 h1
  omega

/-- Each adaptive pin removes a fresh original gate if all partial
assignments in the schedule still admit the patched zero table. -/
theorem minority_pinning_run_of_zero (m : ℕ) (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (hFew : descriptionBitBound m < 2 ^ m) (t : ℕ)
    (hZeroAt : ∀ (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m))), P.card < t →
      mcspSquare m (substitute (pinAt x P) (fun _ => false)) = true) :
    ∃ (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m))),
      P.card = t ∧
      (acceptingTables fun y => mcspSquare m (substitute (pinAt x P) y)).card ≤
        2 ^ descriptionBitBound m ∧
      t + (fresh c.program (pinAt x P)).card ≤ (fresh c.program Sum.inl).card := by
  classical
  induction t with
  | zero =>
    refine ⟨fun _ => false, ∅, rfl, ?_, ?_⟩
    · have hId : (fun y => mcspSquare m (substitute (pinAt (fun _ => false) ∅) y)) =
          mcspSquare m := by
        funext y
        congr 1
      rw [hId]
      exact card_accepting_mcspSquare_le m
    · have hId : pinAt (fun _ : Fin (2 ^ m) => false) ∅ = Sum.inl := by
        funext i
        simp [pinAt]
      simp [hId]
  | succ t ih =>
    obtain ⟨x, P, hP, hSparse, hOld⟩ := ih (fun x P h => hZeroAt x P (by omega))
    let f : BooleanFunction (2 ^ m) := fun y => mcspSquare m (substitute (pinAt x P) y)
    have hZero : f (fun _ => false) = true := hZeroAt x P (by omega)
    have hEss : ∃ i, EssentialAt f i := by
      by_contra h
      have hEmpty : essentialPositions (fun y => f (restrictTable (fun _ => false) Finset.univ y))
          Finset.univ = ∅ := by
        have hId : (fun y => f (restrictTable (fun _ => false) Finset.univ y)) = f := by
          funext y
          congr 1
          funext i
          simp [restrictTable]
        rw [hId]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact h ⟨i, (Finset.mem_filter.mp hi).2⟩
      have hPow := (pow_card_inessential_le f (fun _ => false) Finset.univ hZero).trans hSparse
      rw [hEmpty, Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] at hPow
      exact (not_le_of_gt hFew) ((Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPow)
    obtain ⟨i, he⟩ := hEss
    have hiP : i ∉ P := by
      intro hi
      obtain ⟨y, z, ha, hne⟩ := he
      apply hne
      have hSame : substitute (pinAt x P) y = substitute (pinAt x P) z := by
        funext j
        by_cases hj : j ∈ P
        · simp [substitute, pinAt, hj]
        · have hji : j ≠ i := fun h => hj (h.symm ▸ hi)
          simp [substitute, pinAt, hj, ha j hji]
      exact congrArg (mcspSquare m) hSame
    obtain ⟨v, hv⟩ := exists_sparse_pin f i
    let x' := Function.update x i v
    let τ := pinAt x' ({i} : Finset (Fin (2 ^ m)))
    have hτ (y : BitString (2 ^ m)) : substitute τ y = Function.update y i v := by
      funext j
      by_cases hj : j = i <;> simp [τ, x', substitute, pinAt, hj]
    have hCompose : pinAt x' (insert i P) = compose (pinAt x P) τ :=
      branchPin_compose x P i v hiP
    have hNext : (fun y => mcspSquare m (substitute (pinAt x' (insert i P)) y)) =
        fun y => f (Function.update y i v) := by
      funext y
      rw [hCompose, substitute_compose, hτ]
    have hCircuit := restricted_circuit_eq c hc (pinAt x P)
    have hNotProj : restrictedWire c.program (pinAt x P) (c.outputs 0) ≠ projection i := by
      intro h
      have hh := congrFun (hCircuit.symm.trans h) (fun _ => false)
      change f (fun _ => false) = false at hh
      rw [hZero] at hh
      cases hh
    have hLoss := twice_nextFreshLoss_ge c.program (pinAt x P) τ (c.outputs 0) {i}
      (fun j hj => by rw [Finset.mem_singleton.mp hj, hCircuit]; exact he)
      (fun j hj => by rwa [Finset.mem_singleton.mp hj])
      (fun j hj => ⟨x' j, by simp [τ, pinAt, hj]⟩)
    rw [Finset.card_singleton] at hLoss
    have hSplit := Finset.card_sdiff_add_card_eq_card (fresh_nested c.program (pinAt x P) τ)
    change (nextFreshLoss c.program (pinAt x P) τ).card +
      (fresh c.program (compose (pinAt x P) τ)).card = (fresh c.program (pinAt x P)).card at hSplit
    rw [← hCompose] at hSplit
    refine ⟨x', insert i P, by rw [Finset.card_insert_of_notMem hiP, hP], ?_, by omega⟩
    rw [hNext]
    exact hv.trans hSparse

/-- Under the repair budget, each adaptive pin loses an original fresh
index and the padded residual keeps the original acceptance-count bound. -/
theorem minority_pinning_run (m : ℕ) (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (hFew : descriptionBitBound m < 2 ^ m) (t : ℕ)
    (hBudget : 5 * m + 6 + (m + 2) * t ≤ m ^ 2) :
    ∃ (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m))),
      P.card = t ∧
      (acceptingTables fun y => mcspSquare m (substitute (pinAt x P) y)).card ≤
        2 ^ descriptionBitBound m ∧
      t + (fresh c.program (pinAt x P)).card ≤ (fresh c.program Sum.inl).card := by
  apply minority_pinning_run_of_zero m c hc hFew t
  intro x P hP
  have h := patched_affine_accepted m x P (fun _ => false) false
    (le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (m + 2) hP.le) _) hBudget)
  rwa [affine_constant] at h

/-- Combine the full forest bound for the padded residual with the distinct
original gates lost along the minority-branch schedule. -/
theorem mcspSquare_minority_lower (m t : ℕ)
    (hFew : descriptionBitBound m < 2 ^ m)
    (hBudget : 5 * m + 6 + (m + 2) * t ≤ m ^ 2) :
    18694 * (2 * 2 ^ m + t) + 10 * 2 ^ m ≤
      18694 * (complexity interpretation (single (mcspSquare m)) + 2 * descriptionBitBound m + 1) +
      142 * descriptionBitBound m := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  obtain ⟨x, P, hP, hSparse, hLoss⟩ := minority_pinning_run m c hc hFew t hBudget
  let f : BooleanFunction (2 ^ m) := fun y => mcspSquare m (substitute (pinAt x P) y)
  have hResid := residual_affine_size (f := f) hSparse
    (fun a b => patched_affine_accepted m x P a b (by rwa [hP]))
  have hNon : ¬ ∃ b : Bool, restrictedWire c.program (pinAt x P) (c.outputs 0) = fun _ => b := by
    rw [restricted_circuit_eq c hc]
    rintro ⟨b, hb⟩
    change f = (fun _ => b) at hb
    have hZero : f (fun _ => false) = true := by
      have h := patched_affine_accepted m x P (fun _ => false) false (by rwa [hP])
      rwa [affine_constant] at h
    have hB : b = true := (congrFun hb _).symm.trans hZero
    have hCap := card_masked_le (f := f) hSparse (fun _ => false) ∅ (fun y _ => by
      rw [hb, hB])
    exact (not_le_of_gt hFew) (by simpa using hCap)
  have hSynth := fresh_complexity_le_of_nonconstant c.program (pinAt x P) (c.outputs 0) hNon
  rw [restricted_circuit_eq c hc] at hSynth
  change complexity interpretation (single f) ≤ (fresh c.program (pinAt x P)).card at hSynth
  have hAll : (fresh c.program (Sum.inl : Fin (2 ^ m) → Fin (2 ^ m) ⊕ Bool)).card ≤ c.size := by
    simpa using Finset.card_le_univ (fresh c.program (Sum.inl : Fin (2 ^ m) → Fin (2 ^ m) ⊕ Bool))
  omega

/-- At arity 32, some 25 pins preserve the previous full-size forest
lower bound in the residual and lose at least 25 distinct fresh indices. -/
theorem mcspSquare_32_residual (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    ∃ (x : BitString (2 ^ 32)) (P : Finset (Fin (2 ^ 32))),
      P.card = 25 ∧
      8592176548 ≤ complexity interpretation
        (single (restrictedWire c.program (pinAt x P) (c.outputs 0))) ∧
      25 + (fresh c.program (pinAt x P)).card ≤ (fresh c.program Sum.inl).card := by
  obtain ⟨x, P, hP, hSparse, hLoss⟩ := minority_pinning_run 32 c hc (by decide) 25 (by decide)
  refine ⟨x, P, hP, ?_, hLoss⟩
  rw [restricted_circuit_eq c hc]
  have hb : 5 * 32 + 6 + (32 + 2) * P.card ≤ 32 ^ 2 := by rw [hP]; decide
  have h := residual_affine_size hSparse (fun a b => patched_affine_accepted 32 x P a b hb)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 18694 * (2 * 4294967296) + 10 * 4294967296 ≤
    18694 * (complexity interpretation
      (single fun y => mcspSquare 32 (substitute (pinAt x P) y)) + 2 * 27672 + 1) + 142 * 27672 at h
  change 8592176548 ≤ complexity interpretation
    (single fun y => mcspSquare 32 (substitute (pinAt x P) y))
  omega

theorem mcspSquare_32_minority :
    8592176573 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := mcspSquare_minority_lower 32 25 (by decide) (by decide)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 18694 * (2 * 4294967296 + 25) + 10 * 4294967296 ≤
    18694 * (complexity interpretation (single (mcspSquare 32)) + 2 * 27672 + 1) + 142 * 27672 at h
  omega

/-- The sharper affine estimate survives the same 25-gate minority schedule. -/
theorem mcspSquare_32_tight_minority :
    8592202102 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  obtain ⟨x, P, hP, hSparse, hLoss⟩ := minority_pinning_run 32 c hc (by decide) 25 (by decide)
  let f : BooleanFunction (2 ^ 32) := fun y => mcspSquare 32 (substitute (pinAt x P) y)
  have hAff (a : BitString 32) (b : Bool) :
      f (fun i => affine a b ((BitString.equivFin 32).symm i)) = true := by
    change f (MCSP.truthTable 32 (affine a b)) = true
    exact patched_affine_accepted 32 x P a b (by rw [hP]; decide)
  have h := tight_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding hSparse hAff
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 25884 * (2 * 4294967296) + 14 * 4294967296 ≤
    25884 * (complexity interpretation (single f) + 2 * 27672 + 1) + 196 * 27672 at h
  have hR : 8592202077 ≤ complexity interpretation (single f) := by omega
  have hEq : restrictedWire c.program (pinAt x P) (c.outputs 0) = f :=
    restricted_circuit_eq c hc (pinAt x P)
  have hNon : ¬ ∃ b : Bool, restrictedWire c.program (pinAt x P) (c.outputs 0) = fun _ => b := by
    rintro ⟨b, hb⟩
    rw [hEq] at hb
    have he : complexity interpretation (single f) ≤ 1 := by
      rw [hb]
      exact (Synthesis.const (s := inputs (2 ^ 32)) b).complexity_le
    omega
  have hSynth := fresh_complexity_le_of_nonconstant c.program (pinAt x P) (c.outputs 0) hNon
  rw [hEq] at hSynth
  have hAll : (fresh c.program (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool)).card ≤ c.size := by
    simpa using Finset.card_le_univ (fresh c.program (Sum.inl : Fin (2 ^ 32) → Fin (2 ^ 32) ⊕ Bool))
  omega

#print axioms patched_affine_accepted
#print axioms minority_pinning_run
#print axioms mcspSquare_minority_lower
#print axioms mcspSquare_32_residual
#print axioms mcspSquare_32_minority
#print axioms mcspSquare_32_tight_minority

end PvsNP.Frontier.MinorityResidual
