module

public import MCSPRestrictionCharges

/-! Two nested zero restrictions of the quadratic MCSP slice. -/

@[expose] public section

namespace PvsNP.Frontier.NestedFaces

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open SuperTwoN CornerCertificates TwoCornerStructure RestrictionCharges

variable {n k : ℕ}

/-- Input slots on the leading-zero face are supplied by the smaller table. -/
def faceSub (m : ℕ) : Fin (2 ^ (m + 1)) → Fin (2 ^ m) ⊕ Bool :=
  fun i =>
    let z := (BitString.equivFin (m + 1)).symm i
    if z 0 then .inr false else .inl (BitString.equivFin m (Fin.tail z))

def face (m : ℕ) (T : BitString (2 ^ m)) : BitString (2 ^ (m + 1)) :=
  substitute (faceSub m) T

theorem face_represented (m : ℕ) (T : BitString (2 ^ m)) :
    (MCSP.truthTable (m + 1)).symm (face m T) =
      fun z => !(z 0) && (MCSP.truthTable m).symm T (Fin.tail z) := by
  funext z
  change substitute (faceSub m) T (BitString.equivFin (m + 1) z) =
    (!(z 0) && T (BitString.equivFin m (Fin.tail z)))
  cases hz : z 0 <;> simp [substitute, faceSub, hz]

theorem face_injective (m : ℕ) : Function.Injective (face m) := by
  intro T U he
  have hh := congrArg (MCSP.truthTable (m + 1)).symm he
  rw [face_represented, face_represented] at hh
  apply (MCSP.truthTable m).symm.injective
  funext z
  simpa using congrFun hh (Fin.cons false z)

private theorem lift_tail_size {m : ℕ} (f : BooleanFunction m) :
    complexity interpretation (single fun z : BitString (m + 1) => f (Fin.tail z)) ≤
      complexity interpretation (single f) := by
  obtain ⟨c, hc, hmin⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  let d := c.comp (Circuit.wiring signature (Fin.succ : Fin m → Fin (m + 1)))
  have h : d.Computes interpretation (single fun z : BitString (m + 1) => f (Fin.tail z)) := by
    intro z
    rw [show d.eval interpretation z = c.eval interpretation (Fin.tail z) by
      simp only [d, Circuit.eval_comp, Circuit.eval_wiring]
      rfl]
    exact hc (Fin.tail z)
  exact (complexity_le_of_computes d h).trans (by simpa [d, Circuit.size_comp] using hmin.le)

theorem face_size (m : ℕ) (T : BitString (2 ^ m)) :
    complexity interpretation (single ((MCSP.truthTable (m + 1)).symm (face m T))) ≤
      complexity interpretation (single ((MCSP.truthTable m).symm T)) + 2 := by
  rw [face_represented]
  let f := (MCSP.truthTable m).symm T
  let head : BooleanFunction (m + 1) := fun z => z 0
  have hh : complexity interpretation (single head) = 0 := complexity_single_proj _
  have hnot : complexity interpretation (single fun z => !head z) ≤ 1 :=
    (complexity_not_le head).trans (by rw [hh])
  have ht := lift_tail_size f
  have hAnd := complexity_and_le (fun z => !head z) (fun z => f (Fin.tail z))
  have hsum := Nat.add_le_add_right (Nat.add_le_add hnot ht) 1
  exact hAnd.trans (hsum.trans (show 1 + complexity interpretation (single f) + 1 ≤
    complexity interpretation (single f) + 2 by omega))

noncomputable def middle (m : ℕ) (T : BitString (2 ^ (m + 1))) : Bool := mcspSquare (m + 2) (face (m + 1) T)

noncomputable def inner (m : ℕ) (T : BitString (2 ^ m)) : Bool := middle m (face m T)

private theorem accepting_pullback_le {n k : ℕ} (f : BooleanFunction n) (φ : BitString k → BitString n)
    (hi : Function.Injective φ) :
    (acceptingTables (f ∘ φ)).card ≤ (acceptingTables f).card := by
  classical
  apply Finset.card_le_card_of_injOn φ
  · intro T hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hT).2⟩
  · exact hi.injOn

theorem middle_sparse (m : ℕ) :
    (acceptingTables (middle m)).card ≤ 2 ^ descriptionBitBound (m + 2) :=
  (accepting_pullback_le (mcspSquare (m + 2)) (face (m + 1)) (face_injective _)).trans
    (card_accepting_mcspSquare_le _)

theorem inner_sparse (m : ℕ) :
    (acceptingTables (inner m)).card ≤ 2 ^ descriptionBitBound (m + 2) :=
  (accepting_pullback_le (middle m) (face m) (face_injective _)).trans (middle_sparse m)

theorem middle_affine (m : ℕ) (hm : 5 ≤ m) (a : BitString (m + 1)) (b : Bool) :
    middle m (MCSP.truthTable (m + 1) (affine a b)) = true := by
  unfold middle
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff]
  apply (face_size (m + 1) _).trans
  rw [Equiv.symm_apply_apply]
  have h := complexity_affine_le a b
  exact (Nat.add_le_add_right h 2).trans (by nlinarith)

theorem inner_affine (m : ℕ) (hm : 5 ≤ m) (a : BitString m) (b : Bool) :
    inner m (MCSP.truthTable m (affine a b)) = true := by
  unfold inner middle
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff]
  apply (face_size (m + 1) _).trans
  have h := face_size m (MCSP.truthTable m (affine a b))
  rw [Equiv.symm_apply_apply] at h
  have h₀ := complexity_affine_le a b
  exact (Nat.add_le_add_right (h.trans (Nat.add_le_add_right h₀ 2)) 2).trans (by nlinarith)

theorem affine_constant (m : ℕ) (b : Bool) :
    MCSP.truthTable m (affine (fun _ => false) b) = fun _ => b := by
  have hz : ∀ (j : ℕ) (z : BitString j), dot (fun _ => false) z = false := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro z
      change (false ^^ dot (fun _ => false) (Fin.tail z)) = false
      rw [ih]
      rfl
  funext i
  simp [MCSP.truthTable, affine, hz]

theorem forest_size {m B : ℕ} {f : BooleanFunction (2 ^ m)}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hAff : ∀ (a : BitString m) (b : Bool), f (MCSP.truthTable m (affine a b)) = true) :
    2 * 2 ^ m + 2 ^ m / 2280 ≤ complexity interpretation (single f) + 3 * B + 1 := by
  obtain ⟨c, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  have hCorner (b : Bool) : f (fun _ => b) = true := by
    have h := hAff (fun _ => false) b
    rwa [affine_constant] at h
  have hf0 : cornerValue c.program false (c.outputs 0) = true :=
    (congrFun (hc (fun _ => false)) 0).trans (hCorner false)
  have hf1 : cornerValue c.program true (c.outputs 0) = true :=
    (congrFun (hc (fun _ => true)) 0).trans (hCorner true)
  have h0 := card_needInputs_ge_of_sparse c hc hSparse false (hCorner false)
  have h1 := card_needInputs_ge_of_sparse c hc hSparse true (hCorner true)
  have hA := needInputs_add_slack_eq c.program (c.outputs 0) hf0 hf1
  have hSlack := sparse_affine_slack_bound c hc hSparse (hCorner false) (hCorner true) hAff
  omega

theorem restricted_circuit_eq (c : Circuit signature n 1) {f : BooleanFunction n}
    (hc : c.Computes interpretation (single f)) (ρ : Fin n → Fin k ⊕ Bool) :
    restrictedWire c.program ρ (c.outputs 0) = fun x => f (substitute ρ x) := by
  funext x
  exact congrFun (hc (substitute ρ x)) 0

theorem separate_survivor_bounds (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    (2 * 2 ^ (m + 1) + 2 ^ (m + 1) / 2280 ≤
      (surviving c.program (faceSub (m + 1))).card + 3 * descriptionBitBound (m + 2) + 3) ∧
    (2 * 2 ^ m + 2 ^ m / 2280 ≤
      (surviving c.program (compose (faceSub (m + 1)) (faceSub m))).card +
        3 * descriptionBitBound (m + 2) + 3) := by
  have hmid := forest_size (middle_sparse m) (middle_affine m hm)
  have hin := forest_size (inner_sparse m) (inner_affine m hm)
  have h₁ := restricted_complexity_le c.program (c.outputs 0) (faceSub (m + 1))
  have h₂ := restricted_complexity_le c.program (c.outputs 0) (compose (faceSub (m + 1)) (faceSub m))
  rw [restricted_circuit_eq c hc] at h₁ h₂
  change complexity interpretation (single (middle m)) ≤ _ at h₁
  have he : (fun x => mcspSquare (m + 2) (substitute (compose (faceSub (m + 1)) (faceSub m)) x)) =
      inner m := by
    funext x
    rw [substitute_compose]
    rfl
  rw [he] at h₂
  omega

/-- Charge each eliminated original gate on the first restriction where it
becomes constant. The forest lower bound then applies to the survivors. -/
theorem two_faces_disjoint_charge (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    Disjoint (firstLost c.program (faceSub (m + 1))) (secondLost c.program (faceSub (m + 1)) (faceSub m)) ∧
    2 * 2 ^ m + 2 ^ m / 2280 + (firstLost c.program (faceSub (m + 1))).card +
      (secondLost c.program (faceSub (m + 1)) (faceSub m)).card ≤
        c.size + 3 * descriptionBitBound (m + 2) + 3 := by
  have h := (separate_survivor_bounds m hm c hc).2
  have hC := card_partition c.program (faceSub (m + 1)) (faceSub m)
  exact ⟨losses_disjoint c.program _ _, by omega⟩

#print axioms separate_survivor_bounds
#print axioms two_faces_disjoint_charge

end PvsNP.Frontier.NestedFaces
