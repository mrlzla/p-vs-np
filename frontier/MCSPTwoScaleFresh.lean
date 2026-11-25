module

public import MCSPFreshCharges

/-! Two disjoint, quantitative gate deletion charges on nested faces of exact MCSP. -/

@[expose] public section

namespace PvsNP.Frontier.TwoScaleFresh

open Cslib Cslib.Circuits Cslib.Circuits.Boolean RestrictionCharges NestedFaces FreshCharges

variable {n k l g : ℕ}

noncomputable def pinned (τ : Fin k → Fin l ⊕ Bool) : Finset (Fin k) :=
  open scoped Classical in Finset.univ.filter (fun i => ∃ b : Bool, τ i = .inr b)

theorem card_pinned_face (m : ℕ) : (pinned (faceSub m)).card = 2 ^ m := by
  classical
  let embed (z : BitString m) := BitString.equivFin (m + 1) (Fin.cons true z)
  have hi : Function.Injective embed := by
    intro x y h
    have h' := (BitString.equivFin (m + 1)).injective h
    funext j
    exact congrFun h' j.succ
  have he : pinned (faceSub m) = (Finset.univ : Finset (BitString m)).image embed := by
    ext i
    let z := (BitString.equivFin (m + 1)).symm i
    have hid : BitString.equivFin (m + 1) z = i := Equiv.apply_symm_apply _ _
    have hpin : i ∈ pinned (faceSub m) ↔ z 0 = true := by
      cases hz : z 0 <;> simp [pinned, faceSub, z, hz]
    rw [hpin]
    constructor
    · intro hz
      refine Finset.mem_image.mpr ⟨Fin.tail z, Finset.mem_univ _, ?_⟩
      change BitString.equivFin (m + 1) (Fin.cons true (Fin.tail z)) = i
      rw [← hz, Fin.cons_self_tail, hid]
    · rintro h
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp h
      have h' := (BitString.equivFin (m + 1)).injective (hu.trans hid.symm)
      exact (congrFun h' (0 : Fin (m + 1))).symm
  rw [he, Finset.card_image_of_injective _ hi, Finset.card_univ, BitString.card]

private theorem nonessential_card_le {f : BooleanFunction k} {B : ℕ}
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (h0 : f (fun _ => false) = true) :
    ((Finset.univ : Finset (Fin k)) \ essentialPositions f Finset.univ).card ≤ B := by
  classical
  let full : Finset (Fin k) := Finset.univ
  have he (x : BitString k) : restrictTable (fun _ => false) full x = x := by
    funext i
    simp [restrictTable, full]
  have h := (pow_card_inessential_le f (fun _ => false) full h0).trans hSparse
  simp only [he] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp h

theorem pinned_charge_of_sparse (p : Program signature n g) (ρ : Fin n → Fin k ⊕ Bool)
    (τ : Fin k → Fin l ⊕ Bool) (root : Wire n g) {f : BooleanFunction k} {B : ℕ}
    (hEq : restrictedWire p ρ root = f)
    (hSparse : (acceptingTables f).card ≤ 2 ^ B) (h0 : f (fun _ => false) = true) :
    (pinned τ).card ≤ 2 * (nextFreshLoss p ρ τ).card + B := by
  classical
  let ess := essentialPositions f Finset.univ
  let S := (pinned τ).filter (fun i => i ∈ ess)
  have hcharge := twice_nextFreshLoss_ge p ρ τ root S
    (fun i hi => by rw [hEq]; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2)
    (fun i _ he => by
      have h := congrFun (hEq.symm.trans he) (fun _ => false)
      exact Bool.noConfusion (h0.symm.trans h))
    (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2)
  have hs : pinned τ ⊆ S ∪ ((Finset.univ : Finset (Fin k)) \ ess) := by
    intro i hi
    by_cases he : i ∈ ess
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he⟩)
  have hcap := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hsmall : ((Finset.univ : Finset (Fin k)) \ ess).card ≤ B := nonessential_card_le hSparse h0
  omega

theorem first_face_charge (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    2 ^ (m + 1) ≤ 2 * (firstFreshLoss c.program (faceSub (m + 1))).card + descriptionBitBound (m + 2) := by
  let ρ : Fin (2 ^ (m + 2)) → Fin (2 ^ (m + 2)) ⊕ Bool := Sum.inl
  have hEq : restrictedWire c.program ρ (c.outputs 0) = mcspSquare (m + 2) :=
    restricted_circuit_eq c hc ρ
  have h := pinned_charge_of_sparse c.program ρ (faceSub (m + 1)) (c.outputs 0)
    hEq (card_accepting_mcspSquare_le _) (mcspSquare_constant_table _ (by omega) false)
  rw [card_pinned_face] at h
  have hsub : nextFreshLoss c.program ρ (faceSub (m + 1)) ⊆ firstFreshLoss c.program (faceSub (m + 1)) := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)) _)

theorem second_face_charge (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    2 ^ m ≤ 2 * (nextFreshLoss c.program (faceSub (m + 1)) (faceSub m)).card +
      descriptionBitBound (m + 2) := by
  have hEq : restrictedWire c.program (faceSub (m + 1)) (c.outputs 0) = middle m :=
    restricted_circuit_eq c hc (faceSub (m + 1))
  have h0 := middle_affine m hm (fun _ => false) false
  rw [affine_constant] at h0
  have h := pinned_charge_of_sparse c.program (faceSub (m + 1)) (faceSub m) (c.outputs 0)
    hEq (middle_sparse m) h0
  rwa [card_pinned_face] at h

theorem two_faces_fresh_budget (m : ℕ) (hm : 5 ≤ m)
    (c : Circuit signature (2 ^ (m + 2)) 1)
    (hc : c.Computes interpretation (single (mcspSquare (m + 2)))) :
    Disjoint (firstFreshLoss c.program (faceSub (m + 1))) (nextFreshLoss c.program (faceSub (m + 1)) (faceSub m)) ∧
    2 * 2 ^ m + 2 ^ m / 2280 + (firstFreshLoss c.program (faceSub (m + 1))).card +
      (nextFreshLoss c.program (faceSub (m + 1)) (faceSub m)).card ≤
        c.size + 3 * descriptionBitBound (m + 2) + 3 := by
  let ρ := faceSub (m + 1)
  let τ := faceSub m
  have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (fresh c.program ρ))
  have h2 := Finset.card_sdiff_add_card_eq_card (fresh_nested c.program ρ τ)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  change (firstFreshLoss c.program ρ).card + (fresh c.program ρ).card = c.size at h1
  change (nextFreshLoss c.program ρ τ).card + (fresh c.program (compose ρ τ)).card =
    (fresh c.program ρ).card at h2
  have hF := forest_size (inner_sparse m) (inner_affine m hm)
  have hSize := fresh_complexity_le c.program (compose ρ τ) (c.outputs 0)
  have he : restrictedWire c.program (compose ρ τ) (c.outputs 0) = inner m := by
    rw [restricted_circuit_eq c hc]
    funext x
    rw [substitute_compose]
    rfl
  rw [he] at hSize
  refine ⟨fresh_losses_disjoint c.program ρ τ, ?_⟩
  dsimp only [ρ, τ] at h1 h2 hSize
  omega

/-- At 32 variables, the second face eliminates this many previously
nonredundant original gate indices. -/
theorem second_face_charge_32 (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32))) :
    536857076 ≤ (nextFreshLoss c.program (faceSub 31) (faceSub 30)).card := by
  have h := second_face_charge 30 (by decide) c hc
  rw [show descriptionBitBound (30 + 2) = 27672 by decide] at h
  change 1073741824 ≤ 2 * (nextFreshLoss c.program (faceSub 31) (faceSub 30)).card + 27672 at h
  omega

#print axioms first_face_charge
#print axioms second_face_charge
#print axioms two_faces_fresh_budget
#print axioms second_face_charge_32

end PvsNP.Frontier.TwoScaleFresh
