module

public import MCSPSuperTwoN
public import Complexity.Computability.Circuit.Frontier.Rectangle

/-! A numerical consequence of the current bound and a limitation of the
dense rectangle-free hypothesis for the MCSP complement. -/

@[expose] public section

namespace PvsNP.Frontier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

theorem mcspSquare_32_quantitative :
    2 * 2 ^ 32 + 1800740 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := SuperTwoN.mcspSquare_super_twoN 32 (by decide)
  rw [show descriptionBitBound 32 = 27672 by decide, show (2 : ℕ) ^ 32 / 2280 = 1883757 by decide] at h
  omega

open Cslib.Circuits.Frontier Set in
/-- Remove every left-hand projection of an accepted assignment. The remaining
left side times the entire right side is a rectangle in the complement. -/
theorem not_rectangleFree_compl_of_sparse {ι : Type*} [Finite ι]
    (S : Set (ι → Bool)) (X : Set ι) (B K : ℕ) (hS : S.ncard ≤ B)
    (hleft : K + B ≤ Nat.card (X → Bool)) (hright : K ≤ Nat.card (↥Xᶜ → Bool)) :
    ¬ RectangleFree Sᶜ K := by
  classical
  let projections : Set (X → Bool) := X.domRestrict '' S
  have hproj : projections.ncard ≤ S.ncard := Set.ncard_image_le (Set.toFinite S)
  have hsum := Set.ncard_add_ncard_compl projections
  have hA : K ≤ projectionsᶜ.ncard := by omega
  have hB : K ≤ (univ : Set (↥Xᶜ → Bool)).ncard := by simpa only [Set.ncard_univ] using hright
  have hsub : rectangle X projectionsᶜ (univ : Set (↥Xᶜ → Bool)) ⊆ Sᶜ := by
    intro x hx hs
    exact hx.1 ⟨x, hs, rfl⟩
  intro h
  exact (h.ncard_lt_or X projectionsᶜ univ hsub).elim (not_lt_of_ge hA) (not_lt_of_ge hB)

open Cslib.Circuits.Frontier Set in
theorem mcspSquare_no_rectangle_free_complement (m K : ℕ) (X : Set (Fin (2 ^ m)))
    (hleft : K + 2 ^ descriptionBitBound m ≤ Nat.card (X → Bool))
    (hright : K ≤ Nat.card (↥Xᶜ → Bool)) :
    ¬ RectangleFree {T : BitString (2 ^ m) | mcspSquare m T = true}ᶜ K := by
  let S : Set (BitString (2 ^ m)) := {T | mcspSquare m T = true}
  have he : (↑(acceptingTables (mcspSquare m)) : Set (BitString (2 ^ m))) = S := by
    ext T
    simp [S, acceptingTables]
  have hS : S.ncard ≤ 2 ^ descriptionBitBound m := by
    rw [← he, Set.ncard_coe_finset]
    exact card_accepting_mcspSquare_le m
  exact not_rectangleFree_compl_of_sparse S X _ _ hS hleft hright

#print axioms mcspSquare_32_quantitative
#print axioms mcspSquare_no_rectangle_free_complement

end PvsNP.Frontier
