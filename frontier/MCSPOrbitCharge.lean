module

public import MCSPInvariantControl

/-! Test the transported cuts and pooled reader counts on the symmetric control. -/

@[expose] public section

namespace PvsNP.Frontier.OrbitCharge

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut Downstream
open PermutedCut InvariantControl MatchedCharge

variable {r s : ℕ}

def bandLabel (r s : ℕ) (i : Fin (2 ^ (r + (s + 1)))) : BitString r × Bool :=
  let p := (pointEquiv r s).symm i
  (p.1, lowWeight p.2)

@[simp] theorem bandLabel_point (a : BitString r) (z : BitString (s + 1)) :
    bandLabel r s (point a z) = (a, lowWeight z) := by
  simp [bandLabel, point]

theorem control_equality (selector : BitString (2 ^ (r + (s + 1))))
    (twoSides : ∀ (a : BitString r) (b side : Bool), ∃ z ∈ retained (s + 1),
      lowWeight z = b ∧ selector (point a z) = side)
    (f g : BitString r × Bool → Bool) :
    control r s (splice selector (f ∘ bandLabel r s) (g ∘ bandLabel r s)) = true ↔ f = g := by
  constructor
  · intro hc
    funext q
    obtain ⟨a, b⟩ := q
    obtain ⟨u, hu, hub, hus⟩ := twoSides a b true
    obtain ⟨v, hv, hvb, hvs⟩ := twoSides a b false
    have he := (control_iff _).mp hc a u v hu hv (hub.trans hvb.symm)
    simpa [splice, hus, hvs, hub, hvb] using he
  · rintro rfl
    rw [splice_self]
    apply (control_iff _).mpr
    intro a u v _ _ h
    simp [h]

private theorem weight_sum {w : ℕ} (z : BitString w) :
    weight z = ∑ i, if z i then (1 : ℕ) else 0 := by
  rw [← Finset.sum_filter]
  simp [weight]

private theorem weight_cons {w : ℕ} (b : Bool) (z : BitString w) :
    weight (Fin.cons b z) = weight z + if b then 1 else 0 := by
  rw [weight_sum, weight_sum, Fin.sum_univ_succ]
  simp [Nat.add_comm]

private theorem weight_unit {w : ℕ} (j : Fin w) : weight (unit j) = 1 := by
  unfold weight
  have h : (Finset.univ.filter fun i => unit j i = true) = {j} := by ext i; simp [unit]
  rw [h, Finset.card_singleton]

private theorem retained_of_weight {w : ℕ} (z : BitString w) (h : 2 ≤ weight z) :
    z ∈ retained w := by
  classical
  simp only [retained, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨j, rfl⟩
  rw [weight_unit] at h
  omega

def suffixForBand (b : Bool) : BitString 22 :=
  if b then Fin.cons true (Fin.cons true (fun _ : Fin 20 => false)) else fun _ => true

/-- Each band contains both endpoints of a split pair at one fixed suffix. -/
theorem split_pair_in_band (b d : Bool) :
    Fin.cons d (suffixForBand b) ∈ retained 23 ∧ lowWeight (Fin.cons d (suffixForBand b)) = b := by
  have hzero : weight (fun _ : Fin 20 => false) = 0 := by simp [weight]
  have hone : weight (fun _ : Fin 22 => true) = 22 := by simp [weight]
  have htail : weight (suffixForBand b) = if b then 2 else 22 := by
    cases b
    · exact hone
    · change weight (Fin.cons true (Fin.cons true (fun _ : Fin 20 => false))) = 2
      rw [weight_cons (w := 21), weight_cons (w := 20), hzero]
      rfl
  have hw : weight (Fin.cons d (suffixForBand b)) =
      (if b then 2 else 22) + (if d then 1 else 0) := by
    rw [weight_cons, htail]
  have hge : 2 ≤ weight (Fin.cons d (suffixForBand b)) := by
    rw [hw]
    cases b <;> cases d <;> decide
  refine ⟨retained_of_weight (w := 23) (Fin.cons d (suffixForBand b)) hge, ?_⟩
  unfold lowWeight
  rw [hw]
  cases b <;> cases d <;> decide

theorem base_twoSides (h : BooleanFunction 22) (a : BitString r) (b side : Bool) :
    ∃ z ∈ retained 23, lowWeight z = b ∧ mask r h (point (s := 22) a z) = side := by
  let t := suffixForBand b
  let d := side ^^ h t
  obtain ⟨hz, hb⟩ := split_pair_in_band b d
  refine ⟨Fin.cons d t, hz, hb, ?_⟩
  rw [point_cons, mask_at_position]
  change ((side ^^ h t) ^^ h t) = side
  simp

theorem control32_orbit_width (h : BooleanFunction 22)
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (control 9 22)))
    (j : Fin 23) (owner : Wire (2 ^ 32) c.size → Bool)
    (howner : ∀ i, owner (.input i) = orbitMask (r := 9) h j i) :
    1024 ≤ (crossingWires c.program owner).card := by
  have heq := transport_equality (control 9 22) (tablePerm (splitSwap 9 j))
    (control_perm (Equiv.swap 0 j)) (mask 9 h) (bandLabel 9 22)
    (control_equality (mask 9 h) (base_twoSides h))
  obtain ⟨choose, hinj, hchoose⟩ := exists_distinct_downstream_sources _ _
    (orbitMask (r := 9) h j) c hc heq owner howner
  have hw := width_of_distinct_sources c.program owner _ choose hinj hchoose
  rw [Fintype.card_prod, BitString.card, Fintype.card_bool] at hw
  exact hw

theorem control32_size :
    complexity interpretation (single (control 9 22)) + 18431 ≤ 2 * 2 ^ 32 := by
  have h := control_size 9 22
  rw [retained_card] at h
  norm_num at h ⊢
  omega

theorem control32_sparse :
    (acceptingTables (control 9 22)).card ≤ 2 ^ (2 ^ 9 * 2 + 2 ^ 9 * (22 + 1)) :=
  control_acceptance_count 9 22 (fun b => ⟨_, split_pair_in_band b false⟩)

theorem control32_rejects_refined_probe (h : BooleanFunction 22)
    (hEq : ∀ f g : RefinedCut.Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g) :
    ∃ f : RefinedCut.Coordinate → Bool,
      mcspSquare 32 (f ∘ RefinedCut.label) = true ∧ control 9 22 (f ∘ RefinedCut.label) = false := by
  classical
  let f : RefinedCut.Coordinate → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hAccept := (hEq f f).mpr rfl
  rw [splice_self] at hAccept
  refine ⟨f, hAccept, Bool.eq_false_of_not_eq_true ?_⟩
  intro hc
  let a : BitString 9 := fun _ => false
  let t := suffixForBand true
  obtain ⟨h0, hb0⟩ := split_pair_in_band true false
  obtain ⟨h1, hb1⟩ := split_pair_in_band true true
  have he := (control_iff (r := 9) (s := 22) _).mp hc a _ _ h0 h1 (hb0.trans hb1.symm)
  rw [point_cons (r := 9) (s := 22), point_cons (r := 9) (s := 22)] at he
  have lab (b : Bool) : RefinedCut.label (position a b t) = RefinedCut.pick a b := by
    change RefinedCut.label (positionEquiv 9 22 (a, b, t)) = _
    simp [RefinedCut.label]
  have hhigh : RefinedCut.high a = RefinedCut.zeroHigh := rfl
  change f (RefinedCut.label (position a false t)) = f (RefinedCut.label (position a true t)) at he
  rw [lab false, lab true] at he
  simp [f, RefinedCut.pick, hhigh] at he

theorem control32_margin (c : Circuit signature (2 ^ 32) 1)
    (hc : c.Computes interpretation (single (control 9 22)))
    (hsize : c.size + 18431 ≤ 2 * 2 ^ 32)
    (sample : Finset (BitString (2 ^ 32))) (h0 : (fun _ => false) ∈ sample)
    (h1 : (fun _ => true) ∈ sample) :
    MultiCertificates.netMargin c.program (c.outputs 0) sample ≤ 5122 := by
  have mate : ∀ z ∈ retained 23, ∃ z' ∈ retained 23, lowWeight z' = lowWeight z ∧ z' ≠ z := by
    intro z _
    let b := lowWeight z
    obtain ⟨h0, hb0⟩ := split_pair_in_band b false
    obtain ⟨h1, hb1⟩ := split_pair_in_band b true
    by_cases he : Fin.cons false (suffixForBand b) = z
    · refine ⟨_, h1, hb1, fun hn => ?_⟩
      have hhead := congrFun (he.trans hn.symm) (0 : Fin 23)
      cases hhead
    · exact ⟨_, h0, hb0, he⟩
  have ht0 := control_inputStates_card 9 22 mate c hc sample false h0
  have ht1 := control_inputStates_card 9 22 mate c hc sample true h1
  rw [retained_card] at ht0 ht1
  norm_num at ht0 ht1 hsize
  rw [MultiCertificates.netMargin_eq]
  omega

/-- The same transported masks stay wide for a permutation-invariant low-charge control. -/
theorem control32_joint_test :
    ∃ h : BooleanFunction 22,
      (∀ f g : RefinedCut.Coordinate → Bool,
        mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g) ∧
      ∃ c : Circuit signature (2 ^ 32) 1,
        c.Computes interpretation (single (control 9 22)) ∧
        c.size = complexity interpretation (single (control 9 22)) ∧ c.size + 18431 ≤ 2 * 2 ^ 32 ∧
        (∀ j (owner : Wire (2 ^ 32) c.size → Bool),
          (∀ i, owner (.input i) = orbitMask (r := 9) h j i) →
            1024 ≤ (crossingWires c.program owner).card) ∧
        ∀ (sample : Finset (BitString (2 ^ 32))) (_ : (fun _ => false) ∈ sample)
          (_ : (fun _ => true) ∈ sample) (sources : Fin 23 → Finset (Wire (2 ^ 32) c.size)),
          matchedMargin c.program (c.outputs 0) sample (Finset.univ.biUnion sources) ≤ 5122 := by
  obtain ⟨h, _, heq⟩ := RefinedCut.exists_refined_equality_cut
  obtain ⟨c, hc, hmin⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single (control 9 22))
  have hsize := hmin ▸ control32_size
  refine ⟨h, heq, c, hc, hmin, hsize, control32_orbit_width h c hc, ?_⟩
  intro sample h0 h1 sources
  exact (matchedMargin_le c.program (c.outputs 0) sample (Finset.univ.biUnion sources)).trans
    (control32_margin c hc hsize sample h0 h1)

#print axioms control_perm
#print axioms control32_sparse
#print axioms control32_rejects_refined_probe
#print axioms control32_joint_test

end PvsNP.Frontier.OrbitCharge
