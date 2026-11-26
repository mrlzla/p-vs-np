module

public import MCSPSuperTwoN
public import MCSPMinorityResidual
public import Complexity.Computability.Circuit.Boolean.Synthesis

/-! Replace degree-1 affine probes with rank-1 quadratic probes
`quad a b0 c d z = affine a b0 z ^^ (dot c z && dot d z)`.

On every subset `U ⊆ {0,1}^m`, at most `1/4` of `(U.card - 1)`-weighted rank-1
quadratic probes are constant on `U` (`4 * (|U| - 1) * |constQuad U b| ≤ 2 ^ (3m + 1)`),
breaking the affine 2-plane bottleneck (`3/8`) and eliminating the `+ 2N` linear penalty
in the two-corner forest averaging lemma. Combining this with the tight `6 B + 112 slack`
root/stop-input budget from `MCSPMonotoneForest` gives slope `281 / 280` and strengthens
the unconditional De Morgan lower bound for `mcspSquare 32` by `+28,287,454` gates to
`8,620,555,905` gates from the forest alone and `8,620,555,922` gates with 17
minority-pinning fresh losses. -/

@[expose] public section

namespace PvsNP.Frontier.QuadraticForest

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN
open ForestPinning RestrictionCharges FreshCharges PairSeparation
open MinorityResidual NestedFaces
open scoped Classical

/-! ### Bitwise XOR, `dot` linearity, and rank-1 quadratic probes -/

/-- Coordinatewise XOR on `BitString m`. -/
def bitXor {m : ℕ} (x y : BitString m) : BitString m := fun i => x i ^^ y i

/-- All-false vector in `BitString m`. -/
def zeroVec (m : ℕ) : BitString m := fun _ => false

theorem bitXor_comm {m : ℕ} (x y : BitString m) : bitXor x y = bitXor y x := by
  funext i; exact Bool.xor_comm (x i) (y i)

theorem bitXor_assoc {m : ℕ} (x y z : BitString m) :
    bitXor (bitXor x y) z = bitXor x (bitXor y z) := by
  funext i; exact Bool.xor_assoc (x i) (y i) (z i)

theorem bitXor_self {m : ℕ} (x : BitString m) : bitXor x x = zeroVec m := by
  funext i; exact Bool.xor_self (x i)

theorem bitXor_zero_left {m : ℕ} (x : BitString m) : bitXor (zeroVec m) x = x := by
  funext i; exact Bool.false_xor (x i)

theorem bitXor_zero_right {m : ℕ} (x : BitString m) : bitXor x (zeroVec m) = x := by
  funext i; exact Bool.xor_false (x i)

theorem bitXor_cancel_self_left {m : ℕ} (x y : BitString m) : bitXor x (bitXor x y) = y := by
  rw [← bitXor_assoc, bitXor_self, bitXor_zero_left]

theorem bitXor_cancel_self_right {m : ℕ} (x y : BitString m) : bitXor (bitXor x y) y = x := by
  rw [bitXor_assoc, bitXor_self, bitXor_zero_right]

theorem bitXor_left_inj {m : ℕ} (y : BitString m) : Function.Injective (fun x => bitXor x y) := by
  intro x1 x2 h
  have := congrArg (fun z => bitXor z y) h
  simpa only [bitXor_cancel_self_right] using this

theorem bitXor_right_inj {m : ℕ} (x : BitString m) : Function.Injective (bitXor x) := by
  intro y1 y2 h
  have := congrArg (bitXor x) h
  simpa only [bitXor_cancel_self_left] using this

theorem bitXor_eq_iff {m : ℕ} (x y z : BitString m) : bitXor x y = z ↔ x = bitXor z y := by
  constructor
  · rintro rfl; exact (bitXor_cancel_self_right x y).symm
  · rintro rfl; exact bitXor_cancel_self_right z y

theorem dot_zero_left : ∀ {m : ℕ} (z : BitString m), dot (zeroVec m) z = false
  | 0, _ => rfl
  | m + 1, z => by
    dsimp only [dot]
    rw [show Fin.tail (zeroVec (m + 1)) = zeroVec m from rfl, dot_zero_left]
    simp [zeroVec]

theorem dot_zero_right : ∀ {m : ℕ} (a : BitString m), dot a (zeroVec m) = false
  | 0, _ => rfl
  | m + 1, a => by
    dsimp only [dot]
    rw [show Fin.tail (zeroVec (m + 1)) = zeroVec m from rfl, dot_zero_right]
    simp [zeroVec]

theorem dot_bitXor_right : ∀ {m : ℕ} (a x y : BitString m),
    dot a (bitXor x y) = (dot a x ^^ dot a y)
  | 0, _, _, _ => rfl
  | _ + 1, a, x, y => by
    dsimp only [dot]
    rw [show Fin.tail (bitXor x y) = bitXor (Fin.tail x) (Fin.tail y) from rfl,
      dot_bitXor_right (Fin.tail a) (Fin.tail x) (Fin.tail y)]
    change ((a 0 && (x 0 ^^ y 0)) ^^ (dot (Fin.tail a) (Fin.tail x) ^^ dot (Fin.tail a) (Fin.tail y))) =
      (((a 0 && x 0) ^^ dot (Fin.tail a) (Fin.tail x)) ^^
       ((a 0 && y 0) ^^ dot (Fin.tail a) (Fin.tail y)))
    cases a 0 <;> cases x 0 <;> cases y 0 <;>
      cases dot (Fin.tail a) (Fin.tail x) <;> cases dot (Fin.tail a) (Fin.tail y) <;> decide

theorem dot_bitXor_left : ∀ {m : ℕ} (a b z : BitString m),
    dot (bitXor a b) z = (dot a z ^^ dot b z)
  | 0, _, _, _ => rfl
  | _ + 1, a, b, z => by
    dsimp only [dot]
    rw [show Fin.tail (bitXor a b) = bitXor (Fin.tail a) (Fin.tail b) from rfl,
      dot_bitXor_left (Fin.tail a) (Fin.tail b) (Fin.tail z)]
    change (((a 0 ^^ b 0) && z 0) ^^ (dot (Fin.tail a) (Fin.tail z) ^^ dot (Fin.tail b) (Fin.tail z))) =
      (((a 0 && z 0) ^^ dot (Fin.tail a) (Fin.tail z)) ^^
       ((b 0 && z 0) ^^ dot (Fin.tail b) (Fin.tail z)))
    cases a 0 <;> cases b 0 <;> cases z 0 <;>
      cases dot (Fin.tail a) (Fin.tail z) <;> cases dot (Fin.tail b) (Fin.tail z) <;> decide

theorem dot_basisVec : ∀ {m : ℕ} (i : Fin m) (w : BitString m),
    dot (fun j => decide (j = i)) w = w i
  | 0, i, _ => Fin.elim0 i
  | m + 1, i, w => by
    cases i using Fin.cases with
    | zero =>
      dsimp only [dot]
      rw [show Fin.tail (fun j : Fin (m + 1) => decide (j = 0)) = zeroVec m from
        funext fun j => by simp [Fin.tail, zeroVec], dot_zero_left]
      simp
    | succ i' =>
      dsimp only [dot]
      rw [show Fin.tail (fun j : Fin (m + 1) => decide (j = i'.succ)) =
        (fun j : Fin m => decide (j = i')) from funext fun j => by simp [Fin.tail, Fin.succ_inj],
        dot_basisVec i' (Fin.tail w)]
      simp [(Fin.succ_ne_zero i').symm]
      rfl

theorem affine_bitXor_param {m : ℕ} (a a' : BitString m) (b0 b0' : Bool) (z : BitString m) :
    affine (bitXor a a') (b0 ^^ b0') z = (affine a b0 z ^^ affine a' b0' z) := by
  simp only [affine, dot_bitXor_left]
  cases b0 <;> cases b0' <;> cases dot a z <;> cases dot a' z <;> decide

/-- Rank-1 quadratic Boolean probe `z ↦ affine a b0 z ^^ (dot c z && dot d z)`. -/
def quad {m : ℕ} (a : BitString m) (b0 : Bool) (c d : BitString m) (z : BitString m) : Bool :=
  affine a b0 z ^^ (dot c z && dot d z)

theorem quad_bitXor_affine {m : ℕ} (a a' : BitString m) (b0 b0' : Bool)
    (c d z : BitString m) :
    quad (bitXor a a') (b0 ^^ b0') c d z = (quad a b0 c d z ^^ affine a' b0' z) := by
  simp only [quad, affine_bitXor_param]
  cases affine a b0 z <;> cases affine a' b0' z <;> cases (dot c z && dot d z) <;> decide

theorem quad_square_xor {m : ℕ} (y u1 u2 c d : BitString m) :
    ((((dot c y && dot d y) ^^ (dot c (bitXor y u1) && dot d (bitXor y u1))) ^^
      (dot c (bitXor y u2) && dot d (bitXor y u2))) ^^
      (dot c (bitXor (bitXor y u1) u2) && dot d (bitXor (bitXor y u1) u2))) =
      ((dot c u1 && dot d u2) ^^ (dot c u2 && dot d u1)) := by
  simp only [dot_bitXor_right]
  generalize dot c y = c0
  generalize dot c u1 = c1
  generalize dot c u2 = c2
  generalize dot d y = d0
  generalize dot d u1 = d1
  generalize dot d u2 = d2
  cases c0 <;> cases c1 <;> cases c2 <;> cases d0 <;> cases d1 <;> cases d2 <;> decide

theorem affine_square_xor {m : ℕ} (a : BitString m) (b0 : Bool) (y u1 u2 : BitString m) :
    ((((affine a b0 y ^^ affine a b0 (bitXor y u1)) ^^
      affine a b0 (bitXor y u2)) ^^
      affine a b0 (bitXor (bitXor y u1) u2))) = false := by
  simp only [affine, dot_bitXor_right]
  generalize b0 = b
  generalize dot a y = a0
  generalize dot a u1 = a1
  generalize dot a u2 = a2
  cases b <;> cases a0 <;> cases a1 <;> cases a2 <;> decide

private theorem bool_xor_four_split (x0 x1 x2 x3 y0 y1 y2 y3 : Bool) :
    ((((x0 ^^ y0) ^^ (x1 ^^ y1)) ^^ (x2 ^^ y2)) ^^ (x3 ^^ y3)) =
      ((((x0 ^^ x1) ^^ x2) ^^ x3) ^^ (((y0 ^^ y1) ^^ y2) ^^ y3)) := by
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;>
    cases y0 <;> cases y1 <;> cases y2 <;> cases y3 <;> decide

/-- If a rank-1 quadratic probe is constant on a 2-plane square
`{y, y ⊕ u1, y ⊕ u2, y ⊕ u1 ⊕ u2}`, then `(c · u1)(d · u2) ⊕ (c · u2)(d · u1) = 0`. -/
theorem det_zero_of_quad_const_on_square {m : ℕ} {a : BitString m} {b0 target : Bool}
    {c d y u1 u2 : BitString m}
    (h0 : quad a b0 c d y = target)
    (h1 : quad a b0 c d (bitXor y u1) = target)
    (h2 : quad a b0 c d (bitXor y u2) = target)
    (h3 : quad a b0 c d (bitXor (bitXor y u1) u2) = target) :
    ((dot c u1 && dot d u2) ^^ (dot c u2 && dot d u1)) = false := by
  have hConst : ((((quad a b0 c d y ^^ quad a b0 c d (bitXor y u1)) ^^
      quad a b0 c d (bitXor y u2)) ^^
      quad a b0 c d (bitXor (bitXor y u1) u2))) = false := by
    rw [h0, h1, h2, h3]
    cases target <;> decide
  simp only [quad] at hConst
  rw [bool_xor_four_split, affine_square_xor, quad_square_xor, Bool.false_xor] at hConst
  exact hConst

/-- Every `m`-variable rank-1 quadratic probe has De Morgan circuit complexity at most `12m + 8`. -/
theorem complexity_quad_le {m : ℕ} (a : BitString m) (b0 : Bool) (c d : BitString m) :
    complexity interpretation (single (quad a b0 c d)) ≤ 12 * m + 8 := by
  have hDot (v : BitString m) : complexity interpretation (single (dot v)) ≤ 4 * m + 1 := by
    have hEq : dot v = affine v false := by
      funext z
      exact (Bool.false_xor (dot v z)).symm
    rw [hEq]
    exact complexity_affine_le v false
  have hAnd : complexity interpretation (single fun z => dot c z && dot d z) ≤ 8 * m + 3 :=
    (complexity_and_le (dot c) (dot d)).trans (Nat.le_trans (Nat.add_le_add_right
      (Nat.add_le_add (hDot c) (hDot d)) 1) (by omega))
  have hAff := complexity_affine_le a b0
  have hXor := complexity_xor_le (affine a b0) (fun z => dot c z && dot d z)
  exact hXor.trans (Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add hAff hAnd) 4) (by omega))

/-- For `m ≥ 13`, every rank-1 quadratic truth table is accepted by `mcspSquare m`. -/
theorem mcspSquare_accepts_quad (m : ℕ) (hm : 13 ≤ m) (a : BitString m) (b0 : Bool)
    (c d : BitString m) :
    mcspSquare m (MCSP.truthTable m (quad a b0 c d)) = true := by
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  exact (complexity_quad_le a b0 c d).trans (by nlinarith)

/-- Repair a rank-1 quadratic probe at `P.card` pinned truth-table entries using shared negations. -/
theorem patched_quad_accepted (m : ℕ) (x : BitString (2 ^ m)) (P : Finset (Fin (2 ^ m)))
    (a : BitString m) (b0 : Bool) (c d : BitString m)
    (hBudget : 13 * m + 13 + (m + 2) * P.card ≤ m ^ 2) :
    mcspSquare m (substitute (pinAt x P) (MCSP.truthTable m (quad a b0 c d))) = true := by
  let T := MCSP.truthTable m (quad a b0 c d)
  let D := P.filter fun i => T i ≠ x i
  have hDc : D.card ≤ P.card := Finset.card_filter_le _ _
  let mask : BooleanFunction m := fun z => decide (BitString.equivFin m z ∈ D)
  have hMask : ∀ z : BitString m, mask z = true ↔ BitString.equivFin m z ∈ D := by simp [mask]
  have hEq : MCSP.truthTable m (fun z => quad a b0 c d z ^^ mask z) =
      substitute (pinAt x P) T := by
    funext i
    have hDi := hMask ((BitString.equivFin m).symm i)
    rw [Equiv.apply_symm_apply] at hDi
    change (T i ^^ mask ((BitString.equivFin m).symm i)) = substitute (pinAt x P) T i
    by_cases hi : i ∈ P
    · rw [substitute_inr (show pinAt x P i = .inr (x i) by simp [pinAt, hi])]
      by_cases he : T i = x i
      · have hFalse : mask ((BitString.equivFin m).symm i) = false :=
          Bool.eq_false_of_not_eq_true (fun h => by simpa [D, hi, he] using hDi.mp h)
        rw [hFalse]
        exact (Bool.xor_false (T i)).trans he
      · have hTrue : mask ((BitString.equivFin m).symm i) = true :=
          hDi.mpr (Finset.mem_filter.mpr ⟨hi, he⟩)
        have hx : (!(T i)) = x i := by cases hT : T i <;> cases hx' : x i <;> simp_all
        rw [hTrue]
        exact (Bool.xor_true (T i)).trans hx
    · have hFalse : mask ((BitString.equivFin m).symm i) = false :=
        Bool.eq_false_of_not_eq_true (fun h => hi (Finset.mem_filter.mp (hDi.mp h)).1)
      rw [hFalse, substitute_inl (show pinAt x P i = .inl i by simp [pinAt, hi])]
      exact Bool.xor_false (T i)
  change mcspSquare m (substitute (pinAt x P) T) = true
  rw [← hEq, mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  have hcMask := point_indicator_complexity_le m D
  change complexity interpretation (single mask) ≤ m + D.card * (m + 2) + 1 at hcMask
  have hTermBudget := Nat.mul_le_mul_right (m + 2) hDc
  rw [Nat.mul_comm P.card (m + 2)] at hTermBudget
  have hcQuad := complexity_quad_le a b0 c d
  exact (complexity_xor_le (quad a b0 c d) mask).trans (by omega)

/-! ### Elementary `F_2` span, orthogonality, and exact fiber counting -/

/-- Linear span over `GF(2)` of a list of vectors in `BitString m`. -/
noncomputable def span {m : ℕ} : List (BitString m) → Finset (BitString m)
  | [] => {zeroVec m}
  | v :: L => span L ∪ (span L).image (bitXor v)

/-- Linear independence over `GF(2)` of a list of vectors. -/
def LinIndep {m : ℕ} : List (BitString m) → Prop
  | [] => True
  | v :: L => v ∉ span L ∧ LinIndep L

/-- Orthogonal complement in `(BitString m, dot)`. -/
noncomputable def orth {m : ℕ} (S : Finset (BitString m)) : Finset (BitString m) :=
  Finset.univ.filter fun a => ∀ w ∈ S, dot a w = false

theorem zero_mem_span {m : ℕ} : ∀ L : List (BitString m), zeroVec m ∈ span L
  | [] => Finset.mem_singleton_self _
  | _ :: L => Finset.mem_union_left _ (zero_mem_span L)

theorem bitXor_mem_span {m : ℕ} : ∀ (L : List (BitString m)) {x y : BitString m},
    x ∈ span L → y ∈ span L → bitXor x y ∈ span L
  | [], x, y, hx, hy => by
    simp only [span, Finset.mem_singleton] at hx hy ⊢
    subst hx; subst hy
    exact bitXor_zero_left (zeroVec m)
  | v :: L, x, y, hx, hy => by
    rcases Finset.mem_union.mp hx with hx0 | hx1 <;>
      rcases Finset.mem_union.mp hy with hy0 | hy1
    · exact Finset.mem_union_left _ (bitXor_mem_span L hx0 hy0)
    · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy1
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨bitXor x y',
        bitXor_mem_span L hx0 hy', ?_⟩)
      rw [bitXor_comm v (bitXor x y'), bitXor_assoc, bitXor_comm y' v, ← bitXor_assoc,
        bitXor_comm x v, bitXor_assoc]
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx1
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨bitXor x' y,
        bitXor_mem_span L hx' hy0, ?_⟩)
      rw [bitXor_assoc]
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy1
      refine Finset.mem_union_left _ ?_
      have hCancel : bitXor (bitXor v x') (bitXor v y') = bitXor x' y' := by
        rw [bitXor_comm v x', ← bitXor_assoc, bitXor_cancel_self_right, bitXor_comm x' y']
      rw [hCancel]
      exact bitXor_mem_span L hx' hy'

theorem mem_span_of_mem {m : ℕ} : ∀ {L : List (BitString m)} {v : BitString m},
    v ∈ L → v ∈ span L
  | u :: L, v, hv => by
    rcases List.mem_cons.mp hv with rfl | hvL
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨zeroVec m, zero_mem_span L, bitXor_zero_right v⟩)
    · exact Finset.mem_union_left _ (mem_span_of_mem hvL)

theorem card_span_of_linIndep {m : ℕ} : ∀ {L : List (BitString m)},
    LinIndep L → (span L).card = 2 ^ L.length
  | [], _ => by simp [span]
  | v :: L, ⟨hvNot, hLI⟩ => by
    have hDisj : Disjoint (span L) ((span L).image (bitXor v)) := by
      refine Finset.disjoint_left.mpr fun w hw0 hw1 => ?_
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw1
      have hvEq : bitXor (bitXor v u) u = v := bitXor_cancel_self_right v u
      rw [← hvEq] at hvNot
      exact hvNot (bitXor_mem_span L hw0 hu)
    rw [span, Finset.card_union_of_disjoint hDisj,
      Finset.card_image_of_injective _ (bitXor_right_inj v), card_span_of_linIndep hLI]
    simp [Nat.pow_succ, Nat.mul_two]

private theorem exists_affine_basis_aux {m : ℕ} (U : Finset (BitString m)) (x0 : BitString m) :
    ∀ (k : ℕ) (L : List (BitString m)), 2 ^ m - (span L).card ≤ k →
      LinIndep L → (∀ v ∈ L, bitXor x0 v ∈ U) →
      ∃ L' : List (BitString m),
        LinIndep L' ∧ (∀ v ∈ L', bitXor x0 v ∈ U) ∧ ∀ x ∈ U, bitXor x0 x ∈ span L' := by
  intro k
  induction k with
  | zero =>
    intro L hk hLI hMem
    have hLe : (span L).card ≤ 2 ^ m := by
      have h := Finset.card_le_univ (span L)
      simpa [Fintype.card_fun, BitString] using h
    have hFull : (span L).card = Fintype.card (BitString m) := by
      have hU : Fintype.card (BitString m) = 2 ^ m := by simp [BitString]
      omega
    have hUniv : span L = Finset.univ := Finset.eq_univ_of_card (span L) hFull
    exact ⟨L, hLI, hMem, fun x _ => by rw [hUniv]; exact Finset.mem_univ _⟩
  | succ k ih =>
    intro L hk hLI hMem
    by_cases hCov : ∀ x ∈ U, bitXor x0 x ∈ span L
    · exact ⟨L, hLI, hMem, hCov⟩
    · simp only [not_forall] at hCov
      obtain ⟨x, hxU, hxNot⟩ := hCov
      let v := bitXor x0 x
      have hvIn : v ∈ span (v :: L) :=
        Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨zeroVec m, zero_mem_span L, bitXor_zero_right v⟩)
      have hLt : (span L).card < (span (v :: L)).card :=
        Finset.card_lt_card ⟨Finset.subset_union_left, fun h => hxNot (h hvIn)⟩
      have hvU : bitXor x0 v ∈ U := by
        simpa only [v, bitXor_cancel_self_left] using hxU
      refine ih (v :: L) (by omega) ⟨hxNot, hLI⟩ ?_
      intro u hu
      rcases List.mem_cons.mp hu with rfl | huL
      · exact hvU
      · exact hMem u huL

/-- Every point `x0 ∈ U` anchors an affine basis `L` inside `U ⊕ x0`. -/
theorem exists_affine_basis {m : ℕ} (U : Finset (BitString m)) (x0 : BitString m) :
    ∃ L : List (BitString m),
      LinIndep L ∧ (∀ v ∈ L, bitXor x0 v ∈ U) ∧ ∀ x ∈ U, bitXor x0 x ∈ span L :=
  exists_affine_basis_aux U x0 (2 ^ m) [] (Nat.sub_le _ _) trivial (fun _ h => by cases h)

private def chi {m : ℕ} (w a : BitString m) : ℤ := if dot a w then -1 else 1

private theorem sum_chi_over_a {m : ℕ} (w : BitString m) :
    (∑ a : BitString m, chi w a) = if w = zeroVec m then ((2 ^ m : ℕ) : ℤ) else 0 := by
  by_cases hw : w = zeroVec m
  · subst hw
    have hOne (a : BitString m) : chi (zeroVec m) a = 1 := by simp [chi, dot_zero_right]
    simp [hOne, BitString]
  · simp only [hw, ↓reduceIte]
    have hEx : ∃ i : Fin m, w i = true := by
      by_contra hNo
      apply hw
      funext i
      exact Bool.eq_false_of_not_eq_true fun hi => hNo ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hEx
    let e : BitString m := fun j => decide (j = i)
    refine Finset.sum_involution (fun a _ => bitXor a e) ?_ ?_ (fun a _ => Finset.mem_univ _)
      (fun a _ => bitXor_cancel_self_right a e)
    · intro a _
      have hFlip : dot (bitXor a e) w = !(dot a w) := by
        rw [dot_bitXor_left, dot_basisVec i w, hi]
        cases dot a w <;> rfl
      simp only [chi, hFlip]
      cases dot a w <;> norm_num
    · intro a _ _ hEq
      have hAtI := congrFun hEq i
      have heI : e i = true := by simp [e]
      change (a i ^^ e i) = a i at hAtI
      rw [heI] at hAtI
      cases ha : a i <;> simp [ha] at hAtI

private theorem sum_chi_over_subgroup {m : ℕ} (S : Finset (BitString m))
    (_hZero : zeroVec m ∈ S) (hAdd : ∀ x ∈ S, ∀ y ∈ S, bitXor x y ∈ S)
    (a : BitString m) :
    (∑ w ∈ S, chi w a) = if a ∈ orth S then (S.card : ℤ) else 0 := by
  by_cases ha : a ∈ orth S
  · have hOne : ∀ w ∈ S, chi w a = 1 := fun w hw => by
      have hd : dot a w = false := (Finset.mem_filter.mp ha).2 w hw
      simp [chi, hd]
    simp [ha, Finset.sum_congr rfl hOne]
  · simp only [ha, ↓reduceIte]
    have hEx : ∃ w0 ∈ S, dot a w0 = true := by
      by_contra hNo
      apply ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w hw =>
        Bool.eq_false_of_not_eq_true fun hT => hNo ⟨w, hw, hT⟩⟩
    obtain ⟨w0, hw0, hDot0⟩ := hEx
    have hw0Ne : w0 ≠ zeroVec m := by
      intro hEq
      rw [hEq, dot_zero_right] at hDot0
      cases hDot0
    refine Finset.sum_involution (fun w _ => bitXor w w0) ?_ ?_
      (fun w hw => hAdd w hw w0 hw0) (fun w _ => bitXor_cancel_self_right w w0)
    · intro w _
      have hFlip : dot a (bitXor w w0) = !(dot a w) := by
        rw [dot_bitXor_right, hDot0]
        cases dot a w <;> rfl
      simp only [chi, hFlip]
      cases dot a w <;> norm_num
    · intro w _ _ hEq
      have hC : zeroVec m = w0 := by
        have := congrArg (bitXor w) hEq
        simpa only [bitXor_cancel_self_left, bitXor_self] using this.symm
      exact hw0Ne hC.symm

theorem card_orth_mul_card_span {m : ℕ} (L : List (BitString m)) :
    (orth (span L)).card * (span L).card = 2 ^ m := by
  have hLHS : (∑ a : BitString m, ∑ w ∈ span L, chi w a) =
      ((orth (span L)).card : ℤ) * ((span L).card : ℤ) := by
    calc
      (∑ a : BitString m, ∑ w ∈ span L, chi w a)
          = ∑ a : BitString m, (if a ∈ orth (span L) then ((span L).card : ℤ) else 0) :=
        Finset.sum_congr rfl fun a _ =>
          sum_chi_over_subgroup (span L) (zero_mem_span L) (fun _ hx _ hy => bitXor_mem_span L hx hy) a
      _ = ∑ a ∈ Finset.univ ∩ orth (span L), ((span L).card : ℤ) := Finset.sum_ite_mem Finset.univ (orth (span L)) _
      _ = ((orth (span L)).card : ℤ) * ((span L).card : ℤ) := by
        rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hRHS : (∑ a : BitString m, ∑ w ∈ span L, chi w a) = ((2 ^ m : ℕ) : ℤ) := by
    rw [Finset.sum_comm]
    calc
      (∑ w ∈ span L, ∑ a : BitString m, chi w a)
          = ∑ w ∈ span L, (if w = zeroVec m then ((2 ^ m : ℕ) : ℤ) else 0) :=
        Finset.sum_congr rfl fun w _ => sum_chi_over_a w
      _ = ((2 ^ m : ℕ) : ℤ) := by
        rw [Finset.sum_eq_single_of_mem (zeroVec m) (zero_mem_span L)]
        · simp
        · intro w _ hw; simp [hw]
  have hInt : ((orth (span L)).card * (span L).card : ℕ) = ((2 ^ m : ℕ) : ℤ) := by
    push_cast
    exact hLHS.symm.trans hRHS
  exact Int.ofNat.inj hInt

theorem linIndep_length_le {m : ℕ} {L : List (BitString m)} (hLI : LinIndep L) :
    L.length ≤ m := by
  have hMul := card_orth_mul_card_span L
  rw [card_span_of_linIndep hLI] at hMul
  have hZeroMem : zeroVec m ∈ orth (span L) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun w _ => dot_zero_left w⟩
  have hPos : 1 ≤ (orth (span L)).card := Finset.card_pos.mpr ⟨zeroVec m, hZeroMem⟩
  have hPow : 2 ^ L.length ≤ 2 ^ m := by
    calc
      2 ^ L.length = 1 * 2 ^ L.length := (Nat.one_mul _).symm
      _ ≤ (orth (span L)).card * 2 ^ L.length := Nat.mul_le_mul_right _ hPos
      _ = 2 ^ m := hMul
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hPow

theorem card_orth_linIndep {m : ℕ} {L : List (BitString m)} (hLI : LinIndep L) :
    (orth (span L)).card = 2 ^ (m - L.length) := by
  have hLe := linIndep_length_le hLI
  have hMul := card_orth_mul_card_span L
  rw [card_span_of_linIndep hLI] at hMul
  have hPow : 2 ^ (m - L.length) * 2 ^ L.length = 2 ^ m := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hLe]
  exact Nat.mul_right_cancel (by positivity) (hMul.trans hPow.symm)

private theorem orth_span_iff {m : ℕ} : ∀ (L : List (BitString m)) (a : BitString m),
    a ∈ orth (span L) ↔ ∀ i : Fin L.length, dot a (L.get i) = false
  | [], a => by
    simp only [orth, span, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _ w hw; subst hw; exact dot_zero_right a
  | v :: L, a => by
    simp only [orth, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h i
      cases i using Fin.cases with
      | zero => exact h v (mem_span_of_mem List.mem_cons_self)
      | succ j => exact h ((v :: L).get j.succ) (mem_span_of_mem (List.get_mem _ _))
    · intro h w hw
      have hv : dot a v = false := h 0
      have hRest : a ∈ orth (span L) :=
        (orth_span_iff L a).mpr fun j => h j.succ
      have hSpanL : ∀ u ∈ span L, dot a u = false := (Finset.mem_filter.mp hRest).2
      rw [span] at hw
      rcases Finset.mem_union.mp hw with hu | hImg
      · exact hSpanL w hu
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hImg
        rw [dot_bitXor_right, hv, hSpanL u hu]
        rfl

/-- Evaluation of `a ↦ (a · v₁, ..., a · v_d)` on a basis `L`. -/
def evalDots {m : ℕ} (L : List (BitString m)) (a : BitString m) : Fin L.length → Bool :=
  fun i => dot a (L.get i)

theorem evalDots_surjective {m : ℕ} : ∀ {L : List (BitString m)}, LinIndep L →
    Function.Surjective (evalDots L)
  | [], _, t => ⟨zeroVec m, funext fun i => Fin.elim0 i⟩
  | v :: L, hLIV, t => by
    have hLI : LinIndep L := hLIV.2
    have hLeSucc : L.length + 1 ≤ m := linIndep_length_le hLIV
    have hOrthL : (orth (span L)).card = 2 ^ (m - L.length) := card_orth_linIndep hLI
    have hOrthVL : (orth (span (v :: L))).card = 2 ^ (m - (L.length + 1)) :=
      card_orth_linIndep hLIV
    have hLtPow : m - (L.length + 1) < m - L.length := by omega
    have hCardLt : (orth (span (v :: L))).card < (orth (span L)).card := by
      rw [hOrthL, hOrthVL]
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) hLtPow
    have hNotSub : ¬ (orth (span L) ⊆ orth (span (v :: L))) :=
      fun hSub => Nat.not_le_of_lt hCardLt (Finset.card_le_card hSub)
    rw [Finset.not_subset] at hNotSub
    obtain ⟨a0, ha0In, ha0Out⟩ := hNotSub
    have ha0DotV : dot a0 v = true := by
      by_contra hF
      have hVF : dot a0 v = false := Bool.eq_false_of_not_eq_true hF
      apply ha0Out
      rw [orth_span_iff (v :: L) a0]
      intro i
      cases i using Fin.cases with
      | zero => exact hVF
      | succ j => exact (orth_span_iff L a0).mp ha0In j
    have ha0Rest : ∀ j : Fin L.length, dot a0 (L.get j) = false :=
      (orth_span_iff L a0).mp ha0In
    obtain ⟨a1, ha1⟩ := evalDots_surjective hLI (fun j : Fin L.length => t j.succ)
    by_cases hMatch : dot a1 v = t 0
    · refine ⟨a1, funext fun i => ?_⟩
      cases i using Fin.cases with
      | zero => exact hMatch
      | succ j => simpa [evalDots] using congrFun ha1 j
    · refine ⟨bitXor a1 a0, funext fun i => ?_⟩
      cases i using Fin.cases with
      | zero =>
        change dot (bitXor a1 a0) v = t 0
        rw [dot_bitXor_left, ha0DotV]
        cases ha10 : dot a1 v <;> cases ht0 : t 0 <;> simp_all
      | succ j =>
        change dot (bitXor a1 a0) (L.get j) = t j.succ
        rw [dot_bitXor_left, ha0Rest j, Bool.xor_false]
        exact congrFun ha1 j

theorem card_evalDots_fiber {m : ℕ} {L : List (BitString m)} (hLI : LinIndep L)
    (t : Fin L.length → Bool) :
    (Finset.univ.filter fun a : BitString m => evalDots L a = t).card = 2 ^ (m - L.length) := by
  obtain ⟨a0, ha0⟩ := evalDots_surjective hLI t
  rw [← card_orth_linIndep hLI]
  refine Finset.card_bij (fun a _ => bitXor a a0) ?_ ?_ ?_
  · intro a ha
    have haEq : evalDots L a = t := (Finset.mem_filter.mp ha).2
    rw [orth_span_iff L]
    intro i
    have hi1 : dot a (L.get i) = t i := congrFun haEq i
    have hi0 : dot a0 (L.get i) = t i := congrFun ha0 i
    rw [dot_bitXor_left, hi1, hi0, Bool.xor_self]
  · intro a1 _ a2 _ hEq
    exact bitXor_left_inj a0 hEq
  · intro b hb
    refine ⟨bitXor b a0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext fun i => ?_⟩,
      bitXor_cancel_self_right b a0⟩
    change dot (bitXor b a0) (L.get i) = t i
    rw [dot_bitXor_left, (orth_span_iff L b).mp hb i, Bool.false_xor]
    exact congrFun ha0 i

theorem card_constAffines_false {m : ℕ} (U : Finset (BitString m)) (x0 : BitString m) (hx0 : x0 ∈ U)
    (L : List (BitString m)) (hLI : LinIndep L)
    (hMem : ∀ v ∈ L, bitXor x0 v ∈ U) (hCov : ∀ x ∈ U, bitXor x0 x ∈ span L) :
    (constAffines U false).card = 2 ^ (m - L.length) := by
  rw [← card_orth_linIndep hLI]
  refine Finset.card_bij (fun ab _ => ab.1) ?_ ?_ ?_
  · intro ⟨a, b0⟩ hab
    have hOn := (Finset.mem_filter.mp hab).2
    have hb0 : b0 = dot a x0 := by
      have hx := hOn x0 hx0
      change (b0 ^^ dot a x0) = false at hx
      revert hx; cases b0 <;> cases dot a x0 <;> decide
    rw [orth_span_iff L a]
    intro i
    have hV := hOn (bitXor x0 (L.get i)) (hMem (L.get i) (List.get_mem L i))
    change (b0 ^^ dot a (bitXor x0 (L.get i))) = false at hV
    rw [dot_bitXor_right, hb0] at hV
    revert hV; cases dot a x0 <;> cases dot a (L.get i) <;> decide
  · intro ⟨a1, b1⟩ h1 ⟨a2, b2⟩ h2 hEq
    change a1 = a2 at hEq
    subst hEq
    have hx1 := (Finset.mem_filter.mp h1).2 x0 hx0
    have hx2 := (Finset.mem_filter.mp h2).2 x0 hx0
    change (b1 ^^ dot a1 x0) = false at hx1
    change (b2 ^^ dot a1 x0) = false at hx2
    have hb : b1 = b2 := by
      revert hx1 hx2; cases b1 <;> cases b2 <;> cases dot a1 x0 <;> decide
    exact Prod.ext rfl hb
  · intro a ha
    refine ⟨(a, dot a x0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩, rfl⟩
    have hOrth : ∀ w ∈ span L, dot a w = false := (Finset.mem_filter.mp ha).2
    have hDotZ : dot a z = dot a x0 := by
      have hzSpan := hOrth (bitXor x0 z) (hCov z hz)
      rw [dot_bitXor_right] at hzSpan
      revert hzSpan; cases dot a x0 <;> cases dot a z <;> decide
    change (dot a x0 ^^ dot a z) = false
    rw [hDotZ, Bool.xor_self]

private theorem card_filter_evalDots_pair {m : ℕ} (L : List (BitString m)) (hLI : LinIndep L)
    (P : (Fin L.length → Bool) → (Fin L.length → Bool) → Bool) :
    (Finset.univ.filter fun cd : BitString m × BitString m =>
      P (evalDots L cd.1) (evalDots L cd.2) = true).card =
      (Finset.univ.filter fun t : (Fin L.length → Bool) × (Fin L.length → Bool) =>
        P t.1 t.2 = true).card * 2 ^ (2 * (m - L.length)) := by
  let G : Finset ((Fin L.length → Bool) × (Fin L.length → Bool)) :=
    Finset.univ.filter fun t => P t.1 t.2 = true
  let fiber (t : (Fin L.length → Bool) × (Fin L.length → Bool)) :
      Finset (BitString m × BitString m) :=
    (Finset.univ.filter fun c => evalDots L c = t.1) ×ˢ
      (Finset.univ.filter fun d => evalDots L d = t.2)
  have hEq : (Finset.univ.filter fun cd : BitString m × BitString m =>
      P (evalDots L cd.1) (evalDots L cd.2) = true) = G.biUnion fiber := by
    ext cd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_product, G, fiber]
    constructor
    · intro h
      exact ⟨(evalDots L cd.1, evalDots L cd.2), h, rfl, rfl⟩
    · rintro ⟨t, ht, hc, hd⟩
      rwa [hc, hd]
  have hDisj : ∀ t1 ∈ G, ∀ t2 ∈ G, t1 ≠ t2 → Disjoint (fiber t1) (fiber t2) := by
    intro t1 _ t2 _ hne
    refine Finset.disjoint_left.mpr fun cd h1 h2 => hne ?_
    simp only [fiber, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
  rw [hEq, Finset.card_biUnion hDisj]
  have hFibCard (t : (Fin L.length → Bool) × (Fin L.length → Bool)) :
      (fiber t).card = 2 ^ (2 * (m - L.length)) := by
    simp only [fiber, Finset.card_product, card_evalDots_fiber hLI]
    rw [← Nat.pow_add, Nat.two_mul]
  calc
    (∑ t ∈ G, (fiber t).card) = ∑ _t ∈ G, 2 ^ (2 * (m - L.length)) :=
      Finset.sum_congr rfl fun t _ => hFibCard t
    _ = G.card * 2 ^ (2 * (m - L.length)) := by rw [Finset.sum_const, smul_eq_mul]

/-- Exact 10/16 determinant count over pairs of vectors independent mod 2. -/
theorem card_det_zero_pair {m : ℕ} (u1 u2 : BitString m)
    (hu1 : u1 ≠ zeroVec m) (hu2 : u2 ≠ zeroVec m) (hne : u1 ≠ u2) :
    8 * (Finset.univ.filter fun cd : BitString m × BitString m =>
      ((dot cd.1 u1 && dot cd.2 u2) ^^ (dot cd.1 u2 && dot cd.2 u1)) = false).card =
      5 * 2 ^ (2 * m) := by
  have hLI2 : LinIndep [u2] := by
    refine ⟨?_, trivial⟩
    intro hMem
    simp only [span, Finset.mem_singleton] at hMem
    exact hu2 hMem
  have hLI : LinIndep [u1, u2] := by
    refine ⟨?_, hLI2⟩
    intro hMem
    simp only [span, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hMem
    rcases hMem with hZ | ⟨z, hz, hEq⟩
    · exact hu1 hZ
    · subst hz
      rw [bitXor_zero_right] at hEq
      exact hne hEq.symm
  have hM2 : 2 ≤ m := linIndep_length_le hLI
  let P : (Fin 2 → Bool) → (Fin 2 → Bool) → Bool := fun tc td =>
    decide (((tc 0 && td 1) ^^ (tc 1 && td 0)) = false)
  have hFilterEq : (Finset.univ.filter fun cd : BitString m × BitString m =>
      ((dot cd.1 u1 && dot cd.2 u2) ^^ (dot cd.1 u2 && dot cd.2 u1)) = false) =
      Finset.univ.filter fun cd : BitString m × BitString m =>
        P (evalDots [u1, u2] cd.1) (evalDots [u1, u2] cd.2) = true := by
    ext cd
    simp [P, evalDots]
  rw [hFilterEq, card_filter_evalDots_pair [u1, u2] hLI P]
  let G := Finset.univ.filter fun t : (Fin 2 → Bool) × (Fin 2 → Bool) => P t.1 t.2 = true
  let Gbool := Finset.univ.filter fun q : Bool × Bool × Bool × Bool =>
    decide (((q.1 && q.2.2.2) ^^ (q.2.1 && q.2.2.1)) = false) = true
  have hGCard : G.card = 10 := by
    have hBij : G.card = Gbool.card := by
      refine Finset.card_bij (fun t _ => (t.1 0, t.1 1, t.2 0, t.2 1)) ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
      · intro t1 _ t2 _ hEq
        have hc0 : t1.1 0 = t2.1 0 := congrArg Prod.fst hEq
        have hc1 : t1.1 1 = t2.1 1 := congrArg (fun p => p.2.1) hEq
        have hd0 : t1.2 0 = t2.2 0 := congrArg (fun p => p.2.2.1) hEq
        have hd1 : t1.2 1 = t2.2 1 := congrArg (fun p => p.2.2.2) hEq
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> assumption
      · intro ⟨c0, c1, d0, d1⟩ hq
        refine ⟨(fun i => if i = 0 then c0 else c1, fun i => if i = 0 then d0 else d1),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩, rfl⟩
    rw [hBij]
    decide
  change 8 * (G.card * 2 ^ (2 * (m - 2))) = 5 * 2 ^ (2 * m)
  rw [hGCard]
  have hExp : 16 * 2 ^ (2 * (m - 2)) = 2 ^ (2 * m) := by
    calc
      16 * 2 ^ (2 * (m - 2)) = 2 ^ 4 * 2 ^ (2 * (m - 2)) := rfl
      _ = 2 ^ (4 + 2 * (m - 2)) := (Nat.pow_add 2 4 _).symm
      _ = 2 ^ (2 * m) := by congr 1; omega
  calc
    8 * (10 * 2 ^ (2 * (m - 2))) = 5 * (16 * 2 ^ (2 * (m - 2))) := by ring
    _ = 5 * 2 ^ (2 * m) := by rw [hExp]

/-- Rank-1 quadratic 2-plane vanishing bound on an entire `d`-dimensional basis `L`:
`(goodBasisPairs) * 2 ^ d ≤ 3 * 2 ^ (2 * m)`. -/
theorem card_det_zero_basis {m : ℕ} (L : List (BitString m)) (hLI : LinIndep L) :
    (Finset.univ.filter fun cd : BitString m × BitString m =>
      ∀ i j : Fin L.length,
        ((dot cd.1 (L.get i) && dot cd.2 (L.get j)) ^^
         (dot cd.1 (L.get j) && dot cd.2 (L.get i))) = false).card *
      2 ^ L.length ≤ 3 * 2 ^ (2 * m) := by
  let d := L.length
  have hd : d ≤ m := linIndep_length_le hLI
  let P : (Fin d → Bool) → (Fin d → Bool) → Bool := fun tc td =>
    decide (∀ i j : Fin d, ((tc i && td j) ^^ (tc j && td i)) = false)
  have hFilterEq : (Finset.univ.filter fun cd : BitString m × BitString m =>
      ∀ i j : Fin d,
        ((dot cd.1 (L.get i) && dot cd.2 (L.get j)) ^^
         (dot cd.1 (L.get j) && dot cd.2 (L.get i))) = false) =
      Finset.univ.filter fun cd : BitString m × BitString m =>
        P (evalDots L cd.1) (evalDots L cd.2) = true := by
    ext cd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P, evalDots]
    exact ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩
  rw [hFilterEq, card_filter_evalDots_pair L hLI P]
  let G := Finset.univ.filter fun t : (Fin d → Bool) × (Fin d → Bool) => P t.1 t.2 = true
  let G0 := G.filter fun t => t.1 = fun _ => false
  let G1 := G.filter fun t => t.1 ≠ fun _ => false
  have hG0 : G0.card ≤ 2 ^ d := by
    calc
      G0.card ≤ (Finset.univ : Finset (Fin d → Bool)).card := by
        refine Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) ?_
        intro t1 h1 t2 h2 hSnd
        have hF1 : t1.1 = fun _ => false := (Finset.mem_filter.mp h1).2
        have hF2 : t2.1 = fun _ => false := (Finset.mem_filter.mp h2).2
        exact Prod.ext (hF1.trans hF2.symm) hSnd
      _ = 2 ^ d := by simp [Fintype.card_bool, Fintype.card_fin]
  have hG1 : G1.card ≤ 2 * 2 ^ d := by
    have hMap : G1.card ≤ (Finset.univ : Finset ((Fin d → Bool) × Bool)).card := by
      refine Finset.card_le_card_of_injOn (fun t => (t.1, decide (t.2 = t.1)))
        (fun _ _ => Finset.mem_univ _) ?_
      intro t1 h1 t2 h2 hEq
      have hFst : t1.1 = t2.1 := congrArg (fun p : (Fin d → Bool) × Bool => p.1) hEq
      have hDec : decide (t1.2 = t1.1) = decide (t2.2 = t2.1) :=
        congrArg (fun p : (Fin d → Bool) × Bool => p.2) hEq
      have hProp (t : (Fin d → Bool) × (Fin d → Bool)) (ht : t ∈ G1) :
          t.2 = (fun _ => false) ∨ t.2 = t.1 := by
        have hMemG := (Finset.mem_filter.mp ht).1
        have hAll : ∀ i j : Fin d, ((t.1 i && t.2 j) ^^ (t.1 j && t.2 i)) = false := by
          simpa [P, decide_eq_true_eq] using (Finset.mem_filter.mp hMemG).2
        have hEx : ∃ i0 : Fin d, t.1 i0 = true := by
          by_contra hNo
          apply (Finset.mem_filter.mp ht).2
          funext i
          exact Bool.eq_false_of_not_eq_true fun hT => hNo ⟨i, hT⟩
        obtain ⟨i0, hi0⟩ := hEx
        have hRel (j : Fin d) : t.2 j = (t.1 j && t.2 i0) := by
          have hij := hAll i0 j
          rw [hi0, Bool.true_and] at hij
          revert hij
          cases t.2 j <;> cases (t.1 j && t.2 i0) <;> decide
        cases hi0' : t.2 i0
        · left; funext j; simp [hRel j, hi0']
        · right; funext j; simp [hRel j, hi0']
      rcases hProp t1 h1 with hZero1 | hSelf1 <;> rcases hProp t2 h2 with hZero2 | hSelf2
      · exact Prod.ext hFst (hZero1.trans hZero2.symm)
      · rw [decide_eq_true hSelf2] at hDec
        have hSelf1' := of_decide_eq_true hDec
        exact Prod.ext hFst (hSelf1'.trans (hFst.trans hSelf2.symm))
      · have hFalse : decide (t2.2 = t2.1) = true := by
          rw [← hDec]; exact decide_eq_true hSelf1
        exact Prod.ext hFst (hSelf1.trans (hFst.trans (of_decide_eq_true hFalse).symm))
      · exact Prod.ext hFst (hSelf1.trans (hFst.trans hSelf2.symm))
    simpa [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.mul_comm] using hMap
  have hGSub : G ⊆ G0 ∪ G1 := fun t ht => by
    by_cases h0 : t.1 = fun _ => false
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht, h0⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht, h0⟩)
  have hGCard : G.card ≤ 3 * 2 ^ d := by
    have := (Finset.card_le_card hGSub).trans (Finset.card_union_le G0 G1)
    omega
  change (G.card * 2 ^ (2 * (m - d))) * 2 ^ d ≤ 3 * 2 ^ (2 * m)
  have hPow : 2 ^ d * 2 ^ (2 * (m - d)) * 2 ^ d = 2 ^ (2 * m) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  calc
    (G.card * 2 ^ (2 * (m - d))) * 2 ^ d ≤ (3 * 2 ^ d * 2 ^ (2 * (m - d))) * 2 ^ d :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hGCard)
    _ = 3 * (2 ^ d * 2 ^ (2 * (m - d)) * 2 ^ d) := by ring
    _ = 3 * 2 ^ (2 * m) := by rw [hPow]

/-! ### Uniform 1/4 bound on constant rank-1 quadratic probes (`card_quad_const_mul_le`) -/

/-- All rank-1 quadratic probes `((a, b0), (c, d))` constant with value `target` on `U`. -/
noncomputable def constQuad {m : ℕ} (U : Finset (BitString m)) (target : Bool) :
    Finset ((BitString m × Bool) × (BitString m × BitString m)) :=
  Finset.univ.filter fun p => ∀ z ∈ U, quad p.1.1 p.1.2 p.2.1 p.2.2 z = target

/-- Pairs `(c, d)` that can be completed by some affine `(a, b0)` to equal `target` on `U`. -/
noncomputable def goodCD {m : ℕ} (U : Finset (BitString m)) (target : Bool) :
    Finset (BitString m × BitString m) :=
  Finset.univ.filter fun cd => ∃ ab : BitString m × Bool, ∀ z ∈ U, quad ab.1 ab.2 cd.1 cd.2 z = target

theorem card_constQuad_eq {m : ℕ} (U : Finset (BitString m)) (target : Bool) :
    (constQuad U target).card = (goodCD U target).card * (constAffines U false).card := by
  let fib (cd : BitString m × BitString m) :
      Finset ((BitString m × Bool) × (BitString m × BitString m)) :=
    (constQuad U target).filter fun p => p.2 = cd
  have hPart : constQuad U target = (goodCD U target).biUnion fib := by
    ext ⟨ab, cd⟩
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      constQuad, goodCD, fib]
    constructor
    · intro h
      exact ⟨cd, ⟨ab, h⟩, h, rfl⟩
    · rintro ⟨cd', _, h, rfl⟩
      exact h
  have hDisj : ∀ c1 ∈ goodCD U target, ∀ c2 ∈ goodCD U target, c1 ≠ c2 →
      Disjoint (fib c1) (fib c2) := by
    intro c1 _ c2 _ hne
    refine Finset.disjoint_left.mpr fun p h1 h2 => hne ?_
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    exact e1.symm.trans e2
  have hFibCard (cd : BitString m × BitString m) (hcd : cd ∈ goodCD U target) :
      (fib cd).card = (constAffines U false).card := by
    obtain ⟨⟨a0, b00⟩, hWitness⟩ := (Finset.mem_filter.mp hcd).2
    refine Finset.card_bij (fun p _ => (bitXor p.1.1 a0, p.1.2 ^^ b00)) ?_ ?_ ?_
    · intro ⟨⟨a, b0⟩, cd'⟩ hp
      have hpQ := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hEqCD : cd' = cd := (Finset.mem_filter.mp hp).2
      subst hEqCD
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩
      have h1 := hpQ z hz
      have h0 := hWitness z hz
      change quad a b0 cd'.1 cd'.2 z = target at h1
      change quad a0 b00 cd'.1 cd'.2 z = target at h0
      have hDiff : affine (bitXor a a0) (b0 ^^ b00) z =
          (quad a b0 cd'.1 cd'.2 z ^^ quad a0 b00 cd'.1 cd'.2 z) := by
        have hSub := quad_bitXor_affine a0 (bitXor a a0) b00 (b0 ^^ b00) cd'.1 cd'.2 z
        have hA : bitXor a0 (bitXor a a0) = a := by
          rw [bitXor_comm a0, bitXor_cancel_self_right]
        have hB : (b00 ^^ (b0 ^^ b00)) = b0 := by
          cases b0 <;> cases b00 <;> decide
        rw [hA, hB] at hSub
        cases q0 : quad a0 b00 cd'.1 cd'.2 z <;>
          cases q1 : quad a b0 cd'.1 cd'.2 z <;>
          cases af : affine (bitXor a a0) (b0 ^^ b00) z <;> simp_all
      dsimp only
      rw [hDiff, h1, h0, Bool.xor_self]
    · intro ⟨⟨a1, b1⟩, cd1⟩ h1 ⟨⟨a2, b2⟩, cd2⟩ h2 hEq
      have hcd1 : cd1 = cd := (Finset.mem_filter.mp h1).2
      have hcd2 : cd2 = cd := (Finset.mem_filter.mp h2).2
      subst hcd1; subst hcd2
      have hA : bitXor a1 a0 = bitXor a2 a0 := congrArg Prod.fst hEq
      have hB : (b1 ^^ b00) = (b2 ^^ b00) := congrArg Prod.snd hEq
      have hA' := bitXor_left_inj a0 hA
      have hB' : b1 = b2 := by
        revert hB; cases b1 <;> cases b2 <;> cases b00 <;> decide
      exact Prod.ext (Prod.ext hA' hB') rfl
    · intro ⟨a', b'⟩ ha'
      have hOn := (Finset.mem_filter.mp ha').2
      refine ⟨((bitXor a' a0, b' ^^ b00), cd), Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun z hz => ?_⟩, rfl⟩, ?_⟩
      · have hW := hWitness z hz
        have hAf := hOn z hz
        rw [bitXor_comm a' a0, Bool.xor_comm b' b00, quad_bitXor_affine]
        change quad a0 b00 cd.1 cd.2 z = target at hW
        change affine a' b' z = false at hAf
        rw [hW, hAf, Bool.xor_false]
      · have hB : ((b' ^^ b00) ^^ b00) = b' := by
          cases b' <;> cases b00 <;> decide
        exact Prod.ext (bitXor_cancel_self_right a' a0) hB
  rw [hPart, Finset.card_biUnion hDisj]
  calc
    (∑ cd ∈ goodCD U target, (fib cd).card)
        = ∑ _cd ∈ goodCD U target, (constAffines U false).card :=
      Finset.sum_congr rfl fun cd hcd => hFibCard cd hcd
    _ = (goodCD U target).card * (constAffines U false).card := by
      simp [Finset.sum_const, smul_eq_mul]

/-- Any subset of `span (v :: L')` strictly exceeding half plus 1 contains a non-degenerate
2-plane square `{y, y ⊕ u1, y ⊕ u2, y ⊕ u1 ⊕ u2}`. -/
theorem exists_square_in_dense_half {m : ℕ} {v : BitString m} {L' : List (BitString m)}
    {U' : Finset (BitString m)} (hLI : LinIndep (v :: L')) (hSub : U' ⊆ span (v :: L'))
    (hLarge : 2 ^ L'.length + 2 ≤ U'.card) :
    ∃ y ∈ U', ∃ u1 u2 : BitString m,
      u1 ≠ zeroVec m ∧ u2 ≠ zeroVec m ∧ u1 ≠ u2 ∧
      bitXor y u1 ∈ U' ∧ bitXor y u2 ∈ U' ∧ bitXor (bitXor y u1) u2 ∈ U' := by
  let L := v :: L'
  let Uv := U'.image (bitXor v)
  have hSubUv : Uv ⊆ span L := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact bitXor_mem_span L (mem_span_of_mem List.mem_cons_self) (hSub hu)
  have hUnionSub : U' ∪ Uv ⊆ span L := Finset.union_subset hSub hSubUv
  have hUnionCard : (U' ∪ Uv).card ≤ 2 ^ (L'.length + 1) := by
    have hSpanCard := card_span_of_linIndep hLI
    exact (Finset.card_le_card hUnionSub).trans (by simpa [L] using hSpanCard.le)
  have hInterCard : 4 ≤ (U' ∩ Uv).card := by
    have hIE := Finset.card_union_add_card_inter U' Uv
    have hUvCard : Uv.card = U'.card := Finset.card_image_of_injective _ (bitXor_right_inj v)
    have hPow : 2 ^ (L'.length + 1) = 2 * 2 ^ L'.length := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  let Pv := U'.filter fun y => bitXor y v ∈ U'
  have hInterSub : U' ∩ Uv ⊆ Pv := by
    intro y hy
    obtain ⟨hyU, hyUv⟩ := Finset.mem_inter.mp hy
    obtain ⟨z, hzU, hzEq⟩ := Finset.mem_image.mp hyUv
    have hFlip : bitXor y v = z := by
      rw [← hzEq, bitXor_comm v z, bitXor_cancel_self_right]
    exact Finset.mem_filter.mpr ⟨hyU, hFlip ▸ hzU⟩
  have hPvCard : 4 ≤ Pv.card := hInterCard.trans (Finset.card_le_card hInterSub)
  obtain ⟨y1, hy1⟩ := Finset.card_pos.mp (by omega : 0 < Pv.card)
  let R := Pv \ ({y1, bitXor y1 v} : Finset (BitString m))
  have hRCard : 2 ≤ R.card := by
    have hDiff := Finset.card_sdiff_add_card_inter Pv ({y1, bitXor y1 v} : Finset (BitString m))
    change R.card + (Pv ∩ ({y1, bitXor y1 v} : Finset (BitString m))).card = Pv.card at hDiff
    have hSmall : (Pv ∩ ({y1, bitXor y1 v} : Finset (BitString m))).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans ((Finset.card_insert_le _ _).trans (by simp))
    omega
  obtain ⟨y2, hy2⟩ := Finset.card_pos.mp (by omega : 0 < R.card)
  have hy2Pv : y2 ∈ Pv := (Finset.mem_sdiff.mp hy2).1
  have hy2Not : y2 ∉ ({y1, bitXor y1 v} : Finset (BitString m)) := (Finset.mem_sdiff.mp hy2).2
  have hy2Ne1 : y2 ≠ y1 := fun h => hy2Not (by simp [h])
  have hy2NeFlip : y2 ≠ bitXor y1 v := fun h => hy2Not (by simp [h])
  have hy1U : y1 ∈ U' := (Finset.mem_filter.mp hy1).1
  have hy1vU : bitXor y1 v ∈ U' := (Finset.mem_filter.mp hy1).2
  have hy2U : y2 ∈ U' := (Finset.mem_filter.mp hy2Pv).1
  have hy2vU : bitXor y2 v ∈ U' := (Finset.mem_filter.mp hy2Pv).2
  refine ⟨y1, hy1U, v, bitXor y1 y2, ?_, ?_, ?_, hy1vU, ?_, ?_⟩
  · intro hvZ
    apply hLI.1
    rw [hvZ]
    exact zero_mem_span L'
  · intro hZ
    apply hy2Ne1
    have := congrArg (bitXor y1) hZ
    simpa only [bitXor_cancel_self_left, bitXor_zero_right] using this
  · intro hEq
    apply hy2NeFlip
    rw [hEq, bitXor_cancel_self_left]
  · simpa only [bitXor_cancel_self_left] using hy2U
  · have hSq : bitXor (bitXor y1 v) (bitXor y1 y2) = bitXor y2 v := by
      funext i; dsimp only [bitXor]; cases y1 i <;> cases v i <;> cases y2 i <;> rfl
    rw [hSq]
    exact hy2vU

/-- Any subset exceeding `3/4` of `span L` contains a 2-plane square in every pair of directions. -/
theorem exists_square_for_every_pair {m : ℕ} {L : List (BitString m)} {U' : Finset (BitString m)}
    (hLI : LinIndep L) (hSub : U' ⊆ span L) (hDense : 3 * 2 ^ L.length < 4 * U'.card)
    {u1 u2 : BitString m} (hu1 : u1 ∈ span L) (hu2 : u2 ∈ span L) :
    ∃ y ∈ span L, y ∈ U' ∧ bitXor y u1 ∈ U' ∧ bitXor y u2 ∈ U' ∧
      bitXor (bitXor y u1) u2 ∈ U' := by
  let bad := span L \ U'
  have hBad : 4 * bad.card < 2 ^ L.length := by
    have hSplit := Finset.card_sdiff_add_card_eq_card hSub
    rw [card_span_of_linIndep hLI] at hSplit
    change bad.card + U'.card = 2 ^ L.length at hSplit
    omega
  let covered := bad ∪ bad.image (fun z => bitXor z u1) ∪
    bad.image (fun z => bitXor z u2) ∪ bad.image (fun z => bitXor z (bitXor u1 u2))
  have hCovCard : covered.card ≤ 4 * bad.card := by
    have h1 : covered.card ≤ (bad ∪ bad.image (fun z => bitXor z u1) ∪
        bad.image (fun z => bitXor z u2)).card +
        (bad.image (fun z => bitXor z (bitXor u1 u2))).card :=
      Finset.card_union_le _ _
    have h2 := Finset.card_union_le (bad ∪ bad.image (fun z => bitXor z u1))
      (bad.image (fun z => bitXor z u2))
    have h3 := Finset.card_union_le bad (bad.image (fun z => bitXor z u1))
    have hi1 : (bad.image (fun z => bitXor z u1)).card ≤ bad.card := Finset.card_image_le
    have hi2 : (bad.image (fun z => bitXor z u2)).card ≤ bad.card := Finset.card_image_le
    have hi3 : (bad.image (fun z => bitXor z (bitXor u1 u2))).card ≤ bad.card := Finset.card_image_le
    omega
  have hNotSub : ¬ (span L ⊆ covered) := by
    intro hC
    have := (Finset.card_le_card hC).trans hCovCard
    rw [card_span_of_linIndep hLI] at this
    omega
  rw [Finset.not_subset] at hNotSub
  obtain ⟨y, hySpan, hyNotCov⟩ := hNotSub
  have hyNotBad : y ∉ bad := fun h =>
    hyNotCov (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hyU : y ∈ U' := by
    by_contra hNo
    exact hyNotBad (Finset.mem_sdiff.mpr ⟨hySpan, hNo⟩)
  have hyu1Span : bitXor y u1 ∈ span L := bitXor_mem_span L hySpan hu1
  have hyu2Span : bitXor y u2 ∈ span L := bitXor_mem_span L hySpan hu2
  have hyu12Span : bitXor (bitXor y u1) u2 ∈ span L := bitXor_mem_span L hyu1Span hu2
  have hyu1U : bitXor y u1 ∈ U' := by
    by_contra hNo
    apply hyNotCov
    refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
    exact Finset.mem_image.mpr ⟨bitXor y u1, Finset.mem_sdiff.mpr ⟨hyu1Span, hNo⟩,
      bitXor_cancel_self_right y u1⟩
  have hyu2U : bitXor y u2 ∈ U' := by
    by_contra hNo
    apply hyNotCov
    refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    exact Finset.mem_image.mpr ⟨bitXor y u2, Finset.mem_sdiff.mpr ⟨hyu2Span, hNo⟩,
      bitXor_cancel_self_right y u2⟩
  have hyu12U : bitXor (bitXor y u1) u2 ∈ U' := by
    by_contra hNo
    apply hyNotCov
    refine Finset.mem_union_right _ ?_
    refine Finset.mem_image.mpr ⟨bitXor (bitXor y u1) u2,
      Finset.mem_sdiff.mpr ⟨hyu12Span, hNo⟩, ?_⟩
    funext i; dsimp only [bitXor]; cases y i <;> cases u1 i <;> cases u2 i <;> rfl
  exact ⟨y, hySpan, hyU, hyu1U, hyu2U, hyu12U⟩

/-- **Uniform `1/4` bound on constant rank-1 quadratic probes**: for every `U ⊆ {0,1}^m`
and `target : Bool`, `4 * (|U| - 1) * |constQuad U target| ≤ 2 ^ (3 * m + 1)`. -/
theorem card_quad_const_mul_le {m : ℕ} (U : Finset (BitString m)) (target : Bool) :
    4 * (U.card - 1) * (constQuad U target).card ≤ 2 ^ (3 * m + 1) := by
  by_cases hTriv : U.card ≤ 1
  · have hZ : U.card - 1 = 0 := by omega
    simp [hZ]
  · have hGe2 : 2 ≤ U.card := by omega
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
    obtain ⟨L, hLI, hMem, hCov⟩ := exists_affine_basis U x0
    let d := L.length
    have hd : d ≤ m := linIndep_length_le hLI
    let U' := U.image (bitXor x0)
    have hU'Card : U'.card = U.card := Finset.card_image_of_injective _ (bitXor_right_inj x0)
    have hU'Sub : U' ⊆ span L := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      exact hCov x hx
    have hULeSpan : U.card ≤ 2 ^ d := by
      have hC := (Finset.card_le_card hU'Sub).trans (card_span_of_linIndep hLI).le
      change U'.card ≤ 2 ^ d at hC
      omega
    have hDPos : 1 ≤ d := by
      by_contra hD0
      have hd0 : d = 0 := by omega
      rw [hd0, pow_zero] at hULeSpan
      omega
    have hConstEq := card_constQuad_eq U target
    rw [card_constAffines_false U x0 hx0 L hLI hMem hCov] at hConstEq
    have hGoodTarget : 2 * (U.card - 1) * (goodCD U target).card ≤ 2 ^ d * 2 ^ (2 * m) := by
      by_cases hCase1 : U.card ≤ 2 ^ (d - 1) + 1
      · have hUniv : (goodCD U target).card ≤ 2 ^ (2 * m) := by
          have hSub : (goodCD U target).card ≤
              (Finset.univ : Finset (BitString m × BitString m)).card := Finset.card_le_univ _
          simpa [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
            ← Nat.pow_add, Nat.two_mul] using hSub
        have hSub1 : U.card - 1 ≤ 2 ^ (d - 1) := by omega
        calc
          2 * (U.card - 1) * (goodCD U target).card
              ≤ 2 * 2 ^ (d - 1) * 2 ^ (2 * m) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hSub1) hUniv
          _ = 2 ^ d * 2 ^ (2 * m) := by
            congr 1
            rw [Nat.mul_comm 2 _, ← Nat.pow_succ]
            congr 1
            omega
      · have hDGe2 : 2 ≤ d := by
          by_contra hDLt
          have hd1 : d = 1 := by omega
          rw [hd1] at hULeSpan hCase1
          omega
        by_cases hCase2 : 4 * (U.card - 1) ≤ 3 * 2 ^ d
        · cases L with
          | nil => simp [d] at hDPos
          | cons v L' =>
            have hLarge : 2 ^ L'.length + 2 ≤ U'.card := by
              dsimp only [d] at hCase1
              simp only [List.length_cons, Nat.add_sub_cancel] at hCase1
              rw [hU'Card]
              omega
            obtain ⟨y', hy', u1, u2, hu1, hu2, hne, hy'1, hy'2, hy'12⟩ :=
              exists_square_in_dense_half hLI hU'Sub hLarge
            have hPull (z : BitString m) (hz : z ∈ U') : bitXor x0 z ∈ U := by
              obtain ⟨w, hw, hwEq⟩ := Finset.mem_image.mp hz
              rwa [← hwEq, bitXor_cancel_self_left]
            let y0 := bitXor x0 y'
            have hy0 : y0 ∈ U := hPull y' hy'
            have hy1 : bitXor y0 u1 ∈ U := by
              simpa only [y0, bitXor_assoc] using hPull (bitXor y' u1) hy'1
            have hy2 : bitXor y0 u2 ∈ U := by
              simpa only [y0, bitXor_assoc] using hPull (bitXor y' u2) hy'2
            have hy12 : bitXor (bitXor y0 u1) u2 ∈ U := by
              simpa only [y0, bitXor_assoc] using hPull (bitXor (bitXor y' u1) u2) hy'12
            let Spair := Finset.univ.filter fun cd : BitString m × BitString m =>
              ((dot cd.1 u1 && dot cd.2 u2) ^^ (dot cd.1 u2 && dot cd.2 u1)) = false
            have hSubPair : goodCD U target ⊆ Spair := by
              intro cd hcd
              obtain ⟨ab, hab⟩ := (Finset.mem_filter.mp hcd).2
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                det_zero_of_quad_const_on_square
                  (hab y0 hy0) (hab (bitXor y0 u1) hy1)
                  (hab (bitXor y0 u2) hy2) (hab (bitXor (bitXor y0 u1) u2) hy12)⟩
            have h8Good : 8 * (goodCD U target).card ≤ 5 * 2 ^ (2 * m) := by
              have hCardLe := Finset.card_le_card hSubPair
              have hPairEq := card_det_zero_pair u1 u2 hu1 hu2 hne
              change 8 * Spair.card = 5 * 2 ^ (2 * m) at hPairEq
              omega
            have h16 : 16 * (2 * (U.card - 1) * (goodCD U target).card) ≤
                16 * (2 ^ d * 2 ^ (2 * m)) := by
              calc
                16 * (2 * (U.card - 1) * (goodCD U target).card)
                    = (4 * (U.card - 1)) * (8 * (goodCD U target).card) := by ring
                _ ≤ (3 * 2 ^ d) * (5 * 2 ^ (2 * m)) := Nat.mul_le_mul hCase2 h8Good
                _ = 15 * (2 ^ d * 2 ^ (2 * m)) := by ring
                _ ≤ 16 * (2 ^ d * 2 ^ (2 * m)) := by omega
            omega
        · have hCase3 : 3 * 2 ^ d < 4 * (U.card - 1) := by omega
          have hDGe3 : 3 ≤ d := by
            by_contra hDLt
            have hd2 : d = 2 := by omega
            rw [hd2] at hULeSpan hCase3
            omega
          have hDense : 3 * 2 ^ L.length < 4 * U'.card := by
            change 3 * 2 ^ d < 4 * U'.card
            omega
          let Sbasis := Finset.univ.filter fun cd : BitString m × BitString m =>
            ∀ i j : Fin L.length,
              ((dot cd.1 (L.get i) && dot cd.2 (L.get j)) ^^
               (dot cd.1 (L.get j) && dot cd.2 (L.get i))) = false
          have hSubBasis : goodCD U target ⊆ Sbasis := by
            intro cd hcd
            obtain ⟨ab, hab⟩ := (Finset.mem_filter.mp hcd).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i j => ?_⟩
            obtain ⟨y', _, hy', hy'1, hy'2, hy'12⟩ := exists_square_for_every_pair hLI hU'Sub
              hDense (mem_span_of_mem (List.get_mem L i)) (mem_span_of_mem (List.get_mem L j))
            have hPull (z : BitString m) (hz : z ∈ U') : bitXor x0 z ∈ U := by
              obtain ⟨w, hw, hwEq⟩ := Finset.mem_image.mp hz
              rwa [← hwEq, bitXor_cancel_self_left]
            let y0 := bitXor x0 y'
            have hy0 : y0 ∈ U := hPull y' hy'
            have hy1 : bitXor y0 (L.get i) ∈ U := by
              simpa only [y0, bitXor_assoc] using hPull (bitXor y' (L.get i)) hy'1
            have hy2 : bitXor y0 (L.get j) ∈ U := by
              simpa only [y0, bitXor_assoc] using hPull (bitXor y' (L.get j)) hy'2
            have hy12 : bitXor (bitXor y0 (L.get i)) (L.get j) ∈ U := by
              simpa only [y0, bitXor_assoc] using
                hPull (bitXor (bitXor y' (L.get i)) (L.get j)) hy'12
            exact det_zero_of_quad_const_on_square
              (hab y0 hy0) (hab (bitXor y0 (L.get i)) hy1)
              (hab (bitXor y0 (L.get j)) hy2) (hab (bitXor (bitXor y0 (L.get i)) (L.get j)) hy12)
          have hBasisLe : (goodCD U target).card * 2 ^ d ≤ 3 * 2 ^ (2 * m) :=
            (Nat.mul_le_mul_right _ (Finset.card_le_card hSubBasis)).trans
              (card_det_zero_basis L hLI)
          have hPow8 : 8 ≤ 2 ^ d := by
            calc
              8 = 2 ^ 3 := by decide
              _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hDGe3
          have hMulPow : (2 * (U.card - 1) * (goodCD U target).card) * 2 ^ d ≤
              (2 ^ d * 2 ^ (2 * m)) * 2 ^ d := by
            calc
              (2 * (U.card - 1) * (goodCD U target).card) * 2 ^ d
                  = 2 * (U.card - 1) * ((goodCD U target).card * 2 ^ d) := by ring
              _ ≤ 2 * 2 ^ d * (3 * 2 ^ (2 * m)) :=
                Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) hBasisLe
              _ = 6 * (2 ^ d * 2 ^ (2 * m)) := by ring
              _ ≤ 2 ^ d * (2 ^ d * 2 ^ (2 * m)) := Nat.mul_le_mul_right _ (by omega)
              _ = (2 ^ d * 2 ^ (2 * m)) * 2 ^ d := by ring
          exact Nat.le_of_mul_le_mul_right hMulPow (by positivity)
    have hScale := Nat.mul_le_mul_right (2 * 2 ^ (m - d)) hGoodTarget
    have hPowComb : (2 ^ d * 2 ^ (2 * m)) * (2 * 2 ^ (m - d)) = 2 ^ (3 * m + 1) := by
      have hMD : 2 ^ d * 2 ^ (m - d) = 2 ^ m := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hd]
      calc
        (2 ^ d * 2 ^ (2 * m)) * (2 * 2 ^ (m - d))
            = 2 * (2 ^ d * 2 ^ (m - d)) * 2 ^ (2 * m) := by ring
        _ = 2 * 2 ^ m * 2 ^ (2 * m) := by rw [hMD]
        _ = 2 * (2 ^ m * 2 ^ (2 * m)) := by ring
        _ = 2 ^ (3 * m + 1) := by
          rw [← Nat.pow_add, Nat.mul_comm 2 _, ← Nat.pow_succ]
          congr 1; omega
    calc
      4 * (U.card - 1) * (constQuad U target).card
          = (2 * (U.card - 1) * (goodCD U target).card) * (2 * 2 ^ (m - d)) := by
        rw [hConstEq]; ring
      _ ≤ (2 ^ d * 2 ^ (2 * m)) * (2 * 2 ^ (m - d)) := hScale
      _ = 2 ^ (3 * m + 1) := hPowComb

/-! ### Quadratic forest averaging and improved `mcspSquare 32` lower bounds -/

/-- Clean disjunction roots with at least one raw leaf. -/
noncomputable def groundedOrRoots {n g : ℕ} (p : Program signature n g) (root : Wire n g) :=
  (ORRoot p root).filter fun r => (orInputs p root r).Nonempty

/-- Clean conjunction roots with at least one raw leaf. -/
noncomputable def groundedAndRoots {n g : ℕ} (p : Program signature n g) (root : Wire n g) :=
  (ANDRoot p root).filter fun r => (andInputs p root r).Nonempty

/-- A quadratic probe mask pays only for forest roots with raw leaves. -/
theorem exists_reindexed_quad_forest_mask_grounded {n m : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hQuad : ∀ (a : BitString m) (b0 : Bool) (qc qd : BitString m),
      f (fun i => quad a b0 qc qd (e i)) = true) :
    ∃ (x : BitString n) (P : Finset (Fin n)),
      4 * P.card ≤ 5 * ((groundedOrRoots c.program (c.outputs 0)).card +
        (groundedAndRoots c.program (c.outputs 0)).card) ∧
      IsForestMask c.program (c.outputs 0) x P ∧ f x = true := by
  have hfCorner (b : Bool) : f (fun _ => b) = true := by
    have hEq : (fun i : Fin n => quad (zeroVec m) b (zeroVec m) (zeroVec m) (e i)) =
        fun _ => b := by
      funext i
      simp only [quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    simpa only [hEq] using hQuad (zeroVec m) b (zeroVec m) (zeroVec m)
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc _) 0).trans (hfCorner false)
  have h1 : cornerValue p true root = true := (congrFun (hc _) 0).trans (hfCorner true)
  let T_OR := groundedOrRoots p root
  let T_AND := groundedAndRoots p root
  let I_OR (r : Fin c.size) : Finset (Fin n) := orInputs p root r
  let I_AND (r' : Fin c.size) : Finset (Fin n) := andInputs p root r'
  let U_OR (r : Fin c.size) : Finset (BitString m) := (I_OR r).image e
  let U_AND (r' : Fin c.size) : Finset (BitString m) := (I_AND r').image e
  have hCardUOR (r : Fin c.size) : (U_OR r).card = (I_OR r).card :=
    Finset.card_image_of_injective _ e.injective
  have hCardUAND (r' : Fin c.size) : (U_AND r').card = (I_AND r').card :=
    Finset.card_image_of_injective _ e.injective
  let failOR (q : (BitString m × Bool) × (BitString m × BitString m)) : ℕ :=
    ∑ r ∈ T_OR, if q ∈ constQuad (U_OR r) false then (I_OR r).card - 1 else 0
  let failAND (q : (BitString m × Bool) × (BitString m × BitString m)) : ℕ :=
    ∑ r ∈ T_AND, if q ∈ constQuad (U_AND r) true then (I_AND r).card - 1 else 0
  have hQuadSum (U : Finset (BitString m)) (target : Bool) :
      (∑ q : (BitString m × Bool) × (BitString m × BitString m),
        4 * (if q ∈ constQuad U target then U.card - 1 else 0)) ≤ 2 ^ (3 * m + 1) := by
    rw [← Finset.mul_sum, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, smul_eq_mul]
    calc
      4 * ((constQuad U target).card * (U.card - 1))
          = 4 * (U.card - 1) * (constQuad U target).card := by ring
      _ ≤ 2 ^ (3 * m + 1) := card_quad_const_mul_le U target
  have hSumOR :
      (∑ q : (BitString m × Bool) × (BitString m × BitString m), 4 * failOR q) ≤
        T_OR.card * 2 ^ (3 * m + 1) := by
    dsimp only [failOR]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r ∈ T_OR, 2 ^ (3 * m + 1) := by
        refine Finset.sum_le_sum fun r _ => ?_
        simpa only [hCardUOR] using hQuadSum (U_OR r) false
      _ = T_OR.card * 2 ^ (3 * m + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hSumAND :
      (∑ q : (BitString m × Bool) × (BitString m × BitString m), 4 * failAND q) ≤
        T_AND.card * 2 ^ (3 * m + 1) := by
    dsimp only [failAND]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r' ∈ T_AND, 2 ^ (3 * m + 1) := by
        refine Finset.sum_le_sum fun r' _ => ?_
        simpa only [hCardUAND] using hQuadSum (U_AND r') true
      _ = T_AND.card * 2 ^ (3 * m + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hUnivCard :
      (Finset.univ : Finset ((BitString m × Bool) × (BitString m × BitString m))).card =
        2 ^ (3 * m + 1) := by
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    have hR : (2 ^ m * 2) * (2 ^ m * 2 ^ m) = 2 * (2 ^ m * 2 ^ m * 2 ^ m) := by ring
    rw [hR, ← Nat.pow_add, ← Nat.pow_add, Nat.mul_comm 2 _, ← Nat.pow_succ]
    congr 1
    omega
  have hExQ : ∃ q : (BitString m × Bool) × (BitString m × BitString m),
      4 * (failOR q + failAND q) ≤ T_OR.card + T_AND.card := by
    by_contra hNot
    simp only [not_exists, not_le] at hNot
    have hLower : 2 ^ (3 * m + 1) * (T_OR.card + T_AND.card + 1) ≤
        ∑ q : (BitString m × Bool) × (BitString m × BitString m), 4 * (failOR q + failAND q) := by
      calc
        _ = ∑ _q : (BitString m × Bool) × (BitString m × BitString m),
              (T_OR.card + T_AND.card + 1) := by rw [Finset.sum_const, smul_eq_mul, hUnivCard]
        _ ≤ _ := Finset.sum_le_sum fun q _ => hNot q
    rw [show (∑ q : (BitString m × Bool) × (BitString m × BitString m),
          4 * (failOR q + failAND q)) =
        (∑ q, 4 * failOR q) + (∑ q, 4 * failAND q) by
      simp only [Nat.mul_add, Finset.sum_add_distrib]] at hLower
    have hUpper : (∑ q, 4 * failOR q) + (∑ q, 4 * failAND q) ≤
        (T_OR.card + T_AND.card) * 2 ^ (3 * m + 1) := by
      have := add_le_add hSumOR hSumAND
      simpa only [← Nat.add_mul] using this
    have hGap := hLower.trans hUpper
    rw [Nat.mul_comm (2 ^ (3 * m + 1))] at hGap
    have hPos : 0 < 2 ^ (3 * m + 1) := by positivity
    have hContr := (Nat.mul_le_mul_right_iff hPos).mp hGap
    omega
  obtain ⟨q, hqLe⟩ := hExQ
  let x : BitString n := fun i => quad q.1.1 q.1.2 q.2.1 q.2.2 (e i)
  let maskOR (r : Fin c.size) : Finset (Fin n) :=
    if h : ∃ w ∈ I_OR r, x w = true then {Classical.choose h} else I_OR r
  let maskAND (r' : Fin c.size) : Finset (Fin n) :=
    if h : ∃ u ∈ I_AND r', x u = false then {Classical.choose h} else I_AND r'
  have hMaskORCard (r : Fin c.size) :
      (maskOR r).card ≤ 1 + (if q ∈ constQuad (U_OR r) false then (I_OR r).card - 1 else 0) := by
    by_cases h1 : ∃ w ∈ I_OR r, x w = true <;>
      by_cases h2 : q ∈ constQuad (U_OR r) false
    · simp [maskOR, h1, h2]
    · simp [maskOR, h1, h2]
    · simp [maskOR, h1, h2]; omega
    · exfalso
      apply h2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      by_contra hNeF
      have hXT : x i = true := Bool.eq_true_of_not_eq_false hNeF
      exact h1 ⟨i, hi, hXT⟩
  have hMaskANDCard (r' : Fin c.size) :
      (maskAND r').card ≤ 1 + (if q ∈ constQuad (U_AND r') true then (I_AND r').card - 1 else 0) := by
    by_cases h1 : ∃ u ∈ I_AND r', x u = false <;>
      by_cases h2 : q ∈ constQuad (U_AND r') true
    · simp [maskAND, h1, h2]
    · simp [maskAND, h1, h2]
    · simp [maskAND, h1, h2]; omega
    · exfalso
      apply h2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hz => ?_⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      by_contra hNeT
      have hXF : x i = false := Bool.eq_false_iff.mpr hNeT
      exact h1 ⟨i, hi, hXF⟩
  let Mask : Finset (Fin n) := T_OR.biUnion maskOR ∪ T_AND.biUnion maskAND
  have hMaskCard : Mask.card ≤ T_OR.card + failOR q + T_AND.card + failAND q := by
    have hU := Finset.card_union_le (T_OR.biUnion maskOR) (T_AND.biUnion maskAND)
    have hB1 : (T_OR.biUnion maskOR).card ≤ T_OR.card + failOR q := by
      calc
        (T_OR.biUnion maskOR).card ≤ ∑ r ∈ T_OR, (maskOR r).card := Finset.card_biUnion_le
        _ ≤ ∑ r ∈ T_OR, (1 + (if q ∈ constQuad (U_OR r) false then (I_OR r).card - 1 else 0)) :=
          Finset.sum_le_sum fun r _ => hMaskORCard r
        _ = T_OR.card + failOR q := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    have hB2 : (T_AND.biUnion maskAND).card ≤ T_AND.card + failAND q := by
      calc
        (T_AND.biUnion maskAND).card ≤ ∑ r' ∈ T_AND, (maskAND r').card := Finset.card_biUnion_le
        _ ≤ ∑ r' ∈ T_AND, (1 + (if q ∈ constQuad (U_AND r') true then (I_AND r').card - 1 else 0)) :=
          Finset.sum_le_sum fun r' _ => hMaskANDCard r'
        _ = T_AND.card + failAND q := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    dsimp only [Mask]
    omega
  refine ⟨x, Mask, ?_, ⟨?_, ?_⟩, hQuad q.1.1 q.1.2 q.2.1 q.2.2⟩
  · dsimp only [T_OR, T_AND, p, root] at hMaskCard hqLe
    omega
  · intro r hr
    by_cases hEx : ∃ w ∈ I_OR r, x w = true
    · left
      let w := Classical.choose hEx
      have hw := Classical.choose_spec hEx
      refine ⟨w, hw.1, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ⟨w, hw.1⟩⟩, ?_⟩), hw.2⟩
      simp [maskOR, hEx, w]
    · right
      intro i hi
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ⟨i, hi⟩⟩, by
        simpa [maskOR, hEx] using hi⟩)
  · intro r hr
    by_cases hEx : ∃ u ∈ I_AND r, x u = false
    · left
      let u := Classical.choose hEx
      have hu := Classical.choose_spec hEx
      refine ⟨u, hu.1, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ⟨u, hu.1⟩⟩, ?_⟩), hu.2⟩
      simp [maskAND, hEx, u]
    · right
      intro i hi
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, ⟨i, hi⟩⟩, by
        simpa [maskAND, hEx] using hi⟩)

/-- The quadratic mask bound with the full root count. -/
theorem exists_reindexed_quad_forest_mask_witness {n m : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m)
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hQuad : ∀ (a : BitString m) (b0 : Bool) (qc qd : BitString m),
      f (fun i => quad a b0 qc qd (e i)) = true) :
    ∃ (x : BitString n) (P : Finset (Fin n)),
      4 * P.card ≤ 5 * ((ORRoot c.program (c.outputs 0)).card +
        (ANDRoot c.program (c.outputs 0)).card) ∧
      IsForestMask c.program (c.outputs 0) x P ∧ f x = true := by
  obtain ⟨x, P, hP, hMask, hx⟩ := exists_reindexed_quad_forest_mask_grounded e c hc hQuad
  have hOR : (groundedOrRoots c.program (c.outputs 0)).card ≤ (ORRoot c.program (c.outputs 0)).card :=
    Finset.card_filter_le _ _
  have hAND : (groundedAndRoots c.program (c.outputs 0)).card ≤ (ANDRoot c.program (c.outputs 0)).card :=
    Finset.card_filter_le _ _
  exact ⟨x, P, by omega, hMask, hx⟩

/-- Reindexed quadratic-probe forest lower bound with zero linear penalty:
`280 * (2 * n) + 2 * n ≤ 280 * (complexity f + 2 * B + 1) + 17 * B`. -/
theorem quad_reindexed_forest_size {n m B : ℕ} {f : BooleanFunction n}
    (e : Fin n ↪ BitString m) (hSparse : (acceptingTables f).card ≤ 2 ^ B)
    (hQuad : ∀ (a : BitString m) (b0 : Bool) (qc qd : BitString m),
      f (fun i => quad a b0 qc qd (e i)) = true) :
    280 * (2 * n) + 2 * n ≤
      280 * (complexity interpretation (single f) + 2 * B + 1) + 17 * B := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  have hfCorner (b : Bool) : f (fun _ => b) = true := by
    have hEq : (fun i : Fin n => quad (zeroVec m) b (zeroVec m) (zeroVec m) (e i)) =
        fun _ => b := by
      funext i
      simp only [quad, affine, dot_zero_left, Bool.and_false, Bool.xor_false]
    simpa only [hEq] using hQuad (zeroVec m) b (zeroVec m) (zeroVec m)
  let p := c.program
  let root := c.outputs 0
  have h0 : cornerValue p false root = true := (congrFun (hc _) 0).trans (hfCorner false)
  have h1 : cornerValue p true root = true := (congrFun (hc _) 0).trans (hfCorner true)
  obtain ⟨x, P, hP, hMask, hx⟩ := exists_reindexed_quad_forest_mask_witness e c hc hQuad
  have hAccept (y : BitString n) (hy : ∀ i ∈ P ∪ stopInputs p root, y i = x i) : f y = true := by
    have he := hMask.trace_eq h0 h1 (fun _ _ => rfl)
      (fun i hi => hy i (Finset.mem_union_left _ hi))
      (fun _ hk => Or.inl fun a i ha => hy i (Finset.mem_union_right _ (stopInput_mem_of_wire hk a ha)))
    exact (congrFun (hc y) 0).symm.trans (he.trans ((congrFun (hc x) 0).trans hx))
  have hMasked := card_masked_le hSparse x _ hAccept
  have hUnion := Finset.card_union_le P (stopInputs p root)
  have hBudget := card_stopInputs_and_roots_le_tight c hc hSparse (hfCorner false) (hfCorner true)
  have hN0 := card_needInputs_ge_of_sparse c hc hSparse false (hfCorner false)
  have hN1 := card_needInputs_ge_of_sparse c hc hSparse true (hfCorner true)
  have hAcct := needInputs_add_slack_eq p root h0 h1
  dsimp only [p, root] at hMasked hUnion hAcct
  omega

/-- General unconditional De Morgan circuit lower bound for `mcspSquare m` (`13 ≤ m`). -/
theorem mcspSquare_quad_super_twoN (m : ℕ) (hm : 13 ≤ m) :
    280 * (2 * 2 ^ m) + 2 * 2 ^ m ≤
      280 * (complexity interpretation (single (mcspSquare m)) +
        2 * descriptionBitBound m + 1) + 17 * descriptionBitBound m :=
  quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding
    (card_accepting_mcspSquare_le m) (fun a b qc qd => by
      change mcspSquare m (MCSP.truthTable m (quad a b qc qd)) = true
      exact mcspSquare_accepts_quad m hm a b qc qd)

/-- Concrete pure quadratic-forest lower bound at `m = 32` (`N = 2 ^ 32`):
`8,620,555,905 ≤ complexity (mcspSquare 32)`. -/
theorem mcspSquare_32_quad_forest :
    8620555905 ≤ complexity interpretation (single (mcspSquare 32)) := by
  have h := mcspSquare_quad_super_twoN 32 (by decide)
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 280 * (2 * 4294967296) + 2 * 4294967296 ≤
    280 * (complexity interpretation (single (mcspSquare 32)) + 2 * 27672 + 1) + 17 * 27672 at h
  omega

/-- Combined quadratic-forest + 17-pin minority-residual lower bound at `m = 32`:
`8,620,555,922 ≤ complexity (mcspSquare 32)` (+28,287,454 over `8,592,268,468`). -/
theorem mcspSquare_32_quad_minority :
    8620555922 ≤ complexity interpretation (single (mcspSquare 32)) := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare 32))
  obtain ⟨x, P, hP, hSparse, hLoss⟩ := minority_pinning_run 32 c hc (by decide) 17 (by decide)
  let f : BooleanFunction (2 ^ 32) := fun y => mcspSquare 32 (substitute (pinAt x P) y)
  have hQ (a : BitString 32) (b0 : Bool) (qc qd : BitString 32) :
      f (fun i => quad a b0 qc qd ((BitString.equivFin 32).symm i)) = true := by
    change f (MCSP.truthTable 32 (quad a b0 qc qd)) = true
    exact patched_quad_accepted 32 x P a b0 qc qd (by rw [hP]; omega)
  have h := quad_reindexed_forest_size (BitString.equivFin 32).symm.toEmbedding hSparse hQ
  rw [show descriptionBitBound 32 = 27672 by decide] at h
  change 280 * (2 * 4294967296) + 2 * 4294967296 ≤
    280 * (complexity interpretation (single f) + 2 * 27672 + 1) + 17 * 27672 at h
  have hR : 8620555905 ≤ complexity interpretation (single f) := by omega
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

#print axioms complexity_quad_le
#print axioms mcspSquare_accepts_quad
#print axioms patched_quad_accepted
#print axioms card_quad_const_mul_le
#print axioms exists_reindexed_quad_forest_mask_witness
#print axioms quad_reindexed_forest_size
#print axioms mcspSquare_quad_super_twoN
#print axioms mcspSquare_32_quad_forest
#print axioms mcspSquare_32_quad_minority

end PvsNP.Frontier.QuadraticForest
