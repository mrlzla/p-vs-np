module

public import MCSPLongAndOrbit
public import MCSPFaceDecoder

/-! A signed conjunction with logarithmically many free variables has growing
support. Recover its entire face from shared, noise-tolerant coordinate counts. -/

@[expose] public section

namespace PvsNP.Frontier.GrowingAndOrbit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open JointEquality JointOrbit PatchedCut DegreeSampler PolynomialBarrier
open QuadraticForest LongAndOrbit FaceDecoder
open scoped Classical

variable {m k f : ℕ}

private theorem tally_le_add_noise {H R : BooleanFunction m} (D : Finset (BitString m))
    (hEq : ∀ z, z ∉ D → H z = R z) (q : Slot m) :
    tally H q ≤ tally R q + D.card := by
  rw [tally_eq_card, tally_eq_card]
  let h := Finset.univ.filter (fun z => H z = true ∧ selects q z = true)
  let g := Finset.univ.filter (fun z => R z = true ∧ selects q z = true)
  have hS : h ⊆ g ∪ D := by
    intro z hz
    by_cases hd : z ∈ D
    · exact Finset.mem_union_right _ hd
    · have hYes := (Finset.mem_filter.mp hz).2
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hEq z hd) ▸ hYes⟩)
  exact (Finset.card_le_card hS).trans (Finset.card_union_le _ _)

private def facePoint (e : Fin k ⊕ Fin f ≃ Fin m) (a : BitString k) (y : BitString f) :
    BitString m := fun i => Sum.elim a y (e.symm i)

private theorem facePoint_injective (e : Fin k ⊕ Fin f ≃ Fin m) (a : BitString k) :
    Function.Injective (facePoint e a) := by
  intro x y h
  funext i
  simpa [facePoint] using congrFun h (e (.inr i))

private theorem longAnd_facePoint (e : Fin k ⊕ Fin f ≃ Fin m) (a : BitString k) (y : BitString f) :
    longAnd e a (facePoint e a y) = true := by
  simp [longAnd, pointFn, facePoint]

private theorem tally_lower_of_occurs (e : Fin k ⊕ Fin f ≃ Fin m)
    (a : BitString k) (hf : 5 ≤ f) (i : Fin m) (b : Bool)
    (h : ∃ z, longAnd e a z = true ∧ z i = b) :
    9 ≤ tally (longAnd e a) (some (i,b)) := by
  obtain ⟨z,hz,hzi⟩ := h
  have hFixed : (fun j => z (e (.inl j))) = a := of_decide_eq_true hz
  let S := Finset.univ.filter (fun z => longAnd e a z = true ∧ selects (some (i,b)) z = true)
  rw [tally_eq_card]
  change 9 ≤ S.card
  cases hi : e.symm i with
  | inl j =>
    have hj : e (.inl j) = i := by rw [← hi, e.apply_symm_apply]
    have hB : a j = b := by rw [← congrFun hFixed j, hj, hzi]
    have hSub : (Finset.univ : Finset (BitString f)).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (facePoint e a) _ (facePoint_injective e a).injOn
      intro y _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        longAnd_facePoint _ _ _, by simp [selects, facePoint, hi, hB]⟩
    rw [Finset.card_univ, BitString.card] at hSub
    have hPow : 32 ≤ 2^f := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf
    omega
  | inr j =>
    cases f with
    | zero => omega
    | succ f =>
      let row (y : BitString f) : BitString (f+1) := Fin.cons b y ∘ Equiv.swap 0 j
      have hRow : Function.Injective row := by
        intro x y he
        funext t
        have he' := congrFun he ((Equiv.swap (0 : Fin (f+1)) j) t.succ)
        simpa [row, Function.comp_apply, Equiv.swap_apply_self] using he'
      have hAt (y : BitString f) : row y j = b := by simp [row, Equiv.swap_apply_right]
      have hSub : (Finset.univ : Finset (BitString f)).card ≤ S.card := by
        apply Finset.card_le_card_of_injOn (fun y => facePoint e a (row y)) _
          ((facePoint_injective e a).comp hRow).injOn
        intro y _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          longAnd_facePoint _ _ _, by simp [selects, facePoint, hi, hAt]⟩
      rw [Finset.card_univ, BitString.card] at hSub
      have hPow : 16 ≤ 2^f := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 4 ≤ f by omega)
      omega

theorem recover_longAnd (e : Fin k ⊕ Fin f ≃ Fin m) (a : BitString k) (hf : 5 ≤ f)
    (R : BooleanFunction m) (D : Finset (BitString m)) (hD : D.card ≤ 4)
    (hEq : ∀ z, z ∉ D → R z = longAnd e a z) :
    recovered R = longAnd e a := by
  have hCount (i : Fin m) (b : Bool) :
      5 ≤ tally R (some (i,b)) ↔ ∃ z, longAnd e a z = true ∧ z i = b := by
    constructor
    · intro h
      by_contra hn
      have hEmpty : tally (longAnd e a) (some (i,b)) = 0 := by
        rw [tally_eq_card, Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        apply hn
        have hh := (Finset.mem_filter.mp hz).2
        exact ⟨z,hh.1,by simpa [selects] using hh.2⟩
      have hh := tally_le_add_noise D hEq (some (i,b))
      omega
    · intro h
      have hl := tally_lower_of_occurs e a hf i b h
      have hb := tally_le_add_noise D (fun z hz => (hEq z hz).symm) (some (i,b))
      omega
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [recovered, face, decide_eq_true_eq, hCount]
  constructor
  · intro h
    change decide ((fun j => z (e (.inl j))) = a) = true
    apply decide_eq_true
    funext j
    obtain ⟨y,hy,hi⟩ := h (e (.inl j))
    have hFix : (fun j => y (e (.inl j))) = a := of_decide_eq_true hy
    exact hi.symm.trans (congrFun hFix j)
  · intro hz i
    exact ⟨z,hz,rfl⟩

theorem recover_zero {m : ℕ} (hm : 0 < m) (R : BooleanFunction m)
    (D : Finset (BitString m)) (hD : D.card ≤ 4) (hEq : ∀ z, z ∉ D → R z = false) :
    recovered R = fun _ => false := by
  let i : Fin m := ⟨0,hm⟩
  have hBound (b : Bool) : tally R (some (i,b)) ≤ 4 := by
    have h := tally_le_add_noise D hEq (some (i,b))
    have h0 : tally (fun _ : BitString m => false) (some (i,b)) = 0 := by simp [tally]
    omega
  funext z
  apply Bool.eq_false_of_not_eq_true
  intro hz
  have hb := of_decide_eq_true (of_decide_eq_true hz i)
  have hh := hBound (z i)
  exact (by omega : ¬5 ≤ tally R (some (i,z i))) hb

section Samples

open InvariantControl (weight)

private theorem weight_zero_iff (z : BitString m) : weight z = 0 ↔ z = zeroVec m := by
  rw [weight, Finset.card_eq_zero]
  constructor
  · intro h
    funext i
    change z i = false
    cases hi : z i
    · rfl
    · have hMem : i ∈ (Finset.univ : Finset (Fin m)).filter (fun j => z j = true) := by simp [hi]
      rw [h] at hMem
      exact (Finset.notMem_empty i hMem).elim
  · rintro rfl
    simp [zeroVec]

theorem mem_sample_iff_weight_le (d : ℕ) (z : BitString m) :
    z ∈ sample d m ↔ weight z ≤ d := by
  induction m generalizing d with
  | zero =>
    rw [Subsingleton.elim z (zeroVec 0)]
    cases d <;> simp [sample, weight, zeroVec]
  | succ m ih =>
    cases d with
    | zero => simp only [sample, Finset.mem_singleton, Nat.le_zero, weight_zero_iff]
    | succ d =>
      have hCase (b : Bool) (y : BitString m) :
          Fin.cons b y ∈ sample (d+1) (m+1) ↔
            (if b then y ∈ sample d m else y ∈ sample (d+1) m) := by
        change Fin.cons b y ∈ (sample (d+1) m).map (consEmb m false) ∪
          (sample d m).map (consEmb m true) ↔ _
        simp only [Finset.mem_union, Finset.mem_map]
        have hEmb (a : Bool) (x : BitString m) :
            consEmb m a x = Fin.cons b y ↔ a=b ∧ x=y := by
          constructor
          · intro h
            change @Fin.cons m (fun _ => Bool) a x = @Fin.cons m (fun _ => Bool) b y at h
            exact ⟨congrFun h 0, by simpa using congrArg (Fin.tail : BitString (m+1) → BitString m) h⟩
          · rintro ⟨rfl,rfl⟩
            rfl
        cases b <;> simp [hEmb]
      conv_lhs => rw [← Fin.cons_self_tail z, hCase]
      conv_rhs => rw [← Fin.cons_self_tail z, PatchedCut.weight_cons]
      cases hz : z 0
      · simpa using ih (d+1) (Fin.tail z)
      · simpa using ih d (Fin.tail z)

private theorem weight_xor_le (x y : BitString m) : weight (bitXor x y) ≤ weight x + weight y := by
  let S (z : BitString m) := (Finset.univ : Finset (Fin m)).filter (fun i => z i = true)
  have hs : S (bitXor x y) ⊆ S x ∪ S y := by
    intro i hi
    have hh := (Finset.mem_filter.mp hi).2
    cases hx : x i <;> cases hy : y i <;> simp_all [bitXor, S]
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem longAnd_diameter (e : Fin k ⊕ Fin f ≃ Fin m) (a : BitString k)
    {x y : BitString m} (hx : longAnd e a x = true) (hy : longAnd e a y = true) :
    weight (bitXor x y) ≤ f := by
  have hX : (fun j => x (e (.inl j))) = a := of_decide_eq_true hx
  have hY : (fun j => y (e (.inl j))) = a := of_decide_eq_true hy
  let S := (Finset.univ : Finset (Fin f)).image (fun j => e (.inr j))
  have hS : (Finset.univ.filter (fun i => bitXor x y i = true)) ⊆ S := by
    intro i hi
    obtain ⟨j,rfl⟩ := e.surjective i
    cases j with
    | inl j =>
      have hh := (Finset.mem_filter.mp hi).2
      change (x (e (.inl j)) ^^ y (e (.inl j))) = true at hh
      simp [congrFun hX j, congrFun hY j] at hh
    | inr j => exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  exact (Finset.card_le_card hS).trans (Finset.card_image_le.trans (by simp))

private theorem shifted_sample_iff (d : ℕ) (a z : BitString m) :
    z ∈ shifted (sample d m) a ↔ weight (bitXor z a) ≤ d := by
  rw [← mem_sample_iff_weight_le]
  constructor
  · rintro hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    rwa [bitXor_cancel_self_right]
  · intro hz
    exact Finset.mem_image.mpr ⟨_,hz,bitXor_cancel_self_right _ _⟩

theorem clean_beyond_face {C : Finset (BitString m)} {d f : ℕ}
    (hSep : Separated (sample (d+f) m) C)
    (H : BooleanFunction m) (hDiam : ∀ x y, H x = true → H y = true → weight (bitXor x y) ≤ f)
    (D : Finset (BitString m)) (hC : D.card+1 < C.card) :
    ∃ a ∈ C, Disjoint D (shifted (sample d m) a) ∧
      ∀ z ∈ shifted (sample d m) a, H z = false := by
  let bad := C.filter (fun a => ∃ z ∈ shifted (sample d m) a, H z = true)
  have hBad : bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hn
    obtain ⟨haC,x,hx,hHx⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbC,y,hy,hHy⟩ := Finset.mem_filter.mp hb
    have hX := (shifted_sample_iff d a x).mp hx
    have hY := (shifted_sample_iff d b y).mp hy
    have hW := weight_xor_le (bitXor y x) (bitXor x a)
    rw [bitXor_assoc, bitXor_cancel_self_left] at hW
    have hZ := hDiam y x hHy hHx
    exact Finset.disjoint_left.mp (hSep haC hbC hn)
      ((shifted_sample_iff _ _ _).mpr (by omega : weight (bitXor y a) ≤ d+f))
      ((shifted_sample_iff _ _ _).mpr (by omega : weight (bitXor y b) ≤ d+f))
  let good := C \ bad
  have hGood : D.card < good.card := by
    have hG := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _ : bad ⊆ C)
    change good.card + bad.card = C.card at hG
    omega
  have hSmall : Separated (sample d m) good := by
    intro a ha b hb hn
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    have hzA := (shifted_sample_iff d a z).mp hza
    have hzB := (shifted_sample_iff d b z).mp hzb
    exact Finset.disjoint_left.mp (hSep (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hn)
      ((shifted_sample_iff _ _ _).mpr (by omega : weight (bitXor z a) ≤ d+f))
      ((shifted_sample_iff _ _ _).mpr (by omega : weight (bitXor z b) ≤ d+f))
  obtain ⟨a,ha,hd⟩ := exists_clean hSmall hGood
  obtain ⟨haC,haBad⟩ := Finset.mem_sdiff.mp ha
  refine ⟨a,haC,hd,fun z hz => Bool.eq_false_of_not_eq_true fun hh => ?_⟩
  exact haBad (Finset.mem_filter.mpr ⟨haC,z,hz,hh⟩)

theorem schedule_centers_wideAt (r : ℕ) (hr : 10 ≤ r) {count : ℕ} (hCount : count ≤ 64) :
    ∃ C : Finset (BitString (logArity r)), C.card = count+1 ∧
      Separated (sample (2*r) (logArity r)) C := by
  let m := logArity r
  let B := (sample (2*r) m).card
  have hB : B ≤ 2^((r+1)*(2*r)) := by
    rw [pow_mul]
    exact (card_sample_le _ _).trans (Nat.pow_le_pow_left (schedule_base r hr) _)
  have hMargin := schedule_margin r hr
  have hExp : 6+2*((r+1)*(2*r)) < m := by
    change _ < r+(2^r+1)+1
    nlinarith
  apply exists_separated _ (sample_nonempty _ _)
  change count*(B*B) < 2^m
  calc
    _ ≤ 64*(2^((r+1)*(2*r))*2^((r+1)*(2*r))) :=
      Nat.mul_le_mul hCount (Nat.mul_le_mul hB hB)
    _ = 2^(6+2*((r+1)*(2*r))) := by
      rw [two_mul ((r+1)*(2*r)), pow_add 2 6, pow_add 2 ((r+1)*(2*r))]
      rfl
    _ < _ := Nat.pow_lt_pow_right (by decide) hExp

theorem schedule_centers_wide (r : ℕ) (hr : 10 ≤ r) :
    ∃ C : Finset (BitString (logArity r)), C.card = 6 ∧ Separated (sample (2*r) (logArity r)) C :=
  schedule_centers_wideAt r hr (by decide : 5 ≤ 64)

end Samples

section Control

def residual (T : BitString (2^m)) (F : BooleanFunction m) : BooleanFunction m :=
  fun z => JuntaRadius.viewed m T z ^^ F z

def fitted (T : BitString (2^m)) (F : BooleanFunction m) : BooleanFunction m :=
  fun z => F z ^^ recovered (residual T F) z

noncomputable def attempt {r s : ℕ} (a : BitString (Arity r s)) (T : BitString (2^Arity r s)) : Bool :=
  let F := predicted (r+1) a T
  belongs (r := r) (s := s) F &&
    decide (JuntaRadius.distance (JuntaRadius.viewed _ T) (fitted T F) ≤ 4)

noncomputable def control (r : ℕ) (hr : 10 ≤ r) (T : BitString (2^logArity r)) : Bool :=
  decide (∃ a ∈ (schedule_centers_wide r hr).choose, attempt (r := r) (s := 2^r) a T = true)

private theorem table_cost_of_model (r : ℕ) (hr : 10 ≤ r)
    (j : Fin (logArity r)) (U : Labels r (2^r)) :
    complexity interpretation (single (JuntaRadius.viewed _ (rotated j (diagonal U)))) ≤
      28*logArity r+40 := by
  have hm : 1024 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  have hCost := diagonal_certificate_cost (r := r) (s := 2^r) (by omega) (by omega) U
  rw [view_rotated, PermutedCut.complexity_comp_perm]
  exact hCost.trans (by dsimp [logArity, Arity]; omega)

theorem control_sound (r : ℕ) (hr : 10 ≤ r) {T : BitString (2^logArity r)}
    (hT : control r hr T = true) : mcspSquare (logArity r) T = true := by
  let m := logArity r
  obtain ⟨a,_,ha⟩ := of_decide_eq_true hT
  obtain ⟨hB,hDist⟩ := Bool.and_eq_true_iff.mp ha
  let F := predicted (r+1) a T
  obtain ⟨j,hj⟩ := of_decide_eq_true hB
  let U := recoverLabels (r := r) (s := 2^r) (fun z => F (z ∘ blockSwap j))
  have hF : F = JuntaRadius.viewed m (rotated j (diagonal U)) :=
    eq_of_sample _ _ (degree_predicted _ _ _) (degree_rotated (by omega) j U) hj
  have hFCost : complexity interpretation (single F) ≤ 28*m+40 := by
    rw [hF]
    exact table_cost_of_model r hr j U
  have hFace := face_cost (fun i b => decide (5 ≤ tally (residual T F) (some (i,b))))
  change complexity interpretation (single (recovered (residual T F))) ≤ 2*m+1 at hFace
  have hCost : complexity interpretation (single (fitted T F)) ≤ 30*m+45 :=
    (complexity_xor_le F (recovered (residual T F))).trans (by omega)
  let D := (Finset.univ : Finset (Fin (2^m))).filter fun i =>
    T i ≠ MCSP.truthTable m (fitted T F) i
  have hD : D.card ≤ 4 := by
    have hd : JuntaRadius.distance (JuntaRadius.viewed m T) (fitted T F) ≤ 4 := of_decide_eq_true hDist
    rwa [JuntaRadius.distance_eq_raw] at hd
  have he : T = patch D (MCSP.truthTable m (fitted T F)) := by
    funext i
    simp only [patch, D, Finset.mem_filter, Finset.mem_univ, true_and]
    have hbit (a b : Bool) : a = (b ^^ decide (a ≠ b)) := by cases a <;> cases b <;> decide
    exact hbit _ _
  have hM : 1024 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  have hEnough := Nat.mul_le_mul_right m (show 36 ≤ m by dsimp [m,logArity,Arity]; omega)
  rw [← pow_two] at hEnough
  rw [he]
  exact JuntaRadius.patched_function_of_budget _ D hD hCost (by dsimp [m,logArity,Arity] at *; omega)

private theorem prediction_on_clean {d : ℕ} {G : BooleanFunction m}
    (hG : isDegFn d m G = true) {a : BitString m} {T : BitString (2^m)}
    (hClean : ∀ z ∈ shifted (sample d m) a, JuntaRadius.viewed m T z = G z) :
    predicted d a T = G := by
  have hExt : extend d m (fun z => JuntaRadius.viewed m T (bitXor z a)) =
      fun z => G (bitXor z a) := by
    rw [← extend_eq_of_degree _ _ (isDegFn_comp_affine hG (xor_affine a))]
    exact extend_congr _ _ (fun z hz => hClean _ (Finset.mem_image_of_mem _ hz))
  funext z
  simp [predicted, hExt, bitXor_cancel_self_right]

theorem control_accepts_model (r : ℕ) (hr : 10 ≤ r)
    (j : Fin (logArity r)) (U : Labels r (2^r))
    (H : BooleanFunction (logArity r))
    (hDiam : ∀ x y, H x = true → H y = true → InvariantControl.weight (bitXor x y) ≤ r-1)
    (hRecover : ∀ R (E : Finset (BitString (logArity r))), E.card ≤ 4 →
      (∀ z, z ∉ E → R z = H z) → recovered R = H)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    let G := JuntaRadius.viewed _ (rotated j (diagonal U))
    control r hr (patch D (MCSP.truthTable _ (fun z => G z ^^ H z))) = true := by
  let m := logArity r
  let G := JuntaRadius.viewed m (rotated j (diagonal U))
  let T := patch D (MCSP.truthTable m (fun z => G z ^^ H z))
  let E := D.map (BitString.equivFin m).symm.toEmbedding
  let C := (schedule_centers_wide r hr).choose
  obtain ⟨hC,hSep⟩ := (schedule_centers_wide r hr).choose_spec
  change C.card = 6 at hC
  have hSep' : Separated (sample ((r+1)+(r-1)) m) C := by
    rw [show (r+1)+(r-1)=2*r by omega]
    exact hSep
  have hE : E.card ≤ 4 := by rw [Finset.card_map]; exact hD
  obtain ⟨a,ha,hClean,hH⟩ := clean_beyond_face hSep' H hDiam E (by omega)
  have hRead (z : BitString m) (hz : z ∉ E) :
      JuntaRadius.viewed m T z = (G z ^^ H z) := by
    have hn : BitString.equivFin m z ∉ D := fun hh =>
      hz (Finset.mem_map.mpr ⟨_,hh,Equiv.symm_apply_apply _ _⟩)
    change patch D (MCSP.truthTable m (fun z => G z ^^ H z)) (BitString.equivFin m z) = _
    simp [patch, hn, MCSP.truthTable_apply]
  have hPred : predicted (r+1) a T = G := by
    apply prediction_on_clean (degree_rotated (by omega) j U)
    intro z hz
    rw [hRead z (fun hh => Finset.disjoint_left.mp hClean hh hz), hH z hz, Bool.xor_false]
  have hR : recovered (residual T G) = H := hRecover _ _ hE (fun z hz => by
    rw [residual, hRead z hz]
    cases G z <;> cases H z <;> rfl)
  change control r hr T = true
  apply decide_eq_true
  refine ⟨a,ha,?_⟩
  unfold attempt
  rw [hPred, Bool.and_eq_true]
  constructor
  · exact decide_eq_true ⟨j,fun z _ => congrFun (fit_rotated j U).symm z⟩
  · have he : fitted T G = fun z => G z ^^ H z := by unfold fitted; rw [hR]
    rw [he]
    exact decide_eq_true ((JuntaRadius.patch_distance_le D _).trans hD)

end Control

section Size

private theorem synth_fitted {m : ℕ} (w : BitString m → BooleanFunction (2^m))
    {S : Set (BooleanFunction (2^m))} (hin : inputs (2^m) ⊆ S) (hw : ∀ z, w z ∈ S) :
    Synthesis interpretation S
      (Set.range (fun z T => fitted T (fun y => w y T) z)) (813*2^m) := by
  let R (z : BitString m) (T : BitString (2^m)) := residual T (fun y => w y T) z
  let H (z : BitString m) (T : BitString (2^m)) := recovered (fun y => R y T) z
  let A := S ∪ Set.range R
  let B := A ∪ Set.range H
  have hR (z : BitString m) : Synthesis interpretation S {R z} 4 :=
    (Synthesis.of_mem (hin ⟨BitString.equivFin _ z,rfl⟩)).xor (Synthesis.of_mem (hw z))
  have hAllR : Synthesis interpretation S (Set.range R) (4*2^m) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, Nat.mul_comm] using
      Synthesis.family R (fun _ => 4) hR
  have hH : Synthesis interpretation A (Set.range H) (805*2^m) :=
    synth_recovered R (fun z => Or.inr ⟨z,rfl⟩)
  have hO (z : BitString m) :
      Synthesis interpretation B {fun T => fitted T (fun y => w y T) z} 4 :=
    (Synthesis.of_mem (Or.inl (Or.inl (hw z)))).xor (Synthesis.of_mem (Or.inr ⟨z,rfl⟩))
  have hAllO : Synthesis interpretation B
      (Set.range (fun z T => fitted T (fun y => w y T) z)) (4*2^m) := by
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, BitString.card, Nat.mul_comm] using
      Synthesis.family _ (fun _ => 4) hO
  exact ((hAllR.trans (hH.trans hAllO))).mono Set.Subset.rfl Set.Subset.rfl (by omega)

private theorem synth_attempt {r s : ℕ} (a : BitString (Arity r s)) :
    Synthesis interpretation (inputs (2^Arity r s)) {attempt (r := r) (s := s) a}
      ((8*(r+1)+829)*2^Arity r s+sampleBudget r s+4) := by
  let m := Arity r s
  let w (z : BitString m) (T : BitString (2^m)) := predicted (r+1) a T z
  let S := inputs (2^m) ∪ Set.range w
  let out (z : BitString m) (T : BitString (2^m)) := fitted T (fun y => w y T) z
  have hPredict : Synthesis interpretation (inputs (2^m)) (Set.range w) (8*(r+1)*2^m) := by
    have hE := extend_synthesis (r+1) m (S := inputs (2^m))
      (fun y T => T (BitString.equivFin m (bitXor y a))) (fun y => ⟨_,rfl⟩)
    apply hE.mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨z,rfl⟩
    exact ⟨bitXor z a,rfl⟩
  have hOut : Synthesis interpretation S (Set.range out) (813*2^m) :=
    synth_fitted w (fun _ => Or.inl) (fun z => Or.inr ⟨z,rfl⟩)
  have hModel := synth_belongs w (S := S ∪ Set.range out) (fun z => Or.inl (Or.inr ⟨z,rfl⟩))
  have hDist := synth_distance 4 out (S := S ∪ Set.range out)
    (fun _ h => Or.inl (Or.inl h)) (fun z => Or.inr ⟨z,rfl⟩)
  have hAll := hPredict.trans (hOut.trans (hModel.and hDist))
  apply hAll.mono Set.Subset.rfl Set.Subset.rfl
  change 8*(r+1)*2^m + (813*2^m+(sampleBudget r s+(16*2^m+3)+1)) ≤
    (8*(r+1)+829)*2^m+sampleBudget r s+4
  rw [Nat.add_mul]
  omega

theorem control_size (r : ℕ) (hr : 10 ≤ r) :
    complexity interpretation (single (control r hr)) ≤ 5100*(r+1)*2^logArity r := by
  let m := logArity r
  let N := 2^m
  let C := (schedule_centers_wide r hr).choose
  have hC : C.card = 6 := (schedule_centers_wide r hr).choose_spec.1
  have hN : 1 ≤ N := Nat.two_pow_pos _
  have hB : sampleBudget r (2^r) ≤ N := sample_budget_le r hr
  have hAll := Synthesis.exists_mem C (attempt (r := r) (s := 2^r))
    (fun _ => (8*(r+1)+829)*N+sampleBudget r (2^r)+4) (fun a _ => synth_attempt a)
  have hFinal := Synthesis.congr_iff hAll (g := control r hr) (fun T => by simp [control, C])
  have hSize := hFinal.complexity_le
  simp only [Finset.sum_const, smul_eq_mul, hC, Nat.add_assoc] at hSize
  refine hSize.trans ?_
  change 6*((8*(r+1)+829)*N+(sampleBudget r (2^r)+5))+1 ≤ 5100*(r+1)*N
  calc
    _ = 48*(r+1)*N+4974*N+6*sampleBudget r (2^r)+31 := by ring
    _ ≤ 48*(r+1)*N+5011*N := by omega
    _ = (48*(r+1)+5011)*N := by rw [Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right N (by omega)

theorem control_sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (control r hr)) ≤ logArity r * 2^logArity r := by
  have hf := Nat.eventually_mul_add_one_pow_le_pow_div (5100*K) 1 1
    (by decide : 1 < (2 : ℕ)) (by decide)
  filter_upwards [hf] with r he hr
  have hPoly : 5100*K*(r+1) ≤ 2^r := by simpa using he
  have hm : 2^r ≤ logArity r := by dsimp [logArity, Arity]; omega
  calc
    _ ≤ K*(5100*(r+1)*2^logArity r) := Nat.mul_le_mul_left _ (control_size r hr)
    _ = (5100*K*(r+1))*2^logArity r := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (hPoly.trans hm)

end Size

def radius (r : ℕ) : ℕ := 2^(r-1)+4

private theorem twice_growing_support (r : ℕ) (hr : 10 ≤ r) :
    2*2^(r-1) = 2^r := by
  calc
    _ = 2^((r-1)+1) := (pow_succ' 2 (r-1)).symm
    _ = _ := by rw [Nat.sub_add_cancel (show 1 ≤ r by omega)]

theorem growing_support_bounds (r : ℕ) (hr : 10 ≤ r)
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k) :
    logArity r ≤ 4*(support e a).card ∧ 2*(support e a).card ≤ logArity r := by
  rw [support_card_pow, twice_growing_support r hr]
  have hBase := schedule_base r hr
  rw [pow_succ'] at hBase
  have hp := twice_growing_support r hr
  have hAr : 2^r ≤ logArity r := by dsimp [logArity,Arity]; omega
  exact ⟨by omega,hAr⟩

theorem growing_positive_misses_sample (r : ℕ) (hr : 10 ≤ r)
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) {z : BitString (logArity r)}
    (hz : z ∈ sample (r+1) (logArity r)) : longAnd e (fun _ => true) z = false := by
  apply longAnd_invisible e _ hz
  have hAr := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hAr
  have hp : r < 2^r := Nat.lt_two_pow_self
  dsimp [logArity,Arity] at hAr
  omega

theorem growing_selector (r : ℕ) (hr : 10 ≤ r) :
    ∃ h : BooleanFunction (2^r), TestsAt (r := r) (radius r) h := by
  let t := 2^r-1
  have ht : t+1 = 2^r := by dsimp [t]; have := Nat.two_pow_pos r; omega
  have hp := twice_growing_support r hr
  rw [← ht]
  exact exists_selectorAt r t _ hr ht.ge (by unfold radius; rw [Nat.mul_add, hp]; omega)

theorem control_sparse (r : ℕ) (hr : 10 ≤ r) :
    (acceptingTables (control r hr)).card ≤ 2 ^ descriptionBitBound (logArity r) := by
  apply (Finset.card_le_card ?_).trans (card_accepting_mcspSquare_le _)
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, control_sound r hr (Finset.mem_filter.mp hT).2⟩

theorem control_accepts_longAnd (r : ℕ) (hr : 10 ≤ r) (j : Fin (logArity r))
    (U : Labels r (2^r)) (e : Fin k ⊕ Fin f ≃ Fin (logArity r)) (a : BitString k)
    (hf : 5 ≤ f) (hDim : f ≤ r-1)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    control r hr (patch D (patch (support e a) (rotated j (diagonal U)))) = true := by
  let G := JuntaRadius.viewed _ (rotated j (diagonal U))
  have he : patch (support e a) (rotated j (diagonal U)) =
      MCSP.truthTable _ (fun z => G z ^^ longAnd e a z) := by
    funext i
    simp only [patch, support, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.decide_coe, MCSP.truthTable_apply]
    congr 1
    change rotated j (diagonal U) i = rotated j (diagonal U)
      (BitString.equivFin _ ((BitString.equivFin _).symm i))
    rw [Equiv.apply_symm_apply]
  rw [he]
  exact control_accepts_model r hr j U _ (fun _ _ hx hy => (longAnd_diameter e a hx hy).trans hDim)
    (fun R E hd he => recover_longAnd e a hf R E hd he) D hD

/-- The same sparse circuit passes every signed AND twist and every block
coordinate. The common AND and the four noise flips may overlap. -/
theorem longAnd_tests_up_to (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) (radius r) h) (j : Fin (logArity r)) (U V : Labels r (2^r))
    (e : Fin k ⊕ Fin f ≃ Fin (logArity r)) (a : BitString k)
    (hf : 5 ≤ f) (hDim : f ≤ r-1)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    let T := patch D (patch (support e a) (rotated j (mixed h U V)))
    (mcspSquare (logArity r) T = true ↔ U = V) ∧ (control r hr T = true ↔ U = V) := by
  have hE : (combine D (support e a)).card ≤ radius r := by
    have hc := card_combine_le D (support e a)
    rw [support_card_pow] at hc
    have hp : 2^f ≤ 2^(r-1) := Nat.pow_le_pow_right (by decide) hDim
    unfold radius
    omega
  have hExact : mcspSquare (logArity r) (patch D (patch (support e a) (rotated j (mixed h U V)))) =
      true ↔ U = V := by
    rw [patch_combine]
    exact exact_transportAt hh j U V _ hE
  refine ⟨hExact, fun hc => hExact.mp (control_sound r hr hc), ?_⟩
  rintro rfl
  rw [mixed_eq_splice, CommunicationCut.splice_self]
  exact control_accepts_longAnd r hr j U e a hf hDim D hD

theorem growing_longAnd_tests (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) (radius r) h) (j : Fin (logArity r)) (U V : Labels r (2^r))
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    let T := patch D (patch (support e a) (rotated j (mixed h U V)))
    (mcspSquare (logArity r) T = true ↔ U = V) ∧ (control r hr T = true ↔ U = V) :=
  longAnd_tests_up_to r hr hh j U V e a (by omega) le_rfl D hD

theorem control_original_tests (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : Tests (r := r) h) (j : Fin (logArity r)) (U V : Labels r (2^r))
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    control r hr (patch D (rotated j (mixed h U V))) = true ↔ U = V := by
  refine ⟨fun hc => (exact_transport hh j U V D hD).mp (control_sound r hr hc), ?_⟩
  rintro rfl
  rw [mixed_eq_splice, CommunicationCut.splice_self]
  have h := control_accepts_model r hr j U (fun _ => false)
    (fun _ _ h _ => Bool.false_ne_true h |>.elim)
    (fun R E hd he => recover_zero (show 0 < logArity r from Nat.succ_pos _) R E hd he) D hD
  simp only [Bool.xor_false, JuntaRadius.viewed, Equiv.apply_symm_apply] at h
  exact h

private theorem face_cannot_be_low_degree (r : ℕ) (hr : 10 ≤ r)
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
    (F : BooleanFunction (logArity r)) (hDeg : isDegFn (r+1) (logArity r) F = true)
    (D : Finset (BitString (logArity r))) (hD : D.card ≤ 40)
    (hEq : ∀ z, z ∉ D → F z = longAnd e a z) : False := by
  let m := logArity r
  let H := longAnd e a
  obtain ⟨C,hC,hSep⟩ := schedule_centers_wideAt r hr (by decide : 41 ≤ 64)
  have hSep' : Separated (sample ((r+1)+(r-1)) m) C := by
    rw [show (r+1)+(r-1)=2*r by omega]
    exact hSep
  obtain ⟨u,_,hClean,hH⟩ := clean_beyond_face hSep' H (fun _ _ => longAnd_diameter e a)
    D (by omega)
  have hF0 : (fun z => F (bitXor z u)) = fun _ => false := by
    apply eq_of_sample (r+1) m (isDegFn_comp_affine hDeg (xor_affine u)) (isDegFn_const _ _ _)
    intro z hz
    have hm : bitXor z u ∈ shifted (sample (r+1) m) u := Finset.mem_image_of_mem _ hz
    rw [hEq _ (fun h => Finset.disjoint_left.mp hClean h hm)]
    exact hH _ hm
  have hZero (z : BitString m) : F z = false := by
    simpa only [bitXor_cancel_self_right] using congrFun hF0 (bitXor z u)
  let P := support e a
  let B := D.map (BitString.equivFin m).toEmbedding
  have hP : P.card = 2^(r-1) := support_card_pow e a
  have hMany : 512 ≤ 2^(r-1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 9 ≤ r-1 by omega)
  have hSize : B.card < P.card := by rw [Finset.card_map, hP]; omega
  obtain ⟨i,hi,hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hSize
  let z := (BitString.equivFin m).symm i
  have hz : z ∉ D := fun hd => hn (Finset.mem_map.mpr ⟨_,hd,Equiv.apply_symm_apply _ _⟩)
  have hH' : H z = true := (Finset.mem_filter.mp hi).2
  change longAnd e a z = true at hH'
  rw [← hEq z hz, hZero] at hH'
  cases hH'

theorem control36_rejects_growing (r : ℕ) (hr : 10 ≤ r)
    (j : Fin (logArity r)) (U : Labels r (2^r))
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    control36 r hr (patch D (patch (support e a) (rotated j (diagonal U)))) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  obtain ⟨i,V,E,hE,he⟩ := controlAt_witness (show 1 ≤ r by omega) h
  let m := logArity r
  let A := rotated j (diagonal U)
  let B := rotated i (diagonal V)
  let N := (D ∪ E).map (BitString.equivFin m).symm.toEmbedding
  have hN : N.card ≤ 40 := by
    rw [Finset.card_map]
    exact (Finset.card_union_le D E).trans (by omega)
  let F (z : BitString m) := JuntaRadius.viewed m A z ^^ JuntaRadius.viewed m B z
  have hDeg : isDegFn (r+1) m F = true :=
    isDegFn_xor (degree_rotated (by omega) j U) (degree_rotated (by omega) i V)
  apply face_cannot_be_low_degree r hr e a F hDeg N hN
  intro z hz
  let t := BitString.equivFin m z
  have ht : t ∉ D ∪ E := fun h =>
    hz (Finset.mem_map.mpr ⟨t,h,Equiv.symm_apply_apply _ _⟩)
  have hd : t ∉ D := fun h => ht (Finset.mem_union_left _ h)
  have he' : t ∉ E := fun h => ht (Finset.mem_union_right _ h)
  change patch D (patch (support e a) A) = patch E B at he
  have hVal : decide (t ∈ support e a) = longAnd e a z := by
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Bool.decide_coe]
    change longAnd e a ((BitString.equivFin m).symm ((BitString.equivFin m) z)) = _
    rw [Equiv.symm_apply_apply]
  have hRow := congrFun he t
  simp only [patch, hd, he', decide_false, Bool.xor_false, hVal] at hRow
  have hCancel (a b c : Bool) (h : (a ^^ c) = b) : (a ^^ b) = c := by
    cases a <;> cases b <;> cases c <;> simp_all
  exact hCancel _ _ _ hRow

#print axioms recover_longAnd
#print axioms schedule_centers_wide
#print axioms growing_selector
#print axioms growing_longAnd_tests
#print axioms control36_rejects_growing
#print axioms control_original_tests
#print axioms control_sparse
#print axioms control_sub_nlogn

end PvsNP.Frontier.GrowingAndOrbit
