module

public import MCSPJointOrbit

/-! A long conjunction adds a high-degree diagonal whose support is a
32-entry face. A shared decoder can treat the face as a bounded correction. -/

@[expose] public section

namespace PvsNP.Frontier.LongAndOrbit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open JointEquality JointOrbit PatchedCut DegreeSampler PolynomialBarrier
open QuadraticForest
open scoped Classical

variable {m k : ℕ}

/-- Select k coordinates and leave five free. A positive AND sets every
literal to true. Allowing any signs costs no extra work in the control. -/
def longAnd (e : Fin k ⊕ Fin 5 ≃ Fin m) (a : BitString k) : BooleanFunction m :=
  fun z => pointFn k a (fun i => z (e (.inl i)))

theorem longAnd_cost (e : Fin k ⊕ Fin 5 ≃ Fin m) (a : BitString k) :
    complexity interpretation (single (longAnd e a)) ≤ 2*k+1 :=
  (Boolean.synthesis_minterm (fun i => e (.inl i)) a).complexity_le

theorem longAnd_degree (e : Fin k ⊕ Fin 5 ≃ Fin m) (a : BitString k) {d : ℕ} (hd : d < k) :
    isDegFn d m (longAnd e a) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  let lift (z : BitString k) (i : Fin m) : Bool := Sum.elim z (zeroVec 5) (e.symm i)
  have hL : IsAffineMap lift := by
    intro i
    cases hi : e.symm i with
    | inl j =>
      have he : (fun z => lift z i) = (fun z => z j) := funext fun _ => by simp [lift, hi]
      rw [he]
      exact isDegFn_one_coord _ _
    | inr j =>
      have he : (fun z => lift z i) = (fun _ => false) := funext fun _ => by simp [lift, hi, zeroVec]
      rw [he]
      exact isDegFn_const _ _ _
  have hComp := isDegFn_comp_affine h hL
  have he : (fun z => longAnd e a (lift z)) = pointFn k a := by
    funext z
    simp [longAnd, lift]
  rw [he, isDegFn_pointFn_false hd a] at hComp
  cases hComp

noncomputable def support (e : Fin k ⊕ Fin 5 ≃ Fin m) (a : BitString k) : Finset (Fin (2^m)) :=
  Finset.univ.filter (fun i => longAnd e a ((BitString.equivFin m).symm i) = true)

theorem support_card (e : Fin k ⊕ Fin 5 ≃ Fin m) (a : BitString k) :
    (support e a).card = 32 := by
  let pack (y : BitString 5) (i : Fin m) : Bool := Sum.elim a y (e.symm i)
  let f (y : BitString 5) := BitString.equivFin m (pack y)
  have hI : Function.Injective f := by
    intro y z h
    have h' := (BitString.equivFin m).injective h
    funext i
    have hh := congrFun h' (e (.inr i))
    simpa [pack] using hh
  have he : support e a = Finset.univ.image f := by
    ext i
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      let z := (BitString.equivFin m).symm i
      have hFix : (fun j => z (e (.inl j))) = a := of_decide_eq_true hi
      let y (j : Fin 5) := z (e (.inr j))
      have hx : pack y = z := by
        funext j
        obtain ⟨j, rfl⟩ := e.surjective j
        cases j with
        | inl j =>
          simpa [pack] using (congrFun hFix j).symm
        | inr j => simp [pack, y]
      exact ⟨y, by simp [f, hx, z]⟩
    · rintro ⟨y, rfl⟩
      simp [longAnd, pointFn, f, pack]
  rw [he, Finset.card_image_of_injective _ hI, Finset.card_univ, BitString.card]
  rfl

private theorem low_weight {d m : ℕ} {z : BitString m} (hz : z ∈ sample d m) :
    InvariantControl.weight z ≤ d := by
  induction m generalizing d with
  | zero => simp [InvariantControl.weight]
  | succ m ih =>
    cases d with
    | zero =>
      have h0 : z = zeroVec (m+1) := Finset.mem_singleton.mp hz
      simp [h0, zeroVec, InvariantControl.weight]
    | succ d =>
      change z ∈ (sample (d+1) m).map (consEmb m false) ∪
        (sample d m).map (consEmb m true) at hz
      rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
        have h' := ih hy
        change InvariantControl.weight (Fin.cons false y) ≤ d+1
        simpa [PatchedCut.weight_cons] using h'
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp h
        have h' := ih hy
        change InvariantControl.weight (Fin.cons true y) ≤ d+1
        rw [PatchedCut.weight_cons]
        exact Nat.add_le_add_right h' 1

/-- Every sample of weight at most d misses a positive AND of length > d. -/
theorem longAnd_invisible (e : Fin k ⊕ Fin 5 ≃ Fin m) {d : ℕ} (hd : d < k)
    {z : BitString m} (hz : z ∈ sample d m) :
    longAnd e (fun _ => true) z = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hYes
  have hAll : (fun j => z (e (.inl j))) = (fun _ => true) := of_decide_eq_true hYes
  have hCnt : k ≤ InvariantControl.weight z := by
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k)))
      (t := (Finset.univ : Finset (Fin m)).filter (fun i => z i = true)) (fun i => e (.inl i))
      (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrFun hAll i⟩)
      (fun _ _ _ _ he => Sum.inl.inj (e.injective he))
    simpa only [InvariantControl.weight, Finset.card_univ, Fintype.card_fin] using h
  exact (not_le_of_gt hd) (hCnt.trans (low_weight hz))

private theorem schedule_long (r : ℕ) (hr : 10 ≤ r) : r+1 < logArity r-5 := by
  have h : 1024 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  dsimp [logArity, Arity]
  omega

def scheduleCoordinates (r : ℕ) (hr : 10 ≤ r) :
    Fin (logArity r-5) ⊕ Fin 5 ≃ Fin (logArity r) :=
  finSumFinEquiv.trans
    (Fin.castOrderIso (Nat.sub_add_cancel (by have := schedule_long r hr; omega))).toEquiv

theorem schedule_longAnd_misses_samples (r : ℕ) (hr : 10 ≤ r) :
    let F := longAnd (scheduleCoordinates r hr) (fun _ => true)
    isDegFn (r+1) (logArity r) F = false ∧
      ∀ z ∈ sample (r+1) (logArity r), F z = false :=
  ⟨longAnd_degree _ _ (schedule_long r hr),
    fun _ hz => longAnd_invisible _ (schedule_long r hr) hz⟩

/-- Compose two patches, cancelling entries flipped twice. -/
def combine {n : ℕ} (D E : Finset (Fin n)) : Finset (Fin n) := (D \ E) ∪ (E \ D)

theorem card_combine_le {n : ℕ} (D E : Finset (Fin n)) :
    (combine D E).card ≤ D.card + E.card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset))

theorem patch_combine {n : ℕ} (D E : Finset (Fin n)) (T : BitString n) :
    patch D (patch E T) = patch (combine D E) T := by
  funext i
  by_cases hd : i ∈ D <;> by_cases he : i ∈ E <;> simp [patch, combine, hd, he]

theorem selector36 (r : ℕ) (hr : 10 ≤ r) :
    ∃ h : BooleanFunction (2^r), TestsAt (r := r) 36 h := by
  let t := 2^r-1
  have ht : t+1 = 2^r := by dsimp [t]; have := Nat.two_pow_pos r; omega
  rw [← ht]
  exact exists_selectorAt r t 36 hr ht.ge le_rfl

noncomputable def control36 (r : ℕ) (hr : 10 ≤ r) : BooleanFunction (2^logArity r) :=
  controlAt (r := r) (s := 2^r) 36 (schedule_centersAt r hr (by decide : 36 ≤ 40)).choose

theorem control36_sound (r : ℕ) (hr : 10 ≤ r) {T : BitString (2^logArity r)}
    (hYes : control36 r hr T = true) : mcspSquare (logArity r) T = true := by
  obtain ⟨h, hh⟩ := selector36 r hr
  exact controlAt_sound (by omega) hh hYes

theorem control36_sparse (r : ℕ) (hr : 10 ≤ r) :
    (acceptingTables (control36 r hr)).card ≤ 2 ^ descriptionBitBound (logArity r) := by
  apply (Finset.card_le_card ?_).trans (card_accepting_mcspSquare_le _)
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    control36_sound r hr (Finset.mem_filter.mp hT).2⟩

/-- Both predicates still implement joint equality after applying any common
32-entry twist and four further flips, at any block placement. -/
theorem twisted_tests (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) 36 h) (j : Fin (logArity r)) (U V : Labels r (2^r))
    (D E : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) (hE : E.card ≤ 32) :
    let T := patch D (patch E (rotated j (mixed h U V)))
    (mcspSquare (logArity r) T = true ↔ U = V) ∧
      (control36 r hr T = true ↔ U = V) := by
  have hd : (combine D E).card ≤ 36 := (card_combine_le D E).trans (by omega)
  dsimp only
  rw [patch_combine]
  obtain ⟨hC,hSep⟩ := (schedule_centersAt r hr (by decide : 36 ≤ 40)).choose_spec
  exact ⟨exact_transportAt hh j U V _ hd,
    controlAt_passes (by omega) hh (by omega) hSep j U V _ hd⟩

theorem longAnd_tests (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) 36 h) (j : Fin (logArity r)) (U V : Labels r (2^r))
    (e : Fin k ⊕ Fin 5 ≃ Fin (logArity r)) (a : BitString k)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    let T := patch D (patch (support e a) (rotated j (mixed h U V)))
    (mcspSquare (logArity r) T = true ↔ U = V) ∧
      (control36 r hr T = true ↔ U = V) :=
  twisted_tests r hr hh j U V D (support e a) hD (support_card e a).le

theorem control36_size (r : ℕ) (hr : 10 ≤ r) :
    complexity interpretation (single (control36 r hr)) ≤ 3500*(r+1)*2^logArity r := by
  let N := 2^logArity r
  let C := (schedule_centersAt r hr (by decide : 36 ≤ 40)).choose
  have hC : C.card = 37 := (schedule_centersAt r hr (by decide : 36 ≤ 40)).choose_spec.1
  have hN : 1 ≤ N := Nat.two_pow_pos _
  have hB : sampleBudget r (2^r) ≤ N := sample_budget_le r hr
  have hs := controlAt_size (r := r) (s := 2^r) 36 C
  change complexity interpretation (single (control36 r hr)) ≤
      C.card*((8*(r+1)+80)*N+sampleBudget r (2^r)+5)+1 at hs
  rw [hC] at hs
  refine hs.trans ?_
  change _ ≤ 3500*(r+1)*N
  calc
    _ = 296*(r+1)*N+2960*N+37*sampleBudget r (2^r)+186 := by ring
    _ ≤ 296*(r+1)*N+3183*N := by omega
    _ = (296*(r+1)+3183)*N := by rw [Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right N (by omega)

theorem control36_sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (control36 r hr)) ≤ logArity r * 2^logArity r := by
  have hf := Nat.eventually_mul_add_one_pow_le_pow_div (3500*K) 1 1
    (by decide : 1 < (2 : ℕ)) (by decide)
  filter_upwards [hf] with r he hr
  have hPoly : 3500*K*(r+1) ≤ 2^r := by simpa using he
  have hm : 2^r ≤ logArity r := by dsimp [logArity, Arity]; omega
  calc
    _ ≤ K*(3500*(r+1)*2^logArity r) := Nat.mul_le_mul_left _ (control36_size r hr)
    _ = (3500*K*(r+1))*2^logArity r := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (hPoly.trans hm)

private theorem small_support_zero (r : ℕ) (hr : 10 ≤ r) (F : BooleanFunction (logArity r))
    (hF : isDegFn (r+1) (logArity r) F = true)
    (B : Finset (Fin (2^logArity r))) (hB : B.card ≤ 40)
    (hOut : ∀ i, i ∉ B → F ((BitString.equivFin (logArity r)).symm i) = false) :
    F = fun _ => false := by
  let m := logArity r
  obtain ⟨C,hC,hSep⟩ := schedule_centersAt r hr (by decide : 40 ≤ 40)
  let E := B.map (BitString.equivFin m).symm.toEmbedding
  have hSize : E.card < C.card := by rw [Finset.card_map, hC]; omega
  obtain ⟨a,_,ha⟩ := exists_clean hSep hSize
  have hAffine : IsAffineMap (fun z => bitXor z a) :=
    fun i => isDegFn_xor (isDegFn_one_coord m i) (isDegFn_const 1 m (a i))
  have hShift : (fun z => F (bitXor z a)) = fun _ => false := by
    apply eq_of_sample (r+1) m (isDegFn_comp_affine hF hAffine) (isDegFn_const _ _ _)
    intro z hz
    have hx : BitString.equivFin m (bitXor z a) ∉ B := fun hb =>
      Finset.disjoint_left.mp ha
        (Finset.mem_map.mpr ⟨_,hb,Equiv.symm_apply_apply _ _⟩) (Finset.mem_image_of_mem _ hz)
    have hv := hOut _ hx
    change F ((BitString.equivFin m).symm ((BitString.equivFin m) (bitXor z a))) = false at hv
    rwa [Equiv.symm_apply_apply] at hv
  funext z
  simpa only [bitXor_cancel_self_right] using congrFun hShift (bitXor z a)

/-- The previous four-flip recognizer misses every 32-entry AND twist of
every rotated diagonal, even with four additional flips. -/
theorem original_control_rejects (r : ℕ) (hr : 10 ≤ r)
    (j : Fin (logArity r)) (U : Labels r (2^r))
    (P D : Finset (Fin (2^logArity r))) (hP : P.card = 32) (hD : D.card ≤ 4) :
    logControl r hr (patch D (patch P (rotated j (diagonal U)))) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  obtain ⟨i,V,E,hE,he⟩ := control_witness (show 1 ≤ r by omega) h
  let m := logArity r
  let A : BitString (2^m) := rotated j (diagonal U)
  let B : BitString (2^m) := rotated i (diagonal V)
  change patch D (patch P A) = patch E B at he
  let F : BooleanFunction m := fun z => JuntaRadius.viewed m A z ^^ JuntaRadius.viewed m B z
  have hFAt (t : Fin (2^m)) : F ((BitString.equivFin m).symm t) = (A t ^^ B t) := by
    change ((A ((BitString.equivFin m) ((BitString.equivFin m).symm t))) ^^
      (B ((BitString.equivFin m) ((BitString.equivFin m).symm t)))) = _
    rw [Equiv.apply_symm_apply]
  let used := (D ∪ P) ∪ E
  have hUsed : used.card ≤ 40 := by
    have hu := Finset.card_union_le (D ∪ P) E
    have ht := Finset.card_union_le D P
    dsimp [used]
    omega
  have hDeg : isDegFn (r+1) m F = true :=
    isDegFn_xor (degree_rotated (by omega) j U) (degree_rotated (by omega) i V)
  have hZero := small_support_zero r hr F hDeg used hUsed (fun t ht => by
    have hh := congrFun he t
    have hnD : t ∉ D := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hnP : t ∉ P := fun h => ht (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hnE : t ∉ E := fun h => ht (Finset.mem_union_right _ h)
    simp only [patch, hnD, hnP, hnE, decide_false, Bool.xor_false] at hh
    change F ((BitString.equivFin m).symm t) = false
    rw [hFAt, hh, Bool.xor_self])
  have hSame : A = B := by
    funext t
    have hz := congrFun hZero ((BitString.equivFin m).symm t)
    change F ((BitString.equivFin m).symm t) = false at hz
    rw [hFAt] at hz
    cases hA : A t <;> cases hB : B t <;> simp_all
  have hFew : (D ∪ E).card < P.card := by
    have hUnion := Finset.card_union_le D E
    omega
  obtain ⟨t,ht,hAway⟩ := Finset.exists_mem_notMem_of_card_lt_card hFew
  have hnD : t ∉ D := fun h => hAway (Finset.mem_union_left _ h)
  have hnE : t ∉ E := fun h => hAway (Finset.mem_union_right _ h)
  have hBad := congrFun he t
  simp only [patch, hnD, hnE, ht, decide_false, decide_true, Bool.xor_false, hSame] at hBad
  cases B t <;> simp_all

theorem longAnd_separates (r : ℕ) (hr : 10 ≤ r)
    (j : Fin (logArity r)) (U : Labels r (2^r))
    (e : Fin k ⊕ Fin 5 ≃ Fin (logArity r)) (a : BitString k)
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    let T := patch D (patch (support e a) (rotated j (diagonal U)))
    mcspSquare (logArity r) T = true ∧ logControl r hr T = false ∧ control36 r hr T = true := by
  obtain ⟨h,hh⟩ := selector36 r hr
  have he : mixed h U U = diagonal U := by rw [mixed_eq_splice, CommunicationCut.splice_self]
  have hTests := longAnd_tests r hr hh j U U e a D hD
  dsimp only at hTests
  rw [he] at hTests
  exact ⟨hTests.1.mpr rfl, original_control_rejects r hr j U _ D (support_card e a) hD,
    hTests.2.mpr rfl⟩

#print axioms longAnd_degree
#print axioms schedule_longAnd_misses_samples
#print axioms selector36
#print axioms longAnd_tests
#print axioms longAnd_separates
#print axioms control36_sparse
#print axioms control36_sub_nlogn

end PvsNP.Frontier.LongAndOrbit
