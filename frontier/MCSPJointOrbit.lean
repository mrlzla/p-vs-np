module

public import MCSPJointEquality
public import MCSPDegreeSampler

/-! One recognizer for every choice of the block coordinate in the joint test. -/

@[expose] public section

namespace PvsNP.Frontier.JointOrbit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open JointEquality PermutedCut PatchedCut CommunicationCut
open PolynomialBarrier QuadraticForest DegreeSampler SuperTwoN
open scoped Classical

abbrev Arity (r s : ℕ) := (r+(s+1))+1

variable {r s m : ℕ}

def blockSwap (j : Fin (m+1)) : Equiv.Perm (Fin (m+1)) := Equiv.swap 0 j

@[simp] theorem blockSwap_zero (j : Fin (m+1)) : blockSwap j 0 = j :=
  Equiv.swap_apply_left _ _

def rotated {n : ℕ} (j : Fin (n+1)) (T : BitString (2 ^ (n+1))) : BitString (2 ^ (n+1)) :=
  T ∘ tablePerm (blockSwap j)

theorem exact_transport {h : BooleanFunction s} (hh : Tests (r := r) h)
    (j : Fin (Arity r s)) (U V : Labels r s)
    (D : Finset (Fin (2 ^ Arity r s))) (hD : D.card ≤ 4) :
    mcspSquare (Arity r s) (patch D (rotated j (mixed h U V))) = true ↔ U = V := by
  let e := blockSwap j
  let p := tablePerm e
  have he : patch D (rotated j (mixed h U V)) =
      (patch (D.map p.toEmbedding) (mixed h U V)) ∘ p := by
    funext i
    simp [patch, Function.comp_apply, rotated, p, e]
  rw [he, square_comp_tablePerm]
  exact hh U V _ (by simpa using hD)

theorem crossing_width {h : BooleanFunction s} (hh : Tests (r := r) h)
    (j : Fin (Arity r s)) (D : Finset (Fin (2 ^ Arity r s))) (hD : D.card ≤ 4)
    (c : Circuit signature (2 ^ Arity r s) 1)
    (hc : c.Computes interpretation (single (mcspSquare (Arity r s))))
    (owner : Wire (2 ^ Arity r s) c.size → Bool)
    (hOwner : ∀ i, owner (.input i) = rotated j (selector (r := r) h) i) :
    2*(2^r+(s+1)) ≤ (crossingWires c.program owner).card := by
  apply crossingWires_lower_bound_of_family_equality (card_labels r s)
    (rotated j (selector h)) (fun U => patch D (rotated j (diagonal U))) _ ?_ c hc owner hOwner
  intro U V
  have he : splice (rotated j (selector h)) (patch D (rotated j (diagonal U)))
      (patch D (rotated j (diagonal V))) = patch D (rotated j (mixed h U V)) := by
    funext i
    rw [mixed_eq_splice]
    cases hs : rotated j (selector (r := r) h) i <;> simp [splice, patch, rotated] at hs ⊢ <;>
      simp [hs]
  rw [he]
  exact exact_transport hh j U V D hD

private theorem coordinate_degree (m : ℕ) (f : BooleanFunction m) : isDegFn m m f = true := by
  induction m with
  | zero =>
    exact isDegFn_zero_iff.mpr fun z => congrArg f (Subsingleton.elim z (zeroVec 0))
  | succ m ih =>
    exact Bool.and_eq_true_iff.mpr ⟨isDegFn_mono (Nat.le_succ _) (ih _), ih _⟩

def assignment (b : Bool) (x : BitString r) (a : Bool) (y : BitString s) :
    BitString (Arity r s) := Fin.cons b (Fin.append x (Fin.cons a y))

private theorem at_coordinate (U : Labels r s)
    (b : Bool) (x : BitString r) (a : Bool) (y : BitString s) :
    JuntaRadius.viewed (Arity r s) (diagonal U) (assignment b x a y) =
      ((U b).1 x ^^ (((U b).2.1 && a) ^^ dot (U b).2.2 y)) := by
  change diagonal U (BitString.equivFin _ (assignment b x a y)) = _
  simp only [diagonal, joinBlocks, MCSP.truthTable_apply, Equiv.symm_apply_apply,
    assignment, Fin.tail_cons, Fin.cons_zero]
  exact AffineProbes.tagged_at (U b) x a y

private theorem degree_diagonal (hr : 1 ≤ r) (U : Labels r s) :
    isDegFn (r+1) (Arity r s) (JuntaRadius.viewed _ (diagonal U)) = true := by
  let g (b : Bool) : BooleanFunction (r+(s+1)) := fun z =>
    (U b).1 (z ∘ Fin.castAdd (s+1)) ^^
      dot (AffineProbes.phaseVector (r := r) (U b).2.1 (U b).2.2) z
  have hg (b : Bool) : isDegFn r (r+(s+1)) (g b) = true := by
    have hPrefix : isDegFn r (r+(s+1)) (fun z => (U b).1 (z ∘ Fin.castAdd (s+1))) = true :=
      isDegFn_comp_affine (coordinate_degree r (U b).1) (fun i => isDegFn_one_coord _ _)
    exact isDegFn_xor hPrefix (isDegFn_mono hr (isDegFn_one_dot _ _))
  have he (b : Bool) : (fun z => JuntaRadius.viewed (Arity r s) (diagonal U) (Fin.cons b z)) =
      g b := by
    funext z
    change diagonal U (BitString.equivFin _ (Fin.cons b z)) = g b z
    simp [g, diagonal, joinBlocks, AffineProbes.taggedProbe, AffineProbes.mask, ParityProbes.translate,
      probe, MCSP.truthTable_apply]
  change (isDegFn (r+1) (r+(s+1)) (fun z =>
      JuntaRadius.viewed _ (diagonal U) (Fin.cons false z)) &&
    isDegFn r (r+(s+1)) (fun z => JuntaRadius.viewed _ (diagonal U) (Fin.cons false z) ^^
      JuntaRadius.viewed _ (diagonal U) (Fin.cons true z))) = true
  rw [he false]
  refine Bool.and_eq_true_iff.mpr ⟨isDegFn_mono (Nat.le_succ _) (hg false), ?_⟩
  have hDiff : (fun z => JuntaRadius.viewed (Arity r s) (diagonal U) (Fin.cons false z) ^^
      JuntaRadius.viewed (Arity r s) (diagonal U) (Fin.cons true z)) =
      fun z => g false z ^^ g true z :=
    funext fun z => by rw [congrFun (he false) z, congrFun (he true) z]
  rw [hDiff]
  exact isDegFn_xor (hg false) (hg true)

private theorem view_rotated (j : Fin (m+1)) (T : BitString (2 ^ (m+1))) :
    JuntaRadius.viewed _ (rotated j T) =
      fun z => JuntaRadius.viewed _ T (z ∘ blockSwap j) := by
  funext z
  change T (tablePerm (blockSwap j) (BitString.equivFin _ z)) = _
  rw [tablePerm_at_assignment]
  rfl

private theorem rotated_involutive (j : Fin (m+1)) (T : BitString (2 ^ (m+1))) :
    rotated j (rotated j T) = T := by
  apply (MCSP.truthTable (m+1)).symm.injective
  change JuntaRadius.viewed _ (rotated j (rotated j T)) = JuntaRadius.viewed _ T
  rw [view_rotated, view_rotated]
  exact funext fun z => congrArg (JuntaRadius.viewed _ T) (funext fun i => by
    simp [Function.comp_apply, blockSwap, Equiv.swap_apply_self])

theorem degree_rotated (hr : 1 ≤ r) (j : Fin (Arity r s)) (U : Labels r s) :
    isDegFn (r+1) (Arity r s) (JuntaRadius.viewed _ (rotated j (diagonal U))) = true := by
  rw [view_rotated]
  exact isDegFn_comp_affine (degree_diagonal hr U) (fun _ => isDegFn_one_coord _ _)

/-- Recover the fixed-coordinate model using one read for each prefix value
and first differences for the split and suffix parity coefficients. -/
def recoverLabels (F : BooleanFunction (Arity r s)) : Labels r s := fun b =>
  (fun x => F (assignment b x false (zeroVec s)),
   F (assignment b (zeroVec r) true (zeroVec s)) ^^
     F (assignment b (zeroVec r) false (zeroVec s)),
   fun i => F (assignment b (zeroVec r) false (fun k => decide (k = i))) ^^
     F (assignment b (zeroVec r) false (zeroVec s)))

private theorem cancel_sample (x y : Bool) : ((x ^^ y) ^^ x) = y := by
  cases x <;> cases y <;> rfl

theorem recover_diagonal (U : Labels r s) :
    recoverLabels (JuntaRadius.viewed _ (diagonal U)) = U := by
  funext b
  apply Prod.ext
  · funext x
    change JuntaRadius.viewed _ (diagonal U) (assignment b x false (zeroVec s)) = _
    simp [at_coordinate, dot_zero_right]
  · apply Prod.ext
    · change (JuntaRadius.viewed _ (diagonal U) (assignment b (zeroVec r) true (zeroVec s)) ^^
        JuntaRadius.viewed _ (diagonal U) (assignment b (zeroVec r) false (zeroVec s))) = _
      simp only [at_coordinate, dot_zero_right, Bool.and_true, Bool.and_false,
        Bool.xor_false, cancel_sample]
    · funext i
      change (JuntaRadius.viewed _ (diagonal U)
          (assignment b (zeroVec r) false (fun k => decide (k = i))) ^^
        JuntaRadius.viewed _ (diagonal U) (assignment b (zeroVec r) false (zeroVec s))) = _
      have hBasis (a : BitString s) : dot a (fun k => decide (k = i)) = a i := by
        rw [show dot a (fun k => decide (k = i)) = dot (fun k => decide (k = i)) a by
          simp only [AffineProbes.dot_eq_sum, Bool.and_comm]]
        exact dot_basisVec i a
      simp only [at_coordinate, dot_zero_right, hBasis, Bool.and_false, Bool.false_xor,
        Bool.xor_false, cancel_sample]

def fit (j : Fin (Arity r s)) (F : BooleanFunction (Arity r s)) : BooleanFunction (Arity r s) :=
  JuntaRadius.viewed _ (rotated j (diagonal (recoverLabels (fun z => F (z ∘ blockSwap j)))))

theorem fit_rotated (j : Fin (Arity r s)) (U : Labels r s) :
    fit j (JuntaRadius.viewed _ (rotated j (diagonal U))) =
      JuntaRadius.viewed _ (rotated j (diagonal U)) := by
  unfold fit
  rw [← view_rotated, rotated_involutive, recover_diagonal]

def predicted (d : ℕ) (a : BitString m) (T : BitString (2^m)) : BooleanFunction m :=
  fun z => extend d m (fun y => JuntaRadius.viewed m T (bitXor y a)) (bitXor z a)

private theorem xor_affine (a : BitString m) : IsAffineMap (fun z => bitXor z a) :=
  fun i => isDegFn_xor (isDegFn_one_coord m i) (isDegFn_const 1 m (a i))

theorem degree_predicted (d : ℕ) (a : BitString m) (T : BitString (2^m)) :
    isDegFn d m (predicted d a T) = true := by
  unfold predicted
  exact isDegFn_comp_affine (degree_extend _ _ _) (xor_affine a)

theorem predicted_of_clean {d : ℕ} {a : BitString m} {F : BooleanFunction m}
    (hF : isDegFn d m F = true) {D : Finset (Fin (2^m))}
    (hClean : Disjoint (D.map (BitString.equivFin m).symm.toEmbedding) (shifted (sample d m) a)) :
    predicted d a (patch D (MCSP.truthTable m F)) = F := by
  have hEq : extend d m (fun y => JuntaRadius.viewed m (patch D (MCSP.truthTable m F)) (bitXor y a)) =
      fun y => F (bitXor y a) := by
    rw [← extend_eq_of_degree _ _ (isDegFn_comp_affine hF (xor_affine a))]
    apply extend_congr
    intro z hz
    have hAway : BitString.equivFin m (bitXor z a) ∉ D := fun hh =>
      Finset.disjoint_left.mp hClean (Finset.mem_map.mpr ⟨_,hh,Equiv.symm_apply_apply _ _⟩)
        (Finset.mem_image_of_mem _ hz)
    change patch D (MCSP.truthTable m F) (BitString.equivFin m (bitXor z a)) = _
    simp [patch, hAway, MCSP.truthTable_apply]
  funext z
  simp [predicted, hEq, bitXor_cancel_self_right]

noncomputable def belongs (F : BooleanFunction (Arity r s)) : Bool :=
  decide (∃ j : Fin (Arity r s), ∀ z ∈ sample (r+1) (Arity r s), F z = fit j F z)

noncomputable def attempt (a : BitString (Arity r s)) (T : BitString (2 ^ Arity r s)) : Bool :=
  let F := predicted (r+1) a T
  belongs (r := r) (s := s) F && decide (JuntaRadius.distance (JuntaRadius.viewed _ T) F ≤ 4)

noncomputable def control (C : Finset (BitString (Arity r s))) (T : BitString (2 ^ Arity r s)) : Bool :=
  decide (∃ a ∈ C, attempt (r := r) (s := s) a T = true)

theorem control_witness (hr : 1 ≤ r) {C : Finset (BitString (Arity r s))}
    {T : BitString (2 ^ Arity r s)} (hYes : control (r := r) (s := s) C T = true) :
    ∃ (j : Fin (Arity r s)) (U : Labels r s) (D : Finset (Fin (2 ^ Arity r s))),
      D.card ≤ 4 ∧ T = patch D (rotated j (diagonal U)) := by
  obtain ⟨a, _, ha⟩ := of_decide_eq_true hYes
  obtain ⟨hModel, hDist⟩ := Bool.and_eq_true_iff.mp ha
  let F := predicted (r+1) a T
  obtain ⟨j, hj⟩ := of_decide_eq_true hModel
  let U := recoverLabels (r := r) (s := s) (fun z => F (z ∘ blockSwap j))
  have hF : F = JuntaRadius.viewed _ (rotated j (diagonal U)) :=
    eq_of_sample _ _ (degree_predicted _ _ _) (degree_rotated hr j U) hj
  let D := (Finset.univ : Finset (Fin (2 ^ Arity r s))).filter fun i =>
    T i ≠ (MCSP.truthTable _ F) i
  have hD : D.card ≤ 4 := by
    have hd : JuntaRadius.distance (JuntaRadius.viewed _ T) F ≤ 4 := of_decide_eq_true hDist
    rwa [JuntaRadius.distance_eq_raw] at hd
  have hT : T = patch D (MCSP.truthTable _ F) := by
    funext i
    simp only [patch, D, Finset.mem_filter, Finset.mem_univ, true_and]
    have hbit (a b : Bool) : a = (b ^^ decide (a ≠ b)) := by cases a <;> cases b <;> decide
    exact hbit _ _
  refine ⟨j,U,D,hD,?_⟩
  calc
    T = patch D (MCSP.truthTable _ F) := hT
    _ = patch D (rotated j (diagonal U)) := by
      rw [hF]
      simp only [JuntaRadius.viewed, Equiv.apply_symm_apply]

theorem control_sound (hr : 1 ≤ r) {h : BooleanFunction s} (hh : Tests (r := r) h)
    {C : Finset (BitString (Arity r s))} {T : BitString (2 ^ Arity r s)}
    (hYes : control (r := r) (s := s) C T = true) : mcspSquare (Arity r s) T = true := by
  obtain ⟨j,U,D,hD,rfl⟩ := control_witness hr hYes
  have he : mixed h U U = diagonal U := by rw [mixed_eq_splice, splice_self]
  rw [← he]
  exact (exact_transport hh j U U D hD).mpr rfl

theorem control_accepts (hr : 1 ≤ r) {C : Finset (BitString (Arity r s))}
    (hC : 5 ≤ C.card) (hSep : Separated (sample (r+1) (Arity r s)) C)
    (j : Fin (Arity r s)) (U : Labels r s) (D : Finset (Fin (2 ^ Arity r s)))
    (hD : D.card ≤ 4) :
    control (r := r) (s := s) C (patch D (rotated j (diagonal U))) = true := by
  let F := JuntaRadius.viewed _ (rotated j (diagonal U))
  let E := D.map (BitString.equivFin (Arity r s)).symm.toEmbedding
  have hSize : E.card < C.card := by rw [Finset.card_map]; omega
  obtain ⟨a, ha, hClean⟩ := exists_clean hSep hSize
  have he : (MCSP.truthTable _ F) = rotated j (diagonal U) := Equiv.apply_symm_apply _ _
  have hPred := predicted_of_clean (degree_rotated hr j U) hClean
  rw [he] at hPred
  apply decide_eq_true
  refine ⟨a, ha, ?_⟩
  unfold attempt
  rw [hPred, Bool.and_eq_true]
  constructor
  · exact decide_eq_true ⟨j, fun z _ => congrFun (fit_rotated j U).symm z⟩
  · have hd := (JuntaRadius.patch_distance_le D F).trans hD
    rw [he] at hd
    exact decide_eq_true hd

theorem control_iff (hr : 1 ≤ r) {C : Finset (BitString (Arity r s))}
    (hC : 5 ≤ C.card) (hSep : Separated (sample (r+1) (Arity r s)) C)
    (T : BitString (2 ^ Arity r s)) :
    control (r := r) (s := s) C T = true ↔
      ∃ (j : Fin (Arity r s)) (U : Labels r s) (D : Finset (Fin (2 ^ Arity r s))),
        D.card ≤ 4 ∧ T = patch D (rotated j (diagonal U)) := by
  refine ⟨control_witness hr, ?_⟩
  rintro ⟨j,U,D,hD,rfl⟩
  exact control_accepts hr hC hSep j U D hD

theorem control_passes (hr : 1 ≤ r) {h : BooleanFunction s} (hh : Tests (r := r) h)
    {C : Finset (BitString (Arity r s))}
    (hC : 5 ≤ C.card) (hSep : Separated (sample (r+1) (Arity r s)) C)
    (j : Fin (Arity r s)) (U V : Labels r s) (D : Finset (Fin (2 ^ Arity r s)))
    (hD : D.card ≤ 4) :
    control (r := r) (s := s) C (patch D (rotated j (mixed h U V))) = true ↔ U = V := by
  constructor
  · intro hYes
    exact (exact_transport hh j U V D hD).mp (control_sound hr hh hYes)
  · rintro rfl
    rw [mixed_eq_splice, splice_self]
    exact control_accepts hr hC hSep j U D hD

section Size

variable {n : ℕ} {S : Set (BooleanFunction n)}

private theorem assignment_surjective (z : BitString (Arity r s)) :
    ∃ b x a y, assignment (r := r) (s := s) b x a y = z := by
  obtain ⟨⟨x,a,y⟩, h⟩ := (positionEquiv r s).surjective (BitString.equivFin _ (Fin.tail z))
  have hTail : Fin.append x (Fin.cons a y) = Fin.tail z := (BitString.equivFin _).injective h
  exact ⟨z 0,x,a,y, by rw [assignment, hTail, Fin.cons_self_tail]⟩

/-- At one specified address a fitted model only needs first differences and
an XOR of at most s of the suffix coefficients. -/
private theorem synth_fit (w : BitString (Arity r s) → BooleanFunction n) (hw : ∀ z, w z ∈ S)
    (j : Fin (Arity r s)) (z : BitString (Arity r s)) :
    Synthesis interpretation S {fun T => fit j (fun y => w y T) z} (8*s+13) := by
  obtain ⟨b,x,a,y,he⟩ := assignment_surjective (z ∘ blockSwap j)
  let W (v : BitString (Arity r s)) := w (v ∘ blockSwap j)
  let orig := W (assignment b (zeroVec r) false (zeroVec s))
  let f0 := W (assignment b x false (zeroVec s))
  let phase (i : Fin s) (T : BitString n) :=
    W (assignment b (zeroVec r) false (fun k => decide (k = i))) T ^^ orig T
  let split (T : BitString n) := ((W (assignment b (zeroVec r) true (zeroVec s)) T ^^ orig T) && a)
  have hRead (v : BitString (Arity r s)) : Synthesis interpretation S {W v} 0 :=
    Synthesis.of_mem (hw _)
  have hP (i : Fin s) : Synthesis interpretation S {phase i} 4 :=
    (hRead _).xor (hRead _)
  have hSplit : Synthesis interpretation S {split} 4 := by
    cases a
    · exact (Synthesis.of_forall_eq_const false (f := split) (fun T => Bool.and_false _)).mono
        Set.Subset.rfl Set.Subset.rfl (by decide)
    · have hh := (hRead (assignment b (zeroVec r) true (zeroVec s))).xor
        (hRead (assignment b (zeroVec r) false (zeroVec s)))
      simpa only [split, orig, Bool.and_true] using hh
  let live := (Finset.univ : Finset (Fin s)).filter (fun i => y i = true)
  let sum (T : BitString n) := ∑ i ∈ live, phase i T
  have hSum : Synthesis interpretation S {sum} (8*s+1) := by
    apply (Synthesis.sum live phase (fun _ => 4) (fun i _ => hP i)).mono
      Set.Subset.rfl Set.Subset.rfl
    have hc : live.card ≤ s := by simpa using Finset.card_le_univ live
    simp only [Finset.sum_const, smul_eq_mul]
    omega
  have hOut := (hRead (assignment b x false (zeroVec s))).xor (hSplit.xor hSum)
  have hFn : (fun T => f0 T ^^ (split T ^^ sum T)) = fun T => fit j (fun y => w y T) z := by
    funext T
    change _ = (JuntaRadius.viewed _ (rotated j
      (diagonal (recoverLabels (r := r) (s := s) (fun v => W v T))))) z
    rw [view_rotated]
    change _ = JuntaRadius.viewed _ (diagonal (recoverLabels (fun v => W v T))) (z ∘ blockSwap j)
    rw [← he, at_coordinate]
    have hDot := AffineProbes.dot_eq_sum (fun i => phase i T) y
    simp only [sum, live, Finset.sum_filter]
    have hTerm (i : Fin s) : (if y i = true then phase i T else 0) = (phase i T && y i) := by
      cases y i <;> cases phase i T <;> rfl
    simp only [hTerm, ← hDot]
    rfl
  rw [← hFn]
  exact hOut.mono Set.Subset.rfl Set.Subset.rfl (by omega)

private theorem synth_belongs (w : BitString (Arity r s) → BooleanFunction n)
    (hw : ∀ z, w z ∈ S) :
    Synthesis interpretation S {fun T => belongs (r := r) (s := s) (fun z => w z T)}
      (Arity r s * ((sample (r+1) (Arity r s)).card * (8*s+19) + 2) + 1) := by
  let B := sample (r+1) (Arity r s)
  let eqTest (j : Fin (Arity r s)) (z : BitString (Arity r s)) (T : BitString n) :=
    decide (w z T = fit j (fun y => w y T) z)
  have hTerm (j : Fin (Arity r s)) (z : BitString (Arity r s)) :
      Synthesis interpretation S {eqTest j z} (8*s+18) := by
    have hh := ((Synthesis.of_mem (hw z)).xor (synth_fit w hw j z)).not
    refine (Synthesis.congr_iff hh (g := eqTest j z) (fun T => ?_)).mono
      Set.Subset.rfl Set.Subset.rfl (by omega)
    dsimp [eqTest]
    cases w z T <;> cases fit j (fun y => w y T) z <;> decide
  let ok (j : Fin (Arity r s)) (T : BitString n) := decide (∀ z ∈ B, eqTest j z T = true)
  have hok (j : Fin (Arity r s)) :
      Synthesis interpretation S {ok j} (B.card * (8*s+19) + 1) := by
    have hh := Synthesis.forall_mem B (eqTest j) (fun _ => 8*s+18) (fun z _ => hTerm j z)
    have hEq := Synthesis.congr_iff hh (g := ok j) (fun T => by simp [ok])
    simpa only [Finset.sum_const, smul_eq_mul, show 8*s+18+1 = 8*s+19 by omega] using hEq
  have hAny := Synthesis.exists_mem Finset.univ ok (fun _ => B.card*(8*s+19)+1) (fun j _ => hok j)
  have hOut := Synthesis.congr_iff hAny (g := fun T =>
    belongs (r := r) (s := s) (fun z => w z T)) (fun T => by
      simp [ok, eqTest, belongs, B])
  simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.add_assoc] using hOut

private theorem synth_distance {m : ℕ} (w : BitString m → BooleanFunction (2^m))
    {S : Set (BooleanFunction (2^m))} (hin : inputs (2^m) ⊆ S) (hw : ∀ z, w z ∈ S) :
    Synthesis interpretation S
      {fun T => decide (JuntaRadius.distance (JuntaRadius.viewed m T) (fun z => w z T) ≤ 4)}
      (16*2^m+3) := by
  let diff (i : Fin (2^m)) (T : BitString (2^m)) := T i ^^ w ((BitString.equivFin m).symm i) T
  let B := S ∪ Set.range diff
  have hAll : Synthesis interpretation S (Set.range diff) (4*2^m) := by
    have hf (i : Fin (2^m)) : Synthesis interpretation S {diff i} 4 :=
      (Synthesis.of_mem (hin ⟨i,rfl⟩)).xor (Synthesis.of_mem (hw _))
    simpa only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin, Nat.mul_comm] using
      Synthesis.family diff (fun _ => 4) hf
  have hCount := RadiusControl.synth_counter B diff (fun i => Or.inr ⟨i,rfl⟩)
  have hOut : Synthesis interpretation (B ∪ Set.range (RadiusControl.counterState diff))
      {fun T => !RadiusControl.counterState diff 5 T} 1 :=
    (Synthesis.of_mem (Or.inr ⟨5,rfl⟩)).not
  have hBoth := hAll.trans (hCount.trans hOut)
  refine (Synthesis.congr_iff hBoth (fun T => ?_)).mono Set.Subset.rfl Set.Subset.rfl (by omega)
  rw [JuntaRadius.distance_eq_raw]
  have hWt : InvariantControl.weight (fun i => diff i T) =
      ((Finset.univ : Finset (Fin (2^m))).filter
        (fun i => T i ≠ MCSP.truthTable m (fun z => w z T) i)).card := by
    rfl
  simp only [RadiusControl.counterState, hWt, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]
  omega

def sampleBudget (r s : ℕ) : ℕ :=
  Arity r s * ((sample (r+1) (Arity r s)).card * (8*s+19) + 2) + 1

theorem synth_attempt (a : BitString (Arity r s)) :
    Synthesis interpretation (inputs (2 ^ Arity r s)) {attempt (r := r) (s := s) a}
      ((8*(r+1)+16)*2^(Arity r s)+sampleBudget r s+4) := by
  let m := Arity r s
  let w (z : BitString m) (T : BitString (2^m)) := predicted (r+1) a T z
  let S := inputs (2^m) ∪ Set.range w
  have hPredict : Synthesis interpretation (inputs (2^m)) (Set.range w) (8*(r+1)*2^m) := by
    have hE := extend_synthesis (r+1) m (S := inputs (2^m))
      (fun y T => T (BitString.equivFin m (bitXor y a))) (fun y => ⟨_,rfl⟩)
    apply hE.mono Set.Subset.rfl ?_ le_rfl
    rintro _ ⟨z,rfl⟩
    exact ⟨bitXor z a,rfl⟩
  have hModel := synth_belongs w (S := S) (fun z => Or.inr ⟨z,rfl⟩)
  have hDist := synth_distance w (S := S) (fun _ => Or.inl) (fun z => Or.inr ⟨z,rfl⟩)
  have hAll := hPredict.trans (hModel.and hDist)
  apply hAll.mono Set.Subset.rfl Set.Subset.rfl
  change 8*(r+1)*2^m + (sampleBudget r s + (16*2^m+3)+1) ≤
    (8*(r+1)+16)*2^m+sampleBudget r s+4
  rw [Nat.add_mul]
  omega

theorem control_size (C : Finset (BitString (Arity r s))) :
    complexity interpretation (single (control (r := r) (s := s) C)) ≤
      C.card * ((8*(r+1)+16)*2^(Arity r s)+sampleBudget r s+5) + 1 := by
  have h := Synthesis.exists_mem C (attempt (r := r) (s := s))
    (fun _ => (8*(r+1)+16)*2^(Arity r s)+sampleBudget r s+4) (fun a _ => synth_attempt a)
  have hOut := Synthesis.congr_iff h (g := control (r := r) (s := s) C)
    (fun T => by simp [control])
  simpa only [Finset.sum_const, smul_eq_mul, Nat.add_assoc] using hOut.complexity_le

end Size

section Schedule

abbrev logArity (r : ℕ) := Arity r (2^r)

private theorem schedule_margin (r : ℕ) (hr : 10 ≤ r) : 4*(r+3)^2 ≤ 2^r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    have hSq : (r+1+3)^2 ≤ 2*(r+3)^2 := by nlinarith
    calc
      _ ≤ 4*(2*(r+3)^2) := Nat.mul_le_mul_left _ hSq
      _ = 2*(4*(r+3)^2) := by ring
      _ ≤ 2*2^r := Nat.mul_le_mul_left _ ih
      _ = 2^(r+1) := by rw [pow_succ, Nat.mul_comm]

private theorem schedule_base (r : ℕ) (hr : 10 ≤ r) : logArity r+1 ≤ 2^(r+1) := by
  have hMargin := schedule_margin r hr
  have hPow : r+3 ≤ 4*(r+3)^2 := by nlinarith
  change r+(2^r+1)+1+1 ≤ 2^(r+1)
  rw [pow_succ]
  omega

private theorem center_room (r : ℕ) (hr : 10 ≤ r) :
    4*((sample (r+1) (logArity r)).card * (sample (r+1) (logArity r)).card) < 2^logArity r := by
  let B := (sample (r+1) (logArity r)).card
  have hB : B ≤ 2^((r+1)*(r+1)) := by
    rw [pow_mul]
    exact (card_sample_le _ _).trans (Nat.pow_le_pow_left (schedule_base r hr) _)
  have hExp : 2+((r+1)*(r+1)+(r+1)*(r+1)) < logArity r := by
    have hMargin := schedule_margin r hr
    change _ < r+(2^r+1)+1
    nlinarith
  calc
    4*(B*B) ≤ 4*(2^((r+1)*(r+1))*2^((r+1)*(r+1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hB hB)
    _ = 2^(2+((r+1)*(r+1)+(r+1)*(r+1))) := by rw [pow_add, pow_add 2 ((r+1)*(r+1))]; rfl
    _ < 2^logArity r := Nat.pow_lt_pow_right (by decide) hExp

private theorem sample_budget_le (r : ℕ) (hr : 10 ≤ r) :
    sampleBudget r (2^r) ≤ 2^logArity r := by
  let m := logArity r
  let b := m+1
  let a := b^(r+1)
  have ha : 1 ≤ a := Nat.pow_pos (by dsimp [b]; omega)
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hA : (sample (r+1) m).card ≤ a := card_sample_le _ _
  have hCoeff : 8*2^r+19 ≤ 20*b := by dsimp [b, m, logArity, Arity]; omega
  have hRoom : 5+(r+1)*(r+3) ≤ m := by
    have hMargin := schedule_margin r hr
    dsimp [m, logArity, Arity]
    nlinarith
  change m*((sample (r+1) m).card*(8*2^r+19)+2)+1 ≤ 2^m
  calc
    _ ≤ m*(a*(20*b)+2)+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul hA hCoeff) 2)) 1
    _ ≤ b*(a*(22*b))+1 := by
      have hab : 1 ≤ a*b := Nat.mul_pos (by omega) (by omega)
      have hInner : a*(20*b)+2 ≤ a*(22*b) := by nlinarith
      exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.le_succ m) hInner) 1
    _ ≤ 32*b^(r+3) := by
      rw [show r+3 = (r+1)+2 by omega, pow_add]
      change b*(a*(22*b))+1 ≤ 32*(a*b^2)
      have hP : 1 ≤ a*b^2 := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
      have he : b*(a*(22*b)) = 22*(a*b^2) := by ring
      omega
    _ ≤ 32*(2^(r+1))^(r+3) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (schedule_base r hr) _)
    _ = 2^(5+(r+1)*(r+3)) := by rw [← pow_mul, pow_add]; rfl
    _ ≤ 2^m := Nat.pow_le_pow_right (by decide) hRoom

theorem schedule_centers (r : ℕ) (hr : 10 ≤ r) :
    ∃ C : Finset (BitString (logArity r)), C.card = 5 ∧ Separated (sample (r+1) (logArity r)) C :=
  exists_separated _ (sample_nonempty _ _) (center_room r hr)

noncomputable def logControl (r : ℕ) (hr : 10 ≤ r) : BooleanFunction (2^logArity r) :=
  control (r := r) (s := 2^r) (schedule_centers r hr).choose

theorem log_control_passes (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : Tests (r := r) h) (j : Fin (logArity r)) (U V : Labels r (2^r))
    (D : Finset (Fin (2^logArity r))) (hD : D.card ≤ 4) :
    logControl r hr (patch D (rotated j (mixed h U V))) = true ↔ U = V := by
  obtain ⟨hc,hSep⟩ := (schedule_centers r hr).choose_spec
  exact control_passes (by omega) hh hc.ge hSep j U V D hD

theorem log_control_sound (r : ℕ) (hr : 10 ≤ r) {T : BitString (2^logArity r)}
    (hYes : logControl r hr T = true) : mcspSquare (logArity r) T = true := by
  obtain ⟨h,hh⟩ := JointEquality.log_stage r hr
  exact control_sound (by omega) hh hYes

theorem log_control_sparse (r : ℕ) (hr : 10 ≤ r) :
    (acceptingTables (logControl r hr)).card ≤ 2 ^ descriptionBitBound (logArity r) := by
  apply (Finset.card_le_card ?_).trans (card_accepting_mcspSquare_le _)
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    log_control_sound r hr (Finset.mem_filter.mp hT).2⟩

theorem log_control_size (r : ℕ) (hr : 10 ≤ r) :
    complexity interpretation (single (logControl r hr)) ≤ 160*(r+1)*2^logArity r := by
  let N := 2^logArity r
  have hN : 1 ≤ N := Nat.two_pow_pos _
  have hs := control_size (r := r) (s := 2^r) (schedule_centers r hr).choose
  rw [(schedule_centers r hr).choose_spec.1] at hs
  have hB := sample_budget_le r hr
  change _ ≤ 5*((8*(r+1)+16)*N+sampleBudget r (2^r)+5)+1 at hs
  change complexity interpretation (single (logControl r hr)) ≤ _ at hs
  refine hs.trans ?_
  change _ ≤ 160*(r+1)*N
  change sampleBudget r (2^r) ≤ N at hB
  calc
    _ = 40*(r+1)*N+80*N+5*sampleBudget r (2^r)+26 := by ring
    _ ≤ 40*(r+1)*N+111*N := by omega
    _ = (40*(r+1)+111)*N := by rw [Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right N (by omega)

theorem log_control_sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (logControl r hr)) ≤ logArity r * 2^logArity r := by
  have hf := Nat.eventually_mul_add_one_pow_le_pow_div (160*K) 1 1
    (by decide : 1 < (2 : ℕ)) (by decide)
  filter_upwards [hf] with r he hr
  have hPoly : 160*K*(r+1) ≤ 2^r := by simpa using he
  have hm : 2^r ≤ logArity r := by dsimp [logArity, Arity]; omega
  calc
    _ ≤ K*(160*(r+1)*2^logArity r) := Nat.mul_le_mul_left _ (log_control_size r hr)
    _ = (160*K*(r+1))*2^logArity r := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (hPoly.trans hm)

end Schedule

#print axioms exact_transport
#print axioms crossing_width
#print axioms control_iff
#print axioms log_control_passes
#print axioms log_control_sound
#print axioms log_control_sparse
#print axioms log_control_size
#print axioms log_control_sub_nlogn

end PvsNP.Frontier.JointOrbit
