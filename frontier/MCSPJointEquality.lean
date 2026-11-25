module

public import MCSPAffineProbes

/-! A simultaneous equality test on two disjoint blocks of one truth table. -/

@[expose] public section

namespace PvsNP.Frontier.JointEquality

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CommunicationCut PatchedCut

variable {m r s : ℕ}

/-- The extra represented variable names the block. -/
def blockIndex (b : Bool) (i : Fin (2 ^ m)) : Fin (2 ^ (m+1)) :=
  BitString.equivFin _ (Fin.cons b ((BitString.equivFin m).symm i))

private theorem blockIndex_injective (b : Bool) : Function.Injective (blockIndex (m := m) b) := by
  intro i j hij
  have h := (BitString.equivFin (m+1)).injective hij
  exact (BitString.equivFin m).symm.injective (by simpa using congrArg Fin.tail h)

def readBlock (b : Bool) (T : BitString (2 ^ (m+1))) : BitString (2 ^ m) :=
  T ∘ blockIndex b

def joinBlocks (T : Bool → BitString (2 ^ m)) : BitString (2 ^ (m+1)) :=
  MCSP.truthTable _ (fun z => T (z 0) (BitString.equivFin m (Fin.tail z)))

@[simp] theorem read_join (b : Bool) (T : Bool → BitString (2 ^ m)) :
    readBlock b (joinBlocks T) = T b := by
  funext i
  simp [readBlock, joinBlocks, blockIndex, MCSP.truthTable_apply]

private theorem join_read (T : BitString (2 ^ (m+1))) :
    joinBlocks (fun b => readBlock b T) = T := by
  funext i
  simp only [joinBlocks, MCSP.truthTable_apply, readBlock, Function.comp_apply, blockIndex,
    Equiv.symm_apply_apply, Fin.cons_self_tail, Equiv.apply_symm_apply]

def blockPatch (b : Bool) (D : Finset (Fin (2 ^ (m+1)))) : Finset (Fin (2 ^ m)) :=
  Finset.univ.filter (fun i => blockIndex b i ∈ D)

theorem card_blockPatch_le (b : Bool) (D : Finset (Fin (2 ^ (m+1)))) :
    (blockPatch b D).card ≤ D.card := by
  apply Finset.card_le_card_of_injOn (blockIndex b) _ (blockIndex_injective b).injOn
  intro i hi
  exact (Finset.mem_filter.mp hi).2

@[simp] theorem read_patch (b : Bool) (D : Finset (Fin (2 ^ (m+1))))
    (T : BitString (2 ^ (m+1))) :
    readBlock b (patch D T) = patch (blockPatch b D) (readBlock b T) := by
  funext i
  simp [readBlock, blockPatch, patch]

private theorem rewire_size {n k : ℕ} (f : BooleanFunction n) (select : Fin n → Fin k) :
    complexity interpretation (single (fun x => f (x ∘ select))) ≤
      complexity interpretation (single f) := by
  obtain ⟨c, hc, hs⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := single f)
  let lifted := c.comp (Circuit.wiring signature select)
  have hCompute : lifted.Computes interpretation (single (fun x => f (x ∘ select))) := by
    intro x
    rw [show lifted.eval interpretation x = c.eval interpretation (x ∘ select) by
      simp [lifted, Circuit.eval_comp, Circuit.eval_wiring]]
    exact hc (x ∘ select)
  have hSize : lifted.size = c.size := by simp [lifted, Circuit.size_comp]
  exact (complexity_le_of_computes lifted hCompute).trans_eq (hSize.trans hs)

private theorem mux_cost (f g : BooleanFunction m) :
    complexity interpretation (single (fun z : BitString (m+1) =>
      if z 0 then g (Fin.tail z) else f (Fin.tail z))) ≤
      complexity interpretation (single f) + complexity interpretation (single g) + 4 := by
  let b : BooleanFunction (m+1) := fun z => z 0
  let l : BooleanFunction (m+1) := fun z => f (Fin.tail z)
  let h : BooleanFunction (m+1) := fun z => g (Fin.tail z)
  let neg : BooleanFunction (m+1) := fun z => !b z
  let lo : BooleanFunction (m+1) := fun z => neg z && l z
  let hi : BooleanFunction (m+1) := fun z => b z && h z
  let out : BooleanFunction (m+1) := fun z => lo z || hi z
  have hb : complexity interpretation (single b) = 0 := complexity_single_proj 0
  have hn : complexity interpretation (single neg) ≤ 1 := by
    simpa only [hb, Nat.zero_add] using complexity_not_le b
  have hl : complexity interpretation (single l) ≤ complexity interpretation (single f) :=
    rewire_size f Fin.succ
  have hh : complexity interpretation (single h) ≤ complexity interpretation (single g) :=
    rewire_size g Fin.succ
  have hLeft : complexity interpretation (single lo) ≤
      complexity interpretation (single neg) + complexity interpretation (single l) + 1 :=
    complexity_and_le neg l
  have hRight : complexity interpretation (single hi) ≤
      complexity interpretation (single h) + 1 := by
    simpa only [hb, Nat.zero_add] using complexity_and_le b h
  have hOut : complexity interpretation (single out) ≤
      complexity interpretation (single lo) + complexity interpretation (single hi) + 1 :=
    complexity_or_le lo hi
  have he : (fun z : BitString (m+1) => if z 0 then g (Fin.tail z) else f (Fin.tail z)) =
      out := by
    funext z
    cases hz : z 0 <;> simp [b, l, h, neg, lo, hi, out, hz]
  rw [he]
  omega

/-- Run the existing sparse affine recognizer on each block, then AND the answers. -/
noncomputable def control (r m : ℕ) (hm : r+4 ≤ m) (T : BitString (2 ^ (m+1))) : Bool :=
  AffineProbes.control r m hm (readBlock false T) &&
  AffineProbes.control r m hm (readBlock true T)

theorem control_exact (hm : r+4 ≤ m) (hr : 10 ≤ r) (h2 : 2^r ≤ m)
    {T : BitString (2 ^ (m+1))} (h : control r m hm T = true) :
    mcspSquare (m+1) T = true := by
  obtain ⟨h0, h1⟩ := Bool.and_eq_true_iff.mp h
  let f := (MCSP.truthTable m).symm (readBlock false T)
  let g := (MCSP.truthTable m).symm (readBlock true T)
  have hEval : (MCSP.truthTable (m+1)).symm T =
      fun z => if z 0 then g (Fin.tail z) else f (Fin.tail z) := by
    funext z
    rw [← join_read T, joinBlocks, Equiv.symm_apply_apply]
    cases hz : z 0 <;> rfl
  have hLo := AffineProbes.control_certificate_cost hm h0
  have hHi := AffineProbes.control_certificate_cost hm h1
  change complexity interpretation (single f) ≤ _ at hLo
  change complexity interpretation (single g) ≤ _ at hHi
  have hBig := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans h2
  change 1024 ≤ m at hBig
  have hBudget := Nat.mul_le_mul_right (m+1) (by omega : 48 ≤ m+1)
  rw [← pow_two] at hBudget
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, hEval]
  exact (mux_cost f g).trans (by omega)

theorem control_size (hm : r+4 ≤ m) :
    complexity interpretation (single (control r m hm)) ≤
      2 * complexity interpretation (single (AffineProbes.control r m hm)) + 1 := by
  let f := AffineProbes.control r m hm
  have hlo := rewire_size f (blockIndex false)
  have hhi := rewire_size f (blockIndex true)
  have hAnd := complexity_and_le (fun T => f (readBlock false T)) (fun T => f (readBlock true T))
  exact hAnd.trans (by simpa [readBlock, two_mul, Nat.add_assoc] using (Nat.add_le_add_right
    (Nat.add_le_add hlo hhi) 1))

theorem control_sparse (hm : r+4 ≤ m) (hr : 10 ≤ r) (h2 : 2^r ≤ m) :
    (acceptingTables (control r m hm)).card ≤ 2 ^ descriptionBitBound (m+1) := by
  apply (Finset.card_le_card ?_).trans (card_accepting_mcspSquare_le (m+1))
  intro T hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    control_exact hm hr h2 (Finset.mem_filter.mp hT).2⟩

abbrev Labels (r s : ℕ) := Bool → AffineProbes.Tagged r s

def diagonal (U : Labels r s) : BitString (2 ^ ((r+(s+1))+1)) :=
  joinBlocks (fun b => AffineProbes.taggedProbe (U b))

def selector (h : BooleanFunction s) : BitString (2 ^ ((r+(s+1))+1)) :=
  joinBlocks (fun _ => CommunicationCut.mask r h)

def mixed (h : BooleanFunction s) (U V : Labels r s) : BitString (2 ^ ((r+(s+1))+1)) :=
  joinBlocks (fun b => AffineProbes.taggedMixed h (U b) (V b))

def Tests (h : BooleanFunction s) : Prop :=
  ∀ U V : Labels r s, ∀ D : Finset (Fin (2 ^ ((r+(s+1))+1))), D.card ≤ 4 →
    (mcspSquare ((r+(s+1))+1) (patch D (mixed h U V)) = true ↔ U = V)

private theorem mixed_eq_splice (h : BooleanFunction s) (U V : Labels r s) :
    mixed h U V = splice (selector h) (diagonal U) (diagonal V) := by
  funext i
  simp [mixed, selector, diagonal, AffineProbes.taggedMixed, joinBlocks, MCSP.truthTable_apply, splice]
  rfl

private theorem card_labels (r s : ℕ) :
    Fintype.card (Labels r s) = 2 ^ (2 * (2^r+(s+1))) := by
  rw [Fintype.card_fun, Fintype.card_bool, AffineProbes.tagged_card, ← pow_mul, Nat.mul_comm]

private theorem control_accepts_diagonal (hm : r+4 ≤ r+(s+1)) (h15 : 15 ≤ r+(s+1))
    (U : Labels r s) (D : Finset (Fin (2 ^ ((r+(s+1))+1)))) (hD : D.card ≤ 4) :
    control r (r+(s+1)) hm (patch D (diagonal U)) = true := by
  have hBlock (b : Bool) : AffineProbes.control r (r+(s+1)) hm
      (patch (blockPatch b D) (AffineProbes.taggedProbe (U b))) = true := by
    have hid : PermutedCut.tablePerm (Equiv.refl (Fin (r+(s+1)))) = Equiv.refl _ := by
      ext i
      simp [PermutedCut.tablePerm, PermutedCut.permuteAssignment]
    have h := AffineProbes.control_passes_tag_diag hm h15 (Equiv.refl _) (U b) (blockPatch b D)
      ((card_blockPatch_le b D).trans hD)
    rwa [hid] at h
  simp [control, diagonal, hBlock]

/-- The same selector works for both disjoint blocks, even with independent
affine tags and four arbitrary flips of the combined table. -/
theorem exists_selector (r t : ℕ) (hr : 10 ≤ r) (ht : 2^r ≤ t+1) :
    ∃ h : BooleanFunction (t+1), Tests (r := r) h := by
  let m := r+(t+2)
  let p := 2*(2^r+(t+2))
  have hBig : 1024 ≤ t+1 :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans ht
  have hm : r+4 ≤ m := by dsimp [m]; omega
  have hm2 : 2^r ≤ m := by dsimp [m]; omega
  have hm15 : 15 ≤ m := by dsimp [m]; omega
  have hCard (k : ℕ) : Fintype.card (BooleanFunction k) = 2 ^ 2 ^ k := by simp
  have room : 2 ^ (p+p+((m+1)+1)*4+descriptionBitBound (m+1)+2^t) <
      Fintype.card (BooleanFunction (t+1)) := by
    rw [hCard, pow_succ 2 t]
    apply Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
    have hWide := GrowingPrefix.wide_exponent_le hr (show 2^r ≤ t+2 by omega)
    have hCube : 100*(t+2)^3 ≤ 800*t^3 := by
      calc
        _ ≤ 100*(2*t)^3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ = _ := by ring
    have hLinear : t ≤ t^3 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 1 ≤ 3)
    have hPoly : p+p+((m+1)+1)*4+descriptionBitBound (m+1) ≤ 816*t^3 := by
      dsimp [p, m]
      change 2^r+2^r+(((r+(t+2))+1)+1)*4+descriptionBitBound ((r+(t+2))+1) ≤ _ at hWide
      omega
    have hLt : 816*t^3 < t^4 := by
      rw [pow_succ' t 3]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pow_pos (by omega : 0 < t))
    have hExp := GrowingPrefix.four_power_le_exp t (by omega)
    omega
  refine exists_family_selector_with_aux (mcspSquare (m+1)) (mixed (r := r) (s := t+1))
    (card_labels r (t+1)) (q := m+1) le_rfl (card_accepting_mcspSquare_le _) (hCard t).le room ?_ ?_
  · intro h U D hD
    have hDiag : mixed h U U = diagonal U := by rw [mixed_eq_splice, splice_self]
    rw [hDiag]
    exact control_exact hm hr hm2 (control_accepts_diagonal hm hm15 U D hD)
  · intro U V hne
    obtain ⟨b, hb⟩ : ∃ b, U b ≠ V b := by
      by_contra! h
      exact hne (funext h)
    obtain ⟨aux, hAux⟩ := AffineProbes.tagged_mixed_with_aux hb
    refine ⟨aux, fun h g he => hAux ?_⟩
    have hMix := congrArg (readBlock b) (congrArg Prod.fst he)
    simp only [mixed, read_join] at hMix
    have hAuxEq : aux h = aux g := congrArg Prod.snd he
    exact Prod.ext hMix hAuxEq

theorem control_passes (hm : r+4 ≤ r+(s+1)) (hr : 10 ≤ r) (h2 : 2^r ≤ r+(s+1))
    {h : BooleanFunction s} (hh : Tests (r := r) h) (U V : Labels r s)
    (D : Finset (Fin (2 ^ ((r+(s+1))+1)))) (hD : D.card ≤ 4) :
    control r (r+(s+1)) hm (patch D (mixed h U V)) = true ↔ U = V := by
  constructor
  · intro hYes
    exact (hh U V D hD).mp (control_exact hm hr h2 hYes)
  · rintro rfl
    rw [mixed_eq_splice, splice_self]
    have hBig := (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr).trans h2
    exact control_accepts_diagonal hm (by omega) U D hD

/-- The two independent labels double the number of distinct source wires
required on this single cut. This counts both raw inputs and gate outputs. -/
theorem crossing_width {h : BooleanFunction s} (hh : Tests (r := r) h)
    (D : Finset (Fin (2 ^ ((r+(s+1))+1)))) (hD : D.card ≤ 4)
    (c : Circuit signature (2 ^ ((r+(s+1))+1)) 1)
    (hc : c.Computes interpretation (single (mcspSquare ((r+(s+1))+1))))
    (owner : Wire (2 ^ ((r+(s+1))+1)) c.size → Bool)
    (hOwner : ∀ i, owner (.input i) = selector (r := r) h i) :
    2*(2^r+(s+1)) ≤ (crossingWires c.program owner).card := by
  apply crossingWires_lower_bound_of_family_equality (card_labels r s) (selector h)
    (fun U => patch D (diagonal U)) _ ?_ c hc owner hOwner
  intro U V
  have he : splice (selector h) (patch D (diagonal U)) (patch D (diagonal V)) =
      patch D (mixed h U V) := by
    funext i
    rw [mixed_eq_splice]
    cases hs : selector (r := r) h i <;> simp [splice, patch, hs]
  rw [he]
  exact hh U V D hD

/-- The width bound alone allows a placement whose crossings are all raw inputs. -/
theorem raw_crossing_placement (h : BooleanFunction s)
    (c : Circuit signature (2 ^ ((r+(s+1))+1)) 1) :
    ∃ owner : Wire (2 ^ ((r+(s+1))+1)) c.size → Bool,
      (∀ i, owner (.input i) = selector (r := r) h i) ∧
      ∀ k, Wire.gate k ∉ crossingWires c.program owner := by
  let owner : Wire (2 ^ ((r+(s+1))+1)) c.size → Bool
    | .input i => selector h i
    | .gate _ => false
  refine ⟨owner, fun _ => rfl, fun k hk => ?_⟩
  obtain ⟨j, _, _, hne⟩ := (Finset.mem_filter.mp hk).2
  exact hne (show owner (.gate k) = owner (.gate j) from rfl)

theorem log_stage (r : ℕ) (hr : 10 ≤ r) :
    ∃ h : BooleanFunction (2^r), Tests (r := r) h := by
  let t := 2^r-1
  have ht : t+1 = 2^r := by dsimp [t]; have := Nat.two_pow_pos r; omega
  rw [← ht]
  exact exists_selector r t hr ht.ge

private def parityLabels (r s : ℕ) : Labels r s := fun b =>
  (SuperTwoN.dot (fun _ => b), b, fun _ => b)

private theorem diagonal_parityLabels (r s : ℕ) :
    diagonal (parityLabels r s) =
      MCSP.truthTable _ AffineProbes.gatedParity := by
  have hTag (b : Bool) : AffineProbes.taggedProbe (parityLabels r s b) =
      MCSP.truthTable (r+(s+1)) (fun z => b && SuperTwoN.dot (fun _ => true) z) := by
    funext i
    obtain ⟨⟨x, a, y⟩, rfl⟩ := (positionEquiv r s).surjective i
    change AffineProbes.taggedProbe (parityLabels r s b) (position x a y) = _
    rw [AffineProbes.tagged_at, MCSP.truthTable_apply]
    change (SuperTwoN.dot (fun _ : Fin r => b) x ^^
      ((b && a) ^^ SuperTwoN.dot (fun _ : Fin s => b) y)) =
      (b && SuperTwoN.dot (fun _ => true)
        ((BitString.equivFin _).symm (BitString.equivFin _ (Fin.append x (Fin.cons a y)))))
    rw [Equiv.symm_apply_apply]
    cases b
    · have hx := QuadraticForest.dot_zero_left x
      have hy := QuadraticForest.dot_zero_left y
      change SuperTwoN.dot (fun _ : Fin r => false) x = false at hx
      change SuperTwoN.dot (fun _ : Fin s => false) y = false at hy
      simp [hx, hy]
    · simp only [Bool.true_and, AffineProbes.dot_eq_sum]
      rw [Fin.sum_univ_add, Fin.sum_univ_succ]
      simp only [Fin.append_left, Fin.append_right, Fin.cons_zero, Fin.cons_succ, Bool.add_eq_xor]
  funext i
  simp only [diagonal, joinBlocks, MCSP.truthTable_apply]
  rw [hTag, MCSP.truthTable_apply, Equiv.symm_apply_apply]
  rfl

/-- Two different affine phases produce a diagonal rejected by the original
global affine control, for every placement of the four flips. -/
theorem original_control_fails (r : ℕ) (hr : 10 ≤ r) (h : BooleanFunction (2^r))
    (D : Finset (Fin (2 ^ (LogPrefixControl.arity r+1)))) (hD : D.card ≤ 4) :
    ∃ U : Labels r (2^r),
      mcspSquare (LogPrefixControl.arity r+1) (patch D (mixed h U U)) = true ∧
      AffineProbes.control r (LogPrefixControl.arity r+1)
        ((LogPrefixControl.arity_room r hr).trans (Nat.le_succ _))
        (patch D (mixed h U U)) = false := by
  let m := LogPrefixControl.arity r
  have hBig : 1024 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  have hMargin : r < 2^r := Nat.lt_two_pow_self
  have hWidth : 2*r < m := by dsimp [m, LogPrefixControl.arity]; omega
  have hm : 1024 ≤ m := hBig.trans (LogPrefixControl.arity_pow_le r)
  have hRoom : 8*(m+2) < 2^m := by
    have hSq : m ≤ m^3 := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < m) (by decide : 1 ≤ 3)
    have hMul := Nat.mul_le_mul_right (m^3) (by omega : 16 ≤ m)
    rw [show m * m^3 = m^4 by ring] at hMul
    exact (show 8*(m+2) < m^4 by omega).trans_le
      (GrowingPrefix.four_power_le_exp m (by omega))
  refine ⟨parityLabels r (2^r), ?_⟩
  rw [mixed_eq_splice, splice_self, diagonal_parityLabels]
  exact ⟨AffineProbes.gatedParity_patched_exact (by omega : 32 ≤ m+1) D hD,
    AffineProbes.gatedParity_rejects_control _ hWidth hRoom D hD⟩

theorem control_sub_nlogn (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ hr : 10 ≤ r,
      K * complexity interpretation (single (control r (LogPrefixControl.arity r)
        (LogPrefixControl.arity_room r hr))) ≤
          (LogPrefixControl.arity r + 1) * 2 ^ (LogPrefixControl.arity r + 1) := by
  filter_upwards [AffineProbes.affine_control_sub_nlogn (2*K), Filter.eventually_ge_atTop K] with
    r hSmall hrK hr
  let m := LogPrefixControl.arity r
  let hm := LogPrefixControl.arity_room r hr
  let base := complexity interpretation (single (AffineProbes.control r m hm))
  let full := complexity interpretation (single (control r m hm))
  have hOld : (2*K) * base ≤ m * 2^m := hSmall hr
  have hSize : full ≤ 2*base+1 := control_size hm
  have hK : K ≤ 2^m := hrK.trans ((Nat.le_add_right r (2^r+1)).trans m.lt_two_pow_self.le)
  change K * full ≤ (m+1)*2^(m+1)
  calc
    _ ≤ K*(2*base+1) := Nat.mul_le_mul_left K hSize
    _ = (2*K)*base+K := by ring
    _ ≤ m*2^m+K := Nat.add_le_add_right hOld K
    _ ≤ (m+1)*2^m := by rw [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ (m+1)*(2^m*2) := Nat.mul_le_mul_left _ (by omega)
    _ = (m+1)*2^(m+1) := by rw [pow_succ]

#print axioms log_stage
#print axioms crossing_width
#print axioms raw_crossing_placement
#print axioms original_control_fails
#print axioms control_sparse
#print axioms control_passes
#print axioms control_sub_nlogn

end PvsNP.Frontier.JointEquality
