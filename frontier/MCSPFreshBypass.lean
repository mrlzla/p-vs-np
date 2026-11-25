module

public import MCSPMinimumAliasControl

/-! Unconditional fresh bypass matching for absorbed joint stop readers,
a binate full-support lower bound, and a minimum two-corner control where
an escaping unhit forest root hides a bypass outside `StopGate`. -/

@[expose] public section

namespace PvsNP.Frontier.FreshBypass

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates TwoCornerStructure MonotoneForest SuperTwoN
open ForestPinning RestrictionCharges FreshCharges PairSeparation StopMatching
open MinimumAliases MinimumAliasControl

variable {n k l g : ℕ}

/-! ### Part A: Unconditional No-Alias Global Fresh Bypass Theorem -/

private theorem projection_inj {i j : Fin k} (h : projection i = projection j) : i = j := by
  have hh := congrFun h (fun t => decide (t = i))
  simpa [projection, eq_comm] using hh

private theorem not_essential_const (f : BooleanFunction n) (b : Bool)
    (hf : f = fun _ => b) (j : Fin n) : ¬ EssentialAt f j := by
  rintro ⟨x, y, _, hn⟩
  exact hn (by simp [hf])

private theorem not_essential_projection_of_ne (i j : Fin n) (hne : i ≠ j) :
    ¬ EssentialAt (projection i) j := by
  rintro ⟨x, y, ha, hn⟩
  exact hn (ha i hne)

private theorem essential_argument' (p : Program signature n g) (ρ : Fin n → Fin l ⊕ Bool)
    (j : Fin g) (i : Fin l) (he : EssentialAt (restrictedWire p ρ (.gate j)) i) :
    ∃ a : Fin (signature.Arity (p.lines j).op),
      EssentialAt (restrictedWire p ρ ((p.lines j).wires a)) i := by
  classical
  obtain ⟨x, y, hx, hn⟩ := he
  by_contra! h
  apply hn
  unfold restrictedWire
  rw [p.trace_gate, p.trace_gate]
  congr 1
  funext a
  by_contra hne
  exact h a ⟨x, y, hx, hne⟩

/-- Keep one representative per distinct witness, with the witness map
injective on the chosen representatives. -/
private theorem representatives' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : T → β) :
    ∃ M ⊆ T, M.card = (T.attach.image f).card ∧
      ∃ rep : M → T, (∀ j, (rep j).val = j.val) ∧ Function.Injective (f ∘ rep) := by
  classical
  let R := T.attach.image f
  have hPre (b : R) : ∃ j : T, f j = b.val := by
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp b.property
    exact ⟨j, hj⟩
  let pick (b : R) := (hPre b).choose
  have hp (b : R) : f (pick b) = b.val := (hPre b).choose_spec
  let raw (b : R) := (pick b).val
  have hRaw : Function.Injective raw := by
    intro u v h
    apply Subtype.ext
    rw [← hp u, ← hp v, show pick u = pick v from Subtype.ext h]
  let M := R.attach.image raw
  have hSub : M ⊆ T := by
    intro i hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hi
    exact (pick b).property
  have hCard : M.card = R.card := by
    simp [M, Finset.card_image_of_injective _ hRaw]
  let rep (j : M) : T := ⟨j.val, hSub j.property⟩
  refine ⟨M, hSub, hCard, rep, fun _ => rfl, ?_⟩
  intro i j hij
  obtain ⟨u, _, hu⟩ := Finset.mem_image.mp i.property
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp j.property
  have hu' : pick u = rep i := Subtype.ext hu
  have hv' : pick v = rep j := Subtype.ext hv
  have huv : u = v := Subtype.ext (by simpa only [Function.comp_apply, hp, ← hu', ← hv'] using hij)
  exact Subtype.ext (hu.symm.trans (huv ▸ hv))

/-- Unconditional global fresh bypass theorem: if after `pinAt x P`, branching `i ↦ v`
makes gate `k` insensitive to `j` while `root` remains sensitive to `j`, and `root` does not
already restrict to `projection j` under `pinAt x P`, then some fresh gate `u ≠ k` reads a
wire that restricts to `projection j` under `pinAt x P`. No minimality or `StopGate`
assumption is required. -/
theorem fresh_bypass_of_absorbed_joint {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} {i j : Fin n} (hi : i ∉ P) (hj : j ∉ P)
    (v : Bool) (k : Fin g)
    (hSkip : ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.gate k)) j)
    (hEss : EssentialAt (restrictedWire p (branchPin x P i v) root) j)
    (hRootNotProj : restrictedWire p (pinAt x P) root ≠ projection j) :
    ∃ u ∈ fresh p (pinAt x P), u ≠ k ∧
      ∃ a, restrictedWire p (pinAt x P) ((p.lines u).wires a) = projection j := by
  classical
  by_contra hNo
  push Not at hNo
  have hGateNotEss : ∀ m : ℕ, ∀ u : Fin g, u.val ≤ m →
      restrictedWire p (pinAt x P) (.gate u) ≠ projection j →
      ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.gate u)) j := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro u huLe huNotProj huEss
      by_cases huk : u = k
      · subst huk; exact hSkip huEss
      · by_cases huFresh : u ∈ fresh p (pinAt x P)
        · obtain ⟨a, haEss⟩ := essential_argument' p (branchPin x P i v) u j huEss
          cases hWire : (p.lines u).wires a with
          | input r =>
            by_cases hrj : r = j
            · subst hrj
              have hEqProj : restrictedWire p (pinAt x P) ((p.lines u).wires a) = projection r := by
                rw [hWire]
                funext z
                change substitute (pinAt x P) z r = z r
                simp [substitute, pinAt, hj]
              exact hNo u huFresh huk a hEqProj
            · have hNotEssR : ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.input r)) j := by
                by_cases hri : r = i
                · subst hri
                  apply not_essential_const _ v
                  funext z
                  change substitute (branchPin x P r v) z r = v
                  simp [substitute, branchPin, pinAt]
                · by_cases hrP : r ∈ P
                  · apply not_essential_const _ (x r)
                    funext z
                    change substitute (branchPin x P i v) z r = x r
                    simp [substitute, branchPin, pinAt, hri, hrP]
                  · have hEqR : restrictedWire p (branchPin x P i v) (.input r) = projection r := by
                      funext z
                      change substitute (branchPin x P i v) z r = z r
                      simp [substitute, branchPin, pinAt, hri, hrP]
                    rw [hEqR]
                    exact not_essential_projection_of_ne r j hrj
              rw [hWire] at haEss
              exact hNotEssR haEss
          | gate t =>
            have htLt := p.lt_of_lines_wires_eq_gate u a t hWire
            have htNotProj : restrictedWire p (pinAt x P) (.gate t) ≠ projection j := by
              intro htEq
              exact hNo u huFresh huk a (hWire ▸ htEq)
            rw [hWire] at haEss
            exact ih t.val (by omega) t le_rfl htNotProj haEss
        · have huDisc : disclosed p (pinAt x P) u := by
            by_contra hNotDisc
            exact huFresh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNotDisc⟩)
          rcases huDisc with ⟨b, hb⟩ | ⟨r, hr⟩ | ⟨t, htLt, htEq⟩
          · have hConstB : restrictedWire p (branchPin x P i v) (.gate u) = fun _ => b := by
              rw [branchPin_compose x P i v hi, restrictedWire_compose, hb]
            exact not_essential_const _ b hConstB j huEss
          · have hrj : r ≠ j := fun hEq => huNotProj (hr.trans (congrArg projection hEq))
            by_cases hri : r = i
            · subst hri
              have hConstV : restrictedWire p (branchPin x P r v) (.gate u) = fun _ => v := by
                rw [branchPin_compose x P r v hi, restrictedWire_compose, hr]
                funext z
                change substitute (pinAt (Function.update x r v) {r}) z r = v
                simp [substitute, pinAt]
              exact not_essential_const _ v hConstV j huEss
            · have hProjR : restrictedWire p (branchPin x P i v) (.gate u) = projection r := by
                rw [branchPin_compose x P i v hi, restrictedWire_compose, hr]
                funext z
                change substitute (pinAt (Function.update x i v) {i}) z r = z r
                simp [substitute, pinAt, hri]
              rw [hProjR] at huEss
              exact not_essential_projection_of_ne r j hrj huEss
          · have htNotProj : restrictedWire p (pinAt x P) (.gate t) ≠ projection j :=
              fun htP => huNotProj (htEq.trans htP)
            have hBranchEq : restrictedWire p (branchPin x P i v) (.gate u) =
                restrictedWire p (branchPin x P i v) (.gate t) := by
              rw [branchPin_compose x P i v hi, restrictedWire_compose,
                restrictedWire_compose, htEq]
            rw [hBranchEq] at huEss
            exact ih t.val (by omega) t le_rfl htNotProj huEss
  cases hRoot : root with
  | input r =>
    rw [hRoot] at hEss hRootNotProj
    by_cases hrj : r = j
    · subst hrj
      apply hRootNotProj
      funext z
      change substitute (pinAt x P) z r = z r
      simp [substitute, pinAt, hj]
    · by_cases hri : r = i
      · subst hri
        apply not_essential_const _ v _ j hEss
        funext z
        change substitute (branchPin x P r v) z r = v
        simp [substitute, branchPin, pinAt]
      · by_cases hrP : r ∈ P
        · apply not_essential_const _ (x r) _ j hEss
          funext z
          change substitute (branchPin x P i v) z r = x r
          simp [substitute, branchPin, pinAt, hri, hrP]
        · have hEqR : restrictedWire p (branchPin x P i v) (.input r) = projection r := by
            funext z
            change substitute (branchPin x P i v) z r = z r
            simp [substitute, branchPin, pinAt, hri, hrP]
          rw [hEqR] at hEss
          exact not_essential_projection_of_ne r j hrj hEss
  | gate k0 =>
    rw [hRoot] at hEss hRootNotProj
    exact hGateNotEss k0.val k0 le_rfl hRootNotProj hEss

/-- Monotonicity of `nextFreshLoss` under enlarging the target pin set. -/
theorem nextFreshLoss_mono_targets (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) {J Q : Finset (Fin n)} (h : J ⊆ Q) :
    nextFreshLoss p (pinAt x P) (pinAt x J) ⊆ nextFreshLoss p (pinAt x P) (pinAt x Q) := by
  have hCompose : compose (pinAt x J) (pinAt x Q) = pinAt x Q := by
    funext i
    by_cases hi : i ∈ J
    · simp [compose, pinAt, hi, h hi]
    · simp [compose, pinAt, hi]
  have hFresh := fresh_nested p (compose (pinAt x P) (pinAt x J)) (pinAt x Q)
  rw [AdaptivePinning.compose_assoc, hCompose] at hFresh
  intro k hk
  obtain ⟨hBefore, hAfter⟩ := Finset.mem_sdiff.mp hk
  exact Finset.mem_sdiff.mpr ⟨hBefore, fun hQ => hAfter (hFresh hQ)⟩

private noncomputable def projInputs (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) (u : Fin g) : Finset (Fin n) := open scoped Classical in
  Finset.univ.filter fun j : Fin n =>
    ∃ a, restrictedWire p (pinAt x P) ((p.lines u).wires a) = projection j

private theorem projInputs_card_le (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) (u : Fin g) : (projInputs p x P u).card ≤ 2 := by
  classical
  let into (j : projInputs p x P u) : Fin (signature.Arity (p.lines u).op) :=
    ((Finset.mem_filter.mp j.property).2).choose
  have hInj : Function.Injective into := by
    intro j1 j2 he
    have hj1 := ((Finset.mem_filter.mp j1.property).2).choose_spec
    have hj2 := ((Finset.mem_filter.mp j2.property).2).choose_spec
    change restrictedWire p (pinAt x P) ((p.lines u).wires (into j1)) = projection j1.val at hj1
    change restrictedWire p (pinAt x P) ((p.lines u).wires (into j2)) = projection j2.val at hj2
    rw [he, hj2] at hj1
    exact Subtype.ext (projection_inj hj1.symm)
  have hCard := Fintype.card_le_of_injective into hInj
  have hFan := Program.fanInAtMost_iff.mp p.fanInAtMost_two u
  simp only [Fintype.card_coe, Fintype.card_fin] at hCard
  exact hCard.trans hFan

private theorem projInputs_union_card_le (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) (R : Finset (Fin g)) :
    (R.biUnion (projInputs p x P)).card ≤ 2 * R.card := by
  classical
  calc
    (R.biUnion (projInputs p x P)).card ≤ ∑ u ∈ R, (projInputs p x P u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ R, 2 := Finset.sum_le_sum fun u _ => projInputs_card_le p x P u
    _ = 2 * R.card := by simp [Nat.mul_comm]

private theorem two_reads_disjoint_mem {p : Program signature n g} {u : Fin g}
    (hOp : (p.lines u).op = .and ∨ (p.lines u).op = .or)
    {i1 i2 : Fin n} (hne : i1 ≠ i2) (h1 : Reads p u i1) (h2 : Reads p u i2)
    (a : Fin (signature.Arity (p.lines u).op)) :
    (p.lines u).wires a = .input i1 ∨ (p.lines u).wires a = .input i2 := by
  obtain ⟨a1, ha1⟩ := h1
  obtain ⟨a2, ha2⟩ := h2
  have haNe : a1 ≠ a2 := fun he => hne (by
    have hEq := ha1.symm.trans ((congrArg (p.lines u).wires he).trans ha2)
    injection hEq)
  have hAr : signature.Arity (p.lines u).op = 2 := by
    rcases hOp with h | h <;> rw [h]
  have hFin2 : a = a1 ∨ a = a2 := by
    have haLt : a.val < 2 := hAr ▸ a.isLt
    have h1Lt : a1.val < 2 := hAr ▸ a1.isLt
    have h2Lt : a2.val < 2 := hAr ▸ a2.isLt
    have hNeVal : a1.val ≠ a2.val := fun he => haNe (Fin.ext he)
    by_cases hEq1 : a.val = a1.val
    · left; exact Fin.ext hEq1
    · right; exact Fin.ext (by omega)
  rcases hFin2 with rfl | rfl
  · exact Or.inl ha1
  · exact Or.inr ha2

private theorem reads_of_eq {p : Program signature n g} {u v : Fin g} (h : u = v)
    {i : Fin n} (hv : Reads p v i) : Reads p u i := by
  subst h
  exact hv

private theorem wire_eq_proj_of_eq {p : Program signature n g} {ρ : Fin n → Fin n ⊕ Bool}
    {u v : Fin g} (h : u = v) {q : Fin n}
    (hv : ∃ a, restrictedWire p ρ ((p.lines v).wires a) = projection q) :
    ∃ a, restrictedWire p ρ ((p.lines u).wires a) = projection q := by
  subst h
  exact hv

/-- Unconditional fresh-gate matching without `StopGate`, `IsForestMask`, or minimality:
every certified target loses a distinct fresh joint gate and (outside `E`) half as many
distinct fresh bypass gates, all inside `nextFreshLoss p (pinAt x P) (pinAt x J)`. -/
theorem match_fresh_oriented_readers {p : Program signature n g} {root : Wire n g}
    {x : BitString n} {P : Finset (Fin n)} (anchor : Fin n → Fin n) (J E : Finset (Fin n))
    (hJ : ∀ j ∈ J, j ∉ P)
    (hAnchor : ∀ j ∈ J, anchor j ∉ P ∧ anchor j ∉ J)
    (hNotProj : ∀ j ∈ J \ E, restrictedWire p (pinAt x P) root ≠ projection j)
    (hSep : ∀ j ∈ J \ E, ∀ v : Bool,
      EssentialAt (restrictedWire p (branchPin x P (anchor j) v) root) j)
    (hJoint : ∀ j ∈ J, ∃ k ∈ fresh p (pinAt x P),
      ((p.lines k).op = .and ∨ (p.lines k).op = .or) ∧ Reads p k (anchor j) ∧ Reads p k j) :
    ∃ (M : Finset (Fin n)) (joint : J → Fin g) (bypass : M → Fin g),
      M ⊆ J \ E ∧ (J \ E).card ≤ 2 * M.card ∧
      Function.Injective joint ∧ Function.Injective bypass ∧
      (∀ j t, joint j ≠ bypass t) ∧
      (∀ j, joint j ∈ nextFreshLoss p (pinAt x P) (pinAt x J)) ∧
      (∀ t, bypass t ∈ nextFreshLoss p (pinAt x P) (pinAt x J)) ∧
      J.card + M.card ≤ (nextFreshLoss p (pinAt x P) (pinAt x J)).card := by
  classical
  let C := J \ E
  have hJi {j l : Fin n} (hj : j ∈ J) (hl : l ∈ J) : anchor j ≠ l :=
    fun h => (hAnchor j hj).2 (h.symm ▸ hl)
  let joint (j : J) := (hJoint j.val j.property).choose
  have hJointSpec (j : J) := (hJoint j.val j.property).choose_spec
  have hJointInj : Function.Injective joint := by
    intro j l hEq
    apply Subtype.ext
    obtain ⟨_, hOpJ, hReadAJ, hReadJJ⟩ := hJointSpec j
    obtain ⟨_, _, _, hReadLL⟩ := hJointSpec l
    obtain ⟨a, ha'⟩ := reads_of_eq hEq hReadLL
    rcases two_reads_disjoint_mem hOpJ (hJi j.property j.property) hReadAJ hReadJJ a with hA | hJVal
    · exfalso
      have hEqIn : (.input (anchor j.val) : Wire n g) = .input l.val := hA.symm.trans ha'
      injection hEqIn with hName
      exact hJi j.property l.property hName
    · have hEqIn : (.input j.val : Wire n g) = .input l.val := hJVal.symm.trans ha'
      injection hEqIn
  have hBypass (q : C) : ∃ u ∈ fresh p (pinAt x P),
      u ≠ joint ⟨q.val, (Finset.mem_sdiff.mp q.property).1⟩ ∧
      ∃ a, restrictedWire p (pinAt x P) ((p.lines u).wires a) = projection q.val := by
    let jp : J := ⟨q.val, (Finset.mem_sdiff.mp q.property).1⟩
    let k := joint jp
    let i := anchor jp.val
    have hi : i ∉ P := (hAnchor jp.val jp.property).1
    have hj : jp.val ∉ P := hJ jp.val jp.property
    have hOp : ∃ v : Bool, ((p.lines k).op = .and ∧ v = false) ∨
        ((p.lines k).op = .or ∧ v = true) := by
      rcases (hJointSpec jp).2.1 with ha | ho
      · exact ⟨false, Or.inl ⟨ha, rfl⟩⟩
      · exact ⟨true, Or.inr ⟨ho, rfl⟩⟩
    obtain ⟨v, hv⟩ := hOp
    have hConst := branch_absorbs_gate p x P i v k hv (hJointSpec jp).2.2.1
    have hSkip : ¬ EssentialAt (restrictedWire p (branchPin x P i v) (.gate k)) jp.val := by
      rw [hConst]
      rintro ⟨_, _, _, hn⟩
      exact hn rfl
    exact fresh_bypass_of_absorbed_joint hi hj v k hSkip (hSep q.val q.property v)
      (hNotProj q.val q.property)
  let backup (q : C) := (hBypass q).choose
  have hBackup (q : C) := (hBypass q).choose_spec
  let R := C.attach.image backup
  have hCover : C ⊆ R.biUnion (projInputs p x P) := by
    intro q hq
    let qc : C := ⟨q, hq⟩
    exact Finset.mem_biUnion.mpr ⟨backup qc,
      Finset.mem_image.mpr ⟨qc, Finset.mem_attach C qc, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hBackup qc).2.2⟩⟩
  have hCapacity := (Finset.card_le_card hCover).trans (projInputs_union_card_le p x P R)
  obtain ⟨M, hM, hMCard, rep, hRep, hInj⟩ := representatives' C backup
  let bypass := backup ∘ rep
  have hJointDisj (l : J) (t : M) : joint l ≠ bypass t := by
    intro hEq
    obtain ⟨_, hOpL, hReadAL, hReadLL⟩ := hJointSpec l
    obtain ⟨a, haProjL⟩ := wire_eq_proj_of_eq hEq (hBackup (rep t)).2.2
    rcases two_reads_disjoint_mem hOpL (hJi l.property l.property) hReadAL hReadLL a with hA | hL
    · rw [hA] at haProjL
      have hALProj : restrictedWire p (pinAt x P) (.input (anchor l.val)) =
          projection (anchor l.val) := by
        funext z
        change substitute (pinAt x P) z (anchor l.val) = z (anchor l.val)
        simp [substitute, pinAt, (hAnchor l.val l.property).1]
      have hName := projection_inj (hALProj.symm.trans haProjL)
      exact (hAnchor l.val l.property).2 (hName ▸ (Finset.mem_sdiff.mp (rep t).property).1)
    · rw [hL] at haProjL
      have hLProj : restrictedWire p (pinAt x P) (.input l.val) = projection l.val := by
        funext z
        change substitute (pinAt x P) z l.val = z l.val
        simp [substitute, pinAt, hJ l.val l.property]
      have hName := projection_inj (hLProj.symm.trans haProjL)
      have hlEq : l = (⟨(rep t).val, (Finset.mem_sdiff.mp (rep t).property).1⟩ : J) :=
        Subtype.ext hName
      exact (hBackup (rep t)).2.1 (hEq.symm.trans (congrArg joint hlEq))
  have hPrimary (j : J) : joint j ∈ nextFreshLoss p (pinAt x P) (pinAt x J) := by
    obtain ⟨hf, _, _, hRead⟩ := hJointSpec j
    exact fresh_reader_loss_of_mem p x P J (hJ j.val j.property) j.property hf hRead
  have hSecondary (t : M) : bypass t ∈ nextFreshLoss p (pinAt x P) (pinAt x J) := by
    have hJt : (rep t).val ∈ J := (Finset.mem_sdiff.mp (rep t).property).1
    obtain ⟨hf, _, a, haProj⟩ := hBackup (rep t)
    have hd := disclosed_of_pinned_projection p (pinAt x P) (pinAt x J)
      (bypass t) a (rep t).val (x (rep t).val) haProj (by simp [pinAt, hJt])
    exact Finset.mem_sdiff.mpr ⟨hf, fun hU => (Finset.mem_filter.mp hU).2 hd⟩
  let A := J.attach.image joint
  let D := M.attach.image bypass
  have hA : A.card = J.card := by
    rw [Finset.card_image_of_injective _ hJointInj, Finset.card_attach]
  have hD : D.card = M.card := by
    rw [Finset.card_image_of_injective _ hInj, Finset.card_attach]
  have hU : A ∪ D ⊆ nextFreshLoss p (pinAt x P) (pinAt x J) := by
    intro u hu
    rcases Finset.mem_union.mp hu with ha | hd
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact hPrimary j
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hd
      exact hSecondary t
  have hDisj : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro u ha hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hd
    exact hJointDisj j t ht.symm
  have hCount := Finset.card_le_card hU
  rw [Finset.card_union_of_disjoint hDisj, hA, hD] at hCount
  exact ⟨M, joint, bypass, hM, hMCard ▸ hCapacity, hJointInj, hInj, hJointDisj,
    hPrimary, hSecondary, hCount⟩

/-- On any circuit computing `mcspSquare m` (`m ≥ 7`), any certified joint fresh reader
family forces both the joint fresh loss and half of the non-exceptional extra fresh losses,
with no `StopGate`, `IsForestMask`, minimality, or early-alias subtraction term `A`. -/
theorem mcsp_affine_fresh_oriented_charge (m : ℕ) (hm : 7 ≤ m)
    (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (a : BitString m) (b : Bool) (P J T : Finset (Fin (2 ^ m)))
    (anchor : Fin (2 ^ m) → Fin (2 ^ m))
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m)
    (hJ : Disjoint J P) (hT : Disjoint T P) (hTJ : Disjoint T J)
    (hAnchor : ∀ j ∈ J, anchor j ∈ T)
    (hJoint : ∀ j ∈ J, ∃ k ∈ fresh c.program (pinAt (MCSP.truthTable m (affine a b)) P),
      ((c.program.lines k).op = .and ∨ (c.program.lines k).op = .or) ∧
      Reads c.program k (anchor j) ∧ Reads c.program k j) :
    let x := MCSP.truthTable m (affine a b)
    J.card + (J.card - 2 * descriptionBitBound m * T.card + 1) / 2 ≤
      (nextFreshLoss c.program (pinAt x P) (pinAt x J)).card := by
  classical
  dsimp only
  let x := MCSP.truthTable m (affine a b)
  have hEx (i : T) :=
    affine_two_bit_separation_except m hm a b P i.val
      (fun h => Finset.disjoint_left.mp hT i.property h) hFree
  let exception (i : Fin (2 ^ m)) : Finset (Fin (2 ^ m)) :=
    if hi : i ∈ T then (hEx ⟨i, hi⟩).choose else ∅
  let E := J.filter fun j => j ∈ exception (anchor j)
  have hEc : E.card ≤ 2 * descriptionBitBound m * T.card := by
    have hSub : E ⊆ T.biUnion exception := by
      intro j hj
      obtain ⟨hjJ, hjE⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_biUnion.mpr ⟨anchor j, hAnchor j hjJ, hjE⟩
    calc
      E.card ≤ (T.biUnion exception).card := Finset.card_le_card hSub
      _ ≤ ∑ i ∈ T, (exception i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ T, 2 * descriptionBitBound m := Finset.sum_le_sum fun i hi => by
        simpa only [exception, hi, dite_true] using (hEx ⟨i, hi⟩).choose_spec.2.1
      _ = 2 * descriptionBitBound m * T.card := by
        simp [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hAnchor' (j : Fin (2 ^ m)) (hj : j ∈ J) : anchor j ∉ P ∧ anchor j ∉ J :=
    ⟨fun h => Finset.disjoint_left.mp hT (hAnchor j hj) h,
      fun h => Finset.disjoint_left.mp hTJ (hAnchor j hj) h⟩
  have hNotProj (j : Fin (2 ^ m)) (hj : j ∈ J \ E) :
      restrictedWire c.program (pinAt x P) (c.outputs 0) ≠ projection j := by
    intro hProj
    have hjJ := (Finset.mem_sdiff.mp hj).1
    have hjP : j ∉ P := fun h => Finset.disjoint_left.mp hJ hjJ h
    obtain ⟨_, z, hAgree, _, hzj, _, hzFalse⟩ :=
      mcspSquare_affine_pin_branches_nonconstant m hm a b P j hjP hFree true
    have hSub : substitute (pinAt x P) z = z := by
      funext u
      by_cases hu : u ∈ P
      · have hx : x u = z u := (hAgree u hu).2.symm
        simp [substitute, pinAt, hu, hx]
      · simp [substitute, pinAt, hu]
    have hEval : restrictedWire c.program (pinAt x P) (c.outputs 0) z =
        mcspSquare m (substitute (pinAt x P) z) := by
      rw [NestedFaces.restricted_circuit_eq c hc (pinAt x P)]
    rw [hProj, hSub] at hEval
    have hProjTrue : projection j z = true := by simpa [projection] using hzj
    rw [hProjTrue, hzFalse] at hEval
    exact Bool.noConfusion hEval
  have hSep (j : Fin (2 ^ m)) (hj : j ∈ J \ E) (v : Bool) :
      EssentialAt (restrictedWire c.program
        (branchPin x P (anchor j) v) (c.outputs 0)) j := by
    obtain ⟨hjJ, hjE⟩ := Finset.mem_sdiff.mp hj
    have hi := hAnchor j hjJ
    have hEdge := (hEx ⟨anchor j, hi⟩).choose_spec.2.2
    have hFreeJ : j ∉ insert (anchor j) P := by
      intro h
      rcases Finset.mem_insert.mp h with he | hp
      · exact (hAnchor' j hjJ).2 (he ▸ hjJ)
      · exact Finset.disjoint_left.mp hJ hjJ hp
    have hNot : j ∉ (hEx ⟨anchor j, hi⟩).choose := by
      intro he
      apply hjE
      refine Finset.mem_filter.mpr ⟨hjJ, ?_⟩
      simpa only [exception, hi, dite_true] using he
    rw [NestedFaces.restricted_circuit_eq c hc]
    exact hEdge j (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hFreeJ⟩, hNot⟩) v
  obtain ⟨M, _, _, _, hCap, _, _, _, _, _, hLoss⟩ :=
    match_fresh_oriented_readers anchor J E (fun j hj hp => Finset.disjoint_left.mp hJ hj hp)
      hAnchor' hNotProj hSep hJoint
  have hBound : J.card ≤ (J \ E).card + E.card := by
    have hSub : J ⊆ (J \ E) ∪ E := by
      intro j hj
      by_cases he : j ∈ E
      · exact Finset.mem_union_right _ he
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hj, he⟩)
    exact (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)
  change J.card + (J.card - 2 * descriptionBitBound m * T.card + 1) / 2 ≤
    (nextFreshLoss c.program (pinAt x P) (pinAt x J)).card
  omega

private theorem aliasControl_trueArgs :
    ∀ z ∈ cornerArguments MinimumAliasControl.program (3 : Fin 4) true,
      z.1 = .gate 3 ∨ ∃ i, z.1 = .input i := by
  decide

private theorem aliasControl_reqCornerF_aux :
    cornerArguments MinimumAliasControl.program (1 : Fin 4) false = {(.input 2, false)} := by
  decide

/-- On `MinimumAliasControl.program`, pinning `P = {1}` to `false` creates an early alias
at gate `0`, yet pinning target `0` to `false` still loses fresh stop gate `1` (`x2 && g0`). -/
theorem alias_control_loses_fresh_reader :
    (⟨1, by decide⟩ : Fin MinimumAliasControl.circuit.size) ∈
      losses MinimumAliasControl.program (.gate 3) (fun _ => false) ({1} : Finset (Fin 4)) {0} := by
  classical
  let p := MinimumAliasControl.program
  let ρ1 : Fin 4 → Fin 4 ⊕ Bool := pinAt (fun _ => false) {1}
  have h0 : cornerValue p false (.gate 3) = true := MinimumAliasControl.corners false
  have h1 : cornerValue p true (.gate 3) = true := MinimumAliasControl.corners true
  have hNeed3 : NeedCorner p (.gate 3) false (.gate 3, cornerValue p false (.gate 3)) := by
    have hVal : cornerValue p false (.gate 3) = true := h0
    rw [hVal]
    exact NeedCorner.output
  have hNeed2 : NeedCorner p (.gate 3) false (.gate 2, true) :=
    NeedCorner.argument hNeed3 (by decide)
  have hVal2 : cornerValue p false (.gate 2) = true := by decide
  have hNeed1 : NeedCorner p (.gate 3) false (.gate 1, false) :=
    NeedCorner.argument (hVal2.symm ▸ hNeed2) (by decide)
  have hNoTrueAux : ∀ key : Wire 4 4 × Bool, NeedCorner p (.gate 3) true key →
      (key.1 = .gate 3 ∨ ∃ i, key.1 = .input i) := by
    intro key hw
    induction hw with
    | output => exact Or.inl rfl
    | argument _ ha ih =>
      rcases ih with hk3 | ⟨i, hEq⟩
      · cases hk3
        exact aliasControl_trueArgs _ ha
      · cases hEq
  have h1NotTrue : ∀ v : Bool, ¬ NeedCorner p (.gate 3) true (.gate 1, v) := by
    intro v hv
    rcases hNoTrueAux (.gate 1, v) hv with hEq | ⟨i, hEq⟩
    · cases hEq
    · cases hEq
  have hVal1 : cornerValue p false (.gate 1) = false := by decide
  have hValSet : valSet p (.gate 3) (1 : Fin 4) = {false} := by
    ext v
    rw [valSet, stateValues, Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and, Need]
    constructor
    · rintro (hf | ht)
      · have hEq := needCorner_eq_cornerValue h0 hf
        simp_all
      · exact (h1NotTrue v ht).elim
    · rintro rfl
      exact Or.inl hNeed1
  have hReqCornerF : reqCorner p (.gate 3) false (1 : Fin 4) = {(.input 2, false)} := by
    unfold reqCorner
    rw [ite_eq_left_iff.mpr (fun h => (h (hVal1.symm ▸ hNeed1)).elim)]
    exact aliasControl_reqCornerF_aux
  have hReqCornerT : reqCorner p (.gate 3) true (1 : Fin 4) = ∅ := by
    unfold reqCorner
    exact ite_eq_right_iff.mpr (fun h => (h1NotTrue _ h).elim)
  have hReq1 : req p (.gate 3) (1 : Fin 4) = {(.input 2, false)} := by
    simp [req, hReqCornerF, hReqCornerT]
  have hBad1 : (1 : Fin 4) ∈ badGates p (.gate 3) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    unfold unused
    rw [hValSet, hReq1]
    decide
  have h1Stop : (1 : Fin 4) ∈ StopGate p (.gate 3) :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ hBad1))))
  have h0Proj : restrictedWire p ρ1 (.gate 0) = projection 0 := by
    funext z
    change (substitute ρ1 z 0 || substitute ρ1 z 1) = z 0
    simp [substitute, ρ1, pinAt]
  have h1Fresh : (1 : Fin 4) ∈ fresh p ρ1 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
    · cases b
      · have hT := congrFun hb (fun j => decide (j = 0 ∨ j = 2))
        revert hT; decide
      · have hF := congrFun hb (fun _ => false)
        revert hF; decide
    · have h12 := congrFun hi (fun j => decide (j = 0 ∨ j = 2))
      have h0Only := congrFun hi (fun j => decide (j = 0))
      have h2Only := congrFun hi (fun j => decide (j = 2))
      fin_cases i <;> revert h12 h0Only h2Only <;> decide
    · have ht0 : t = 0 := Fin.ext (by omega)
      subst ht0
      have hW := congrFun heq (fun j => decide (j = 0))
      revert hW; decide
  have hDisc : disclosed p (compose ρ1 (pinAt (fun _ => false) {0})) (1 : Fin 4) :=
    disclosed_of_pinned_projection p ρ1 (pinAt (fun _ => false) {0}) (1 : Fin 4)
      ⟨1, by decide⟩ 0 false
      (by
        change restrictedWire p ρ1 (.gate 0) = projection 0
        exact h0Proj)
      (by simp [pinAt])
  change (1 : Fin 4) ∈ losses p (.gate 3) (fun _ => false) ({1} : Finset (Fin 4)) {0}
  exact Finset.mem_inter.mpr ⟨h1Stop, Finset.mem_sdiff.mpr ⟨h1Fresh,
    fun hu => (Finset.mem_filter.mp hu).2 hDisc⟩⟩

/-! ### Part B: Binate Full-Support Minimality Lower Bound -/

private inductive Reach (p : Program signature n g) : Wire n g → Wire n g → Prop where
  | refl (w : Wire n g) : Reach p w w
  | step {k : Fin g} (a : Fin (signature.Arity (p.lines k).op)) {w' : Wire n g} :
      Reach p (.gate k) w' → Reach p ((p.lines k).wires a) w'

private theorem reach_trans {p : Program signature n g} {w1 w2 w3 : Wire n g}
    (h12 : Reach p w1 w2) (h23 : Reach p w2 w3) : Reach p w1 w3 := by
  induction h12 with
  | refl => exact h23
  | step a _ ih => exact Reach.step a (ih h23)

private theorem mem_wireSupport_reach (p : Program signature n g) {i : Fin n} :
    ∀ {w : Wire n g}, i ∈ p.wireSupport w → Reach p (.input i) w := by
  intro w
  refine p.wire_induction (P := fun w => i ∈ p.wireSupport w → Reach p (.input i) w) ?_ ?_ w
  · intro r hr
    have hEq : i = r := by simpa using hr
    subst hEq
    exact Reach.refl _
  · intro k ih hk
    change i ∈ p.trace (supportInterpretation signature n) (fun x => {x}) (.gate k) at hk
    rw [p.trace_gate] at hk
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hk
    exact reach_trans (ih a ha) (Reach.step a (Reach.refl _))

private theorem reach_live {p : Program signature n g} {root w1 w2 : Wire n g}
    (hw2 : WireAccounting.Live p root w2) (h : Reach p w1 w2) :
    WireAccounting.Live p root w1 := by
  induction h with
  | refl => exact hw2
  | step a _ ih => exact WireAccounting.Live.argument (ih hw2) a

private theorem reach_wireOrder_le {p : Program signature n g} {w1 w2 : Wire n g}
    (h : Reach p w1 w2) : wireOrder w1 ≤ wireOrder w2 := by
  induction h with
  | refl => exact le_rfl
  | @step k a _ _ ih =>
    exact (le_of_lt (wireOrder_lt_of_wire k a)).trans ih

private theorem reach_total_of_inj {p : Program signature n g} {root : Wire n g}
    (hInj : Set.InjOn (fun a : Σ k : Fin g, Fin (signature.Arity (p.lines k).op) =>
      (p.lines a.1).wires a.2) (WireAccounting.pins p root : Set _))
    {w u1 u2 : Wire n g} (hu1 : WireAccounting.Live p root u1)
    (hu2 : WireAccounting.Live p root u2)
    (h1 : Reach p w u1) (h2 : Reach p w u2) :
    Reach p u1 u2 ∨ Reach p u2 u1 := by
  classical
  induction h1 generalizing u2 with
  | refl =>
    exact Or.inl h2
  | @step k1 a1 _ h1 ih =>
    generalize hStart : (p.lines k1).wires a1 = start at h2
    cases h2 with
    | refl => exact Or.inr (hStart ▸ Reach.step a1 h1)
    | @step k2 a2 _ h2' =>
      have hk1Live : WireAccounting.Live p root (.gate k1) := reach_live hu1 h1
      have hk2Live : WireAccounting.Live p root (.gate k2) := reach_live hu2 h2'
      have hp1 : (⟨k1, a1⟩ : Σ k : Fin g, Fin (signature.Arity (p.lines k).op)) ∈
          WireAccounting.pins p root :=
        Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk1Live⟩, Finset.mem_univ _⟩
      have hp2 : (⟨k2, a2⟩ : Σ k : Fin g, Fin (signature.Arity (p.lines k).op)) ∈
          WireAccounting.pins p root :=
        Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk2Live⟩, Finset.mem_univ _⟩
      have hEqPair := hInj hp2 hp1 hStart.symm
      have hkEq : k2 = k1 := congrArg Sigma.fst hEqPair
      subst hkEq
      exact ih hu1 hu2 h2'

private theorem live_children_support_disjoint {p : Program signature n g} {root : Wire n g}
    (hInj : Set.InjOn (fun a : Σ k : Fin g, Fin (signature.Arity (p.lines k).op) =>
      (p.lines a.1).wires a.2) (WireAccounting.pins p root : Set _))
    {k : Fin g} (hk : WireAccounting.Live p root (.gate k))
    {a b : Fin (signature.Arity (p.lines k).op)} (hab : a ≠ b) :
    Disjoint (p.wireSupport ((p.lines k).wires a)) (p.wireSupport ((p.lines k).wires b)) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiA hiB
  let u1 := (p.lines k).wires a
  let u2 := (p.lines k).wires b
  have hu1 : WireAccounting.Live p root u1 := WireAccounting.Live.argument hk a
  have hu2 : WireAccounting.Live p root u2 := WireAccounting.Live.argument hk b
  have hR1 := mem_wireSupport_reach p hiA
  have hR2 := mem_wireSupport_reach p hiB
  have hTot := reach_total_of_inj hInj hu1 hu2 hR1 hR2
  have hNoReach : ∀ {x y : Wire n g} {sx sy : Fin (signature.Arity (p.lines k).op)},
      WireAccounting.Live p root y →
      (x = (p.lines k).wires sx) → (y = (p.lines k).wires sy) →
      sx ≠ sy → ¬ Reach p x y := by
    intro x y sx sy hyLive hxEq hyEq hne hR
    cases hR with
    | refl =>
      have hp1 : (⟨k, sx⟩ : Σ t : Fin g, Fin (signature.Arity (p.lines t).op)) ∈
          WireAccounting.pins p root :=
        Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, Finset.mem_univ _⟩
      have hp2 : (⟨k, sy⟩ : Σ t : Fin g, Fin (signature.Arity (p.lines t).op)) ∈
          WireAccounting.pins p root :=
        Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, Finset.mem_univ _⟩
      have hPair := hInj hp1 hp2 (hxEq.symm.trans hyEq)
      exact hne (eq_of_heq (Sigma.ext_iff.mp hPair).2)
    | @step k' a' _ hRest =>
      have hk'Live : WireAccounting.Live p root (.gate k') := reach_live hyLive hRest
      have hp' : (⟨k', a'⟩ : Σ t : Fin g, Fin (signature.Arity (p.lines t).op)) ∈
          WireAccounting.pins p root :=
        Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'Live⟩, Finset.mem_univ _⟩
      have hpS : (⟨k, sx⟩ : Σ t : Fin g, Fin (signature.Arity (p.lines t).op)) ∈
          WireAccounting.pins p root :=
        Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, Finset.mem_univ _⟩
      have hPair := hInj hp' hpS hxEq
      have hkEq : k' = k := congrArg Sigma.fst hPair
      subst k'
      have hOrd1 := reach_wireOrder_le hRest
      have hOrd2 : wireOrder y < @wireOrder n g (.gate k) := by
        rw [hyEq]; exact wireOrder_lt_of_wire k sy
      omega
  rcases hTot with h12 | h21
  · exact hNoReach hu2 rfl rfl hab h12
  · exact hNoReach hu1 rfl rfl hab.symm h21

private def UnateAt (f : BooleanFunction n) (i : Fin n) : Prop :=
  (∀ x, f (Function.update x i false) ≤ f (Function.update x i true)) ∨
  (∀ x, f (Function.update x i true) ≤ f (Function.update x i false))

private theorem interpretation_const {op : Op} {b : Bool} (h : op = .const b)
    (u : Fin (signature.Arity op) → Bool) : interpretation op u = b := by
  subst h
  rfl

private theorem interpretation_not {op : Op} (h : op = .not)
    (u : Fin (signature.Arity op) → Bool) :
    interpretation op u = !u ⟨0, by rw [h]; decide⟩ := by
  subst h
  rfl

private theorem monotone_op' (op : Op) (hNot : op ≠ .not)
    {u v : Fin (signature.Arity op) → Bool} (h : ∀ i, u i ≤ v i) :
    interpretation op u ≤ interpretation op v := by
  cases op with
  | const b => exact le_rfl
  | not => exact (hNot rfl).elim
  | and =>
    have h0 := h 0; have h1 := h 1
    cases hu0 : u 0 <;> cases hu1 : u 1 <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;>
      simp_all [interpretation]
  | or =>
    have h0 := h 0; have h1 := h 1
    cases hu0 : u 0 <;> cases hu1 : u 1 <;> cases hv0 : v 0 <;> cases hv1 : v 1 <;>
      simp_all [interpretation]

/-- A fan-in-two De Morgan circuit computing a nonmonotone function with full essential
support and at least one binate input `i0` requires at least `n + 1` gates. -/
theorem binate_full_support_lower (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hEss : ∀ i, EssentialAt f i) (hNon : ¬ Monotone f)
    (i0 : Fin n)
    (hInc : ∃ x, f (Function.update x i0 false) = false ∧ f (Function.update x i0 true) = true)
    (hDec : ∃ x, f (Function.update x i0 false) = true ∧ f (Function.update x i0 true) = false) :
    n + 1 ≤ c.size := by
  classical
  let p := c.program
  let root := c.outputs 0
  have hRead : WireAccounting.inputs p root = Finset.univ := by
    ext i
    exact ⟨fun _ => Finset.mem_univ _, fun _ => WireAccounting.essential_mem_inputs hc (hEss i)⟩
  have hLiveNot : ∃ j ∈ WireAccounting.gates p root, (p.lines j).op = .not := by
    by_contra h
    apply hNon
    intro x y hxy
    have hTrace (w : Wire n c.size) : WireAccounting.Live p root w →
        p.trace interpretation x w ≤ p.trace interpretation y w := by
      refine p.wire_induction (P := fun w => WireAccounting.Live p root w →
        p.trace interpretation x w ≤ p.trace interpretation y w) ?_ ?_ w
      · intro i _; exact hxy i
      · intro j ih hj
        rw [p.trace_gate, p.trace_gate]
        apply monotone_op' (p.lines j).op (fun hop =>
          h ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hop⟩)
        intro a
        exact ih a (WireAccounting.Live.argument hj a)
    have he := hTrace root WireAccounting.Live.output
    change c.eval interpretation x 0 ≤ c.eval interpretation y 0 at he
    rwa [hc x, hc y] at he
  obtain ⟨j, hj, hop⟩ := hLiveNot
  let G := WireAccounting.gates p root
  have hSum : ∑ k ∈ G, signature.Arity (p.lines k).op < 2 * G.card := by
    have hOther : ∑ k ∈ G.erase j, signature.Arity (p.lines k).op ≤ 2 * (G.erase j).card := by
      calc
        _ ≤ ∑ _k ∈ G.erase j, 2 := Finset.sum_le_sum fun k _ =>
          Program.fanInAtMost_iff.mp p.fanInAtMost_two k
        _ = _ := by simp [Nat.mul_comm]
    have hSplit := Finset.sum_erase_add G (fun k => signature.Arity (p.lines k).op) hj
    rw [hop, show signature.Arity Op.not = 1 by rfl] at hSplit
    have hGpos : 0 < G.card := Finset.card_pos.mpr ⟨j, hj⟩
    rw [Finset.card_erase_of_mem hj] at hOther
    dsimp only [G] at hOther hGpos hSplit ⊢
    omega
  have hMissing : 0 < WireAccounting.missingPins p root := by
    unfold WireAccounting.missingPins WireAccounting.pins
    rw [Finset.card_sigma]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_pos_of_lt hSum
  have hAcct := WireAccounting.inputs_add_charges_le p root
  rw [hRead, Finset.card_univ, Fintype.card_fin] at hAcct
  by_contra hSmall
  have hRepZero : WireAccounting.repeatedUses p root = 0 := by omega
  have hCardEq : (WireAccounting.pins p root).card = (WireAccounting.pinSources p root).card := by
    unfold WireAccounting.repeatedUses at hRepZero
    have hLe : (WireAccounting.pinSources p root).card ≤ (WireAccounting.pins p root).card :=
      Finset.card_image_le
    omega
  have hInj : Set.InjOn (fun a : Σ k : Fin c.size, Fin (signature.Arity (p.lines k).op) =>
      (p.lines a.1).wires a.2) (WireAccounting.pins p root : Set _) :=
    Finset.card_image_iff.mp hCardEq.symm
  have hUnate : ∀ w : Wire n c.size, WireAccounting.Live p root w →
      UnateAt (fun x => p.trace interpretation x w) i0 := by
    intro w
    refine p.wire_induction (P := fun w => WireAccounting.Live p root w →
        UnateAt (fun x => p.trace interpretation x w) i0) ?_ ?_ w
    · intro r _
      by_cases hri : r = i0
      · subst hri; left; intro x; simp
      · left; intro x; simp [Function.update_of_ne hri]
    · intro k ih hk
      have hConstOn (a : Fin (signature.Arity (p.lines k).op))
          (hNotIn : i0 ∉ p.wireSupport ((p.lines k).wires a)) :
          ∀ x, p.trace interpretation (Function.update x i0 false) ((p.lines k).wires a) =
            p.trace interpretation (Function.update x i0 true) ((p.lines k).wires a) := by
        intro x
        apply p.trace_congr
        intro r hr
        have hne : r ≠ i0 := fun hEq => hNotIn (hEq ▸ hr)
        simp [Function.update_of_ne hne]
      have hMonoStep (hOp : (p.lines k).op ≠ .not)
          {a0 : Fin (signature.Arity (p.lines k).op)}
          (hUnate0 : UnateAt (fun x => p.trace interpretation x ((p.lines k).wires a0)) i0)
          (hRest : ∀ b : Fin (signature.Arity (p.lines k).op), b ≠ a0 →
            ∀ x, p.trace interpretation (Function.update x i0 false) ((p.lines k).wires b) =
              p.trace interpretation (Function.update x i0 true) ((p.lines k).wires b)) :
          UnateAt (fun x => p.trace interpretation x (.gate k)) i0 := by
        rcases hUnate0 with hInc0 | hDec0
        · left
          intro x
          dsimp only
          rw [p.trace_gate, p.trace_gate]
          apply monotone_op' (p.lines k).op hOp
          intro b
          by_cases hb : b = a0
          · subst hb; exact hInc0 x
          · exact le_of_eq (hRest b hb x)
        · right
          intro x
          dsimp only
          rw [p.trace_gate, p.trace_gate]
          apply monotone_op' (p.lines k).op hOp
          intro b
          by_cases hb : b = a0
          · subst hb; exact hDec0 x
          · exact le_of_eq (hRest b hb x).symm
      cases hOp : (p.lines k).op with
      | const b =>
        left; intro x
        dsimp only
        rw [p.trace_gate, p.trace_gate, interpretation_const hOp, interpretation_const hOp]
      | not =>
        let z0 : Fin (signature.Arity (p.lines k).op) := ⟨0, by rw [hOp]; decide⟩
        rcases ih z0 (WireAccounting.Live.argument hk z0) with hInc0 | hDec0
        · right
          intro x
          have hx := hInc0 x
          dsimp only at hx ⊢
          rw [p.trace_gate, p.trace_gate, interpretation_not hOp, interpretation_not hOp]
          cases h1 : p.trace interpretation (Function.update x i0 false) ((p.lines k).wires z0) <;>
            cases h2 : p.trace interpretation (Function.update x i0 true) ((p.lines k).wires z0) <;>
            simp_all [z0]
        · left
          intro x
          have hx := hDec0 x
          dsimp only at hx ⊢
          rw [p.trace_gate, p.trace_gate, interpretation_not hOp, interpretation_not hOp]
          cases h1 : p.trace interpretation (Function.update x i0 false) ((p.lines k).wires z0) <;>
            cases h2 : p.trace interpretation (Function.update x i0 true) ((p.lines k).wires z0) <;>
            simp_all [z0]
      | and =>
        let a0 : Fin (signature.Arity (p.lines k).op) := ⟨0, by rw [hOp]; decide⟩
        let a1 : Fin (signature.Arity (p.lines k).op) := ⟨1, by rw [hOp]; decide⟩
        have hAr2 : signature.Arity (p.lines k).op = 2 := by rw [hOp]
        have hne01 : a0 ≠ a1 := fun h => absurd (congrArg Fin.val h) (by simp [a0, a1])
        by_cases hi1 : i0 ∈ p.wireSupport ((p.lines k).wires a1)
        · have hiNot0 : i0 ∉ p.wireSupport ((p.lines k).wires a0) := fun hi0 =>
            Finset.disjoint_left.mp (live_children_support_disjoint hInj hk hne01) hi0 hi1
          refine hMonoStep (by simp [hOp]) (ih a1 (WireAccounting.Live.argument hk a1)) ?_
          intro b hb
          have hbEq : b = a0 := Fin.ext (by
            have hbLt : b.val < 2 := hAr2 ▸ b.isLt
            have hbne : b.val ≠ 1 := fun hv => hb (Fin.ext hv)
            omega)
          rw [hbEq]; exact hConstOn a0 hiNot0
        · refine hMonoStep (by simp [hOp]) (ih a0 (WireAccounting.Live.argument hk a0)) ?_
          intro b hb
          have hbEq : b = a1 := Fin.ext (by
            have hbLt : b.val < 2 := hAr2 ▸ b.isLt
            have hbne : b.val ≠ 0 := fun hv => hb (Fin.ext hv)
            omega)
          rw [hbEq]; exact hConstOn a1 hi1
      | or =>
        let a0 : Fin (signature.Arity (p.lines k).op) := ⟨0, by rw [hOp]; decide⟩
        let a1 : Fin (signature.Arity (p.lines k).op) := ⟨1, by rw [hOp]; decide⟩
        have hAr2 : signature.Arity (p.lines k).op = 2 := by rw [hOp]
        have hne01 : a0 ≠ a1 := fun h => absurd (congrArg Fin.val h) (by simp [a0, a1])
        by_cases hi1 : i0 ∈ p.wireSupport ((p.lines k).wires a1)
        · have hiNot0 : i0 ∉ p.wireSupport ((p.lines k).wires a0) := fun hi0 =>
            Finset.disjoint_left.mp (live_children_support_disjoint hInj hk hne01) hi0 hi1
          refine hMonoStep (by simp [hOp]) (ih a1 (WireAccounting.Live.argument hk a1)) ?_
          intro b hb
          have hbEq : b = a0 := Fin.ext (by
            have hbLt : b.val < 2 := hAr2 ▸ b.isLt
            have hbne : b.val ≠ 1 := fun hv => hb (Fin.ext hv)
            omega)
          rw [hbEq]; exact hConstOn a0 hiNot0
        · refine hMonoStep (by simp [hOp]) (ih a0 (WireAccounting.Live.argument hk a0)) ?_
          intro b hb
          have hbEq : b = a1 := Fin.ext (by
            have hbLt : b.val < 2 := hAr2 ▸ b.isLt
            have hbne : b.val ≠ 0 := fun hv => hb (Fin.ext hv)
            omega)
          rw [hbEq]; exact hConstOn a1 hi1
  have hU := hUnate root WireAccounting.Live.output
  have hFunEq : (fun x => p.trace interpretation x root) = f :=
    funext fun x => congrFun (hc x) 0
  rw [hFunEq] at hU
  rcases hU with hMonoInc | hMonoDec
  · obtain ⟨xDec, hxF, hxT⟩ := hDec
    have hLe := hMonoInc xDec
    rw [hxF, hxT] at hLe
    exact absurd hLe (by decide)
  · obtain ⟨xInc, hxF, hxT⟩ := hInc
    have hLe := hMonoDec xInc
    rw [hxF, hxT] at hLe
    exact absurd hLe (by decide)

/-! ### Part C: Minimum Two-Corner Forest-Escape Control -/

def escapeP0 : Program signature 8 0 := .empty
def escapeP1 : Program signature 8 1 :=
  escapeP0.gate ⟨.or, fun a => if a = 0 then .input 0 else .input 1⟩
def escapeP2 : Program signature 8 2 :=
  escapeP1.gate ⟨.or, fun a => if a = 0 then .input 6 else .input 7⟩
def escapeP3 : Program signature 8 3 :=
  escapeP2.gate ⟨.and, fun a => if a = 0 then .gate 0 else .gate 1⟩
def escapeP4 : Program signature 8 4 :=
  escapeP3.gate ⟨.and, fun a => if a = 0 then .input 1 else .input 2⟩
def escapeP5 : Program signature 8 5 :=
  escapeP4.gate ⟨.and, fun a => if a = 0 then .input 3 else .input 4⟩
def escapeP6 : Program signature 8 6 :=
  escapeP5.gate ⟨.or, fun a => if a = 0 then .gate 3 else .gate 4⟩
def escapeP7 : Program signature 8 7 :=
  escapeP6.gate ⟨.or, fun a => if a = 0 then .gate 5 else .input 5⟩
def escapeP8 : Program signature 8 8 :=
  escapeP7.gate ⟨.not, fun _ => .gate 6⟩

def escapeProgram : Program signature 8 9 :=
  escapeP8.gate ⟨.or, fun a => if a = 0 then .gate 7 else .gate 2⟩

def escapeCircuit : Circuit signature 8 1 := ⟨escapeProgram, fun _ => .gate 8⟩

def escapeDecision (x : BitString 8) : Bool :=
  (!(((x 1 && x 2) || (x 3 && x 4)) || x 5)) || ((x 0 || x 1) && (x 6 || x 7))

def escapeX : BitString 8 := fun j => decide (j = 2)

private theorem escape_lines_0 :
    escapeProgram.lines 0 = ⟨.or, fun a => if a.val = 0 then .input 0 else .input 1⟩ := by
  have h0 : (0 : Fin 9) =
      ((((((((Fin.last 0).castSucc).castSucc).castSucc).castSucc).castSucc).castSucc).castSucc).castSucc := rfl
  rw [h0, escapeProgram, escapeP8, escapeP7, escapeP6, escapeP5, escapeP4, escapeP3, escapeP2, escapeP1]
  iterate 8 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_1 :
    escapeProgram.lines 1 = ⟨.or, fun a => if a.val = 0 then .input 6 else .input 7⟩ := by
  have h1 : (1 : Fin 9) =
      (((((((Fin.last 1).castSucc).castSucc).castSucc).castSucc).castSucc).castSucc).castSucc := rfl
  rw [h1, escapeProgram, escapeP8, escapeP7, escapeP6, escapeP5, escapeP4, escapeP3, escapeP2]
  iterate 7 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_2 :
    escapeProgram.lines 2 = ⟨.and, fun a => if a.val = 0 then .gate 0 else .gate 1⟩ := by
  have h2 : (2 : Fin 9) =
      ((((((Fin.last 2).castSucc).castSucc).castSucc).castSucc).castSucc).castSucc := rfl
  rw [h2, escapeProgram, escapeP8, escapeP7, escapeP6, escapeP5, escapeP4, escapeP3]
  iterate 6 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_3 :
    escapeProgram.lines 3 = ⟨.and, fun a => if a.val = 0 then .input 1 else .input 2⟩ := by
  have h3 : (3 : Fin 9) =
      (((((Fin.last 3).castSucc).castSucc).castSucc).castSucc).castSucc := rfl
  rw [h3, escapeProgram, escapeP8, escapeP7, escapeP6, escapeP5, escapeP4]
  iterate 5 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_4 :
    escapeProgram.lines 4 = ⟨.and, fun a => if a.val = 0 then .input 3 else .input 4⟩ := by
  have h4 : (4 : Fin 9) = ((((Fin.last 4).castSucc).castSucc).castSucc).castSucc := rfl
  rw [h4, escapeProgram, escapeP8, escapeP7, escapeP6, escapeP5]
  iterate 4 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_5 :
    escapeProgram.lines 5 = ⟨.or, fun a => if a.val = 0 then .gate 3 else .gate 4⟩ := by
  have h5 : (5 : Fin 9) = (((Fin.last 5).castSucc).castSucc).castSucc := rfl
  rw [h5, escapeProgram, escapeP8, escapeP7, escapeP6]
  iterate 3 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_6 :
    escapeProgram.lines 6 = ⟨.or, fun a => if a.val = 0 then .gate 5 else .input 5⟩ := by
  have h6 : (6 : Fin 9) = ((Fin.last 6).castSucc).castSucc := rfl
  rw [h6, escapeProgram, escapeP8, escapeP7]
  iterate 2 rw [Program.lines_gate_castSucc]
  rw [Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private theorem escape_lines_7 :
    escapeProgram.lines 7 = ⟨.not, fun _ => .gate 6⟩ := by
  have h7 : (7 : Fin 9) = (Fin.last 7).castSucc := rfl
  rw [h7, escapeProgram, escapeP8]
  rw [Program.lines_gate_castSucc, Program.lines_gate_last]
  simp only [Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a; rfl)

private theorem escape_lines_8 :
    escapeProgram.lines 8 = ⟨.or, fun a => if a.val = 0 then .gate 7 else .gate 2⟩ := by
  have h8 : (8 : Fin 9) = Fin.last 8 := rfl
  rw [h8, escapeProgram]
  simp only [Program.lines_gate_last, Line.mapWires]
  refine congrArg (Line.mk _) (funext fun a => by fin_cases a <;> rfl)

private def escapeGateEval (k : Fin 9) (x : BitString 8) : Bool :=
  match k.val with
  | 0 => x 0 || x 1
  | 1 => x 6 || x 7
  | 2 => (x 0 || x 1) && (x 6 || x 7)
  | 3 => x 1 && x 2
  | 4 => x 3 && x 4
  | 5 => (x 1 && x 2) || (x 3 && x 4)
  | 6 => ((x 1 && x 2) || (x 3 && x 4)) || x 5
  | 7 => !(((x 1 && x 2) || (x 3 && x 4)) || x 5)
  | _ => (!(((x 1 && x 2) || (x 3 && x 4)) || x 5) || ((x 0 || x 1) && (x 6 || x 7)))

private theorem escape_eval_eq (x : BitString 8) :
    (fun k : Fin 9 => escapeGateEval k x) = escapeProgram.eval interpretation x := by
  apply Program.eq_eval_of_forall_lines_eval
  intro gate
  have hgate : gate = 0 ∨ gate = 1 ∨ gate = 2 ∨ gate = 3 ∨ gate = 4 ∨
      gate = 5 ∨ gate = 6 ∨ gate = 7 ∨ gate = 8 := by
    fin_cases gate <;> simp
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [escape_lines_0]; rfl
  · rw [escape_lines_1]; rfl
  · rw [escape_lines_2]; rfl
  · rw [escape_lines_3]; rfl
  · rw [escape_lines_4]; rfl
  · rw [escape_lines_5]; rfl
  · rw [escape_lines_6]; rfl
  · rw [escape_lines_7]; rfl
  · rw [escape_lines_8]; rfl

private theorem escape_trace_gate (k : Fin 9) (x : BitString 8) :
    escapeProgram.trace interpretation x (.gate k) = escapeGateEval k x := by
  change escapeProgram.eval interpretation x k = escapeGateEval k x
  rw [← escape_eval_eq x]

private theorem escape_restrictedWire_gate (ρ : Fin 8 → Fin 8 ⊕ Bool) (k : Fin 9) (z : BitString 8) :
    restrictedWire escapeProgram ρ (.gate k) z = escapeGateEval k (substitute ρ z) :=
  escape_trace_gate k (substitute ρ z)

private def escapeWireSpec (u : Fin 9) (a : Nat) : Wire 8 9 :=
  match u.val with
  | 0 => if a = 0 then .input 0 else .input 1
  | 1 => if a = 0 then .input 6 else .input 7
  | 2 => if a = 0 then .gate 0 else .gate 1
  | 3 => if a = 0 then .input 1 else .input 2
  | 4 => if a = 0 then .input 3 else .input 4
  | 5 => if a = 0 then .gate 3 else .gate 4
  | 6 => if a = 0 then .gate 5 else .input 5
  | 7 => .gate 6
  | _ => if a = 0 then .gate 7 else .gate 2

private theorem escape_wires_eq_of_line {u : Fin 9} {op : Op}
    {w : Fin (signature.Arity op) → Wire 8 9}
    (hLine : escapeProgram.lines u = ⟨op, w⟩)
    (hSpec : ∀ a : Fin (signature.Arity op), w a = escapeWireSpec u a.val)
    (a : Fin (signature.Arity (escapeProgram.lines u).op)) :
    (escapeProgram.lines u).wires a = escapeWireSpec u a.val := by
  have hOp : (escapeProgram.lines u).op = op := congrArg Line.op hLine
  have ha : a.val < signature.Arity op := hOp ▸ a.isLt
  have hw : (escapeProgram.lines u).wires a = w ⟨a.val, ha⟩ := by
    revert a ha
    rw [hLine]
    intro a ha
    exact congrArg w (Fin.ext rfl)
  exact hw.trans (hSpec ⟨a.val, ha⟩)

private theorem escapeWires_eq (u : Fin 9) (a : Fin (signature.Arity (escapeProgram.lines u).op)) :
    (escapeProgram.lines u).wires a = escapeWireSpec u a.val := by
  have hu : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7 ∨ u = 8 := by
    fin_cases u <;> simp
  revert a
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro a; exact escape_wires_eq_of_line escape_lines_0 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_1 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_2 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_3 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_4 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_5 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_6 (fun b => by fin_cases b <;> rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_7 (fun b => by fin_cases b; rfl) a
  · intro a; exact escape_wires_eq_of_line escape_lines_8 (fun b => by fin_cases b <;> rfl) a

private def escapeCornerValSpec (b : Bool) (w : Wire 8 9) : Bool :=
  match w with
  | .input _ => b
  | .gate k => if b = false then decide (k = 7 ∨ k = 8) else decide (k ≠ 7)

private theorem escapeCornerVal_eq (b : Bool) (w : Wire 8 9) :
    cornerValue escapeProgram b w = escapeCornerValSpec b w := by
  cases w with
  | input i => rfl
  | gate k =>
    change escapeProgram.trace interpretation (fun _ => b) (.gate k) = escapeCornerValSpec b (.gate k)
    rw [escape_trace_gate]
    cases b <;> fin_cases k <;> rfl

private def escapeCornerArgsSpec (b : Bool) (k : Fin 9) : Finset (Wire 8 9 × Bool) :=
  if b = false then
    match k.val with
    | 0 => {(.input 0, false), (.input 1, false)}
    | 1 => {(.input 6, false), (.input 7, false)}
    | 2 => {(.gate 0, false)}
    | 3 => {(.input 1, false)}
    | 4 => {(.input 3, false)}
    | 5 => {(.gate 3, false), (.gate 4, false)}
    | 6 => {(.gate 5, false), (.input 5, false)}
    | 7 => {(.gate 6, false)}
    | _ => {(.gate 7, true)}
  else
    match k.val with
    | 0 => {(.input 0, true)}
    | 1 => {(.input 6, true)}
    | 2 => {(.gate 0, true), (.gate 1, true)}
    | 3 => {(.input 1, true), (.input 2, true)}
    | 4 => {(.input 3, true), (.input 4, true)}
    | 5 => {(.gate 3, true)}
    | 6 => {(.gate 5, true)}
    | 7 => {(.gate 6, true)}
    | _ => {(.gate 2, true)}

private theorem escapeCornerArgs_of_line {k : Fin 9} {op : Op}
    {w : Fin (signature.Arity op) → Wire 8 9}
    (hLine : escapeProgram.lines k = ⟨op, w⟩) (b : Bool) :
    cornerArguments escapeProgram k b =
      argumentStates op w (fun a => escapeCornerValSpec b (w a)) := by
  unfold cornerArguments
  have hVal : (fun a => cornerValue escapeProgram b ((escapeProgram.lines k).wires a)) =
      fun a => escapeCornerValSpec b ((escapeProgram.lines k).wires a) := by
    funext a
    exact escapeCornerVal_eq b _
  rw [hVal]
  generalize escapeProgram.lines k = line at hLine ⊢
  subst hLine
  rfl

private theorem escapeCornerArgs_eq (b : Bool) (k : Fin 9) :
    cornerArguments escapeProgram k b = escapeCornerArgsSpec b k := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by
    fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [escapeCornerArgs_of_line escape_lines_0 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_1 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_2 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_3 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_4 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_5 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_6 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_7 b]; cases b <;> decide
  · rw [escapeCornerArgs_of_line escape_lines_8 b]; cases b <;> decide

theorem escape_computes : escapeCircuit.Computes interpretation (single escapeDecision) := by
  intro x
  funext i
  have hi0 : i = 0 := Fin.ext (by omega)
  subst hi0
  change escapeProgram.trace interpretation x (.gate 8) = escapeDecision x
  rw [escape_trace_gate]
  rfl

theorem escape_minimum :
    escapeCircuit.size = complexity interpretation (single escapeDecision) := by
  apply le_antisymm _ (complexity_le_of_computes escapeCircuit escape_computes)
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single escapeDecision)
  rw [← hsize]
  change 8 + 1 ≤ c.size
  refine binate_full_support_lower c hc ?_ ?_ (1 : Fin 8) ?_ ?_
  · intro i
    fin_cases i
    · let x : BitString 8 := fun j => decide (j = 5 ∨ j = 6)
      exact ⟨x, Function.update x 0 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun j => decide (j = 2)
      exact ⟨x, Function.update x 1 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun j => decide (j = 1)
      exact ⟨x, Function.update x 2 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun j => decide (j = 4)
      exact ⟨x, Function.update x 3 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun j => decide (j = 3)
      exact ⟨x, Function.update x 4 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun _ => false
      exact ⟨x, Function.update x 5 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun j => decide (j = 0 ∨ j = 5)
      exact ⟨x, Function.update x 6 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
    · let x : BitString 8 := fun j => decide (j = 0 ∨ j = 5)
      exact ⟨x, Function.update x 7 true, fun j hj => by rw [Function.update_of_ne (by simpa using hj)], by decide⟩
  · intro h
    let x : BitString 8 := fun j => decide (j = 2)
    let y := Function.update x 1 true
    have hxy : x ≤ y := by decide
    have hFalse : ¬ escapeDecision x ≤ escapeDecision y := by decide
    exact hFalse (h hxy)
  · exact ⟨fun j => decide (j = 5 ∨ j = 6), by decide⟩
  · exact ⟨fun j => decide (j = 2), by decide⟩

theorem escape_corners (b : Bool) : cornerValue escapeProgram b (.gate 8) = true := by
  rw [escapeCornerVal_eq]
  cases b <;> rfl

private def escapeNeedSpec (b : Bool) (key : Wire 8 9 × Bool) : Bool :=
  decide (if b = false then
    key = (.gate 8, true) ∨ key = (.gate 7, true) ∨ key = (.gate 6, false) ∨
    key = (.gate 5, false) ∨ key = (.input 5, false) ∨ key = (.gate 3, false) ∨
    key = (.gate 4, false) ∨ key = (.input 1, false) ∨ key = (.input 3, false)
  else
    key = (.gate 8, true) ∨ key = (.gate 2, true) ∨ key = (.gate 0, true) ∨
    key = (.gate 1, true) ∨ key = (.input 0, true) ∨ key = (.input 6, true))

private theorem escapeNeed_iff (b : Bool) (key : Wire 8 9 × Bool) :
    NeedCorner escapeProgram (.gate 8) b key ↔ escapeNeedSpec b key = true := by
  constructor
  · intro h
    have hStep : ∀ (c : Bool) (k : Fin 9) (z : Wire 8 9 × Bool),
        escapeNeedSpec c (.gate k, escapeCornerValSpec c (.gate k)) = true →
        z ∈ escapeCornerArgsSpec c k → escapeNeedSpec c z = true := by
      decide
    induction h with
    | output => cases b <;> rfl
    | argument _ ha ih =>
      rw [escapeCornerVal_eq] at ih
      rw [escapeCornerArgs_eq] at ha
      exact hStep b _ _ ih ha
  · intro h
    have hvF8 : cornerValue escapeProgram false (.gate 8) = true := (escapeCornerVal_eq false (.gate 8)).trans rfl
    have hvF7 : cornerValue escapeProgram false (.gate 7) = true := (escapeCornerVal_eq false (.gate 7)).trans rfl
    have hvF6 : cornerValue escapeProgram false (.gate 6) = false := (escapeCornerVal_eq false (.gate 6)).trans rfl
    have hvF5 : cornerValue escapeProgram false (.gate 5) = false := (escapeCornerVal_eq false (.gate 5)).trans rfl
    have hvF3 : cornerValue escapeProgram false (.gate 3) = false := (escapeCornerVal_eq false (.gate 3)).trans rfl
    have hvF4 : cornerValue escapeProgram false (.gate 4) = false := (escapeCornerVal_eq false (.gate 4)).trans rfl
    have hvT8 : cornerValue escapeProgram true (.gate 8) = true := (escapeCornerVal_eq true (.gate 8)).trans rfl
    have hvT2 : cornerValue escapeProgram true (.gate 2) = true := (escapeCornerVal_eq true (.gate 2)).trans rfl
    have hvT0 : cornerValue escapeProgram true (.gate 0) = true := (escapeCornerVal_eq true (.gate 0)).trans rfl
    have hvT1 : cornerValue escapeProgram true (.gate 1) = true := (escapeCornerVal_eq true (.gate 1)).trans rfl
    have hf8 : NeedCorner escapeProgram (.gate 8) false (.gate 8, true) := NeedCorner.output
    have hf7 : NeedCorner escapeProgram (.gate 8) false (.gate 7, true) :=
      NeedCorner.argument (b := false) (k := 8) (hvF8.symm ▸ hf8) (by rw [escapeCornerArgs_eq]; decide)
    have hf6 : NeedCorner escapeProgram (.gate 8) false (.gate 6, false) :=
      NeedCorner.argument (b := false) (k := 7) (hvF7.symm ▸ hf7) (by rw [escapeCornerArgs_eq]; decide)
    have hf5 : NeedCorner escapeProgram (.gate 8) false (.gate 5, false) :=
      NeedCorner.argument (b := false) (k := 6) (hvF6.symm ▸ hf6) (by rw [escapeCornerArgs_eq]; decide)
    have hfi5 : NeedCorner escapeProgram (.gate 8) false (.input 5, false) :=
      NeedCorner.argument (b := false) (k := 6) (hvF6.symm ▸ hf6) (by rw [escapeCornerArgs_eq]; decide)
    have hf3 : NeedCorner escapeProgram (.gate 8) false (.gate 3, false) :=
      NeedCorner.argument (b := false) (k := 5) (hvF5.symm ▸ hf5) (by rw [escapeCornerArgs_eq]; decide)
    have hf4 : NeedCorner escapeProgram (.gate 8) false (.gate 4, false) :=
      NeedCorner.argument (b := false) (k := 5) (hvF5.symm ▸ hf5) (by rw [escapeCornerArgs_eq]; decide)
    have hfi1 : NeedCorner escapeProgram (.gate 8) false (.input 1, false) :=
      NeedCorner.argument (b := false) (k := 3) (hvF3.symm ▸ hf3) (by rw [escapeCornerArgs_eq]; decide)
    have hfi3 : NeedCorner escapeProgram (.gate 8) false (.input 3, false) :=
      NeedCorner.argument (b := false) (k := 4) (hvF4.symm ▸ hf4) (by rw [escapeCornerArgs_eq]; decide)
    have ht8 : NeedCorner escapeProgram (.gate 8) true (.gate 8, true) := NeedCorner.output
    have ht2 : NeedCorner escapeProgram (.gate 8) true (.gate 2, true) :=
      NeedCorner.argument (b := true) (k := 8) (hvT8.symm ▸ ht8) (by rw [escapeCornerArgs_eq]; decide)
    have ht0 : NeedCorner escapeProgram (.gate 8) true (.gate 0, true) :=
      NeedCorner.argument (b := true) (k := 2) (hvT2.symm ▸ ht2) (by rw [escapeCornerArgs_eq]; decide)
    have ht1 : NeedCorner escapeProgram (.gate 8) true (.gate 1, true) :=
      NeedCorner.argument (b := true) (k := 2) (hvT2.symm ▸ ht2) (by rw [escapeCornerArgs_eq]; decide)
    have hti0 : NeedCorner escapeProgram (.gate 8) true (.input 0, true) :=
      NeedCorner.argument (b := true) (k := 0) (hvT0.symm ▸ ht0) (by rw [escapeCornerArgs_eq]; decide)
    have hti6 : NeedCorner escapeProgram (.gate 8) true (.input 6, true) :=
      NeedCorner.argument (b := true) (k := 1) (hvT1.symm ▸ ht1) (by rw [escapeCornerArgs_eq]; decide)
    cases b
    · simp only [escapeNeedSpec, ite_true, decide_eq_true_eq] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hf8
      · exact hf7
      · exact hf6
      · exact hf5
      · exact hfi5
      · exact hf3
      · exact hf4
      · exact hfi1
      · exact hfi3
    · simp only [escapeNeedSpec, Bool.true_eq_false, ite_false, decide_eq_true_eq] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ht8
      · exact ht2
      · exact ht0
      · exact ht1
      · exact hti0
      · exact hti6

private def escapeReqCornerSpec (b : Bool) (k : Fin 9) : Finset (Wire 8 9 × Bool) :=
  if escapeNeedSpec b (.gate k, escapeCornerValSpec b (.gate k)) then
    escapeCornerArgsSpec b k
  else ∅

private def escapeReqSpec (k : Fin 9) : Finset (Wire 8 9 × Bool) :=
  escapeReqCornerSpec false k ∪ escapeReqCornerSpec true k

private def escapeValSetSpec (k : Fin 9) : Finset Bool :=
  Finset.univ.filter fun v => escapeNeedSpec false (.gate k, v) || escapeNeedSpec true (.gate k, v)

private theorem escapeReq_eq (k : Fin 9) :
    req escapeProgram (.gate 8) k = escapeReqSpec k := by
  classical
  have hRC (b : Bool) : reqCorner escapeProgram (.gate 8) b k = escapeReqCornerSpec b k := by
    simp only [reqCorner, escapeReqCornerSpec, escapeCornerVal_eq, escapeCornerArgs_eq,
      escapeNeed_iff]
  simp only [req, escapeReqSpec, hRC]

private theorem escapeValSet_eq (k : Fin 9) :
    valSet escapeProgram (.gate 8) k = escapeValSetSpec k := by
  classical
  ext v
  simp only [valSet, stateValues, Need, escapeValSetSpec, Finset.mem_filter,
    Finset.mem_univ, true_and, escapeNeed_iff, Bool.or_eq_true]

private theorem escape_not_stop_aux {k : Fin 9}
    (hkUnused : (escapeValSetSpec k).card + 1 - (escapeReqSpec k).card = 0)
    (hkS0 : escapeNeedSpec false (.gate k, true) = false)
    (hkS1 : escapeNeedSpec true (.gate k, false) = false)
    (hkDual : ¬ (escapeNeedSpec false (.gate k, false) = true ∧
      escapeNeedSpec true (.gate k, true) = true))
    (hkRep : ∀ s ∈ escapeReqSpec k,
      (Finset.univ.filter fun m => s ∈ escapeReqSpec m).card < 2)
    (hkTarget : ∀ m : Fin 9,
      1 ≤ (escapeValSetSpec m).card + 1 - (escapeReqSpec m).card →
      ∀ a < 2, escapeWireSpec m a ≠ .gate k) :
    k ∉ StopGate escapeProgram (.gate 8) := by
  classical
  intro hStop
  rcases Finset.mem_union.mp hStop with hCut | hTar
  · rcases Finset.mem_union.mp hCut with hOther | hHasRep
    · rcases Finset.mem_union.mp hOther with hBF | hBadAnd
      · rcases Finset.mem_union.mp hBF with hBF' | hBadOr
        · rcases Finset.mem_union.mp hBF' with hBG | hFG
          · have hu : 1 ≤ unused escapeProgram (.gate 8) k := (Finset.mem_filter.mp hBG).2
            have hu' : 1 ≤ (escapeValSetSpec k).card + 1 - (escapeReqSpec k).card := by
              simpa only [unused, escapeValSet_eq, escapeReq_eq] using hu
            omega
          · have hS := (Finset.mem_sdiff.mp hFG).1
            rcases Finset.mem_union.mp hS with hs0 | hs1
            · have hs0' := (Finset.mem_filter.mp hs0).2
              rw [escapeNeed_iff, hkS0] at hs0'
              cases hs0'
            · have hs1' := (Finset.mem_filter.mp hs1).2
              rw [escapeNeed_iff, hkS1] at hs1'
              cases hs1'
        · have hDualOR := (Finset.mem_filter.mp hBadOr).2.1
          apply hkDual
          refine ⟨(escapeNeed_iff false _).mp hDualOR.2.1, (escapeNeed_iff true _).mp hDualOR.2.2⟩
      · have hDualAND := (Finset.mem_filter.mp hBadAnd).2.1
        apply hkDual
        refine ⟨(escapeNeed_iff false _).mp hDualAND.2.1, (escapeNeed_iff true _).mp hDualAND.2.2⟩
    · obtain ⟨s, hsReq, hsRep⟩ := (Finset.mem_filter.mp hHasRep).2
      have hIsRep : IsRepeatState escapeProgram (.gate 8) s := (Finset.mem_filter.mp hsRep).2
      unfold IsRepeatState at hIsRep
      simp only [escapeReq_eq] at hsReq hIsRep
      have hLt := hkRep s hsReq
      omega
  · obtain ⟨m, hmBG, hmW⟩ := Finset.mem_biUnion.mp ((Finset.mem_filter.mp hTar).2)
    have hu : 1 ≤ unused escapeProgram (.gate 8) m := (Finset.mem_filter.mp hmBG).2
    have hu' : 1 ≤ (escapeValSetSpec m).card + 1 - (escapeReqSpec m).card := by
      simpa only [unused, escapeValSet_eq, escapeReq_eq] using hu
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmW
    have haLt : a.val < 2 :=
      lt_of_lt_of_le a.isLt (Program.fanInAtMost_iff.mp escapeProgram.fanInAtMost_two m)
    rw [escapeWires_eq] at ha
    exact hkTarget m hu' a.val haLt ha

theorem escape_five_not_stop : (⟨5, by decide⟩ : Fin 9) ∉ StopGate escapeProgram (.gate 8) :=
  escape_not_stop_aux (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem escape_two_not_stop : (⟨2, by decide⟩ : Fin 9) ∉ StopGate escapeProgram (.gate 8) :=
  escape_not_stop_aux (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem escape_unused_0 : 1 ≤ (escapeValSetSpec 0).card + 1 - (escapeReqSpec 0).card := by decide
private theorem escape_unused_1 : 1 ≤ (escapeValSetSpec 1).card + 1 - (escapeReqSpec 1).card := by decide
private theorem escape_unused_3 : 1 ≤ (escapeValSetSpec 3).card + 1 - (escapeReqSpec 3).card := by decide
private theorem escape_unused_4 : 1 ≤ (escapeValSetSpec 4).card + 1 - (escapeReqSpec 4).card := by decide
private theorem escape_unused_7 : 1 ≤ (escapeValSetSpec ⟨7, by decide⟩).card + 1 - (escapeReqSpec ⟨7, by decide⟩).card := by decide
private theorem escape_need_8_false : escapeNeedSpec false (.gate 8, true) = true := by decide

theorem escape_stop_others :
    ∀ k : Fin 9, k ≠ ⟨2, by decide⟩ → k ≠ ⟨5, by decide⟩ →
      k ∈ StopGate escapeProgram (.gate 8) := by
  classical
  intro k hk2 hk5
  have hBad (m : Fin 9) (hm : 1 ≤ (escapeValSetSpec m).card + 1 - (escapeReqSpec m).card) :
      m ∈ StopGate escapeProgram (.gate 8) := by
    have hBG : m ∈ badGates escapeProgram (.gate 8) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [unused, escapeValSet_eq, escapeReq_eq] using hm
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hBG))))
  fin_cases k
  · exact hBad 0 escape_unused_0
  · exact hBad 1 escape_unused_1
  · exact (hk2 rfl).elim
  · exact hBad 3 escape_unused_3
  · exact hBad 4 escape_unused_4
  · exact (hk5 rfl).elim
  · have h7 : (⟨7, by decide⟩ : Fin 9) ∈ badGates escapeProgram (.gate 8) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [unused, escapeValSet_eq, escapeReq_eq] using escape_unused_7
    have ha7 : 0 < signature.Arity (escapeProgram.lines ⟨7, by decide⟩).op := by
      have hOp7 : (escapeProgram.lines ⟨7, by decide⟩).op = .not := congrArg Line.op escape_lines_7
      rw [hOp7]; decide
    have hTgt : (.gate (⟨6, by decide⟩ : Fin 9) : Wire 8 9) ∈ badGatesTargets escapeProgram (.gate 8) :=
      Finset.mem_biUnion.mpr ⟨⟨7, by decide⟩, h7,
        Finset.mem_image.mpr ⟨⟨0, ha7⟩, Finset.mem_univ _,
          (escapeWires_eq ⟨7, by decide⟩ ⟨0, ha7⟩).trans rfl⟩⟩
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTgt⟩)
  · exact hBad ⟨7, by decide⟩ escape_unused_7
  · have h8S0 : (⟨8, by decide⟩ : Fin 9) ∈ S0 escapeProgram (.gate 8) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (escapeNeed_iff false _).mpr escape_need_8_false⟩
    have h8BF : (⟨8, by decide⟩ : Fin 9) ∈ badFlip escapeProgram (.gate 8) := by
      by_cases hb : (⟨8, by decide⟩ : Fin 9) ∈ badGates escapeProgram (.gate 8)
      · exact Finset.mem_union_left _ hb
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ h8S0, hb⟩)
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h8BF)))

private theorem escape_wire_two_five_spec :
    ∀ u : Fin 9, (u = 2 ∨ u = 5) → ∀ a < 2,
      ∃ t : Fin 9, escapeWireSpec u a = .gate t ∧ t ≠ 2 ∧ t ≠ 5 := by
  decide

private theorem escape_nonstop_children_stop (u : Fin 9) (hu : u = ⟨2, by decide⟩ ∨ u = ⟨5, by decide⟩)
    (a : Fin (signature.Arity (escapeProgram.lines u).op)) :
    ∃ t : Fin 9, (escapeProgram.lines u).wires a = .gate t ∧
      t ∈ StopGate escapeProgram (.gate 8) := by
  have haLt : a.val < 2 :=
    lt_of_lt_of_le a.isLt (Program.fanInAtMost_iff.mp escapeProgram.fanInAtMost_two u)
  obtain ⟨t, htW, ht2, ht5⟩ := escape_wire_two_five_spec u hu a.val haLt
  exact ⟨t, (escapeWires_eq u a).trans htW, escape_stop_others t ht2 ht5⟩

private theorem escape_orMember_two_or_five {r k : Fin 9}
    (hr : r = ⟨2, by decide⟩ ∨ r = ⟨5, by decide⟩)
    (hk : ORMember escapeProgram (.gate 8) r k) :
    k = ⟨2, by decide⟩ ∨ k = ⟨5, by decide⟩ := by
  have hMain : (k = ⟨2, by decide⟩ ∨ k = ⟨5, by decide⟩) ∧ ORMember escapeProgram (.gate 8) r k := by
    induction hk with
    | self => exact ⟨hr, ORMember.self ‹_›⟩
    | @child u v hu hv ho hWire ih =>
      obtain ⟨a, ha⟩ := hWire
      obtain ⟨t, htW, htStop⟩ := escape_nonstop_children_stop u ih.1 a
      have hEq := ha.symm.trans htW
      injection hEq with htEq
      subst htEq
      exact ((stopGate_outside_forest htStop).1 r (ORMember.child ih.2 hv ho ⟨a, ha⟩)).elim
  exact hMain.1

private theorem escape_andMember_two_or_five {r k : Fin 9}
    (hr : r = ⟨2, by decide⟩ ∨ r = ⟨5, by decide⟩)
    (hk : ANDMember escapeProgram (.gate 8) r k) :
    k = ⟨2, by decide⟩ ∨ k = ⟨5, by decide⟩ := by
  have hMain : (k = ⟨2, by decide⟩ ∨ k = ⟨5, by decide⟩) ∧ ANDMember escapeProgram (.gate 8) r k := by
    induction hk with
    | self => exact ⟨hr, ANDMember.self ‹_›⟩
    | @child u v hu hv ho hWire ih =>
      obtain ⟨a, ha⟩ := hWire
      obtain ⟨t, htW, htStop⟩ := escape_nonstop_children_stop u ih.1 a
      have hEq := ha.symm.trans htW
      injection hEq with htEq
      subst htEq
      exact ((stopGate_outside_forest htStop).2 r (ANDMember.child ih.2 hv ho ⟨a, ha⟩)).elim
  exact hMain.1

theorem escape_forest_mask :
    IsForestMask escapeProgram (.gate 8) escapeX {2} := by
  classical
  constructor
  · intro r hr
    right
    intro i hi
    obtain ⟨k, hkMem, a, ha⟩ := (Finset.mem_filter.mp hi).2
    have hr25 : r = ⟨2, by decide⟩ ∨ r = ⟨5, by decide⟩ := by
      by_contra hNot
      simp only [not_or] at hNot
      exact (stopGate_outside_forest (escape_stop_others r hNot.1 hNot.2)).1 r (ORMember.self hr)
    obtain ⟨t, htW, _⟩ := escape_nonstop_children_stop k (escape_orMember_two_or_five hr25 hkMem) a
    have hContra := ha.symm.trans htW
    cases hContra
  · intro r hr
    right
    intro i hi
    obtain ⟨k, hkMem, a, ha⟩ := (Finset.mem_filter.mp hi).2
    have hr25 : r = ⟨2, by decide⟩ ∨ r = ⟨5, by decide⟩ := by
      by_contra hNot
      simp only [not_or] at hNot
      exact (stopGate_outside_forest (escape_stop_others r hNot.1 hNot.2)).2 r (ANDMember.self hr)
    obtain ⟨t, htW, _⟩ := escape_nonstop_children_stop k (escape_andMember_two_or_five hr25 hkMem) a
    have hContra := ha.symm.trans htW
    cases hContra

theorem escape_separated (v : Bool) :
    EssentialAt (restrictedWire escapeProgram (branchPin escapeX {2} 0 v) (.gate 8)) 1 := by
  let y : BitString 8 := fun _ => false
  refine ⟨y, Function.update y 1 true,
    fun j hj => by rw [Function.update_of_ne (by simpa using hj)], ?_⟩
  rw [escape_restrictedWire_gate, escape_restrictedWire_gate]
  cases v <;> decide

private theorem escape_zero_fresh :
    (⟨0, by decide⟩ : Fin 9) ∈ fresh escapeProgram (pinAt escapeX {2}) := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, _⟩)
  · cases b
    · have h := congrFun hb (fun j => decide (j = 0))
      rw [escape_restrictedWire_gate] at h
      revert h; decide
    · have h := congrFun hb (fun _ => false)
      rw [escape_restrictedWire_gate] at h
      revert h; decide
  · have h0 := congrFun hi (fun j => decide (j = 0))
    have h1 := congrFun hi (fun j => decide (j = 1))
    rw [escape_restrictedWire_gate] at h0 h1
    fin_cases i <;> revert h0 h1 <;> decide
  · exact Fin.not_lt_zero t hlt

theorem escape_joint_fresh :
    (⟨0, by decide⟩ : Fin 9) ∈ StopGate escapeProgram (.gate 8) ∧
      (⟨0, by decide⟩ : Fin 9) ∈ fresh escapeProgram (pinAt escapeX {2}) :=
  ⟨escape_stop_others _ (by decide) (by decide), escape_zero_fresh⟩

private theorem escape_surv_3 :
    restrictedWire escapeProgram (pinAt escapeX {2}) (.gate 3) (fun _ => false) ≠
      restrictedWire escapeProgram (pinAt escapeX {2}) (.gate 3) (fun j => decide (j = 1)) := by
  rw [escape_restrictedWire_gate, escape_restrictedWire_gate]
  decide

theorem escape_early_alias :
    (⟨3, by decide⟩ : Fin 9) ∈ earlyReaders escapeProgram (.gate 8) escapeX {2} {1} := by
  classical
  have hStop : (⟨3, by decide⟩ : Fin 9) ∈ StopGate escapeProgram (.gate 8) :=
    escape_stop_others _ (by decide) (by decide)
  have hSurv : (⟨3, by decide⟩ : Fin 9) ∈ surviving escapeProgram (pinAt escapeX {2}) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨fun _ => false, fun j => decide (j = 1), escape_surv_3⟩
  have hEq : restrictedWire escapeProgram (pinAt escapeX {2}) (.gate 3) = projection 1 := by
    funext z
    rw [escape_restrictedWire_gate]
    simp [projection, escapeGateEval, substitute, pinAt, escapeX]
  have hNotFresh : (⟨3, by decide⟩ : Fin 9) ∉ fresh escapeProgram (pinAt escapeX {2}) :=
    fun h => (Finset.mem_filter.mp h).2 (Or.inr (Or.inl ⟨1, hEq⟩))
  have ha3 : 0 < signature.Arity (escapeProgram.lines ⟨3, by decide⟩).op := by
    have hOp3 : (escapeProgram.lines ⟨3, by decide⟩).op = .and := congrArg Line.op escape_lines_3
    rw [hOp3]; decide
  exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
    ⟨Finset.mem_inter.mpr ⟨hStop, hSurv⟩, hNotFresh⟩,
    1, by simp, ⟨⟨0, ha3⟩, (escapeWires_eq ⟨3, by decide⟩ ⟨0, ha3⟩).trans rfl⟩⟩

private theorem escape_five_fresh_start :
    (⟨5, by decide⟩ : Fin 9) ∈ fresh escapeProgram (pinAt escapeX {2}) := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
  · cases b
    · have h := congrFun hb (fun j => decide (j = 1))
      rw [escape_restrictedWire_gate] at h
      revert h; decide
    · have h := congrFun hb (fun _ => false)
      rw [escape_restrictedWire_gate] at h
      revert h; decide
  · have h1 := congrFun hi (fun j => decide (j = 1))
    have h34 := congrFun hi (fun j => decide (j = 3 ∨ j = 4))
    rw [escape_restrictedWire_gate] at h1 h34
    fin_cases i <;> revert h1 h34 <;> decide
  · fin_cases t
    · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4))
      rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
    · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4))
      rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
    · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4))
      rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
    · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4))
      rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
    · have h := congrFun heq (fun j => decide (j = 1))
      rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)

private theorem escape_zero_lost :
    (⟨0, by decide⟩ : Fin 9) ∈ nextFreshLoss escapeProgram (pinAt escapeX {2}) (pinAt escapeX {1}) := by
  classical
  have hDisc : disclosed escapeProgram (compose (pinAt escapeX {2}) (pinAt escapeX {1})) 0 := by
    refine Or.inr (Or.inl ⟨0, ?_⟩)
    funext z
    rw [escape_restrictedWire_gate]
    simp [projection, escapeGateEval, substitute, compose, pinAt, escapeX]
  exact Finset.mem_sdiff.mpr ⟨escape_joint_fresh.2,
    fun h => by simp [fresh, hDisc] at h⟩

private theorem escape_five_lost :
    (⟨5, by decide⟩ : Fin 9) ∈ nextFreshLoss escapeProgram (pinAt escapeX {2}) (pinAt escapeX {1}) := by
  classical
  have hDisc : disclosed escapeProgram (compose (pinAt escapeX {2}) (pinAt escapeX {1})) 5 := by
    refine Or.inr (Or.inr ⟨4, by decide, ?_⟩)
    funext z
    rw [escape_restrictedWire_gate, escape_restrictedWire_gate]
    simp [escapeGateEval, substitute, compose, pinAt, escapeX]
  exact Finset.mem_sdiff.mpr ⟨escape_five_fresh_start,
    fun h => by simp [fresh, hDisc] at h⟩

theorem escape_fresh_losses_ge_two :
    2 ≤ (nextFreshLoss escapeProgram (pinAt escapeX {2}) (pinAt escapeX {1})).card := by
  classical
  exact Finset.one_lt_card.mpr ⟨⟨0, by decide⟩, escape_zero_lost, ⟨5, by decide⟩, escape_five_lost,
    by decide⟩

private theorem escape_fresh_end_mem (k : Fin 9) (hk1 : k = 1 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8) :
    k ∈ fresh escapeProgram (compose (pinAt escapeX {2}) (pinAt escapeX {1})) := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases hk1 with rfl | rfl | rfl | rfl | rfl
  · rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
    · cases b
      · have h := congrFun hb (fun j => decide (j = 6)); rw [escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun hb (fun _ => false); rw [escape_restrictedWire_gate] at h; revert h; decide
    · have h6 := congrFun hi (fun j => decide (j = 6))
      have h7 := congrFun hi (fun j => decide (j = 7))
      rw [escape_restrictedWire_gate] at h6 h7
      fin_cases i <;> revert h6 h7 <;> decide
    · have ht0 : t = 0 := Fin.ext (by omega)
      subst ht0
      have h := congrFun heq (fun j => decide (j = 6))
      rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
  · rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
    · cases b
      · have h := congrFun hb (fun j => decide (j = 3 ∨ j = 4)); rw [escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun hb (fun _ => false); rw [escape_restrictedWire_gate] at h; revert h; decide
    · have h34 := congrFun hi (fun j => decide (j = 3 ∨ j = 4))
      have h3 := congrFun hi (fun j => decide (j = 3))
      have h4 := congrFun hi (fun j => decide (j = 4))
      rw [escape_restrictedWire_gate] at h34 h3 h4
      fin_cases i <;> revert h34 h3 h4 <;> decide
    · fin_cases t
      · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 3 ∨ j = 4)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
  · rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
    · cases b
      · have h := congrFun hb (fun j => decide (j = 5)); rw [escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun hb (fun _ => false); rw [escape_restrictedWire_gate] at h; revert h; decide
    · have h5 := congrFun hi (fun j => decide (j = 5))
      have h34 := congrFun hi (fun j => decide (j = 3 ∨ j = 4))
      rw [escape_restrictedWire_gate] at h5 h34
      fin_cases i <;> revert h5 h34 <;> decide
    · fin_cases t
      · have h := congrFun heq (fun j => decide (j = 5)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 5)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 5)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 5)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 5)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 5)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
  · rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
    · cases b
      · have h := congrFun hb (fun _ => false); rw [escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun hb (fun j => decide (j = 5)); rw [escape_restrictedWire_gate] at h; revert h; decide
    · have h0 := congrFun hi (fun _ => false)
      rw [escape_restrictedWire_gate] at h0
      fin_cases i <;> revert h0 <;> decide
    · fin_cases t
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · exact absurd hlt (by decide)
      · exact absurd hlt (by decide)
  · rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨t, hlt, heq⟩)
    · cases b
      · have h := congrFun hb (fun _ => false); rw [escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun hb (fun j => decide (j = 5)); rw [escape_restrictedWire_gate] at h; revert h; decide
    · have h0 := congrFun hi (fun _ => false)
      rw [escape_restrictedWire_gate] at h0
      fin_cases i <;> revert h0 <;> decide
    · fin_cases t
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun _ => false); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · have h := congrFun heq (fun j => decide (j = 0 ∨ j = 5 ∨ j = 6)); rw [escape_restrictedWire_gate, escape_restrictedWire_gate] at h; revert h; decide
      · exact absurd hlt (by decide)

theorem escape_stop_losses_card :
    (losses escapeProgram (.gate 8) escapeX {2} {1}).card = 1 := by
  classical
  have hEq : losses escapeProgram (.gate 8) escapeX {2} {1} = {⟨0, by decide⟩} := by
    ext k
    simp only [losses, Finset.mem_inter, Finset.mem_singleton]
    constructor
    · rintro ⟨hStop, hNext⟩
      have hNotFreshEnd : k ∉ fresh escapeProgram
          (compose (pinAt escapeX {2}) (pinAt escapeX {1})) :=
        (Finset.mem_sdiff.mp hNext).2
      have hSurvFresh : k ∈ fresh escapeProgram (pinAt escapeX {2}) :=
        (Finset.mem_sdiff.mp hNext).1
      fin_cases k
      · rfl
      · exact (hNotFreshEnd (escape_fresh_end_mem 1 (Or.inl rfl))).elim
      · exact (escape_two_not_stop hStop).elim
      · have hNot3 : (⟨3, by decide⟩ : Fin 9) ∉ fresh escapeProgram (pinAt escapeX {2}) := by
          have hEq3 : restrictedWire escapeProgram (pinAt escapeX {2}) (.gate 3) = projection 1 := by
            funext z
            rw [escape_restrictedWire_gate]
            simp [projection, escapeGateEval, substitute, pinAt, escapeX]
          exact fun h => (Finset.mem_filter.mp h).2 (Or.inr (Or.inl ⟨1, hEq3⟩))
        exact (hNot3 hSurvFresh).elim
      · exact (hNotFreshEnd (escape_fresh_end_mem 4 (Or.inr (Or.inl rfl)))).elim
      · exact (escape_five_not_stop hStop).elim
      · exact (hNotFreshEnd (escape_fresh_end_mem 6 (Or.inr (Or.inr (Or.inl rfl))))).elim
      · exact (hNotFreshEnd (escape_fresh_end_mem 7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).elim
      · exact (hNotFreshEnd (escape_fresh_end_mem 8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))).elim
    · rintro rfl
      exact ⟨escape_joint_fresh.1, escape_zero_lost⟩
  rw [hEq, Finset.card_singleton]

/-- The fresh bypass lost on the control keeps its original index outside
the stop set. -/
theorem escape_outside_loss :
    (5 : Fin 9) ∈ nextFreshLoss escapeProgram (pinAt escapeX {2}) (pinAt escapeX {1}) \
      StopGate escapeProgram (.gate 8) :=
  Finset.mem_sdiff.mpr ⟨escape_five_lost, escape_five_not_stop⟩

/-- The clean bypass gate requests two gate states in the original corner
certificates and has no direct request to a raw input. -/
theorem escape_five_requests :
    req escapeProgram (.gate 8) 5 = {(.gate 3, false), (.gate 4, false)} :=
  (escapeReq_eq 5).trans (by decide)

#print axioms fresh_bypass_of_absorbed_joint
#print axioms match_fresh_oriented_readers
#print axioms mcsp_affine_fresh_oriented_charge
#print axioms alias_control_loses_fresh_reader
#print axioms binate_full_support_lower
#print axioms escape_minimum
#print axioms escape_forest_mask
#print axioms escape_stop_losses_card
#print axioms escape_fresh_losses_ge_two

end PvsNP.Frontier.FreshBypass
