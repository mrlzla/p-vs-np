module

public import MCSPCommunicationCut
public import MCSPSampleControls

/-! A sparse, near-`2N` control whose circuits are wide on every cut in the verified family. -/

@[expose] public section

namespace PvsNP.Frontier.NarrowCut

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut
open SampleControls (agreesOn agreesOn_eq_true agreesOn_cost)

variable {r s : ℕ}

def prefixBlock (keep : Finset (BitString s)) (a : BitString r) :
    Finset (Fin (2 ^ (r + (s + 1)))) :=
  ((Finset.univ : Finset Bool) ×ˢ keep).image fun x => position a x.1 x.2

theorem position_mem_prefixBlock (keep : Finset (BitString s)) (a : BitString r) (b : Bool)
    (u : BitString s) (hu : u ∈ keep) : position a b u ∈ prefixBlock keep a :=
  Finset.mem_image.mpr ⟨(b, u), Finset.mem_product.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩

theorem card_prefixBlock (keep : Finset (BitString s)) (a : BitString r) :
    (prefixBlock keep a).card = 2 * keep.card := by
  have hinj : Function.Injective (fun x : Bool × BitString s => position a x.1 x.2) := by
    intro x y heq
    change positionEquiv r s (a, x) = positionEquiv r s (a, y) at heq
    exact congrArg (fun z : BitString r × Bool × BitString s => z.2) ((positionEquiv r s).injective heq)
  rw [prefixBlock, Finset.card_image_of_injective _ hinj, Finset.card_product]
  simp

/-- The bits in each retained prefix block must all agree. Omitted suffixes are free. -/
noncomputable def prefixControl (r : ℕ) (keep : Finset (BitString s))
    (x : BitString (2 ^ (r + (s + 1)))) : Bool :=
  open scoped Classical in decide (∀ a : BitString r, agreesOn (prefixBlock keep a) x = true)

theorem prefixControl_accepts_probe (keep : Finset (BitString s)) (f : BooleanFunction r) :
    prefixControl r keep (probe s f) = true := by
  classical
  rw [prefixControl, decide_eq_true_eq]
  intro a
  apply (agreesOn_eq_true _ _).mpr
  intro i hi j hj
  obtain ⟨⟨b, u⟩, _, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨⟨b', u'⟩, _, rfl⟩ := Finset.mem_image.mp hj
  simp

/-- A retained split pair witnesses disagreement of any two different prefix probes,
for every selector in the family. -/
theorem prefixControl_equality (keep : Finset (BitString s)) (hne : keep.Nonempty)
    (h : BooleanFunction s) (f g : BooleanFunction r) :
    prefixControl r keep (splice (mask r h) (probe s f) (probe s g)) = true ↔ f = g := by
  classical
  constructor
  · intro hAccept
    apply funext
    intro a
    let u := hne.choose
    have hu : u ∈ keep := hne.choose_spec
    have hBlocks := of_decide_eq_true hAccept
    have hPair := (agreesOn_eq_true _ _).mp (hBlocks a)
      (position a false u) (position_mem_prefixBlock keep a false u hu)
      (position a true u) (position_mem_prefixBlock keep a true u hu)
    simp only [splice, mask_at_position, probe_at_position] at hPair
    cases hb : h u
    · simpa [hb] using hPair.symm
    · simpa [hb] using hPair
  · rintro rfl
    rw [splice_self]
    exact prefixControl_accepts_probe keep f

theorem prefixControl_size_bound (r : ℕ) (keep : Finset (BitString s)) :
    complexity interpretation (single (prefixControl r keep)) ≤
      2 ^ r * (4 * keep.card + 5) + 1 := by
  classical
  have hSynth := Synthesis.forall_mem (Finset.univ : Finset (BitString r))
    (fun a => agreesOn (prefixBlock keep a)) (fun a => 2 * (prefixBlock keep a).card + 4)
    (fun a _ => agreesOn_cost _)
  have h := Synthesis.congr_iff hSynth (g := prefixControl r keep) (fun x => by simp [prefixControl])
  apply h.complexity_le.trans
  simp [card_prefixBlock]
  omega

open scoped Classical in
/-- One bit per prefix block plus the bits at omitted suffixes determines an accepted table. -/
theorem prefixControl_accepting_count_le (r : ℕ) (keep : Finset (BitString s)) (hne : keep.Nonempty) :
    (acceptingTables (prefixControl r keep)).card ≤ 2 ^ (2 ^ r + 2 * 2 ^ r * keepᶜ.card) := by
  classical
  let known := acceptingTables (prefixControl r keep)
  let code (x : known) :
      BooleanFunction r × ((BitString r × Bool × (↑(keepᶜ) : Type)) → Bool) :=
    (fun a => x.val (position a false hne.choose), fun q => x.val (position q.1 q.2.1 q.2.2.val))
  have hinj : Function.Injective code := by
    intro x y heq
    apply Subtype.ext
    funext i
    obtain ⟨⟨a, b, u⟩, rfl⟩ := (positionEquiv r s).surjective i
    change x.val (position a b u) = y.val (position a b u)
    by_cases hu : u ∈ keep
    · have hx := (agreesOn_eq_true _ _).mp
        ((of_decide_eq_true (Finset.mem_filter.mp x.property).2) a)
        (position a b u) (position_mem_prefixBlock keep a b u hu)
        (position a false hne.choose) (position_mem_prefixBlock keep a false _ hne.choose_spec)
      have hy := (agreesOn_eq_true _ _).mp
        ((of_decide_eq_true (Finset.mem_filter.mp y.property).2) a)
        (position a b u) (position_mem_prefixBlock keep a b u hu)
        (position a false hne.choose) (position_mem_prefixBlock keep a false _ hne.choose_spec)
      exact hx.trans ((congrFun (congrArg Prod.fst heq) a).trans hy.symm)
    · exact congrFun (congrArg Prod.snd heq) (a, b, ⟨u, Finset.mem_compl.mpr hu⟩)
  have hCard := Fintype.card_le_of_injective code hinj
  rw [Finset.card_compl, BitString.card]
  simpa [known, Fintype.card_prod, Fintype.card_fun, BitString.card, pow_add, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hCard

theorem every_prefixControl_circuit_is_wide (h : BooleanFunction s) (keep : Finset (BitString s))
    (hne : keep.Nonempty) (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (prefixControl r keep)))
    (owner : Wire (2 ^ (r + (s + 1))) c.size → Bool)
    (hOwner : ∀ i, owner (.input i) = mask r h i) :
    2 ^ r ≤ (crossingWires c.program owner).card :=
  crossingWires_lower_bound_of_equality h (prefixControl r keep)
    (prefixControl_equality keep hne h) c hc owner hOwner

def splitProjection (r s : ℕ) : BitString (2 ^ (r + (s + 1))) :=
  MCSP.truthTable _ (fun x => x (Fin.natAdd r (0 : Fin (s + 1))))

theorem splitProjection_mcsp (r s : ℕ) : mcspSquare (r + (s + 1)) (splitProjection r s) = true := by
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, splitProjection, Equiv.symm_apply_apply,
    complexity_single_proj]
  exact Nat.zero_le _

theorem splitProjection_rejected_by_control (r : ℕ) (keep : Finset (BitString s)) (hne : keep.Nonempty) :
    prefixControl r keep (splitProjection r s) = false := by
  cases h : prefixControl r keep (splitProjection r s) with
  | false => rfl
  | true =>
    let a : BitString r := fun _ => false
    let u := hne.choose
    have hAll := of_decide_eq_true h
    have hPair := (agreesOn_eq_true _ _).mp (hAll a)
      (position a false u) (position_mem_prefixBlock keep a false u hne.choose_spec)
      (position a true u) (position_mem_prefixBlock keep a true u hne.choose_spec)
    simp [splitProjection, position] at hPair

/-- At arity 32, omit two suffixes. This frees 2,048 positions while retaining a split pair
in every prefix block. -/
noncomputable def keep32 : Finset (BitString 22) := open scoped Classical in
  {(BitString.equivFin 22).symm 1, (BitString.equivFin 22).symm 2}ᶜ

private theorem keep32_nonempty : keep32.Nonempty := by
  classical
  let e := (BitString.equivFin 22).symm
  refine ⟨e 0, ?_⟩
  have h1 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h2 : e 0 ≠ e 2 := e.injective.ne (by decide)
  simp [keep32, h1, h2, e]

open scoped Classical in
private theorem keep32_compl_card : keep32ᶜ.card = 2 := by
  classical
  have h : (BitString.equivFin 22).symm 1 ≠ (BitString.equivFin 22).symm 2 :=
    (BitString.equivFin 22).symm.injective.ne (by decide)
  simp [keep32, h]

private theorem keep32_card : keep32.card = 2 ^ 22 - 2 := by
  classical
  have h := keep32_compl_card
  rw [Finset.card_compl, BitString.card] at h
  omega

theorem prefixControl32_sparse :
    (acceptingTables (prefixControl 9 keep32)).card ≤ 2 ^ descriptionBitBound 32 := by
  classical
  have h := prefixControl_accepting_count_le 9 keep32 keep32_nonempty
  rw [keep32_compl_card] at h
  exact h.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by decide))

/-- A control under the literal `2N` cap that accepts all equality probes and every circuit
for which is wide across the entire verified mask family. The witness is a minimum circuit. -/
theorem minimum_wide_control_32 :
    ∃ c : Circuit signature (2 ^ 32) 1,
      c.Computes interpretation (single (prefixControl 9 keep32)) ∧
      c.size = complexity interpretation (single (prefixControl 9 keep32)) ∧
      c.size + 1535 ≤ 2 * 2 ^ 32 ∧
      ∀ (h : BooleanFunction 22) (owner : Wire (2 ^ 32) c.size → Bool),
        (∀ i, owner (.input i) = mask 9 h i) → 512 ≤ (crossingWires c.program owner).card := by
  obtain ⟨c, hc, hMin⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (prefixControl 9 keep32))
  refine ⟨c, hc, hMin, ?_, fun h owner hOwner =>
    every_prefixControl_circuit_is_wide h keep32 keep32_nonempty c hc owner hOwner⟩
  have hSize := prefixControl_size_bound 9 keep32
  rw [keep32_card] at hSize
  omega

theorem splitProjection32_distinguishes :
    prefixControl 9 keep32 (splitProjection 9 22) = false ∧
      mcspSquare 32 (splitProjection 9 22) = true :=
  ⟨splitProjection_rejected_by_control 9 keep32 keep32_nonempty, splitProjection_mcsp 9 22⟩

section PairSymmetry

private theorem coordinates_position (a : BitString r) (b : Bool) (u : BitString s) :
    (positionEquiv r s).symm (position a b u) = (a, b, u) :=
  (positionEquiv r s).symm_apply_apply (a, b, u)

noncomputable def swapPair (key : BitString r × BitString s)
    (x : BitString (2 ^ (r + (s + 1)))) (i : Fin (2 ^ (r + (s + 1)))) : Bool :=
  open scoped Classical in
  let z := (positionEquiv r s).symm i
  if (z.1, z.2.2) = key then x (position z.1 (!z.2.1) z.2.2) else x i

noncomputable def orientedProjection (moves : Finset (BitString r × BitString s))
    (i : Fin (2 ^ (r + (s + 1)))) : Bool := open scoped Classical in
  let z := (positionEquiv r s).symm i
  if (z.1, z.2.2) ∈ moves then !z.2.1 else z.2.1

open scoped Classical in
@[simp] theorem orientedProjection_at (moves : Finset (BitString r × BitString s))
    (a : BitString r) (b : Bool) (u : BitString s) :
    orientedProjection moves (position a b u) = if (a, u) ∈ moves then !b else b := by
  simp [orientedProjection, coordinates_position]

theorem orientedProjection_empty (r s : ℕ) :
    orientedProjection (∅ : Finset (BitString r × BitString s)) = splitProjection r s := by
  funext i
  obtain ⟨⟨a, b, u⟩, rfl⟩ := (positionEquiv r s).surjective i
  change orientedProjection ∅ (position a b u) = splitProjection r s (position a b u)
  rw [orientedProjection_at]
  simp [splitProjection, position]

open scoped Classical in
theorem swap_orientedProjection_insert (key : BitString r × BitString s)
    (moves : Finset (BitString r × BitString s)) (hNew : key ∉ moves) :
    swapPair key (orientedProjection moves) = orientedProjection (insert key moves) := by
  classical
  funext i
  obtain ⟨⟨a, b, u⟩, rfl⟩ := (positionEquiv r s).surjective i
  change swapPair key (orientedProjection moves) (position a b u) =
    orientedProjection (insert key moves) (position a b u)
  by_cases heq : (a, u) = key
  · simp [swapPair, coordinates_position, heq, hNew]
  · simp [swapPair, coordinates_position, heq]

/-- For exact MCSP, at most the counting loss many split pairs can be individually swap-invariant.
Otherwise the orbit of the accepted split projection supplies too many accepted tables. -/
theorem mcspSquare_swap_invariance_bound (pairs : Finset (BitString r × BitString s))
    (hInv : ∀ key ∈ pairs, ∀ x, mcspSquare (r + (s + 1)) (swapPair key x) = mcspSquare (r + (s + 1)) x) :
    pairs.card ≤ descriptionBitBound (r + (s + 1)) := by
  classical
  have accepted (moves : Finset (BitString r × BitString s)) (hSub : moves ⊆ pairs) :
      mcspSquare (r + (s + 1)) (orientedProjection moves) = true := by
    induction moves using Finset.induction_on with
    | empty => rw [orientedProjection_empty]; exact splitProjection_mcsp r s
    | @insert key moves hNew ih =>
      rw [← swap_orientedProjection_insert key moves hNew,
        hInv key (hSub (Finset.mem_insert_self ..))]
      exact ih ((Finset.subset_insert ..).trans hSub)
  have hInjective : Function.Injective (orientedProjection (r := r) (s := s)) := by
    intro u v huv
    ext key
    have hBit := congrFun huv (position key.1 false key.2)
    by_cases hu : key ∈ u <;> by_cases hv : key ∈ v <;> simp_all
  have hCount : pairs.powerset.card ≤ (acceptingTables (mcspSquare (r + (s + 1)))).card := by
    apply Finset.card_le_card_of_injOn orientedProjection
    · intro moves hmoves
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, accepted moves (Finset.mem_powerset.mp hmoves)⟩
    · intro _ _ _ _ heq
      exact hInjective heq
  rw [Finset.card_powerset] at hCount
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
    (hCount.trans (card_accepting_mcspSquare_le _))

end PairSymmetry

end PvsNP.Frontier.NarrowCut
