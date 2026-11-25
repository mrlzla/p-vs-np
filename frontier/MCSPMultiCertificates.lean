module

public import MCSPRestrictions

/-! Count shared certificate demands over an arbitrary finite set of truth tables. -/

@[expose] public section

namespace PvsNP.Frontier.MultiCertificates

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates (argumentStates selectedPins agrees_of_selectedPins stateSet stateValues
  stateInputs card_stateSet)

def requiredArgumentValue (op : Op) (out : Bool) : Bool :=
  match op with
  | .not => !out
  | _ => out

theorem selected_value (op : Op) (x : Fin (signature.Arity op) → Bool) :
    ∀ a ∈ selectedPins op x, x a = requiredArgumentValue op (interpretation op x) := by
  cases op with
  | const b => simp [selectedPins]
  | not =>
    intro a _
    have ha : a = 0 := Subsingleton.elim ..
    subst a
    simp [requiredArgumentValue, interpretation]
  | and =>
    rw [Fin.forall_fin_two]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp_all [selectedPins, requiredArgumentValue, interpretation]
  | or =>
    rw [Fin.forall_fin_two]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp_all [selectedPins, requiredArgumentValue, interpretation]

variable {n g : ℕ}

def argumentsAt (p : Program signature n g) (k : Fin g) (x : BitString n) :
    Finset (Wire n g × Bool) :=
  argumentStates (p.lines k).op (p.lines k).wires
    (fun a => p.trace interpretation x ((p.lines k).wires a))

/-- A demand is a wire together with the value that must be certified. -/
inductive Needed (p : Program signature n g) (root : Wire n g) (sample : Finset (BitString n)) :
    Wire n g × Bool → Prop where
  | output : Needed p root sample (root, true)
  | argument {x : BitString n} (hx : x ∈ sample) {k : Fin g}
      (h : Needed p root sample (.gate k, p.trace interpretation x (.gate k)))
      {key : Wire n g × Bool} (ha : key ∈ argumentsAt p k x) : Needed p root sample key

noncomputable def requestedArguments (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (k : Fin g) : Finset (Wire n g × Bool) := open scoped Classical in
  (sample.filter fun x => Needed p root sample (.gate k, p.trace interpretation x (.gate k))).biUnion
    (argumentsAt p k)

noncomputable abbrev inputStates (p : Program signature n g) (root : Wire n g) (sample : Finset (BitString n))
    (b : Bool) := stateInputs (Needed p root sample) b

noncomputable abbrev outputValues (p : Program signature n g) (root : Wire n g) (sample : Finset (BitString n))
    (k : Fin g) := stateValues (Needed p root sample) (.gate k)

/-- A gate's distinct argument demands use only its input wires and the demanded output values,
with the values complemented for NOT. -/
theorem card_requestedArguments_le (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (k : Fin g) : (requestedArguments p root sample k).card ≤
      signature.Arity (p.lines k).op * (outputValues p root sample k).card := by
  classical
  let line := p.lines k
  let sources := (Finset.univ : Finset (Fin (signature.Arity line.op))).image line.wires
  let values := (outputValues p root sample k).image (requiredArgumentValue line.op)
  have hSub : requestedArguments p root sample k ⊆ sources ×ˢ values := by
    intro key hKey
    obtain ⟨x, hx, ha⟩ := Finset.mem_biUnion.mp hKey
    obtain ⟨a, hPin, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p.trace interpretation x (.gate k), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · rw [p.trace_gate]
      exact (selected_value line.op _ _ hPin).symm
  calc
    _ ≤ (sources ×ˢ values).card := Finset.card_le_card hSub
    _ = sources.card * values.card := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul (Finset.card_image_le.trans (by simp [line])) Finset.card_image_le

noncomputable def excess (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (k : Fin g) : ℕ :=
  (requestedArguments p root sample k).card - ((outputValues p root sample k).card + 1)

noncomputable def unused (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (k : Fin g) : ℕ :=
  (outputValues p root sample k).card + 1 - (requestedArguments p root sample k).card

noncomputable def sharedRequests (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) : ℕ :=
  (∑ k : Fin g, (requestedArguments p root sample k).card) -
    ((Finset.univ : Finset (Fin g)).biUnion (requestedArguments p root sample)).card

/-- The extra local cost is exactly one if a gate has all four possible argument states. -/
theorem excess_eq_indicator (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (k : Fin g) :
    excess p root sample k = if (requestedArguments p root sample k).card = 4 then 1 else 0 := by
  classical
  have hArity := Program.fanInAtMost_iff.mp p.fanInAtMost_two k
  have hStates := (card_requestedArguments_le p root sample k).trans
    (Nat.mul_le_mul_right _ hArity)
  have hValues : (outputValues p root sample k).card ≤ 2 := by
    simpa using Finset.card_le_univ (outputValues p root sample k)
  unfold excess
  split <;> omega

private def wireOrder : Wire n g → ℕ
  | .input _ => 0
  | .gate k => k.val + 1

private theorem argument_precedes (p : Program signature n g) (k : Fin g) (x : BitString n)
    {key : Wire n g × Bool} (h : key ∈ argumentsAt p k x) :
    wireOrder key.1 < wireOrder (.gate k : Wire n g) := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h
  change wireOrder ((p.lines k).wires a) < k.val + 1
  cases hWire : (p.lines k).wires a with
  | input i => simp [wireOrder]
  | gate j =>
    exact Nat.succ_lt_succ (show j.val < k.val from p.lt_of_lines_wires_eq_gate k a j hWire)

private theorem needed_precedes_root {p : Program signature n g} {root : Wire n g}
    {sample : Finset (BitString n)} {key : Wire n g × Bool} (h : Needed p root sample key) :
    wireOrder key.1 ≤ wireOrder root := by
  induction h with
  | output => exact le_rfl
  | @argument x hx k hGate key hArg ih =>
    exact (argument_precedes p k x hArg).le.trans ih

/-- Exact accounting. Each requested state is either the root demand or an argument demand,
and the designated output cannot occur among its own ancestors. -/
theorem input_states_add_charges_eq (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) :
    (inputStates p root sample false).card + (inputStates p root sample true).card +
      sharedRequests p root sample + ∑ k : Fin g, unused p root sample k =
      g + 1 + ∑ k : Fin g, excess p root sample k := by
  classical
  let allArgs := (Finset.univ : Finset (Fin g)).biUnion (requestedArguments p root sample)
  have hArgs : ∀ key ∈ allArgs, wireOrder key.1 < wireOrder root := by
    intro key hKey
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hKey
    obtain ⟨x, hx, hArg⟩ := Finset.mem_biUnion.mp hk
    exact (argument_precedes p k x hArg).trans_le
      (needed_precedes_root (Finset.mem_filter.mp hx).2)
  have hRoot : (root, true) ∉ allArgs := fun hr =>
    (Nat.lt_irrefl (wireOrder root)) (hArgs _ hr)
  have hSet : stateSet (Needed p root sample) = insert (root, true) allArgs := by
    ext key
    constructor
    · intro hk
      have h := (Finset.mem_filter.mp hk).2
      cases h with
      | output => exact Finset.mem_insert_self ..
      | @argument x hx k hGate key hArg =>
        exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hGate⟩, hArg⟩⟩)
    · intro hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hKey
      · exact Needed.output
      · obtain ⟨k, _, hAt⟩ := Finset.mem_biUnion.mp hKey
        obtain ⟨x, hx, hArg⟩ := Finset.mem_biUnion.mp hAt
        exact Needed.argument (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2 hArg
  have hSize : (stateSet (Needed p root sample)).card = allArgs.card + 1 := by
    rw [hSet, Finset.card_insert_of_notMem hRoot]
  have hTotal : allArgs.card ≤ ∑ k : Fin g, (requestedArguments p root sample k).card :=
    Finset.card_biUnion_le
  have localBalance (k : Fin g) : (requestedArguments p root sample k).card + unused p root sample k =
      (outputValues p root sample k).card + 1 + excess p root sample k := by
    unfold unused excess
    omega
  have hBalance := congrArg (fun f : Fin g → ℕ => ∑ k, f k) (funext localBalance)
  have hBalance' : (∑ k : Fin g, (requestedArguments p root sample k).card) +
      (∑ k : Fin g, unused p root sample k) = (∑ k : Fin g, (outputValues p root sample k).card) +
      g + ∑ k : Fin g, excess p root sample k := by
    simpa [Finset.sum_add_distrib] using hBalance
  rw [card_stateSet] at hSize
  change (inputStates p root sample false).card + (inputStates p root sample true).card +
    (∑ k : Fin g, (outputValues p root sample k).card) = allArgs.card + 1 at hSize
  change _ + ((∑ k : Fin g, (requestedArguments p root sample k).card) - allArgs.card) + _ = _
  omega

theorem input_states_add_charges_le (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) :
    (inputStates p root sample false).card + (inputStates p root sample true).card +
      sharedRequests p root sample + ∑ k : Fin g, unused p root sample k ≤
      g + 1 + ∑ k : Fin g, excess p root sample k :=
  (input_states_add_charges_eq p root sample).le

theorem Needed.mono {p : Program signature n g} {root : Wire n g}
    {small large : Finset (BitString n)} (hSub : small ⊆ large) {key : Wire n g × Bool}
    (h : Needed p root small key) : Needed p root large key := by
  induction h with
  | output => exact .output
  | argument hx _ ha ih => exact .argument (hSub hx) ih ha

/-- `R + U - E` in the certificate bound, with subtraction taken in the integers. -/
noncomputable def netMargin (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) : ℤ :=
  ((sharedRequests p root sample + ∑ k : Fin g, unused p root sample k : ℕ) : ℤ) -
    ((∑ k : Fin g, excess p root sample k : ℕ) : ℤ)

theorem netMargin_eq (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) : netMargin p root sample =
      (g : ℤ) + 1 - (inputStates p root sample false).card -
      (inputStates p root sample true).card := by
  have h := input_states_add_charges_eq p root sample
  unfold netMargin
  omega

theorem inputStates_mono (p : Program signature n g) (root : Wire n g)
    {small large : Finset (BitString n)} (hSub : small ⊆ large) (b : Bool) :
    inputStates p root small b ⊆ inputStates p root large b := by
  classical
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Needed.mono hSub (Finset.mem_filter.mp hi).2⟩

theorem netMargin_antitone (p : Program signature n g) (root : Wire n g)
    {small large : Finset (BitString n)} (hSub : small ⊆ large) :
    netMargin p root large ≤ netMargin p root small := by
  have h0 := Finset.card_le_card (inputStates_mono p root hSub false)
  have h1 := Finset.card_le_card (inputStates_mono p root hSub true)
  rw [netMargin_eq, netMargin_eq]
  omega

theorem certifies_accepted (p : Program signature n g) (root : Wire n g)
    (sample : Finset (BitString n)) (x y : BitString n) (hx : x ∈ sample)
    (hRoot : p.trace interpretation x root = true)
    (agree : ∀ i ∈ inputStates p root sample (x i), y i = x i) :
    p.trace interpretation y root = true := by
  classical
  have hTrace : ∀ w, Needed p root sample (w, p.trace interpretation x w) →
      p.trace interpretation y w = p.trace interpretation x w := by
    intro w
    refine p.wire_induction (P := fun w => Needed p root sample (w, p.trace interpretation x w) →
      p.trace interpretation y w = p.trace interpretation x w) ?_ ?_ w
    · intro i hi
      exact agree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro k ih hk
      rw [p.trace_gate, p.trace_gate]
      apply agrees_of_selectedPins
      intro a ha
      exact ih a (Needed.argument hx hk (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
  exact (hTrace root (hRoot.symm ▸ Needed.output)).trans hRoot

private theorem constant_certificate_card (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (sample : Finset (BitString (2 ^ m))) (b : Bool) (hCenter : (fun _ => b) ∈ sample) :
    2 ^ m ≤ (inputStates c.program (c.outputs 0) sample b).card + descriptionBitBound m := by
  classical
  let fixed := inputStates c.program (c.outputs 0) sample b
  let free := Finset.univ \ fixed
  let center : BitString (2 ^ m) := fun _ => b
  have hAccept : mcspSquare m center = true := mcspSquare_constant_table m hm b
  have hRoot : c.program.trace interpretation center (c.outputs 0) = true :=
    (congrFun (hc center) 0).trans hAccept
  have hAll (x : BitString (2 ^ m)) : mcspSquare m (restrictTable center free x) = true := by
    have hTrace := certifies_accepted c.program (c.outputs 0) sample center
      (restrictTable center free x) hCenter hRoot fun i hi => by
        have hNot : i ∉ free := fun h => (Finset.mem_sdiff.mp h).2 hi
        simp [restrictTable, hNot, center]
    exact (congrFun (hc (restrictTable center free x)) 0).symm.trans hTrace
  have hEmpty : essentialPositions (fun x => mcspSquare m (restrictTable center free x)) free = ∅ := by
    ext i
    simp [essentialPositions, EssentialAt, hAll]
  have hLoss := mcspSquare_restriction_loss m center free hAccept
  rw [hEmpty, Finset.card_empty, Nat.zero_add] at hLoss
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ fixed)
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  change free.card + fixed.card = 2 ^ m at hSplit
  change 2 ^ m ≤ fixed.card + descriptionBitBound m
  omega

/-- The many-certificate bound for the quadratic-cutoff slice, including both constant tables. -/
theorem mcspSquare_sample_bound (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (sample : Finset (BitString (2 ^ m)))
    (h0 : (fun _ => false) ∈ sample) (h1 : (fun _ => true) ∈ sample) :
    2 * 2 ^ m + sharedRequests c.program (c.outputs 0) sample +
      ∑ k : Fin c.size, unused c.program (c.outputs 0) sample k ≤
    c.size + 1 + 2 * descriptionBitBound m +
      ∑ k : Fin c.size, excess c.program (c.outputs 0) sample k := by
  have hFalse := constant_certificate_card m hm c hc sample false h0
  have hTrue := constant_certificate_card m hm c hc sample true h1
  have hCount := input_states_add_charges_le c.program (c.outputs 0) sample
  omega

/-- A shared-demand margin large enough to beat the two-certificate bound and its error. -/
theorem mcspSquare_above_two_of_margin (m extra : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (sample : Finset (BitString (2 ^ m))) (h0 : (fun _ => false) ∈ sample)
    (h1 : (fun _ => true) ∈ sample)
    (margin : 1 + 2 * descriptionBitBound m + extra +
        (∑ k : Fin c.size, excess c.program (c.outputs 0) sample k) ≤
      sharedRequests c.program (c.outputs 0) sample +
        ∑ k : Fin c.size, unused c.program (c.outputs 0) sample k) :
    2 * 2 ^ m + extra ≤ c.size := by
  have h := mcspSquare_sample_bound m hm c hc sample h0 h1
  omega

/-- Three samples can make one AND gate request every input pin in both polarities. -/
theorem and_three_samples_need_four :
    (argumentStates .and (id : Fin 2 → Fin 2) (fun i => decide (i = 1)) ∪
      argumentStates .and id (fun i => decide (i = 0)) ∪
      argumentStates .and id (fun _ => true)).card = 4 := by decide

theorem mcspSquare_accepts_projection (m : ℕ) (j : Fin m) :
    mcspSquare m (MCSP.truthTable m (fun x => x j)) = true := by
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  rw [complexity_single_proj]
  exact Nat.zero_le _

/-- Two constant tables and the `m` coordinate projections, all accepted at cutoff `m^2`. -/
noncomputable def projectionProbes (m : ℕ) : Finset (BitString (2 ^ m)) := open scoped Classical in
  insert (fun _ => false) (insert (fun _ => true)
    (Finset.univ.image fun j : Fin m => MCSP.truthTable m (fun x => x j)))

theorem projectionProbes_are_accepted (m : ℕ) (hm : 1 ≤ m) {x : BitString (2 ^ m)}
    (hx : x ∈ projectionProbes m) : mcspSquare m x = true := by
  classical
  simp only [projectionProbes, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | rfl | ⟨j, rfl⟩
  · exact mcspSquare_constant_table m hm false
  · exact mcspSquare_constant_table m hm true
  · exact mcspSquare_accepts_projection m j

theorem projectionProbes_card_le (m : ℕ) : (projectionProbes m).card ≤ m + 2 := by
  classical
  let rows := (Finset.univ : Finset (Fin m)).image fun j => MCSP.truthTable m (fun x => x j)
  have hRows : rows.card ≤ m := Finset.card_image_le.trans (by simp)
  have hTrue := Finset.card_insert_le (fun _ => true) rows
  have hFalse := Finset.card_insert_le (fun _ => false) (insert (fun _ => true) rows)
  change (insert (fun _ => false) (insert (fun _ => true) rows)).card ≤ m + 2
  omega

/-- The projection probes distinguish every pair of truth-table positions. -/
theorem projectionProbes_separate_positions (m : ℕ) :
    Function.Injective (fun i : Fin (2 ^ m) => fun x : projectionProbes m => x.val i) := by
  classical
  intro i j h
  apply (BitString.equivFin m).symm.injective
  funext k
  let row := MCSP.truthTable m (fun x => x k)
  have hRow : row ∈ projectionProbes m :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  have hp := congrFun h ⟨row, hRow⟩
  simpa [row, MCSP.truthTable_apply] using hp

/-- The sample used by the two-certificate proof. -/
noncomputable def constantProbes (n : ℕ) : Finset (BitString n) :=
  open scoped Classical in {(fun _ => false), (fun _ => true)}

theorem constantProbes_subset_projectionProbes (m : ℕ) :
    constantProbes (2 ^ m) ⊆ projectionProbes m := by
  classical
  intro x hx
  simp only [constantProbes, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;> simp [projectionProbes]

/-- The projection signatures cannot increase the margin for a fixed circuit and output. -/
theorem projection_margin_le_constant_margin (m : ℕ) (p : Program signature (2 ^ m) g)
    (root : Wire (2 ^ m) g) :
    netMargin p root (projectionProbes m) ≤ netMargin p root (constantProbes (2 ^ m)) :=
  netMargin_antitone p root (constantProbes_subset_projectionProbes m)

/-- On an MCSP solver, the change in margin from adding the projections is between `-2 B(m)`
and zero: the two constant probes already demand nearly all the available input states. -/
theorem projection_margin_bounds (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m))) :
    netMargin c.program (c.outputs 0) (projectionProbes m) ≤
        netMargin c.program (c.outputs 0) (constantProbes (2 ^ m)) ∧
      netMargin c.program (c.outputs 0) (constantProbes (2 ^ m)) ≤
        netMargin c.program (c.outputs 0) (projectionProbes m) + 2 * (descriptionBitBound m : ℤ) := by
  classical
  refine ⟨projection_margin_le_constant_margin m _ _, ?_⟩
  have h0 := constant_certificate_card m hm c hc (constantProbes (2 ^ m)) false
    (by simp [constantProbes])
  have h1 := constant_certificate_card m hm c hc (constantProbes (2 ^ m)) true
    (by simp [constantProbes])
  have hUpper (b : Bool) : (inputStates c.program (c.outputs 0) (projectionProbes m) b).card ≤ 2 ^ m := by
    simpa using Finset.card_le_univ (inputStates c.program (c.outputs 0) (projectionProbes m) b)
  have hp0 := hUpper false
  have hp1 := hUpper true
  rw [netMargin_eq, netMargin_eq]
  omega

/-- Even maximal coverage of input states by the projection probes leaves a gate-count
obligation. In this case the requested margin is equivalent to the stronger size bound. -/
theorem saturated_projection_margin_iff (m extra : ℕ) (p : Program signature (2 ^ m) g)
    (root : Wire (2 ^ m) g)
    (h : ∀ b, inputStates p root (projectionProbes m) b = Finset.univ) :
    1 + 2 * (descriptionBitBound m : ℤ) + (extra : ℤ) ≤
        netMargin p root (projectionProbes m) ↔
      2 * 2 ^ m + 2 * descriptionBitBound m + extra ≤ g := by
  rw [netMargin_eq, h false, h true, Finset.card_univ, Fintype.card_fin]
  omega

end PvsNP.Frontier.MultiCertificates
