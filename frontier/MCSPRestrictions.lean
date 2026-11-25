module

public import Complexity.Computability.Circuit.Support
public import Complexity.Computability.Circuit.Boolean.Hierarchy
public import Complexity.Computability.MCSP.Basic
public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Finset.Sum

/-! Truth-table restrictions and a gate-count bound that charges wire reuse. -/

@[expose] public section

namespace PvsNP.Frontier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

namespace WireAccounting

variable {n g : ℕ}

/-- Wires found by following argument pins backwards from the designated output. -/
inductive Live (p : Program signature n g) (root : Wire n g) : Wire n g → Prop where
  | output : Live p root root
  | argument {k : Fin g} (h : Live p root (.gate k)) (a : Fin (signature.Arity (p.lines k).op)) :
      Live p root ((p.lines k).wires a)

noncomputable def inputs (p : Program signature n g) (root : Wire n g) : Finset (Fin n) :=
  open scoped Classical in Finset.univ.filter fun i => Live p root (.input i)

noncomputable def gates (p : Program signature n g) (root : Wire n g) : Finset (Fin g) :=
  open scoped Classical in Finset.univ.filter fun k => Live p root (.gate k)

noncomputable def wires (p : Program signature n g) (root : Wire n g) : Finset (Wire n g) :=
  open scoped Classical in Finset.univ.filter (Live p root)

/-- Argument pins are counted separately, even when two pins read the same wire. -/
noncomputable def pins (p : Program signature n g) (root : Wire n g) :
    Finset (Σ k : Fin g, Fin (signature.Arity (p.lines k).op)) :=
  (gates p root).sigma fun _ => Finset.univ

noncomputable def pinSources (p : Program signature n g) (root : Wire n g) : Finset (Wire n g) :=
  (pins p root).image fun a => (p.lines a.1).wires a.2

/-- For each wire read by a live gate, charge every use beyond its first use. -/
noncomputable def repeatedUses (p : Program signature n g) (root : Wire n g) : ℕ :=
  (pins p root).card - (pinSources p root).card

/-- Missing argument slots at live gates, relative to a two-input gate. -/
noncomputable def missingPins (p : Program signature n g) (root : Wire n g) : ℕ :=
  2 * (gates p root).card - (pins p root).card

private theorem card_wires (p : Program signature n g) (root : Wire n g) :
    (wires p root).card = (inputs p root).card + (gates p root).card := by
  classical
  have h : (wires p root).map (Wire.equiv n g).toEmbedding =
      (inputs p root).disjSum (gates p root) := by
    ext w
    cases w with
    | inl i =>
      rw [Finset.mem_map_equiv]
      simp [wires, inputs, Wire.equiv]
    | inr k =>
      rw [Finset.mem_map_equiv]
      simp [wires, gates, Wire.equiv]
  simpa using congrArg Finset.card h

private theorem wires_eq (p : Program signature n g) (root : Wire n g) :
    wires p root = insert root (pinSources p root) := by
  classical
  ext w
  simp only [wires, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    pinSources, Finset.mem_image, pins, Finset.mem_sigma, gates, and_true]
  constructor
  · intro hw
    cases hw with
    | output => exact Or.inl rfl
    | argument h a => exact Or.inr ⟨⟨_, a⟩, h, rfl⟩
  · rintro (rfl | ⟨⟨k, a⟩, hk, rfl⟩)
    · exact Live.output
    · exact Live.argument hk a

/-- Wire accounting for an arbitrary one-output De Morgan circuit, including dead gates. -/
theorem inputs_add_charges_le (p : Program signature n g) (root : Wire n g) :
    (inputs p root).card + repeatedUses p root + missingPins p root ≤ g + 1 := by
  classical
  have hG : (gates p root).card ≤ g := by
    simpa using Finset.card_le_univ (gates p root)
  have hW : (wires p root).card ≤ (pinSources p root).card + 1 := by
    rw [wires_eq]
    exact Finset.card_insert_le ..
  have hDistinct : (pinSources p root).card ≤ (pins p root).card := Finset.card_image_le
  have hPins : (pins p root).card ≤ 2 * (gates p root).card := by
    rw [pins, Finset.card_sigma]
    calc
      _ ≤ ∑ _k ∈ gates p root, (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro k _
        simpa using (Program.fanInAtMost_iff.mp p.fanInAtMost_two k)
      _ = _ := by simp [Nat.mul_comm]
  rw [card_wires] at hW
  unfold repeatedUses missingPins
  omega

private theorem live_of_mem_support (p : Program signature n g) (root : Wire n g)
    {w : Wire n g} (hw : Live p root w) {i : Fin n} (hi : i ∈ p.wireSupport w) :
    Live p root (.input i) := by
  revert hw hi
  refine p.wire_induction (P := fun w => Live p root w → i ∈ p.wireSupport w →
    Live p root (.input i)) ?_ ?_ w
  · intro j hj hi
    simpa using (show i = j from by simpa using hi) ▸ hj
  · intro k ih hk hi
    change i ∈ p.trace (supportInterpretation signature n) (fun j => {j}) (.gate k) at hi
    rw [p.trace_gate] at hi
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hi
    exact ih a (Live.argument hk a) ha

theorem essential_mem_inputs {f : BitString n → Bool} {c : Circuit signature n 1}
    (hc : c.Computes interpretation (single f)) {i : Fin n} (hi : EssentialAt f i) :
    i ∈ inputs c.program (c.outputs 0) := by
  classical
  have hDep : DependsOn f (c.inputSupport : Set (Fin n)) := by
    intro x y h
    exact congrFun (hc.dependsOn h) 0
  obtain ⟨j, hj⟩ := (Circuit.mem_inputSupport (c := c)).mp (hi.mem_support hDep)
  have hj0 : j = 0 := Subsingleton.elim ..
  subst j
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, live_of_mem_support _ _ Live.output hj⟩

end WireAccounting

section Restrictions

variable {n : ℕ}

/-- Hold the truth-table entries outside `free` at their values in `center`. -/
def restrictTable (center : BitString n) (free : Finset (Fin n)) (values : BitString n) :
    BitString n := fun i => if i ∈ free then values i else center i

noncomputable def essentialPositions (f : BitString n → Bool) (free : Finset (Fin n)) :
    Finset (Fin n) := open scoped Classical in free.filter (EssentialAt f)

noncomputable def acceptingTables (f : BitString n → Bool) : Finset (BitString n) :=
  Finset.univ.filter fun t => f t = true

/-- Inessential coordinates can be changed together without changing the result. -/
theorem eq_of_agree_off {f : BitString n → Bool} (ignored : Finset (Fin n))
    (h : ∀ i ∈ ignored, ¬ EssentialAt f i) {x y : BitString n}
    (agree : ∀ i ∉ ignored, x i = y i) : f x = f y := by
  induction ignored using Finset.induction_on generalizing x with
  | empty =>
    have : x = y := funext fun i => agree i (by simp)
    rw [this]
  | @insert i tail _ ih =>
    let next := Function.update x i (y i)
    have heq : f x = f next := by
      by_contra hne
      apply h i (Finset.mem_insert_self ..)
      exact ⟨x, next, fun j hj => by simp [next, Function.update_of_ne hj], hne⟩
    apply heq.trans
    apply ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    intro j hj
    by_cases hji : j = i
    · subst j
      simp [next]
    · simpa [next, Function.update_of_ne hji] using agree j (by simp [hji, hj])

/-- Inessential free positions in an accepting restriction generate an accepting subcube. -/
theorem pow_card_inessential_le (f : BitString n → Bool) (center : BitString n)
    (free : Finset (Fin n)) (hCenter : f center = true) :
    2 ^ (free \ essentialPositions (fun x => f (restrictTable center free x)) free).card ≤
      (acceptingTables f).card := by
  classical
  let restricted := fun x => f (restrictTable center free x)
  let ignored := free \ essentialPositions restricted free
  have hFree : ignored ⊆ free := Finset.sdiff_subset
  have hInessential : ∀ i ∈ ignored, ¬EssentialAt restricted i := by
    intro i hi he
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_filter.mpr ⟨hFree hi, he⟩)
  let table (bits : (i : ignored) → Bool) : BitString n :=
    fun i => if h : i ∈ ignored then bits ⟨i, h⟩ else center i
  have hAccept (bits : (i : ignored) → Bool) : table bits ∈ acceptingTables f := by
    have hAgree : ∀ i ∉ ignored, table bits i = center i := by
      intro i hi
      simp [table, hi]
    have hRestricted := eq_of_agree_off ignored hInessential hAgree
    have hTable : restrictTable center free (table bits) = table bits := by
      funext i
      by_cases hi : i ∈ free
      · simp [restrictTable, hi]
      · simp [restrictTable, table, hi, show i ∉ ignored from fun h => hi (hFree h)]
    have hSelf : restrictTable center free center = center := by
      funext i
      simp [restrictTable]
    simpa [restricted, hTable, hSelf, acceptingTables, hCenter] using hRestricted
  let into (bits : (i : ignored) → Bool) : acceptingTables f := ⟨table bits, hAccept bits⟩
  have hInjective : Function.Injective into := by
    intro a b h
    funext i
    have hi := congrFun (congrArg Subtype.val h) i.val
    simpa [into, table, i.property] using hi
  change 2 ^ ignored.card ≤ (acceptingTables f).card
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool] using
    Fintype.card_le_of_injective into hInjective

end Restrictions

/-- The exact MCSP slice with a quadratic cutoff on the represented function's arity. -/
noncomputable def mcspSquare (m : ℕ) : BitString (2 ^ m) → Bool :=
  (GapMCSP.yesSet fun j => j ^ 2).slice (2 ^ m)

/-- An upper bound on the number of binary digits needed to index the accepted tables. -/
def descriptionBitBound (m : ℕ) : ℕ :=
  let b := (m + 1).log2 + 1
  4 * b + (3 + 4 * b) * m ^ 2

/-- Retain the factorial from the circuit counting estimate. -/
theorem card_accepting_mcspSquare_mul_factorial_le (m : ℕ) :
    (acceptingTables (mcspSquare m)).card * (m^2).factorial ≤ 2 ^ descriptionBitBound m := by
  classical
  let s := m ^ 2
  let b := (m + 1).log2 + 1
  have hAccepted : (↑(acceptingTables (mcspSquare m)) : Set (BitString (2 ^ m))) =
      {T | (⟨m, T, s⟩ : MCSP.Instance) ∈ Cslib.MCSP} := by
    ext T
    simp [acceptingTables, mcspSquare, s, MCSP.mem_iff, MCSP.Instance.function]
  rw [← Set.ncard_coe_finset, hAccepted, MCSP.ncard_setOf_mem]
  have hCount := Boolean.card_computableFunctions_mul_factorial_le m s
  have hmb : m + 1 ≤ 2 ^ b := (Nat.lt_log2_self (n := m + 1)).le
  have hBase : m + s + 1 ≤ 2 ^ (2 * b) := by
    rw [Nat.mul_comm 2, pow_mul]
    exact (show m + s + 1 ≤ (m + 1) ^ 2 by dsimp [s]; nlinarith).trans
      (Nat.pow_le_pow_left hmb 2)
  have hGate : 5 * (m + s + 1) ^ 2 ≤ 2 ^ (3 + 4 * b) := by
    calc
      _ ≤ 2 ^ 3 * (2 ^ (2 * b)) ^ 2 :=
        Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left hBase 2)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  calc
    (computableFunctions m s).card * s.factorial ≤
      (s + 1) * (5 * (m + s + 1) ^ 2) ^ s * (m + s) := hCount
    _ ≤ 2 ^ (2 * b) * (2 ^ (3 + 4 * b)) ^ s * 2 ^ (2 * b) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hGate s)) (by omega)
    _ = _ := by
      change _ = 2 ^ (4 * b + (3 + 4 * b) * s)
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

theorem card_accepting_mcspSquare_le (m : ℕ) :
    (acceptingTables (mcspSquare m)).card ≤ 2 ^ descriptionBitBound m :=
  (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)).trans
    (card_accepting_mcspSquare_mul_factorial_le m)

theorem mcspSquare_constant_table (m : ℕ) (hm : 1 ≤ m) (b : Bool) :
    mcspSquare m (fun _ => b) = true := by
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff]
  change complexity interpretation (single (fun _ : BitString m => b)) ≤ m ^ 2
  rw [Boolean.complexity_const]
  exact Nat.one_le_pow _ _ hm

theorem mcspSquare_restriction_loss (m : ℕ) (center : BitString (2 ^ m))
    (free : Finset (Fin (2 ^ m))) (accepted : mcspSquare m center = true) :
    free.card ≤ (essentialPositions (fun x => mcspSquare m (restrictTable center free x)) free).card
      + descriptionBitBound m := by
  classical
  let ess := essentialPositions (fun x => mcspSquare m (restrictTable center free x)) free
  have hPow := (pow_card_inessential_le (mcspSquare m) center free accepted).trans
    (card_accepting_mcspSquare_le m)
  change 2 ^ (free \ ess).card ≤ 2 ^ descriptionBitBound m at hPow
  have hLost := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hPow
  have hSubset : ess ⊆ free := Finset.filter_subset _ _
  have hParts := Finset.card_sdiff_add_card_eq_card hSubset
  change free.card ≤ ess.card + descriptionBitBound m
  omega

theorem mcspSquare_wire_bound (m : ℕ) (hm : 1 ≤ m) (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m))) :
    2 ^ m + WireAccounting.repeatedUses c.program (c.outputs 0) +
      WireAccounting.missingPins c.program (c.outputs 0) ≤ c.size + 1 + descriptionBitBound m := by
  classical
  have hRestricted := mcspSquare_restriction_loss m (fun _ => false) Finset.univ
    (mcspSquare_constant_table m hm false)
  have hIdentity (x : BitString (2 ^ m)) : restrictTable (fun _ => false) Finset.univ x = x := by
    funext i
    simp [restrictTable]
  simp only [hIdentity, Finset.card_univ, Fintype.card_fin] at hRestricted
  change 2 ^ m ≤ (essentialPositions (mcspSquare m) Finset.univ).card + _ at hRestricted
  have hEss : (essentialPositions (mcspSquare m) Finset.univ).card ≤
      (WireAccounting.inputs c.program (c.outputs 0)).card := by
    apply Finset.card_le_card
    intro i hi
    exact WireAccounting.essential_mem_inputs hc (Finset.mem_filter.mp hi).2
  have hCharge := WireAccounting.inputs_add_charges_le c.program (c.outputs 0)
  omega

/-- A near-linear lower bound in `N = 2^m`, with an explicit `O(m^2 log m)` loss. -/
theorem mcspSquare_near_linear (m : ℕ) (hm : 1 ≤ m) :
    2 ^ m ≤ complexity interpretation (single (mcspSquare m)) + 1 + descriptionBitBound m := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  have h := mcspSquare_wire_bound m hm c hc
  omega

namespace CornerCertificates

/-- Select argument pins sufficient to certify a gate's value at an assignment. -/
def selectedPins : (op : Op) → (Fin (signature.Arity op) → Bool) → Finset (Fin (signature.Arity op))
  | .const _, _ => ∅
  | .not, _ => {0}
  | .and, x => if x 0 then (if x 1 then Finset.univ else {1}) else {0}
  | .or, x => if x 0 then {0} else (if x 1 then {1} else Finset.univ)

theorem agrees_of_selectedPins (op : Op) (x y : Fin (signature.Arity op) → Bool)
    (h : ∀ a ∈ selectedPins op x, y a = x a) : interpretation op y = interpretation op x := by
  cases op with
  | const b => rfl
  | not => simpa [interpretation] using congrArg Bool.not (h 0 (by simp [selectedPins]))
  | and =>
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp_all [selectedPins, interpretation, Fin.forall_fin_two]
  | or =>
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp_all [selectedPins, interpretation, Fin.forall_fin_two]

/-- Index a requirement by the source wire and its required Boolean value. -/
def argumentStates {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x : Fin (signature.Arity op) → Bool) :
    Finset (W × Bool) := (selectedPins op x).image fun a => (sources a, x a)

theorem card_argumentStates_le {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x : Fin (signature.Arity op) → Bool) :
    (argumentStates op sources x).card ≤ 2 := by
  exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans
    (by cases op <;> simp))

private theorem and_short {W : Type*} [DecidableEq W] (sources : Fin 2 → W)
    (x : Fin 2 → Bool) (h : interpretation .and x = false) :
    (argumentStates .and sources x).card ≤ 1 := by
  apply Finset.card_image_le.trans
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all [selectedPins, interpretation]

private theorem or_short {W : Type*} [DecidableEq W] (sources : Fin 2 → W)
    (x : Fin 2 → Bool) (h : interpretation .or x = true) :
    (argumentStates .or sources x).card ≤ 1 := by
  apply Finset.card_image_le.trans
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all [selectedPins, interpretation]

theorem union_bound {W : Type*} [DecidableEq W] (op : Op)
    (sources : Fin (signature.Arity op) → W) (x y : Fin (signature.Arity op) → Bool) :
    (argumentStates op sources x ∪ argumentStates op sources y).card ≤
      if interpretation op x = interpretation op y then 2 else 3 := by
  have hx := card_argumentStates_le op sources x
  have hy := card_argumentStates_le op sources y
  have hu := Finset.card_union_le (argumentStates op sources x) (argumentStates op sources y)
  cases op with
  | const b => simp [argumentStates, selectedPins]
  | not =>
    have hx' : (argumentStates .not sources x).card ≤ 1 := by simp [argumentStates, selectedPins]
    have hy' : (argumentStates .not sources y).card ≤ 1 := by simp [argumentStates, selectedPins]
    split <;> omega
  | and =>
    cases h0 : interpretation .and x <;> cases h1 : interpretation .and y
    · have hx' := and_short sources x h0
      have hy' := and_short sources y h1
      simp only [ite_true]
      omega
    · have hx' := and_short sources x h0
      simp only [Bool.false_eq_true, ite_false]
      omega
    · have hy' := and_short sources y h1
      simp only [Bool.true_eq_false, ite_false]
      omega
    · have hxy : x = y := by
        simp only [interpretation, Bool.and_eq_true] at h0 h1
        funext i
        have h : ∀ a : Fin 2, x a = y a := by
          rw [Fin.forall_fin_two]
          exact ⟨h0.1.trans h1.1.symm, h0.2.trans h1.2.symm⟩
        exact h i
      subst y
      simpa using hx
  | or =>
    cases h0 : interpretation .or x <;> cases h1 : interpretation .or y
    · have hxy : x = y := by
        have bothFalse (z : Fin 2 → Bool) (hz : interpretation .or z = false) :
            z 0 = false ∧ z 1 = false := by
          cases hFirst : z 0 <;> cases hSecond : z 1 <;> simp_all [interpretation]
        have hx' := bothFalse x h0
        have hy' := bothFalse y h1
        funext i
        have h : ∀ a : Fin 2, x a = y a := by
          rw [Fin.forall_fin_two]
          exact ⟨hx'.1.trans hy'.1.symm, hx'.2.trans hy'.2.symm⟩
        exact h i
      subst y
      simpa using hx
    · have hy' := or_short sources y h1
      simp only [Bool.false_eq_true, ite_false]
      omega
    · have hx' := or_short sources x h0
      simp only [Bool.true_eq_false, ite_false]
      omega
    · have hx' := or_short sources x h0
      have hy' := or_short sources y h1
      simp only [ite_true]
      omega

variable {n g : ℕ}

def cornerValue (p : Program signature n g) (b : Bool) (w : Wire n g) : Bool :=
  p.trace interpretation (fun _ => b) w

def cornerArguments (p : Program signature n g) (k : Fin g) (b : Bool) :
    Finset (Wire n g × Bool) :=
  argumentStates (p.lines k).op (p.lines k).wires (fun a => cornerValue p b ((p.lines k).wires a))

theorem cornerValue_gate (p : Program signature n g) (b : Bool) (k : Fin g) :
    cornerValue p b (.gate k) = interpretation (p.lines k).op
      (fun a => cornerValue p b ((p.lines k).wires a)) :=
  p.trace_gate interpretation (fun _ => b) k

/-- Follow the certificates for both constant inputs. A common `(wire, value)` pair is shared. -/
inductive Needed (p : Program signature n g) (root : Wire n g) : Wire n g × Bool → Prop where
  | output : Needed p root (root, true)
  | argument {k : Fin g} {b : Bool} (h : Needed p root (.gate k, cornerValue p b (.gate k)))
      {key : Wire n g × Bool} (ha : key ∈ cornerArguments p k b) : Needed p root key

noncomputable def neededStates (p : Program signature n g) (root : Wire n g) :
    Finset (Wire n g × Bool) := open scoped Classical in Finset.univ.filter (Needed p root)

noncomputable def neededValues (p : Program signature n g) (root : Wire n g) (w : Wire n g) :
    Finset Bool := open scoped Classical in Finset.univ.filter fun b => Needed p root (w, b)

noncomputable def cornerInputs (p : Program signature n g) (root : Wire n g) (b : Bool) :
    Finset (Fin n) := open scoped Classical in Finset.univ.filter fun i => Needed p root (.input i, b)

noncomputable def requestedArguments (p : Program signature n g) (root : Wire n g) (k : Fin g) :
    Finset (Wire n g × Bool) := open scoped Classical in
  (if Needed p root (.gate k, cornerValue p false (.gate k)) then cornerArguments p k false else ∅) ∪
    (if Needed p root (.gate k, cornerValue p true (.gate k)) then cornerArguments p k true else ∅)

private theorem card_requestedArguments_le (p : Program signature n g) (root : Wire n g)
    (k : Fin g) : (requestedArguments p root k).card ≤ (neededValues p root (.gate k)).card + 1 := by
  classical
  let v₀ := cornerValue p false (.gate k)
  let v₁ := cornerValue p true (.gate k)
  let S := neededValues p root (.gate k)
  have hv (b : Bool) : b ∈ S ↔ Needed p root (.gate k, b) := by simp [S, neededValues]
  have hOne (b : Bool) : (cornerArguments p k b).card ≤ 2 := card_argumentStates_le ..
  have hUnion : (cornerArguments p k false ∪ cornerArguments p k true).card ≤
      if v₀ = v₁ then 2 else 3 := by
    have h := union_bound (p.lines k).op (p.lines k).wires
      (fun a => cornerValue p false ((p.lines k).wires a))
      (fun a => cornerValue p true ((p.lines k).wires a))
    simpa only [v₀, v₁, cornerArguments, cornerValue_gate] using h
  change ((if Needed p root (.gate k, v₀) then cornerArguments p k false else ∅) ∪
    (if Needed p root (.gate k, v₁) then cornerArguments p k true else ∅)).card ≤ S.card + 1
  by_cases h0 : Needed p root (.gate k, v₀) <;>
    by_cases h1 : Needed p root (.gate k, v₁) <;> simp [h0, h1]
  · by_cases heq : v₀ = v₁
    · have hcard := Finset.card_pos.mpr ⟨v₀, (hv _).mpr h0⟩
      simp [heq] at hUnion
      omega
    · have hset : ({v₀, v₁} : Finset Bool) ⊆ S := by
        intro b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact (hv _).mpr h0
        · exact (hv _).mpr h1
      have hcard := Finset.card_le_card hset
      simp [heq] at hUnion hcard
      omega
  · have hcard := Finset.card_pos.mpr ⟨v₀, (hv _).mpr h0⟩
    have hh := hOne false
    omega
  · have hcard := Finset.card_pos.mpr ⟨v₁, (hv _).mpr h1⟩
    have hh := hOne true
    omega

noncomputable def stateSet (marked : Wire n g × Bool → Prop) : Finset (Wire n g × Bool) :=
  open scoped Classical in Finset.univ.filter marked

noncomputable def stateValues (marked : Wire n g × Bool → Prop) (w : Wire n g) : Finset Bool :=
  open scoped Classical in Finset.univ.filter fun b => marked (w, b)

noncomputable def stateInputs (marked : Wire n g × Bool → Prop) (b : Bool) : Finset (Fin n) :=
  open scoped Classical in Finset.univ.filter fun i => marked (.input i, b)

/-- Count marked wire states by separating inputs from gates and splitting input values. -/
theorem card_stateSet (marked : Wire n g × Bool → Prop) :
    (stateSet marked).card = (stateInputs marked false).card +
      (stateInputs marked true).card + ∑ k : Fin g, (stateValues marked (.gate k)).card := by
  classical
  let counts := fun w : Wire n g => (stateValues marked w).card
  have hMap : (Finset.univ.sigma (stateValues marked)).map
      (Equiv.sigmaEquivProd (Wire n g) Bool).toEmbedding = stateSet marked := by
    ext key
    rw [Finset.mem_map_equiv]
    simp [Equiv.sigmaEquivProd, stateValues, stateSet]
  have hCard := congrArg Finset.card hMap
  rw [Finset.card_map, Finset.card_sigma] at hCard
  change ∑ w : Wire n g, counts w = (stateSet marked).card at hCard
  have hSplit : ∑ w : Wire n g, counts w = (∑ i : Fin n, counts (.input i)) +
      ∑ k : Fin g, counts (.gate k) := by
    rw [← (Wire.equiv n g).symm.sum_comp counts, Fintype.sum_sum_type]
    rfl
  have hInputs : (∑ i : Fin n, counts (.input i)) =
      (stateInputs marked false).card + (stateInputs marked true).card := by
    simp only [counts, stateValues, stateInputs, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm, Fintype.sum_bool]
    exact Nat.add_comm ..
  rw [← hCard, hSplit, hInputs]

private theorem card_neededStates (p : Program signature n g) (root : Wire n g) :
    (neededStates p root).card = (cornerInputs p root false).card +
      (cornerInputs p root true).card + ∑ k : Fin g, (neededValues p root (.gate k)).card :=
  card_stateSet (Needed p root)

/-- Count a repeated request for the same wire and value only after its first use. -/
noncomputable def repeatedStateRequests (p : Program signature n g) (root : Wire n g) : ℕ :=
  (∑ k : Fin g, (requestedArguments p root k).card) -
    ((Finset.univ : Finset (Fin g)).biUnion (requestedArguments p root)).card

theorem card_cornerInputs_add_reuse_le (p : Program signature n g) (root : Wire n g) :
    (cornerInputs p root false).card + (cornerInputs p root true).card +
      repeatedStateRequests p root ≤ g + 1 := by
  classical
  let allArgs := (Finset.univ : Finset (Fin g)).biUnion (requestedArguments p root)
  have hSub : neededStates p root ⊆ insert (root, true) allArgs := by
    intro key hKey
    have hn := (Finset.mem_filter.mp hKey).2
    cases hn with
    | output => exact Finset.mem_insert_self ..
    | @argument k b hk key ha =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_univ _, ?_⟩
      cases b with
      | false => exact Finset.mem_union_left _ (by simpa [hk] using ha)
      | true => exact Finset.mem_union_right _ (by simpa [hk] using ha)
  have hSize := Finset.card_le_card hSub
  have hDistinct : allArgs.card ≤ ∑ k : Fin g, (requestedArguments p root k).card :=
    Finset.card_biUnion_le
  have hSum : (∑ k : Fin g, (requestedArguments p root k).card) ≤
      ∑ k : Fin g, ((neededValues p root (.gate k)).card + 1) :=
    Finset.sum_le_sum fun k _ => card_requestedArguments_le p root k
  have hInsert := Finset.card_insert_le (root, true) allArgs
  rw [card_neededStates] at hSize
  have hSum' : (∑ k : Fin g, (requestedArguments p root k).card) ≤
      (∑ k : Fin g, (neededValues p root (.gate k)).card) + g := by
    simpa [Finset.sum_add_distrib] using hSum
  change _ + ((∑ k : Fin g, (requestedArguments p root k).card) - allArgs.card) ≤ _
  omega

theorem agrees_on_cornerInputs (p : Program signature n g) (root : Wire n g) (b : Bool)
    (hRoot : cornerValue p b root = true) (x : BitString n)
    (agree : ∀ i ∈ cornerInputs p root b, x i = b) : p.trace interpretation x root = true := by
  classical
  have hTrace : ∀ w, Needed p root (w, cornerValue p b w) →
      p.trace interpretation x w = cornerValue p b w := by
    intro w
    refine p.wire_induction (P := fun w => Needed p root (w, cornerValue p b w) →
      p.trace interpretation x w = cornerValue p b w) ?_ ?_ w
    · intro i hi
      exact agree i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    · intro k ih hk
      rw [p.trace_gate, cornerValue_gate]
      apply agrees_of_selectedPins
      intro a ha
      exact ih a (Needed.argument hk (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
  exact (hTrace root (hRoot.symm ▸ Needed.output)).trans hRoot

end CornerCertificates

open CornerCertificates

private theorem mcspSquare_cornerInputs_bound (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m)))
    (b : Bool) : 2 ^ m ≤ (cornerInputs c.program (c.outputs 0) b).card + descriptionBitBound m := by
  classical
  let fixed := cornerInputs c.program (c.outputs 0) b
  let free := Finset.univ \ fixed
  let center : BitString (2 ^ m) := fun _ => b
  have hCenter : mcspSquare m center = true := mcspSquare_constant_table m hm b
  have hRoot : cornerValue c.program b (c.outputs 0) = true := by
    change c.eval interpretation center 0 = true
    exact (congrFun (hc center) 0).trans hCenter
  have hAll (x : BitString (2 ^ m)) : mcspSquare m (restrictTable center free x) = true := by
    have hTrace := agrees_on_cornerInputs c.program (c.outputs 0) b hRoot
      (restrictTable center free x) (fun i hi => by
        have hNot : i ∉ free := fun h => (Finset.mem_sdiff.mp h).2 hi
        simp [restrictTable, hNot, center])
    change c.eval interpretation (restrictTable center free x) 0 = true at hTrace
    rw [hc] at hTrace
    exact hTrace
  have hEmpty : essentialPositions (fun x => mcspSquare m (restrictTable center free x)) free = ∅ := by
    ext i
    simp [essentialPositions, EssentialAt, hAll]
  have hLoss := mcspSquare_restriction_loss m center free hCenter
  rw [hEmpty, Finset.card_empty, Nat.zero_add] at hLoss
  have hSplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ fixed)
  simp only [Finset.card_univ, Fintype.card_fin] at hSplit
  change free.card + fixed.card = 2 ^ m at hSplit
  change 2 ^ m ≤ fixed.card + descriptionBitBound m
  omega

/-- A two-certificate lower bound for every circuit deciding the quadratic MCSP slice. -/
theorem mcspSquare_two_certificate_size_bound (m : ℕ) (hm : 1 ≤ m)
    (c : Circuit signature (2 ^ m) 1) (hc : c.Computes interpretation (single (mcspSquare m))) :
    2 * 2 ^ m + repeatedStateRequests c.program (c.outputs 0) ≤
      c.size + 1 + 2 * descriptionBitBound m := by
  have h0 := mcspSquare_cornerInputs_bound m hm c hc false
  have h1 := mcspSquare_cornerInputs_bound m hm c hc true
  have hSum := card_cornerInputs_add_reuse_le c.program (c.outputs 0)
  omega

/-- Near twice the truth-table length, with an explicit loss of order `m^2 log m`. -/
theorem mcspSquare_two_certificate_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    2 * 2 ^ m ≤ complexity interpretation (single (mcspSquare m)) +
      1 + 2 * descriptionBitBound m := by
  obtain ⟨c, hc, hSize⟩ := exists_computes_size_eq_complexity
    (I := interpretation) (f := single (mcspSquare m))
  have h := mcspSquare_two_certificate_size_bound m hm c hc
  omega

theorem mcspSquare_sixteen_lower_bound :
    119255 ≤ complexity interpretation (single (mcspSquare 16)) := by
  have h := mcspSquare_two_certificate_lower_bound 16 (by decide)
  have hBits : descriptionBitBound 16 = 5908 := by decide
  rw [hBits] at h
  omega

end PvsNP.Frontier
