import PEqualNP.Outside.L_meta_168
import PEqualNP.Outside.L_meta_169
import PEqualNP.Outside.L_meta_170
import PEqualNP.Outside.L_meta_171
import PEqualNP.Outside.L_meta_175
import PEqualNP.Outside.L_meta_176

/-! Tight one-bit restrictions and equality probes in Brilliant's circuit model. -/

namespace PvsNP.PEqualNPAudit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ReadsInput {n : ℕ} (C : Circuit) (j : Fin C.gates.length) (i : Fin n) : Prop :=
  let g := C.gates.get j
  (g.op = .not ∧ g.inputs.head? = some i.val) ∨
    (g.op ≠ .not ∧ i.val ∈ g.inputs)

def DependsOnLast {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) : Prop :=
  ∃ y : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y true)

def PinLast {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) : (Fin n → Bool) → Bool :=
  fun y => f (Fin.snoc y b)

def HasForcedReader {n : ℕ} (C : Circuit) (b : Bool) : Prop :=
  ∃ j : Fin C.gates.length, ReadsInput C j (Fin.last n) ∧
    (∀ k : Fin C.gates.length, ReadsInput C k (Fin.last n) → k = j) ∧
    (C.gates.get j).op = (if b then GateOp.and else GateOp.or) ∧
    (C.gates.get j).inputs.length = 2 ∧
    ∃ w ∈ (C.gates.get j).inputs, w ≠ n ∧ w < n + 1 + j.val

/-- A cofactor lower bound within one gate of a minimum circuit fixes the only reader. -/
theorem forced_reader_of_pin_bound {n L : ℕ} {C : Circuit} {b : Bool}
    (hmin : IsMinimalCircuit (n + 1) C) (hdep : DependsOnLast (circuitFun (n + 1) C))
    (hnc : ∃ y y', PinLast (circuitFun (n + 1) C) b y ≠ PinLast (circuitFun (n + 1) C) b y')
    (hsize : C.size ≤ L + 1)
    (hlower : ∀ s, HasCircuitSize n (PinLast (circuitFun (n + 1) C) b) s → L ≤ s) :
    HasForcedReader (n := n) C b := by
  have tight (s : ℕ) (hs : HasCircuitSize n (PinLast (circuitFun (n + 1) C) b) s) :
      C.size ≤ s + 1 := by
    have h := hlower s hs
    omega
  cases b with
  | false =>
    obtain ⟨j, hj, hu⟩ := PEqualNP.Outside.L_meta_168 n C hmin hdep hnc tight
    obtain ⟨hop, hlen, _, hw⟩ := PEqualNP.Outside.L_meta_169 n C hmin hdep hnc tight j hj
    exact ⟨j, hj, hu, hop, hlen, hw⟩
  | true =>
    obtain ⟨j, hj, hu⟩ := PEqualNP.Outside.L_meta_170 n C hmin hdep hnc tight
    obtain ⟨hop, hlen, _, hw⟩ := PEqualNP.Outside.L_meta_171 n C hmin hdep hnc tight j hj
    exact ⟨j, hj, hu, hop, hlen, hw⟩

/-- Replace the last input with an AND (true mode) or OR (false mode) of two copies. -/
def duplicateLast {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool)
    (x : Fin (n + 2) → Bool) : Bool :=
  f (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc)
    (if b then x (Fin.last n).castSucc && x (Fin.last (n + 1))
     else x (Fin.last n).castSucc || x (Fin.last (n + 1))))

@[simp] theorem duplicateLast_neutral {n : ℕ} (f : (Fin (n + 1) → Bool) → Bool) (b : Bool)
    (y : Fin (n + 1) → Bool) : duplicateLast f b (Fin.snoc y b) = f y := by
  have hy : Fin.snoc (fun i : Fin n => y i.castSucc) (y (Fin.last n)) = y := by
    funext j
    refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp
  cases b <;> simp [duplicateLast, hy]

theorem duplicateLast_size_iff {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (hdep : DependsOnLast f) (b : Bool) :
    HasCircuitSize (n + 2) (duplicateLast f b) (s + 1) ↔ HasCircuitSize (n + 1) f s := by
  cases b
  · exact PEqualNP.Outside.L_meta_176 n s f hdep
  · exact PEqualNP.Outside.L_meta_175 n s f hdep

theorem duplicateLast_forces_reader {n s : ℕ} {f : (Fin (n + 1) → Bool) → Bool}
    (hdep : DependsOnLast f) (b : Bool) (hf : HasCircuitSize (n + 1) f s)
    (hlower : ∀ t, HasCircuitSize (n + 1) f t → s ≤ t) {C : Circuit}
    (hmin : IsMinimalCircuit (n + 2) C) (hfun : circuitFun (n + 2) C = duplicateLast f b) :
    HasForcedReader (n := n + 1) C b := by
  apply forced_reader_of_pin_bound (L := s) hmin
  · rw [hfun]
    obtain ⟨y, hy⟩ := hdep
    refine ⟨Fin.snoc y b, ?_⟩
    cases b <;> simpa [duplicateLast] using hy
  · rw [hfun]
    obtain ⟨y, hy⟩ := hdep
    exact ⟨Fin.snoc y false, Fin.snoc y true, by simpa [PinLast] using hy⟩
  · obtain ⟨D, hD, hsize, heval⟩ := (duplicateLast_size_iff hdep b).mpr hf
    exact (hmin.2 D hD ((funext heval).trans hfun.symm)).trans hsize
  · intro t ht
    rw [hfun] at ht
    have hpin : PinLast (duplicateLast f b) b = f := funext (duplicateLast_neutral f b)
    exact hlower t (hpin ▸ ht)

def spliceInputs {n : ℕ} (mask x y : Fin n → Bool) : Fin n → Bool :=
  fun i => if mask i then x i else y i

/-- A forced input reader can coexist with any equality restriction of the original function.
Fix the new input to the neutral value for all probes. -/
theorem duplicateLast_preserves_equality {n : ℕ} {ι : Type*}
    {f : (Fin (n + 1) → Bool) → Bool} (b side : Bool)
    (mask : Fin (n + 1) → Bool) (probe : ι → Fin (n + 1) → Bool)
    (heq : ∀ u v, f (spliceInputs mask (probe u) (probe v)) = true ↔ u = v) :
    ∀ u v, duplicateLast f b
      (spliceInputs (Fin.snoc mask side) (Fin.snoc (probe u) b) (Fin.snoc (probe v) b)) = true ↔
      u = v := by
  intro u v
  have h : spliceInputs (Fin.snoc mask side) (Fin.snoc (probe u) b) (Fin.snoc (probe v) b) =
      Fin.snoc (spliceInputs mask (probe u) (probe v)) b := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [spliceInputs]
    · simp [spliceInputs]
  rw [h, duplicateLast_neutral]
  exact heq u v

/-- Any cut signature sound for the duplicated equality probes has at least
enough bits to distinguish the full probe family. -/
theorem duplicateLast_cut_signature_lower {n w : ℕ} {ι : Type*} [Fintype ι]
    {f : (Fin (n + 1) → Bool) → Bool} (b side : Bool)
    (mask : Fin (n + 1) → Bool) (probe : ι → Fin (n + 1) → Bool)
    (heq : ∀ u v, f (spliceInputs mask (probe u) (probe v)) = true ↔ u = v)
    (signature : ι → Fin w → Bool)
    (sound : ∀ u v, signature u = signature v → duplicateLast f b
      (spliceInputs (Fin.snoc mask side) (Fin.snoc (probe u) b) (Fin.snoc (probe v) b)) = true) :
    Fintype.card ι ≤ 2 ^ w := by
  have hinj : Function.Injective signature := fun {_ _} h =>
    (duplicateLast_preserves_equality b side mask probe heq _ _).mp (sound _ _ h)
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    Fintype.card_le_of_injective signature hinj

#print axioms forced_reader_of_pin_bound
#print axioms duplicateLast_forces_reader
#print axioms duplicateLast_preserves_equality
#print axioms duplicateLast_cut_signature_lower

end PvsNP.PEqualNPAudit
