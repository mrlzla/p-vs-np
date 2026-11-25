module

public import MCSPMatchedCharge

/-! Relabel represented variables and transport cuts inside one decision circuit. -/

@[expose] public section

namespace PvsNP.Frontier.PermutedCut

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut Downstream MatchedSignals

variable {m n g r s : ℕ}

/-- Permuting the coordinates of an assignment is an equivalence. -/
def permuteAssignment (e : Equiv.Perm (Fin m)) : Equiv.Perm (BitString m) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := funext fun i => by simp
  right_inv x := funext fun i => by simp

/-- Reindex truth-table entries by permuting the represented variables. -/
def tablePerm (e : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (2 ^ m)) :=
  (BitString.equivFin m).symm.trans ((permuteAssignment e).trans (BitString.equivFin m))

theorem tablePerm_at_assignment (e : Equiv.Perm (Fin m)) (x : BitString m) :
    tablePerm e (BitString.equivFin m x) = BitString.equivFin m (x ∘ e) := by
  simp [tablePerm, permuteAssignment]

theorem complexity_comp_perm (e : Equiv.Perm (Fin m)) (f : BooleanFunction m) :
    complexity interpretation (single fun x => f (x ∘ e)) =
      complexity interpretation (single f) := by
  have upper (e' : Equiv.Perm (Fin m)) (f' : BooleanFunction m) :
      complexity interpretation (single fun x => f' (x ∘ e')) ≤ complexity interpretation (single f') := by
    obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity
      (I := interpretation) (f := single f')
    let d := c.comp (Circuit.wiring signature e')
    have hd : d.Computes interpretation (single fun x => f' (x ∘ e')) := by
      intro x
      rw [show d.eval interpretation x = c.eval interpretation (x ∘ e') by
        simp [d, Circuit.eval_comp, Circuit.eval_wiring, Function.comp_def]]
      exact hc _
    exact (complexity_le_of_computes d hd).trans (by simpa [d, Circuit.size_comp] using hsize.le)
  apply le_antisymm (upper e f)
  have h := upper e.symm (fun x => f (x ∘ e))
  have heq : (fun x : BitString m => f ((x ∘ e.symm) ∘ e)) = f := by
    funext x
    congr 1
    funext i
    simp
  rwa [heq] at h

theorem square_comp_tablePerm (e : Equiv.Perm (Fin m)) (T : BitString (2 ^ m)) :
    mcspSquare m (T ∘ tablePerm e) = mcspSquare m T := by
  apply Bool.eq_iff_iff.mpr
  simp only [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff]
  have hf : (MCSP.truthTable m).symm (T ∘ tablePerm e) =
      fun x => (MCSP.truthTable m).symm T (x ∘ e) := by
    funext x
    change T (tablePerm e (BitString.equivFin m x)) = T (BitString.equivFin m (x ∘ e))
    rw [tablePerm_at_assignment]
  rw [hf, complexity_comp_perm]

/-- Lift a tail permutation that leaves all prefix coordinates fixed. -/
def liftTail (r : ℕ) (e : Equiv.Perm (Fin (s + 1))) : Equiv.Perm (Fin (r + (s + 1))) :=
  finSumFinEquiv.symm.trans (((Equiv.refl (Fin r)).sumCongr e).trans finSumFinEquiv)

@[simp] theorem liftTail_left (e : Equiv.Perm (Fin (s + 1))) (i : Fin r) :
    liftTail r e (Fin.castAdd (s + 1) i) = Fin.castAdd (s + 1) i := by
  simp [liftTail, ← finSumFinEquiv_apply_left]

@[simp] theorem liftTail_right (e : Equiv.Perm (Fin (s + 1))) (i : Fin (s + 1)) :
    liftTail r e (Fin.natAdd r i) = Fin.natAdd r (e i) := by
  simp [liftTail, ← finSumFinEquiv_apply_right]

theorem append_comp_liftTail (e : Equiv.Perm (Fin (s + 1))) (a : BitString r) (t : BitString (s + 1)) :
    Fin.append a t ∘ liftTail r e = Fin.append a (t ∘ e) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Function.comp_def]

/-- Index zero is the original split. Index j.succ exchanges it with suffix bit j. -/
def splitSwap (r : ℕ) (j : Fin (s + 1)) : Equiv.Perm (Fin (r + (s + 1))) :=
  liftTail r (Equiv.swap 0 j)

def orbitMask (h : BooleanFunction s) (j : Fin (s + 1)) : BitString (2 ^ (r + (s + 1))) :=
  mask r h ∘ tablePerm (splitSwap r j)

/-- Pull back the labels as well as the cut. The decision circuit stays fixed. -/
theorem transport_equality {ι : Type*} (f : BooleanFunction n) (e : Equiv.Perm (Fin n))
    (hinv : ∀ T, f (T ∘ e) = f T) (σ : BitString n) (ℓ : Fin n → ι)
    (hEq : ∀ a b : ι → Bool, f (splice σ (a ∘ ℓ) (b ∘ ℓ)) = true ↔ a = b) :
    ∀ a b : ι → Bool, f (splice (σ ∘ e) (a ∘ (ℓ ∘ e)) (b ∘ (ℓ ∘ e))) = true ↔ a = b := by
  intro a b
  change f ((splice σ (a ∘ ℓ) (b ∘ ℓ)) ∘ e) = true ↔ _
  rw [hinv]
  exact hEq a b

theorem orbitMask_balanced (h : BooleanFunction s) (j : Fin (s + 1)) (b : Bool) :
    (Finset.univ.filter (fun i => orbitMask (r := r) h j i = b)).card = 2 ^ (r + s) := by
  classical
  let e := tablePerm (splitSwap r j)
  have he :
      (Finset.univ.filter (fun i => orbitMask (r := r) h j i = b)).map e.toEmbedding =
        Finset.univ.filter (fun i => mask r h i = b) := by
    ext i
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
    change mask r h (e (e.symm i)) = b ↔ _
    rw [e.apply_symm_apply]
  rw [← Finset.card_map (f := e.toEmbedding), he, card_mask_side]

theorem exact32_orbit_matchings (h : BooleanFunction 22)
    (hEq : ∀ f g : RefinedCut.Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g)
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (mcspSquare 32)))
    (owners : Fin 23 → Wire (2 ^ 32) c.size → Bool)
    (howners : ∀ j i, owners j (.input i) = orbitMask (r := 9) h j i) :
    ∃ matchWire : Fin 23 → RefinedCut.Coordinate → Wire (2 ^ 32) c.size,
      ∀ j, Function.Injective (matchWire j) ∧ ∀ a,
        matchWire j a ∈ varyingSources c.program (owners j)
          (RefinedCut.label ∘ tablePerm (splitSwap 9 j)) a := by
  classical
  have hmatch (j : Fin 23) :=
    exists_varying_matching (mcspSquare 32) (RefinedCut.label ∘ tablePerm (splitSwap 9 j))
      (orbitMask (r := 9) h j) c hc
      (transport_equality _ _ (square_comp_tablePerm (splitSwap 9 j)) (mask 9 h) _ hEq)
      (owners j) (howners j)
  exact ⟨fun j => (hmatch j).choose, fun j => (hmatch j).choose_spec⟩

private theorem varying_matching_width {ι : Type*} [Fintype ι]
    (p : Program signature n g) (owner : Wire n g → Bool) (label : Fin n → ι)
    (choose : ι → Wire n g) (hinj : Function.Injective choose)
    (hw : ∀ a, choose a ∈ varyingSources p owner label a) :
    Fintype.card ι ≤ (crossingWires p owner).card := by
  classical
  have h := Finset.card_le_card_of_injOn (s := Finset.univ) choose (t := crossingWires p owner)
    (fun a _ => (Finset.mem_filter.mp (hw a)).1) hinj.injOn
  rwa [Finset.card_univ] at h

theorem exact32_orbit_width (h : BooleanFunction 22)
    (hEq : ∀ f g : RefinedCut.Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g)
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (mcspSquare 32)))
    (owners : Fin 23 → Wire (2 ^ 32) c.size → Bool)
    (howners : ∀ j i, owners j (.input i) = orbitMask (r := 9) h j i) :
    ∀ j, 544 ≤ (crossingWires c.program (owners j)).card := by
  obtain ⟨choose, hm⟩ := exact32_orbit_matchings h hEq c hc owners howners
  intro j
  have hw := varying_matching_width c.program (owners j) _ (choose j) (hm j).1 (hm j).2
  rw [Fintype.card_sum, BitString.card, BitString.card] at hw
  exact hw

theorem exact32_orbit_input_matchings (h : BooleanFunction 22)
    (hEq : ∀ f g : RefinedCut.Coordinate → Bool,
      mcspSquare 32 (splice (mask 9 h) (f ∘ RefinedCut.label) (g ∘ RefinedCut.label)) = true ↔ f = g)
    (c : Circuit signature (2 ^ 32) 1) (hc : c.Computes interpretation (single (mcspSquare 32))) :
    ∃ matchWire : Fin 23 → RefinedCut.Coordinate → Wire (2 ^ 32) c.size,
      ∀ j, Function.Injective (matchWire j) ∧ ∀ a,
        (∃ i, matchWire j a = .input i) ∧
        matchWire j a ∈ varyingSources c.program
          (Wire.elim (orbitMask (r := 9) h j) (fun _ => true))
          (RefinedCut.label ∘ tablePerm (splitSwap 9 j)) a := by
  classical
  let owners (j : Fin 23) : Wire (2 ^ 32) c.size → Bool :=
    Wire.elim (orbitMask (r := 9) h j) (fun _ => true)
  obtain ⟨matchWire, hmatch⟩ := exact32_orbit_matchings h hEq c hc owners (fun _ _ => rfl)
  refine ⟨matchWire, fun j => ⟨(hmatch j).1, fun a => ⟨?_, (hmatch j).2 a⟩⟩⟩
  have hw := (hmatch j).2 a
  obtain ⟨k, pin, _, hcross⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
  cases he : matchWire j a with
  | input i => exact ⟨i, rfl⟩
  | gate l => exact (hcross (by rw [he]; rfl)).elim

/-- Counting the union of matched sources on the pooled certificates is bounded by
the earlier global net margin, even with different owners on every cut. -/
theorem pooled_margin_le_original {α : Type*} (p : Program signature n g) (root : Wire n g)
    (core pooled : Finset (BitString n)) (h : core ⊆ pooled) (cuts : Finset α)
    (sources : α → Finset (Wire n g)) :
    MatchedCharge.matchedMargin p root pooled (cuts.biUnion sources) ≤
      MultiCertificates.netMargin p root core :=
  (MatchedCharge.matchedMargin_le ..).trans (MultiCertificates.netMargin_antitone p root h)

theorem pooled_margin_add_new_input_states (p : Program signature n g) (root : Wire n g)
    (core pooled : Finset (BitString n)) (h : core ⊆ pooled) :
    MultiCertificates.netMargin p root pooled +
        ((MultiCertificates.inputStates p root pooled false \
          MultiCertificates.inputStates p root core false).card : ℤ) +
        ((MultiCertificates.inputStates p root pooled true \
          MultiCertificates.inputStates p root core true).card : ℤ) =
      MultiCertificates.netMargin p root core := by
  classical
  have hcard (b : Bool) := Finset.card_sdiff_add_card_eq_card
    (MultiCertificates.inputStates_mono p root h b)
  rw [MultiCertificates.netMargin_eq, MultiCertificates.netMargin_eq]
  have h0 := hcard false
  have h1 := hcard true
  omega

noncomputable def probePool {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] (labels : κ → Fin n → ι) :
    Finset (BitString n) := open scoped Classical in
  Finset.univ.biUnion (fun k => (Finset.univ : Finset (ι → Bool)).image (fun f => f ∘ labels k))

theorem constant_mem_probePool {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (labels : κ → Fin n → ι) (k : κ) (b : Bool) :
    (fun _ => b) ∈ probePool labels := by
  classical
  unfold probePool
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_image.mpr
    ⟨fun _ => b, Finset.mem_univ _, rfl⟩⟩

theorem probePool_accepts {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (labels : κ → Fin n → ι) (f : BooleanFunction n)
    (accept : ∀ k (a : ι → Bool), f (a ∘ labels k) = true)
    (T : BitString n) (ht : T ∈ probePool labels) : f T = true := by
  classical
  unfold probePool at ht
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hk
  exact accept k a

theorem probePool_charge_le_corners {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (p : Program signature n g) (root : Wire n g)
    (labels : κ → Fin n → ι) (k : κ) (sources : κ → Finset (Wire n g)) :
    MatchedCharge.matchedMargin p root (probePool labels)
        (Finset.univ.biUnion sources) ≤
      MultiCertificates.netMargin p root (MultiCertificates.constantProbes n) := by
  classical
  apply pooled_margin_le_original
  intro x hx
  simp only [MultiCertificates.constantProbes, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact constant_mem_probePool labels k _
  · exact constant_mem_probePool labels k _

#print axioms square_comp_tablePerm
#print axioms exact32_orbit_matchings
#print axioms exact32_orbit_width
#print axioms exact32_orbit_input_matchings
#print axioms pooled_margin_le_original
#print axioms pooled_margin_add_new_input_states
#print axioms probePool_charge_le_corners

end PvsNP.Frontier.PermutedCut
