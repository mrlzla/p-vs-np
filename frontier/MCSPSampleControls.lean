module

public import Complexity.Computability.Circuit.Boolean.Synthesis

/-! Small prescribed sets of accepting tables have circuits of size close to twice the table
length. This is a control for arguments based on a bounded number of accepting samples. -/

@[expose] public section

namespace PvsNP.Frontier.SampleControls

open Cslib Cslib.Circuits Cslib.Circuits.Boolean

variable {n : ℕ}

abbrev SignatureOf (sample : Finset (BitString n)) := sample → Bool

def coordinateSignature (sample : Finset (BitString n)) (i : Fin n) : SignatureOf sample :=
  fun x => x.val i

noncomputable def group (sample : Finset (BitString n)) (key : SignatureOf sample) :
    Finset (Fin n) := open scoped Classical in
  Finset.univ.filter fun i => coordinateSignature sample i = key

noncomputable def readGroup (sample : Finset (BitString n)) (key : SignatureOf sample)
    (x : BitString n) : Bool := open scoped Classical in
  if h : (group sample key).Nonempty then x h.choose else false

noncomputable def agreesOn (positions : Finset (Fin n)) (x : BitString n) : Bool :=
  open scoped Classical in
  decide (∀ i ∈ positions, x i = true) || !(decide (∃ i ∈ positions, x i = true))

noncomputable def groupAgrees (sample : Finset (BitString n)) (key : SignatureOf sample)
    (x : BitString n) : Bool := agreesOn (group sample key) x

theorem agreesOn_eq_true (positions : Finset (Fin n)) (x : BitString n) :
    agreesOn positions x = true ↔ ∀ i ∈ positions, ∀ j ∈ positions, x i = x j := by
  classical
  unfold agreesOn
  by_cases h : ∃ i ∈ positions, x i = true
  · obtain ⟨i, hi, hxi⟩ := h
    have hSome : ∃ i ∈ positions, x i = true := ⟨i, hi, hxi⟩
    simp only [hSome, decide_true, Bool.not_true, Bool.or_false, decide_eq_true_eq]
    exact ⟨fun hh j hj k hk => (hh j hj).trans (hh k hk).symm,
      fun hh j hj => (hh j hj i hi).trans hxi⟩
  · simp only [h, decide_false, Bool.not_false, Bool.or_true, true_iff]
    intro i hi j hj
    have h0 (k : Fin n) (hk : k ∈ positions) : x k = false := by
      cases hBit : x k with
      | false => rfl
      | true => exact (h ⟨k, hk, hBit⟩).elim
    exact (h0 i hi).trans (h0 j hj).symm

theorem groupAgrees_eq_true (sample : Finset (BitString n)) (key : SignatureOf sample)
    (x : BitString n) : groupAgrees sample key x = true ↔
      ∀ i ∈ group sample key, ∀ j ∈ group sample key, x i = x j :=
  agreesOn_eq_true (group sample key) x

noncomputable def matchesRow (sample : Finset (BitString n)) (row x : BitString n) : Bool :=
  open scoped Classical in decide (∀ key : SignatureOf sample, readGroup sample key x = readGroup sample key row)

noncomputable def sampleRecognizer (sample : Finset (BitString n)) (x : BitString n) : Bool :=
  open scoped Classical in
  decide (∀ key : SignatureOf sample, groupAgrees sample key x = true) &&
    decide (∃ row ∈ sample, matchesRow sample row x = true)

theorem sampleRecognizer_accepts_exactly (sample : Finset (BitString n)) (x : BitString n) :
    sampleRecognizer sample x = true ↔ x ∈ sample := by
  classical
  have rowAgrees (row : BitString n) (hr : row ∈ sample) (key : SignatureOf sample)
      (i j : Fin n) (hi : i ∈ group sample key) (hj : j ∈ group sample key) : row i = row j := by
    exact congrFun ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) ⟨row, hr⟩
  simp only [sampleRecognizer, Bool.and_eq_true, decide_eq_true_eq, matchesRow]
  constructor
  · rintro ⟨hGroups, row, hr, hMatch⟩
    have heq : x = row := by
      funext i
      let key := coordinateSignature sample i
      have hi : i ∈ group sample key := by simp [group, key]
      have hne : (group sample key).Nonempty := ⟨i, hi⟩
      have hmi := hMatch key
      rw [readGroup, dite_eq_left hne, readGroup, dite_eq_left hne] at hmi
      exact ((groupAgrees_eq_true sample key x).mp (hGroups key) i hi hne.choose
        hne.choose_spec).trans (hmi.trans (rowAgrees row hr key hne.choose i hne.choose_spec hi))
    exact heq ▸ hr
  · intro hx
    exact ⟨fun key => (groupAgrees_eq_true sample key x).mpr
      (fun i hi j hj => rowAgrees x hx key i j hi hj), x, hx, fun _ => rfl⟩

private theorem synth_projection (i : Fin n) :
    Synthesis interpretation (inputs n) {fun x => x i} 0 := Synthesis.of_mem ⟨i, rfl⟩

theorem agreesOn_cost (positions : Finset (Fin n)) :
    Synthesis interpretation (inputs n) {agreesOn positions} (2 * positions.card + 4) := by
  classical
  have hTrue := Synthesis.forall_mem positions (fun i (x : BitString n) => x i) (fun _ => 0)
    (fun i _ => synth_projection i)
  have hSome := Synthesis.exists_mem positions (fun i (x : BitString n) => x i) (fun _ => 0)
    (fun i _ => synth_projection i)
  have h := Synthesis.congr_iff (hTrue.or hSome.not) (g := agreesOn positions)
    (fun x => by simp [agreesOn])
  apply h.mono Set.Subset.rfl Set.Subset.rfl
  simp
  omega

private theorem groupAgrees_cost (sample : Finset (BitString n)) (key : SignatureOf sample) :
    Synthesis interpretation (inputs n) {groupAgrees sample key}
      (2 * (group sample key).card + 4) := agreesOn_cost _

private theorem readGroup_cost (sample : Finset (BitString n)) (key : SignatureOf sample) :
    Synthesis interpretation (inputs n) {readGroup sample key} 1 := by
  classical
  by_cases h : (group sample key).Nonempty
  · apply Synthesis.congr_iff
      ((synth_projection h.choose).mono Set.Subset.rfl Set.Subset.rfl (show 0 ≤ 1 by decide))
    intro x
    rw [readGroup, dite_eq_left h]
  · apply Synthesis.congr_iff (Synthesis.const (s := inputs n) false)
    intro x
    simp [readGroup, h]

private theorem matchesRow_cost (sample : Finset (BitString n)) (row : BitString n) :
    Synthesis interpretation (inputs n) {matchesRow sample row} (3 * 2 ^ sample.card + 1) := by
  classical
  let bits (key : SignatureOf sample) (x : BitString n) :=
    decide (readGroup sample key x = readGroup sample key row)
  have hBit (key : SignatureOf sample) : Synthesis interpretation (inputs n) {bits key} 2 := by
    have h := readGroup_cost sample key
    cases hb : readGroup sample key row
    · apply Synthesis.congr_iff h.not
      intro x
      simp [bits, hb]
    · apply Synthesis.congr_iff (h.mono Set.Subset.rfl Set.Subset.rfl (show 1 ≤ 2 by decide))
      intro x
      simp [bits, hb]
  have hAll := Synthesis.forall_mem Finset.univ bits (fun _ => 2) (fun i _ => hBit i)
  have h := Synthesis.congr_iff hAll (g := matchesRow sample row)
    (fun x => by simp [bits, matchesRow])
  exact h.mono Set.Subset.rfl Set.Subset.rfl (by simp [Nat.mul_comm])

private theorem sum_card_group (sample : Finset (BitString n)) :
    (∑ key : SignatureOf sample, (group sample key).card) = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (SignatureOf sample))) (f := coordinateSignature sample)
    (fun _ _ => Finset.mem_univ _)
  simpa [group] using h.symm

/-- Any prescribed sample of `t` accepted tables is itself recognized using `2n + O(t 2^t)`
De Morgan gates. The circuit first checks that bits with the same sample signature agree. -/
theorem sampleRecognizer_size_bound (sample : Finset (BitString n)) :
    complexity interpretation (single (sampleRecognizer sample)) ≤
      2 * n + 5 * 2 ^ sample.card + sample.card * (3 * 2 ^ sample.card + 2) + 3 := by
  classical
  have hGroups := Synthesis.forall_mem Finset.univ (groupAgrees sample)
    (fun key => 2 * (group sample key).card + 4) (fun key _ => groupAgrees_cost sample key)
  have hRows := Synthesis.exists_mem sample (matchesRow sample)
    (fun _ => 3 * 2 ^ sample.card + 1) (fun row _ => matchesRow_cost sample row)
  apply (hGroups.and hRows).complexity_le.trans
  simp [Nat.add_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, sum_card_group, Nat.mul_comm]
  omega

end PvsNP.Frontier.SampleControls
