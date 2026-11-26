module

public import PvsNP.BlockContraction
public import PvsNP.BranchingCompression

@[expose] public section

/-!
# Automatic Stride-`h` Block Contraction & Hybrid Cut Contraction

Compiles any fan-in-2 Boolean circuit (`Circuit n w`) automatically into a `2 ^ h`-input
`BlockCircuit` by partitioning topological binary (`AND`/`OR`) depth into stride-`h` residue
buckets and picking an optimal phase offset `r : Fin h` by pigeonhole:
1. **Binary Depth & Wire Span (`wireDepth`, `maxBinaryReaderDepth`, `wireSpan`)**: tracks binary
   topological depth (ignoring unary `.not` layers) and each wire's forward span to its furthest
   binary reader.
2. **Residue Pigeonhole (`exists_stride_residue_le`, `totalTruncatedSpan_layered_le`)**: for every
   stride `h ≥ 1`, averaging over `r : Fin h` selects a phase with at most
   `totalTruncatedSpan c h / h` crossing gate wires (`≤ c.gateCount / h` for unit-span layered
   circuits).
3. **Automatic Stride-`h` Compiler (`compileStride`, `strideCertificate`,
   `stride_contraction_subexponential`)**: produces `BlockContractionCertificate source (2 ^ h)`
   with exact model preservation (`#SAT` and `SAT`) and `≤ totalTruncatedSpan source.circuit h / h + 1`
   blocks.
4. **Hybrid Cut + Stride Contraction (`HybridBlockCertificate`, `hybridOfCutStride`,
   `hybrid_block_subexponential`)**: conditions on an `o(n)` wire cut (breaking long-span skip
   wires) and runs automatic stride-`h` block contraction on each residual circuit.
5. **Automatic Layered Witness (`LayeredRing`)**: synchronous `D`-layer cyclic ring circuit where
   `strideCertificate` yields an unconditional factor-`h` variable reduction (`≤ D * n / h + 1`)
   with no manual block partitioning.
-/

namespace PvsNP

open Std.Sat (CNF)
open Asymptotics Filter

/-! ### 1. Topological Binary Depth & Wire Span -/

theorem Circuit.inputs_pos_of_wire {n : Nat} : {w : Nat} → Circuit n w → Fin w → 0 < n
  | _, .inputsOnly, u => Nat.lt_of_le_of_lt (Nat.zero_le u.val) u.isLt
  | _, .snoc earlier (.not a), _ => earlier.inputs_pos_of_wire a
  | _, .snoc earlier (.and a _), _ => earlier.inputs_pos_of_wire a
  | _, .snoc earlier (.or a _), _ => earlier.inputs_pos_of_wire a

theorem Circuit.inputs_le_wires {n : Nat} : {w : Nat} → Circuit n w → n ≤ w
  | _, c => by
    have hw := c.wire_count
    omega

/-- Binary (`AND`/`OR`) topological depth of wire `u` in `c`. Unary `.not` gates inherit their
input's binary depth. -/
def wireDepth {n : Nat} : {w : Nat} → Circuit n w → Fin w → Nat
  | _, .inputsOnly, _ => 0
  | _, .snoc earlier (.not a), u =>
    Fin.lastCases (wireDepth earlier a) (wireDepth earlier) u
  | _, .snoc earlier (.and a b), u =>
    Fin.lastCases (max (wireDepth earlier a) (wireDepth earlier b) + 1) (wireDepth earlier) u
  | _, .snoc earlier (.or a b), u =>
    Fin.lastCases (max (wireDepth earlier a) (wireDepth earlier b) + 1) (wireDepth earlier) u

@[simp] theorem wireDepth_inputsOnly {n : Nat} (u : Fin n) :
    wireDepth (Circuit.inputsOnly : Circuit n n) u = 0 := rfl

@[simp] theorem wireDepth_snoc_not_last {n w : Nat} (c : Circuit n w) (a : Fin w) :
    wireDepth (c.snoc (.not a)) (Fin.last w) = wireDepth c a := by
  simp [wireDepth]

@[simp] theorem wireDepth_snoc_and_last {n w : Nat} (c : Circuit n w) (a b : Fin w) :
    wireDepth (c.snoc (.and a b)) (Fin.last w) = max (wireDepth c a) (wireDepth c b) + 1 := by
  simp [wireDepth]

@[simp] theorem wireDepth_snoc_or_last {n w : Nat} (c : Circuit n w) (a b : Fin w) :
    wireDepth (c.snoc (.or a b)) (Fin.last w) = max (wireDepth c a) (wireDepth c b) + 1 := by
  simp [wireDepth]

@[simp] theorem wireDepth_snoc_castSucc {n w : Nat} (c : Circuit n w) (g : Gate w) (q : Fin w) :
    wireDepth (c.snoc g) q.castSucc = wireDepth c q := by
  cases g <;> simp [wireDepth]

theorem wireDepth_input_eq_zero {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (u : Fin w) → u.val < n → wireDepth c u = 0
  | _, .inputsOnly, _, _ => rfl
  | _, .snoc earlier g, u, hu => by
    cases u using Fin.lastCases with
    | last =>
      have hge := earlier.inputs_le_wires
      simp only [Fin.val_last] at hu
      omega
    | cast q =>
      rw [wireDepth_snoc_castSucc]
      exact wireDepth_input_eq_zero earlier q (by simpa using hu)

/-- Maximum of wire `u`'s own binary depth and the binary depths of all binary (`AND`/`OR`) gates
that read `u`. -/
def maxBinaryReaderDepth {n : Nat} : {w : Nat} → Circuit n w → Fin w → Nat
  | _, .inputsOnly, _ => 0
  | _, .snoc earlier (.not a), u =>
    Fin.lastCases (wireDepth earlier a) (maxBinaryReaderDepth earlier) u
  | _, .snoc earlier (.and a b), u =>
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    Fin.lastCases d
      (fun q => if q = a ∨ q = b then max (maxBinaryReaderDepth earlier q) d
        else maxBinaryReaderDepth earlier q) u
  | _, .snoc earlier (.or a b), u =>
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    Fin.lastCases d
      (fun q => if q = a ∨ q = b then max (maxBinaryReaderDepth earlier q) d
        else maxBinaryReaderDepth earlier q) u

@[simp] theorem maxBinaryReaderDepth_inputsOnly {n : Nat} (u : Fin n) :
    maxBinaryReaderDepth (Circuit.inputsOnly : Circuit n n) u = 0 := rfl

@[simp] theorem maxBinaryReaderDepth_snoc_not_last {n w : Nat} (c : Circuit n w) (a : Fin w) :
    maxBinaryReaderDepth (c.snoc (.not a)) (Fin.last w) = wireDepth c a := by
  simp [maxBinaryReaderDepth]

@[simp] theorem maxBinaryReaderDepth_snoc_not_castSucc {n w : Nat} (c : Circuit n w)
    (a q : Fin w) :
    maxBinaryReaderDepth (c.snoc (.not a)) q.castSucc = maxBinaryReaderDepth c q := by
  simp [maxBinaryReaderDepth]

@[simp] theorem maxBinaryReaderDepth_snoc_and_last {n w : Nat} (c : Circuit n w) (a b : Fin w) :
    maxBinaryReaderDepth (c.snoc (.and a b)) (Fin.last w) =
      max (wireDepth c a) (wireDepth c b) + 1 := by
  simp [maxBinaryReaderDepth]

@[simp] theorem maxBinaryReaderDepth_snoc_and_castSucc {n w : Nat} (c : Circuit n w)
    (a b q : Fin w) :
    maxBinaryReaderDepth (c.snoc (.and a b)) q.castSucc =
      if q = a ∨ q = b then
        max (maxBinaryReaderDepth c q) (max (wireDepth c a) (wireDepth c b) + 1)
      else maxBinaryReaderDepth c q := by
  simp [maxBinaryReaderDepth]

@[simp] theorem maxBinaryReaderDepth_snoc_or_last {n w : Nat} (c : Circuit n w) (a b : Fin w) :
    maxBinaryReaderDepth (c.snoc (.or a b)) (Fin.last w) =
      max (wireDepth c a) (wireDepth c b) + 1 := by
  simp [maxBinaryReaderDepth]

@[simp] theorem maxBinaryReaderDepth_snoc_or_castSucc {n w : Nat} (c : Circuit n w)
    (a b q : Fin w) :
    maxBinaryReaderDepth (c.snoc (.or a b)) q.castSucc =
      if q = a ∨ q = b then
        max (maxBinaryReaderDepth c q) (max (wireDepth c a) (wireDepth c b) + 1)
      else maxBinaryReaderDepth c q := by
  simp [maxBinaryReaderDepth]

theorem wireDepth_le_maxBinaryReaderDepth {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (u : Fin w) → wireDepth c u ≤ maxBinaryReaderDepth c u
  | _, .inputsOnly, _ => le_rfl
  | _, .snoc earlier g, u => by
    cases u using Fin.lastCases with
    | last =>
      cases g <;> simp
    | cast q =>
      rw [wireDepth_snoc_castSucc]
      have ih := wireDepth_le_maxBinaryReaderDepth earlier q
      cases g with
      | not a => simpa using ih
      | and a b =>
        rw [maxBinaryReaderDepth_snoc_and_castSucc]
        split_ifs
        · exact ih.trans (le_max_left _ _)
        · exact ih
      | or a b =>
        rw [maxBinaryReaderDepth_snoc_or_castSucc]
        split_ifs
        · exact ih.trans (le_max_left _ _)
        · exact ih

theorem maxBinaryReaderDepth_snoc_castSucc_ge {n w : Nat} (c : Circuit n w)
    (g : Gate w) (q : Fin w) :
    maxBinaryReaderDepth c q ≤ maxBinaryReaderDepth (c.snoc g) q.castSucc := by
  cases g with
  | not _ => simp
  | and a b =>
    rw [maxBinaryReaderDepth_snoc_and_castSucc]
    split_ifs <;> simp
  | or a b =>
    rw [maxBinaryReaderDepth_snoc_or_castSucc]
    split_ifs <;> simp

/-- Forward binary depth span of wire `u`. -/
def wireSpan {n w : Nat} (c : Circuit n w) (u : Fin w) : Nat :=
  maxBinaryReaderDepth c u - wireDepth c u

/-- Total truncated forward span over all gate wires (`n ≤ u.val`) at stride `h`. -/
def totalTruncatedSpan {n w : Nat} (c : Circuit n w) (h : Nat) : Nat :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin w => n ≤ u.val), min h (wireSpan c u)

/-! ### 2. Residue Buckets, Crossing Wires, and Exact Pigeonhole -/

/-- Stride-`h` topological depth bucket with offset `r`. -/
def bucket (h r d : Nat) : Nat := (d + r) / h

/-- Whether gate wire `u` crosses a stride-`h` bucket boundary at phase `r` before its last
binary reader. -/
def isCrossing {n w : Nat} (c : Circuit n w) (h r : Nat) (u : Fin w) : Bool :=
  decide (n ≤ u.val ∧ bucket h r (wireDepth c u) < bucket h r (maxBinaryReaderDepth c u))

/-- Gate wires crossing a stride-`h` bucket boundary at phase `r`. -/
def crossingWires {n w : Nat} (c : Circuit n w) (h r : Nat) : Finset (Fin w) :=
  Finset.univ.filter (fun u => isCrossing c h r u = true)

private theorem add_mod_eq_inj {h d a b : Nat} (ha : a < h) (hb : b < h)
    (hMod : (d + a) % h = (d + b) % h) : a = b := by
  have hh : 0 < h := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  have h1 : (d + a) % h = (d % h + a) % h := by
    conv_lhs => rw [← Nat.div_add_mod d h, Nat.add_assoc, Nat.mul_add_mod]
  have h2 : (d + b) % h = (d % h + b) % h := by
    conv_lhs => rw [← Nat.div_add_mod d h, Nat.add_assoc, Nat.mul_add_mod]
  rw [h1, h2] at hMod
  have hd : d % h < h := Nat.mod_lt d hh
  by_cases hda : d % h + a < h <;> by_cases hdb : d % h + b < h
  · rw [Nat.mod_eq_of_lt hda, Nat.mod_eq_of_lt hdb] at hMod; omega
  · have hda' : (d % h + b) % h = d % h + b - h := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt hda, hda'] at hMod; omega
  · have hda' : (d % h + a) % h = d % h + a - h := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hda', Nat.mod_eq_of_lt hdb] at hMod; omega
  · have ha' : (d % h + a) % h = d % h + a - h := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hb' : (d % h + b) % h = d % h + b - h := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [ha', hb'] at hMod; omega

/-- At most `min h σ` phase offsets `r : Fin h` cause a span-`σ` wire starting at depth `d` to
cross a stride-`h` bucket boundary. -/
theorem card_residues_crossing_le (h d σ : Nat) (hh : 0 < h) :
    (Finset.univ.filter (fun r : Fin h => (d + r.val) / h < (d + σ + r.val) / h)).card ≤
      min h σ := by
  by_cases hZero : σ = 0
  · subst hZero
    simp
  · have hσPos : 0 < σ := Nat.pos_of_ne_zero hZero
    by_cases hBig : h ≤ σ
    · rw [min_eq_left hBig]
      exact (Finset.card_filter_le _ _).trans (by simp)
    · have hSmall : σ < h := Nat.lt_of_not_ge hBig
      rw [min_eq_right hSmall.le]
      let S := Finset.univ.filter (fun r : Fin h => (d + r.val) / h < (d + σ + r.val) / h)
      have hGe : ∀ r ∈ S, h - σ ≤ (d + r.val) % h := by
        intro r hr
        have hLt : (d + r.val) / h < (d + σ + r.val) / h := (Finset.mem_filter.mp hr).2
        by_contra hNot
        have hModLt : (d + r.val) % h + σ < h := by omega
        have hdm : h * ((d + r.val) / h) + (d + r.val) % h = d + r.val := Nat.div_add_mod (d + r.val) h
        have hEq : d + σ + r.val = (d + r.val) % h + σ + (d + r.val) / h * h := by
          rw [Nat.mul_comm ((d + r.val) / h) h]
          omega
        have hDiv : (d + σ + r.val) / h = (d + r.val) / h := by
          rw [hEq, Nat.add_mul_div_right _ _ hh, Nat.div_eq_of_lt hModLt, Nat.zero_add]
        omega
      let map : Fin h → Fin σ := fun r =>
        ⟨(d + r.val) % h - (h - σ), by have := Nat.mod_lt (d + r.val) hh; omega⟩
      have hInj : Set.InjOn map S := by
        intro r₁ hr₁ r₂ hr₂ hEq
        have h1 := hGe r₁ hr₁
        have h2 := hGe r₂ hr₂
        have hv : (map r₁).val = (map r₂).val := congrArg Fin.val hEq
        dsimp [map] at hv
        have hMod : (d + r₁.val) % h = (d + r₂.val) % h := by omega
        exact Fin.ext (add_mod_eq_inj r₁.isLt r₂.isLt hMod)
      calc
        S.card ≤ (Finset.univ : Finset (Fin σ)).card :=
          Finset.card_le_card_of_injOn map (fun _ _ => Finset.mem_univ _) hInj
        _ = σ := by simp

theorem sum_crossingWires_le_totalTruncatedSpan {n w : Nat} (c : Circuit n w) (h : Nat)
    (hh : 0 < h) :
    ∑ r : Fin h, (crossingWires c h r.val).card ≤ totalTruncatedSpan c h := by
  have hStep (r : Fin h) : (crossingWires c h r.val).card =
      ∑ u : Fin w, if isCrossing c h r.val u = true then 1 else 0 := by
    rw [crossingWires, Finset.card_filter]
  simp_rw [hStep]
  rw [Finset.sum_comm, totalTruncatedSpan, Finset.sum_filter]
  refine Finset.sum_le_sum fun u _ => ?_
  by_cases hu : n ≤ u.val
  · simp only [hu, ite_true, isCrossing, bucket, decide_eq_true_eq]
    have hSpan : wireDepth c u + wireSpan c u = maxBinaryReaderDepth c u := by
      have hle := wireDepth_le_maxBinaryReaderDepth c u
      unfold wireSpan
      omega
    rw [← hSpan, ← Finset.card_filter]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      card_residues_crossing_le h (wireDepth c u) (wireSpan c u) hh
  · simp [isCrossing, hu]

/-- **Stride-`h` Residue Pigeonhole Theorem**: for any circuit `c` and stride `h ≥ 1`, there
exists a residue `r : Fin h` leaving at most `totalTruncatedSpan c h / h` crossing gate wires. -/
theorem exists_stride_residue_le {n w : Nat} (c : Circuit n w) (h : Nat) (hh : 0 < h) :
    ∃ r : Fin h, (crossingWires c h r.val).card ≤ totalTruncatedSpan c h / h := by
  by_contra hAll
  push Not at hAll
  have hSumLower : h * (totalTruncatedSpan c h / h + 1) ≤
      ∑ r : Fin h, (crossingWires c h r.val).card := by
    calc
      h * (totalTruncatedSpan c h / h + 1) = ∑ _ : Fin h, (totalTruncatedSpan c h / h + 1) := by
        simp [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ r : Fin h, (crossingWires c h r.val).card :=
        Finset.sum_le_sum fun r _ => hAll r
  have hSumUpper := sum_crossingWires_le_totalTruncatedSpan c h hh
  have hDiv := Nat.lt_div_mul_add hh (a := totalTruncatedSpan c h)
  nlinarith

private theorem gateWire_filter_card {n : Nat} : {w : Nat} → (c : Circuit n w) →
    (Finset.univ.filter (fun u : Fin w => n ≤ u.val)).card = c.gateCount
  | _, .inputsOnly => by
    have hEmpty : (Finset.univ.filter (fun u : Fin n => n ≤ u.val)) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      have := u.isLt
      omega
    rw [hEmpty, Finset.card_empty]
    rfl
  | w + 1, .snoc earlier _ => by
    rw [Finset.card_filter, Fin.sum_univ_castSucc, ← Finset.card_filter]
    have hGe : n ≤ w := earlier.inputs_le_wires
    have hTail : (if n ≤ (Fin.last w).val then 1 else 0) = 1 := by simp [hGe]
    have hOld : (Finset.univ.filter (fun q : Fin w => n ≤ q.castSucc.val)).card =
        earlier.gateCount := by
      simpa [Fin.val_castSucc] using gateWire_filter_card earlier
    rw [hTail, hOld]
    rfl

theorem totalTruncatedSpan_layered_le {n w : Nat} (c : Circuit n w) (h : Nat)
    (hUnit : ∀ u : Fin w, n ≤ u.val → wireSpan c u ≤ 1) :
    totalTruncatedSpan c h ≤ c.gateCount := by
  calc
    totalTruncatedSpan c h
      ≤ ∑ _ ∈ Finset.univ.filter (fun u : Fin w => n ≤ u.val), 1 := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hs := hUnit u (Finset.mem_filter.mp hu).2
        exact (Nat.min_le_right h (wireSpan c u)).trans hs
    _ = (Finset.univ.filter (fun u : Fin w => n ≤ u.val)).card := by simp
    _ = c.gateCount := gateWire_filter_card c

/-! ### 3. Universal Automatic Compiler `Circuit n w → BlockCircuit n (2 ^ h)` -/

/-- Structural closure condition guaranteeing that whenever a gate computes an `.and`/`.or` at depth
`d`, any non-input operand from an earlier bucket has `keep = true`. -/
def BucketClosed {n : Nat} : {w : Nat} → Circuit n w → Nat → Nat → (Fin w → Bool) → Prop
  | _, .inputsOnly, _, _, _ => True
  | _, .snoc earlier (.not _), h, r, keep =>
    BucketClosed earlier h r (keep ∘ Fin.castSucc)
  | _, .snoc earlier (.and a b), h, r, keep =>
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    BucketClosed earlier h r (keep ∘ Fin.castSucc) ∧
      (n ≤ a.val → bucket h r (wireDepth earlier a) < bucket h r d → keep a.castSucc = true) ∧
      (n ≤ b.val → bucket h r (wireDepth earlier b) < bucket h r d → keep b.castSucc = true)
  | _, .snoc earlier (.or a b), h, r, keep =>
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    BucketClosed earlier h r (keep ∘ Fin.castSucc) ∧
      (n ≤ a.val → bucket h r (wireDepth earlier a) < bucket h r d → keep a.castSucc = true) ∧
      (n ≤ b.val → bucket h r (wireDepth earlier b) < bucket h r d → keep b.castSucc = true)

theorem bucketClosed_of_crossing {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (h r : Nat) → (keep : Fin w → Bool) →
    (∀ u : Fin w, isCrossing c h r u = true → keep u = true) →
    BucketClosed c h r keep
  | _, .inputsOnly, _, _, _, _ => trivial
  | _, .snoc earlier g, h, r, keep, hCross => by
    have hEarlierCross : ∀ q : Fin _, isCrossing earlier h r q = true → (keep ∘ Fin.castSucc) q = true := by
      intro q hq
      simp only [isCrossing, decide_eq_true_eq] at hq
      have hDepth : bucket h r (wireDepth (earlier.snoc g) q.castSucc) <
          bucket h r (maxBinaryReaderDepth (earlier.snoc g) q.castSucc) := by
        rw [wireDepth_snoc_castSucc]
        exact lt_of_lt_of_le hq.2 (Nat.div_le_div_right (Nat.add_le_add_right
          (maxBinaryReaderDepth_snoc_castSucc_ge earlier g q) r))
      exact hCross q.castSucc (decide_eq_true ⟨by simpa using hq.1, hDepth⟩)
    have ih := bucketClosed_of_crossing earlier h r (keep ∘ Fin.castSucc) hEarlierCross
    cases g with
    | not _ => exact ih
    | and a b =>
      refine ⟨ih, fun ha hLt => hCross a.castSucc ?_, fun hb hLt => hCross b.castSucc ?_⟩
      · simp only [isCrossing, decide_eq_true_eq, Fin.val_castSucc, wireDepth_snoc_castSucc]
        exact ⟨ha, lt_of_lt_of_le hLt (Nat.div_le_div_right (Nat.add_le_add_right
          (by simp) r))⟩
      · simp only [isCrossing, decide_eq_true_eq, Fin.val_castSucc, wireDepth_snoc_castSucc]
        exact ⟨hb, lt_of_lt_of_le hLt (Nat.div_le_div_right (Nat.add_le_add_right
          (by simp) r))⟩
    | or a b =>
      refine ⟨ih, fun ha hLt => hCross a.castSucc ?_, fun hb hLt => hCross b.castSucc ?_⟩
      · simp only [isCrossing, decide_eq_true_eq, Fin.val_castSucc, wireDepth_snoc_castSucc]
        exact ⟨ha, lt_of_lt_of_le hLt (Nat.div_le_div_right (Nat.add_le_add_right
          (by simp) r))⟩
      · simp only [isCrossing, decide_eq_true_eq, Fin.val_castSucc, wireDepth_snoc_castSucc]
        exact ⟨hb, lt_of_lt_of_le hLt (Nat.div_le_div_right (Nat.add_le_add_right
          (by simp) r))⟩

/-- Number of kept gate wires (`n ≤ u.val ∧ keep u = true`). -/
def keptCount (n : Nat) {w : Nat} (keep : Fin w → Bool) : Nat :=
  (Finset.univ.filter (fun u : Fin w => n ≤ u.val ∧ keep u = true)).card

theorem keptCount_snoc (n w : Nat) (keep : Fin (w + 1) → Bool) :
    keptCount n keep = keptCount n (keep ∘ Fin.castSucc) +
      if n ≤ w ∧ keep (Fin.last w) = true then 1 else 0 := by
  unfold keptCount
  rw [Finset.card_filter, Fin.sum_univ_castSucc, ← Finset.card_filter]
  simp only [Function.comp_apply, Fin.val_castSucc, Fin.val_last]

/-- Non-dependent compiled prefix state for `compileStride`. Every wire's local cone is stored
inside the uniform carrier `Fin (2 ^ h) → Fin (n + blocks)` while only inspecting the first
`2 ^ ((wireDepth c u + r) % h + 1)` entries (`cone_local`). -/
structure StrideState {n w : Nat} (c : Circuit n w) (h r : Nat) (keep : Fin w → Bool) where
  blocks : Nat
  bc : BlockCircuit n (2 ^ h) (n + blocks)
  blocks_eq : blocks = keptCount n keep
  wireIdx : Fin w → Fin (n + blocks)
  wireIdx_eval : ∀ x u, (u.val < n ∨ keep u = true) → bc.evalWires x (wireIdx u) = c.evalWires x u
  coneArgs : Fin w → Fin (2 ^ h) → Fin (n + blocks)
  coneEval : Fin w → (Fin (2 ^ h) → Bool) → Bool
  cone_correct : ∀ x u, coneEval u (fun j => bc.evalWires x (coneArgs u j)) = c.evalWires x u
  cone_local : ∀ u vals₁ vals₂,
    (∀ j : Fin (2 ^ h), j.val < 2 ^ ((wireDepth c u + r) % h + 1) → vals₁ j = vals₂ j) →
    coneEval u vals₁ = coneEval u vals₂

/-- Single-wire cone on `Fin (2 ^ h)` reading `j = 0`. -/
def singleWireConeH (h : Nat) {w : Nat} (wire : Fin w) :
    (Fin (2 ^ h) → Fin w) × ((Fin (2 ^ h) → Bool) → Bool) :=
  (fun _ => wire, fun vals => vals ⟨0, Nat.two_pow_pos h⟩)

theorem eval_singleWireConeH (h : Nat) {w : Nat} (wire : Fin w) (wireVal : Fin w → Bool) :
    (singleWireConeH h wire).2 (fun j => wireVal ((singleWireConeH h wire).1 j)) = wireVal wire :=
  rfl

theorem local_singleWireConeH (h : Nat) {k : Nat} (hk : 1 ≤ 2 ^ k)
    (vals₁ vals₂ : Fin (2 ^ h) → Bool)
    (hAgree : ∀ j : Fin (2 ^ h), j.val < 2 ^ k → vals₁ j = vals₂ j) :
    (singleWireConeH h (⟨0, Nat.zero_lt_one⟩ : Fin 1)).2 vals₁ =
      (singleWireConeH h (⟨0, Nat.zero_lt_one⟩ : Fin 1)).2 vals₂ :=
  hAgree ⟨0, Nat.two_pow_pos h⟩ (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)

/-- Combines two `Fin (2 ^ h)` cones supported on `[0, 2 ^ t)` into one cone supported on
`[0, 2 ^ (t + 1))` (for `t + 1 ≤ h`). -/
def combineConesH {w : Nat} (h t : Nat) (ht : t + 1 ≤ h) (dummy : Fin w)
    (op : Bool → Bool → Bool) (lArgs rArgs : Fin (2 ^ h) → Fin w)
    (lFn rFn : (Fin (2 ^ h) → Bool) → Bool) :
    (Fin (2 ^ h) → Fin w) × ((Fin (2 ^ h) → Bool) → Bool) :=
  (fun j =>
      if hj : j.val < 2 ^ t then lArgs j
      else if hj2 : j.val < 2 ^ (t + 1) then
        rArgs ⟨j.val - 2 ^ t, by
          have := lt_of_lt_of_le hj2 (Nat.pow_le_pow_right (by decide) ht)
          omega⟩
      else dummy,
   fun vals =>
      op
        (lFn vals)
        (rFn (fun i =>
          if hi : i.val < 2 ^ t then
            vals ⟨2 ^ t + i.val, by
              have hP : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) ht
              rw [Nat.pow_succ] at hP
              omega⟩
          else false)))

theorem eval_combineConesH {w : Nat} (h t : Nat) (ht : t + 1 ≤ h) (dummy : Fin w)
    (op : Bool → Bool → Bool) (lArgs rArgs : Fin (2 ^ h) → Fin w)
    (lFn rFn : (Fin (2 ^ h) → Bool) → Bool)
    (hlLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ h), j.val < 2 ^ t → vals₁ j = vals₂ j) →
      lFn vals₁ = lFn vals₂)
    (hrLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ h), j.val < 2 ^ t → vals₁ j = vals₂ j) →
      rFn vals₁ = rFn vals₂)
    (wireVal : Fin w → Bool) :
    (combineConesH h t ht dummy op lArgs rArgs lFn rFn).2
        (fun j => wireVal ((combineConesH h t ht dummy op lArgs rArgs lFn rFn).1 j)) =
      op (lFn (fun j => wireVal (lArgs j))) (rFn (fun j => wireVal (rArgs j))) := by
  dsimp only [combineConesH]
  congr 1
  · apply hlLocal
    intro j hj
    simp [hj]
  · apply hrLocal
    intro i hi
    have hP : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) ht
    have hLt2 : 2 ^ t + i.val < 2 ^ (t + 1) := by rw [Nat.pow_succ]; omega
    simp [hi, show ¬(2 ^ t + i.val < 2 ^ t) by omega, hLt2]

theorem local_combineConesH {w : Nat} (h t : Nat) (ht : t + 1 ≤ h) (dummy : Fin w)
    (op : Bool → Bool → Bool) (lArgs rArgs : Fin (2 ^ h) → Fin w)
    (lFn rFn : (Fin (2 ^ h) → Bool) → Bool)
    (hlLocal : ∀ vals₁ vals₂, (∀ j : Fin (2 ^ h), j.val < 2 ^ t → vals₁ j = vals₂ j) →
      lFn vals₁ = lFn vals₂)
    (vals₁ vals₂ : Fin (2 ^ h) → Bool)
    (hAgree : ∀ j : Fin (2 ^ h), j.val < 2 ^ (t + 1) → vals₁ j = vals₂ j) :
    (combineConesH h t ht dummy op lArgs rArgs lFn rFn).2 vals₁ =
      (combineConesH h t ht dummy op lArgs rArgs lFn rFn).2 vals₂ := by
  dsimp only [combineConesH]
  have hPowL : 2 ^ t ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ t)
  have hPowH : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) ht
  congr 1
  · exact hlLocal vals₁ vals₂ fun j hj => hAgree j (lt_of_lt_of_le hj hPowL)
  · congr 1
    funext i
    split_ifs with hi
    · apply hAgree
      simp only [Nat.pow_succ]
      change 2 ^ t + i.val < 2 ^ t * 2
      omega
    · rfl

theorem mod_lt_of_same_bucket {h r d₁ d₂ : Nat}
    (hLt : d₁ < d₂) (hNotCross : ¬((d₁ + r) / h < (d₂ + r) / h)) :
    (d₁ + r) % h + 1 ≤ (d₂ + r) % h := by
  have hLeDiv : (d₁ + r) / h ≤ (d₂ + r) / h := Nat.div_le_div_right (by omega)
  have hEqDiv : (d₁ + r) / h = (d₂ + r) / h := by omega
  have h1 := Nat.div_add_mod (d₁ + r) h
  have h2 := Nat.div_add_mod (d₂ + r) h
  rw [hEqDiv] at h1
  omega

/-- Helper building a `Fin (2 ^ h)` cone for child `a` supported inside `[0, 2 ^ ((d + r) % h))`. -/
def buildChildConeH {n w : Nat} (earlier : Circuit n w) (h r d : Nat) (keep : Fin w → Bool)
    (prev : StrideState earlier h r keep)
    (a : Fin w) (haLt : wireDepth earlier a < d)
    (haClosed : n ≤ a.val → bucket h r (wireDepth earlier a) < bucket h r d → keep a = true) :
    { p : (Fin (2 ^ h) → Fin (n + prev.blocks)) × ((Fin (2 ^ h) → Bool) → Bool) //
      (∀ x, p.2 (fun j => prev.bc.evalWires x (p.1 j)) = earlier.evalWires x a) ∧
      (∀ vals₁ vals₂, (∀ j : Fin (2 ^ h), j.val < 2 ^ ((d + r) % h) → vals₁ j = vals₂ j) →
        p.2 vals₁ = p.2 vals₂) } :=
  if haIn : a.val < n then
    ⟨singleWireConeH h (prev.wireIdx a),
      fun x => by rw [eval_singleWireConeH, prev.wireIdx_eval x a (Or.inl haIn)],
      fun vals₁ vals₂ hAgree => hAgree ⟨0, Nat.two_pow_pos h⟩ (Nat.two_pow_pos ((d + r) % h))⟩
  else if hCross : bucket h r (wireDepth earlier a) < bucket h r d then
    ⟨singleWireConeH h (prev.wireIdx a),
      fun x => by
        rw [eval_singleWireConeH, prev.wireIdx_eval x a (Or.inr (haClosed (by omega) hCross))],
      fun vals₁ vals₂ hAgree => hAgree ⟨0, Nat.two_pow_pos h⟩ (Nat.two_pow_pos ((d + r) % h))⟩
  else
    let hk : (wireDepth earlier a + r) % h + 1 ≤ (d + r) % h :=
      mod_lt_of_same_bucket haLt hCross
    ⟨(prev.coneArgs a, prev.coneEval a),
      fun x => prev.cone_correct x a,
      fun vals₁ vals₂ hAgree => prev.cone_local a vals₁ vals₂ fun j hj =>
        hAgree j (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by decide) hk))⟩

/-- Helper extending a `StrideState` by one gate `g` whose uniform `Fin (2 ^ h)` cone
`(coneArgsLast, coneEvalLast)` computes the new wire's value locally within
`2 ^ ((wireDepth (earlier.snoc g) (Fin.last w) + r) % h + 1)`. -/
def extendState {n w : Nat} {earlier : Circuit n w} (g : Gate w)
    (h r : Nat) (hn : 0 < n) (keep : Fin (w + 1) → Bool)
    (prev : StrideState earlier h r (keep ∘ Fin.castSucc))
    (coneArgsLast : Fin (2 ^ h) → Fin (n + prev.blocks))
    (coneEvalLast : (Fin (2 ^ h) → Bool) → Bool)
    (hLast : ∀ x, coneEvalLast (fun j => prev.bc.evalWires x (coneArgsLast j)) =
      (earlier.snoc g).evalWires x (Fin.last w))
    (hLocal : ∀ vals₁ vals₂,
      (∀ j : Fin (2 ^ h), j.val < 2 ^ ((wireDepth (earlier.snoc g) (Fin.last w) + r) % h + 1) →
        vals₁ j = vals₂ j) →
      coneEvalLast vals₁ = coneEvalLast vals₂) :
    StrideState (earlier.snoc g) h r keep :=
  let nw : Nat := n + prev.blocks
  if hKeep : n ≤ w ∧ keep (Fin.last w) = true then
    let newBc : BlockCircuit n (2 ^ h) (n + (prev.blocks + 1)) :=
      prev.bc.snoc coneArgsLast coneEvalLast
    { blocks := prev.blocks + 1
      bc := newBc
      blocks_eq := by simp [keptCount_snoc, hKeep, prev.blocks_eq]
      wireIdx := Fin.lastCases (Fin.last nw) (fun q => (prev.wireIdx q).castSucc)
      wireIdx_eval := fun x u hu => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          dsimp only [newBc, BlockCircuit.evalWires]
          rw [Fin.snoc_last]
          exact hLast x
        | cast q =>
          rw [Fin.lastCases_castSucc]
          have hq : q.val < n ∨ (keep ∘ Fin.castSucc) q = true := by
            simpa [Fin.val_castSucc] using hu
          dsimp only [newBc, BlockCircuit.evalWires]
          rw [Fin.snoc_castSucc, prev.wireIdx_eval x q hq]
          simp [Circuit.evalWires, Fin.snoc_castSucc]
      coneArgs := Fin.lastCases (fun _ => Fin.last nw) (fun q j => (prev.coneArgs q j).castSucc)
      coneEval := Fin.lastCases (fun vals => vals ⟨0, Nat.two_pow_pos h⟩) prev.coneEval
      cone_correct := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, Fin.lastCases_last]
          dsimp only [newBc, BlockCircuit.evalWires]
          rw [Fin.snoc_last]
          exact hLast x
        | cast q =>
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          have hW : (fun j => newBc.evalWires x (prev.coneArgs q j).castSucc) =
              fun j => prev.bc.evalWires x (prev.coneArgs q j) := by
            funext j
            dsimp only [newBc, BlockCircuit.evalWires]
            rw [Fin.snoc_castSucc]
          rw [hW, prev.cone_correct]
          simp [Circuit.evalWires, Fin.snoc_castSucc]
      cone_local := fun u vals₁ vals₂ hAgree => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact hAgree ⟨0, Nat.two_pow_pos h⟩ (Nat.two_pow_pos _)
        | cast q =>
          rw [Fin.lastCases_castSucc]
          rw [wireDepth_snoc_castSucc] at hAgree
          exact prev.cone_local q vals₁ vals₂ hAgree }
  else
    { blocks := prev.blocks
      bc := prev.bc
      blocks_eq := by simp [keptCount_snoc, hKeep, prev.blocks_eq]
      wireIdx := Fin.lastCases (⟨0, by omega⟩) prev.wireIdx
      wireIdx_eval := fun x u hu => by
        cases u using Fin.lastCases with
        | last =>
          exfalso
          have hge := earlier.inputs_le_wires
          rcases hu with huLt | hKeepT
          · simp only [Fin.val_last] at huLt; omega
          · exact hKeep ⟨hge, hKeepT⟩
        | cast q =>
          rw [Fin.lastCases_castSucc]
          have hq : q.val < n ∨ (keep ∘ Fin.castSucc) q = true := by
            simpa [Fin.val_castSucc] using hu
          simp [Circuit.evalWires, Fin.snoc_castSucc, prev.wireIdx_eval x q hq]
      coneArgs := Fin.lastCases coneArgsLast prev.coneArgs
      coneEval := Fin.lastCases coneEvalLast prev.coneEval
      cone_correct := fun x u => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, Fin.lastCases_last]
          exact hLast x
        | cast q =>
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
          simp [Circuit.evalWires, Fin.snoc_castSucc, prev.cone_correct]
      cone_local := fun u vals₁ vals₂ hAgree => by
        cases u using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last]
          exact hLocal vals₁ vals₂ hAgree
        | cast q =>
          rw [Fin.lastCases_castSucc]
          rw [wireDepth_snoc_castSucc] at hAgree
          exact prev.cone_local q vals₁ vals₂ hAgree }

/-- **Universal Stride-`h` Compiler**: compiles any circuit `c` satisfying `BucketClosed c h r keep`
into a `2 ^ h`-input `BlockCircuit` with `keptCount n keep` blocks. -/
def compileStride {n : Nat} :
    {w : Nat} → (c : Circuit n w) → (h r : Nat) → (hh : 0 < h) → (hn : 0 < n) →
    (keep : Fin w → Bool) → BucketClosed c h r keep → StrideState c h r keep
  | _, .inputsOnly, h, r, _, hn, keep, _ =>
    { blocks := 0
      bc := BlockCircuit.inputsOnly
      blocks_eq := by
        unfold keptCount
        have hEmpty : (Finset.univ.filter (fun u : Fin n => n ≤ u.val ∧ keep u = true)) = ∅ := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          have := u.isLt
          omega
        rw [hEmpty, Finset.card_empty]
      wireIdx := fun u => u
      wireIdx_eval := fun _ _ _ => rfl
      coneArgs := fun u => (singleWireConeH h u).1
      coneEval := fun u => (singleWireConeH h u).2
      cone_correct := fun _ _ => rfl
      cone_local := fun _ _ _ hAgree => hAgree ⟨0, Nat.two_pow_pos h⟩ (Nat.two_pow_pos _) }
  | _, .snoc earlier (.not a), h, r, hh, hn, keep, hClosed =>
    let prev := compileStride earlier h r hh hn (keep ∘ Fin.castSucc) hClosed
    extendState (.not a) h r hn keep prev (prev.coneArgs a) (fun vals => !(prev.coneEval a vals))
      (fun x => by
        have hEq := prev.cone_correct x a
        simpa [Circuit.evalWires, Gate.eval, Fin.snoc_last] using congrArg Bool.not hEq)
      (fun vals₁ vals₂ hAgree => by
        rw [wireDepth_snoc_not_last] at hAgree
        exact congrArg Bool.not (prev.cone_local a vals₁ vals₂ hAgree))
  | _, .snoc earlier (.and a b), h, r, hh, hn, keep, hClosed =>
    let prev := compileStride earlier h r hh hn (keep ∘ Fin.castSucc) hClosed.1
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    let t := (d + r) % h
    let ht : t + 1 ≤ h := Nat.succ_le_of_lt (Nat.mod_lt (d + r) hh)
    let dummy : Fin (n + prev.blocks) := ⟨0, by omega⟩
    let cL := buildChildConeH earlier h r d (keep ∘ Fin.castSucc) prev a (by omega) hClosed.2.1
    let cR := buildChildConeH earlier h r d (keep ∘ Fin.castSucc) prev b (by omega) hClosed.2.2
    let combined := combineConesH h t ht dummy (· && ·) cL.1.1 cR.1.1 cL.1.2 cR.1.2
    extendState (.and a b) h r hn keep prev combined.1 combined.2
      (fun x => by
        have hComb := eval_combineConesH h t ht dummy (· && ·) cL.1.1 cR.1.1 cL.1.2 cR.1.2
          cL.2.2 cR.2.2 (prev.bc.evalWires x)
        have hL := cL.2.1 x
        have hR := cR.2.1 x
        simpa [Circuit.evalWires, Gate.eval, Fin.snoc_last] using
          hComb.trans (congrArg₂ (· && ·) hL hR))
      (fun vals₁ vals₂ hAgree => by
        rw [wireDepth_snoc_and_last] at hAgree
        exact local_combineConesH h t ht dummy (· && ·) cL.1.1 cR.1.1 cL.1.2 cR.1.2
          cL.2.2 vals₁ vals₂ hAgree)
  | _, .snoc earlier (.or a b), h, r, hh, hn, keep, hClosed =>
    let prev := compileStride earlier h r hh hn (keep ∘ Fin.castSucc) hClosed.1
    let d := max (wireDepth earlier a) (wireDepth earlier b) + 1
    let t := (d + r) % h
    let ht : t + 1 ≤ h := Nat.succ_le_of_lt (Nat.mod_lt (d + r) hh)
    let dummy : Fin (n + prev.blocks) := ⟨0, by omega⟩
    let cL := buildChildConeH earlier h r d (keep ∘ Fin.castSucc) prev a (by omega) hClosed.2.1
    let cR := buildChildConeH earlier h r d (keep ∘ Fin.castSucc) prev b (by omega) hClosed.2.2
    let combined := combineConesH h t ht dummy (· || ·) cL.1.1 cR.1.1 cL.1.2 cR.1.2
    extendState (.or a b) h r hn keep prev combined.1 combined.2
      (fun x => by
        have hComb := eval_combineConesH h t ht dummy (· || ·) cL.1.1 cR.1.1 cL.1.2 cR.1.2
          cL.2.2 cR.2.2 (prev.bc.evalWires x)
        have hL := cL.2.1 x
        have hR := cR.2.1 x
        simpa [Circuit.evalWires, Gate.eval, Fin.snoc_last] using
          hComb.trans (congrArg₂ (· || ·) hL hR))
      (fun vals₁ vals₂ hAgree => by
        rw [wireDepth_snoc_or_last] at hAgree
        exact local_combineConesH h t ht dummy (· || ·) cL.1.1 cR.1.1 cL.1.2 cR.1.2
          cL.2.2 vals₁ vals₂ hAgree)

/-- Automatic `BlockContractionCertificate` for any `CircuitInstance n` at stride `h ≥ 1`, using
the optimal pigeonhole residue `r : Fin h`. -/
noncomputable def strideCertificate {n : Nat} (source : CircuitInstance n) (h : Nat)
    (hh : 0 < h) : BlockContractionCertificate source (2 ^ h) :=
  let r : Fin h := Classical.choose (exists_stride_residue_le source.circuit h hh)
  let keep : Fin source.wires → Bool := fun u =>
    isCrossing source.circuit h r.val u || decide (u = source.output ∧ n ≤ u.val)
  let hClosed : BucketClosed source.circuit h r.val keep :=
    bucketClosed_of_crossing source.circuit h r.val keep fun u hu => by simp [keep, hu]
  let hn : 0 < n := source.circuit.inputs_pos_of_wire source.output
  let st := compileStride source.circuit h r.val hh hn keep hClosed
  let hOut : source.output.val < n ∨ keep source.output = true := by
    by_cases hlt : source.output.val < n
    · exact Or.inl hlt
    · right; simp [keep, show n ≤ source.output.val by omega]
  { blocks := st.blocks
    bc := st.bc
    output := st.wireIdx source.output
    eval_eq := fun x => st.wireIdx_eval x source.output hOut }

theorem strideCertificate_blocks_le {n : Nat} (source : CircuitInstance n) (h : Nat)
    (hh : 0 < h) :
    (strideCertificate source h hh).blocks ≤ totalTruncatedSpan source.circuit h / h + 1 := by
  classical
  dsimp only [strideCertificate]
  set r : Fin h := Classical.choose (exists_stride_residue_le source.circuit h hh)
  have hr : (crossingWires source.circuit h r.val).card ≤
      totalTruncatedSpan source.circuit h / h :=
    Classical.choose_spec (exists_stride_residue_le source.circuit h hh)
  set keep : Fin source.wires → Bool := fun u =>
    isCrossing source.circuit h r.val u || decide (u = source.output ∧ n ≤ u.val)
  set st := compileStride source.circuit h r.val hh
    (source.circuit.inputs_pos_of_wire source.output) keep _
  rw [st.blocks_eq]
  have hSub : Finset.univ.filter (fun u : Fin source.wires => n ≤ u.val ∧ keep u = true) ⊆
      crossingWires source.circuit h r.val ∪ {source.output} := by
    intro u hu
    obtain ⟨hGe, hKeep⟩ := (Finset.mem_filter.mp hu).2
    simp only [keep, Bool.or_eq_true, decide_eq_true_eq] at hKeep
    rcases hKeep with hCross | ⟨rfl, _⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCross⟩)
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  calc
    keptCount n keep
      ≤ (crossingWires source.circuit h r.val ∪ {source.output}).card :=
        Finset.card_le_card hSub
    _ ≤ (crossingWires source.circuit h r.val).card + ({source.output} : Finset (Fin source.wires)).card :=
        Finset.card_union_le _ _
    _ = (crossingWires source.circuit h r.val).card + 1 := by simp
    _ ≤ totalTruncatedSpan source.circuit h / h + 1 := Nat.add_le_add_right hr 1

theorem strideCertificate_layered_blocks_le {n : Nat} (source : CircuitInstance n) (h : Nat)
    (hh : 0 < h)
    (hUnit : ∀ u : Fin source.wires, n ≤ u.val → wireSpan source.circuit u ≤ 1) :
    (strideCertificate source h hh).blocks ≤ source.circuit.gateCount / h + 1 :=
  (strideCertificate_blocks_le source h hh).trans
    (Nat.add_le_add_right (Nat.div_le_div_right (totalTruncatedSpan_layered_le source.circuit h hUnit)) 1)

theorem stride_contraction_subexponential {n : Nat → Nat} (source : (i : Nat) → CircuitInstance (n i))
    (h : Nat) (hh : 0 < h) (hn : Tendsto n atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hSpan : ∀ᶠ i in atTop,
      ((totalTruncatedSpan (source i).circuit h / h + 1 : Nat) : ℝ) ≤
        c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C overheadDeg : ℝ) :
    (fun i => logTimeBudget (n i) (n i + (strideCertificate (source i) h hh).blocks) C overheadDeg)
      =o[atTop] fun i => (n i : ℝ) := by
  refine block_contraction_subexponential source (fun i => strideCertificate (source i) h hh)
    hn hc hα ?_ C overheadDeg
  filter_upwards [hSpan] with i hi
  exact (Nat.cast_le.mpr (strideCertificate_blocks_le (source i) h hh)).trans hi

/-! ### 4. Hybrid Wire-Cut + Stride-`h` Block Contraction -/

/-- Branching block-contraction certificate partitioning `source.Accepting` into `branches`
disjoint `d`-input `BlockCircuit` encodings. -/
structure HybridBlockCertificate {n : Nat} (source : CircuitInstance n) (d : Nat) where
  branches : Nat
  blocks : Fin branches → Nat
  bc : (b : Fin branches) → BlockCircuit n d (n + blocks b)
  output : (b : Fin branches) → Fin (n + blocks b)
  modelsEquiv : (Σ b : Fin branches, Models ((bc b).encode (output b))) ≃ source.Accepting

namespace HybridBlockCertificate

theorem exact_count_sum {n d : Nat} {source : CircuitInstance n}
    (cert : HybridBlockCertificate source d) :
    Nat.card source.Accepting =
      ∑ b : Fin cert.branches, Nat.card (Models ((cert.bc b).encode (cert.output b))) := by
  classical
  rw [← Nat.card_congr cert.modelsEquiv, Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Nat.card_eq_fintype_card.symm

theorem canonical_count_sum {n d : Nat} {source : CircuitInstance n}
    (cert : HybridBlockCertificate source d) :
    Nat.card source.Accepting =
      ∑ b : Fin cert.branches,
        Nat.card (CanonicalModels (canonicalize ((cert.bc b).encode (cert.output b)))) := by
  rw [cert.exact_count_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Nat.card_congr (canonicalModelsEquiv ((cert.bc b).encode (cert.output b))).symm

theorem clause_width {n d : Nat} {source : CircuitInstance n}
    (cert : HybridBlockCertificate source d) (b : Fin cert.branches)
    {cl : CNF.Clause (Fin (n + cert.blocks b))}
    (h : cl ∈ ((cert.bc b).encode (cert.output b)).clauses) :
    cl.size ≤ d + 1 :=
  (cert.bc b).encode_width (cert.output b) h

theorem sat_iff {n d : Nat} {source : CircuitInstance n}
    (cert : HybridBlockCertificate source d) :
    (∃ input, source.eval input = true) ↔
      ∃ b : Fin cert.branches, ∃ σ : Fin (n + cert.blocks b) → Bool,
        ((cert.bc b).encode (cert.output b)).eval σ = true := by
  constructor
  · rintro ⟨input, hIn⟩
    obtain ⟨b, σ, hSat⟩ := cert.modelsEquiv.symm ⟨input, hIn⟩
    exact ⟨b, σ, hSat⟩
  · rintro ⟨b, σ, hSat⟩
    obtain ⟨input, hIn⟩ := cert.modelsEquiv ⟨b, ⟨σ, hSat⟩⟩
    exact ⟨input, hIn⟩

end HybridBlockCertificate

/-- Combines a width-`k` wire cut (`boundary : Fin k → Fin source.wires`) with automatic
stride-`h` block contraction on each residual circuit `residual fixed`. -/
noncomputable def hybridOfCutStride {n k : Nat} (source : CircuitInstance n)
    (boundary : Fin k → Fin source.wires)
    (residual : (Fin k → Bool) → CircuitInstance n)
    (hRes : ∀ fixed input, (residual fixed).eval input = true ↔
      source.eval input = true ∧ source.circuit.evalWires input ∘ boundary = fixed)
    (h : Nat) (hh : 0 < h) : HybridBlockCertificate source (2 ^ h) :=
  let cert : (b : Fin (2 ^ k)) →
      BlockContractionCertificate (residual ((cutBranchEquiv k).symm b)) (2 ^ h) :=
    fun b => strideCertificate (residual ((cutBranchEquiv k).symm b)) h hh
  { branches := 2 ^ k
    blocks := fun b => (cert b).blocks
    bc := fun b => (cert b).bc
    output := fun b => (cert b).output
    modelsEquiv := by
      let partEquiv : (Σ fixed : Fin k → Bool, (residual fixed).Accepting) ≃ source.Accepting :=
        { toFun := fun s => ⟨s.2.val, ((hRes s.1 s.2.val).mp s.2.property).1⟩
          invFun := fun input =>
            ⟨source.circuit.evalWires input.val ∘ boundary,
              ⟨input.val, (hRes _ input.val).mpr ⟨input.property, rfl⟩⟩⟩
          left_inv := fun ⟨fixed, input, hIn⟩ => by
            have hFix := ((hRes fixed input).mp hIn).2
            subst hFix
            rfl
          right_inv := fun ⟨_, _⟩ => rfl }
      exact (Equiv.sigmaCongr (cutBranchEquiv k).symm fun b =>
        (cert b).modelsEquiv).trans partEquiv }

theorem hybridOfCutStride_blocks_le {n k : Nat} (source : CircuitInstance n)
    (boundary : Fin k → Fin source.wires)
    (residual : (Fin k → Bool) → CircuitInstance n)
    (hRes : ∀ fixed input, (residual fixed).eval input = true ↔
      source.eval input = true ∧ source.circuit.evalWires input ∘ boundary = fixed)
    (h : Nat) (hh : 0 < h) (b : Fin (2 ^ k)) :
    (hybridOfCutStride source boundary residual hRes h hh).blocks b ≤
      totalTruncatedSpan (residual ((cutBranchEquiv k).symm b)).circuit h / h + 1 :=
  strideCertificate_blocks_le _ h hh

/-- Subexponential `#SAT` runtime transfer for hybrid cut + block contraction: `R i` branches
(`log (R i + 1) = o(n i)`) with per-branch `v i ≤ n i + B i` in the `O(n * (log n)^α)` window
(`α < 1 / 2`) keep `sopLogTimeBudget (n i) (R i) 1 (v i) C d = o(n i)`. -/
theorem hybrid_block_subexponential {n R maxBlocks : Nat → Nat}
    (hn : Tendsto n atTop atTop)
    (hBranches : (fun i => Real.log ((R i : ℝ) + 1)) =o[atTop] fun i => (n i : ℝ))
    {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hBlocks : ∀ᶠ i in atTop,
      (maxBlocks i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ α)
    (C d : ℝ) :
    (fun i => sopLogTimeBudget (n i) (R i) 1 (n i + maxBlocks i) C d) =o[atTop]
      fun i => (n i : ℝ) := by
  let β : ℝ := max α 0
  have hnReal : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hFactors : (fun _ : Nat => Real.log (((1 : Nat) : ℝ) + 1)) =o[atTop]
      fun i => (n i : ℝ) :=
    isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp hnReal))
  have hLogN : Tendsto (fun i => Real.log ((n i : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  refine sopLogTimeBudget_isLittleO_of_rpow_log hn hBranches hFactors (show (0 : ℝ) ≤ c + 1 by linarith)
    (max_lt hα (by norm_num) : β < 1 / 2) ?_ C d
  filter_upwards [hBlocks, hLogN.eventually_ge_atTop 1] with i hB hLN1
  have hRpowGe1 : 1 ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
    Real.one_le_rpow hLN1 (le_max_right α 0)
  have hRpowLe : (Real.log ((n i : ℝ) + 16)) ^ α ≤ (Real.log ((n i : ℝ) + 16)) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hLN1 (le_max_left α 0)
  have hBBound : (maxBlocks i : ℝ) ≤ c * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β :=
    hB.trans (mul_le_mul_of_nonneg_left hRpowLe (by positivity))
  have hNBound : (n i : ℝ) ≤ 1 * (n i : ℝ) * (Real.log ((n i : ℝ) + 16)) ^ β := by nlinarith
  push_cast
  linarith

/-! ### 5. Concrete Automatic Contraction Witness (`LayeredRing`) -/

namespace LayeredRing

/-- Total wire count after `D` layers of width `n`. -/
def ringWires (n : Nat) : Nat → Nat
  | 0 => n
  | D + 1 => ringWires n D + n

theorem ringWires_eq (n D : Nat) : ringWires n D = (D + 1) * n := by
  induction D with
  | zero => simp [ringWires]
  | succ D ih =>
    change ringWires n D + n = (D + 2) * n
    rw [ih]
    ring

def ringGate (k ℓ j : Nat) (_hj : j < k + 1) : Gate (ringWires (k + 1) ℓ + j) :=
  let n := k + 1
  have hnPos : 1 ≤ n := Nat.succ_pos k
  have hBase : ringWires n ℓ = (ℓ + 1) * n := ringWires_eq n ℓ
  let a : Fin (ringWires n ℓ + j) := ⟨ℓ * n + j, by
    rw [hBase]
    have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
    omega⟩
  let b : Fin (ringWires n ℓ + j) := ⟨ℓ * n + (j + 1) % n, by
    have hm : (j + 1) % n < n := Nat.mod_lt (j + 1) (Nat.succ_pos k)
    rw [hBase]
    have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
    omega⟩
  if ℓ % 2 = 0 then .and a b else .or a b

def appendRingRow (k ℓ : Nat) :
    (j : Nat) → j ≤ k + 1 → Circuit (k + 1) (ringWires (k + 1) ℓ) →
      Circuit (k + 1) (ringWires (k + 1) ℓ + j)
  | 0, _, c => c
  | j + 1, hj, c => (appendRingRow k ℓ j (by omega) c).snoc (ringGate k ℓ j (by omega))

def buildLayeredRing (k : Nat) : (D : Nat) → Circuit (k + 1) (ringWires (k + 1) D)
  | 0 => Circuit.inputsOnly
  | D + 1 => appendRingRow k D (k + 1) (le_refl _) (buildLayeredRing k D)

/-- Synchronous `D`-layer cyclic ring circuit on `n = k + 1` inputs with `D * (k + 1)` binary
gates and unit wire span. -/
def source (k D : Nat) : CircuitInstance (k + 1) where
  wires := ringWires (k + 1) D
  circuit := buildLayeredRing k D
  output := ⟨ringWires (k + 1) D - 1, by
    have hEq := ringWires_eq (k + 1) D
    have hPos : 0 < (D + 1) * (k + 1) := Nat.mul_pos (Nat.succ_pos D) (Nat.succ_pos k)
    omega⟩

private theorem gateCount_appendRingRow (k ℓ : Nat) (c : Circuit (k + 1) (ringWires (k + 1) ℓ)) :
    ∀ j (hj : j ≤ k + 1), (appendRingRow k ℓ j hj c).gateCount = c.gateCount + j
  | 0, _ => rfl
  | j + 1, hj => by
    dsimp [appendRingRow, ringGate]
    split_ifs <;> simp [Circuit.gateCount, gateCount_appendRingRow k ℓ c j (by omega), Nat.add_assoc]

theorem source_gateCount (k D : Nat) :
    (source k D).circuit.gateCount = D * (k + 1) := by
  dsimp [source]
  induction D with
  | zero => simp [buildLayeredRing, Circuit.gateCount]
  | succ D ih =>
    change (appendRingRow k D (k + 1) (le_refl _) (buildLayeredRing k D)).gateCount = (D + 1) * (k + 1)
    rw [gateCount_appendRingRow, ih]
    ring

private theorem div_layer_eq {n ℓ j : Nat} (hj : j < n) : (ℓ * n + j) / n = ℓ := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) hj
  rw [Nat.add_comm (ℓ * n) j, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hj, Nat.zero_add]

private theorem appendRingRow_inv (k ℓ : Nat) (c : Circuit (k + 1) (ringWires (k + 1) ℓ))
    (hDepth : ∀ u : Fin (ringWires (k + 1) ℓ), wireDepth c u = u.val / (k + 1))
    (hMax : ∀ u : Fin (ringWires (k + 1) ℓ),
      maxBinaryReaderDepth c u ≤ u.val / (k + 1) + 1) :
    ∀ j (hj : j ≤ k + 1),
      (∀ u : Fin (ringWires (k + 1) ℓ + j),
        wireDepth (appendRingRow k ℓ j hj c) u = u.val / (k + 1)) ∧
      (∀ u : Fin (ringWires (k + 1) ℓ + j),
        maxBinaryReaderDepth (appendRingRow k ℓ j hj c) u ≤ u.val / (k + 1) + 1) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hDepth, hMax⟩
  | succ j ih =>
    intro hj
    obtain ⟨ihD, ihM⟩ := ih (by omega)
    let n := k + 1
    let prev := appendRingRow k ℓ j (by omega) c
    have hBase : ringWires n ℓ = (ℓ + 1) * n := ringWires_eq n ℓ
    have hMul : ℓ * n + n = (ℓ + 1) * n := by ring
    let a : Fin (ringWires n ℓ + j) := ⟨ℓ * n + j, by rw [hBase]; omega⟩
    let b : Fin (ringWires n ℓ + j) := ⟨ℓ * n + (j + 1) % n, by
      have hm : (j + 1) % n < n := Nat.mod_lt (j + 1) (by omega : 0 < n)
      rw [hBase]; omega⟩
    have haDiv : (ℓ * (k + 1) + j) / (k + 1) = ℓ := div_layer_eq (by omega : j < k + 1)
    have hbDiv : (ℓ * (k + 1) + (j + 1) % (k + 1)) / (k + 1) = ℓ :=
      div_layer_eq (Nat.mod_lt (j + 1) (Nat.succ_pos k))
    have haD : wireDepth prev ⟨ℓ * (k + 1) + j, by
        change ℓ * n + j < ringWires n ℓ + j
        rw [hBase]; omega⟩ = ℓ :=
      (ihD a).trans haDiv
    have hbD : wireDepth prev ⟨ℓ * (k + 1) + (j + 1) % (k + 1), by
        change ℓ * n + (j + 1) % n < ringWires n ℓ + j
        have hm := Nat.mod_lt (j + 1) (by omega : 0 < n); rw [hBase]; omega⟩ = ℓ :=
      (ihD b).trans hbDiv
    have hLastDiv : (ringWires (k + 1) ℓ + j) / (k + 1) = ℓ + 1 := by
      change (ringWires n ℓ + j) / n = ℓ + 1
      rw [hBase]
      exact div_layer_eq (by omega : j < n)
    refine ⟨fun u => ?_, fun u => ?_⟩
    · cases u using Fin.lastCases with
      | last =>
        change wireDepth (prev.snoc (ringGate k ℓ j (by omega))) (Fin.last _) = _
        dsimp [ringGate]
        split_ifs
        · rw [wireDepth_snoc_and_last, haD, hbD, hLastDiv]; simp
        · rw [wireDepth_snoc_or_last, haD, hbD, hLastDiv]; simp
      | cast q =>
        change wireDepth (prev.snoc (ringGate k ℓ j (by omega))) q.castSucc = _
        rw [wireDepth_snoc_castSucc]
        exact ihD q
    · cases u using Fin.lastCases with
      | last =>
        change maxBinaryReaderDepth (prev.snoc (ringGate k ℓ j (by omega))) (Fin.last _) ≤ _
        dsimp [ringGate]
        split_ifs
        · rw [maxBinaryReaderDepth_snoc_and_last, haD, hbD, hLastDiv]; simp
        · rw [maxBinaryReaderDepth_snoc_or_last, haD, hbD, hLastDiv]; simp
      | cast q =>
        change maxBinaryReaderDepth (prev.snoc (ringGate k ℓ j (by omega))) q.castSucc ≤ _
        dsimp [ringGate]
        split_ifs
        · rw [maxBinaryReaderDepth_snoc_and_castSucc]
          split_ifs with hq
          · rcases hq with rfl | rfl
            · refine max_le ?_ (by rw [haD, hbD, haDiv]; simp)
              simpa [prev, a, n] using ihM a
            · refine max_le ?_ (by rw [haD, hbD, hbDiv]; simp)
              simpa [prev, b, n] using ihM b
          · exact ihM q
        · rw [maxBinaryReaderDepth_snoc_or_castSucc]
          split_ifs with hq
          · rcases hq with rfl | rfl
            · refine max_le ?_ (by rw [haD, hbD, haDiv]; simp)
              simpa [prev, a, n] using ihM a
            · refine max_le ?_ (by rw [haD, hbD, hbDiv]; simp)
              simpa [prev, b, n] using ihM b
          · exact ihM q

private theorem buildLayeredRing_inv (k D : Nat) :
    (∀ u : Fin (ringWires (k + 1) D), wireDepth (buildLayeredRing k D) u = u.val / (k + 1)) ∧
    (∀ u : Fin (ringWires (k + 1) D),
      maxBinaryReaderDepth (buildLayeredRing k D) u ≤ u.val / (k + 1) + 1) := by
  induction D with
  | zero =>
    dsimp [buildLayeredRing, ringWires]
    refine ⟨fun u => ?_, fun u => ?_⟩
    · have hu : u.val < k + 1 := u.isLt
      exact (Nat.div_eq_of_lt hu).symm
    · exact Nat.zero_le _
  | succ D ih =>
    exact appendRingRow_inv k D (buildLayeredRing k D) ih.1 ih.2 (k + 1) (le_refl _)

theorem source_unit_span (k D : Nat) :
    ∀ u : Fin (source k D).wires, k + 1 ≤ u.val → wireSpan (source k D).circuit u ≤ 1 := by
  intro u _
  have ⟨hD, hM⟩ := buildLayeredRing_inv k D
  unfold wireSpan
  dsimp [source]
  have huD := hD u
  have huM := hM u
  omega

/-- Automatic factor-`h` block contraction of `LayeredRing.source k D` at any stride `h ≥ 1`. -/
theorem automatic_stride_contraction (k D h : Nat) (hh : 0 < h) :
    (strideCertificate (source k D) h hh).blocks ≤ (D * (k + 1)) / h + 1 := by
  simpa [source_gateCount] using
    strideCertificate_layered_blocks_le (source k D) h hh (source_unit_span k D)

theorem subexponential (k D : Nat → Nat) (h : Nat) (hh : 0 < h)
    (hk : Tendsto k atTop atTop) {c α : ℝ} (hc : 0 ≤ c) (hα : α < 1 / 2)
    (hDepth : ∀ᶠ i in atTop,
      ((D i : ℝ) / h) ≤ c * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ α)
    (C overheadDeg : ℝ) :
    (fun i => logTimeBudget (k i + 1)
      ((k i + 1) + (strideCertificate (source (k i) (D i)) h hh).blocks) C overheadDeg)
      =o[atTop] fun i => ((k i + 1 : Nat) : ℝ) := by
  let β : ℝ := max α 0
  have hn : Tendsto (fun i => k i + 1) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b => by
      obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp hk b
      exact ⟨N, fun i hi => by have := hN i hi; omega⟩
  have hnReal : Tendsto (fun i => ((k i + 1 : Nat) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hLogN : Tendsto (fun i => Real.log (((k i + 1 : Nat) : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) hnReal)
  refine stride_contraction_subexponential (fun i => source (k i) (D i)) h hh hn
    (show (0 : ℝ) ≤ c + 1 by linarith) (max_lt hα (by norm_num) : β < 1 / 2) ?_ C overheadDeg
  filter_upwards [hDepth, hLogN.eventually_ge_atTop 1, hnReal.eventually_ge_atTop 1] with i hDi hL hN
  have hDivCast :
      ((totalTruncatedSpan (source (k i) (D i)).circuit h / h + 1 : Nat) : ℝ) ≤
        ((D i * (k i + 1) / h + 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.div_le_div_right ((totalTruncatedSpan_layered_le (source (k i) (D i)).circuit h
        (source_unit_span (k i) (D i))).trans_eq (source_gateCount (k i) (D i)))) 1
  have hNatDiv : ((D i * (k i + 1) / h + 1 : Nat) : ℝ) ≤
      (D i : ℝ) * ((k i + 1 : Nat) : ℝ) / (h : ℝ) + 1 := by
    have hhPos : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
    have hMul : ((D i * (k i + 1) / h * h : Nat) : ℝ) ≤ ((D i * (k i + 1) : Nat) : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self (D i * (k i + 1)) h
    have hCast : ((D i * (k i + 1) / h * h : Nat) : ℝ) =
        ((D i * (k i + 1) / h : Nat) : ℝ) * (h : ℝ) := by push_cast; ring
    have hCast2 : ((D i * (k i + 1) : Nat) : ℝ) = (D i : ℝ) * ((k i + 1 : Nat) : ℝ) := by
      push_cast; ring
    rw [hCast, hCast2] at hMul
    have hDiv : ((D i * (k i + 1) / h : Nat) : ℝ) ≤
        (D i : ℝ) * ((k i + 1 : Nat) : ℝ) / (h : ℝ) := (le_div_iff₀ hhPos).mpr hMul
    push_cast at hDiv ⊢
    linarith
  have hRpowGe1 : 1 ≤ (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ β :=
    Real.one_le_rpow hL (le_max_right α 0)
  have hRpowLe : (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ α ≤
      (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hL (le_max_left α 0)
  have hMain : (D i : ℝ) * ((k i + 1 : Nat) : ℝ) / (h : ℝ) ≤
      c * ((k i + 1 : Nat) : ℝ) * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ β := by
    calc
      (D i : ℝ) * ((k i + 1 : Nat) : ℝ) / (h : ℝ)
        = ((D i : ℝ) / h) * ((k i + 1 : Nat) : ℝ) := by ring
      _ ≤ (c * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ α) * ((k i + 1 : Nat) : ℝ) :=
          mul_le_mul_of_nonneg_right hDi (by positivity)
      _ ≤ (c * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ β) * ((k i + 1 : Nat) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRpowLe hc) (by positivity)
      _ = c * ((k i + 1 : Nat) : ℝ) * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ β := by ring
  have hOne : (1 : ℝ) ≤ 1 * ((k i + 1 : Nat) : ℝ) * (Real.log (((k i + 1 : Nat) : ℝ) + 16)) ^ β := by
    nlinarith
  linarith

end LayeredRing

end PvsNP
