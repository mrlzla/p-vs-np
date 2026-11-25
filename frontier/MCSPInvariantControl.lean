module

public import MCSPPermutedCut

/-! A control invariant under all permutations of the split and suffix coordinates. -/

@[expose] public section

namespace PvsNP.Frontier.InvariantControl

open Cslib Cslib.Circuits Cslib.Circuits.Boolean CommunicationCut PermutedCut
open SampleControls (agreesOn agreesOn_eq_true agreesOn_cost)
open SplitControl (blockControl active_in_certificate)

variable {r s : ℕ}

def pointEquiv (r s : ℕ) : BitString r × BitString (s + 1) ≃ Fin (2 ^ (r + (s + 1))) :=
  (Fin.appendEquiv r (s + 1)).trans (BitString.equivFin _)

def point (a : BitString r) (z : BitString (s + 1)) : Fin (2 ^ (r + (s + 1))) :=
  pointEquiv r s (a, z)

@[simp] theorem point_cons (a : BitString r) (b : Bool) (t : BitString s) :
    point a (Fin.cons b t) = position a b t := rfl

@[simp] theorem perm_point (e : Equiv.Perm (Fin (s + 1))) (a : BitString r) (z : BitString (s + 1)) :
    tablePerm (liftTail r e) (point a z) = point a (z ∘ e) := by
  change tablePerm (liftTail r e) (BitString.equivFin _ (Fin.append a z)) = _
  rw [tablePerm_at_assignment, append_comp_liftTail]
  rfl

def unit {w : ℕ} (i : Fin w) : BitString w := fun j => decide (j = i)

noncomputable def retained (w : ℕ) : Finset (BitString w) := open scoped Classical in
  (Finset.univ.image (unit : Fin w → BitString w))ᶜ

def weight {w : ℕ} (z : BitString w) : ℕ := (Finset.univ.filter fun i => z i = true).card

def lowWeight {w : ℕ} (z : BitString w) : Bool := decide (weight z ≤ 3)

theorem unit_injective (w : ℕ) : Function.Injective (unit : Fin w → BitString w) := by
  intro i j h
  have he := congrFun h i
  simp [unit] at he
  exact he

theorem unit_perm {w : ℕ} (i : Fin w) (e : Equiv.Perm (Fin w)) :
    unit i ∘ e = unit (e.symm i) := by
  funext j
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, unit, decide_eq_true_eq]
  exact ⟨fun h => e.injective (h.trans (e.apply_symm_apply i).symm),
    fun h => (congrArg e h).trans (e.apply_symm_apply i)⟩

theorem retained_card (w : ℕ) : (retained w).card = 2 ^ w - w := by
  classical
  rw [retained, Finset.card_compl, BitString.card,
    Finset.card_image_of_injective _ (unit_injective w), Finset.card_univ, Fintype.card_fin]

theorem weight_perm {w : ℕ} (z : BitString w) (e : Equiv.Perm (Fin w)) :
    weight (z ∘ e) = weight z := by
  classical
  have he :
      (Finset.univ.filter (fun i => (z ∘ e) i = true)).map e.toEmbedding =
      Finset.univ.filter (fun i => z i = true) := by
    ext i
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    rw [e.apply_symm_apply]
  unfold weight
  rw [← Finset.card_map (f := e.toEmbedding), he]

theorem lowWeight_perm {w : ℕ} (z : BitString w) (e : Equiv.Perm (Fin w)) :
    lowWeight (z ∘ e) = lowWeight z := by
  unfold lowWeight
  rw [weight_perm]

theorem retained_perm {w : ℕ} (z : BitString w) (e : Equiv.Perm (Fin w)) :
    z ∘ e ∈ retained w ↔ z ∈ retained w := by
  classical
  simp only [retained, Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    rintro ⟨i, rfl⟩
    exact h ⟨e.symm i, (unit_perm i e).symm⟩
  · intro h
    rintro ⟨i, hi⟩
    apply h
    refine ⟨e i, ?_⟩
    have he := congrArg (fun t : BitString w => t ∘ e.symm) hi
    rw [unit_perm] at he
    simpa [Function.comp_def] using he

noncomputable def band (w : ℕ) (b : Bool) : Finset (BitString w) :=
  (retained w).filter (fun z => lowWeight z = b)

noncomputable def block (q : BitString r × Bool) : Finset (Fin (2 ^ (r + (s + 1)))) :=
  (band (s + 1) q.2).image (point q.1)

noncomputable def control (r s : ℕ) : BooleanFunction (2 ^ (r + (s + 1))) :=
  blockControl (block (r := r) (s := s))

theorem point_mem_block (a : BitString r) {z : BitString (s + 1)} {b : Bool}
    (hz : z ∈ retained (s + 1)) (hu : lowWeight z = b) :
    point a z ∈ block (a, b) :=
  Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hu⟩, rfl⟩

theorem control_iff (T : BitString (2 ^ (r + (s + 1)))) :
    control r s T = true ↔
      ∀ (a : BitString r) (z z' : BitString (s + 1)), z ∈ retained (s + 1) →
        z' ∈ retained (s + 1) → lowWeight z = lowWeight z' → T (point a z) = T (point a z') := by
  classical
  rw [control, blockControl, decide_eq_true_eq]
  constructor
  · intro h a z z' hz hz' he
    exact (agreesOn_eq_true _ _).mp (h (a, lowWeight z)) _ (point_mem_block a hz rfl)
      _ (point_mem_block a hz' he.symm)
  · intro h q
    apply (agreesOn_eq_true _ _).mpr
    intro i hi j hj
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hz, he⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz', he'⟩ := Finset.mem_filter.mp hz'
    exact h q.1 z z' hz hz' (he.trans he'.symm)

theorem control_perm (e : Equiv.Perm (Fin (s + 1))) (T : BitString (2 ^ (r + (s + 1)))) :
    control r s (T ∘ tablePerm (liftTail r e)) = control r s T := by
  apply Bool.eq_iff_iff.mpr
  simp only [control_iff]
  constructor
  · intro h a z z' hz hz' he
    have hh := h a (z ∘ e.symm) (z' ∘ e.symm) ((retained_perm z e.symm).mpr hz)
      ((retained_perm z' e.symm).mpr hz') (by simpa only [lowWeight_perm] using he)
    simpa [Function.comp_def] using hh
  · intro h a z z' hz hz' he
    simpa only [Function.comp_apply, perm_point] using
      h a (z ∘ e) (z' ∘ e) ((retained_perm z e).mpr hz)
        ((retained_perm z' e).mpr hz') (by simpa only [lowWeight_perm] using he)

theorem block_card (q : BitString r × Bool) :
    (block (s := s) q).card = (band (s + 1) q.2).card := by
  unfold block
  apply Finset.card_image_of_injective
  intro z z' he
  exact congrArg Prod.snd ((pointEquiv r s).injective he)

theorem band_card_sum (w : ℕ) :
    (band w false).card + (band w true).card = (retained w).card := by
  classical
  have he : (retained w).filter (fun z => ¬ lowWeight z = false) = band w true := by
    ext z
    cases hb : lowWeight z <;> simp [band, hb]
  have h := Finset.card_filter_add_card_filter_not (s := retained w) (p := fun z => lowWeight z = false)
  rwa [he] at h

theorem control_size (r s : ℕ) :
    complexity interpretation (single (control r s)) ≤
      2 * (2 ^ r * (retained (s + 1)).card) + 5 * (2 ^ r * 2) + 1 := by
  classical
  let keys := (Finset.univ : Finset (BitString r × Bool))
  let B := block (r := r) (s := s)
  have hSynth := Synthesis.forall_mem keys (fun q => agreesOn (B q)) (fun q => 2 * (B q).card + 4)
    (fun q _ => agreesOn_cost (B q))
  have h := Synthesis.congr_iff hSynth (g := control r s) (fun x => by simp [control, blockControl, keys, B])
  have hSum : (∑ q : BitString r × Bool, (B q).card) = 2 ^ r * (retained (s + 1)).card := by
    simp only [B, block_card, Fintype.sum_prod_type, Fintype.sum_bool]
    rw [add_comm (band (s + 1) true).card, band_card_sum]
    simp
  have hKeys : keys.card = 2 ^ r * 2 := by simp [keys, Fintype.card_prod]
  apply h.complexity_le.trans
  have hs : (∑ q ∈ keys, (B q).card) = 2 ^ r * (retained (s + 1)).card := hSum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.nsmul_eq_mul, hs, hKeys]
  omega

noncomputable def active (r s : ℕ) : Finset (Fin (2 ^ (r + (s + 1)))) :=
  ((Finset.univ : Finset (BitString r)) ×ˢ retained (s + 1)).map (pointEquiv r s).toEmbedding

theorem active_card (r s : ℕ) : (active r s).card = 2 ^ r * (retained (s + 1)).card := by
  classical
  simp [active, Finset.card_product]

theorem control_acceptance_count (r s : ℕ)
    (hband : ∀ b : Bool, ∃ z ∈ retained (s + 1), lowWeight z = b) :
    (acceptingTables (control r s)).card ≤ 2 ^ (2 ^ r * 2 + 2 ^ r * (s + 1)) := by
  classical
  let representative (b : Bool) := (hband b).choose
  let tables := acceptingTables (control r s)
  let code (x : tables) : ((BitString r × Bool) → Bool) × ((BitString r × Fin (s + 1)) → Bool) :=
    (fun q => x.val (point q.1 (representative q.2)),
      fun q => x.val (point q.1 (unit q.2)))
  have hinj : Function.Injective code := by
    intro x y he
    apply Subtype.ext
    funext i
    obtain ⟨⟨a, z⟩, rfl⟩ := (pointEquiv r s).surjective i
    change x.val (point a z) = y.val (point a z)
    by_cases hz : z ∈ retained (s + 1)
    · have hr := (hband (lowWeight z)).choose_spec
      have hx := (control_iff _).mp (Finset.mem_filter.mp x.property).2 a z
        (representative (lowWeight z)) hz hr.1 hr.2.symm
      have hy := (control_iff _).mp (Finset.mem_filter.mp y.property).2 a z
        (representative (lowWeight z)) hz hr.1 hr.2.symm
      exact hx.trans ((congrFun (congrArg Prod.fst he) (a, lowWeight z)).trans hy.symm)
    · have hu : z ∈ Finset.univ.image (unit : Fin (s + 1) → BitString (s + 1)) := by
        simpa [retained] using hz
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
      exact congrFun (congrArg Prod.snd he) (a, j)
  have h := Fintype.card_le_of_injective code hinj
  simpa [tables, Fintype.card_prod, Fintype.card_fun, BitString.card, pow_add] using h

theorem control_inputStates_card (r s : ℕ)
    (mate : ∀ z ∈ retained (s + 1), ∃ z' ∈ retained (s + 1), lowWeight z' = lowWeight z ∧ z' ≠ z)
    (c : Circuit signature (2 ^ (r + (s + 1))) 1)
    (hc : c.Computes interpretation (single (control r s)))
    (sample : Finset (BitString (2 ^ (r + (s + 1))))) (b : Bool) (hb : (fun _ => b) ∈ sample) :
    2 ^ r * (retained (s + 1)).card ≤
      (MultiCertificates.inputStates c.program (c.outputs 0) sample b).card := by
  classical
  have h := active_in_certificate (block (r := r) (s := s)) (active r s)
    (fun i hi => by
      obtain ⟨⟨a, z⟩, hmem, rfl⟩ := Finset.mem_map.mp hi
      have hz := (Finset.mem_product.mp hmem).2
      obtain ⟨z', hz', he, hne⟩ := mate z hz
      refine ⟨(a, lowWeight z), point_mem_block a hz rfl, point a z',
        point_mem_block a hz' he, ?_⟩
      intro h
      exact hne (congrArg Prod.snd ((pointEquiv r s).injective h)))
    c hc sample b hb
  rw [← active_card r s]
  exact (Finset.card_le_card h).trans (Finset.card_le_card fun _ hi => (Finset.mem_filter.mp hi).2)

end PvsNP.Frontier.InvariantControl
