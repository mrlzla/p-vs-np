module

public import MCSPBatchRank
public import Mathlib.FieldTheory.Finiteness

/-! A sparse residual needs independent traces modulo its raw inputs.
A pivot costs at most one linear constraint on a subspace through an
accepting input. A gate that reads a constant consumes no residual pivot. -/

@[expose] public section

namespace PvsNP.Frontier.ResidualTraceRank

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open BatchRank RestrictionCharges ForestPinning DownstreamBlockPinning
open scoped Classical BigOperators

section Linearization

variable {V : Type*} [AddCommGroup V] [Module F₂ V]

/-- Functions agreeing with a linear functional on the chosen subspace. -/
def linearOn (W : Submodule F₂ V) : Submodule F₂ (V → F₂) where
  carrier := {f | ∃ L : V →ₗ[F₂] F₂, ∀ x ∈ W, f x = L x}
  zero_mem' := ⟨0,fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨L,hL⟩ ⟨M,hM⟩
    exact ⟨L+M,fun x hx => by change f x+g x = L x+M x; rw [hL x hx,hM x hx]⟩
  smul_mem' := by
    rintro a f ⟨L,hL⟩
    exact ⟨a • L,fun x hx => by change a * f x = a * L x; rw [hL x hx]⟩

theorem linearOn_mono {W U : Submodule F₂ V} (hWU : W ≤ U) :
    linearOn U ≤ linearOn W := by
  rintro f ⟨L,hL⟩
  exact ⟨L,fun x hx => hL x (hWU hx)⟩

private theorem kernel_cut (W : Submodule F₂ V) [Module.Finite F₂ V] (L : V →ₗ[F₂] F₂) :
    Module.finrank F₂ W ≤ Module.finrank F₂ ↥(W ⊓ LinearMap.ker L)+1 := by
  have h := L.finrank_range_add_finrank_ker
  have hR : Module.finrank F₂ (LinearMap.range L) ≤ 1 :=
    (Submodule.finrank_le _).trans_eq (Module.finrank_self F₂)
  have hSup := Submodule.finrank_sup_add_finrank_inf_eq (K := F₂) W (LinearMap.ker L)
  have hTop := Submodule.finrank_le (W ⊔ LinearMap.ker L)
  omega

private theorem linearize_gate (W : Submodule F₂ V) [Module.Finite F₂ V]
    (op : Op) (base : Fin (signature.Arity op) → Bool)
    (T : V → Fin (signature.Arity op) → Bool)
    (hInputs : ∀ j, (fun i => bit (base j ^^ T i j)) ∈ linearOn W) :
    ∃ W' ≤ W, Module.finrank F₂ W ≤ Module.finrank F₂ W'+1 ∧
      (fun i => bit (interpretation op base ^^ interpretation op (T i))) ∈ linearOn W' := by
  let d (j : Fin (signature.Arity op)) (i : V) := bit (base j ^^ T i j)
  have hProduct : ∃ W' ≤ W, Module.finrank F₂ W ≤ Module.finrank F₂ W'+1 ∧
      gateProduct op d ∈ linearOn W' := by
    have hMul (f g : V → F₂) (hf : f ∈ linearOn W) :
        ∃ W' ≤ W, Module.finrank F₂ W ≤ Module.finrank F₂ W'+1 ∧ (f*g) ∈ linearOn W' := by
      obtain ⟨L,hL⟩ := hf
      refine ⟨W ⊓ LinearMap.ker L, inf_le_left, kernel_cut W L, ⟨0,?_⟩⟩
      intro z h
      have hz : L z = 0 := LinearMap.mem_ker.mp h.2
      change f z*g z = 0
      rw [hL z h.1, hz, zero_mul]
    cases op with
    | const b => exact ⟨W,le_rfl,Nat.le_succ _,(linearOn W).zero_mem⟩
    | not => exact ⟨W,le_rfl,Nat.le_succ _,(linearOn W).zero_mem⟩
    | and => exact hMul (d 0) (d 1) (hInputs 0)
    | or => exact hMul (d 0) (d 1) (hInputs 0)
  obtain ⟨W',hSub,hDim,hP⟩ := hProduct
  exact ⟨W',hSub,hDim,gate_centered_mem _ op base T
    (fun j => linearOn_mono hSub (hInputs j)) hP⟩

end Linearization

section Prefix

variable {I : Type*} {n g : ℕ}

noncomputable def rawSpan (base : BitString n) (T : I → BitString n) :
    Submodule F₂ (I → F₂) :=
  Submodule.span F₂ (Set.range (raw base T))

noncomputable def traceSpan (p : Program signature n g) (base : BitString n) (T : I → BitString n) :
    Submodule F₂ ((I → F₂) ⧸ rawSpan base T) :=
  Submodule.span F₂ (Set.range (fun w => (rawSpan base T).mkQ (centered p base T w)))

noncomputable def traceRank [Fintype I] (p : Program signature n g) (base : BitString n)
    (T : I → BitString n) : ℕ := Module.finrank F₂ (traceSpan p base T)

private theorem centered_cast (p : Program signature n g) (L : Line signature n g)
    (base : BitString n) (T : I → BitString n) (w : Wire n g) :
    centered (p.gate L) base T w.castSucc = centered p base T w := by
  funext i
  simp only [centered, Program.trace_gate_castSucc]

private theorem centered_last (p : Program signature n g) (L : Line signature n g)
    (base : BitString n) (T : I → BitString n) :
    centered (p.gate L) base T (.gate (Fin.last g)) =
      fun i => bit (interpretation L.op (fun j => p.trace interpretation base (L.wires j)) ^^
        interpretation L.op (fun j => p.trace interpretation (T i) (L.wires j))) := by
  funext i
  unfold centered
  change bit ((p.gate L).eval interpretation base (Fin.last g) ^^
    (p.gate L).eval interpretation (T i) (Fin.last g)) = _
  rw [Program.eval_gate_last, Program.eval_gate_last]
  rfl

private theorem traceSpan_step (p : Program signature n g) (L : Line signature n g)
    (base : BitString n) (T : I → BitString n) :
    traceSpan (p.gate L) base T =
      traceSpan p base T ⊔ Submodule.span F₂
        {(rawSpan base T).mkQ (centered (p.gate L) base T (.gate (Fin.last g)))} := by
  let q := (rawSpan base T).mkQ
  let e := q (centered (p.gate L) base T (.gate (Fin.last g)))
  have he : Set.range (fun w => q (centered (p.gate L) base T w)) =
      insert e (Set.range (fun w => q (centered p base T w))) := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      refine Wire.lastCases ?_ (fun u => ?_) w
      · exact Set.mem_insert _ _
      · change q (centered (p.gate L) base T u.castSucc) ∈ insert e _
        rw [centered_cast]
        exact Set.mem_insert_of_mem _ ⟨u,rfl⟩
    · intro hz
      rcases Set.mem_insert_iff.mp hz with rfl | ⟨w,rfl⟩
      · exact ⟨.gate (Fin.last g),rfl⟩
      · exact ⟨w.castSucc, congrArg q (centered_cast p L base T w)⟩
  change Submodule.span F₂ (Set.range (fun w => q (centered (p.gate L) base T w))) =
    traceSpan p base T ⊔ Submodule.span F₂ {e}
  rw [he, Submodule.span_insert, sup_comm]
  rfl

private theorem mem_space_of_quotient_mem (p : Program signature n g) (base : BitString n)
    (T : I → BitString n) (S : Submodule F₂ (I → F₂))
    (hW : ∀ w, centered p base T w ∈ S) {z : I → F₂}
    (hz : (rawSpan base T).mkQ z ∈ traceSpan p base T) : z ∈ S := by
  let U := rawSpan base T
  let q := U.mkQ
  have hU : U ≤ S := Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    exact hW (.input i))
  have hRange : traceSpan p base T ≤ S.map q := Submodule.span_le.mpr (by
    rintro _ ⟨w,rfl⟩
    exact Submodule.mem_map.mpr ⟨_,hW w,rfl⟩)
  obtain ⟨v,hv,he⟩ := Submodule.mem_map.mp (hRange hz)
  have hh : z-v ∈ LinearMap.ker q := LinearMap.mem_ker.mpr (by rw [map_sub, he, sub_self])
  have hk : z-v ∈ U := by
    change z-v ∈ LinearMap.ker U.mkQ at hh
    rwa [Submodule.ker_mkQ] at hh
  have hs := S.add_mem (hU hk) hv
  simpa only [sub_add_cancel] using hs

end Prefix

section Main

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] [Module.Finite F₂ V]
variable {n g : ℕ}

/-- Restrict by at most one linear equation per new quotient direction.
Every original wire is linear on the resulting subspace. -/
theorem linear_subspace_of_traceRank (p : Program signature n g) (base : BitString n)
    (T : V → BitString n) (hRaw : ∀ i, raw base T i ∈ linearOn (⊤ : Submodule F₂ V)) :
    ∃ W : Submodule F₂ V, Module.finrank F₂ V ≤ Module.finrank F₂ W+traceRank p base T ∧
      ∀ w, centered p base T w ∈ linearOn W := by
  induction p with
  | empty =>
    refine ⟨⊤,?_,?_⟩
    · rw [finrank_top]
      omega
    · intro w
      cases w with
      | input i => exact hRaw i
      | gate j => exact j.elim0
  | @gate g p L ih =>
    obtain ⟨W,hW,hLinear⟩ := ih
    let out := centered (p.gate L) base T (.gate (Fin.last g))
    let e := (rawSpan base T).mkQ out
    have hStep : traceSpan (p.gate L) base T = traceSpan p base T ⊔ Submodule.span F₂ {e} :=
      traceSpan_step p L base T
    by_cases he : e ∈ traceSpan p base T
    · refine ⟨W,?_ ,?_⟩
      · change Module.finrank F₂ V ≤ Module.finrank F₂ W+Module.finrank F₂ (traceSpan (p.gate L) base T)
        rw [hStep, sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using he))]
        exact hW
      · refine Wire.lastCases ?_ (fun w => ?_)
        · exact mem_space_of_quotient_mem p base T (linearOn W) hLinear he
        · rw [centered_cast]
          exact hLinear w
    · obtain ⟨W',hSub,hDim,hGate⟩ := linearize_gate W L.op
        (fun j => p.trace interpretation base (L.wires j))
        (fun z j => p.trace interpretation (T z) (L.wires j)) (fun j => hLinear (L.wires j))
      refine ⟨W',?_ ,?_⟩
      · have hR : traceRank (p.gate L) base T = traceRank p base T+1 := by
          change Module.finrank F₂ (traceSpan (p.gate L) base T) =
            Module.finrank F₂ (traceSpan p base T)+1
          rw [hStep, Submodule.finrank_sup_span_singleton he]
        omega
      · refine Wire.lastCases ?_ (fun w => ?_)
        · rw [centered_last]
          exact hGate
        · rw [centered_cast]
          exact linearOn_mono hSub (hLinear w)

theorem constant_subspace_of_traceRank (p : Program signature n g) (base : BitString n)
    (T : V → BitString n) (hRaw : ∀ i, raw base T i ∈ linearOn (⊤ : Submodule F₂ V))
    (out : Wire n g) :
    ∃ W : Submodule F₂ V, Module.finrank F₂ V ≤ Module.finrank F₂ W+traceRank p base T+1 ∧
      ∀ z ∈ W, p.trace interpretation (T z) out = p.trace interpretation base out := by
  obtain ⟨U,hDim,hL⟩ := linear_subspace_of_traceRank p base T hRaw
  obtain ⟨L,hLinear⟩ := hL out
  have hCut := kernel_cut U L
  refine ⟨U ⊓ LinearMap.ker L,by omega,?_⟩
  intro z hz
  have h0 := hLinear z hz.1
  rw [LinearMap.mem_ker.mp hz.2] at h0
  change bit (p.trace interpretation base out ^^ p.trace interpretation (T z) out) = 0 at h0
  have hbit (a b : Bool) (h : bit (a ^^ b) = 0) : b = a := by cases a <;> cases b <;> simp [bit] at h ⊢
  exact hbit _ _ h0

end Main

section PinBatch

variable {n k g : ℕ}

/-- Label the residual assignments by field-valued perturbations from one
accepting assignment. This is a bijective change of assignment coordinates. -/
def perturb (a : BitString k) (z : Fin k → F₂) : BitString k :=
  fun i => a i ^^ decide (z i = 1)

private theorem bit_of_field (z : F₂) : bit (decide (z = 1)) = z := by
  fin_cases z
  · change bit (decide ((0 : F₂) = 1)) = 0
    simp [bit]
  · change bit (decide ((1 : F₂) = 1)) = 1
    simp [bit]

private theorem bit_perturb (a : BitString k) (z : Fin k → F₂) (i : Fin k) :
    bit (a i ^^ perturb a z i) = z i := by
  have h (x y : Bool) : (x ^^ (x ^^ y)) = y := by cases x <;> cases y <;> rfl
  unfold perturb
  rw [h, bit_of_field]

theorem perturb_injective (a : BitString k) : Function.Injective (perturb a) := by
  intro z w h
  funext i
  have hh := congrArg (fun b => bit (a i ^^ b)) (congrFun h i)
  rw [bit_perturb,bit_perturb] at hh
  exact hh

noncomputable def pinRank (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) : ℕ :=
  traceRank p (substitute pin a) (fun z => substitute pin (perturb a z))

theorem pin_raw_linear (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) (i : Fin n) :
    raw (substitute pin a) (fun z => substitute pin (perturb a z)) i ∈
      linearOn (⊤ : Submodule F₂ (Fin k → F₂)) := by
  cases he : pin i with
  | inl j =>
    refine ⟨LinearMap.proj j,fun z _ => ?_⟩
    change bit (substitute pin a i ^^ substitute pin (perturb a z) i) = z j
    simp only [substitute,he,Sum.elim_inl,bit_perturb]
  | inr b =>
    refine ⟨0,fun z _ => ?_⟩
    simp [raw,substitute,he,bit]

open CornerCertificates in
/-- On a sparse nonempty restriction the original quotient traces need at
least k-B-1 independent dimensions on the residual input cube. -/
theorem pinRank_lower (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) (out : Wire n g) (B : ℕ)
    (hYes : restrictedWire p pin out a = true)
    (hSparse : (acceptingTables (restrictedWire p pin out)).card ≤ 2^B) :
    k ≤ B+pinRank p pin a+1 := by
  obtain ⟨W,hDim,hTrue⟩ := constant_subspace_of_traceRank p (substitute pin a)
    (fun z => substitute pin (perturb a z)) (pin_raw_linear pin a) out
  let f := restrictedWire p pin out
  let into (z : W) : acceptingTables f :=
    ⟨perturb a z.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hTrue z.val z.property).trans hYes⟩⟩
  have hi : Function.Injective into := fun _ _ he =>
    Subtype.ext (perturb_injective a (congrArg Subtype.val he))
  have hCard := Fintype.card_le_of_injective into hi
  rw [Module.card_eq_pow_finrank (K := F₂) (V := W), ZMod.card, Fintype.card_coe] at hCard
  have hB := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hCard.trans hSparse)
  have hDim' : k ≤ Module.finrank F₂ W+pinRank p pin a+1 := by
    simpa only [pinRank, Module.finrank_pi, Fintype.card_fin] using hDim
  omega

private theorem gateProduct_zero_on_port {I : Type*} (op : Op)
    (d : Fin (signature.Arity op) → I → F₂) (b : Fin (signature.Arity op)) (hb : d b = 0) :
    gateProduct op d = 0 := by
  cases op with
  | const _ => rfl
  | not => rfl
  | and =>
    fin_cases b
    · change d 0 = 0 at hb
      simp [gateProduct,hb]
    · change d 1 = 0 at hb
      simp [gateProduct,hb]
  | or =>
    fin_cases b
    · change d 0 = 0 at hb
      simp [gateProduct,hb]
    · change d 1 = 0 at hb
      simp [gateProduct,hb]

/-- A constant-reading gate contributes the zero interaction to this
entire restricted batch. Its wire may still copy another trace. -/
theorem pin_interaction_zero_of_constantReader (p : Program signature n g)
    (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) {j : Fin g} (hj : j ∈ constantReaders p pin) :
    interaction p (substitute pin a) (fun z => substitute pin (perturb a z)) j = 0 := by
  obtain ⟨b,c,hc⟩ := (Finset.mem_filter.mp hj).2
  apply gateProduct_zero_on_port _ _ b
  funext z
  have hA := congrFun hc a
  have hZ := congrFun hc (perturb a z)
  change bit (restrictedWire p pin ((p.lines j).wires b) a ^^
      restrictedWire p pin ((p.lines j).wires b) (perturb a z)) = 0
  simp [hA,hZ,bit]

noncomputable def pinQuotientTrace (p : Program signature n g)
    (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) (j : Fin g) :
    ((Fin k → F₂) → F₂) ⧸ rawSpan (substitute pin a) (fun z => substitute pin (perturb a z)) :=
  let base := substitute pin a
  let T (z : Fin k → F₂) := substitute pin (perturb a z)
  (rawSpan base T).mkQ (centered p base T (.gate j))

/-- The quotient is spanned by the actual gate traces of binary gates
that have no constant input under the restriction. -/
theorem pin_traceSpan_eq_active (p : Program signature n g)
    (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) :
    traceSpan p (substitute pin a) (fun z => substitute pin (perturb a z)) =
      Submodule.span F₂ (Set.range (fun j : ↥(binaryGates p \ constantReaders p pin) =>
        pinQuotientTrace p pin a j.val)) := by
  let base := substitute pin a
  let T (z : Fin k → F₂) := substitute pin (perturb a z)
  let U := rawSpan base T
  let S := binaryGates p \ constantReaders p pin
  let gen (j : S) := pinQuotientTrace p pin a j.val
  let V := Submodule.span F₂ (Set.range gen)
  change traceSpan p base T = V
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    change U.mkQ (centered p base T w) ∈ V
    refine p.wire_induction (P := fun w => U.mkQ (centered p base T w) ∈ V) ?_ ?_ w
    · intro i
      change U.mkQ (raw base T i) ∈ V
      have hk : raw base T i ∈ LinearMap.ker U.mkQ := by
        rw [Submodule.ker_mkQ]
        exact Submodule.subset_span ⟨i,rfl⟩
      rw [LinearMap.mem_ker.mp hk]
      exact V.zero_mem
    · intro j ih
      by_cases hj : j ∈ S
      · exact Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩
      · have hz : interaction p base T j = 0 := by
          by_cases hC : j ∈ constantReaders p pin
          · exact pin_interaction_zero_of_constantReader p pin a hC
          · have hBin : j ∉ binaryGates p := fun h => hj (Finset.mem_sdiff.mpr ⟨h,hC⟩)
            exact gateProduct_eq_zero _ (fun h => hBin (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)) _
        have hProd : interaction p base T j ∈ V.comap U.mkQ := by
          rw [hz]
          exact (V.comap U.mkQ).zero_mem
        change centered p base T (.gate j) ∈ V.comap U.mkQ
        unfold centered
        simp only [p.trace_gate]
        exact gate_centered_mem _ _ _ _ ih hProd
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span ⟨Wire.gate j.val,rfl⟩

theorem pinRank_le_active_binary (p : Program signature n g)
    (pin : Fin n → Fin k ⊕ Bool) (a : BitString k) :
    pinRank p pin a ≤ (binaryGates p \ constantReaders p pin).card := by
  unfold pinRank traceRank
  rw [pin_traceSpan_eq_active]
  exact (finrank_range_le_card (fun j : ↥(binaryGates p \ constantReaders p pin) =>
    pinQuotientTrace p pin a j.val)).trans_eq (Fintype.card_coe _)

/-- Select independent vectors from original gate indices and leave every
constant-reading gate available for the separate loss accounting. -/
theorem pin_independent_active (p : Program signature n g) (pin : Fin n → Fin k ⊕ Bool)
    (a : BitString k) :
    ∃ pick : Fin (pinRank p pin a) ↪ Fin g,
      (∀ i, pick i ∈ binaryGates p \ constantReaders p pin) ∧
      LinearIndependent F₂ (fun i => pinQuotientTrace p pin a (pick i)) := by
  let S := binaryGates p \ constantReaders p pin
  let gen (j : S) := pinQuotientTrace p pin a j.val
  have he : pinRank p pin a = Module.finrank F₂ (Submodule.span F₂ (Set.range gen)) := by
    unfold pinRank traceRank
    rw [pin_traceSpan_eq_active]
  rw [he]
  obtain ⟨f,hf,_,hli⟩ := Submodule.exists_fun_fin_finrank_span_eq F₂ (Set.range gen)
  choose j hj using hf
  have hVec : (fun i => pinQuotientTrace p pin a (j i).val) = f := funext hj
  have hi : Function.Injective (fun i => (j i).val) := by
    intro u v h
    apply hli.injective
    rw [← hj u,← hj v]
    exact congrArg (pinQuotientTrace p pin a) h
  exact ⟨⟨_,hi⟩,fun i => (j i).property,hVec.symm ▸ hli⟩

theorem pinRank_with_reader_losses (p : Program signature n g)
    (P : Finset (Fin n)) (x a : BitString n) :
    pinRank p (pinAt x P) a + (directReaders p P).card +
      (downstreamReaders p P x).card ≤ g := by
  let C := constantReaders p (pinAt x P)
  have hD := Finset.card_sdiff_add_card_eq_card (directReaders_subset_constantReaders p P x)
  have hR := pinRank_le_active_binary p (pinAt x P) a
  have hSub : binaryGates p \ C ⊆ Finset.univ \ C := by
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hj).2⟩
  have hLe := Finset.card_le_card hSub
  have hG := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
  simp only [Finset.card_univ,Fintype.card_fin] at hG
  change (downstreamReaders p P x).card+(directReaders p P).card = C.card at hD
  change pinRank p (pinAt x P) a ≤ (binaryGates p \ C).card at hR
  omega

end PinBatch

section BatchExtension

variable {I J D : Type*} {n g : ℕ}

private def restrictProfile (select : J → I) : (I → F₂) →ₗ[F₂] (J → F₂) where
  toFun f := f ∘ select
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Independent gate traces modulo raw inputs on a slice are independent in
any larger batch containing that slice, with the same centering input. -/
theorem independent_lifts_from_slice (p : Program signature n g) (base : BitString n)
    (T : I → BitString n) (select : J → I) (pick : D → Fin g)
    (h : LinearIndependent F₂ (fun i => (rawSpan base (T ∘ select)).mkQ
      (centered p base (T ∘ select) (.gate (pick i))))) :
    LinearIndependent F₂ (fun i => (rawSpan base T).mkQ
      (centered p base T (.gate (pick i)))) := by
  let U := rawSpan base T
  let U' := rawSpan base (T ∘ select)
  let q := U'.mkQ.comp (restrictProfile select)
  have hRaw : U ≤ LinearMap.ker q := Submodule.span_le.mpr (by
    rintro _ ⟨i,rfl⟩
    apply LinearMap.mem_ker.mpr
    change U'.mkQ (raw base (T ∘ select) i) = 0
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact Submodule.subset_span ⟨i,rfl⟩)
  let L := U.liftQ q hRaw
  apply LinearIndependent.of_comp L
  have he : (L ∘ fun i => U.mkQ (centered p base T (.gate (pick i)))) =
      fun i => U'.mkQ (centered p base (T ∘ select) (.gate (pick i))) := by
    funext i
    change U.liftQ q hRaw (Submodule.Quotient.mk (centered p base T (.gate (pick i)))) = _
    rw [Submodule.liftQ_apply]
    rfl
  rwa [he]

end BatchExtension

section Applications

open CornerCertificates JointSparseCompletion MultiBlockPinning QuadraticForest

set_option exponentiation.threshold 30000 in
/-- The same eleven-exit joint restriction preserves billions of independent
original gate traces, all from outside the constant-reader loss set. -/
theorem mcsp32_joint_independent (c : Circuit signature (2^32) 1)
    (hc : c.Computes interpretation (single (mcspSquare 32)))
    (hMin : c.size = complexity interpretation (single (mcspSquare 32)))
    (hSize : c.size ≤ 3*(2^32)) :
    ∃ (E : Finset (BitString 28)) (x : BitString (2^32)) (exit : E ↪ Fin c.size),
      E.card = 11 ∧
      (∀ s : E, exit s ∈ downstreamReaders c.program (blocks (d := 4) E) x) ∧
      (let pin := pinAt x (blocks (d := 4) E)
       ∃ pick : Fin 4294948381 ↪ Fin c.size,
         (∀ i, pick i ∈ binaryGates c.program \ constantReaders c.program pin) ∧
         LinearIndependent F₂ (fun i => pinQuotientTrace c.program pin (fun _ => false) (pick i))) := by
  obtain ⟨E,x,exit,hE,hExit,hS,hQ,_⟩ := mcsp32_eleven_joint_exits c hc hMin hSize
  let P := blocks (d := 4) E
  let pin := pinAt x P
  let p := c.program
  let a : BitString (2^32) := fun _ => false
  have hEq := NestedFaces.restricted_circuit_eq c hc pin
  have hYes : restrictedWire p pin (c.outputs 0) a = true := by
    have h := hQ (zeroVec 32) false (zeroVec 32) (zeroVec 32)
    have he : MCSP.truthTable 32 (quad (zeroVec 32) false (zeroVec 32) (zeroVec 32)) = a := by
      funext i
      simp only [MCSP.truthTable_apply,quad,SuperTwoN.affine,dot_zero_left,Bool.and_false,Bool.xor_false]
      rfl
    rw [he] at h
    rw [hEq]
    exact h
  have hSparse : (acceptingTables (restrictedWire p pin (c.outputs 0))).card ≤ 2^18914 := by
    rw [hEq]
    exact hS
  have hRank := pinRank_lower p pin a (c.outputs 0) 18914 hYes hSparse
  have hDim : 4294948381 ≤ pinRank p pin a := by norm_num at hRank; omega
  obtain ⟨pick,hPick,hLI⟩ := pin_independent_active p pin a
  let emb : Fin 4294948381 ↪ Fin (pinRank p pin a) :=
    ⟨Fin.castLE hDim,Fin.castLE_injective hDim⟩
  refine ⟨E,x,exit,hE,fun s => (hExit s).2,emb.trans pick,fun i => hPick (emb i),?_⟩
  exact hLI.comp emb emb.injective

/-- Applying the same sparsity argument to the existing signed-AND control
also forces a large independent family. The one shared downstream gate
continues to contribute zero interaction across the all-one restrictions. -/
theorem signedAnd_independent_under_allOne_pins (r : ℕ) (hr : 10 ≤ r) :
    let m := JointOrbit.logArity r
    let N := 2^m
    ∃ (c : Circuit signature N 1) (shared : Fin c.size),
      c.Computes interpretation (single (GrowingAndOrbit.control r hr)) ∧
      c.size ≤ 5104*(r+1)*N ∧
      ∀ P : Finset (Fin N), P.Nonempty → P.card ≤ 2^(m-1) →
        let a : BitString N := fun _ => true
        let pin := pinAt a P
        shared ∈ downstreamReaders c.program P a ∧
        interaction c.program (substitute pin a) (fun z => substitute pin (perturb a z)) shared = 0 ∧
        ∃ pick : Fin (N-(descriptionBitBound m+P.card+1)) ↪ Fin c.size,
          (∀ i, pick i ∈ binaryGates c.program \ constantReaders c.program pin) ∧
          LinearIndependent F₂ (fun i => pinQuotientTrace c.program pin a (pick i)) := by
  let m := JointOrbit.logArity r
  let N := 2^m
  let f := GrowingAndOrbit.control r hr
  obtain ⟨c,hc,hSize,j,hShared⟩ := ChargeMultiplicity.signedAnd_control_shared_reader r hr
  refine ⟨c,j,hc,hSize,?_⟩
  intro P hP hHalf
  let a : BitString N := fun _ => true
  let pin := pinAt a P
  have hShare := (hShared P hP hHalf).1
  have h0 := pin_interaction_zero_of_constantReader c.program pin a (Finset.mem_sdiff.mp hShare).1
  refine ⟨hShare,h0,?_⟩
  have hEq := NestedFaces.restricted_circuit_eq c hc pin
  have hYes : restrictedWire c.program pin (c.outputs 0) a = true := by
    rw [hEq]
    have he : substitute pin a = a := by
      funext i
      by_cases hi : i ∈ P <;> simp [pin,substitute,pinAt,hi]
    change f (substitute pin a) = true
    rw [he]
    exact ChargeMultiplicity.signedAnd_constant r hr true
  have hSparse : (acceptingTables (restrictedWire c.program pin (c.outputs 0))).card ≤
      2^(descriptionBitBound m+P.card) := by
    rw [hEq]
    calc
      _ ≤ 2^P.card*(acceptingTables f).card := card_accepting_pin_le f a P
      _ ≤ 2^P.card*2^descriptionBitBound m := Nat.mul_le_mul_left _ (GrowingAndOrbit.control_sparse r hr)
      _ = _ := by rw [Nat.mul_comm,← pow_add]
  have hRank := pinRank_lower c.program pin a (c.outputs 0) (descriptionBitBound m+P.card) hYes hSparse
  have hDim : N-(descriptionBitBound m+P.card+1) ≤ pinRank c.program pin a := by
    change N ≤ _ at hRank
    omega
  obtain ⟨pick,hPick,hLI⟩ := pin_independent_active c.program pin a
  let emb : Fin (N-(descriptionBitBound m+P.card+1)) ↪ Fin (pinRank c.program pin a) :=
    ⟨Fin.castLE hDim,Fin.castLE_injective hDim⟩
  exact ⟨emb.trans pick,fun i => hPick (emb i),hLI.comp emb emb.injective⟩

/-- In the earlier minimum alias control the first exit actually has zero
quotient trace after the forcing pin. -/
theorem alias_exit_zero_rank (a : BitString 4) :
    pinQuotientTrace SecondBlockExits.aliasProgram
      (pinAt (fun _ => true) SecondBlockExits.aliasPins) a 1 = 0 := by
  let pin := pinAt (fun _ => true) SecondBlockExits.aliasPins
  let p := SecondBlockExits.aliasProgram
  let base := substitute pin a
  let T (z : Fin 4 → F₂) := substitute pin (perturb a z)
  have he : centered p base T (.gate 1) = raw base T 2 := by
    funext z
    change bit (restrictedWire p pin (.gate 1) a ^^ restrictedWire p pin (.gate 1) (perturb a z)) =
      bit (substitute pin a 2 ^^ substitute pin (perturb a z) 2)
    rw [SecondBlockExits.alias_control_has_one_when_true.2]
    simp [substitute,pin,pinAt,SecondBlockExits.aliasPins,FreshCharges.projection]
  unfold pinQuotientTrace
  change (rawSpan base T).mkQ (centered p base T (.gate 1)) = 0
  rw [he]
  apply LinearMap.mem_ker.mp
  rw [Submodule.ker_mkQ]
  exact Submodule.subset_span ⟨2,rfl⟩

end Applications

#print axioms pinRank_lower
#print axioms pinRank_with_reader_losses
#print axioms independent_lifts_from_slice
#print axioms mcsp32_joint_independent
#print axioms signedAnd_independent_under_allOne_pins
#print axioms alias_exit_zero_rank

end PvsNP.Frontier.ResidualTraceRank
