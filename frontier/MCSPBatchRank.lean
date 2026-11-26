module

public import MCSPJointSparseCompletion
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod

/-! One centered trace vector for each original gate across the entire batch.
AND and OR contribute one product of two centered traces. -/

@[expose] public section

namespace PvsNP.Frontier.BatchRank

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open RestrictionCharges
open scoped Classical BigOperators

abbrev F₂ := ZMod 2

def bit (b : Bool) : F₂ := if b then 1 else 0

noncomputable def binaryGates {n g : ℕ} (p : Program signature n g) : Finset (Fin g) :=
  Finset.univ.filter fun j => (p.lines j).op = .and ∨ (p.lines j).op = .or

def centered {I : Type*} {n g : ℕ} (p : Program signature n g)
    (base : BitString n) (T : I → BitString n) (w : Wire n g) : I → F₂ :=
  fun i => bit ((p.trace interpretation base w) ^^ (p.trace interpretation (T i) w))

def raw {I : Type*} {n : ℕ} (base : BitString n) (T : I → BitString n) (j : Fin n) : I → F₂ :=
  fun i => bit (base j ^^ T i j)

def gateProduct {I : Type*} (op : Op) (D : Fin (signature.Arity op) → I → F₂) : I → F₂ :=
  match op with
  | .const _ | .not => 0
  | .and | .or => D 0 * D 1

def interaction {I : Type*} {n g : ℕ} (p : Program signature n g)
    (base : BitString n) (T : I → BitString n) (j : Fin g) : I → F₂ :=
  gateProduct (p.lines j).op (fun b => centered p base T ((p.lines j).wires b))

theorem gateProduct_eq_zero {I : Type*} (op : Op)
    (h : ¬(op = .and ∨ op = .or)) (D : Fin (signature.Arity op) → I → F₂) :
    gateProduct op D = 0 := by
  cases op with
  | const b => rfl
  | not => rfl
  | and => exact (h (Or.inl rfl)).elim
  | or => exact (h (Or.inr rfl)).elim

private theorem dAND (a b x y : Bool) :
    bit ((a && b) ^^ (x && y)) =
      bit b * bit (a ^^ x) + bit a * bit (b ^^ y) + bit (a ^^ x)*bit (b ^^ y) := by
  cases a <;> cases b <;> cases x <;> cases y <;> decide

private theorem dOR (a b x y : Bool) :
    bit ((a || b) ^^ (x || y)) =
      bit (!b) * bit (a ^^ x) + bit (!a) * bit (b ^^ y) + bit (a ^^ x)*bit (b ^^ y) := by
  cases a <;> cases b <;> cases x <;> cases y <;> decide

private theorem dNOT (a b : Bool) : bit ((!a) ^^ (!b)) = bit (a ^^ b) := by
  cases a <;> cases b <;> decide

theorem gate_centered_mem {I : Type*} (S : Submodule F₂ (I → F₂))
    (op : Op) (base : Fin (signature.Arity op) → Bool)
    (T : I → Fin (signature.Arity op) → Bool)
    (hW : ∀ j, (fun i => bit (base j ^^ T i j)) ∈ S)
    (hProduct : gateProduct op (fun j i => bit (base j ^^ T i j)) ∈ S) :
    (fun i => bit (interpretation op base ^^ interpretation op (T i))) ∈ S := by
  cases op with
  | const b =>
    have he : (fun i => bit (interpretation (.const b) base ^^ interpretation (.const b) (T i))) =
        (0 : I → F₂) := by funext i; simp [interpretation, bit]
    rw [he]
    exact S.zero_mem
  | not =>
    have he : (fun i => bit (interpretation .not base ^^ interpretation .not (T i))) =
        fun i => bit (base 0 ^^ T i 0) := funext fun _ => dNOT _ _
    rw [he]
    exact hW 0
  | and =>
    have he : (fun i => bit (interpretation .and base ^^ interpretation .and (T i))) =
        bit (base 1) • (fun i => bit (base 0 ^^ T i 0)) +
        bit (base 0) • (fun i => bit (base 1 ^^ T i 1)) +
        gateProduct .and (fun j i => bit (base j ^^ T i j)) :=
      funext fun _ => dAND _ _ _ _
    rw [he]
    exact S.add_mem (S.add_mem (S.smul_mem _ (hW 0)) (S.smul_mem _ (hW 1))) hProduct
  | or =>
    have he : (fun i => bit (interpretation .or base ^^ interpretation .or (T i))) =
        bit (!(base 1)) • (fun i => bit (base 0 ^^ T i 0)) +
        bit (!(base 0)) • (fun i => bit (base 1 ^^ T i 1)) +
        gateProduct .or (fun j i => bit (base j ^^ T i j)) :=
      funext fun _ => dOR _ _ _ _
    rw [he]
    exact S.add_mem (S.add_mem (S.smul_mem _ (hW 0)) (S.smul_mem _ (hW 1))) hProduct

/-- In any common trace space across the entire batch, raw inputs and one
product vector for each binary gate generate all centered wire traces. -/
theorem centered_mem_of_generators {I : Type*} {n g : ℕ}
    (S : Submodule F₂ (I → F₂)) (p : Program signature n g)
    (base : BitString n) (T : I → BitString n)
    (hRaw : ∀ j, raw base T j ∈ S)
    (hProd : ∀ j ∈ binaryGates p, interaction p base T j ∈ S) (w : Wire n g) :
    centered p base T w ∈ S := by
  refine p.wire_induction (P := fun w => centered p base T w ∈ S) hRaw ?_ w
  intro j ih
  have hP : interaction p base T j ∈ S := by
    by_cases hj : j ∈ binaryGates p
    · exact hProd j hj
    · have h : ¬((p.lines j).op = .and ∨ (p.lines j).op = .or) :=
        fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      unfold interaction
      rw [gateProduct_eq_zero _ h]
      exact S.zero_mem
  unfold centered
  simp only [p.trace_gate]
  exact gate_centered_mem S _ _ _ ih hP

/-- The dimension after quotienting out the raw-input traces charges each
original AND or OR at most once, with the same coefficient across the batch. -/
theorem quotient_trace_rank_le_binary {I : Type*} [Fintype I] {n g : ℕ}
    (p : Program signature n g) (base : BitString n) (T : I → BitString n) :
    let U := Submodule.span F₂ (Set.range (raw base T))
    (Set.range (fun w => U.mkQ (centered p base T w))).finrank F₂ ≤ (binaryGates p).card := by
  let U := Submodule.span F₂ (Set.range (raw base T))
  let gen (j : binaryGates p) := U.mkQ (interaction p base T j.val)
  let V := Submodule.span F₂ (Set.range gen)
  have hLocal (w : Wire n g) : U.mkQ (centered p base T w) ∈ V := by
    apply centered_mem_of_generators (V.comap U.mkQ) p base T ?_ ?_ w
    · intro i
      change U.mkQ (raw base T i) ∈ V
      have ha : raw base T i ∈ U := Submodule.subset_span ⟨i,rfl⟩
      have hk : raw base T i ∈ LinearMap.ker U.mkQ := by
        rwa [Submodule.ker_mkQ]
      have hz : U.mkQ (raw base T i) = 0 := LinearMap.mem_ker.mp hk
      rw [hz]
      exact V.zero_mem
    · intro j hj
      exact Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩
  have hSub : Submodule.span F₂ (Set.range (fun w => U.mkQ (centered p base T w))) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact hLocal w
  exact (Submodule.finrank_mono hSub).trans
    ((finrank_range_le_card gen).trans_eq (Fintype.card_coe _))

/-- In particular, a batch may use unrelated restrictions and residual
assignments. They still share the same rank budget. -/
theorem restriction_trace_rank_le_binary {A I : Type*} [Fintype A] [Fintype I] {n k g : ℕ}
    (p : Program signature n g) (base : BitString n)
    (pin : A → Fin n → Fin k ⊕ Bool) (sample : A → I → BitString k) :
    let T (q : A × I) := substitute (pin q.1) (sample q.1 q.2)
    let U := Submodule.span F₂ (Set.range (raw base T))
    (Set.range (fun w => U.mkQ (centered p base T w))).finrank F₂ ≤ (binaryGates p).card :=
  quotient_trace_rank_le_binary p base _

section MatrixBudget

abbrev asMatrix {A B : Type*} (f : A × B → F₂) : Matrix A B F₂ :=
  fun a b => f (a,b)

private def columnMap {A B : Type*} (b : B) : (A × B → F₂) →ₗ[F₂] (A → F₂) where
  toFun f := fun a => f (a,b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem finrank_sup_finset_le {A J : Type*} [Fintype A] (E : Finset J)
    (f : J → Submodule F₂ (A → F₂)) : Module.finrank F₂ ↥(E.sup f) ≤
      ∑ j ∈ E, Module.finrank F₂ (f j) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    change Module.finrank F₂ ↥(⊥ : Submodule F₂ (A → F₂)) ≤ 0
    exact (finrank_bot F₂ (A → F₂)).le
  | @insert j E hj ih =>
    rw [Finset.sup_insert, Finset.sum_insert hj]
    have h := Submodule.finrank_add_le_finrank_add_finrank (K := F₂) (V := A → F₂) (f j) (E.sup f)
    omega

/-- A weighted charge on original binary gates. Each contributes the
matrix rank of its interaction, once for the whole batch. -/
theorem matrix_rank_le_interaction_budget {A B : Type*} [Fintype A] [Fintype B] {n g : ℕ}
    (p : Program signature n g) (base : BitString n) (T : A × B → BitString n) (w : Wire n g) :
    (asMatrix (centered p base T w)).rank ≤
      (∑ i : Fin n, (asMatrix (raw base T i)).rank) +
        ∑ j : binaryGates p, (asMatrix (interaction p base T j.val)).rank := by
  let gvec : Fin n ⊕ binaryGates p → (A × B → F₂) :=
    Sum.elim (raw base T) (fun j => interaction p base T j.val)
  let columns (j : Fin n ⊕ binaryGates p) : Submodule F₂ (A → F₂) :=
    Submodule.span F₂ (Set.range (asMatrix (gvec j)).col)
  let V := (Finset.univ : Finset (Fin n ⊕ binaryGates p)).sup columns
  let S := ⨅ b : B, V.comap (columnMap b)
  have hGen (j : Fin n ⊕ binaryGates p) : gvec j ∈ S := by
    apply (Submodule.mem_iInf _).mpr
    intro b
    exact (Finset.le_sup (s := (Finset.univ : Finset (Fin n ⊕ binaryGates p)))
      (f := columns) (Finset.mem_univ j)) (Submodule.subset_span ⟨b,rfl⟩)
  have hw : centered p base T w ∈ S := centered_mem_of_generators S p base T
    (fun i => hGen (.inl i)) (fun j hj => hGen (.inr ⟨j,hj⟩)) w
  have hSub : Submodule.span F₂ (Set.range (asMatrix (centered p base T w)).col) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b,rfl⟩
    exact (Submodule.mem_iInf _).mp hw b
  rw [Matrix.rank_eq_finrank_span_cols]
  apply (Submodule.finrank_mono hSub).trans
  have hV := finrank_sup_finset_le (Finset.univ : Finset (Fin n ⊕ binaryGates p)) columns
  simpa only [columns, ← Matrix.rank_eq_finrank_span_cols, Fintype.sum_sum_type, gvec,
    Sum.elim_inl, Sum.elim_inr] using hV

private theorem rank_left_only {A B : Type*} [Fintype A] [Fintype B] (f : A → F₂) :
    (asMatrix (fun q : A×B => f q.1)).rank ≤ 1 := by
  let U : Matrix A (Fin 1) F₂ := fun a _ => f a
  let V : Matrix (Fin 1) B F₂ := fun _ _ => 1
  have h : asMatrix (fun q : A×B => f q.1) = U*V := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    change f a = f a * 1
    simp
  rw [h]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using U.rank_le_card_width)

private theorem rank_right_only {A B : Type*} [Fintype A] [Fintype B] (f : B → F₂) :
    (asMatrix (fun q : A×B => f q.2)).rank ≤ 1 := by
  let U : Matrix A (Fin 1) F₂ := fun _ _ => 1
  let V : Matrix (Fin 1) B F₂ := fun _ b => f b
  have h : asMatrix (fun q : A×B => f q.2) = U*V := by
    ext a b
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    change f b = 1 * f b
    simp
  rw [h]
  exact (Matrix.rank_mul_le_left U V).trans (by simpa using U.rank_le_card_width)

set_option maxHeartbeats 300000 in
/-- When each raw coordinate comes from one side of the cut, its whole
centered matrix has rank at most one. -/
theorem matrix_rank_le_of_separable_raw {A B : Type*} [Fintype A] [Fintype B] {n g : ℕ}
    (p : Program signature n g) (base : BitString n) (T : A × B → BitString n) (w : Wire n g)
    (hSplit : ∀ i : Fin n, (∃ f : A → Bool, ∀ a b, T (a,b) i = f a) ∨
      (∃ f : B → Bool, ∀ a b, T (a,b) i = f b)) :
    (asMatrix (centered p base T w)).rank ≤ n+
        ∑ j : binaryGates p, (asMatrix (interaction p base T j.val)).rank := by
  apply (matrix_rank_le_interaction_budget p base T w).trans
  apply Nat.add_le_add_right
  have hR (i : Fin n) : (asMatrix (raw base T i)).rank ≤ 1 := by
    rcases hSplit i with ⟨f,hf⟩ | ⟨f,hf⟩
    · have he : raw base T i = fun q => bit (base i ^^ f q.1) :=
        funext fun ⟨a,b⟩ => congrArg (fun x => bit (base i ^^ x)) (hf a b)
      exact (congrArg (fun z : A × B → F₂ => (asMatrix z).rank) he).le.trans
        (rank_left_only (A := A) (B := B) (fun a => bit (base i ^^ f a)))
    · have he : raw base T i = fun q => bit (base i ^^ f q.2) :=
        funext fun ⟨a,b⟩ => congrArg (fun x => bit (base i ^^ x)) (hf a b)
      exact (congrArg (fun z : A × B → F₂ => (asMatrix z).rank) he).le.trans
        (rank_right_only (A := A) (B := B) (fun b => bit (base i ^^ f b)))
  exact (Finset.sum_le_sum (fun i _ => hR i)).trans_eq (by simp)

end MatrixBudget

section SignedAnd

open JointEquality JointOrbit GrowingAndOrbit PatchedCut

variable {r s : ℕ}

/-- The test inputs after any common twist and error patch. Each entry still
comes from one of the two labels. -/
def spliceBatch (h : BooleanFunction s) (j : Fin (Arity r s))
    (P D : Finset (Fin (2^Arity r s))) (q : Labels r s × Labels r s) :
    BitString (2^Arity r s) :=
  patch D (patch P (rotated j (mixed h q.1 q.2)))

theorem spliceBatch_raw (h : BooleanFunction s) (j : Fin (Arity r s))
    (P D : Finset (Fin (2^Arity r s))) (i : Fin (2^Arity r s)) :
    (∃ f : Labels r s → Bool, ∀ u v, spliceBatch h j P D (u,v) i = f u) ∨
      (∃ f : Labels r s → Bool, ∀ u v, spliceBatch h j P D (u,v) i = f v) := by
  let t := PermutedCut.tablePerm (blockSwap j) i
  cases hs : selector (r := r) h t
  · right
    refine ⟨fun v => patch D (patch P (rotated j (diagonal v))) i,?_⟩
    intro u v
    simp only [spliceBatch,mixed_eq_splice,patch,rotated,Function.comp_apply]
    change ((CommunicationCut.splice (selector h) (diagonal u) (diagonal v) t ^^ _) ^^ _) =
      ((diagonal v t ^^ _) ^^ _)
    simp [CommunicationCut.splice,hs]
  · left
    refine ⟨fun u => patch D (patch P (rotated j (diagonal u))) i,?_⟩
    intro u v
    simp only [spliceBatch,mixed_eq_splice,patch,rotated,Function.comp_apply]
    change ((CommunicationCut.splice (selector h) (diagonal u) (diagonal v) t ^^ _) ^^ _) =
      ((diagonal u t ^^ _) ^^ _)
    simp [CommunicationCut.splice,hs]

def baselineLabels (r s : ℕ) : Labels r s × Labels r s :=
  (fun _ => (fun _ => false,false,fun _ => false),
   fun _ => (fun _ => false,true,fun _ => false))

private theorem baselineLabels_ne (r s : ℕ) : (baselineLabels r s).1 ≠ (baselineLabels r s).2 := by
  intro h
  exact Bool.false_ne_true (congrArg (fun (u : Labels r s) => (u false).2.1) h)

abbrev tableSize (r : ℕ) := 2^logArity r

theorem centered_matrix_eq_one_of_equality {A : Type*} [DecidableEq A] {n : ℕ}
    (T : A × A → BitString n) (f : BooleanFunction n)
    (hResult : ∀ u v, f (T (u,v)) = true ↔ u=v)
    {u₀ v₀ : A} (hne : u₀ ≠ v₀) (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f)) :
    asMatrix (centered c.program (T (u₀,v₀)) T (c.outputs 0)) = 1 := by
  have hTrace (q : A × A) :
      c.program.trace interpretation (T q) (c.outputs 0) = f (T q) :=
    congrFun (hc (T q)) 0
  have hBase : c.program.trace interpretation (T (u₀,v₀)) (c.outputs 0) = false := by
    rw [hTrace]
    exact Bool.eq_false_of_not_eq_true (fun hc =>
      hne ((hResult _ _).mp hc))
  ext u v
  change bit ((c.program.trace interpretation (T (u₀,v₀)) (c.outputs 0)) ^^
      (c.program.trace interpretation (T (u,v)) (c.outputs 0))) =
        (1 : Matrix A A F₂) u v
  rw [hBase, hTrace, Bool.false_xor, Matrix.one_apply]
  by_cases he : u = v
  · rw [(hResult u v).mpr he]
    simp [bit,he]
  · rw [Bool.eq_false_of_not_eq_true (fun h => he ((hResult u v).mp h))]
    simp [bit,he]

/-- The signed-AND control actually produces an identity communication
matrix on every enriched cut. This uses the original Boolean recognizer. -/
theorem signedAnd_centered_matrix (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) (radius r) h)
    (j : Fin (logArity r)) (P D : Finset (Fin (tableSize r)))
    {k : ℕ} (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
    (hP : P = LongAndOrbit.support e a) (hD : D.card ≤ 4)
    (c : Circuit signature (tableSize r) 1)
    (hc : c.Computes interpretation (single (GrowingAndOrbit.control r hr))) :
    asMatrix (centered c.program (spliceBatch h j P D (baselineLabels r (2^r)))
      (spliceBatch h j P D) (c.outputs 0)) = 1 := by
  subst P
  exact centered_matrix_eq_one_of_equality (spliceBatch h j (LongAndOrbit.support e a) D)
    (GrowingAndOrbit.control r hr) (fun u v => (growing_longAnd_tests r hr hh j u v e a D hD).2)
    (baselineLabels_ne r (2^r)) c hc

private theorem spliceBatch_interaction_budget {g : ℕ} (r : ℕ) (h : BooleanFunction (2^r))
    (j : Fin (logArity r)) (P D : Finset (Fin (tableSize r)))
    (p : Program signature (tableSize r) g) (w : Wire (tableSize r) g)
    (hm : asMatrix (centered p (spliceBatch h j P D (baselineLabels r (2^r)))
      (spliceBatch h j P D) w) = 1) :
    let T := spliceBatch h j P D
    let base := T (baselineLabels r (2^r))
    (tableSize r)^2 ≤ tableSize r + ∑ u : binaryGates p,
      (asMatrix (interaction p base T u.val)).rank := by
  let T := spliceBatch h j P D
  let base := T (baselineLabels r (2^r))
  have hb := matrix_rank_le_of_separable_raw p base T w
    (spliceBatch_raw h j P D)
  rw [hm,Matrix.rank_one,JointEquality.card_labels] at hb
  apply le_trans _ hb
  have hR : r < 2^r := Nat.lt_two_pow_self
  have hAr : 2*logArity r ≤ 2*(2^r+(2^r+1)) := by dsimp [logArity,Arity]; omega
  calc
    _ = 2^(2*logArity r) := by rw [Nat.mul_comm 2 (logArity r),pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hAr

theorem signedAnd_interaction_budget (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) (radius r) h)
    (j : Fin (logArity r)) {k : ℕ}
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
    (D : Finset (Fin (tableSize r))) (hD : D.card ≤ 4)
    (c : Circuit signature (tableSize r) 1)
    (hc : c.Computes interpretation (single (GrowingAndOrbit.control r hr))) :
    let T := spliceBatch h j (LongAndOrbit.support e a) D
    let base := T (baselineLabels r (2^r))
    (tableSize r)^2 ≤ tableSize r + ∑ u : binaryGates c.program,
      (asMatrix (interaction c.program base T u.val)).rank := by
  exact spliceBatch_interaction_budget r h j (LongAndOrbit.support e a) D c.program (c.outputs 0)
    (signedAnd_centered_matrix r hr hh j _ D e a rfl hD c hc)

/-- Exact MCSP has the same weighted rank lower bound on the enriched family. -/
theorem exact_mcsp_interaction_budget (r : ℕ) (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
    (hh : TestsAt (r := r) (radius r) h) (j : Fin (logArity r)) {k : ℕ}
    (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
    (D : Finset (Fin (tableSize r))) (hD : D.card ≤ 4)
    (c : Circuit signature (tableSize r) 1)
    (hc : c.Computes interpretation (single (mcspSquare (logArity r)))) :
    let T := spliceBatch h j (LongAndOrbit.support e a) D
    let base := T (baselineLabels r (2^r))
    (tableSize r)^2 ≤ tableSize r + ∑ u : binaryGates c.program,
      (asMatrix (interaction c.program base T u.val)).rank := by
  let P := LongAndOrbit.support e a
  have hm := centered_matrix_eq_one_of_equality (spliceBatch h j P D)
    (mcspSquare (logArity r))
    (fun u v => (growing_longAnd_tests r hr hh j u v e a D hD).1) (baselineLabels_ne r (2^r)) c hc
  exact spliceBatch_interaction_budget r h j P D c.program (c.outputs 0) hm

/-- Hence even minimum signed-AND circuits have some interaction whose
rank is above any fixed per-original-gate charge cap, on large stages. -/
theorem signedAnd_unbounded_gate_rank (K : ℕ) :
    ∀ᶠ r in Filter.atTop, ∀ (hr : 10 ≤ r) {h : BooleanFunction (2^r)}
      (_ : TestsAt (r := r) (radius r) h) (j : Fin (logArity r)) {k : ℕ}
      (e : Fin k ⊕ Fin (r-1) ≃ Fin (logArity r)) (a : BitString k)
      (D : Finset (Fin (tableSize r))) (_ : D.card ≤ 4)
      (c : Circuit signature (tableSize r) 1)
      (_ : c.Computes interpretation (single (GrowingAndOrbit.control r hr)))
      (_ : c.size = complexity interpretation (single (GrowingAndOrbit.control r hr))),
      let T := spliceBatch h j (LongAndOrbit.support e a) D
      let base := T (baselineLabels r (2^r))
      ∃ u ∈ binaryGates c.program, K < (asMatrix (interaction c.program base T u)).rank := by
  have hf := Nat.eventually_mul_add_one_pow_le_pow_div (5100*K+2) 1 1
    (by decide : 1 < (2 : ℕ)) (by decide)
  filter_upwards [hf] with r he hr h hh j k e a D hD c hc hMin
  let T := spliceBatch h j (LongAndOrbit.support e a) D
  let base := T (baselineLabels r (2^r))
  let n := tableSize r
  change ∃ u ∈ binaryGates c.program, K < (asMatrix (interaction c.program base T u)).rank
  by_contra! hSmall
  have hLower : n^2 ≤ n+∑ u : binaryGates c.program,
      (asMatrix (interaction c.program base T u.val)).rank :=
    signedAnd_interaction_budget r hr hh j e a D hD c hc
  have hCap : (∑ u : binaryGates c.program, (asMatrix (interaction c.program base T u.val)).rank)
      ≤ K*c.size := calc
    _ ≤ ∑ _u : binaryGates c.program, K := Finset.sum_le_sum (fun u _ => hSmall u.val u.property)
    _ = K*(binaryGates c.program).card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (by
      have hb := Finset.card_le_univ (binaryGates c.program)
      simpa using hb)
  have hSize : c.size ≤ 5100*(r+1)*n := hMin ▸ GrowingAndOrbit.control_size r hr
  have hN : (5100*K+2)*(r+1) ≤ n := by
    have hPoly : (5100*K+2)*(r+1) ≤ 2^r := by simpa using he
    exact hPoly.trans (Nat.pow_le_pow_right (by decide) (by dsimp [logArity,Arity]; omega))
  have hStrict : 1+K*(5100*(r+1)) < n := by
    have hx : (5100*K+2)*(r+1) = K*(5100*(r+1))+2*(r+1) := by ring
    omega
  have hn : 0 < n := Nat.two_pow_pos _
  have hFalse : n+K*c.size < n^2 := calc
    _ ≤ n+K*(5100*(r+1)*n) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hSize) _
    _ = (1+K*(5100*(r+1)))*n := by ring
    _ < n*n := Nat.mul_lt_mul_of_pos_right hStrict hn
    _ = _ := (pow_two _).symm
  exact (not_le_of_gt hFalse) (hLower.trans (Nat.add_le_add_left hCap _))

end SignedAnd

#print axioms restriction_trace_rank_le_binary
#print axioms matrix_rank_le_interaction_budget
#print axioms signedAnd_centered_matrix
#print axioms signedAnd_interaction_budget
#print axioms exact_mcsp_interaction_budget
#print axioms signedAnd_unbounded_gate_rank

end PvsNP.Frontier.BatchRank
