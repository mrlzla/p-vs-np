module

public import MCSPQuadraticForest
public import MCSPPairFunnelGap
public import MCSPCommunicationCut
public import Complexity.Computability.Circuit.Boolean.Formula.Restriction

/-! The bounded-degree `𝔽₂`-polynomial (Reed–Muller) barrier for `mcspSquare m`.

This module proves unconditionally that the exact `𝔽₂`-degree-`≤ d` decider `isDeg d m`:
1. Is algebraically closed under XOR, complement, and degree addition under AND, accepting
   every affine function, rank-1 quadratic `quad`, and `≤ d`-degree polynomial (`isDegFn_two_quad`);
2. Is invariant under all invertible `AGL(m, 𝔽₂)` affine transformations of the represented
   inputs as well as De Morgan truth-table duality (`isDegFn_comp_affine`, `isDeg_agl_invariant`,
   `isDeg_perm`, `isDeg_dualTable`);
3. Has exact accepting-table count `2 ^ rmDim d m`, and at degree `d = 2` satisfies the exact
   `mcspSquare m` sparsity bound `(acceptingTables (isDeg 2 m)).card ≤ 2 ^ descriptionBitBound m`
   (`rmDim_two_le_descriptionBitBound`, `card_accepting_isDeg2_le_mcspBound`);
4. Yet admits explicit linear-size De Morgan circuits (`complexity ≤ (4 * d + 2) * 2^m + d * (m + 1)^d`,
   hence `≤ 10 * N + m^2` at `d = 2`) and explicit linear-size De Morgan formulas (`formulaSize ≤
   2 * 4^d * 2^m`, hence `≤ 32 * N` at `d = 2`).

Applying `quad_reindexed_forest_size` from `MCSPQuadraticForest` pins `isDeg 2 32` inside the
verified two-sided bracket `[8,620,611,839, 42,949,673,984]`, showing formally that no lower-bound
proof relying solely on sparsity, `AGL(m, 𝔽₂)` / De Morgan symmetry, and bounded-degree polynomial
probes can separate `mcspSquare m` from `O(N)` circuits. We also verify explicit separation
witnesses (`pointFn`, `monomial3`, and 9-bit prefix `CommunicationCut.probe`) that `mcspSquare m`
accepts and `isDeg 2 m` rejects. -/

@[expose] public section

namespace PvsNP.Frontier.PolynomialBarrier

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open CornerCertificates SuperTwoN QuadraticForest PairFunnelGap CommunicationCut
open scoped Classical

/-! ### Part 1: Recursive `𝔽₂`-degree-`≤ d` test and algebraic closure -/

/-- Recursive `𝔽₂`-algebraic-degree-`≤ d` test for a Boolean function `f : BitString m → Bool`:
- degree `≤ 0` means constant (`∀ z, f z = f (zeroVec m)`),
- on `0` variables every function has degree `≤ d + 1`,
- on `m + 1` variables, `deg(f) ≤ d + 1` iff `deg(f|_{x₀=0}) ≤ d + 1` and
  `deg(f|_{x₀=0} ⊕ f|_{x₀=1}) ≤ d`. -/
def isDegFn : (d m : ℕ) → BooleanFunction m → Bool
  | 0, m, f => decide (∀ z : BitString m, f z = f (zeroVec m))
  | _ + 1, 0, _ => true
  | d + 1, m + 1, f =>
      isDegFn (d + 1) m (fun y => f (Fin.cons false y)) &&
      isDegFn d m (fun y => f (Fin.cons false y) ^^ f (Fin.cons true y))

/-- Truth-table formulation of the `𝔽₂`-degree-`≤ d` test on `N = 2 ^ m`-bit strings. -/
def isDeg (d m : ℕ) : BooleanFunction (2 ^ m) :=
  fun T => isDegFn d m ((MCSP.truthTable m).symm T)

@[simp] theorem isDeg_truthTable (d m : ℕ) (f : BooleanFunction m) :
    isDeg d m (MCSP.truthTable m f) = isDegFn d m f := by
  simp [isDeg]

theorem isDegFn_zero_iff {m : ℕ} {f : BooleanFunction m} :
    isDegFn 0 m f = true ↔ ∀ z : BitString m, f z = f (zeroVec m) := by
  simp [isDegFn]

theorem isDegFn_const (d m : ℕ) (c : Bool) :
    isDegFn d m (fun _ => c) = true := by
  induction m generalizing d c with
  | zero =>
    cases d with
    | zero => simp [isDegFn]
    | succ d => rfl
  | succ m ih =>
    cases d with
    | zero => simp [isDegFn]
    | succ d =>
      have hL := ih (d + 1) c
      have hR := ih d false
      simpa only [isDegFn, Bool.and_eq_true, Bool.xor_self] using ⟨hL, hR⟩

theorem isDegFn_mono {d₁ d₂ m : ℕ} (hd : d₁ ≤ d₂) {f : BooleanFunction m}
    (hf : isDegFn d₁ m f = true) : isDegFn d₂ m f = true := by
  induction m generalizing d₁ d₂ with
  | zero =>
    cases d₂ with
    | zero =>
      have : d₁ = 0 := by omega
      subst this
      exact hf
    | succ d₂ => rfl
  | succ m ih =>
    cases d₁ with
    | zero =>
      have hConst : ∀ z, f z = f (zeroVec (m + 1)) := isDegFn_zero_iff.mp hf
      cases d₂ with
      | zero => exact hf
      | succ d₂ =>
        change isDegFn (d₂ + 1) m (fun y => f (Fin.cons false y)) &&
            isDegFn d₂ m (fun y => f (Fin.cons false y) ^^ f (Fin.cons true y)) = true
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · have h0 : (fun y : BitString m => f (Fin.cons false y)) =
              fun _ => f (zeroVec (m + 1)) := funext fun y => hConst _
          rw [h0]
          exact isDegFn_const (d₂ + 1) m _
        · have h1 : (fun y : BitString m => f (Fin.cons false y) ^^ f (Fin.cons true y)) =
              fun _ => false := funext fun y => by
            rw [hConst (Fin.cons false y), hConst (Fin.cons true y), Bool.xor_self]
          rw [h1]
          exact isDegFn_const d₂ m false
    | succ a =>
      cases d₂ with
      | zero => omega
      | succ b =>
        change isDegFn (a + 1) m _ && isDegFn a m _ = true at hf
        change isDegFn (b + 1) m _ && isDegFn b m _ = true
        rw [Bool.and_eq_true] at hf ⊢
        exact ⟨ih (by omega) hf.1, ih (by omega) hf.2⟩

theorem isDegFn_xor {d m : ℕ} {f g : BooleanFunction m}
    (hf : isDegFn d m f = true) (hg : isDegFn d m g = true) :
    isDegFn d m (fun z => f z ^^ g z) = true := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero =>
      rw [isDegFn_zero_iff] at hf hg ⊢
      intro z
      rw [hf z, hg z]
    | succ d => rfl
  | succ m ih =>
    cases d with
    | zero =>
      rw [isDegFn_zero_iff] at hf hg ⊢
      intro z
      rw [hf z, hg z]
    | succ d =>
      change isDegFn (d + 1) m _ && isDegFn d m _ = true at hf hg
      change isDegFn (d + 1) m _ && isDegFn d m _ = true
      rw [Bool.and_eq_true] at hf hg ⊢
      refine ⟨ih hf.1 hg.1, ?_⟩
      have hEq :
          (fun y => (f (Fin.cons false y) ^^ g (Fin.cons false y)) ^^
            (f (Fin.cons true y) ^^ g (Fin.cons true y))) =
          (fun y => (f (Fin.cons false y) ^^ f (Fin.cons true y)) ^^
            (g (Fin.cons false y) ^^ g (Fin.cons true y))) := by
        funext y
        cases f (Fin.cons false y) <;> cases g (Fin.cons false y) <;>
          cases f (Fin.cons true y) <;> cases g (Fin.cons true y) <;> rfl
      rw [hEq]
      exact ih hf.2 hg.2

theorem isDegFn_not (d m : ℕ) (f : BooleanFunction m) :
    isDegFn d m (fun z => !(f z)) = isDegFn d m f := by
  have hInv (g : BooleanFunction m) : isDegFn d m g = true →
      isDegFn d m (fun z => !(g z)) = true := fun hg => by
    have hEq : (fun z => !(g z)) = fun z => g z ^^ true := by
      funext z; cases g z <;> rfl
    rw [hEq]
    exact isDegFn_xor hg (isDegFn_const d m true)
  apply Bool.eq_iff_iff.mpr
  refine ⟨fun h => ?_, hInv f⟩
  have hEq : f = fun z => !(!(f z)) := by funext z; simp
  rw [hEq]
  exact hInv (fun z => !(f z)) h

private theorem bool_and_deriv_split (f0 f1 g0 g1 : Bool) :
    ((f0 && g0) ^^ (f1 && g1)) =
      (((f0 && (g0 ^^ g1)) ^^ ((f0 ^^ f1) && g0)) ^^ ((f0 ^^ f1) && (g0 ^^ g1))) := by
  cases f0 <;> cases f1 <;> cases g0 <;> cases g1 <;> decide

theorem isDegFn_and {d₁ d₂ m : ℕ} {f g : BooleanFunction m}
    (hf : isDegFn d₁ m f = true) (hg : isDegFn d₂ m g = true) :
    isDegFn (d₁ + d₂) m (fun z => f z && g z) = true := by
  induction m generalizing d₁ d₂ with
  | zero =>
    cases hSum : d₁ + d₂ with
    | zero =>
      rw [isDegFn_zero_iff]
      intro z
      rw [Subsingleton.elim z (zeroVec 0)]
    | succ k => rfl
  | succ m ih =>
    cases d₁ with
    | zero =>
      have hfConst := isDegFn_zero_iff.mp hf
      rw [Nat.zero_add]
      cases hc : f (zeroVec (m + 1)) with
      | false =>
        have hEq : (fun z => f z && g z) = fun _ => false := funext fun z => by
          rw [hfConst z, hc]; rfl
        rw [hEq]
        exact isDegFn_const d₂ (m + 1) false
      | true =>
        have hEq : (fun z => f z && g z) = g := funext fun z => by
          rw [hfConst z, hc]; rfl
        rw [hEq]
        exact hg
    | succ a =>
      cases d₂ with
      | zero =>
        have hgConst := isDegFn_zero_iff.mp hg
        rw [Nat.add_zero]
        cases hc : g (zeroVec (m + 1)) with
        | false =>
          have hEq : (fun z => f z && g z) = fun _ => false := funext fun z => by
            rw [hgConst z, hc]; exact Bool.and_false _
          rw [hEq]
          exact isDegFn_const (a + 1) (m + 1) false
        | true =>
          have hEq : (fun z => f z && g z) = f := funext fun z => by
            rw [hgConst z, hc]; exact Bool.and_true _
          rw [hEq]
          exact hf
      | succ b =>
        change isDegFn (a + 1) m _ && isDegFn a m _ = true at hf
        change isDegFn (b + 1) m _ && isDegFn b m _ = true at hg
        rw [Bool.and_eq_true] at hf hg
        rw [show (a + 1) + (b + 1) = (a + b + 1) + 1 by omega]
        change isDegFn ((a + b + 1) + 1) m _ && isDegFn (a + b + 1) m _ = true
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · have h0 := ih (d₁ := a + 1) (d₂ := b + 1) hf.1 hg.1
          rwa [show a + 1 + (b + 1) = a + b + 1 + 1 by omega] at h0
        · have hDeriv :
              (fun y => (f (Fin.cons false y) && g (Fin.cons false y)) ^^
                (f (Fin.cons true y) && g (Fin.cons true y))) =
              (fun y => ((f (Fin.cons false y) && (g (Fin.cons false y) ^^ g (Fin.cons true y))) ^^
                ((f (Fin.cons false y) ^^ f (Fin.cons true y)) && g (Fin.cons false y))) ^^
                ((f (Fin.cons false y) ^^ f (Fin.cons true y)) &&
                  (g (Fin.cons false y) ^^ g (Fin.cons true y)))) :=
            funext fun y => bool_and_deriv_split _ _ _ _
          rw [hDeriv]
          have hT1 := ih (d₁ := a + 1) (d₂ := b) hf.1 hg.2
          rw [show a + 1 + b = a + b + 1 by omega] at hT1
          have hT2 := ih (d₁ := a) (d₂ := b + 1) hf.2 hg.1
          have hT3 := isDegFn_mono (by omega : a + b ≤ a + b + 1)
            (ih (d₁ := a) (d₂ := b) hf.2 hg.2)
          exact isDegFn_xor (isDegFn_xor hT1 hT2) hT3

theorem isDegFn_one_coord (m : ℕ) (i : Fin m) :
    isDegFn 1 m (fun z => z i) = true := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    cases i using Fin.cases with
    | zero =>
      have h0 : (fun y : BitString m => (Fin.cons false y : BitString (m + 1)) 0) = fun _ => false :=
        funext fun _ => rfl
      have h1 : (fun y : BitString m =>
          (Fin.cons false y : BitString (m + 1)) 0 ^^ (Fin.cons true y : BitString (m + 1)) 0) =
          fun _ => true := funext fun _ => rfl
      change isDegFn 1 m _ && isDegFn 0 m _ = true
      rw [h0, h1, isDegFn_const 1 m false, isDegFn_const 0 m true]
      rfl
    | succ j =>
      have h0 : (fun y : BitString m => (Fin.cons false y : BitString (m + 1)) j.succ) =
          fun y => y j := funext fun _ => rfl
      have h1 : (fun y : BitString m =>
          (Fin.cons false y : BitString (m + 1)) j.succ ^^
          (Fin.cons true y : BitString (m + 1)) j.succ) = fun _ => false := funext fun y =>
        Bool.xor_self (y j)
      change isDegFn 1 m _ && isDegFn 0 m _ = true
      rw [h0, h1, ih j, isDegFn_const 0 m false]
      rfl

theorem isDegFn_one_dot (m : ℕ) (a : BitString m) :
    isDegFn 1 m (dot a) = true := by
  induction m with
  | zero => exact isDegFn_const 1 0 false
  | succ m ih =>
    cases h0 : a 0 with
    | false =>
      have hEq : dot a = fun z : BitString (m + 1) => dot (Fin.tail a) (Fin.tail z) := funext fun z => by
        simp [dot, h0]
      rw [hEq]
      dsimp only [isDegFn]
      have h0' : (fun y : BitString m =>
          dot (Fin.tail a) (Fin.tail (Fin.cons false y : BitString (m + 1)))) =
          dot (Fin.tail a) := rfl
      have h1' : (fun y : BitString m =>
          dot (Fin.tail a) (Fin.tail (Fin.cons false y : BitString (m + 1))) ^^
          dot (Fin.tail a) (Fin.tail (Fin.cons true y : BitString (m + 1)))) =
          fun _ => false := funext fun y => Bool.xor_self (dot (Fin.tail a) y)
      rw [h0', h1', ih (Fin.tail a), isDegFn_const 0 m false]
      rfl
    | true =>
      have hEq : dot a = fun z : BitString (m + 1) =>
          z 0 ^^ dot (Fin.tail a) (Fin.tail z) := funext fun z => by
        simp [dot, h0]
      rw [hEq]
      have hHead : isDegFn 1 (m + 1) (fun z : BitString (m + 1) => z 0) = true :=
        isDegFn_one_coord (m + 1) 0
      have hTail : isDegFn 1 (m + 1) (fun z : BitString (m + 1) => dot (Fin.tail a) (Fin.tail z)) =
          true := by
        dsimp only [isDegFn]
        have h0' : (fun y : BitString m =>
            dot (Fin.tail a) (Fin.tail (Fin.cons false y : BitString (m + 1)))) =
            dot (Fin.tail a) := rfl
        have h1' : (fun y : BitString m =>
            dot (Fin.tail a) (Fin.tail (Fin.cons false y : BitString (m + 1))) ^^
            dot (Fin.tail a) (Fin.tail (Fin.cons true y : BitString (m + 1)))) =
            fun _ => false := funext fun y => Bool.xor_self (dot (Fin.tail a) y)
        rw [h0', h1', ih (Fin.tail a), isDegFn_const 0 m false]
        rfl
      exact isDegFn_xor hHead hTail

theorem isDegFn_one_affine (m : ℕ) (a : BitString m) (b0 : Bool) :
    isDegFn 1 m (affine a b0) = true := by
  change isDegFn 1 m (fun z => b0 ^^ dot a z) = true
  exact isDegFn_xor (isDegFn_const 1 m b0) (isDegFn_one_dot m a)

theorem isDegFn_two_quad (m : ℕ) (a : BitString m) (b0 : Bool) (c d : BitString m) :
    isDegFn 2 m (quad a b0 c d) = true := by
  have hAff : isDegFn 2 m (affine a b0) = true :=
    isDegFn_mono (by omega : 1 ≤ 2) (isDegFn_one_affine m a b0)
  have hQuad : isDegFn 2 m (fun z => dot c z && dot d z) = true :=
    isDegFn_and (isDegFn_one_dot m c) (isDegFn_one_dot m d)
  exact isDegFn_xor hAff hQuad

theorem isDeg_two_accepts_quad (m : ℕ) (a : BitString m) (b0 : Bool) (c d : BitString m) :
    isDeg 2 m (MCSP.truthTable m (quad a b0 c d)) = true := by
  rw [isDeg_truthTable]
  exact isDegFn_two_quad m a b0 c d

/-! ### Part 2: `AGL(m, 𝔽₂)` affine-map invariance and De Morgan duality invariance -/

/-- A map `Φ : BitString m → BitString k` is affine over `𝔽₂` iff every output coordinate has
`𝔽₂`-degree `≤ 1`. -/
def IsAffineMap {m k : ℕ} (Φ : BitString m → BitString k) : Prop :=
  ∀ j : Fin k, isDegFn 1 m (fun z => Φ z j) = true

private theorem boolFn_succ_decomp {k : ℕ} (f : BooleanFunction (k + 1)) (w : BitString (k + 1)) :
    f w = (f (Fin.cons false (Fin.tail w)) ^^
      (w 0 && (f (Fin.cons false (Fin.tail w)) ^^ f (Fin.cons true (Fin.tail w))))) := by
  cases hw : w 0 with
  | false =>
    have hW : Fin.cons false (Fin.tail w) = w := by
      have : Fin.cons (w 0) (Fin.tail w) = w := Fin.cons_self_tail w
      simpa [hw] using this
    rw [hW]
    generalize f w = x
    generalize f (Fin.cons true (Fin.tail w)) = y
    cases x <;> cases y <;> decide
  | true =>
    have hW : Fin.cons true (Fin.tail w) = w := by
      have : Fin.cons (w 0) (Fin.tail w) = w := Fin.cons_self_tail w
      simpa [hw] using this
    rw [hW]
    generalize f (Fin.cons false (Fin.tail w)) = x
    generalize f w = y
    cases x <;> cases y <;> decide

/-- Composition with any `𝔽₂`-affine map preserves the degree bound `isDegFn d · = true`. -/
theorem isDegFn_comp_affine {d m k : ℕ} {f : BooleanFunction k} {Φ : BitString m → BitString k}
    (hf : isDegFn d k f = true) (hΦ : IsAffineMap Φ) :
    isDegFn d m (fun z => f (Φ z)) = true := by
  induction k generalizing d with
  | zero =>
    have hEq : (fun z => f (Φ z)) = fun _ => f (zeroVec 0) := funext fun z => by
      rw [Subsingleton.elim (Φ z) (zeroVec 0)]
    rw [hEq]
    exact isDegFn_const d m _
  | succ k ih =>
    cases d with
    | zero =>
      have hConst := isDegFn_zero_iff.mp hf
      have hEq : (fun z => f (Φ z)) = fun _ => f (zeroVec (k + 1)) := funext fun z => hConst (Φ z)
      rw [hEq]
      exact isDegFn_const 0 m _
    | succ d =>
      change isDegFn (d + 1) k _ && isDegFn d k _ = true at hf
      rw [Bool.and_eq_true] at hf
      let f0 : BooleanFunction k := fun y => f (Fin.cons false y)
      let df : BooleanFunction k := fun y => f (Fin.cons false y) ^^ f (Fin.cons true y)
      let Φ' : BitString m → BitString k := fun z => Fin.tail (Φ z)
      have hΦ' : IsAffineMap Φ' := fun j => by
        simpa [Φ', Fin.tail] using hΦ j.succ
      have hf0Comp : isDegFn (d + 1) m (fun z => f0 (Φ' z)) = true := ih hf.1 hΦ'
      have hdfComp : isDegFn d m (fun z => df (Φ' z)) = true := ih hf.2 hΦ'
      have h0Comp : isDegFn 1 m (fun z => Φ z 0) = true := hΦ 0
      have hProd : isDegFn (1 + d) m (fun z => Φ z 0 && df (Φ' z)) = true :=
        isDegFn_and h0Comp hdfComp
      have hProd' : isDegFn (d + 1) m (fun z => Φ z 0 && df (Φ' z)) = true := by
        simpa [Nat.add_comm] using hProd
      have hEq : (fun z => f (Φ z)) = fun z => f0 (Φ' z) ^^ (Φ z 0 && df (Φ' z)) := funext fun z =>
        boolFn_succ_decomp f (Φ z)
      rw [hEq]
      exact isDegFn_xor hf0Comp hProd'

/-- Every invertible `𝔽₂`-affine bijection preserves exact `isDegFn d m` membership. -/
theorem isDegFn_comp_affineEquiv {d m : ℕ} (f : BooleanFunction m)
    (e : BitString m ≃ BitString m) (he : IsAffineMap e) (hes : IsAffineMap e.symm) :
    isDegFn d m (fun z => f (e z)) = isDegFn d m f := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨fun h => ?_, fun h => isDegFn_comp_affine h he⟩
  have hEq : f = fun z => (fun w => f (e w)) (e.symm z) := funext fun z => by simp
  rw [hEq]
  exact isDegFn_comp_affine (f := fun w => f (e w)) h hes

private theorem basisVec_bitXor_tail : ∀ {m : ℕ} (z : BitString (m + 1)),
    z = bitXor (if z 0 then (fun j : Fin (m + 1) => decide (j = 0)) else zeroVec (m + 1))
      (Fin.cons false (Fin.tail z)) := by
  intro m z
  funext j
  cases j using Fin.cases with
  | zero =>
    cases z 0 <;> simp [bitXor, zeroVec]
  | succ j' =>
    cases hz : z 0
    · simp only [bitXor, Bool.false_eq_true, ↓reduceIte, zeroVec, Fin.cons_succ, Bool.false_xor]
      rfl
    · simp only [bitXor, ↓reduceIte, Fin.succ_ne_zero, decide_false, Fin.cons_succ, Bool.false_xor]
      rfl

private theorem linear_bool_eq_dot : ∀ {m : ℕ} (g : BitString m → Bool),
    (∀ x y, g (bitXor x y) = (g x ^^ g y)) →
    ∃ a : BitString m, ∀ z, g z = dot a z
  | 0, g, hg => ⟨zeroVec 0, fun z => by
      have h0 : g (zeroVec 0) = false := by
        have hxx := hg (zeroVec 0) (zeroVec 0)
        rw [bitXor_self] at hxx
        cases hv : g (zeroVec 0)
        · rfl
        · rw [hv] at hxx; exact absurd hxx (by decide)
      rw [Subsingleton.elim z (zeroVec 0), h0, dot_zero_right]⟩
  | m + 1, g, hg => by
    let gTail : BitString m → Bool := fun y => g (Fin.cons false y)
    have hgTail : ∀ u v, gTail (bitXor u v) = (gTail u ^^ gTail v) := fun u v => by
      dsimp only [gTail]
      have hCons : Fin.cons false (bitXor u v) = bitXor (Fin.cons false u) (Fin.cons false v) := by
        funext j
        cases j using Fin.cases with
        | zero => rfl
        | succ j' => rfl
      rw [hCons]
      exact hg _ _
    obtain ⟨aTail, haTail⟩ := linear_bool_eq_dot gTail hgTail
    let e0 : BitString (m + 1) := fun j => decide (j = 0)
    let a : BitString (m + 1) := Fin.cons (g e0) aTail
    refine ⟨a, fun z => ?_⟩
    have hz := basisVec_bitXor_tail z
    conv_lhs => rw [hz, hg]
    have hTailEq : g (Fin.cons false (Fin.tail z)) = dot aTail (Fin.tail z) := haTail (Fin.tail z)
    have hHeadEq : g (if z 0 then e0 else zeroVec (m + 1)) = (a 0 && z 0) := by
      cases hz0 : z 0 with
      | false =>
        have hg0 : g (zeroVec (m + 1)) = false := by
          have hxx := hg (zeroVec (m + 1)) (zeroVec (m + 1))
          rw [bitXor_self] at hxx
          cases hv : g (zeroVec (m + 1))
          · rfl
          · rw [hv] at hxx; exact absurd hxx (by decide)
        simp [hg0, Bool.and_false]
      | true =>
        simp [a, e0, Bool.and_true]
    rw [hHeadEq, hTailEq]
    simp [dot, a]

theorem isAffineMap_of_linear_translate {m k : ℕ} (Φ : BitString m → BitString k)
    (hLin : ∀ x y : BitString m, Φ (bitXor x y) = bitXor (bitXor (Φ x) (Φ y)) (Φ (zeroVec m))) :
    IsAffineMap Φ := by
  intro j
  let v : BitString k := Φ (zeroVec m)
  let g : BitString m → Bool := fun z => Φ z j ^^ v j
  have hg : ∀ x y, g (bitXor x y) = (g x ^^ g y) := fun x y => by
    dsimp only [g]
    have hpt := congrFun (hLin x y) j
    dsimp only [bitXor] at hpt
    rw [hpt]
    dsimp only [v]
    generalize Φ x j = fx
    generalize Φ y j = fy
    generalize Φ (zeroVec m) j = fv
    cases fx <;> cases fy <;> cases fv <;> decide
  obtain ⟨a, ha⟩ := linear_bool_eq_dot g hg
  have hCoord : (fun z => Φ z j) = affine a (v j) := funext fun z => by
    have hz := ha z
    dsimp only [g] at hz
    change Φ z j = (v j ^^ dot a z)
    rw [← hz]
    cases Φ z j <;> cases v j <;> decide
  rw [hCoord]
  exact isDegFn_one_affine m a (v j)

/-- Full `AGL(m, 𝔽₂)` invariance of `isDeg d m`: every invertible affine bijection on
`BitString m` preserves `isDeg d m`. -/
theorem isDeg_agl_invariant (d m : ℕ) (e : BitString m ≃ BitString m)
    (he : ∀ x y : BitString m, e (bitXor x y) = bitXor (bitXor (e x) (e y)) (e (zeroVec m)))
    (T : BitString (2 ^ m)) :
    isDeg d m (fun i => T (BitString.equivFin m (e ((BitString.equivFin m).symm i)))) =
      isDeg d m T := by
  have heAff : IsAffineMap e := isAffineMap_of_linear_translate e he
  let v : BitString m := e (zeroVec m)
  let L : BitString m → BitString m := fun x => bitXor (e x) v
  have hLLin : ∀ x y, L (bitXor x y) = bitXor (L x) (L y) := fun x y => by
    dsimp only [L]
    rw [he x y]
    funext j
    simp only [bitXor]
    dsimp only [v]
    generalize e x j = ex
    generalize e y j = ey
    generalize e (zeroVec m) j = ev
    cases ex <;> cases ey <;> cases ev <;> decide
  let Ls : BitString m → BitString m := fun y => e.symm (bitXor y v)
  have hLsInvL (x : BitString m) : Ls (L x) = x := by
    dsimp only [Ls, L]
    rw [bitXor_cancel_self_right, e.symm_apply_apply]
  have hLLsInv (y : BitString m) : L (Ls y) = y := by
    dsimp only [L, Ls]
    rw [e.apply_symm_apply, bitXor_cancel_self_right]
  have hLsLin : ∀ u w, Ls (bitXor u w) = bitXor (Ls u) (Ls w) := fun u w => by
    have hLapply : L (Ls (bitXor u w)) = L (bitXor (Ls u) (Ls w)) := by
      rw [hLLsInv, hLLin, hLLsInv, hLLsInv]
    simpa [hLsInvL] using congrArg Ls hLapply
  have hSymmLaw : ∀ x y, e.symm (bitXor x y) =
      bitXor (bitXor (e.symm x) (e.symm y)) (e.symm (zeroVec m)) := fun x y => by
    have hs (u : BitString m) : e.symm u = Ls (bitXor u v) := by
      dsimp only [Ls]
      rw [bitXor_cancel_self_right]
    rw [hs (bitXor x y), hs x, hs y, hs (zeroVec m), bitXor_zero_left]
    have hx : bitXor (bitXor x y) v = bitXor (bitXor (bitXor x v) (bitXor y v)) v := by
      funext j
      simp only [bitXor]
      cases x j <;> cases y j <;> cases v j <;> decide
    rw [hx, hLsLin, hLsLin]
  have hesAff : IsAffineMap e.symm := isAffineMap_of_linear_translate e.symm hSymmLaw
  have hFn :
      (MCSP.truthTable m).symm (fun i => T (BitString.equivFin m (e ((BitString.equivFin m).symm i)))) =
        fun z => (MCSP.truthTable m).symm T (e z) := by
    funext z
    simp [MCSP.truthTable]
  change isDegFn d m ((MCSP.truthTable m).symm _) = isDegFn d m ((MCSP.truthTable m).symm T)
  rw [hFn]
  exact isDegFn_comp_affineEquiv _ e heAff hesAff

/-- Coordinate permutations (`PermutedCut.tablePerm`) preserve `isDeg d m`. -/
theorem isDeg_perm (d m : ℕ) (σ : Equiv.Perm (Fin m)) (T : BitString (2 ^ m)) :
    isDeg d m (T ∘ PermutedCut.tablePerm σ) = isDeg d m T := by
  let e : BitString m ≃ BitString m := PermutedCut.permuteAssignment σ
  have hTable : (T ∘ PermutedCut.tablePerm σ) =
      fun i => T (BitString.equivFin m (e ((BitString.equivFin m).symm i))) := rfl
  rw [hTable]
  refine isDeg_agl_invariant d m e (fun x y => ?_) T
  funext j
  simp [e, PermutedCut.permuteAssignment, bitXor, zeroVec]

/-- XOR translations preserve `isDeg d m`. -/
theorem isDeg_translate (d m : ℕ) (v : BitString m) (T : BitString (2 ^ m)) :
    isDeg d m (fun i => T (BitString.equivFin m (bitXor ((BitString.equivFin m).symm i) v))) =
      isDeg d m T := by
  let e : BitString m ≃ BitString m :=
    { toFun := fun x => bitXor x v
      invFun := fun x => bitXor x v
      left_inv := fun x => bitXor_cancel_self_right x v
      right_inv := fun x => bitXor_cancel_self_right x v }
  refine isDeg_agl_invariant d m e (fun x y => ?_) T
  funext j
  change bitXor (bitXor x y) v j = bitXor (bitXor (bitXor x v) (bitXor y v)) (bitXor (zeroVec m) v) j
  simp only [bitXor, zeroVec]
  cases x j <;> cases y j <;> cases v j <;> decide

/-- Complementing truth-table outputs preserves `isDeg d m`. -/
theorem isDeg_notTable (d m : ℕ) (T : BitString (2 ^ m)) :
    isDeg d m (fun i => !(T i)) = isDeg d m T := by
  have hFn : (MCSP.truthTable m).symm (fun i => !(T i)) =
      fun z => !((MCSP.truthTable m).symm T z) := by
    funext z; simp [MCSP.truthTable]
  change isDegFn d m ((MCSP.truthTable m).symm _) = isDegFn d m ((MCSP.truthTable m).symm T)
  rw [hFn]
  exact isDegFn_not d m _

/-- Exact invariance of `isDeg d m` under De Morgan truth-table duality (`dualTable`). -/
theorem isDeg_dualTable (d m : ℕ) (T : BitString (2 ^ m)) :
    isDeg d m (dualTable m T) = isDeg d m T := by
  let ones : BitString m := fun _ => true
  have hVec : ∀ i : Fin (2 ^ m),
      (fun k : Fin m => !((BitString.equivFin m).symm i k)) =
        bitXor ((BitString.equivFin m).symm i) ones := fun i => funext fun j => by
    dsimp only [bitXor, ones]
    cases (BitString.equivFin m).symm i j <;> decide
  have hDual : dualTable m T = fun i =>
      !(T (BitString.equivFin m (bitXor ((BitString.equivFin m).symm i) ones))) :=
    funext fun i => congrArg (fun u => !(T (BitString.equivFin m u))) (hVec i)
  rw [hDual, isDeg_notTable]
  exact isDeg_translate d m ones T

/-! ### Part 3: Exact accepting-table count and sparsity vs `mcspSquare m` -/

/-- Reed–Muller `𝔽₂`-dimension `∑_{j=0}^d C(m, j)`. -/
def rmDim : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | d + 1, m + 1 => rmDim (d + 1) m + rmDim d m

@[simp] theorem rmDim_zero (m : ℕ) : rmDim 0 m = 1 := by
  cases m <;> rfl

@[simp] theorem rmDim_succ_zero (d : ℕ) : rmDim (d + 1) 0 = 1 := rfl

@[simp] theorem rmDim_succ_succ (d m : ℕ) :
    rmDim (d + 1) (m + 1) = rmDim (d + 1) m + rmDim d m := rfl

theorem rmDim_eq_sum_choose (d m : ℕ) :
    rmDim d m = ∑ j ∈ Finset.range (d + 1), m.choose j := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => simp
    | succ d =>
      rw [rmDim_succ_zero, Finset.sum_range_succ']
      simp
  | succ m ih =>
    cases d with
    | zero => simp
    | succ d =>
      rw [rmDim_succ_succ, ih (d + 1), ih d,
        Finset.sum_range_succ' (f := fun j => (m + 1).choose j) (n := d + 1),
        Finset.sum_range_succ' (f := fun j => m.choose j) (n := d + 1)]
      simp only [Nat.choose_zero_right]
      have hSub :
          (∑ k ∈ Finset.range (d + 1), (m.choose (k + 1) + m.choose k)) =
            ∑ k ∈ Finset.range (d + 1), (m + 1).choose (k + 1) :=
        Finset.sum_congr rfl fun k _ => by rw [Nat.choose_succ_succ', Nat.add_comm]
      rw [Finset.sum_add_distrib] at hSub
      omega

theorem rmDim_one (m : ℕ) : rmDim 1 m = m + 1 := by
  rw [rmDim_eq_sum_choose, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.add_comm]

theorem rmDim_two (m : ℕ) : rmDim 2 m = 1 + m + m.choose 2 := by
  rw [rmDim_eq_sum_choose, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.add_assoc]

/-- Bijection splitting `f : BooleanFunction (m + 1)` into its `x₀ = false` slice and its
discrete derivative along `x₀`. -/
def splitXorEquiv (m : ℕ) : BooleanFunction (m + 1) ≃ BooleanFunction m × BooleanFunction m where
  toFun f := (fun y => f (Fin.cons false y), fun y => f (Fin.cons false y) ^^ f (Fin.cons true y))
  invFun p := fun z => if z 0 then p.1 (Fin.tail z) ^^ p.2 (Fin.tail z) else p.1 (Fin.tail z)
  left_inv f := funext fun z => by
    cases hz : z 0 with
    | false =>
      have hW : Fin.cons false (Fin.tail z) = z := by
        simpa [hz] using Fin.cons_self_tail z
      simp [hz, hW]
    | true =>
      have hW : Fin.cons true (Fin.tail z) = z := by
        simpa [hz] using Fin.cons_self_tail z
      dsimp only
      rw [ite_eq_left_iff.mpr (fun h => absurd hz h), show f (Fin.cons true (Fin.tail z)) = f z from by rw [hW]]
      generalize f (Fin.cons false (Fin.tail z)) = x
      generalize f z = y
      cases x <;> cases y <;> decide
  right_inv p := by
    ext y
    · simp [Fin.cons_zero]
    · simp only [Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, Fin.tail_cons]
      generalize p.1 y = x
      generalize p.2 y = z
      cases x <;> cases z <;> decide

theorem card_isDegFn (d m : ℕ) :
    (Finset.univ.filter fun f : BooleanFunction m => isDegFn d m f = true).card =
      2 ^ rmDim d m := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero =>
      have hSet : (Finset.univ.filter fun f : BooleanFunction 0 => isDegFn 0 0 f = true) =
          Finset.univ := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rw [isDegFn_zero_iff]
        intro z
        rw [Subsingleton.elim z (zeroVec 0)]
      rw [hSet, Finset.card_univ, Fintype.card_fun, BitString.card, Fintype.card_bool,
        rmDim_zero]
      decide
    | succ d =>
      have hSet : (Finset.univ.filter fun f : BooleanFunction 0 => isDegFn (d + 1) 0 f = true) =
          Finset.univ := by
        ext f; simp [isDegFn]
      rw [hSet, Finset.card_univ, Fintype.card_fun, BitString.card, Fintype.card_bool,
        rmDim_succ_zero]
      decide
  | succ m ih =>
    cases d with
    | zero =>
      let S := Finset.univ.filter fun f : BooleanFunction (m + 1) => isDegFn 0 (m + 1) f = true
      have hEq : S = Finset.image (fun b : Bool => (fun _ : BitString (m + 1) => b)) Finset.univ := by
        ext f
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hf
          refine ⟨f (zeroVec (m + 1)), funext fun z => (isDegFn_zero_iff.mp hf z).symm⟩
        · rintro ⟨b, rfl⟩
          exact isDegFn_const 0 (m + 1) b
      have hinj : Function.Injective (fun b : Bool => (fun _ : BitString (m + 1) => b)) := by
        intro b₁ b₂ h
        exact congrFun h (zeroVec (m + 1))
      change S.card = _
      rw [hEq, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_bool,
        rmDim_zero, pow_one]
    | succ d =>
      let A := Finset.univ.filter fun g : BooleanFunction m => isDegFn (d + 1) m g = true
      let B := Finset.univ.filter fun h : BooleanFunction m => isDegFn d m h = true
      let S := Finset.univ.filter fun f : BooleanFunction (m + 1) =>
        isDegFn (d + 1) (m + 1) f = true
      have hMap : S.map (splitXorEquiv m).toEmbedding = A ×ˢ B := by
        ext p
        simp only [S, A, B, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, isDegFn, Bool.and_eq_true]
        change (isDegFn (d + 1) m (splitXorEquiv m ((splitXorEquiv m).symm p)).1 = true ∧
            isDegFn d m (splitXorEquiv m ((splitXorEquiv m).symm p)).2 = true) ↔ _
        rw [(splitXorEquiv m).apply_symm_apply]
      have hCard : S.card = A.card * B.card := by
        rw [← Finset.card_map (f := (splitXorEquiv m).toEmbedding), hMap, Finset.card_product]
      change S.card = _
      rw [hCard, ih (d + 1), ih d, rmDim_succ_succ, pow_add]

theorem card_accepting_isDeg (d m : ℕ) :
    (acceptingTables (isDeg d m)).card = 2 ^ rmDim d m := by
  let A := Finset.univ.filter fun f : BooleanFunction m => isDegFn d m f = true
  have hMap : A.map (MCSP.truthTable m).toEmbedding = acceptingTables (isDeg d m) := by
    ext T
    dsimp only [A, acceptingTables]
    rw [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_filter]
    simp [isDeg]
  rw [← hMap, Finset.card_map, card_isDegFn]

theorem rmDim_two_le_descriptionBitBound (m : ℕ) (hm : 1 ≤ m) :
    rmDim 2 m ≤ descriptionBitBound m := by
  rw [rmDim_two]
  have hChoose : m.choose 2 ≤ m ^ 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self (m * (m - 1)) 2).trans (by
      have hSub : m * (m - 1) ≤ m * m := Nat.mul_le_mul_left m (Nat.sub_le m 1)
      nlinarith [hSub])
  have hb : 1 ≤ (m + 1).log2 + 1 := Nat.le_add_left 1 _
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hBound : 4 + 7 * m ^ 2 ≤ descriptionBitBound m := by
    dsimp only [descriptionBitBound]
    have h1 : 4 * 1 ≤ 4 * ((m + 1).log2 + 1) := Nat.mul_le_mul_left 4 hb
    have h2 : (3 + 4 * 1) * m ^ 2 ≤ (3 + 4 * ((m + 1).log2 + 1)) * m ^ 2 :=
      Nat.mul_le_mul_right (m ^ 2) (by omega)
    omega
  omega

theorem card_accepting_isDeg2_le_mcspBound (m : ℕ) (hm : 1 ≤ m) :
    (acceptingTables (isDeg 2 m)).card ≤ 2 ^ descriptionBitBound m := by
  rw [card_accepting_isDeg]
  exact Nat.pow_le_pow_right (by decide) (rmDim_two_le_descriptionBitBound m hm)

/-! ### Part 4: Explicit linear-size De Morgan circuit upper bound -/

/-- Exact gate budget of our linear-size `isDeg d m` circuit synthesizer. -/
def circBound : ℕ → ℕ → ℕ
  | 0, m => 2 * 2 ^ m
  | _ + 1, 0 => 1
  | d + 1, m + 1 => 4 * 2 ^ m + circBound (d + 1) m + circBound d m + 1

/-- Degree-`≤ d` test over an arbitrary `2 ^ m`-tuple of synthesized wire functions. -/
def isDegOn {N : ℕ} (d m : ℕ) (w : BitString m → BooleanFunction N) : BooleanFunction N :=
  fun x => isDegFn d m (fun z => w z x)

private theorem allTrue_synthesis {N : ℕ} (m : ℕ) {s : Set (BooleanFunction N)}
    (w : BitString m → BooleanFunction N) (hw : ∀ z, w z ∈ s) :
    Synthesis interpretation s {fun x => decide (∀ z : BitString m, w z x = true)} (2 ^ m - 1) := by
  induction m with
  | zero =>
    have hEq : (fun x => decide (∀ z : BitString 0, w z x = true)) = w (zeroVec 0) :=
      funext fun x => by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact ⟨fun h => h (zeroVec 0), fun h z => by rwa [Subsingleton.elim z (zeroVec 0)]⟩
    rw [hEq, show 2 ^ 0 - 1 = 0 by decide]
    exact Synthesis.of_mem (hw _)
  | succ m ih =>
    have hL := ih (fun y => w (Fin.cons false y)) (fun y => hw _)
    have hR := ih (fun y => w (Fin.cons true y)) (fun y => hw _)
    have hComb := hL.and hR
    have hEq :
        (fun x => decide (∀ y : BitString m, w (Fin.cons false y) x = true) &&
          decide (∀ y : BitString m, w (Fin.cons true y) x = true)) =
        (fun x => decide (∀ z : BitString (m + 1), w z x = true)) := funext fun x => by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h0, h1⟩ z
        have hz := Fin.cons_self_tail z
        cases hZ0 : z 0
        · have : z = Fin.cons false (Fin.tail z) := by simpa [hZ0] using hz.symm
          rw [this]; exact h0 (Fin.tail z)
        · have : z = Fin.cons true (Fin.tail z) := by simpa [hZ0] using hz.symm
          rw [this]; exact h1 (Fin.tail z)
      · intro h
        exact ⟨fun y => h _, fun y => h _⟩
    rw [hEq] at hComb
    have hPos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    exact hComb.mono Set.Subset.rfl Set.Subset.rfl (by rw [pow_succ]; omega)

private theorem anyTrue_synthesis {N : ℕ} (m : ℕ) {s : Set (BooleanFunction N)}
    (w : BitString m → BooleanFunction N) (hw : ∀ z, w z ∈ s) :
    Synthesis interpretation s {fun x => decide (∃ z : BitString m, w z x = true)} (2 ^ m - 1) := by
  induction m with
  | zero =>
    have hEq : (fun x => decide (∃ z : BitString 0, w z x = true)) = w (zeroVec 0) :=
      funext fun x => by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact ⟨fun ⟨z, hz⟩ => by rwa [Subsingleton.elim z (zeroVec 0)] at hz,
          fun h => ⟨zeroVec 0, h⟩⟩
    rw [hEq, show 2 ^ 0 - 1 = 0 by decide]
    exact Synthesis.of_mem (hw _)
  | succ m ih =>
    have hL := ih (fun y => w (Fin.cons false y)) (fun y => hw _)
    have hR := ih (fun y => w (Fin.cons true y)) (fun y => hw _)
    have hComb := hL.or hR
    have hEq :
        (fun x => decide (∃ y : BitString m, w (Fin.cons false y) x = true) ||
          decide (∃ y : BitString m, w (Fin.cons true y) x = true)) =
        (fun x => decide (∃ z : BitString (m + 1), w z x = true)) := funext fun x => by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨y, hy⟩ | ⟨y, hy⟩) <;> exact ⟨_, hy⟩
      · rintro ⟨z, hz⟩
        have hEqZ := Fin.cons_self_tail z
        cases hZ0 : z 0
        · left; refine ⟨Fin.tail z, ?_⟩
          have : Fin.cons false (Fin.tail z) = z := by simpa [hZ0] using hEqZ
          rwa [this]
        · right; refine ⟨Fin.tail z, ?_⟩
          have : Fin.cons true (Fin.tail z) = z := by simpa [hZ0] using hEqZ
          rwa [this]
    rw [hEq] at hComb
    have hPos : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
    exact hComb.mono Set.Subset.rfl Set.Subset.rfl (by rw [pow_succ]; omega)

theorem isDegOn_synthesis {N : ℕ} (d m : ℕ) {s : Set (BooleanFunction N)}
    (w : BitString m → BooleanFunction N) (hw : ∀ z, w z ∈ s) :
    Synthesis interpretation s {isDegOn d m w} (circBound d m) := by
  induction m generalizing d s with
  | zero =>
    cases d with
    | zero =>
      have hAll := allTrue_synthesis 0 w hw
      have hNotAny := (anyTrue_synthesis 0 w hw).not
      have hOr := hAll.or hNotAny
      have hEq :
          (fun x => decide (∀ z : BitString 0, w z x = true) ||
            !decide (∃ z : BitString 0, w z x = true)) =
          isDegOn 0 0 w := funext fun x => by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          not_exists, Bool.not_eq_true, isDegOn, isDegFn]
        constructor
        · rintro (hT | hF) z
          · rw [hT z, hT (zeroVec 0)]
          · rw [hF z, hF (zeroVec 0)]
        · intro h
          cases h0 : w (zeroVec 0) x
          · right; intro z; rw [h z, h0]
          · left; intro z; rw [h z, h0]
      rw [hEq] at hOr
      exact hOr.mono Set.Subset.rfl Set.Subset.rfl (by decide)
    | succ d =>
      exact (Synthesis.of_forall_eq_const true (fun _ => rfl)).mono
        Set.Subset.rfl Set.Subset.rfl (by dsimp [circBound]; omega)
  | succ m ih =>
    cases d with
    | zero =>
      have hAll := allTrue_synthesis (m + 1) w hw
      have hNotAny := (anyTrue_synthesis (m + 1) w hw).not
      have hOr := hAll.or hNotAny
      have hPos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow (m + 1) 2 (by decide)
      have hEq :
          (fun x => decide (∀ z : BitString (m + 1), w z x = true) ||
            !decide (∃ z : BitString (m + 1), w z x = true)) =
          isDegOn 0 (m + 1) w := funext fun x => by
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          not_exists, Bool.not_eq_true, isDegOn, isDegFn]
        constructor
        · rintro (hT | hF) z
          · rw [hT z, hT (zeroVec (m + 1))]
          · rw [hF z, hF (zeroVec (m + 1))]
        · intro h
          cases h0 : w (zeroVec (m + 1)) x
          · right; intro z; rw [h z, h0]
          · left; intro z; rw [h z, h0]
      rw [hEq] at hOr
      have hCirc : circBound 0 (m + 1) = 2 * 2 ^ (m + 1) := rfl
      exact hOr.mono Set.Subset.rfl Set.Subset.rfl (by rw [hCirc]; omega)
    | succ d =>
      let w0 : BitString m → BooleanFunction N := fun y => w (Fin.cons false y)
      let w1 : BitString m → BooleanFunction N := fun y => w (Fin.cons true y)
      let wDelta : BitString m → BooleanFunction N := fun y x => w0 y x ^^ w1 y x
      have hDelta : Synthesis interpretation s (Set.range wDelta) (4 * 2 ^ m) := by
        have hFam := Synthesis.family wDelta (fun _ => 4) fun y =>
          (Synthesis.of_mem (hw (Fin.cons false y))).xor (Synthesis.of_mem (hw (Fin.cons true y)))
        simpa [Finset.sum_const, smul_eq_mul, BitString.card, Nat.mul_comm] using hFam
      have h0 := ih (d + 1) (s := s ∪ Set.range wDelta) w0 (fun y => Set.mem_union_left _ (hw _))
      have h1 := ih d (s := s ∪ Set.range wDelta) wDelta (fun y => Set.mem_union_right _ ⟨y, rfl⟩)
      have hBoth := h0.and h1
      have hEq : (fun x => isDegOn (d + 1) m w0 x && isDegOn d m wDelta x) =
          isDegOn (d + 1) (m + 1) w := funext fun x => rfl
      rw [hEq] at hBoth
      have hFull := hDelta.trans hBoth
      exact hFull.mono Set.Subset.rfl Set.Subset.rfl (by dsimp [circBound]; omega)

@[simp] theorem circBound_zero (m : ℕ) : circBound 0 m = 2 * 2 ^ m := by
  cases m <;> rfl

theorem circBound_one_le (m : ℕ) : circBound 1 m ≤ 6 * 2 ^ m + m := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hStep : circBound 1 (m + 1) = 4 * 2 ^ m + circBound 1 m + circBound 0 m + 1 := rfl
    rw [hStep, circBound_zero, pow_succ]
    omega

theorem circBound_two_le (m : ℕ) : circBound 2 m ≤ 10 * 2 ^ m + m ^ 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hStep : circBound 2 (m + 1) = 4 * 2 ^ m + circBound 2 m + circBound 1 m + 1 := rfl
    have h1 := circBound_one_le m
    rw [hStep, pow_succ]
    nlinarith

private theorem poly_slack_step (a d : ℕ) :
    (d + 2) * (a + 1) ^ (d + 2) + (d + 1) * (a + 1) ^ (d + 1) + 1 ≤
      (d + 2) * (a + 2) ^ (d + 2) := by
  have hBase : ∀ k ≥ 2, (a + 1) ^ k + k * (a + 1) ^ (k - 1) + 1 ≤ (a + 2) ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [show 2 - 1 = 1 by rfl]
      nlinarith
    | succ k hk ihk =>
      have hSplit : (a + 1) ^ k = (a + 1) ^ (k - 1) * (a + 1) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      have hMul : ((a + 1) ^ k + k * (a + 1) ^ (k - 1) + 1) * (a + 2) ≤ (a + 2) ^ (k + 1) := by
        rw [pow_succ]
        exact Nat.mul_le_mul_right (a + 2) ihk
      have hMid : (a + 1) ^ (k + 1) + (k + 1) * (a + 1) ^ k + 1 ≤
          ((a + 1) ^ k + k * (a + 1) ^ (k - 1) + 1) * (a + 2) := by
        have hLHS : (a + 1) ^ (k + 1) + (k + 1) * (a + 1) ^ k + 1 =
            (a + 1) ^ k * (a + 1) + k * (a + 1) ^ k + (a + 1) ^ k + 1 := by
          rw [pow_succ]; ring
        have hRHS : ((a + 1) ^ k + k * (a + 1) ^ (k - 1) + 1) * (a + 2) =
            (a + 1) ^ k * (a + 1) + (a + 1) ^ k + k * ((a + 1) ^ (k - 1) * (a + 1)) +
              k * (a + 1) ^ (k - 1) + a + 2 := by ring
        rw [hLHS, hRHS, ← hSplit]
        omega
      rw [show k + 1 - 1 = k by omega]
      exact hMid.trans hMul
  have h2 := hBase (d + 2) (by omega)
  rw [show d + 2 - 1 = d + 1 by omega] at h2
  have hMul : (d + 2) * ((a + 1) ^ (d + 2) + (d + 2) * (a + 1) ^ (d + 1) + 1) ≤
      (d + 2) * (a + 2) ^ (d + 2) := Nat.mul_le_mul_left (d + 2) h2
  have hQuad : d + 1 ≤ (d + 2) * (d + 2) := by nlinarith
  have hY : (d + 1) * (a + 1) ^ (d + 1) ≤ (d + 2) * (d + 2) * (a + 1) ^ (d + 1) :=
    Nat.mul_le_mul_right _ hQuad
  have hOne : 1 ≤ d + 2 := by omega
  have hExp : (d + 2) * ((a + 1) ^ (d + 2) + (d + 2) * (a + 1) ^ (d + 1) + 1) =
      (d + 2) * (a + 1) ^ (d + 2) + (d + 2) * (d + 2) * (a + 1) ^ (d + 1) + (d + 2) := by ring
  omega

theorem circBound_le (d m : ℕ) :
    circBound d m ≤ (4 * d + 2) * 2 ^ m + d * (m + 1) ^ d := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => decide
    | succ d =>
      change 1 ≤ (4 * (d + 1) + 2) * 2 ^ 0 + (d + 1) * (0 + 1) ^ (d + 1)
      simp only [pow_zero, Nat.mul_one]
      omega
  | succ m ih =>
    cases d with
    | zero =>
      rw [circBound_zero]
      omega
    | succ d =>
      cases d with
      | zero =>
        have h1 := circBound_one_le (m + 1)
        simp only [Nat.zero_add, Nat.mul_one, pow_one]
        omega
      | succ d =>
        change circBound (d + 2) (m + 1) ≤
          (4 * (d + 2) + 2) * 2 ^ (m + 1) + (d + 2) * (m + 2) ^ (d + 2)
        have hA := ih (d + 2)
        have hB := ih (d + 1)
        have hP := poly_slack_step m d
        have hStep : circBound (d + 2) (m + 1) =
            4 * 2 ^ m + circBound (d + 2) m + circBound (d + 1) m + 1 := rfl
        have hAlg : 4 * 2 ^ m + (4 * (d + 2) + 2) * 2 ^ m + (4 * (d + 1) + 2) * 2 ^ m ≤
            (4 * (d + 2) + 2) * 2 ^ (m + 1) := by
          rw [pow_succ 2 m]
          nlinarith
        omega

/-- Explicit linear-size De Morgan circuit upper bound for `isDeg d m`. -/
theorem complexity_isDeg_le (d m : ℕ) :
    complexity interpretation (single (isDeg d m)) ≤ (4 * d + 2) * 2 ^ m + d * (m + 1) ^ d := by
  have hSyn := isDegOn_synthesis d m (N := 2 ^ m) (s := inputs (2 ^ m))
    (fun z => fun T : BitString (2 ^ m) => T (BitString.equivFin m z))
    (fun z => ⟨BitString.equivFin m z, rfl⟩)
  have hEq : isDegOn d m (fun z => fun T : BitString (2 ^ m) => T (BitString.equivFin m z)) =
      isDeg d m := rfl
  rw [hEq] at hSyn
  exact hSyn.complexity_le.trans (circBound_le d m)

theorem complexity_isDeg1_le (m : ℕ) :
    complexity interpretation (single (isDeg 1 m)) ≤ 6 * 2 ^ m + m := by
  have hSyn := isDegOn_synthesis 1 m (N := 2 ^ m) (s := inputs (2 ^ m))
    (fun z => fun T : BitString (2 ^ m) => T (BitString.equivFin m z))
    (fun z => ⟨BitString.equivFin m z, rfl⟩)
  have hEq : isDegOn 1 m (fun z => fun T : BitString (2 ^ m) => T (BitString.equivFin m z)) =
      isDeg 1 m := rfl
  rw [hEq] at hSyn
  exact hSyn.complexity_le.trans (circBound_one_le m)

theorem complexity_isDeg2_le (m : ℕ) :
    complexity interpretation (single (isDeg 2 m)) ≤ 10 * 2 ^ m + m ^ 2 := by
  have hSyn := isDegOn_synthesis 2 m (N := 2 ^ m) (s := inputs (2 ^ m))
    (fun z => fun T : BitString (2 ^ m) => T (BitString.equivFin m z))
    (fun z => ⟨BitString.equivFin m z, rfl⟩)
  have hEq : isDegOn 2 m (fun z => fun T : BitString (2 ^ m) => T (BitString.equivFin m z)) =
      isDeg 2 m := rfl
  rw [hEq] at hSyn
  exact hSyn.complexity_le.trans (circBound_two_le m)

/-! ### Part 5: Explicit linear-size De Morgan formula leaf-size upper bound -/

theorem leafSize_bind_mul_le {k n c : ℕ} (G : Fin k → Formula signature n)
    (hG : ∀ i, (G i).leafSize ≤ c) (F : Formula signature k) :
    (F.bind G).leafSize ≤ c * F.leafSize := by
  induction F with
  | input i => simpa using hG i
  | gate op args ih =>
    rw [Formula.gate_bind, Formula.leafSize_gate, Formula.leafSize_gate, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => ih j

/-- Balanced recursive conjunction formula over `2 ^ m` leaf formulas. -/
def andAllFormula {n : ℕ} : (m : ℕ) → (BitString m → Formula signature n) → Formula signature n
  | 0, F => F (zeroVec 0)
  | m + 1, F =>
      (andAllFormula m fun y => F (Fin.cons false y)).and
        (andAllFormula m fun y => F (Fin.cons true y))

theorem eval_andAllFormula {n : ℕ} (m : ℕ) (F : BitString m → Formula signature n)
    (x : BitString n) :
    (andAllFormula m F).eval interpretation x = true ↔
      ∀ z : BitString m, (F z).eval interpretation x = true := by
  induction m with
  | zero =>
    change (F (zeroVec 0)).eval interpretation x = true ↔ _
    exact ⟨fun h z => by rwa [Subsingleton.elim z (zeroVec 0)], fun h => h (zeroVec 0)⟩
  | succ m ih =>
    simp only [andAllFormula, Formula.eval_and, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ z
      have hz := Fin.cons_self_tail z
      cases hz0 : z 0
      · have : z = Fin.cons false (Fin.tail z) := by simpa [hz0] using hz.symm
        rw [this]; exact h0 _
      · have : z = Fin.cons true (Fin.tail z) := by simpa [hz0] using hz.symm
        rw [this]; exact h1 _
    · intro h
      exact ⟨fun y => h _, fun y => h _⟩

theorem leafSize_andAllFormula {n : ℕ} (m : ℕ) (F : BitString m → Formula signature n)
    (hF : ∀ z, (F z).leafSize = 1) :
    (andAllFormula m F).leafSize = 2 ^ m := by
  induction m with
  | zero => simpa [andAllFormula] using hF (zeroVec 0)
  | succ m ih =>
    simp only [andAllFormula, Formula.leafSize_and]
    rw [ih (fun y => F (Fin.cons false y)) (fun y => hF _),
      ih (fun y => F (Fin.cons true y)) (fun y => hF _), pow_succ]
    omega

/-- Index of `(false, y)` inside `Fin (2 ^ (m + 1))`. -/
def idx0 {m : ℕ} (i : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  BitString.equivFin (m + 1) (Fin.cons false ((BitString.equivFin m).symm i))

/-- Index of `(true, y)` inside `Fin (2 ^ (m + 1))`. -/
def idx1 {m : ℕ} (i : Fin (2 ^ m)) : Fin (2 ^ (m + 1)) :=
  BitString.equivFin (m + 1) (Fin.cons true ((BitString.equivFin m).symm i))

/-- Explicit linear-size De Morgan formula computing `isDeg d m`. -/
def degFormula : (d m : ℕ) → Formula signature (2 ^ m)
  | 0, m =>
      (andAllFormula m fun z => Formula.input (BitString.equivFin m z)).or
        (andAllFormula m fun z => (Formula.input (BitString.equivFin m z)).not)
  | _ + 1, 0 => Formula.const true
  | d + 1, m + 1 =>
      ((degFormula (d + 1) m).bind fun i => Formula.input (idx0 i)).and
        ((degFormula d m).bind fun i => (Formula.input (idx0 i)).xor (Formula.input (idx1 i)))

private theorem degFormula_zero_computes (m : ℕ) :
    (degFormula 0 m).Computes interpretation (isDeg 0 m) := by
  intro T
  have hEq0 : degFormula 0 m =
      (andAllFormula m fun z => Formula.input (BitString.equivFin m z)).or
        (andAllFormula m fun z => (Formula.input (BitString.equivFin m z)).not) := by
    cases m <;> rfl
  rw [hEq0, Formula.eval_or, isDeg]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, eval_andAllFormula, Formula.eval_not, Formula.eval_input,
    isDegFn, decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro (hT | hF) z
    · have h0 := hT (zeroVec m)
      have hz := hT z
      change T (BitString.equivFin m z) = T (BitString.equivFin m (zeroVec m))
      exact hz.trans h0.symm
    · have h0 := hF (zeroVec m)
      have hz := hF z
      change T (BitString.equivFin m z) = T (BitString.equivFin m (zeroVec m))
      exact hz.trans h0.symm
  · intro h
    cases h0 : T (BitString.equivFin m (zeroVec m))
    · right
      intro z
      have hz : T (BitString.equivFin m z) = T (BitString.equivFin m (zeroVec m)) := h z
      rw [hz, h0]
    · left
      intro z
      have hz : T (BitString.equivFin m z) = T (BitString.equivFin m (zeroVec m)) := h z
      rw [hz, h0]

theorem degFormula_computes (d m : ℕ) :
    (degFormula d m).Computes interpretation (isDeg d m) := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero => exact degFormula_zero_computes 0
    | succ d =>
      intro T
      rfl
  | succ m ih =>
    cases d with
    | zero => exact degFormula_zero_computes (m + 1)
    | succ d =>
      intro T
      change (((degFormula (d + 1) m).bind fun i => Formula.input (idx0 i)).and
          ((degFormula d m).bind fun i =>
            (Formula.input (idx0 i)).xor (Formula.input (idx1 i)))).eval interpretation T =
        isDeg (d + 1) (m + 1) T
      simp only [Formula.eval_and, Formula.eval_bind, Formula.eval_xor, Formula.eval_input]
      have h0 :
          (degFormula (d + 1) m).eval interpretation (fun i => T (idx0 i)) =
            isDegFn (d + 1) m (fun y => (MCSP.truthTable (m + 1)).symm T (Fin.cons false y)) := by
        have hComp := ih (d + 1) (MCSP.truthTable m (fun y => (MCSP.truthTable (m + 1)).symm T (Fin.cons false y)))
        have hIn : (fun i => T (idx0 i)) =
            MCSP.truthTable m (fun y => (MCSP.truthTable (m + 1)).symm T (Fin.cons false y)) := by
          funext i
          simp [idx0, MCSP.truthTable]
        rw [hIn, hComp, isDeg_truthTable]
      have h1 :
          (degFormula d m).eval interpretation (fun i => T (idx0 i) ^^ T (idx1 i)) =
            isDegFn d m (fun y =>
              (MCSP.truthTable (m + 1)).symm T (Fin.cons false y) ^^
              (MCSP.truthTable (m + 1)).symm T (Fin.cons true y)) := by
        have hComp := ih d (MCSP.truthTable m (fun y =>
          (MCSP.truthTable (m + 1)).symm T (Fin.cons false y) ^^
          (MCSP.truthTable (m + 1)).symm T (Fin.cons true y)))
        have hIn : (fun i => T (idx0 i) ^^ T (idx1 i)) =
            MCSP.truthTable m (fun y =>
              (MCSP.truthTable (m + 1)).symm T (Fin.cons false y) ^^
              (MCSP.truthTable (m + 1)).symm T (Fin.cons true y)) := by
          funext i
          simp [idx0, idx1, MCSP.truthTable]
        rw [hIn, hComp, isDeg_truthTable]
      rw [h0, h1]
      rfl

theorem leafSize_degFormula_le (d m : ℕ) :
    (degFormula d m).leafSize ≤ 2 * 4 ^ d * 2 ^ m := by
  induction m generalizing d with
  | zero =>
    cases d with
    | zero =>
      simp only [degFormula, Formula.leafSize_or]
      rw [leafSize_andAllFormula 0 _ (fun _ => rfl),
        leafSize_andAllFormula 0 _ (fun _ => by simp [Formula.leafSize_not, Formula.leafSize_input])]
      decide
    | succ d =>
      simp [degFormula, Formula.leafSize_const]
  | succ m ih =>
    cases d with
    | zero =>
      have hEq0 : degFormula 0 (m + 1) =
          (andAllFormula (m + 1) fun z => Formula.input (BitString.equivFin (m + 1) z)).or
            (andAllFormula (m + 1) fun z => (Formula.input (BitString.equivFin (m + 1) z)).not) := rfl
      rw [hEq0, Formula.leafSize_or,
        leafSize_andAllFormula (m + 1) _ (fun _ => rfl),
        leafSize_andAllFormula (m + 1) _ (fun _ => by simp [Formula.leafSize_not, Formula.leafSize_input])]
      simp [pow_zero]
      omega
    | succ d =>
      have hStep : degFormula (d + 1) (m + 1) =
          ((degFormula (d + 1) m).bind fun i => Formula.input (idx0 i)).and
            ((degFormula d m).bind fun i => (Formula.input (idx0 i)).xor (Formula.input (idx1 i))) := rfl
      rw [hStep, Formula.leafSize_and]
      have hL : ((degFormula (d + 1) m).bind fun i => Formula.input (idx0 i)).leafSize ≤
          (degFormula (d + 1) m).leafSize :=
        Formula.leafSize_bind_le (fun _ => le_rfl) _
      have hR : ((degFormula d m).bind fun i => (Formula.input (idx0 i)).xor (Formula.input (idx1 i))).leafSize ≤
          4 * (degFormula d m).leafSize :=
        leafSize_bind_mul_le _ (fun _ => by simp [Formula.leafSize_xor, Formula.leafSize_input]) _
      have hL' : ((degFormula (d + 1) m).bind fun i => Formula.input (idx0 i)).leafSize ≤
          2 * 4 ^ (d + 1) * 2 ^ m := hL.trans (ih (d + 1))
      have hR' : ((degFormula d m).bind fun i => (Formula.input (idx0 i)).xor (Formula.input (idx1 i))).leafSize ≤
          2 * 4 ^ (d + 1) * 2 ^ m := by
        calc
          _ ≤ 4 * (degFormula d m).leafSize := hR
          _ ≤ 4 * (2 * 4 ^ d * 2 ^ m) := Nat.mul_le_mul_left 4 (ih d)
          _ = 2 * 4 ^ (d + 1) * 2 ^ m := by rw [pow_succ]; ring
      calc
        ((degFormula (d + 1) m).bind fun i => Formula.input (idx0 i)).leafSize +
            ((degFormula d m).bind fun i =>
              (Formula.input (idx0 i)).xor (Formula.input (idx1 i))).leafSize
            ≤ 2 * 4 ^ (d + 1) * 2 ^ m + 2 * 4 ^ (d + 1) * 2 ^ m := Nat.add_le_add hL' hR'
        _ = 2 * 4 ^ (d + 1) * 2 ^ (m + 1) := by rw [pow_succ 2 m]; ring

theorem formulaSize_isDeg_le (d m : ℕ) :
    formulaSize (isDeg d m) ≤ 2 * 4 ^ d * 2 ^ m :=
  (formulaSize_le (degFormula_computes d m)).trans (leafSize_degFormula_le d m)

theorem formulaSize_isDeg2_le (m : ℕ) :
    formulaSize (isDeg 2 m) ≤ 32 * 2 ^ m := by
  simpa using formulaSize_isDeg_le 2 m

/-! ### Part 6: Exact two-sided bracket for `isDeg 2 32` and `mcspSquare` separation witnesses -/

/-- `MCSPQuadraticForest.quad_reindexed_forest_size` applies unconditionally to `isDeg 2 m`
using its exact accepting-table bound `2 ^ rmDim 2 m`. -/
theorem isDeg2_quad_super_twoN (m : ℕ) :
    280 * (2 * 2 ^ m) + 2 * 2 ^ m ≤
      280 * (complexity interpretation (single (isDeg 2 m)) + 2 * rmDim 2 m + 1) +
        17 * rmDim 2 m :=
  quad_reindexed_forest_size (BitString.equivFin m).symm.toEmbedding
    (le_of_eq (card_accepting_isDeg 2 m))
    (fun a b0 c d => by
      change isDeg 2 m (MCSP.truthTable m (quad a b0 c d)) = true
      exact isDeg_two_accepts_quad m a b0 c d)

/-- Complete two-sided barrier bundle at `m = 32` (`N = 2^32 = 4,294,967,296`,
`rmDim 2 32 = 529 < 27,672 = descriptionBitBound 32`). -/
theorem isDeg2_32_bracket :
    (acceptingTables (isDeg 2 32)).card = 2 ^ 529 ∧
    (acceptingTables (isDeg 2 32)).card ≤ 2 ^ descriptionBitBound 32 ∧
    (∀ (a : BitString 32) (b0 : Bool) (c d : BitString 32),
      isDeg 2 32 (MCSP.truthTable 32 (quad a b0 c d)) = true) ∧
    8620611839 ≤ complexity interpretation (single (isDeg 2 32)) ∧
    complexity interpretation (single (isDeg 2 32)) ≤ 42949673984 ∧
    formulaSize (isDeg 2 32) ≤ 137438953472 := by
  have hRm : rmDim 2 32 = 529 := by
    rw [rmDim_two]
    decide
  have hCard : (acceptingTables (isDeg 2 32)).card = 2 ^ 529 := by
    rw [card_accepting_isDeg, hRm]
  have hSparse : (acceptingTables (isDeg 2 32)).card ≤ 2 ^ descriptionBitBound 32 :=
    card_accepting_isDeg2_le_mcspBound 32 (by decide)
  have hLB : 8620611839 ≤ complexity interpretation (single (isDeg 2 32)) := by
    have h := isDeg2_quad_super_twoN 32
    rw [hRm] at h
    change 280 * (2 * 4294967296) + 2 * 4294967296 ≤
      280 * (complexity interpretation (single (isDeg 2 32)) + 2 * 529 + 1) + 17 * 529 at h
    omega
  have hUB : complexity interpretation (single (isDeg 2 32)) ≤ 42949673984 := by
    have h := complexity_isDeg2_le 32
    change complexity interpretation (single (isDeg 2 32)) ≤ 10 * 4294967296 + 1024 at h
    omega
  have hForm : formulaSize (isDeg 2 32) ≤ 137438953472 := by
    have h := formulaSize_isDeg2_le 32
    change formulaSize (isDeg 2 32) ≤ 32 * 4294967296 at h
    omega
  exact ⟨hCard, hSparse, fun a b0 c d => isDeg_two_accepts_quad 32 a b0 c d, hLB, hUB, hForm⟩

/-- Point-indicator function on `m` bits: `true` solely at `a : BitString m`. -/
def pointFn (m : ℕ) (a : BitString m) : BooleanFunction m :=
  fun z => decide (z = a)

theorem isDegFn_pointFn_false : ∀ {d m : ℕ} (_hdm : d < m) (a : BitString m),
    isDegFn d m (pointFn m a) = false
  | 0, m + 1, _, a => by
    rw [Bool.eq_false_iff]
    intro hT
    have hConst := isDegFn_zero_iff.mp hT
    let aFlip : BitString (m + 1) := fun j => if j = 0 then !(a 0) else a j
    have h1 := hConst a
    have h2 := hConst aFlip
    have ha : pointFn (m + 1) a a = true := by simp [pointFn]
    have haf : pointFn (m + 1) a aFlip = false := by
      simp only [pointFn, decide_eq_false_iff_not]
      intro hEq
      have h0Eq := congrFun hEq 0
      simp only [aFlip, ↓reduceIte] at h0Eq
      exact Bool.not_ne_self (a 0) h0Eq
    rw [ha] at h1
    rw [haf] at h2
    have hBad : true = false := h1.trans h2.symm
    cases hBad
  | d + 1, m + 1, hdm, a => by
    have hDeriv :
        (fun y => pointFn (m + 1) a (Fin.cons false y) ^^
          pointFn (m + 1) a (Fin.cons true y)) =
        pointFn m (Fin.tail a) := by
      funext y
      by_cases hy : y = Fin.tail a
      · subst hy
        cases ha0 : a 0
        · have h0 : Fin.cons false (Fin.tail a) = a := by
            simpa [ha0] using Fin.cons_self_tail a
          have h1 : Fin.cons true (Fin.tail a) ≠ a := by
            intro hEq
            have := congrFun hEq 0
            simp [ha0] at this
          simp [pointFn, h0, h1]
        · have h1 : Fin.cons true (Fin.tail a) = a := by
            simpa [ha0] using Fin.cons_self_tail a
          have h0 : Fin.cons false (Fin.tail a) ≠ a := by
            intro hEq
            have := congrFun hEq 0
            simp [ha0] at this
          simp [pointFn, h0, h1]
      · have hNe (b : Bool) : Fin.cons b y ≠ a := fun hEq =>
          hy (funext fun j => by simpa [Fin.tail] using congrFun hEq j.succ)
        simp [pointFn, hNe false, hNe true, hy]
    simp only [isDegFn, hDeriv, Bool.and_eq_false_iff]
    right
    exact isDegFn_pointFn_false (by omega) (Fin.tail a)

theorem mcspSquare_accepts_pointFn {m : ℕ} (hm : 3 ≤ m) (a : BitString m) :
    mcspSquare m (MCSP.truthTable m (pointFn m a)) = true := by
  have hSyn := Boolean.synthesis_minterm (n := m) id a
  have hEq : (fun x : BitString m => decide ((fun i => x (id i)) = a)) = pointFn m a := rfl
  rw [hEq] at hSyn
  have hBudget : 2 * m + 1 ≤ m ^ 2 := by nlinarith
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  exact hSyn.complexity_le.trans hBudget

theorem mcspSquare_ne_isDeg_of_pointFn {d m : ℕ} (hdm : d < m) (hm : 3 ≤ m) (a : BitString m) :
    mcspSquare m (MCSP.truthTable m (pointFn m a)) = true ∧
      isDeg d m (MCSP.truthTable m (pointFn m a)) = false :=
  ⟨mcspSquare_accepts_pointFn hm a, by
    rw [isDeg_truthTable]
    exact isDegFn_pointFn_false hdm a⟩

/-- Explicit degree-3 monomial separation witness `x₀ ∧ x₁ ∧ x₂` (gate cost `≤ 2`). -/
def monomial3 (m : ℕ) (hm : 3 ≤ m) : BooleanFunction m :=
  fun z => (z ⟨0, by omega⟩ && z ⟨1, by omega⟩) && z ⟨2, by omega⟩

theorem mcspSquare_accepts_monomial3 {m : ℕ} (hm : 3 ≤ m) :
    mcspSquare m (MCSP.truthTable m (monomial3 m hm)) = true := by
  have h0 : Synthesis interpretation (inputs m) {fun z : BitString m => z ⟨0, by omega⟩} 0 :=
    Synthesis.of_mem (s := inputs m) ⟨⟨0, by omega⟩, rfl⟩
  have h1 : Synthesis interpretation (inputs m) {fun z : BitString m => z ⟨1, by omega⟩} 0 :=
    Synthesis.of_mem (s := inputs m) ⟨⟨1, by omega⟩, rfl⟩
  have h2 : Synthesis interpretation (inputs m) {fun z : BitString m => z ⟨2, by omega⟩} 0 :=
    Synthesis.of_mem (s := inputs m) ⟨⟨2, by omega⟩, rfl⟩
  have h012 : Synthesis interpretation (inputs m) {monomial3 m hm} 2 :=
    (h0.and h1).and h2
  have hBudget : 2 ≤ m ^ 2 := by nlinarith
  rw [mcspSquare, GapMCSP.slice_yesSet_eq_true_iff, Equiv.symm_apply_apply]
  exact h012.complexity_le.trans hBudget

theorem isDeg_monomial3_false {m : ℕ} (hm : 3 ≤ m) :
    isDeg 2 m (MCSP.truthTable m (monomial3 m hm)) = false := by
  rw [isDeg_truthTable, Bool.eq_false_iff]
  intro hDeg
  let Φ : BitString 3 → BitString m := fun w => BitString.zeroExtend w
  have hΦ : IsAffineMap Φ := fun j => by
    by_cases hj : j.val < 3
    · have hEq : (fun w : BitString 3 => Φ w j) = fun w => w ⟨j.val, hj⟩ := funext fun w => by
        simp [Φ, BitString.zeroExtend, hj]
      rw [hEq]
      exact isDegFn_one_coord 3 ⟨j.val, hj⟩
    · have hEq : (fun w : BitString 3 => Φ w j) = fun _ => false := funext fun w => by
        simp [Φ, BitString.zeroExtend, hj]
      rw [hEq]
      exact isDegFn_const 1 3 false
  have hComp : (fun w : BitString 3 => monomial3 m hm (Φ w)) = pointFn 3 (fun _ => true) := by
    funext w
    have h0 : Φ w ⟨0, by omega⟩ = w 0 := by simp [Φ, BitString.zeroExtend]
    have h1 : Φ w ⟨1, by omega⟩ = w 1 := by simp [Φ, BitString.zeroExtend]
    have h2 : Φ w ⟨2, by omega⟩ = w 2 := by simp [Φ, BitString.zeroExtend]
    simp only [monomial3, pointFn, h0, h1, h2]
    have : w = (fun _ : Fin 3 => true) ↔ (w 0 = true ∧ w 1 = true ∧ w 2 = true) := by
      constructor
      · intro hw; simp [hw]
      · intro ⟨hw0, hw1, hw2⟩
        funext i
        fin_cases i <;> assumption
    cases hw0 : w 0 <;> cases hw1 : w 1 <;> cases hw2 : w 2 <;> simp_all
  have hBad := isDegFn_comp_affine hDeg hΦ
  rw [hComp, isDegFn_pointFn_false (d := 2) (m := 3) (by decide) (fun _ => true)] at hBad
  cases hBad

/-- At `m = 32`, the 9-bit prefix probe `CommunicationCut.probe 22 (pointFn 9 (zeroVec 9))`
is accepted by `mcspSquare 32` while rejected by `isDeg d 32` for every degree `d < 9`
(including `isDeg 2 32`). -/
theorem isDeg_prefix_probe_sep_32 (d : ℕ) (hd : d < 9) :
    mcspSquare 32 (CommunicationCut.probe 22 (pointFn 9 (zeroVec 9))) = true ∧
      isDeg d 32 (CommunicationCut.probe 22 (pointFn 9 (zeroVec 9))) = false := by
  let f9 : BooleanFunction 9 := pointFn 9 (zeroVec 9)
  have hAcc : mcspSquare 32 (CommunicationCut.probe 22 f9) = true :=
    probe_is_accepted_shannon (k := 2) (d := 7) f9 (by decide)
  refine ⟨hAcc, ?_⟩
  rw [Bool.eq_false_iff]
  intro hDeg
  change isDeg d (9 + (22 + 1)) (CommunicationCut.probe 22 f9) = true at hDeg
  change isDegFn d (9 + (22 + 1))
    ((MCSP.truthTable (9 + (22 + 1))).symm (CommunicationCut.probe 22 f9)) = true at hDeg
  let Φ : BitString 9 → BitString (9 + (22 + 1)) := fun w => BitString.zeroExtend w
  have hΦ : IsAffineMap Φ := fun j => by
    by_cases hj : j.val < 9
    · have hEq : (fun w : BitString 9 => Φ w j) = fun w => w ⟨j.val, hj⟩ := funext fun w => by
        simp [Φ, BitString.zeroExtend, hj]
      rw [hEq]
      exact isDegFn_one_coord 9 ⟨j.val, hj⟩
    · have hEq : (fun w : BitString 9 => Φ w j) = fun _ => false := funext fun w => by
        simp [Φ, BitString.zeroExtend, hj]
      rw [hEq]
      exact isDegFn_const 1 9 false
  have hComp :
      (fun w : BitString 9 =>
        ((MCSP.truthTable (9 + (22 + 1))).symm (CommunicationCut.probe 22 f9)) (Φ w)) = f9 := by
    funext w
    rw [CommunicationCut.probe, Equiv.symm_apply_apply]
    congr 1
    funext i
    simp [Φ, BitString.zeroExtend, i.isLt]
  have hBad := isDegFn_comp_affine hDeg hΦ
  rw [hComp, isDegFn_pointFn_false hd (zeroVec 9)] at hBad
  cases hBad

end PvsNP.Frontier.PolynomialBarrier
