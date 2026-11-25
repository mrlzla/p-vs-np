import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_066_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl run w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, run]; omega

private theorem run_keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl run w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (run w g) (by simp [run]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem append_and_chain (todo : List ℕ) (start acc : ℕ)
    (hacc : acc < start) (hvalid : ∀ i ∈ todo, i < start) :
    ∃ gs : List Gate, ∃ o : ℕ,
      FanInTwo ⟨gs, o⟩ ∧ gs.length = todo.length ∧ o < start + gs.length ∧
      ∀ w : List Bool, w.length = start →
        (gs.foldl run w).getD o false = (w.getD acc false && todo.all fun i => w.getD i false) := by
  induction todo generalizing start acc with
  | nil =>
    exact ⟨[], acc, by simp [FanInTwo], rfl, by simpa using hacc, by simp⟩
  | cons i is ih =>
    have hi := hvalid i (List.mem_cons_self ..)
    obtain ⟨gs, o, hgs, hlen, ho, hev⟩ := ih (start + 1) start (by omega) (fun j hj =>
      (hvalid j (List.mem_cons_of_mem i hj)).trans (Nat.lt_succ_self start))
    let gate : Gate := ⟨GateOp.and, [acc, i]⟩
    refine ⟨gate :: gs, o, ?_, by simp [hlen], by simp; omega, ?_⟩
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [gate]
      · exact hgs g hg
    · intro w hw
      have hkeep (j : ℕ) (hj : j < start) : (run w gate).getD j false = w.getD j false :=
        List.getD_append _ _ _ _ (hw.symm ▸ hj)
      have hnew : (run w gate).getD start false = (w.getD acc false && w.getD i false) := by
        rw [← hw]
        simp [run, gate, GateOp.eval]
      have htail : (is.all fun j => (run w gate).getD j false) = (is.all fun j => w.getD j false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true]
        exact ⟨fun h j hj => (hkeep j (hvalid j (List.mem_cons_of_mem i hj))).symm.trans (h j hj),
          fun h j hj => (hkeep j (hvalid j (List.mem_cons_of_mem i hj))).trans (h j hj)⟩
      rw [List.foldl_cons, hev (run w gate) (by simp [run, hw]), hnew, htail, List.all_cons]
      exact Bool.and_assoc _ _ _

end PEqualNP.Outside.L_meta_066_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_066_aux in
theorem PEqualNP.Outside.L_meta_066 :
    ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool) (u : Fin n → Bool),
      1 ≤ (Finset.univ.filter fun i : Fin n => u i = true).card →
      PEqualNP.MetaComplexity.HasCircuitSize n f s →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x : Fin n → Bool => f x || decide (∀ i : Fin n, u i = true → x i = true))
        (s + (Finset.univ.filter fun i : Fin n => u i = true).card) := by
  classical
  intro n s f u hnonempty hsize
  obtain ⟨C, hfan, hbudget, hvalue⟩ := hsize
  let selected := (Finset.univ : Finset (Fin n)).filter fun i => u i = true
  let marks := selected.toList
  have hn : marks.length = selected.card := by simp [marks]
  obtain ⟨first, tail, hmarks⟩ : ∃ i tail, marks = i :: tail := by
    cases he : marks with
    | nil =>
      rw [he, List.length_nil] at hn
      exact (Nat.not_le_of_lt (show selected.card < 1 by omega) hnonempty).elim
    | cons i tail => exact ⟨i, tail, rfl⟩
  let start := n + C.gates.length
  obtain ⟨gs, o, hgs, hlen, ho, heval⟩ := append_and_chain (tail.map Fin.val)
    start first.val (by have := first.isLt; dsimp [start]; omega) (fun j hj => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
      exact i.isLt.trans_le (Nat.le_add_right _ _))
  let next := start + gs.length
  let old := if C.output < start then C.output else next + 1
  let last : Gate := ⟨GateOp.or, [old, o]⟩
  refine ⟨⟨C.gates ++ gs ++ [last], next⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact (List.mem_append.mp hg).elim (hfan g) (hgs g)
    · have he := List.mem_singleton.mp hg
      subst g
      simp [last]
  · have hC : C.gates.length ≤ s := hbudget
    change (C.gates ++ gs ++ [last]).length ≤ s + selected.card
    rw [hmarks] at hn
    simp only [List.length_append, List.length_cons, List.length_nil, hlen, List.length_map] at *
    omega
  · intro x
    let w := C.wires (List.ofFn x)
    let v := gs.foldl run w
    have hW : w.length = start := by
      change (C.gates.foldl run (List.ofFn x)).length = _
      rw [run_length]
      simp [start]
    have hV : v.length = next := by rw [run_length, hW]
    have hInput (i : Fin n) : w.getD i.val false = x i := by
      change (C.gates.foldl run (List.ofFn x)).getD i.val false = _
      rw [run_keeps _ _ _ (by simp)]
      simp
    have hAnd : v.getD o false = decide (∀ i : Fin n, u i = true → x i = true) := by
      rw [heval w hW]
      have hAll : marks.all x = (w.getD first.val false && (tail.map Fin.val).all fun j => w.getD j false) := by
        rw [hmarks, List.all_cons, hInput, List.all_map]
        congr 1
        exact List.all_congr rfl (fun i => (hInput i).symm)
      rw [← hAll]
      apply Bool.eq_iff_iff.mpr
      simp only [marks, selected, List.all_eq_true, Finset.mem_toList, Finset.mem_filter,
        Finset.mem_univ, true_and, decide_eq_true_eq]
    have hOld : v.getD old false = f x := by
      have hOriginal : w.getD C.output false = f x := hvalue x
      by_cases ho : C.output < start
      · have hold : old = C.output := by simp [old, ho]
        rw [hold, run_keeps _ _ _ (hW.symm ▸ ho)]
        exact hOriginal
      · have hold : old = next + 1 := by simp [old, ho]
        rw [hold, List.getD_eq_default _ _ (by omega)]
        rw [List.getD_eq_default _ _ (by omega)] at hOriginal
        exact hOriginal
    change ((C.gates ++ gs ++ [last]).foldl run (List.ofFn x)).getD next false = _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (run v last).getD next false = _
    have hLast : (run v last).getD v.length false = (v.getD old false || v.getD o false) := by
      simp [run, last, GateOp.eval]
    rw [← hV, hLast, hAnd, hOld]
