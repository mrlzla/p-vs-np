module

public import MCSPStopMatching

/-! The original minimum circuit bounds early bypass aliases by the gates
whose functions change under the forest pins. -/

@[expose] public section

namespace PvsNP.Frontier.MinimumAliases

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open ForestPinning SuperTwoN MonotoneForest
open RestrictionCharges FreshCharges StopMatching

variable {n g : ℕ}

theorem minimum_no_original_alias (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f)) (j : Fin c.size) :
    ¬ ((∃ i : Fin n, restrictedWire c.program Sum.inl (.gate j) = projection i) ∨
      ∃ t : Fin c.size, t < j ∧ restrictedWire c.program Sum.inl (.gate j) =
        restrictedWire c.program Sum.inl (.gate t)) := by
  intro h
  have hSize := original_alias_complexity_le c.program (c.outputs 0) j h
  rw [NestedFaces.restricted_circuit_eq c hc Sum.inl] at hSize
  change complexity interpretation (single f) ≤ c.size - 1 at hSize
  rw [← hMin] at hSize
  have hj := j.isLt
  omega

theorem minimum_original_gate_injective (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f)) :
    Function.Injective (fun j : Fin c.size => restrictedWire c.program Sum.inl (.gate j)) := by
  intro j t he
  rcases lt_trichotomy j t with hlt | rfl | hgt
  · exact (minimum_no_original_alias c hc hMin t (Or.inr ⟨j, hlt, he.symm⟩)).elim
  · rfl
  · exact (minimum_no_original_alias c hc hMin j (Or.inr ⟨t, hgt, he⟩)).elim

/-- Gates whose Boolean functions change when the indicated forest values
are fixed. A gate outside this set is unchanged as a function on all inputs. -/
noncomputable def changedGates (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) : Finset (Fin g) := open scoped Classical in
  Finset.univ.filter fun j =>
    restrictedWire p (pinAt x P) (.gate j) ≠ restrictedWire p Sum.inl (.gate j)

private theorem unchanged_eq {p : Program signature n g} {x : BitString n}
    {P : Finset (Fin n)} {j : Fin g} (h : j ∉ changedGates p x P) :
    restrictedWire p (pinAt x P) (.gate j) = restrictedWire p Sum.inl (.gate j) := by
  classical
  by_contra hne
  exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)

/-- An unchanged nonconstant alias has a fresh restricted representative.
That representative changed under the forest pins, since original gate
functions of a minimum circuit are distinct. -/
private theorem unchanged_alias_representative (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (x : BitString n) (P : Finset (Fin n)) (j : Fin c.size)
    (hChanged : j ∉ changedGates c.program x P)
    (hVar : j ∈ surviving c.program (pinAt x P))
    (hOld : j ∉ fresh c.program (pinAt x P)) :
    ∃ t ∈ fresh c.program (pinAt x P), t ∈ changedGates c.program x P ∧
      restrictedWire c.program (pinAt x P) (.gate t) =
        restrictedWire c.program (pinAt x P) (.gate j) := by
  classical
  let trace (u : Fin c.size) := restrictedWire c.program (pinAt x P) (.gate u)
  have hneConst (b : Bool) : trace j ≠ (fun _ => b) := by
    intro h
    obtain ⟨y, z, hne⟩ := (Finset.mem_filter.mp hVar).2
    exact hne ((congrFun h y).trans (congrFun h z).symm)
  have hneProj (i : Fin n) : trace j ≠ projection i := by
    intro h
    exact minimum_no_original_alias c hc hMin j
      (Or.inl ⟨i, (unchanged_eq hChanged).symm.trans h⟩)
  have hDisclosed : disclosed c.program (pinAt x P) j := by
    by_contra h
    exact hOld (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨u, hu, he⟩ : ∃ u : Fin c.size, u < j ∧ trace j = trace u := by
    rcases hDisclosed with ⟨b, hb⟩ | ⟨i, hi⟩ | h
    · exact (hneConst b hb).elim
    · exact (hneProj i hi).elim
    · exact h
  let candidates := (Finset.univ : Finset (Fin c.size)).filter fun t => trace t = trace j
  have huCand : u ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm⟩
  have hNonempty : candidates.Nonempty := ⟨u, huCand⟩
  let t := candidates.min' hNonempty
  have htEq : trace t = trace j :=
    (Finset.mem_filter.mp (Finset.min'_mem candidates hNonempty)).2
  have ht : t < j := (Finset.min'_le candidates u huCand).trans_lt hu
  have htFresh : t ∈ fresh c.program (pinAt x P) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rintro (⟨b, hb⟩ | ⟨i, hi⟩ | ⟨k, hkt, hk⟩)
    · exact hneConst b (htEq.symm.trans hb)
    · exact hneProj i (htEq.symm.trans hi)
    · have hkCand : k ∈ candidates :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.symm.trans htEq⟩
      exact (not_lt_of_ge (Finset.min'_le candidates k hkCand)) hkt
  have htChanged : t ∈ changedGates c.program x P := by
    by_contra h
    have hg := (unchanged_eq h).symm.trans (htEq.trans (unchanged_eq hChanged))
    exact (ne_of_lt ht) (minimum_original_gate_injective c hc hMin hg)
  exact ⟨t, htFresh, htChanged, htEq⟩

/-- Charge a changed bypass alias to itself. Charge an unchanged one to its
changed, fresh representative. The two kinds of charges have disjoint images,
and distinct unchanged gates have distinct representatives. -/
theorem minimum_early_readers_injection (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (x : BitString n) (P J : Finset (Fin n)) :
    let C := changedGates c.program x P
    let F := fresh c.program (pinAt x P)
    let H := StopGate c.program (c.outputs 0)
    ∃ charge : earlyReaders c.program (c.outputs 0) x P J → Fin c.size,
      Function.Injective charge ∧ ∀ j,
        charge j ∈ ((H ∩ C) \ F) ∪ (C ∩ F) := by
  classical
  dsimp only
  let p := c.program
  let root := c.outputs 0
  let C := changedGates p x P
  let F := fresh p (pinAt x P)
  let A := earlyReaders p root x P J
  have hA (j : A) : j.val ∈ StopGate p root ∧
      j.val ∈ surviving p (pinAt x P) ∧ j.val ∉ F := by
    obtain ⟨hBefore, hOld⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp j.property).1
    exact ⟨(Finset.mem_inter.mp hBefore).1, (Finset.mem_inter.mp hBefore).2, hOld⟩
  have hRep (j : A) (hj : j.val ∉ C) : ∃ t ∈ F, t ∈ C ∧
      restrictedWire p (pinAt x P) (.gate t) = restrictedWire p (pinAt x P) (.gate j.val) :=
    unchanged_alias_representative c hc hMin x P j.val hj (hA j).2.1 (hA j).2.2
  let charge (j : A) : Fin c.size := if hj : j.val ∈ C then j.val else (hRep j hj).choose
  have own (j : A) (hj : j.val ∈ C) : charge j = j.val := dite_eq_left hj
  have other (j : A) (hj : j.val ∉ C) : charge j ∈ F ∧ charge j ∈ C ∧
      restrictedWire p (pinAt x P) (.gate (charge j)) =
        restrictedWire p (pinAt x P) (.gate j.val) := by
    simpa only [charge, hj, dite_false] using (hRep j hj).choose_spec
  refine ⟨charge, ?_, ?_⟩
  · intro j t he
    by_cases hj : j.val ∈ C <;> by_cases ht : t.val ∈ C
    · exact Subtype.ext ((own j hj).symm.trans (he.trans (own t ht)))
    · exact ((hA j).2.2 ((he.symm.trans (own j hj)) ▸ (other t ht).1)).elim
    · exact ((hA t).2.2 ((he.trans (own t ht)) ▸ (other j hj).1)).elim
    · have hg := (other j hj).2.2.symm.trans (he ▸ (other t ht).2.2)
      have hBase := (unchanged_eq hj).symm.trans (hg.trans (unchanged_eq ht))
      exact Subtype.ext (minimum_original_gate_injective c hc hMin hBase)
  · intro j
    by_cases hj : j.val ∈ C
    · exact Finset.mem_union_left _ ((own j hj).symm ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨(hA j).1, hj⟩, (hA j).2.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨(other j hj).2.1, (other j hj).1⟩)

theorem minimum_early_readers_card_le (c : Circuit signature n 1)
    {f : BooleanFunction n} (hc : c.Computes interpretation (single f))
    (hMin : c.size = complexity interpretation (single f))
    (x : BitString n) (P J : Finset (Fin n)) :
    (earlyReaders c.program (c.outputs 0) x P J).card ≤ (changedGates c.program x P).card := by
  classical
  obtain ⟨charge, hInj, hMem⟩ := minimum_early_readers_injection c hc hMin x P J
  let into (j : earlyReaders c.program (c.outputs 0) x P J) :
      changedGates c.program x P := ⟨charge j, by
    rcases Finset.mem_union.mp (hMem j) with hOwn | hOther
    · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hOwn).1).2
    · exact (Finset.mem_inter.mp hOther).1⟩
  have hi : Function.Injective into := fun _ _ he => hInj (congrArg Subtype.val he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective into hi

/-- The support of a changed gate intersects the pinned coordinates. This
gives a syntactic upper bound on the semantic budget. -/
theorem changedGates_subset_support (p : Program signature n g) (x : BitString n)
    (P : Finset (Fin n)) :
    changedGates p x P ⊆ Finset.univ.filter (fun j => ¬ Disjoint (p.wireSupport (.gate j)) P) := by
  classical
  intro j hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hDisj
  apply (Finset.mem_filter.mp hj).2
  funext y
  apply p.trace_congr interpretation _ _ (.gate j)
  intro i hi
  have hNot : i ∉ P := fun h => Finset.disjoint_left.mp hDisj hi h
  simp [substitute, pinAt, hNot]

/-- If the fixed forest values change few original gates, minimality forces
additional fresh stop-gate losses beyond the distinct joint readers. -/
theorem minimum_mcsp_oriented_charge (m : ℕ) (hm : 7 ≤ m)
    (c : Circuit signature (2 ^ m) 1)
    (hc : c.Computes interpretation (single (mcspSquare m)))
    (hMin : c.size = complexity interpretation (single (mcspSquare m)))
    (a : BitString m) (b : Bool) (P J T : Finset (Fin (2 ^ m)))
    (hMask : IsForestMask c.program (c.outputs 0) (MCSP.truthTable m (affine a b)) P)
    (anchor : Fin (2 ^ m) → Fin (2 ^ m))
    (hFree : P.card + descriptionBitBound m + 1 < 2 ^ m)
    (hJ : Disjoint J P) (hT : Disjoint T P) (hTJ : Disjoint T J)
    (hAnchor : ∀ j ∈ J, anchor j ∈ T)
    (hJoint : ∀ j ∈ J, ∃ k ∈ StopGate c.program (c.outputs 0),
      k ∈ fresh c.program (pinAt (MCSP.truthTable m (affine a b)) P) ∧
      ((c.program.lines k).op = .and ∨ (c.program.lines k).op = .or) ∧
      Reads c.program k (anchor j) ∧ Reads c.program k j) :
    let x := MCSP.truthTable m (affine a b)
    let C := (changedGates c.program x P).card
    J.card + ((J.card - 2 * descriptionBitBound m * T.card + 1) / 2 - C) ≤
      (losses c.program (c.outputs 0) x P J).card := by
  have hA := minimum_early_readers_card_le c hc hMin (MCSP.truthTable m (affine a b)) P J
  have h := (mcsp_affine_oriented_charge m hm c hc a b P J T hMask anchor hFree
    hJ hT hTJ hAnchor hJoint).1
  exact (Nat.add_le_add_left (Nat.sub_le_sub_left hA _) _).trans h

#print axioms minimum_no_original_alias
#print axioms minimum_early_readers_card_le
#print axioms minimum_mcsp_oriented_charge

end PvsNP.Frontier.MinimumAliases
