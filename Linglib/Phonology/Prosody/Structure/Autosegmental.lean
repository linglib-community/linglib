/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TierTree.Basic
public import Linglib.Phonology.Prosody.Structure
public import Mathlib.Data.Fintype.Sigma

/-!
# The prosodic structure of an autosegmental representation

A representation along a tree of tiers denotes a prosodic structure, `AR.toStructure`: its nodes
are the positions of the representation, a position dominates the positions that descending
lines lead to, `AR.Dom`, and one position precedes another when both stand on one tier and the
first is earlier. Positions on different tiers stand in no precedence.

The tokens a slot dominates in `AR.Dominates` are those below it in the structure
(`dominates_iff_dom`). No Crossing of the structure gives the No-Crossing Constraint between each
tier and the tier it hangs from (`isNonCrossing_lines_of_noCrossing_toStructure`).

## Implementation notes

The structure reads a line as domination, which is transitive, where the reading of a line as
overlap in time is not. No Crossing of the structure is therefore the stronger condition: it
compares what two nodes dominate through any number of lines, and the No-Crossing Constraint
compares two lines between the same two tiers. A phonological frame of [bird-blackburn-1991]
has both relations at once, the transitive closure of dominance contained in overlap.

## References

* [sagey-1988]
* [bird-klein-1990]
* [bird-blackburn-1991]
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] (T : ParentTree ι) (X : AR τ)

/-- The prosodic structure of a representation along a tree of tiers. -/
def toStructure : Prosody.Structure (Σ i, τ i) where
  Node := X.Pos
  dominance :=
    { le := fun v w ↦ X.Dom T (v.1, v.2) (w.1, w.2)
      le_refl := fun _ ↦ .refl
      le_trans := fun _ _ _ ↦ .trans
      le_antisymm := fun v w hvw hwv ↦ by
        have key : ∀ {v w : X.Pos}, ((v.1, (v.2 : ℕ)) : ι × ℕ) = (w.1, (w.2 : ℕ)) → v = w := by
          rintro ⟨i, p⟩ ⟨j, q⟩ h
          obtain ⟨rfl, hpq⟩ := Prod.mk.inj h
          exact congrArg _ (Fin.ext hpq)
        rcases hvw.eq_or_depth_lt with h | h
        · exact key h
        · rcases hwv.eq_or_depth_lt with h' | h'
          · exact (key h').symm
          · simp only at h h'
            omega }
  Precedes := fun v w ↦ v.1 = w.1 ∧ (v.2 : ℕ) < w.2
  label := fun v ↦ ⟨v.1, X.label v⟩

variable {T X}

instance : DecidableLE (X.toStructure T).Node := fun v w ↦
  inferInstanceAs (Decidable (X.Dom T (v.1, v.2) (w.1, w.2)))

instance : DecidableLT (X.toStructure T).Node := decidableLTOfDecidableLE

instance : DecidableRel (X.toStructure T).Precedes := fun v w ↦
  inferInstanceAs (Decidable (v.1 = w.1 ∧ (v.2 : ℕ) < w.2))

instance : Fintype (X.toStructure T).Node := inferInstanceAs (Fintype X.Pos)

instance : Decidable (X.toStructure T).NoCrossing :=
  inferInstanceAs (Decidable (∀ a a' b b' : (X.toStructure T).Node,
    (X.toStructure T).Precedes a a' → a < b → a' < b' → ¬ (X.toStructure T).Precedes b' b))

/-- No Crossing of the structure gives the No-Crossing Constraint between a tier and the tier it
hangs from. -/
theorem isNonCrossing_lines_of_noCrossing_toStructure (h : (X.toStructure T).NoCrossing) {j : ι}
    (hj : j ≠ T.root) : IsNonCrossing (X.lines (T.parent j) j : SetRel ℕ ℕ) :=
  isNonCrossing_lines_iff.2 fun p q p' q' h₁ h₂ hlt ↦ by
    by_contra! hgt
    have hne : T.parent j ≠ j := fun he ↦ hj (T.eq_root_of_iterate_eq (n := 1) one_ne_zero he)
    have lt : ∀ {p q : ℕ} (hl : X.Link (T.parent j) j p q),
        @LT.lt (X.toStructure T).Node _ ⟨T.parent j, ⟨p, hl.lt_left⟩⟩ ⟨j, ⟨q, hl.lt_right⟩⟩ :=
      fun hl ↦ @lt_of_le_of_ne (X.toStructure T).Node _ _ _
        (Relation.ReflTransGen.single (mem_children.2 ⟨rfl, hj, hl⟩))
        fun he ↦ hne (congrArg Sigma.fst he)
    exact h (a := ⟨_, ⟨p, h₁.lt_left⟩⟩) (a' := ⟨_, ⟨p', h₂.lt_left⟩⟩) ⟨rfl, hlt⟩ (lt h₁) (lt h₂)
      ⟨rfl, hgt⟩

end Autosegmental.AR
