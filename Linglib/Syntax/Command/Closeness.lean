/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Command.Basic
public import Linglib.Core.Order.Minimal
public import Mathlib.Order.Minimal

/-!
# Closeness

Of two nodes of a dominance order the closer is the one with fewer ancestors: under a generator
`P`, `a` is at least as close as `b` when `ancestors P a ⊆ ancestors P b`. Closeness is
[command without the generators above a node](##PhraseStructure.ancestors_subset_ancestors_iff):
where command relates a node to all it dominates in both directions or neither, closeness puts a
generator strictly before what it dominates. Between nodes neither of which dominates the other,
the closer [commands without being
commanded](##PhraseStructure.ancestors_ssubset_ancestors_iff_commands), and the equally close are
[the mates](##PhraseStructure.ancestors_eq_ancestors_iff). The closest nodes of a set are the
[goals](##PhraseStructure.minimalFor_ancestors_iff) of [chomsky-1995]'s Minimal Link Condition.

## References

* [barker-pullum-1990]
* [chomsky-1995]
-/

@[expose] public section

namespace PhraseStructure

open Order Set
open scoped SetRel

variable {α : Type*}

section Closeness

variable [PartialOrder α] {P : Set α} {a b x : α}

/-- A node is at least as close as another when it commands it and the other is not one of its
ancestors. -/
theorem ancestors_subset_ancestors_iff :
    ancestors P a ⊆ ancestors P b ↔ a ~[C[P]] b ∧ b ∉ ancestors P a :=
  ⟨fun h ↦ ⟨fun _ hx hxa ↦ (h ⟨hx, hxa⟩).2.le, fun hb ↦ lt_irrefl b (h hb).2⟩,
    fun ⟨h, hb⟩ _ hx ↦ ⟨hx.1, (h hx.1 hx.2).lt_of_ne fun e : _ = b ↦ hb (e ▸ hx)⟩⟩

/-- A node commands every node at most as close as it. -/
theorem mem_commandRelation_of_ancestors_subset (h : ancestors P a ⊆ ancestors P b) :
    a ~[C[P]] b :=
  (ancestors_subset_ancestors_iff.1 h).1

theorem ancestors_subset_ancestors_iff_of_not_lt (hba : ¬ b < a) :
    ancestors P a ⊆ ancestors P b ↔ a ~[C[P]] b :=
  ancestors_subset_ancestors_iff.trans (and_iff_left fun hb ↦ hba hb.2)

/-- A node is closer than the nodes it dominates through a generator. -/
theorem ancestors_ssubset_ancestors_of_le_of_lt (hax : a ≤ x) (hxb : x < b) (hx : x ∈ P) :
    ancestors P a ⊂ ancestors P b :=
  (ssubset_iff_of_subset (ancestors_subset_ancestors (hax.trans hxb.le))).2
    ⟨x, ⟨hx, hxb⟩, fun h ↦ lt_irrefl x (h.2.trans_le hax)⟩

/-- Between nodes neither of which properly dominates the other, strict closeness is asymmetric
command. -/
theorem ancestors_ssubset_ancestors_iff (hab : ¬ a < b) (hba : ¬ b < a) :
    ancestors P a ⊂ ancestors P b ↔ a ~[C[P]] b ∧ ¬ b ~[C[P]] a := by
  rw [ssubset_def, ancestors_subset_ancestors_iff_of_not_lt hba,
    ancestors_subset_ancestors_iff_of_not_lt hab]

/-- Between nodes neither of which properly dominates the other, the equally close are the
mates. -/
theorem ancestors_eq_ancestors_iff (hab : ¬ a < b) (hba : ¬ b < a) :
    ancestors P a = ancestors P b ↔ a ~[mateRelation P] b := by
  rw [Subset.antisymm_iff, ancestors_subset_ancestors_iff_of_not_lt hba,
    ancestors_subset_ancestors_iff_of_not_lt hab, mem_mateRelation]

/-- Between nodes neither of which dominates the other, the closer is the one that commands
without being commanded. -/
theorem ancestors_ssubset_ancestors_iff_commands (h : IncompRel (· ≤ ·) a b) :
    ancestors P a ⊂ ancestors P b ↔ Commands P a b ∧ ¬ Commands P b a := by
  simp only [ancestors_ssubset_ancestors_iff h.not_lt h.not_gt, commands_iff, h, h.symm,
    and_true]

/-- Among nodes none of which dominates another, the closest are those that no node of the set
commands without being commanded, the Minimal Link Condition. -/
theorem minimalFor_ancestors_iff {S : Set α} (hS : IsAntichain (· ≤ ·) S) :
    MinimalFor (· ∈ S) (ancestors P) a ↔
      a ∈ S ∧ ∀ ⦃b⦄, b ∈ S → ¬ (Commands P b a ∧ ¬ Commands P a b) :=
  minimalFor_iff_of_isAntichain hS (fun _ h ↦ h.2 h.1) fun _ _ ↦
    ancestors_ssubset_ancestors_iff_commands

end Closeness

end PhraseStructure
