module

public import Linglib.Syntax.WordOrder

/-!
# Agreement with conjoined noun phrases

A target whose controller consists of conjoined noun phrases agrees with one of them or with all
of them. This file defines the three options, `Agreement.ConjunctAgreement`, and for each the
conjuncts whose features it gives the target access to: for the conjuncts `cs` in linear order and
a target on side `d` of them, `a.conjuncts d cs` is `(d.nearest cs).toList` for agreement with the
nearest conjunct, `cs.take 1` for agreement with the first, and `cs` for agreement with all. A
head that checks its selectional features against coordinated arguments has the same options.

The conjuncts an option selects stand together in the coordination
(`Agreement.ConjunctAgreement.conjuncts_infix`) and are selected by their position alone, so
selection commutes with any reading of the conjuncts
(`Agreement.ConjunctAgreement.conjuncts_map`). Two options select the same conjuncts of every
coordination exactly when they are the same option, or the target precedes the conjuncts and
each is agreement with one conjunct, the nearest then being the first
(`Agreement.ConjunctAgreement.conjuncts_eq_conjuncts_iff`). Agreement with the nearest conjunct
and agreement with all are their own mirror images, a target after the reversed coordination
selecting what a target before the coordination does, and agreement with the first is not
(`Agreement.ConjunctAgreement.revConj_conjuncts_swap_iff`): its mirror image, agreement with the
last conjunct alone, arises only as agreement with the nearest by a target that follows the
conjuncts (`Agreement.ConjunctAgreement.conjuncts_concat_eq_singleton_iff`).

## Implementation notes

* The side of the conjuncts the target is on is a `HeadDirection`, the target counting as the
  head, so a verb before its conjoined subject is head-initial.
* An option says which conjuncts the target accesses, not how its values are computed from
  theirs: agreement with one conjunct takes that conjunct's values, agreement with all resolves
  them (`Agreement.ResolutionRule`).
* The first conjunct is first in linear order; whether an analysis picks it for its position or
  as the structurally highest conjunct is left to the analysis.

## References

* [corbett-2000]
* [corbett-1991]
* [bruening-alkhalaf-2020]
-/

@[expose] public section

namespace Agreement

/-- A target agrees with conjoined noun phrases by agreeing with one conjunct, the nearest or the
first, or with all of them. -/
inductive ConjunctAgreement where
  /-- Agreement with the nearest conjunct. -/
  | nearest
  /-- Agreement with the first conjunct, the more distant one when the target follows them. -/
  | first
  /-- Agreement with all conjuncts, by resolution. -/
  | all
  deriving DecidableEq, Fintype, Repr

namespace ConjunctAgreement

variable {α β : Type*} {a b : ConjunctAgreement} {d : HeadDirection} {cs l : List α} {x : α}

/-- `a.conjuncts d cs` lists the conjuncts, of the conjuncts `cs` in linear order, whose features
a target on side `d` of them accesses when it agrees by the option `a`. -/
def conjuncts : ConjunctAgreement → HeadDirection → List α → List α
  | nearest, d, cs => (d.nearest cs).toList
  | first, _, cs => cs.take 1
  | all, _, cs => cs

@[simp] theorem conjuncts_nearest : nearest.conjuncts d cs = (d.nearest cs).toList := rfl

@[simp] theorem conjuncts_first : first.conjuncts d cs = cs.take 1 := rfl

@[simp] theorem conjuncts_all : all.conjuncts d cs = cs := rfl

theorem conjuncts_first_prefix (d : HeadDirection) (cs : List α) : first.conjuncts d cs <+: cs :=
  List.take_prefix 1 cs

/-- The conjuncts an option selects stand together in the coordination. -/
theorem conjuncts_infix (a : ConjunctAgreement) (d : HeadDirection) (cs : List α) :
    a.conjuncts d cs <:+: cs := by
  cases a
  exacts [d.toList_nearest_infix cs, (List.take_prefix 1 cs).isInfix, List.infix_rfl]

/-- An option selects conjuncts by their position, so selecting commutes with reading each
conjunct through `f`. -/
theorem conjuncts_map (f : α → β) (a : ConjunctAgreement) (d : HeadDirection) (cs : List α) :
    a.conjuncts d (cs.map f) = (a.conjuncts d cs).map f := by
  cases a
  · rw [conjuncts_nearest, conjuncts_nearest, HeadDirection.nearest_map]
    cases d.nearest cs <;> rfl
  · simp [List.map_take]
  · rfl

theorem conjuncts_nearest_headInitial (d : HeadDirection) (cs : List α) :
    nearest.conjuncts .headInitial cs = first.conjuncts d cs := by
  simp [List.take_one]

/-- Two options select the same conjuncts of every coordination exactly when they are the same
option, or the target precedes the conjuncts and each is agreement with one conjunct. -/
theorem conjuncts_eq_conjuncts_iff [Nontrivial α] :
    a.conjuncts d = b.conjuncts (α := α) d ↔ a = b ∨ d = .headInitial ∧ a ≠ all ∧ b ≠ all := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne α
    have := congrFun h [x, y]
    cases a <;> cases b <;> cases d <;> simp_all [eq_comm]
  · rintro (rfl | ⟨rfl, ha, hb⟩)
    · rfl
    · funext cs
      cases a <;> cases b <;> simp_all [List.take_one]

/-- Only a target that follows the conjuncts tells agreement with the nearest from agreement with
the first. -/
theorem conjuncts_nearest_eq_first_iff [Nontrivial α] :
    nearest.conjuncts d = first.conjuncts (α := α) d ↔ d = .headInitial := by
  simp [conjuncts_eq_conjuncts_iff]

/-- Agreement with the nearest conjunct and agreement with all are their own mirror images, and
agreement with the first is not. -/
theorem revConj_conjuncts_swap_iff [Nontrivial α] :
    List.revConj (a.conjuncts d.swap) = a.conjuncts (α := α) d ↔ a ≠ first := by
  refine ⟨?_, fun h ↦ funext fun cs ↦ ?_⟩
  · rintro h rfl
    obtain ⟨x, y, hxy⟩ := exists_pair_ne α
    simpa [List.revConj, hxy.symm] using congrFun h [x, y]
  · cases a
    · rw [List.revConj, conjuncts_nearest, HeadDirection.nearest_swap_reverse, conjuncts_nearest]
      cases d.nearest cs <;> rfl
    · exact absurd rfl h
    · simp [List.revConj]

/-- Agreement with the last conjunct alone is agreement with the nearest by a target that follows
the conjuncts, so there is no agreement with the last when it is the more distant. -/
theorem conjuncts_concat_eq_singleton_iff (hl : l ≠ []) (hx : x ∉ l) :
    a.conjuncts d (l ++ [x]) = [x] ↔ a = nearest ∧ d = .headFinal := by
  obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  have hy : y ≠ x := fun h ↦ hx (h ▸ List.mem_cons_self)
  cases a <;> cases d <;> simp [hy, List.getLast?_cons]

end ConjunctAgreement

end Agreement
