module

public import Linglib.Syntax.WordOrder

/-!
# Agreement with conjoined noun phrases

A target whose controller consists of conjoined noun phrases agrees with one of them or with all
of them. Agreement with one conjunct is normally with the nearest, which is the first or the last
according to the side of the conjuncts the target stands on, and occasionally with the first when
it is the more distant; agreement with the last when it is the more distant is excluded. Agreement
with all conjuncts requires access to the features of every conjunct, from which resolution rules
compute the target's values (`Agreement.ResolutionRule`). A head that checks its selectional
features against coordinated arguments has the same options.

This file defines the three options by the conjuncts whose features each gives the target access
to, given the conjuncts in linear order and the side of them the target is on.

## Main definitions

* `Agreement.ConjunctAgreement`: agreement with the nearest conjunct, with the first, or with all.
* `Agreement.ConjunctAgreement.conjuncts`: the conjuncts an option gives the target access to.

## Main results

* `Agreement.ConjunctAgreement.conjuncts_nearest_eq_first_iff`: the nearest conjunct is the first
  for every coordination exactly when the target precedes the conjuncts.
* `Agreement.ConjunctAgreement.eq_nearest_of_conjuncts_eq_singleton`: a target agrees with the last
  of several conjuncts alone only by agreeing with the nearest, and only when it follows them.

## Implementation notes

* The side of the conjuncts the target is on is a `HeadDirection`, the target counting as the
  head, so a verb before its conjoined subject is head-initial.
* An option says which conjuncts the target accesses, not how its values are computed from
  theirs: agreement with one conjunct takes that conjunct's values, agreement with all resolves
  them.
* The first conjunct is first in linear order; whether an analysis picks it for its position or
  as the structurally highest conjunct is left to the analysis.

## References

* [corbett-2000] — §6.5.1, the options, pp. 195–198
* [corbett-1991] — resolution rules
* [bruening-alkhalaf-2020] — the options for a selector checking coordinated arguments
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

variable {α : Type*} {a : ConjunctAgreement} {d : HeadDirection} {cs l : List α} {x : α}

/-- `a.conjuncts d cs` lists the conjuncts, of the conjuncts `cs` in linear order, whose features
a target on side `d` of them accesses when it agrees by the option `a`. -/
def conjuncts : ConjunctAgreement → HeadDirection → List α → List α
  | nearest, d, cs => (d.nearest cs).toList
  | first, _, cs => cs.take 1
  | all, _, cs => cs

@[simp] theorem conjuncts_nearest : nearest.conjuncts d cs = (d.nearest cs).toList := rfl

@[simp] theorem conjuncts_first : first.conjuncts d cs = cs.take 1 := rfl

@[simp] theorem conjuncts_all : all.conjuncts d cs = cs := rfl

theorem conjuncts_sublist (a : ConjunctAgreement) (d : HeadDirection) (cs : List α) :
    (a.conjuncts d cs).Sublist cs := by
  cases a
  · cases d
    · simpa [← List.take_one] using List.take_sublist 1 cs
    · rcases List.eq_nil_or_concat cs with rfl | ⟨l, x, rfl⟩ <;> simp
  · exact List.take_sublist 1 cs
  · exact List.Sublist.refl cs

theorem conjuncts_nearest_headInitial (d : HeadDirection) (cs : List α) :
    nearest.conjuncts .headInitial cs = first.conjuncts d cs := by
  simp [List.take_one]

/-- The nearest conjunct is the first for every coordination exactly when the target precedes the
conjuncts, so only a target that follows them tells agreement with the nearest from agreement
with the first. -/
theorem conjuncts_nearest_eq_first_iff [Nontrivial α] :
    (∀ cs : List α, nearest.conjuncts d cs = first.conjuncts d cs) ↔ d = .headInitial := by
  refine ⟨fun h ↦ ?_, fun h cs ↦ h ▸ conjuncts_nearest_headInitial d cs⟩
  cases d with
  | headInitial => rfl
  | headFinal =>
    obtain ⟨x, y, hxy⟩ := exists_pair_ne α
    simpa [hxy.symm] using h [x, y]

theorem conjuncts_nearest_swap_reverse (d : HeadDirection) (cs : List α) :
    nearest.conjuncts d.swap cs.reverse = nearest.conjuncts d cs := by
  simp [HeadDirection.nearest_swap_reverse]

/-- Agreement with the last conjunct alone is agreement with the nearest by a target that follows
the conjuncts: agreement with the last when it is the more distant is excluded
([corbett-2000], p. 197). -/
theorem eq_nearest_of_conjuncts_eq_singleton (hl : l ≠ []) (hx : x ∉ l)
    (h : a.conjuncts d (l ++ [x]) = [x]) : a = nearest ∧ d = .headFinal := by
  obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases a <;> cases d <;> simp_all

end ConjunctAgreement

end Agreement
