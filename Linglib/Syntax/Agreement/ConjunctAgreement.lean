module

public import Linglib.Syntax.WordOrder

/-!
# Agreement with conjoined noun phrases

A target whose controller consists of conjoined noun phrases agrees with one of them or with all
of them. This file defines the options, `Agreement.ConjunctAgreement`: agreement with the conjunct
at an edge `e` of the coordination, `one e`, and agreement with all conjuncts, `all`. For the
conjuncts `cs` in linear order, `a.conjuncts cs` lists the conjuncts whose features the option `a`
gives the target access to, `e.takeAt 1 cs` for `one e` and `cs` for `all`. Agreement with the
first conjunct is `one .left`, agreement with the last is `one .right`, and agreement with the
conjunct nearest a target on side `d` of the conjuncts is `one d.headEdge`, which is agreement
with the first when the target precedes them. A head that checks its selectional features against
coordinated arguments has the same options.

The conjuncts an option selects stand together in the coordination
(`Agreement.ConjunctAgreement.conjuncts_infix`) and are selected by their position alone, so
selection commutes with any reading of the conjuncts
(`Agreement.ConjunctAgreement.conjuncts_map`), and distinct options select different conjuncts of
some coordination (`Agreement.ConjunctAgreement.conjuncts_injective`). The mirror image of an
option, `Agreement.ConjunctAgreement.swap`, selects from the reversed coordination what the option
selects (`Agreement.ConjunctAgreement.revConj_conjuncts`).

A target agrees with the nearest conjunct, with the first, or with all, and not with the last
when it is the more distant: `a.Attested d` holds of these options for a target on side `d`, that
is, of every option but agreement with the last conjunct by a target that precedes the conjuncts
(`Agreement.ConjunctAgreement.attested_iff`). The mirror image of such an option is one too,
except for agreement with the first conjunct by a target that follows
(`Agreement.ConjunctAgreement.attested_swap_swap_iff`).

## Implementation notes

* The side of the conjuncts the target is on is a `HeadDirection`, the target counting as the
  head, so a verb before its conjoined subject is head-initial.
* An option says which conjuncts the target accesses, not how its values are computed from
  theirs: agreement with one conjunct takes that conjunct's values, agreement with all resolves
  them (`Agreement.ResolutionRule`).
* The first conjunct is first in linear order; whether an analysis picks it for its position or
  as the structurally highest conjunct is left to the analysis.
* Agreement with the last conjunct is an option whether or not the target follows the conjuncts,
  so that the options are closed under mirror image and the restriction to the nearest and the
  first is a predicate on them, `Agreement.ConjunctAgreement.Attested`.

## References

* [corbett-2000]
* [corbett-1991]
* [bruening-alkhalaf-2020]
-/

@[expose] public section

namespace Agreement

/-- A target agrees with conjoined noun phrases by agreeing with one conjunct, the first or the
last, or with all of them. -/
inductive ConjunctAgreement where
  /-- Agreement with the conjunct at the edge `e` of the coordination. -/
  | one (e : Edge)
  /-- Agreement with all conjuncts, by resolution. -/
  | all
  deriving DecidableEq, Fintype, Repr

namespace ConjunctAgreement

variable {α β : Type*} {a : ConjunctAgreement} {d : HeadDirection} {e : Edge} {cs l : List α}
  {x : α}

/-- Agreement with the first conjunct. -/
def first : ConjunctAgreement := one .left

/-- Agreement with the last conjunct. -/
def last : ConjunctAgreement := one .right

/-- Agreement with the conjunct nearest a target on side `d` of the conjuncts. -/
def nearest (d : HeadDirection) : ConjunctAgreement := one d.headEdge

@[simp] theorem nearest_headInitial : nearest .headInitial = first := rfl

@[simp] theorem nearest_headFinal : nearest .headFinal = last := rfl

/-- The mirror image of an option exchanges the first conjunct and the last. -/
def swap : ConjunctAgreement → ConjunctAgreement
  | one e => one e.swap
  | all => all

@[simp] theorem swap_one : (one e).swap = one e.swap := rfl

@[simp] theorem swap_all : all.swap = all := rfl

@[simp] theorem swap_first : first.swap = last := rfl

@[simp] theorem swap_last : last.swap = first := rfl

@[simp] theorem swap_nearest (d : HeadDirection) : (nearest d).swap = nearest d.swap := by
  simp [nearest]

@[simp] theorem swap_swap : ∀ a : ConjunctAgreement, a.swap.swap = a := by decide

theorem swap_involutive : Function.Involutive swap := swap_swap

/-! ### The conjuncts an option selects -/

/-- `a.conjuncts cs` lists the conjuncts, of the conjuncts `cs` in linear order, whose features a
target accesses when it agrees by the option `a`. -/
def conjuncts : ConjunctAgreement → List α → List α
  | one e, cs => e.takeAt 1 cs
  | all, cs => cs

@[simp] theorem conjuncts_one : (one e).conjuncts cs = e.takeAt 1 cs := rfl

@[simp] theorem conjuncts_all : all.conjuncts cs = cs := rfl

@[simp] theorem conjuncts_first : first.conjuncts cs = cs.take 1 := rfl

@[simp] theorem conjuncts_last : last.conjuncts cs = cs.rtake 1 := rfl

@[simp] theorem conjuncts_nearest : (nearest d).conjuncts cs = d.headEdge.takeAt 1 cs := rfl

theorem mem_conjuncts_one : x ∈ (one e).conjuncts cs ↔ x ∈ e.head? cs := by
  rw [conjuncts_one, ← Edge.toList_head?, Option.mem_toList, Option.mem_def]

/-- The conjuncts an option selects stand together in the coordination. -/
theorem conjuncts_infix (a : ConjunctAgreement) (cs : List α) : a.conjuncts cs <:+: cs := by
  cases a
  exacts [Edge.takeAt_infix .., List.infix_rfl]

/-- An option selects conjuncts by their position, so selecting commutes with reading each
conjunct through `f`. -/
theorem conjuncts_map (f : α → β) (a : ConjunctAgreement) (cs : List α) :
    a.conjuncts (cs.map f) = (a.conjuncts cs).map f := by
  cases a
  exacts [Edge.takeAt_map .., rfl]

/-- Distinct options select different conjuncts of some coordination. -/
theorem conjuncts_injective [Nontrivial α] :
    Function.Injective (conjuncts (α := α)) := fun a b h ↦ by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  have := congrFun h [x, y]
  rcases a with (_ | _) | _ <;> rcases b with (_ | _) | _ <;> simp_all [List.rtake]

/-- The mirror image of an option selects from the reversed coordination what the option
selects. -/
theorem revConj_conjuncts (a : ConjunctAgreement) :
    List.revConj a.conjuncts = a.swap.conjuncts (α := α) := by
  funext cs
  cases a <;> simp [List.revConj, Edge.takeAt_reverse]

/-- Only agreement with the last conjunct selects the last of several conjuncts alone. -/
theorem conjuncts_concat_eq_singleton_iff (hl : l ≠ []) (hx : x ∉ l) :
    a.conjuncts (l ++ [x]) = [x] ↔ a = last := by
  obtain ⟨y, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  have hy : y ≠ x := fun h ↦ hx (h ▸ List.mem_cons_self)
  rcases a with (_ | _) | _ <;> simp [hy, last, List.rtake_eq_reverse_take_reverse]

/-! ### The options found -/

/-- `a.Attested d` holds of the options [corbett-2000] reports for a target on side `d` of the
conjuncts: agreement with the nearest conjunct, with the first, and with all. -/
def Attested (d : HeadDirection) : ConjunctAgreement → Prop
  | one e => e = d.headEdge ∨ e = .left
  | all => True

instance : ∀ a, Decidable (Attested d a)
  | one _ => inferInstanceAs (Decidable (_ ∨ _))
  | all => inferInstanceAs (Decidable True)

@[simp] theorem attested_nearest (d : HeadDirection) : (nearest d).Attested d := .inl rfl

@[simp] theorem attested_first (d : HeadDirection) : first.Attested d := .inr rfl

@[simp] theorem attested_all (d : HeadDirection) : all.Attested d := trivial

/-- The options found are all but agreement with the last conjunct by a target that precedes the
conjuncts, to which it is the more distant. -/
theorem attested_iff : a.Attested d ↔ (a = last → d = .headFinal) := by
  revert a d; decide

@[simp] theorem attested_last_iff : last.Attested d ↔ d = .headFinal := by
  simp [attested_iff]

/-- The mirror image of an option is among the options found for a target on the other side,
except for agreement with the first conjunct by a target that follows the conjuncts. -/
theorem attested_swap_swap_iff : a.swap.Attested d.swap ↔ (a = first → d = .headInitial) := by
  revert a d; decide

end ConjunctAgreement

end Agreement
