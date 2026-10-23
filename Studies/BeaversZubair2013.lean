module

public import Linglib.Semantics.Aspect.Defs
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Sinhala.Verbs
public import Studies.KoontzGarboden2009
public import Linglib.Core.Order.Cover
public import Mathlib.Tactic.DeriveFintype

/-!
# Beavers and Zubair (2013): Anticausatives in Sinhala

Beavers and Zubair analyze the anticausatives of Colloquial Sinhala. A causative root has two
involitive detransitives, one with a nominative subject and no entailed external causer, and one
with an accusative subject and an entailed external causer. Causer suppression derives both: it
removes the causer from the verb's arguments, keeps the causation, and leaves the causer to be
identified with the patient, as in Chierchia's and Koontz-Garboden's reflexivization, or bound
existentially, as in Levin and Rappaport Hovav's analysis. A verb selects the sort of its causer,
and suppression applies only when that sort includes the individuals, so *minimarannə* 'murder'
and *kapannə* 'cut', which select events, have no inchoative.

## Main definitions

* `CauserSort`: the typology of causer sorts, ordered by inclusion of basic sorts.
* `causerSuppress`: causer suppression.
* `Reading.resolve`: the two resolutions of the suppressed causer.
* `caseOfReading`: the accusative marks existential resolution.
* `Anticausativizes`: the condition of causer suppression on a root.

## Main results

* `CauserSort.not_event_le_individual`: anticausatives are never volitive.
* `reflexive_resolve_eq_reflexivize`: reflexive resolution is Koontz-Garboden's reflexivization.
* `causative_entails_existential`: the inchoative is true whenever the causative is.
* `ibeem_incompatible_with_external`: *ibeemə* 'by itself' excludes the accusative variant.
* `anticausativizes_iff_alternates`: the roots that meet the condition are those with an
  inchoative.
* `exists_hasInvolitive_not_anticausativizes`: the involitive does not mark anticausatives.

## Implementation notes

Sorts are checked rather than denoted. `causerSuppress` takes a proof that the root's causer sort
includes the individuals in place of the conjunct `x ∈ U_I` of (77), and the volitive's sort
condition is `CauserSort.event ≤ s`. *kada-* 'break' selects the whole domain as in (76), which
revises the eventualities of (65a).

## References

* [J. Beavers and C. Zubair, *Anticausatives in Sinhala: Involitivity and causer suppression*
  (2013)][beavers-zubair-2013]
* [J. Beavers and C. Zubair, *The Interaction of Transitivity Features in the Sinhala
  Involitive* (2010)][beavers-zubair-2010]
* [A. Koontz-Garboden, *Anticausativization* (2009)][koontz-garboden-2009]
* [G. Chierchia, *A Semantics for Unaccusatives and its Syntactic Consequences*
  (2004)][chierchia-2004b]
* [B. Levin and M. Rappaport Hovav, *Unaccusativity: At the Syntax-Lexical Semantics Interface*
  (1995)][levin-hovav-1995]
-/

@[expose] public section

namespace BeaversZubair2013

/-! ### Sorts

The domain is sorted into individuals and eventualities, and the eventualities into events and
states (§4.3). A verb's causer ranges over one of the sorts of the typology (81). -/

/-- The basic sorts of the domain are the individuals and the eventualities of each dynamicity,
the events being the dynamic eventualities. -/
inductive BasicSort where
  | individual
  | eventuality (k : Aspect.Dynamicity)
  deriving DecidableEq

/-- A causer sort is a node of the typology (81). -/
inductive CauserSort where
  /-- `U_E` comprises the events, the causers that *murder* verbs select. -/
  | event
  /-- `U_S` comprises the states, which (81) assigns to *bloom* verbs and negligence readings. -/
  | state
  /-- `U_V` comprises the eventualities, the causers that *destroy* verbs select (80). -/
  | eventuality
  /-- `U_I` comprises the individuals, the subjects of anticausatives. -/
  | individual
  /-- `U` is the whole domain, the causers that transitive *break* verbs select (76). -/
  | any
  deriving DecidableEq, Fintype

namespace CauserSort

/-- `s.basicSorts` is the set of basic sorts that the causer sort `s` comprises. -/
def basicSorts : CauserSort → Finset BasicSort
  | event => {.eventuality .dynamic}
  | state => {.eventuality .stative}
  | eventuality => {.eventuality .dynamic, .eventuality .stative}
  | individual => {.individual}
  | any => {.individual, .eventuality .dynamic, .eventuality .stative}

theorem basicSorts_injective : Function.Injective basicSorts := by decide

/-- One causer sort lies below another when its basic sorts are among the other's. -/
instance : PartialOrder CauserSort := PartialOrder.lift basicSorts basicSorts_injective

instance : DecidableLE CauserSort := fun s t ↦
  inferInstanceAs (Decidable (s.basicSorts ⊆ t.basicSorts))

instance : DecidableLT CauserSort := decidableLTOfDecidableLE

/-- The typology (81) is a tree whose leaves are the events, the states and the individuals. -/
theorem covBy_tree :
    event ⋖ eventuality ∧ state ⋖ eventuality ∧ eventuality ⋖ any ∧ individual ⋖ any := by
  decide

/-- Causer suppression (77) applies to the roots whose causer sort includes the individuals,
those that select the individuals or the whole domain. -/
theorem individual_le_iff {s : CauserSort} : individual ≤ s ↔ s = individual ∨ s = any := by
  cases s <;> decide

/-- The volitive (71) applies to a predicate whose subject sort includes the events. These are
the sorts of *murder*, *destroy* and *break* verbs, the three kinds of causative of §7.3. -/
theorem event_le_iff {s : CauserSort} :
    event ≤ s ↔ s = event ∨ s = eventuality ∨ s = any := by
  cases s <;> decide

/-- An individual subject cannot be resolved to an event, so an anticausative, whose subject is
an individual, has no volitive (§7.3). -/
theorem not_event_le_individual : ¬ event ≤ individual := by decide

end CauserSort

/-! ### Causer suppression -/

/-- Causer suppression (77) saturates the causer argument of `vp` with the open variable `z`.
It is defined only for a root whose causer sort includes the individuals. -/
def causerSuppress {E α : Type} (s : CauserSort) (_h : CauserSort.individual ≤ s) (z : E)
    (vp : E → α) : α :=
  vp z

/-! ### The two resolutions of the suppressed causer -/

/-- An anticausativized verb has two readings (78), on which the suppressed causer is coindexed
with the patient or existentially closed. -/
inductive Reading where
  | reflexive
  | existential
  deriving DecidableEq, Repr

/-- A reading's denotation binds the open causer that `causerSuppress` leaves to the patient
under reflexive resolution and closes it under existential resolution. The verb takes its causer
first, so `vp x y` has causer `x` and patient `y`. -/
def Reading.resolve {E : Type} {s : CauserSort} (r : Reading)
    (h : CauserSort.individual ≤ s) (vp : E → E → Prop) : E → Prop :=
  match r with
  | .reflexive   => fun y ↦ causerSuppress s h y vp y
  | .existential => fun y ↦ ∃ x, causerSuppress s h x vp y

/-- Reflexive resolution is Koontz-Garboden's reflexivization, the null reflexive (37). -/
theorem reflexive_resolve_eq_reflexivize {E : Type} {s : CauserSort}
    (h : CauserSort.individual ≤ s) (vp : E → E → Prop) :
    Reading.reflexive.resolve h vp = KoontzGarboden2009.reflexivize vp :=
  rfl

/-- An anticausative's subject is accusative under existential resolution and nominative, the
elsewhere case, under reflexive resolution (§7.3). Accusative is optional and limited to animates
(fn. 27), so the converse is not stated. -/
def caseOfReading : Reading → Case
  | .reflexive   => .nom
  | .existential => .acc

/-- Any causative claim entails the existentially resolved inchoative. Inchoatives are true in
agentive contexts ((51), §5.3), so the ban on volitive inchoatives is formal rather than
truth-conditional. -/
theorem causative_entails_existential {E : Type} {s : CauserSort}
    (h : CauserSort.individual ≤ s) (vp : E → E → Prop) (x y : E)
    (hxy : vp x y) : Reading.existential.resolve h vp y :=
  ⟨x, hxy⟩

theorem reflexive_entails_existential {E : Type} {s : CauserSort}
    (h : CauserSort.individual ≤ s) (vp : E → E → Prop) (y : E)
    (hy : Reading.reflexive.resolve h vp y) : Reading.existential.resolve h vp y :=
  ⟨y, hy⟩

/-- The *ibeemə* 'by itself' diagnostic (58) denies external causation, which contradicts the
accusative's distinct external causer, so accusative-subject anticausatives reject *ibeemə*. -/
theorem ibeem_incompatible_with_external {E : Type} (vp : E → E → Prop) (y : E) :
    ¬ ((∀ x, vp x y → x = y) ∧ ∃ x, x ≠ y ∧ vp x y) :=
  fun ⟨hno, _, hne, hvp⟩ ↦ hne (hno _ hvp)

/-! ### The roots and their causer sorts -/

open Sinhala

/-- A `Root` is one of the Sinhala roots that the paper analyzes. -/
inductive Root where
  | kada | gila | mara | minimara | kapa | vinaashKara
  deriving DecidableEq, Fintype, Repr

/-- `r.verb` is the fragment verb of the root `r`. -/
def Root.verb : Root → Sinhala.Verb
  | .kada => kadann
  | .gila => gilann
  | .mara => marann
  | .minimara => minimarann
  | .kapa => kapann
  | .vinaashKara => vinaashKarann

/-- `r.causerSort` is the causer sort that `r` selects. The agent-subject roots *minimara-* 'murder'
((65b)) and *kapa-* 'cut' select events, and the effector-subject roots select the whole domain, as
*kada-* 'break' does (76) and as 'destroy' does in Sinhala, where it alternates (p. 40). -/
def Root.causerSort : Root → CauserSort
  | .minimara | .kapa => .event
  | .kada | .gila | .mara | .vinaashKara => .any

/-- A root anticausativizes when its causer sort includes the individuals, the condition of
causer suppression (77). -/
def Anticausativizes (r : Root) : Prop := CauserSort.individual ≤ r.causerSort

instance : DecidablePred Anticausativizes := fun r ↦
  inferInstanceAs (Decidable (CauserSort.individual ≤ r.causerSort))

/-- The operator instantiates for *kada-*. -/
example {E : Type} (z : E) (vp : E → Prop) : Prop :=
  causerSuppress Root.kada.causerSort (by decide) z vp

/-- The roots that meet the condition of causer suppression are exactly those whose verbs have
an inchoative. -/
theorem anticausativizes_iff_alternates (r : Root) :
    Anticausativizes r ↔ r.verb.Alternates Voice.anticausative := by
  cases r <;> decide

/-- A root that anticausativizes has an involitive stem, where its inchoative surfaces since the
volitive is barred (§7.3). -/
theorem hasInvolitive_of_anticausativizes {r : Root} (h : Anticausativizes r) :
    r.verb.HasInvolitive := by
  revert h
  cases r <;> decide

/-- The involitive does not mark anticausatives, since *kapa-* 'cut' has an involitive stem
((7c)) and no inchoative ((26)). -/
theorem exists_hasInvolitive_not_anticausativizes :
    ∃ r : Root, r.verb.HasInvolitive ∧ ¬ Anticausativizes r :=
  ⟨.kapa, by decide, by decide⟩

end BeaversZubair2013
