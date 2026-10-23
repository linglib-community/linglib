module

public import Linglib.Semantics.Questions.Bias
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Fragments.German.PolarityItems

/-!
# Büring and Gunlogson 2000: aren't positive and negative polar questions the same?

This file formalizes Büring and Gunlogson's felicity conditions. Standard question
semantics gives *Is she left-handed?*, *Isn't she left-handed?* and *Is she right-handed?* one and
the same denotation, yet the three types are felicitous in different contexts: a positive question
is barred by compelling contextual evidence against its proposition, an inner-negation question
requires such evidence, and an outer-negation question is barred by evidence for it. The paper's
appendix derives all three from one proto-condition applied to the question's proposition, to its
negation, or negated in turn, and Ladd's morphosyntactic probes — *kein* vs *nicht
ein*, *no* vs *not some*, and the polarity items they admit — classify a question independently of
those judgements.

The three question types are readings, `Option Polarity`: `none` is the paper's PPQ, and a
negative question is an inner-negation NPQ, `some .negative`, when the negation sits inside the
questioned proposition, and an outer-negation NPQ, `some .positive`, when it sits outside. The
contextual evidence of a situation is the sign of `p` it supports, and reading it relative to `¬p`
negates it.

## Main definitions

* `E`, `Felicitous` — the proto-condition and the felicity condition of each question type
* `Determiner`, `Question` — the morphosyntactic probes and a probed question; the polarity items
  are the fragments' `either`, `too` and `brauchen`

## Main results

* `felicitous_none_iff`, `felicitous_some_positive_iff`, `felicitous_some_negative_iff` — the
  three evidence conditions
* `felicity_separates_readings` — no two question types share a felicity profile
* `outer_is_interrogative_only` — only inner-negation determiners occur in declaratives
* `polarity_eq_negative_of_isNPI`, `polarity_eq_positive_of_isPPI` — a polarity item forces the
  reading the determiner gives

## References

* [buring-gunlogson-2000]
* [ladd-1981]
* [hamblin-1973b]
-/

@[expose] public section

namespace BuringGunlogson2000

open Question
open English.PolarityItems (either too)
open German.PolarityItems (brauchen)

/-! ### Compelling contextual evidence -/

/-- Evidence is **compelling** for `p` when it would on its own justify the inference that `p`. -/
def CompellingFor (ev : SignType) : Prop := ev = 1

/-- Evidence is compelling against `p` when it is compelling for `¬p`, the evidence read relative
to `¬p`. -/
def CompellingAgainst (ev : SignType) : Prop := CompellingFor (-ev)

instance (ev : SignType) : Decidable (CompellingFor ev) :=
  inferInstanceAs (Decidable (_ = _))

instance (ev : SignType) : Decidable (CompellingAgainst ev) :=
  inferInstanceAs (Decidable (CompellingFor _))

/-! ### The evidence conditions -/

/-- The proto-condition: there is no compelling contextual evidence against `p`. -/
def E (ev : SignType) : Prop := ¬ CompellingAgainst ev

instance (ev : SignType) : Decidable (E ev) := inferInstanceAs (Decidable ¬ _)

/-- The felicity condition of each question type, as one proto-condition applied three ways: a
positive question imposes it on its own proposition, an outer-negation question on the negation,
and an inner-negation question imposes its negation. -/
def Felicitous : Option Polarity → SignType → Prop
  | none, ev => E ev
  | some .negative, ev => ¬ E ev
  | some .positive, ev => E (-ev)

instance : ∀ (r : Option Polarity) (ev : SignType), Decidable (Felicitous r ev)
  | none, ev => inferInstanceAs (Decidable (E ev))
  | some .negative, ev => inferInstanceAs (Decidable ¬ E ev)
  | some .positive, ev => inferInstanceAs (Decidable (E (-ev)))

theorem felicitous_none_iff (ev : SignType) :
    Felicitous none ev ↔ ¬ CompellingAgainst ev := Iff.rfl

theorem felicitous_some_positive_iff (ev : SignType) :
    Felicitous (some .positive) ev ↔ ¬ CompellingFor ev := by
  decide +revert

theorem felicitous_some_negative_iff (ev : SignType) :
    Felicitous (some .negative) ev ↔ CompellingAgainst ev := by
  decide +revert

theorem not_felicitous_none_neg_one : ¬ Felicitous none (-1) := by decide

theorem felicitous_some_negative_iff_eq (ev : SignType) :
    Felicitous (some .negative) ev ↔ ev = -1 := by
  decide +revert

theorem felicitous_some_positive_zero_not_negative :
    Felicitous (some .positive) 0 ∧ ¬ Felicitous (some .negative) 0 := by
  decide

theorem felicity_separates_readings (r s : Option Polarity)
    (h : ∀ ev, Felicitous r ev ↔ Felicitous s ev) :
    r = s := by
  rcases r with _ | _ | _ <;> rcases s with _ | _ | _ <;>
    first
      | rfl
      | exact absurd (h 0) (by decide)
      | exact absurd (h 1) (by decide)

/-! ### The morphosyntactic probes -/

/-- The negative determiners that probe the distinction are German *kein* and *nicht ein* and
English *no* and *not some*. -/
inductive Determiner | kein | nichtEin | no | notSome
  deriving DecidableEq

/-- The polarity of the proposition a question with the determiner double-checks: *nicht ein* and
*not some* leave the negation outside it, so it is positive; *kein* and *no* place it inside. -/
def Determiner.polarity : Determiner → Polarity
  | .kein | .no => .negative
  | .nichtEin | .notSome => .positive

/-- Whether the determiner also occurs in a declarative. The non-amalgamated forms do not, even
under rising intonation. -/
def Determiner.declarativeOK : Determiner → Prop
  | .kein | .no => True
  | .nichtEin | .notSome => False

instance : ∀ d : Determiner, Decidable d.declarativeOK
  | .kein | .no => inferInstanceAs (Decidable True)
  | .nichtEin | .notSome => inferInstanceAs (Decidable False)

theorem outer_is_interrogative_only (d : Determiner) :
    d.polarity = .positive ↔ ¬ d.declarativeOK := by
  cases d <;> decide

/-- A polar question as its two probes, a negative determiner and, optionally, a polarity item,
English *either* or *too* or German *brauchen*. -/
structure Question where
  determiner : Determiner
  item : Option PolarityItem

/-- The probes agree on where the negation sits, since a negative polarity item must sit under it,
so it requires the inner construal, and a positive polarity item must escape it, so it requires
the outer one. -/
def Question.WellFormed (q : Question) : Prop :=
  ∀ e ∈ q.item,
    (e.IsNPI → q.determiner.polarity = .negative) ∧ (e.IsPPI → q.determiner.polarity = .positive)

instance : ∀ q : Question, Decidable q.WellFormed
  | ⟨_, none⟩ => isTrue (by simp [Question.WellFormed])
  | ⟨d, some e⟩ =>
    decidable_of_iff ((e.IsNPI → d.polarity = .negative) ∧ (e.IsPPI → d.polarity = .positive))
      (by simp [Question.WellFormed])

/-- In *Is there no vegetarian restaurant either/\*too?* (14a) the inner-negation determiner takes
the negative polarity item and refuses the positive one. -/
theorem no_takes_either_not_too :
    (Question.mk .no (some either)).WellFormed ∧
      ¬ (Question.mk .no (some too)).WellFormed := by decide

/-- In *Isn't there some vegetarian restaurant \*either/too?* (14b) the outer-negation determiner
takes the positive polarity item and refuses the negative one. -/
theorem notSome_takes_too_not_either :
    (Question.mk .notSome (some too)).WellFormed ∧
      ¬ (Question.mk .notSome (some either)).WellFormed := by decide

/-- In *Brauchst du keine/\*nicht eine Entschuldigung mitzubringen?* (16) the German NPI likewise
goes with the amalgamated determiner only. -/
theorem brauchen_takes_kein_not_nichtEin :
    (Question.mk .kein (some brauchen)).WellFormed ∧
      ¬ (Question.mk .nichtEin (some brauchen)).WellFormed := by decide

/-- A negative polarity item forces the inner-negation reading (13a). -/
theorem polarity_eq_negative_of_isNPI {d : Determiner} {e : PolarityItem} (he : e.IsNPI)
    (h : (Question.mk d (some e)).WellFormed) : d.polarity = .negative :=
  (h e rfl).1 he

/-- A positive polarity item forces the outer-negation reading (13b). -/
theorem polarity_eq_positive_of_isPPI {d : Determiner} {e : PolarityItem} (he : e.IsPPI)
    (h : (Question.mk d (some e)).WellFormed) : d.polarity = .positive :=
  (h e rfl).2 he

end BuringGunlogson2000
