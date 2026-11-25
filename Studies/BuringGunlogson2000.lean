module

public import Linglib.Semantics.Questions.Bias
public import Linglib.Semantics.PolarityItem.Polarity
public import Linglib.Languages.English.PolarityItems
public import Linglib.Languages.German.PolarityItems

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
contextual evidence a question type admits is a bias value, a set of signs of the `p` the
evidence supports.

## Main definitions

* `E`, `evidential` — the proto-condition and the evidence each question type admits
* `Determiner`, `Question` — the morphosyntactic probes and a probed question; the polarity items
  are the language files' `either`, `too` and `brauchen`

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

/-! ### The evidence conditions -/

/-- The proto-condition on the proposition of polarity `s`: there is no compelling contextual
evidence against it. Evidence is compelling for a proposition when it would on its own justify
inferring it, and compelling against it when it is compelling for the opposite one. -/
def E (s : Polarity) : BiasValue := .minus (.negative * s)

/-- The evidence each question type admits, as one proto-condition applied three ways: a positive
question imposes it on its own proposition, an outer-negation question on the negation, and an
inner-negation question imposes its negation. -/
def evidential : Option Polarity → BiasValue
  | none => E .positive
  | some .negative => (E .positive)ᶜ
  | some .positive => E .negative

variable {ev : SignType}

/-- A positive question requires no compelling evidence against `p`. -/
theorem mem_evidential_none : ev ∈ evidential none ↔ ev ≠ -1 := by
  simp [evidential, E]

/-- An outer-negation question requires no compelling evidence for `p`. -/
theorem mem_evidential_outer : ev ∈ evidential (some .positive) ↔ ev ≠ 1 := by
  simp [evidential, E]

/-- An inner-negation question requires compelling evidence against `p`. -/
theorem mem_evidential_inner : ev ∈ evidential (some .negative) ↔ ev = -1 := by
  simp [evidential, E]

-- the proto-condition holds of a consistent body of evidence that does not support the opposite
-- proposition, which is what it is for the evidence not to be compelling against it
theorem bias_mem_E_iff {W : Type*} {F : Filter W} [F.NeBot] {p : Set W} (s : Polarity) :
    bias F p ∈ E s ↔ (s • p)ᶜ ∉ F := by
  rw [E, bias_mem_minus_iff, mul_smul, Polarity.negative_smul_set]

/-- No two question types admit the same evidence, so the predicted synonymies of a Hamblin
denotation ([hamblin-1973b]) are not real. -/
theorem evidential_injective : Function.Injective evidential := by decide

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

/-- An outer-negation construal is confined to the syntactic category of interrogative: exactly the
determiners that fail in declaratives are the outer-negation ones. -/
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
  ∀ e ∈ q.item, q.determiner.polarity.Admits e

instance (q : Question) : Decidable q.WellFormed :=
  inferInstanceAs (Decidable (∀ e ∈ q.item, _))

-- (14a)
theorem no_takes_either_not_too :
    (Question.mk .no (some either)).WellFormed ∧
      ¬ (Question.mk .no (some too)).WellFormed := by decide

-- (14b)
theorem notSome_takes_too_not_either :
    (Question.mk .notSome (some too)).WellFormed ∧
      ¬ (Question.mk .notSome (some either)).WellFormed := by decide

-- (16)
theorem brauchen_takes_kein_not_nichtEin :
    (Question.mk .kein (some brauchen)).WellFormed ∧
      ¬ (Question.mk .nichtEin (some brauchen)).WellFormed := by decide

/-- A negative polarity item forces the inner-negation reading (13a). -/
theorem polarity_eq_negative_of_isNPI {d : Determiner} {e : PolarityItem} (he : e.IsNPI)
    (h : (Question.mk d (some e)).WellFormed) : d.polarity = .negative :=
  (h e rfl).2 he

/-- A positive polarity item forces the outer-negation reading (13b). -/
theorem polarity_eq_positive_of_isPPI {d : Determiner} {e : PolarityItem} (he : e.IsPPI)
    (h : (Question.mk d (some e)).WellFormed) : d.polarity = .positive :=
  (h e rfl).1 he

end BuringGunlogson2000
