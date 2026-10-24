module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.BigOperators
public import Linglib.Core.Logic.Function.FactorsThrough

/-!
# Gender systems

A *gender* is a class of nouns that take the same agreements, so a language's genders are its
own: there is no universal inventory of gender values as there is of number and person values.
This file takes a language's controller genders as a type `G`, whose cardinality is the number of
genders, and defines the comparative labels they may partially bear and when `G` is *faithful* to
agreement evidence: distinct genders are distinguished by some agreement target.

## Main definitions

* `Gender`: the comparative labels, realized in Universal Dependencies in `Morphology/Word/UD`.
* `Gender.Faithful`: the agreement evidence is injective on genders.

## Main results

* `Gender.Faithful.card_le_pow`: `f` forms on each of `t` targets support at most `f ^ t`
  controller genders.

## Implementation notes

* `G` is the controller-gender partition: singular and plural of one noun are one gender.
  Classifiers and declension classes trigger no agreement and are not genders.
* Languages lacking gender, the majority, declare no `G`. Where gender is located in the nominal
  spine is left to studies.
* Kramer's two-class minimum is the hypothesis `Nontrivial G` where needed: one agreement pattern
  for all nouns is the absence of a system.
* A fragment's gender enum is a `G`, and its `toLabel` maps it into `Gender`. Assignment systems
  are in `Syntax/Gender/Assignment.lean`.

## References

* [corbett-1991] — genders as agreement classes, crediting [hockett-1958]
* [zaliznjak-1964] — agreement classes
* [kramer-2015] — the two-class minimum
* [harbour-2014] — the universal calculi of number and person, which gender lacks
-/

@[expose] public section

/-- Comparative-concept labels for controller genders ([corbett-1991]).

These are the descriptive labels cross-linguistic comparison uses for a language's agreement
classes, not a universal value inventory. A language's actual genders form its own type, which a
fragment's `toLabel` maps into this vocabulary. -/
inductive Gender where
  /-- The masculine holds male humans and higher animates, and is the default in many sex-based
  systems. -/
  | masculine
  /-- The feminine holds female humans and higher animates, and is marked in many sex-based
  systems. -/
  | feminine
  /-- The neuter is neither masculine nor feminine, and is the inanimate default in three-gender
  systems. -/
  | neuter
  /-- The common gender merges masculine and feminine (Swedish, Danish). -/
  | common
  /-- The animate holds animate referents in animacy-based systems (Algonquian). -/
  | animate
  /-- The inanimate holds inanimate referents in animacy-based systems. -/
  | inanimate
  deriving DecidableEq, Repr, Fintype

namespace Gender

/-! ### Language-particular genders

A gender system is language-particular: its values are the language's own controller genders,
supplied as a type `G` (a fragment's gender enum). The comparative labels above enter only through
a fragment's partial map into them, and `G` need not fit them. This accommodates Bantu-scale
inventories that no label vocabulary covers. -/

variable {G : Type*}

/-! ### Agreement faithfulness

Agreement evidence for `G` is a map `agr : G → T → F` giving the form each target shows for
each gender. `G` is faithful to the evidence when distinct genders are distinguished by some
target. Otherwise it posits a spurious distinction, since two genders that agree alike everywhere
are one gender. The target and form types are parameters, leaving open what counts as a target:
this is where [kramer-2015]'s strict-Agree and loose-covariation definitions of gender differ. -/

section Faithful

variable {T F : Type*}

/-- A type `G` of controller genders is faithful to agreement evidence `agr` when distinct
genders are distinguished by some target's form.

It is an `abbrev` so that `Function.Injective`'s decidability instance (under `[Fintype G]`,
`[DecidableEq T]`, `[DecidableEq F]`) applies and concrete fragments prove faithfulness by
`decide`. -/
abbrev Faithful (agr : G → T → F) : Prop :=
  Function.Injective agr

/-- A language whose agreement morphology shows `f` forms on each of `t` targets supports at
most `f ^ t` controller genders. -/
theorem Faithful.card_le_pow [Fintype G] [Fintype T] [Fintype F] [DecidableEq T]
    {agr : G → T → F} (h : Faithful agr) :
    Fintype.card G ≤ Fintype.card F ^ Fintype.card T := by
  rw [← Fintype.card_fun]
  exact Fintype.card_le_of_injective agr h

end Faithful

end Gender
