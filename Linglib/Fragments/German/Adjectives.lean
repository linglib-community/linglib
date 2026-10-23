module

public import Linglib.Fragments.German.Determiners

/-!
# German adjective declension

This file defines the endings of German attributive adjectives and the principle that chooses
between them. An adjective declines when it stands before its noun, and has no ending in the
predicate. It has two sets of endings. The strong endings are those of *dieser*, but for *-en* in
the genitive singular masculine and neuter; the weak endings are *-e* in the nominative singular
and in the accusative singular feminine and neuter, and *-en* everywhere else. Durrell gives one
principle that chooses between them: an adjective takes the strong endings when no determiner in
its noun phrase has an ending, and the weak endings when one does. So it is strong with no
determiner, weak after the definite article and *dieser*, and after *ein*, *kein* and the
possessives strong in the three cells where they have no ending and weak in the rest. That last
declension, which seems to mix the other two and is sometimes called the mixed declension, is not
a third declension.

Adjectives agree with the grammatical gender of their noun, also where it is not the sex of the
referent: *ein junges Mädchen* 'a young girl'.

## Main definitions

* `German.Adjectives.strong`, `German.Adjectives.weak`: the two sets of endings.
* `German.Adjectives.Preceding`: what precedes an adjective in its noun phrase, for the choice.
* `German.Adjectives.ending`: the ending an adjective takes.

## Main results

* `German.Adjectives.ending_einWord_ne_weak_iff`: after an *ein*-word an adjective departs from
  the weak endings exactly in the cells where the determiner has no ending.
* `German.Adjectives.ein_junges_maedchen`: *ein junges Mädchen*, from the gender the suffix fixes.

## References

* [durrell-2011]
-/

@[expose] public section

namespace German.Adjectives

open German.Determiners (GenderNumber Endingless strongEnding)

/-- `strong x c` is the strong ending of the cell, the ending of *dieser* except for *-en* in the
genitive singular masculine and neuter. -/
def strong (x : GenderNumber) (c : Case) : String :=
  if c = .gen ∧ (x = .sg .masc ∨ x = .sg .neut) then "en" else strongEnding x c

/-- `weak x c` is the weak ending of the cell, *-e* in the nominative singular and in the
accusative singular feminine and neuter and *-en* everywhere else. -/
def weak (x : GenderNumber) (c : Case) : String :=
  if c = .nom ∧ x ≠ .pl ∨ c = .acc ∧ (x = .sg .fem ∨ x = .sg .neut) then "e"
  else "en"

/-- An adjective is preceded in its noun phrase by no determiner, by a determiner with an ending in
every cell such as the definite article or *dieser*, or by an *ein*-word. -/
inductive Preceding where
  | none
  | inflected
  | einWord
  deriving DecidableEq, Repr, Fintype

/-- `p.HasEnding x c` holds when the preceding determiner has an ending in the cell. -/
def Preceding.HasEnding : Preceding → GenderNumber → Case → Prop
  | .none, _, _ => False
  | .inflected, _, _ => True
  | .einWord, x, c => ¬ Endingless x c

instance : (p : Preceding) → (x : GenderNumber) → (c : Case) → Decidable (p.HasEnding x c)
  | .none, _, _ => inferInstanceAs (Decidable False)
  | .inflected, _, _ => inferInstanceAs (Decidable True)
  | .einWord, x, c => inferInstanceAs (Decidable (¬ Endingless x c))

/-- An adjective takes the weak ending when the preceding determiner has an ending, and the strong
ending when there is none. -/
def ending (p : Preceding) (x : GenderNumber) (c : Case) : String :=
  if p.HasEnding x c then weak x c else strong x c

@[simp] theorem ending_none : ending .none = strong := by
  funext x c; simp [ending, Preceding.HasEnding]

@[simp] theorem ending_inflected : ending .inflected = weak := by
  funext x c; simp [ending, Preceding.HasEnding]

theorem ending_einWord_ne_weak_iff (x : GenderNumber) (c : Case) :
    ending .einWord x c ≠ weak x c ↔ Endingless x c := by
  revert x c; decide

theorem ein_junges_maedchen :
    Determiners.ein (.sg Gender.maedchen.gender) .nom = some "ein" ∧
      "jung" ++ ending .einWord (.sg Gender.maedchen.gender) .nom = "junges" ∧
      Determiners.ein (.sg .fem) .nom = some "eine" ∧
      "jung" ++ ending .einWord (.sg .fem) .nom = "junge" := by
  decide

end German.Adjectives
