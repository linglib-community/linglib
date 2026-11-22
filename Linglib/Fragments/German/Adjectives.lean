module

public import Linglib.Fragments.German.Determiners
public import Linglib.Syntax.Agreement.Target

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

The two sets of endings and the bare predicative form are agreement targets, `strongAdjective`,
`weakAdjective` and `predicativeAdjective`: the attributive ones inflect for gender, number and
case, and the predicative one for nothing.

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

open German.Determiners (Endingless strongEnding)

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

/-- After an *ein*-word an adjective departs from the weak endings exactly in the cells where the
determiner has no ending. -/
theorem ending_einWord_ne_weak_iff (x : GenderNumber) (c : Case) :
    ending .einWord x c ≠ weak x c ↔ Endingless x c := by
  revert x c; decide

/-- The noun phrase *ein junges Mädchen* 'a young girl' agrees with the gender the suffix fixes:
*Mädchen* is neuter, *ein* has no ending in the nominative singular neuter, and the adjective
takes the strong *-es*. The feminine, the sex of the referent, would give *eine junge*. -/
theorem ein_junges_maedchen :
    Determiners.ein (.sg Gender.maedchen.gender) .nom = some "ein" ∧
      "jung" ++ ending .einWord (.sg Gender.maedchen.gender) .nom = "junges" ∧
      Determiners.ein (.sg .fem) .nom = some "eine" ∧
      "jung" ++ ending .einWord (.sg .fem) .nom = "junge" := by
  decide

/-! ### Agreement targets -/

open Agreement Function

/-- The values German adjective agreement distinguishes in each dimension: the numbers, the three
genders and the four cases, and no person or definiteness. -/
abbrev Value : Dimension → Type
  | .number => Number
  | .gender => Gender.Value
  | .case => Case
  | .person | .definiteness => Unit

/-- The gender and number of a cell, gender being distinguished in the singular alone. -/
def genderNumber (x : Π d, Value d) : GenderNumber :=
  if x .number = .singular then .sg (x .gender) else .pl

/-- The masculine nominative singular, the cell from which the witnesses of inflection depart. -/
private def base : Π d, Value d
  | .number => .singular
  | .gender => .masc
  | .case => .nom
  | .person | .definiteness => ()

/-- The adjective with the strong endings, used attributively, inflects for gender, number and
case. -/
def strongAdjective : Target Value String :=
  .ofDependsOn {.attributive} (fun x ↦ strong (genderNumber x) (x .case)) {.gender, .number, .case}
    (fun x y h ↦ by
      simp only [genderNumber, h .gender (by simp), h .number (by simp), h .case (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨base, Gender.Value.fem, by decide⟩, ⟨base, Number.plural, by decide⟩,
        ⟨base, Case.gen, by decide⟩⟩)

/-- The adjective with the weak endings, used attributively, inflects for gender, number and
case. -/
def weakAdjective : Target Value String :=
  .ofDependsOn {.attributive} (fun x ↦ weak (genderNumber x) (x .case)) {.gender, .number, .case}
    (fun x y h ↦ by
      simp only [genderNumber, h .gender (by simp), h .number (by simp), h .case (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨update base .case Case.acc, Gender.Value.fem, by decide⟩,
        ⟨base, Number.plural, by decide⟩, ⟨base, Case.acc, by decide⟩⟩)

/-- The predicative adjective has no ending and inflects for nothing. -/
def predicativeAdjective : Target Value String :=
  .ofDependsOn {.predicate} (fun _ ↦ "") ∅ (fun _ _ _ ↦ rfl) (by simp)

end German.Adjectives
