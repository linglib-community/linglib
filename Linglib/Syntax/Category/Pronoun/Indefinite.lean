module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Indefinite pronouns

An indefinite pronoun is a pronoun with the ontological category it stands for. Indefinite
pronouns come in series whose members are formed alike across the categories, as the English
*some*-series *somebody*, *something*, *somewhere*, and a series is read as a paradigm whose cells
are the categories. The functions a series covers on Haspelmath's implicational map are an
analysis of its distribution, which studies pair with the series.

## Main definitions

* `IndefinitePronoun`: a pronoun with its ontological category.
* `IndefinitePronoun.ofInterrogative`: the indefinite a marker builds on an interrogative.
* `IndefinitePronoun.toWord`: its token, of UD pronoun type `Ind`.
* `IndefinitePronoun.Series`: the members of a series, with the name it is cited by.
* `IndefinitePronoun.Series.forms`: the series as a paradigm over the ontological categories.

## References

* [haspelmath-1997]
-/

@[expose] public section

/-- An indefinite pronoun is a `Pronoun` with the ontological category it stands for. -/
@[ext]
structure IndefinitePronoun extends Pronoun where
  /-- The ontological category the pronoun stands for. -/
  ontology : Pronoun.OntologicalCategory

instance : DecidableEq IndefinitePronoun :=
  fun _ _ ↦ decidable_of_iff _ IndefinitePronoun.ext_iff.symm

namespace IndefinitePronoun

/-- The indefinite a series marker builds on an interrogative pronoun, as Russian *-nibud'* builds
*kto-nibud'* on *kto*. It has the interrogative's features and category and the marked form. The
marker acts on the romanized form, so the native script of the marked form is left unrecorded. -/
@[simps ontology]
def ofInterrogative (mark : String → String) (q : InterrogativePronoun) : IndefinitePronoun :=
  { q.toPronoun with form := mark q.form, script := none, ontology := q.ontology }

/-- An indefinite's token is of UD pronoun type `Ind`, with the word class its category
fixes. -/
def toWord (p : IndefinitePronoun) : Morphology.Word :=
  { p.toPronoun.toWord (some .Ind) with cat := p.ontology.upos }

/-- An indefinite series is the indefinite pronouns formed alike across the ontological
categories, as the English *some*-series *somebody*, *something*, *somewhere*. -/
structure Series where
  /-- The name the series is cited by, its marker where it has one, as *some-*, *-nibud'* or
  *ugodno*. -/
  name : String
  /-- The members, each with its ontological category. -/
  members : Finset IndefinitePronoun
  deriving DecidableEq

namespace Series

variable {s : Series} {c : Pronoun.OntologicalCategory} {f : String}

/-- The forms a series has in an ontological category, read as a paradigm whose cells are the
categories: none where the series is defective, several where a category has more than one
member. -/
def forms (s : Series) (c : Pronoun.OntologicalCategory) : Finset String :=
  Morphology.formsAt (fun p ↦ {p.ontology}) (·.form) s.members c

theorem mem_forms : f ∈ s.forms c ↔ ∃ p ∈ s.members, p.ontology = c ∧ p.form = f := by
  simp [forms, Morphology.mem_formsAt, @eq_comm _ c]

end Series

end IndefinitePronoun
