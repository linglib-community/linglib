module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Indefinite pronouns

An indefinite pronoun is a proform whose function is indefinite reference. Indefinite
pronouns come in series whose members are formed alike across the categories, as the English
*some*-series *somebody*, *something*, *somewhere*, and a series is read as a paradigm whose cells
are the categories. The functions a series covers on Haspelmath's implicational map are an
analysis of its distribution, which studies pair with the series.

## Main definitions

* `IndefinitePronoun`: a proform of the indefinite kind.
* `IndefinitePronoun.ofProForm`, `IndefinitePronoun.ofInterrogative`: the indefinite a marker
  builds on a proform.
* `ProForm.IsQuexistential`: the proform is an interrogative and an indefinite of the language
  under one form.
* `IndefinitePronoun.toWord`: its token, of UD pronoun type `Ind`, an R-expression where nominal
  (`IndefinitePronoun.bindingClassOf_toWord`).
* `IndefinitePronoun.Series`: the members of a series, with the name it is cited by.
* `IndefinitePronoun.Series.forms`: the series as a paradigm over the ontological categories.

## References

* [haspelmath-1997]
* [chomsky-1981]
* [hengeveld-iatridou-roelofsen-2023]
-/

@[expose] public section

/-- An indefinite pronoun is a `ProForm` of the indefinite kind. -/
@[ext]
structure IndefinitePronoun extends ProForm

instance : DecidableEq IndefinitePronoun :=
  fun _ _ ↦ decidable_of_iff _ IndefinitePronoun.ext_iff.symm

namespace IndefinitePronoun

/-- The indefinite a series marker builds on a proform. It has the base's features, category and
word class and the marked form. The marker acts on the romanized form, so the native script of
the marked form is left unrecorded. -/
@[simps ontology cat]
def ofProForm (mark : String → String) (q : ProForm) : IndefinitePronoun :=
  { q with form := mark q.form, script := none }

/-- The indefinite a series marker builds on an interrogative pronoun, as Russian *-nibud'* builds
*kto-nibud'* on *kto*. -/
abbrev ofInterrogative (mark : String → String) (q : InterrogativePronoun) : IndefinitePronoun :=
  ofProForm mark q.toProForm

/-- An indefinite's token is of UD pronoun type `Ind`. -/
def toWord (p : IndefinitePronoun) : Morphology.Word := p.toProForm.toWord .Ind

/-- An indefinite is a quantifier expression, so an R-expression where its word class is nominal,
as *someone* is and *somewhere* is not, and is not a pronominal ([chomsky-1981]). -/
@[simp]
theorem bindingClassOf_toWord (p : IndefinitePronoun) :
    Binding.bindingClassOf p.toWord =
      if Binding.IsNominal p.cat then some .rExpression else none :=
  p.toProForm.bindingClassOf_toWord (.inr (.inr (.inl rfl)))

/-- A proform is a quexistential of a language when it is among its interrogatives and among its
indefinites with no difference in spell-out, as Dutch *wat* is 'what' and 'something'
([hengeveld-iatridou-roelofsen-2023]). -/
def _root_.ProForm.IsQuexistential (p : ProForm) (interrogatives : Finset InterrogativePronoun)
    (indefinites : Finset IndefinitePronoun) : Prop :=
  ⟨p⟩ ∈ interrogatives ∧ ⟨p⟩ ∈ indefinites

instance (p : ProForm) (I : Finset InterrogativePronoun) (J : Finset IndefinitePronoun) :
    Decidable (p.IsQuexistential I J) :=
  inferInstanceAs (Decidable (_ ∧ _))

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

variable {s : Series} {c : ProForm.OntologicalCategory} {f : String}

/-- The forms a series has in an ontological category, read as a paradigm whose cells are the
categories: none where the series is defective, several where a category has more than one
member. -/
def forms (s : Series) (c : ProForm.OntologicalCategory) : Finset String :=
  Morphology.formsAt (fun p ↦ {p.ontology}) (·.form) s.members c

theorem mem_forms : f ∈ s.forms c ↔ ∃ p ∈ s.members, p.ontology = c ∧ p.form = f := by
  simp [forms, Morphology.mem_formsAt, @eq_comm _ c]

end Series

end IndefinitePronoun
