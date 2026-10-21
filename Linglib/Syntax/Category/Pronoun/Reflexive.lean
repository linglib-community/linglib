module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Reflexive pronouns

A reflexive pronoun is a pronoun whose kind fixes its binding class: it is an anaphor, bound in
its local domain. Some reflexives, as Japanese *zibun* and Icelandic *sig*, also take an
antecedent outside that domain; what licenses the distant antecedent is a matter of analysis and
is not recorded on the entry.

## Main definitions

* `ReflexivePronoun`: a pronoun of the reflexive kind.
* `ReflexivePronoun.paradigm`: the forms an inventory offers for each category its person and
  number realize.
* `ReflexivePronoun.toWord`: its token, marked reflexive.

## Main statements

* `ReflexivePronoun.bindingClassOf_toWord`: the token of a reflexive classifies as a reflexive
  anaphor.

## References

* [chomsky-1981]
-/

@[expose] public section

/-- A reflexive pronoun is a `Pronoun` of the reflexive kind. -/
@[ext]
structure ReflexivePronoun extends Pronoun

instance : DecidableEq ReflexivePronoun :=
  fun _ _ ↦ decidable_of_iff _ ReflexivePronoun.ext_iff.symm

namespace ReflexivePronoun

/-- The paradigm of an inventory assigns each category the forms of the reflexives whose person
and number realize it. A reflexive denotes what its antecedent does, so its cells are those of
its agreement features. -/
def paradigm : Finset ReflexivePronoun → Person.Category → Finset String :=
  Morphology.formsAt (·.categories) (·.form)

theorem mem_paradigm {I : Finset ReflexivePronoun} {c : Person.Category} {f : String} :
    f ∈ paradigm I c ↔ ∃ p ∈ I, c ∈ p.categories ∧ p.form = f :=
  Morphology.mem_formsAt

/-- A reflexive's token is of UD pronoun type `Prs` and marked reflexive. -/
def toWord (p : ReflexivePronoun) : Morphology.Word := p.toPronoun.toWord (some .Prs) (some ())

/-- A reflexive pronoun is a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord (p : ReflexivePronoun) :
    Binding.bindingClassOf p.toWord = some .reflexive :=
  Pronoun.bindingClassOf_toWord_reflex _ _

end ReflexivePronoun
