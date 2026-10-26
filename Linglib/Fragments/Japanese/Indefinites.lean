module

public import Linglib.Fragments.Japanese.Coordination
public import Linglib.Fragments.Japanese.Pronouns
public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Japanese indefinite pronouns

Japanese builds its indefinite series on the indeterminate pronouns with a particle: *-ka*
(*dare-ka* 'someone'), *-mo* (*dare-mo* 'nobody' with clausemate negation, and without negation the
universal 'everyone') and *-demo* (*dare-demo* 'anyone'). A member of a series is its marker applied
to an interrogative of `Japanese.Pronouns`, which derives its form and category; the particles *ka*
and *mo* are the coordinators of `Japanese.Coordination`. The members are those of Haspelmath's
table, in the Hepburn spelling of the interrogatives where he writes *itu*, *doo* and *ikutu*.

## References

* [haspelmath-1997]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

namespace Japanese.Indefinites

open Pronouns

/-! ### The markers -/

/-- The *-ka* marker puts the particle `Japanese.Coordination.ka` after the indeterminate. -/
def ka : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-" ++ Coordination.ka.morph.form)

/-- The *-mo* marker puts the particle `Japanese.Coordination.mo` after the indeterminate. -/
def mo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-" ++ Coordination.mo.morph.form)

/-- The *-demo* marker puts *-demo* after the indeterminate. -/
def demo : InterrogativePronoun → IndefinitePronoun :=
  IndefinitePronoun.ofInterrogative (· ++ "-demo")

/-! ### The person row -/

/-- *dare-ka* 'someone'. -/
def dareKa : IndefinitePronoun := ka Pronouns.dare

/-- *dare-mo* 'nobody' under clausemate negation. -/
def dareMo : IndefinitePronoun := mo Pronouns.dare

/-- *dare-demo* 'anyone'. -/
def dareDemo : IndefinitePronoun := demo Pronouns.dare

/-! ### The series -/

/-- The *-ka* series. -/
def kaSeries : IndefinitePronoun.Series :=
  ⟨"-ka", ({dare, nani, doko, itsu, doo, ikura, ikutsu, dore} : Finset _).image ka⟩

/-- The *-mo* series, which has members only for a person, a thing, a place and a
determiner. -/
def moSeries : IndefinitePronoun.Series := ⟨"-mo", ({dare, nani, doko, dore} : Finset _).image mo⟩

/-- The *-demo* series. -/
def demoSeries : IndefinitePronoun.Series :=
  ⟨"-demo", ({dare, nani, doko, itsu, doo, ikura, ikutsu, dore} : Finset _).image demo⟩

end Japanese.Indefinites
