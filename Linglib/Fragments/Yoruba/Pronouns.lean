module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Yorùbá subject pronouns

The six pronouns Awobuluyi calls polymorphic nouns take one form as subject, another as object
and a third as a genitival qualifier, with further subject forms before some adverbs. Their
subject forms distinguish three persons in two numbers, the first person plural making no
clusivity distinction. Aremu calls them the weak pronouns. A focused subject leaves the one of its
person and number in its position: *Èmi ni mo na Akin* 'It was me that beat Akin', with *mo*
where a third person subject would leave *ó*.

## Main definitions

* `Yoruba.Pronouns.subject`: the subject pronoun of each person and number.

## References

* [awobuluyi-1978]
* [aremu-2025b]
-/

@[expose] public section

namespace Yoruba.Pronouns

/-- The first person singular subject *mo*. -/
def mo : PersonalPronoun :=
  { form := "mo", person := some .first, number := some .singular, case_ := some .nom,
    strength := some .weak }

/-- The second person singular subject *o*. -/
def o : PersonalPronoun :=
  { form := "o", person := some .second, number := some .singular, case_ := some .nom,
    strength := some .weak }

/-- The third person singular subject *ó*. -/
def «ó» : PersonalPronoun :=
  { form := "ó", person := some .third, number := some .singular, case_ := some .nom,
    strength := some .weak }

/-- The first person plural subject *a*. -/
def a : PersonalPronoun :=
  { form := "a", person := some .first, number := some .plural, case_ := some .nom,
    strength := some .weak }

/-- The second person plural subject *ẹ*. -/
def «ẹ» : PersonalPronoun :=
  { form := "ẹ", person := some .second, number := some .plural, case_ := some .nom,
    strength := some .weak }

/-- The third person plural subject *wọn*, as Awobuluyi's table gives it; Aremu prints the
resumptive of a plural focus *wọ́n*. -/
def «wọn» : PersonalPronoun :=
  { form := "wọn", person := some .third, number := some .plural, case_ := some .nom,
    strength := some .weak }

/-- The subject pronoun of a person and number, where Yorùbá has one. -/
def subject : Person → Number → Option PersonalPronoun
  | .first, .singular => some mo
  | .second, .singular => some o
  | .third, .singular => some «ó»
  | .first, .plural => some a
  | .second, .plural => some «ẹ»
  | .third, .plural => some «wọn»
  | _, _ => none

end Yoruba.Pronouns
