module

public import Linglib.Syntax.Category.Pronoun.Indefinite

/-!
# Latin indefinite pronouns

Latin builds most of its indefinite pronouns on the interrogative *quis*: *quidam*, with the suffix
*-dam*, for a referent the speaker has in mind; *aliquis*, with the prefix *ali-*, for one the
speaker cannot identify, for irrealis non-specific reference and in questions and conditionals;
*quisquam*, with *-quam*, in the negative-polarity functions short of direct negation; and *quivis*,
with *-vis* 'you want' (and *quilibet*, with *-libet* 'it pleases'), for free choice. The negative
series, *nemo* 'nobody' from *ne* and *homo* 'man', is built on generic nouns and confined to direct
negation. In questions and conditionals the bare interrogative is commoner than *aliquis* where it
can lean on *si* or *num*. The members are those of Haspelmath's table, in their usual spelling
where he hyphenates (*ali-quis*); his dual determiners (*neuter*, *utervis*) are determiners here,
and the *-dam* series is the one his note to the table lists.

## References

* [haspelmath-1997]
-/

@[expose] public section

namespace Latin.Indefinites

/-- *quidam* 'somebody', the suffix *-dam* on the interrogative. -/
def quidam : IndefinitePronoun := { form := "quidam", ontology := .person }

/-- *aliquis*, the prefix *ali-* on the interrogative. -/
def aliquis : IndefinitePronoun := { form := "aliquis", ontology := .person }

/-- *quisquam*, the suffix *-quam* on the interrogative. -/
def quisquam : IndefinitePronoun := { form := "quisquam", ontology := .person }

/-- *nemo* 'nobody', the negator on a generic noun. -/
def nemo : IndefinitePronoun := { form := "nemo", ontology := .person }

/-- *quivis*, the interrogative with *-vis* 'you want'. -/
def quivis : IndefinitePronoun := { form := "quivis", ontology := .person }

/-! ### The series -/

/-- The *-dam* series of *quidam* 'somebody', *quiddam* 'something' and the determiner *quidam*
'a certain'. -/
def damSeries : IndefinitePronoun.Series :=
  ⟨"-dam", {quidam, { form := "quiddam", ontology := .thing },
    { form := "quidam", ontology := .determiner }}⟩

/-- The *ali-* series. -/
def aliSeries : IndefinitePronoun.Series :=
  ⟨"ali-", {aliquis, { form := "aliquid", ontology := .thing },
    { form := "alicubi", ontology := .place },
    { form := "aliquando", ontology := .time }, { form := "aliqui", ontology := .determiner }}⟩

/-- The *-quam* series. -/
def quamSeries : IndefinitePronoun.Series :=
  ⟨"-quam", {quisquam, { form := "quidquam", ontology := .thing },
    { form := "usquam", ontology := .place },
    { form := "umquam", ontology := .time }, { form := "ullus", ontology := .determiner }}⟩

/-- The negative series. -/
def nSeries : IndefinitePronoun.Series :=
  ⟨"n-", {nemo, { form := "nihil", ontology := .thing }, { form := "nusquam", ontology := .place },
    { form := "numquam", ontology := .time }, { form := "nullus", ontology := .determiner },
    { form := "neuter", ontology := .determiner }}⟩

/-- The *-vis* series. -/
def visSeries : IndefinitePronoun.Series :=
  ⟨"-vis", {quivis, { form := "quidvis", ontology := .thing },
    { form := "ubivis", ontology := .place },
    { form := "quivis", ontology := .determiner }, { form := "utervis", ontology := .determiner }}⟩

end Latin.Indefinites
