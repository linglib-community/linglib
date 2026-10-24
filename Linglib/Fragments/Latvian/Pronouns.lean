module

public import Linglib.Fragments.Latvian.Case
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Latvian pronouns

The interrogative pronouns *kas* 'who, what', *kurš* 'who, which' and *kāds* 'what, what
kind', with the interrogative pro-adverbs *kur* 'where', *kad* 'when' and *kā* 'how', each by
the ontological category it asks about: *kas* asks about persons and things alike, and *kurš*
and *kāds* are determiners. They are the bases of the indefinite series of
`Latvian.Indefinites`. The emphatic pronoun *pats* 'self', feminine *pati*, inflects for case,
number and gender on a stem *pat-* ~ *paš-*.

## Implementation notes

The forms of *pats* are segmented into stem and ending as [kalnaca-lokmane-2021] give them;
the instrumental is the form the preposition *ar* 'with' governs.

## References

* [haspelmath-1997]
* [kalnaca-lokmane-2021]
-/

@[expose] public section

namespace Latvian.Pronouns

open Morphology (Morph)

/-! ### Interrogative pronouns -/

/-- *kas* 'who', asking about a person. -/
def kasPerson : InterrogativePronoun := { form := "kas", ontology := .person }

/-- *kas* 'what', the same form asking about a thing. -/
def kasThing : InterrogativePronoun := { form := "kas", ontology := .thing }

/-- *kur* 'where'. -/
def kur : InterrogativePronoun := { form := "kur", ontology := .place }

/-- *kad* 'when'. -/
def kad : InterrogativePronoun := { form := "kad", ontology := .time }

/-- *kā* 'how'. -/
def kā : InterrogativePronoun := { form := "kā", ontology := .manner }

/-- *kāds* 'what, what kind', a determiner. -/
def kāds : InterrogativePronoun := { form := "kāds", ontology := .determiner }

/-- *kurš* 'which, who', a determiner, asking about a member of a known set. -/
def kurš : InterrogativePronoun := { form := "kurš", ontology := .determiner }

/-! ### The emphatic pronoun -/

/-- The emphatic pronoun *pats* 'self', feminine *pati*, as stem and ending in each case,
number and gender ([kalnaca-lokmane-2021], Table 2.21); `none` in the vocative and outside the
two numbers and the two genders. -/
def pats : Case → Number → UD.Gender → Option (List Morph)
  | .nom, .singular, .Masc => some [.root "pat", .suff "s"]
  | .gen, .singular, .Masc => some [.root "paš", .suff "a"]
  | .dat, .singular, .Masc => some [.root "paš", .suff "am"]
  | .acc, .singular, .Masc => some [.root "paš", .suff "u"]
  | .inst, .singular, .Masc => some [.root "paš", .suff "u"]
  | .loc, .singular, .Masc => some [.root "paš", .suff "ā"]
  | .nom, .plural, .Masc => some [.root "paš", .suff "i"]
  | .gen, .plural, .Masc => some [.root "paš", .suff "u"]
  | .dat, .plural, .Masc => some [.root "paš", .suff "iem"]
  | .acc, .plural, .Masc => some [.root "paš", .suff "us"]
  | .inst, .plural, .Masc => some [.root "paš", .suff "iem"]
  | .loc, .plural, .Masc => some [.root "paš", .suff "os"]
  | .nom, .singular, .Fem => some [.root "pat", .suff "i"]
  | .gen, .singular, .Fem => some [.root "paš", .suff "as"]
  | .dat, .singular, .Fem => some [.root "paš", .suff "ai"]
  | .acc, .singular, .Fem => some [.root "paš", .suff "u"]
  | .inst, .singular, .Fem => some [.root "paš", .suff "u"]
  | .loc, .singular, .Fem => some [.root "paš", .suff "ā"]
  | .nom, .plural, .Fem => some [.root "paš", .suff "as"]
  | .gen, .plural, .Fem => some [.root "paš", .suff "u"]
  | .dat, .plural, .Fem => some [.root "paš", .suff "ām"]
  | .acc, .plural, .Fem => some [.root "paš", .suff "as"]
  | .inst, .plural, .Fem => some [.root "paš", .suff "ām"]
  | .loc, .plural, .Fem => some [.root "paš", .suff "ās"]
  | _, _, _ => none

/-- The instrumental of *pats* is its accusative in the singular and its dative in the plural
([kalnaca-lokmane-2021] p. 118). -/
theorem pats_inst_eq (g : UD.Gender) :
    pats .inst .singular g = pats .acc .singular g ∧
      pats .inst .plural g = pats .dat .plural g := by
  cases g <;> decide

end Latvian.Pronouns
