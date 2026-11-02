module

public import Linglib.Data.Statistics.Schema

/-!
# GundelHedbergZacharski1993: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/GundelHedbergZacharski1993.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

The referring expressions of naturally occurring discourse in Mandarin Chinese, English, Japanese,
Russian and Spanish, from novels, short stories, magazine articles, news broadcasts, interviews and
casual conversations, and for all languages but Russian narrative descriptions of a silent film,
each token coded by two coders for the highest cognitive status its referent met in context. A blank
cell of the printed tables is no token and is omitted. Spanish personal pronouns were mostly not
coded for stress.

## References

* [gundel-hedberg-zacharski-1993]
-/

@[expose] public section

namespace GundelHedbergZacharski1993

open Data.Statistics

/-- The languages of the study. -/
inductive Language where
  /-- Chinese: Mandarin Chinese, Table 2 -/
  | chinese
  /-- English: English, Table 3 -/
  | english
  /-- Japanese: Japanese, Table 4 -/
  | japanese
  /-- Russian: Russian, Table 5 -/
  | russian
  /-- Spanish: Spanish, Table 6 -/
  | spanish
  deriving DecidableEq, Repr, Fintype

/-- A referring form, as the rows of Tables 2-6 print it. -/
inductive Form where
  /-- ø: a zero pronominal -/
  | zero
  /-- tā: the personal pronoun 's/he, it' -/
  | ta
  /-- zhè: the proximal demonstrative pronoun 'this' -/
  | zhe
  /-- nèi: the distal demonstrative pronoun 'that' -/
  | nei
  /-- zhè N: the proximal demonstrative determiner with a noun -/
  | zheN
  /-- nèi N: the distal demonstrative determiner with a noun -/
  | neiN
  /-- yī N: 'one' with a noun, 'a N' -/
  | yiN
  /-- N: a bare noun -/
  | bare
  /-- it: the unstressed personal pronoun -/
  | it
  /-- HE: a stressed personal pronoun -/
  | stressedHe
  /-- this: the proximal demonstrative pronoun -/
  | thisPronoun
  /-- that: the distal demonstrative pronoun -/
  | thatPronoun
  /-- this N: the proximal demonstrative determiner with a noun -/
  | thisN
  /-- that N: the distal demonstrative determiner with a noun -/
  | thatN
  /-- the N: the definite article with a noun -/
  | theN
  /-- indefinite this N: indefinite this with a noun -/
  | indefiniteThisN
  /-- a N: the indefinite article with a noun -/
  | aN
  /-- kare: the personal pronoun 'he' -/
  | kare
  /-- kore: the proximal demonstrative pronoun 'this' -/
  | kore
  /-- sore: the medial demonstrative pronoun 'that' -/
  | sore
  /-- are: the distal demonstrative pronoun 'that' -/
  | are
  /-- kono N: the proximal demonstrative determiner with a noun -/
  | konoN
  /-- sono N: the medial demonstrative determiner with a noun -/
  | sonoN
  /-- ano N: the distal demonstrative determiner with a noun -/
  | anoN
  /-- ono: the unstressed personal pronoun 'it' -/
  | ono
  /-- ONO: the stressed personal pronoun 'it' -/
  | stressedOno
  /-- èto: the proximal demonstrative pronoun 'this' -/
  | eto
  /-- tot: the distal demonstrative pronoun 'that' -/
  | tot
  /-- èto N: the proximal demonstrative determiner with a noun -/
  | etoN
  /-- to N: the distal demonstrative determiner with a noun -/
  | toN
  /-- él (subj): the personal pronoun 'he' as subject, stressed or unstressed -/
  | elSubj
  /-- él (nonsubj): the personal pronoun 'he' as nonsubject, stressed or unstressed -/
  | elNonsubj
  /-- éste: the proximal demonstrative pronoun 'this' -/
  | este
  /-- ése: the medial demonstrative pronoun 'that' -/
  | ese
  /-- aquél: the distal demonstrative pronoun 'that' -/
  | aquel
  /-- este N: the proximal demonstrative determiner with a noun -/
  | esteN
  /-- ese N: the medial demonstrative determiner with a noun -/
  | eseN
  /-- aquel N: the distal demonstrative determiner with a noun -/
  | aquelN
  /-- el N: the definite article with a noun -/
  | elN
  /-- un N: the indefinite article with a noun -/
  | unN
  deriving DecidableEq, Repr, Fintype

/-- The highest cognitive status a referent met, as the columns of Tables 2-6 print it. -/
inductive Status where
  /-- In focus: in focus -/
  | inFocus
  /-- Activated: activated -/
  | activated
  /-- Familiar: familiar -/
  | familiar
  /-- Unique: uniquely identifiable -/
  | unique
  /-- Referential: referential -/
  | referential
  /-- Type: type identifiable -/
  | typeIdentifiable
  deriving DecidableEq, Repr, Fintype

/-- A row of Tables 2-6, pp. 291-292: the tokens of a form whose referent met a status as its
highest. -/
structure Cell where
  /-- The language. -/
  language : Language
  /-- The referring form. -/
  form : Form
  /-- The highest status the referent met. -/
  status : Status
  /-- The number of tokens. -/
  tokens : ℕ
  deriving DecidableEq, Repr

/-- The 87 rows of Tables 2-6, pp. 291-292, in the paper's order; counted in a corpus; checked
against the page images. -/
def distribution : List Cell :=
  [⟨.chinese, .zero, .inFocus, 25⟩,
   ⟨.chinese, .zero, .activated, 1⟩,
   ⟨.chinese, .ta, .inFocus, 40⟩,
   ⟨.chinese, .zhe, .activated, 2⟩,
   ⟨.chinese, .zheN, .inFocus, 12⟩,
   ⟨.chinese, .zheN, .activated, 26⟩,
   ⟨.chinese, .zheN, .familiar, 1⟩,
   ⟨.chinese, .neiN, .inFocus, 1⟩,
   ⟨.chinese, .neiN, .activated, 7⟩,
   ⟨.chinese, .neiN, .familiar, 2⟩,
   ⟨.chinese, .yiN, .referential, 17⟩,
   ⟨.chinese, .yiN, .typeIdentifiable, 2⟩,
   ⟨.chinese, .bare, .inFocus, 12⟩,
   ⟨.chinese, .bare, .activated, 17⟩,
   ⟨.chinese, .bare, .familiar, 14⟩,
   ⟨.chinese, .bare, .unique, 49⟩,
   ⟨.chinese, .bare, .referential, 2⟩,
   ⟨.chinese, .bare, .typeIdentifiable, 10⟩,
   ⟨.english, .it, .inFocus, 214⟩,
   ⟨.english, .it, .activated, 1⟩,
   ⟨.english, .stressedHe, .activated, 1⟩,
   ⟨.english, .thisPronoun, .activated, 15⟩,
   ⟨.english, .thatPronoun, .inFocus, 1⟩,
   ⟨.english, .thatPronoun, .activated, 17⟩,
   ⟨.english, .thisN, .inFocus, 1⟩,
   ⟨.english, .thisN, .activated, 11⟩,
   ⟨.english, .thatN, .activated, 10⟩,
   ⟨.english, .thatN, .familiar, 7⟩,
   ⟨.english, .theN, .inFocus, 30⟩,
   ⟨.english, .theN, .activated, 95⟩,
   ⟨.english, .theN, .familiar, 47⟩,
   ⟨.english, .theN, .unique, 108⟩,
   ⟨.english, .indefiniteThisN, .referential, 1⟩,
   ⟨.english, .aN, .referential, 41⟩,
   ⟨.english, .aN, .typeIdentifiable, 55⟩,
   ⟨.japanese, .zero, .inFocus, 87⟩,
   ⟨.japanese, .zero, .activated, 1⟩,
   ⟨.japanese, .kare, .inFocus, 4⟩,
   ⟨.japanese, .kore, .inFocus, 1⟩,
   ⟨.japanese, .kore, .activated, 1⟩,
   ⟨.japanese, .sore, .activated, 1⟩,
   ⟨.japanese, .konoN, .inFocus, 1⟩,
   ⟨.japanese, .konoN, .activated, 7⟩,
   ⟨.japanese, .konoN, .familiar, 1⟩,
   ⟨.japanese, .sonoN, .inFocus, 18⟩,
   ⟨.japanese, .sonoN, .activated, 15⟩,
   ⟨.japanese, .sonoN, .familiar, 1⟩,
   ⟨.japanese, .anoN, .activated, 1⟩,
   ⟨.japanese, .anoN, .familiar, 1⟩,
   ⟨.japanese, .bare, .inFocus, 14⟩,
   ⟨.japanese, .bare, .activated, 32⟩,
   ⟨.japanese, .bare, .familiar, 17⟩,
   ⟨.japanese, .bare, .unique, 71⟩,
   ⟨.japanese, .bare, .referential, 45⟩,
   ⟨.japanese, .bare, .typeIdentifiable, 44⟩,
   ⟨.russian, .zero, .inFocus, 18⟩,
   ⟨.russian, .ono, .inFocus, 51⟩,
   ⟨.russian, .ono, .activated, 2⟩,
   ⟨.russian, .stressedOno, .activated, 1⟩,
   ⟨.russian, .eto, .inFocus, 2⟩,
   ⟨.russian, .eto, .activated, 9⟩,
   ⟨.russian, .etoN, .inFocus, 1⟩,
   ⟨.russian, .etoN, .activated, 7⟩,
   ⟨.russian, .etoN, .familiar, 2⟩,
   ⟨.russian, .bare, .inFocus, 25⟩,
   ⟨.russian, .bare, .activated, 29⟩,
   ⟨.russian, .bare, .familiar, 22⟩,
   ⟨.russian, .bare, .unique, 66⟩,
   ⟨.russian, .bare, .referential, 21⟩,
   ⟨.russian, .bare, .typeIdentifiable, 28⟩,
   ⟨.spanish, .zero, .inFocus, 63⟩,
   ⟨.spanish, .elSubj, .inFocus, 30⟩,
   ⟨.spanish, .elSubj, .activated, 3⟩,
   ⟨.spanish, .elNonsubj, .inFocus, 57⟩,
   ⟨.spanish, .elNonsubj, .activated, 2⟩,
   ⟨.spanish, .este, .activated, 1⟩,
   ⟨.spanish, .ese, .activated, 4⟩,
   ⟨.spanish, .aquel, .activated, 1⟩,
   ⟨.spanish, .eseN, .inFocus, 1⟩,
   ⟨.spanish, .eseN, .activated, 2⟩,
   ⟨.spanish, .eseN, .familiar, 3⟩,
   ⟨.spanish, .elN, .inFocus, 23⟩,
   ⟨.spanish, .elN, .activated, 45⟩,
   ⟨.spanish, .elN, .familiar, 22⟩,
   ⟨.spanish, .elN, .unique, 42⟩,
   ⟨.spanish, .unN, .referential, 22⟩,
   ⟨.spanish, .unN, .typeIdentifiable, 10⟩]

end GundelHedbergZacharski1993
