module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Syntax.Category.Pronoun.Interrogative

/-!
# Japanese pronouns

The personal pronouns of Japanese are the first-person forms *watashi*, *boku* and *ore*, which
differ in register, the last two indexing the masculine stance Ochs describes, the second-person
*kimi* and *anata*, and the third-person *kare*, *kanojo* and *karera*. With them are the reciprocal
*otagai* and the reflexive *jibun*. The honorific grades rank *kimi* below *anata*, as they rank the
plain verb below the addressee-honorific suffix *-mas-* (`Japanese.Verb.Exponent.mas`), which Alok
and Bhalla show to be sensitive to the complementizer when embedded. The indeterminate pronouns of
Kratzer and Shimoyama, *dare* 'who', *nani* 'what', *dono* 'which', *doko* 'where', *itsu* 'when',
*naze* 'why' and *dō* 'how', are the interrogatives, and the quantifiers and indefinite series of
`Fragments/Japanese/Determiners.lean` and `Fragments/Japanese/Indefinites.lean` are built on them,
as is *nan-* 'how many' before a classifier.

## References

* [alok-bhalla-2026]
* [ochs-1992]
* [sells-1987]
* [kratzer-shimoyama-2002]
-/

@[expose] public section

namespace Japanese

/-- The honorific grades of Japanese pronouns and the addressee-honorific marker, lowest first. -/
inductive Grade where
  /-- The plain grade, *kimi*. -/
  | plain
  /-- The polite grade, *anata* and *-mas-*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-- 私 *watashi* 'I', of neutral register. -/
def watashi : PersonalPronoun :=
  { form := "watashi", script := some "私", person := some .first, number := some .singular,
    register := .neutral }

/-- 僕 *boku* 'I', informal, associated with men through its register rather than a gender
feature ([ochs-1992]). -/
def boku : PersonalPronoun :=
  { form := "boku", script := some "僕", person := some .first, number := some .singular,
    register := .informal }

/-- 俺 *ore* 'I', very informal, indexing masculinity through an assertive stance
([ochs-1992]). -/
def ore : PersonalPronoun :=
  { form := "ore", script := some "俺", person := some .first, number := some .singular,
    register := .informal }

/-- 私たち *watashitachi* 'we'. -/
def watashitachi : PersonalPronoun :=
  { form := "watashitachi", script := some "私たち", person := some .first,
    number := some .plural }

/-- 君 *kimi* 'you', of the plain grade. -/
def kimi : PersonalPronoun :=
  { form := "kimi", script := some "君", person := some .second, number := some .singular }

/-- あなた *anata* 'you', of the polite grade. -/
def anata : PersonalPronoun :=
  { form := "anata", script := some "あなた", person := some .second, number := some .singular }

/-- 彼 *kare* 'he'. -/
def kare : PersonalPronoun :=
  { form := "kare", script := some "彼", person := some .third, number := some .singular,
    gender := some .Masc }

/-- 彼女 *kanojo* 'she'. -/
def kanojo : PersonalPronoun :=
  { form := "kanojo", script := some "彼女", person := some .third, number := some .singular,
    gender := some .Fem }

/-- 彼ら *karera* 'they'. -/
def karera : PersonalPronoun :=
  { form := "karera", script := some "彼ら", person := some .third, number := some .plural }

/-- The second person singular at each grade. -/
def addressee : Grade → PersonalPronoun
  | .plain => kimi
  | .polite => anata

/-- The personal-pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {watashi, boku, ore, watashitachi, kimi, anata, kare, kanojo, karera}

/-- 互い *otagai* 'each other', the reciprocal, distinct from the reflexive *jibun*. -/
def otagai : ReciprocalPronoun :=
  { form := "otagai", script := some "互い", number := some .plural }

/-- 自分 *jibun*, romanized *zibun* in [sells-1987], is the reflexive, which also takes an
antecedent outside its clause. -/
def jibun : ReflexivePronoun := { form := "jibun", script := some "自分" }

/-! ### Indeterminate pronouns -/

/-- 誰 *dare* 'who'. -/
def dare : InterrogativePronoun := { form := "dare", script := some "誰", ontology := .person }

/-- 何 *nani* 'what'. -/
def nani : InterrogativePronoun := { form := "nani", script := some "何", ontology := .thing }

/-- どの *dono* 'which', a determiner. -/
def dono : InterrogativePronoun :=
  { form := "dono", script := some "どの", ontology := .determiner }

/-- どこ *doko* 'where'. -/
def doko : InterrogativePronoun := { form := "doko", script := some "どこ", ontology := .place }

/-- いつ *itsu* 'when'. -/
def itsu : InterrogativePronoun := { form := "itsu", script := some "いつ", ontology := .time }

/-- なぜ *naze* 'why'. -/
def naze : InterrogativePronoun := { form := "naze", script := some "なぜ", ontology := .reason }

/-- どう *dō* 'how'. -/
def doo : InterrogativePronoun := { form := "dō", script := some "どう", ontology := .manner }

/-- 何 *nan-* 'how many', before a classifier. -/
def nan : InterrogativePronoun := { form := "nan", script := some "何", ontology := .amount }

/-- どれ *dore* 'which one', the determiner of Haspelmath's table. -/
def dore : InterrogativePronoun :=
  { form := "dore", script := some "どれ", ontology := .determiner }

/-- いくら *ikura* 'how much'. -/
def ikura : InterrogativePronoun := { form := "ikura", script := some "いくら", ontology := .amount }

/-- いくつ *ikutsu* 'how many'. -/
def ikutsu : InterrogativePronoun :=
  { form := "ikutsu", script := some "いくつ", ontology := .amount }

end Pronouns

end Japanese
