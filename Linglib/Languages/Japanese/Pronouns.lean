module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Syntax.Category.Pronoun.Interrogative
public import Linglib.Syntax.Category.Pronoun.Demonstrative

/-!
# Japanese pronouns

The personal pronouns of Japanese are the first-person forms *watashi*, *boku* and *ore*, which
differ in register, the second-person
*kimi* and *anata*, and the third-person *kare*, *kanojo* and *karera*. A pronoun for several
referents is the singular with *-tachi*, *watashitachi*, *kimitachi* and *anatatachi*, or with
*-ra*, *karera*. With them are the reciprocal
*otagai* and the reflexive *jibun*. The honorific grades rank *kimi* below *anata*, as they rank the
plain verb below the addressee-honorific suffix *-mas-* (`Japanese.Verb.Exponent.mas`), which Alok
and Bhalla show to be sensitive to the complementizer when embedded. The indeterminate pronouns of
Kratzer and Shimoyama, *dare* 'who', *nani* 'what', *dono* 'which', *doko* 'where', *itsu* 'when',
*naze* 'why' and *dō* 'how', are the interrogatives, and the quantifiers and indefinite series of
`Languages/Japanese/Determiners.lean` and `Languages/Japanese/Indefinites.lean` are built on them,
as is *nan-* 'how many' before a classifier. The demonstrative pronouns *kore*, *sore* and *are*
are Tsujimura's ko-so-a series: near the speaker, near the listener, and far from both.

## Implementation notes

The forms in *-tachi* and *-ra* are recorded as plurals: Kaiser, Ichikawa, Kobayashi and
Yamamoto give *-tachi* as optional on a noun and mandatory on a personal pronoun, which without
it is singular, with *watashi-tachi* and *anata-tachi* among their examples, and Iwasaki gives
*kimi-tachi*. Tsujimura notes that *-tachi* is not a plural marker like the English ending: it
is confined to humans, and a noun with it names a group that includes the noun's referent,
*Yamada-sensei-tachi* being Professor Yamada and those with him; Iwasaki glosses *boku-tachi*
likewise as the speaker and his friends. The registers follow the list Tsujimura takes from
Ide, whose levels of formality are formal, plain and deprecatory: plain *boku* is entered as
neutral and deprecatory *ore* as informal, and *watashi*, formal in men's speech and plain in
women's, carries none.

## References

* [alok-bhalla-2026]
* [iwasaki-2013]
* [kaiser-ichikawa-kobayashi-yamamoto-2013]
* [sells-1987]
* [kratzer-shimoyama-2002]
* [tsujimura-2014]
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

/-- 私 *watashi* 'I', formal in men's speech and plain in women's. -/
def watashi : PersonalPronoun :=
  { form := "watashi", script := some "私", person := some .first, number := some .singular }

/-- 僕 *boku* 'I', plain in men's speech. -/
def boku : PersonalPronoun :=
  { form := "boku", script := some "僕", person := some .first, number := some .singular,
    register := some .neutral }

/-- 俺 *ore* 'I', deprecatory in men's speech. -/
def ore : PersonalPronoun :=
  { form := "ore", script := some "俺", person := some .first, number := some .singular,
    register := some .informal }

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

/-- 君たち *kimitachi* 'you', several addressees, of the plain grade. -/
def kimitachi : PersonalPronoun :=
  { form := "kimitachi", script := some "君たち", person := some .second,
    number := some .plural }

/-- あなたたち *anatatachi* 'you', several addressees, of the polite grade. -/
def anatatachi : PersonalPronoun :=
  { form := "anatatachi", script := some "あなたたち", person := some .second,
    number := some .plural }

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
def addresseeSg : Grade → PersonalPronoun
  | .plain => kimi
  | .polite => anata

/-- The second person plural at each grade. -/
def addresseePl : Grade → PersonalPronoun
  | .plain => kimitachi
  | .polite => anatatachi

/-- The personal-pronoun inventory. -/
def personal : Finset PersonalPronoun :=
  {watashi, boku, ore, watashitachi, kimi, anata, kimitachi, anatatachi, kare, kanojo, karera}

/-- Every person and number has a pronoun. -/
theorem forms_nonempty :
    ∀ c ∈ Agreement.Bundle.personNumberCells, (PersonalPronoun.forms personal c).Nonempty := by
  decide +kernel

/-- Every grade distinguishes one addressee from several. -/
theorem addresseeSg_ne_addresseePl (g : Grade) : addresseeSg g ≠ addresseePl g := by
  cases g <;> decide

/-- 互い *otagai* 'each other', the reciprocal, distinct from the reflexive *jibun*. -/
def otagai : ReciprocalPronoun :=
  { form := "otagai", script := some "互い", number := some .plural }

/-- 自分 *jibun*, romanized *zibun* in [sells-1987], is the reflexive, which also takes an
antecedent outside its clause. -/
def jibun : ReflexivePronoun := { form := "jibun", script := some "自分" }

/-! ### Indeterminate pronouns -/

/-- 誰 *dare* 'who'. -/
def dare : ProForm := { form := "dare", script := some "誰", ontology := .person }

/-- 何 *nani* 'what'. -/
def nani : ProForm := { form := "nani", script := some "何", ontology := .thing }

/-- どの *dono* 'which', a determiner. -/
def dono : ProForm :=
  { form := "dono", script := some "どの", ontology := .determiner }

/-- どこ *doko* 'where'. -/
def doko : ProForm := { form := "doko", script := some "どこ", ontology := .place }

/-- いつ *itsu* 'when'. -/
def itsu : ProForm := { form := "itsu", script := some "いつ", ontology := .time }

/-- なぜ *naze* 'why'. -/
def naze : ProForm := { form := "naze", script := some "なぜ", ontology := .reason }

/-- どう *dō* 'how'. -/
def doo : ProForm := { form := "dō", script := some "どう", ontology := .manner }

/-- 何 *nan-* 'how many', before a classifier. -/
def nan : ProForm := { form := "nan", script := some "何", ontology := .amount }

/-- どれ *dore* 'which one', the determiner of Haspelmath's table, a pronoun. -/
def dore : ProForm :=
  { form := "dore", script := some "どれ", ontology := .determiner, cat := .PRON }

/-- いくら *ikura* 'how much'. -/
def ikura : ProForm := { form := "ikura", script := some "いくら", ontology := .amount }

/-- いくつ *ikutsu* 'how many'. -/
def ikutsu : ProForm :=
  { form := "ikutsu", script := some "いくつ", ontology := .amount }

/-! ### Demonstrative pronouns -/

/-- これ *kore* 'this one', near the speaker ([tsujimura-2014] (24)). -/
def kore : DemonstrativePronoun :=
  { form := "kore", script := some "これ", person := some .third,
    deixis := some ⟨.speaker, .plus⟩ }

/-- それ *sore* 'that one', removed from the speaker but close to the listener. Tsujimura also
gives the so-series a reading slightly removed from both participants, a degree of distance, which
is not recorded ([tsujimura-2014] (24)). -/
def sore : DemonstrativePronoun :=
  { form := "sore", script := some "それ", person := some .third,
    deixis := some ⟨.addressee, .plus⟩ }

/-- あれ *are* 'that one', far from both the speaker and the listener ([tsujimura-2014] (24)). -/
def are : DemonstrativePronoun :=
  { form := "are", script := some "あれ", person := some .third,
    deixis := some ⟨.participant, .minus⟩ }

/-- The demonstrative pronouns. -/
def demonstratives : List DemonstrativePronoun := [kore, sore, are]

end Pronouns

end Japanese
